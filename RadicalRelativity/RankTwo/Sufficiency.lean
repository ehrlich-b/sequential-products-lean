/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.Bloch
import RadicalRelativity.Necessity.FrameConstancy

set_option linter.style.longLine false

/-!
# `prop:n2-sufficiency`: the frame-dependent twist product, algebraic core

`Hermitian/Sequential.lean` builds the twist product for a **constant** parameter
(`twistSequentialProduct`, `lem:twist-sufficiency`).  The article's rank-two sufficiency
proposition needs the parameter to vary with the left argument's spectral frame, and
`WallCertificates/prop-n2-sufficiency.lean` records where that generalization is genuinely
harder: the axioms relating *two* left arguments (S5, S7) stop being formal, because the inner
and outer products carry different numbers.

**The mechanism, and it is cheaper than the certificate's route.**  A Hermitian `2×2` matrix is
`α·𝟙 + n·σ`, and its unordered spectral frame *is* the `ℝP²` point of its Bloch axis `n`.  Two
Hermitian matrices commute exactly when their Bloch axes are parallel — and that is an
elementary computation, not a spectral argument: the three components of `n_a × n_b` are the
`(0,0)` and `(0,1)` entries of the commutator.  So "compatible ⟹ same frame ⟹ same parameter"
comes out of `blochHerm_parallel_of_commute`, with no eigenvectors and no simultaneous
diagonalization.

The remaining structure is a reduction: in any occurrence of the product, the parameter may be
replaced by one reference value (`twistSeq_n2Tau_eq`), because at a *non-scalar* argument
commutation pins the parameter and at a *scalar* argument the product does not depend on the
parameter at all (`twistSeq_smul_one_left`).  That is what makes the article's convention
`t_a = 0` at the scalars free rather than a case to be checked.  Every axiom then reduces to
its constant-parameter counterpart in `Hermitian/Sequential.lean`.

* `blochHerm`, `blochPoint_eq_of_commute` — the frame of a Hermitian matrix, and the
  commutation criterion.
* `HermitianMat.twistSeq_smul_one_left` / `_right` — a scalar argument acts by scalar
  multiplication, whatever the parameter.
* `HermitianMat.twistSeq_smul_left` — positive homogeneity in the first argument, obtained from
  the constant-parameter S5 with a scalar left factor, so no functional-calculus scaling
  identity is needed anywhere in this file.
* `HermitianMat.twistSeq_zero_symm_param` — S4 at two parameters (the argument never touches
  the parameter).
* `n2Tau`, `n2Sp`, `n2SequentialProduct` — the parameter, the product, and the
  `SequentialProductOn` structure.

**What is NOT here:** S2 (`FirstArgContinuous`) for this product.  The parameter map `a ↦ t_a`
is discontinuous at the scalars, and the article's argument that the *product* is nonetheless
continuous there is a genuine estimate rather than plumbing; it is not attempted in this file.
So this file supplies `prop:n2-sufficiency`'s S1, S3–S7 and leaves its S2 open.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open scoped LinearAlgebra.Projectivization
open OrderUnitSpace

namespace RankTwo


/-- The Bloch axis of a Hermitian `2×2` matrix: the traceless part, in `σ`-coordinates. -/
def blochHerm (a : HermitianMat (Fin 2) ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * (a.mat 0 1).re, -(2 * (a.mat 0 1).im),
    (a.mat 0 0).re - (a.mat 1 1).re]

theorem blochHerm_apply_zero (a : HermitianMat (Fin 2) ℂ) :
    (WithLp.ofLp (blochHerm a)) 0 = 2 * (a.mat 0 1).re := rfl

theorem blochHerm_apply_one (a : HermitianMat (Fin 2) ℂ) :
    (WithLp.ofLp (blochHerm a)) 1 = -(2 * (a.mat 0 1).im) := rfl

theorem blochHerm_apply_two (a : HermitianMat (Fin 2) ℂ) :
    (WithLp.ofLp (blochHerm a)) 2 = (a.mat 0 0).re - (a.mat 1 1).re := rfl

/-- **Vanishing of the Bloch axis is scalarity**, in coordinates. -/
theorem blochHerm_eq_zero_iff (a : HermitianMat (Fin 2) ℂ) :
    blochHerm a = 0 ↔ (a.mat 0 1).re = 0 ∧ (a.mat 0 1).im = 0
      ∧ (a.mat 0 0).re = (a.mat 1 1).re := by
  constructor
  · intro h
    have k0 : (WithLp.ofLp (blochHerm a)) 0 = 0 := by rw [h]; rfl
    have k1 : (WithLp.ofLp (blochHerm a)) 1 = 0 := by rw [h]; rfl
    have k2 : (WithLp.ofLp (blochHerm a)) 2 = 0 := by rw [h]; rfl
    rw [blochHerm_apply_zero] at k0
    rw [blochHerm_apply_one] at k1
    rw [blochHerm_apply_two] at k2
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨k0, k1, k2⟩
    have m0 : (a 0 1).re = 0 := k0
    have m1 : (a 0 1).im = 0 := k1
    have m2 : (a 0 0).re = (a 1 1).re := k2
    apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
    funext i
    fin_cases i <;> simp [blochHerm, m0, m1, m2]

/-- A cross-product-zero pair of vectors in `ℝ³`, second one nonzero, is proportional.
Stated in scalar coordinates so no `Fin 3` case analysis leaks into the caller. -/
theorem exists_scalar_of_cross_zero {u0 u1 u2 v0 v1 v2 : ℝ}
    (hv : v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0)
    (c0 : u1 * v2 - u2 * v1 = 0) (c1 : u2 * v0 - u0 * v2 = 0)
    (c2 : u0 * v1 - u1 * v0 = 0) :
    ∃ c : ℝ, c * v0 = u0 ∧ c * v1 = u1 ∧ c * v2 = u2 := by
  by_cases h0 : v0 = 0
  · by_cases h1 : v1 = 0
    · have h2 : v2 ≠ 0 := by
        rcases hv with h | h | h
        · exact absurd h0 h
        · exact absurd h1 h
        · exact h
      have hu0 : u0 = 0 := by
        have : u0 * v2 = 0 := by rw [h0] at c1; linear_combination -c1
        exact (mul_eq_zero.mp this).resolve_right h2
      have hu1 : u1 = 0 := by
        have : u1 * v2 = 0 := by rw [h1] at c0; linear_combination c0
        exact (mul_eq_zero.mp this).resolve_right h2
      refine ⟨u2 / v2, ?_, ?_, ?_⟩
      · rw [h0, mul_zero, hu0]
      · rw [h1, mul_zero, hu1]
      · exact div_mul_cancel₀ _ h2
    · have hu0 : u0 = 0 := by
        have : u0 * v1 = 0 := by rw [h0] at c2; linear_combination c2
        exact (mul_eq_zero.mp this).resolve_right h1
      refine ⟨u1 / v1, ?_, ?_, ?_⟩
      · rw [h0, mul_zero, hu0]
      · exact div_mul_cancel₀ _ h1
      · rw [div_mul_eq_mul_div, div_eq_iff h1]
        linear_combination c0
  · refine ⟨u0 / v0, ?_, ?_, ?_⟩
    · exact div_mul_cancel₀ _ h0
    · rw [div_mul_eq_mul_div, div_eq_iff h0]
      linear_combination c2
    · rw [div_mul_eq_mul_div, div_eq_iff h0]
      linear_combination -c1

/-- **Commuting Hermitian `2×2` matrices have parallel Bloch axes.**  Elementary: the
`(0,0)` and `(0,1)` entries of the commutator are exactly the three components of the
cross product `n_a × n_b`. -/
theorem blochHerm_parallel_of_commute {a b : HermitianMat (Fin 2) ℂ}
    (h : Commute a.mat b.mat) (hb : blochHerm b ≠ 0) :
    ∃ c : ℝ, c • blochHerm b = blochHerm a := by
  -- the Hermitian relations: the off-diagonal entries are conjugate, the diagonal is real
  have ha10 : a.mat 1 0 = star (a.mat 0 1) := by
    have hh := congrFun (congrFun a.H 1) 0
    rw [Matrix.conjTranspose_apply] at hh
    exact hh.symm
  have hb10 : b.mat 1 0 = star (b.mat 0 1) := by
    have hh := congrFun (congrFun b.H 1) 0
    rw [Matrix.conjTranspose_apply] at hh
    exact hh.symm
  have hreal : ∀ (x : HermitianMat (Fin 2) ℂ) (i : Fin 2), (x.mat i i).im = 0 := by
    intro x i
    have hh := congrFun (congrFun x.H i) i
    rw [Matrix.conjTranspose_apply] at hh
    have := congrArg Complex.im hh
    simpa [Complex.star_def] using this
  have ha00 := hreal a 0
  have ha11 := hreal a 1
  have hb00 := hreal b 0
  have hb11 := hreal b 1
  -- the two commutator entries
  have e00 := congrFun (congrFun h.eq 0) 0
  have e01 := congrFun (congrFun h.eq 0) 1
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
    ha10, hb10] at e00
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e01
  have E1 : (a.mat 0 1).im * (b.mat 0 1).re = (a.mat 0 1).re * (b.mat 0 1).im := by
    have hh := congrArg Complex.im e00
    simp only [Complex.add_im, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im] at hh
    linarith [hh]
  have E2 : (b.mat 0 1).re * ((a.mat 0 0).re - (a.mat 1 1).re)
      = (a.mat 0 1).re * ((b.mat 0 0).re - (b.mat 1 1).re) := by
    have hh := congrArg Complex.re e01
    simp only [Complex.add_re, Complex.mul_re, ha00, hb00, ha11, hb11] at hh
    linarith [hh]
  have E3 : (b.mat 0 1).im * ((a.mat 0 0).re - (a.mat 1 1).re)
      = (a.mat 0 1).im * ((b.mat 0 0).re - (b.mat 1 1).re) := by
    have hh := congrArg Complex.im e01
    simp only [Complex.add_im, Complex.mul_im, ha00, hb00, ha11, hb11] at hh
    linarith [hh]
  -- the second axis is nonzero in coordinates
  have hvne : 2 * (b.mat 0 1).re ≠ 0 ∨ -(2 * (b.mat 0 1).im) ≠ 0
      ∨ (b.mat 0 0).re - (b.mat 1 1).re ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k0, k1, k2⟩ := hcon
    exact hb ((blochHerm_eq_zero_iff b).mpr ⟨by linarith, by linarith, by linarith⟩)
  obtain ⟨c, k0, k1, k2⟩ := exists_scalar_of_cross_zero
    (u0 := 2 * (a.mat 0 1).re) (u1 := -(2 * (a.mat 0 1).im))
    (u2 := (a.mat 0 0).re - (a.mat 1 1).re)
    (v0 := 2 * (b.mat 0 1).re) (v1 := -(2 * (b.mat 0 1).im))
    (v2 := (b.mat 0 0).re - (b.mat 1 1).re)
    hvne (by linear_combination 2 * E3) (by linear_combination 2 * E2)
    (by linear_combination 4 * E1)
  refine ⟨c, ?_⟩
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i
  · show c * (2 * (b.mat 0 1).re) = 2 * (a.mat 0 1).re
    exact k0
  · show c * (-(2 * (b.mat 0 1).im)) = -(2 * (a.mat 0 1).im)
    exact k1
  · show c * ((b.mat 0 0).re - (b.mat 1 1).re) = (a.mat 0 0).re - (a.mat 1 1).re
    exact k2

/-- **Commuting non-scalar Hermitian `2×2` matrices determine the same point of `ℝP²`.** -/
theorem blochPoint_eq_of_commute {a b : HermitianMat (Fin 2) ℂ}
    (h : Commute a.mat b.mat) (ha : blochHerm a ≠ 0) (hb : blochHerm b ≠ 0) :
    RP2.mk (blochHerm a) ha = RP2.mk (blochHerm b) hb :=
  (RP2.mk_eq_mk_iff ha hb).mpr (blochHerm_parallel_of_commute h hb)

end RankTwo

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The continuous functional calculus at a scalar. -/
theorem cfc_smul_one (c : ℝ) (f : ℝ → ℝ) :
    ((c • (1 : HermitianMat n ℂ)).cfc f) = f c • 1 := by
  rw [← HermitianMat.cfc_const_mul_id (r := c) (A := (1 : HermitianMat n ℂ)),
    ← HermitianMat.cfc_comp_apply, HermitianMat.cfc_apply_one, mul_one]

/-- The twist factor at a scalar is a scalar. -/
theorem twistFactor_smul_one (c t : ℝ) :
    twistFactor (c • (1 : HermitianMat n ℂ)) t
      = (⟨Real.sqrt c * Real.cos (t * Real.log c),
          Real.sqrt c * Real.sin (t * Real.log c)⟩ : ℂ) • (1 : Matrix n n ℂ) := by
  have hscalar : (⟨Real.sqrt c * Real.cos (t * Real.log c),
        Real.sqrt c * Real.sin (t * Real.log c)⟩ : ℂ)
      = ((Real.sqrt c * Real.cos (t * Real.log c) : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt c * Real.sin (t * Real.log c) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
  unfold twistFactor twistRe twistIm
  rw [cfc_smul_one, cfc_smul_one, HermitianMat.mat_smul, HermitianMat.mat_smul,
    HermitianMat.mat_one, hscalar, add_smul, ← Complex.coe_smul, ← Complex.coe_smul,
    smul_smul]

/-- **The twist product with a scalar left argument is scalar multiplication**, for every
twist parameter.  This is what makes the frame function's value at the scalars irrelevant to
the operation, so the article's convention `t_a = 0` there costs nothing. -/
theorem twistSeq_smul_one_left {c : ℝ} (hc : 0 ≤ c) (t : ℝ) (b : HermitianMat n ℂ) :
    twistSeq t (c • (1 : HermitianMat n ℂ)) b = c • b := by
  have hsq : (Real.sqrt c * Real.cos (t * Real.log c)) ^ 2
      + (Real.sqrt c * Real.sin (t * Real.log c)) ^ 2 = c := by
    have h1 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
    have h2 := Real.sin_sq_add_cos_sq (t * Real.log c)
    nlinarith [h1, h2]
  have hmu : star (⟨Real.sqrt c * Real.cos (t * Real.log c),
        Real.sqrt c * Real.sin (t * Real.log c)⟩ : ℂ)
      * (⟨Real.sqrt c * Real.cos (t * Real.log c),
        Real.sqrt c * Real.sin (t * Real.log c)⟩ : ℂ) = ((c : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;>
      nlinarith [hsq]
  ext1
  rw [twistSeq_mat, twistFactor_smul_one, HermitianMat.mat_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_smul, hmu, Complex.coe_smul]

/-- **The twist product with a scalar right argument is scalar multiplication.** -/
theorem twistSeq_smul_one_right {a : HermitianMat n ℂ} (ha : 0 ≤ a) (t c : ℝ) :
    twistSeq t a (c • (1 : HermitianMat n ℂ)) = c • a := by
  ext1
  rw [twistSeq_mat, HermitianMat.mat_smul, HermitianMat.mat_smul, HermitianMat.mat_one,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, twistFactor_mul_conjTranspose ha]

/-- **Positive homogeneity of the twist product in its first argument** — obtained from the
constant-parameter S5 with a scalar left factor, so no functional-calculus scaling identity
is needed. -/
theorem twistSeq_smul_left {c : ℝ} (hc : 0 ≤ c) {a : HermitianMat n ℂ} (ha : 0 ≤ a)
    (t : ℝ) (b : HermitianMat n ℂ) :
    twistSeq t (c • a) b = c • twistSeq t a b := by
  have hs : (0 : HermitianMat n ℂ) ≤ c • (1 : HermitianMat n ℂ) := smul_nonneg hc zero_le_one
  have hcomm : twistSeq t (c • (1 : HermitianMat n ℂ)) a
      = twistSeq t a (c • (1 : HermitianMat n ℂ)) := by
    rw [twistSeq_smul_one_left hc, twistSeq_smul_one_right ha]
  have key := twistSeq_assoc_of_comm t hs ha hcomm b
  rw [twistSeq_smul_one_left hc t (twistSeq t a b), twistSeq_smul_one_left hc t a] at key
  exact key.symm

end HermitianMat

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **S4 at two parameters.**  The zero-symmetry argument never touches the parameter: it runs
entirely through `trace_twistSeq`, which is parameter-independent. -/
theorem twistSeq_zero_symm_param {a b : HermitianMat n ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {t t' : ℝ} (h : twistSeq t a b = 0) : twistSeq t' b a = 0 := by
  apply eq_zero_of_nonneg_trace_zero (twistSeq_nonneg t' b ha)
  rw [trace_twistSeq hb a, Matrix.trace_mul_comm]
  rw [← trace_twistSeq ha b t, h]
  simp

end HermitianMat

namespace RankTwo

open HermitianMat

theorem blochHerm_smul (c : ℝ) (a : HermitianMat (Fin 2) ℂ) :
    blochHerm (c • a) = c • blochHerm a := by
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;> simp [blochHerm] <;> ring

theorem blochHerm_one : blochHerm (1 : HermitianMat (Fin 2) ℂ) = 0 := by
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;> simp [blochHerm, Matrix.one_apply]

theorem blochHerm_sub (a b : HermitianMat (Fin 2) ℂ) :
    blochHerm (a - b) = blochHerm a - blochHerm b := by
  have e : ∀ i j : Fin 2, (a - b) i j = a i j - b i j := by
    intro i j
    show (a - b).mat i j = a.mat i j - b.mat i j
    rw [HermitianMat.mat_sub]
    rfl
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;> simp [blochHerm, e] <;> ring

theorem blochHerm_add (a b : HermitianMat (Fin 2) ℂ) :
    blochHerm (a + b) = blochHerm a + blochHerm b := by
  have e : ∀ i j : Fin 2, (a + b) i j = a i j + b i j := by
    intro i j
    show (a + b).mat i j = a.mat i j + b.mat i j
    rw [HermitianMat.mat_add]
    rfl
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;> simp [blochHerm, e] <;> ring

/-- Complementation negates the Bloch axis, hence fixes the `ℝP²` point. -/
theorem blochHerm_one_sub (b : HermitianMat (Fin 2) ℂ) :
    blochHerm (1 - b) = -blochHerm b := by
  rw [blochHerm_sub, blochHerm_one, zero_sub]

/-- A complex number with vanishing imaginary part is its own real part. -/
theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = ((z.re : ℝ) : ℂ) :=
  Complex.ext rfl (by simp [hz])

/-- **A vanishing Bloch axis means the matrix is a real scalar.** -/
theorem eq_smul_one_of_blochHerm_eq_zero {a : HermitianMat (Fin 2) ℂ} (h : blochHerm a = 0) :
    a = ((a.mat 0 0).re) • (1 : HermitianMat (Fin 2) ℂ) := by
  obtain ⟨k0, k1, k2⟩ := (blochHerm_eq_zero_iff a).mp h
  have h01 : a.mat 0 1 = 0 := Complex.ext k0 k1
  have h10 : a.mat 1 0 = 0 := by
    have hh := congrFun (congrFun a.H 1) 0
    rw [Matrix.conjTranspose_apply, h01] at hh
    simpa using hh.symm
  have hdiag : ∀ i : Fin 2, (a.mat i i).im = 0 := by
    intro i
    have hh := congrFun (congrFun a.H i) i
    rw [Matrix.conjTranspose_apply] at hh
    have := congrArg Complex.im hh
    simpa [Complex.star_def] using this
  ext1
  rw [HermitianMat.mat_smul, HermitianMat.mat_one, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul, mul_one]
    exact eq_ofReal_re_of_im_eq_zero (hdiag 0)
  · rw [Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero]
    exact h01
  · rw [Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero]
    exact h10
  · rw [Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul, mul_one,
      eq_ofReal_re_of_im_eq_zero (hdiag 1), k2]

/-- **The frame-dependent twist parameter** of `prop:n2-sufficiency`: the article's `t_a`,
read off the Bloch axis of `a`, and `0` at the scalars (where the operation does not see it,
`twistSeq_smul_one_left`). -/
def n2Tau (t : C(RP2, ℝ)) (a : HermitianMat (Fin 2) ℂ) : ℝ :=
  letI := Classical.dec (blochHerm a = 0)
  if h : blochHerm a = 0 then 0 else t (RP2.mk (blochHerm a) h)

theorem n2Tau_of_ne_zero (t : C(RP2, ℝ)) {a : HermitianMat (Fin 2) ℂ} (h : blochHerm a ≠ 0) :
    n2Tau t a = t (RP2.mk (blochHerm a) h) := by
  rw [n2Tau, dif_neg h]

/-- **Commuting non-scalar effects carry the same parameter.** -/
theorem n2Tau_eq_of_commute (t : C(RP2, ℝ)) {a b : HermitianMat (Fin 2) ℂ}
    (hab : Commute a.mat b.mat) (ha : blochHerm a ≠ 0) (hb : blochHerm b ≠ 0) :
    n2Tau t a = n2Tau t b := by
  rw [n2Tau_of_ne_zero t ha, n2Tau_of_ne_zero t hb, blochPoint_eq_of_commute hab ha hb]

/-- **The reduction lemma.**  In any occurrence of the frame-dependent product, the parameter
may be replaced by a reference value `T`, provided `T` is the parameter at every *non-scalar*
argument — at the scalars the product does not depend on the parameter at all. -/
theorem twistSeq_n2Tau_eq (t : C(RP2, ℝ)) {x : HermitianMat (Fin 2) ℂ} (hx : 0 ≤ x)
    {T : ℝ} (hT : blochHerm x ≠ 0 → n2Tau t x = T) (b : HermitianMat (Fin 2) ℂ) :
    twistSeq (n2Tau t x) x b = twistSeq T x b := by
  by_cases h : blochHerm x = 0
  · have hxs := eq_smul_one_of_blochHerm_eq_zero h
    have hc : (0 : ℝ) ≤ (x.mat 0 0).re := by
      have := HermitianMat.zero_le_iff.mp hx
      have hd : (0 : ℂ) ≤ x.mat 0 0 := Matrix.PosSemidef.diag_nonneg this
      exact (Complex.le_def.mp hd).1
    rw [hxs, twistSeq_smul_one_left hc, twistSeq_smul_one_left hc]
  · rw [hT h]

end RankTwo

namespace RankTwo

open HermitianMat

theorem n2Tau_of_eq_zero (t : C(RP2, ℝ)) {a : HermitianMat (Fin 2) ℂ} (h : blochHerm a = 0) :
    n2Tau t a = 0 := by
  rw [n2Tau, dif_pos h]

/-- The parameter is scale-invariant: `ℝP²` quotients by every nonzero real scaling. -/
theorem n2Tau_smul (t : C(RP2, ℝ)) {γ : ℝ} (hγ : γ ≠ 0) (b : HermitianMat (Fin 2) ℂ) :
    n2Tau t (γ • b) = n2Tau t b := by
  by_cases h : blochHerm b = 0
  · rw [n2Tau_of_eq_zero t h,
      n2Tau_of_eq_zero t (by rw [blochHerm_smul, h, smul_zero] : blochHerm (γ • b) = 0)]
  · have h' : blochHerm (γ • b) ≠ 0 := by
      rw [blochHerm_smul]; exact smul_ne_zero hγ h
    rw [n2Tau_of_ne_zero t h', n2Tau_of_ne_zero t h]
    congr 1
    exact (RP2.mk_eq_mk_iff h' h).mpr ⟨γ, by rw [blochHerm_smul]⟩

/-- **The frame-dependent product of `prop:n2-sufficiency`**: the twist product whose parameter
is read off the left argument's own Bloch axis. -/
def n2Sp (t : C(RP2, ℝ)) (a b : HermitianMat (Fin 2) ℂ) : HermitianMat (Fin 2) ℂ :=
  twistSeq (n2Tau t a) a b

/-- A scalar left argument acts by scalar multiplication, whatever the frame function. -/
theorem n2Sp_smul_one_left (t : C(RP2, ℝ)) {γ : ℝ} (hγ : 0 ≤ γ) (b : HermitianMat (Fin 2) ℂ) :
    n2Sp t (γ • (1 : HermitianMat (Fin 2) ℂ)) b = γ • b :=
  twistSeq_smul_one_left hγ _ b

/-- A scalar right argument likewise. -/
theorem n2Sp_smul_one_right (t : C(RP2, ℝ)) {x : HermitianMat (Fin 2) ℂ} (hx : 0 ≤ x) (γ : ℝ) :
    n2Sp t x (γ • (1 : HermitianMat (Fin 2) ℂ)) = γ • x :=
  twistSeq_smul_one_right hx _ γ

theorem n2Sp_zero_left (t : C(RP2, ℝ)) (c : HermitianMat (Fin 2) ℂ) :
    n2Sp t (0 : HermitianMat (Fin 2) ℂ) c = 0 := by
  calc n2Sp t (0 : HermitianMat (Fin 2) ℂ) c
      = n2Sp t ((0 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) c := by rw [zero_smul]
    _ = (0 : ℝ) • c := n2Sp_smul_one_left t le_rfl c
    _ = 0 := zero_smul ℝ c

/-- **Positive homogeneity of the frame-dependent product**, from `ℝP²`-scale-invariance of the
parameter plus homogeneity at a fixed parameter. -/
theorem n2Sp_smul_left (t : C(RP2, ℝ)) {γ : ℝ} (hγ : 0 ≤ γ)
    {b : HermitianMat (Fin 2) ℂ} (hb : 0 ≤ b) (c : HermitianMat (Fin 2) ℂ) :
    n2Sp t (γ • b) c = γ • n2Sp t b c := by
  rcases eq_or_ne γ 0 with rfl | hγ0
  · rw [zero_smul, zero_smul, n2Sp_zero_left]
  · unfold n2Sp
    rw [n2Tau_smul t hγ0, twistSeq_smul_left hγ hb]

/-- Every effect that is a scalar is a nonnegative multiple of the unit. -/
theorem exists_smul_one_of_blochHerm_eq_zero {a : HermitianMat (Fin 2) ℂ} (ha : 0 ≤ a)
    (h : blochHerm a = 0) :
    ∃ γ : ℝ, 0 ≤ γ ∧ a = γ • (1 : HermitianMat (Fin 2) ℂ) := by
  refine ⟨(a.mat 0 0).re, ?_, eq_smul_one_of_blochHerm_eq_zero h⟩
  have hd : (0 : ℂ) ≤ a.mat 0 0 :=
    Matrix.PosSemidef.diag_nonneg (HermitianMat.zero_le_iff.mp ha)
  simpa using (Complex.le_def.mp hd).1

theorem commute_of_n2Sp_comm (t : C(RP2, ℝ)) {a b : HermitianMat (Fin 2) ℂ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : n2Sp t a b = n2Sp t b a) : Commute a.mat b.mat :=
  HermitianMat.commute_of_twistSeq_comm_param ha hb h

/-! ### The seven axioms -/

theorem n2Sp_assoc (t : C(RP2, ℝ)) {a b c : HermitianMat (Fin 2) ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hcomm : n2Sp t a b = n2Sp t b a) :
    n2Sp t a (n2Sp t b c) = n2Sp t (n2Sp t a b) c := by
  by_cases hane : blochHerm a = 0
  · obtain ⟨γ, hγ0, rfl⟩ := exists_smul_one_of_blochHerm_eq_zero ha.1 hane
    rw [n2Sp_smul_one_left t hγ0, n2Sp_smul_one_left t hγ0, n2Sp_smul_left t hγ0 hb.1]
  · have hab : Commute a.mat b.mat := commute_of_n2Sp_comm t ha.1 hb.1 hcomm
    have hT : twistSeq (n2Tau t a) a b = twistSeq (n2Tau t a) b a :=
      twistSeq_comm_of_commute ha.1 hb.1 hab _
    have hab2 : Commute a.mat (twistSeq (n2Tau t a) a b).mat := by
      rw [twistSeq_mat_of_commute ha.1 hab]
      exact (Commute.refl a.mat).mul_right hab
    unfold n2Sp
    rw [twistSeq_n2Tau_eq t hb.1
        (fun hx => n2Tau_eq_of_commute t hab.symm hx hane) c,
      twistSeq_n2Tau_eq t (twistSeq_nonneg _ a hb.1)
        (fun hx => n2Tau_eq_of_commute t hab2.symm hx hane) c]
    exact twistSeq_assoc_of_comm _ ha.1 hb.1 hT c

theorem n2Sp_compat_ortho (t : C(RP2, ℝ)) {a b : HermitianMat (Fin 2) ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hcomm : n2Sp t a b = n2Sp t b a) :
    n2Sp t a (1 - b) = n2Sp t (1 - b) a := by
  have hb1 : b ≤ (1 : HermitianMat (Fin 2) ℂ) := by
    have := hb.2; rwa [HermitianMat.ousUnit_eq_one] at this
  by_cases hane : blochHerm a = 0
  · obtain ⟨γ, hγ0, rfl⟩ := exists_smul_one_of_blochHerm_eq_zero ha.1 hane
    rw [n2Sp_smul_one_left t hγ0, n2Sp_smul_one_right t (sub_nonneg.mpr hb1) γ]
  · have hab : Commute a.mat b.mat := commute_of_n2Sp_comm t ha.1 hb.1 hcomm
    have hasub : Commute a.mat (1 - b).mat := by
      rw [HermitianMat.mat_sub, HermitianMat.mat_one]
      exact (Commute.one_right _).sub_right hab
    have hT : twistSeq (n2Tau t a) a b = twistSeq (n2Tau t a) b a :=
      twistSeq_comm_of_commute ha.1 hb.1 hab _
    unfold n2Sp
    rw [twistSeq_n2Tau_eq t (sub_nonneg.mpr hb1)
      (fun hx => n2Tau_eq_of_commute t hasub.symm hx hane) a]
    exact twistSeq_compat_one_sub _ ha.1 hb.1 hb1 hT

theorem n2Sp_compat_add (t : C(RP2, ℝ)) {a b c : HermitianMat (Fin 2) ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hc : IsEffect c)
    (h1 : n2Sp t a b = n2Sp t b a) (h2 : n2Sp t a c = n2Sp t c a) :
    n2Sp t a (b + c) = n2Sp t (b + c) a := by
  by_cases hane : blochHerm a = 0
  · obtain ⟨γ, hγ0, rfl⟩ := exists_smul_one_of_blochHerm_eq_zero ha.1 hane
    rw [n2Sp_smul_one_left t hγ0, n2Sp_smul_one_right t (_root_.add_nonneg hb.1 hc.1) γ]
  · have hab : Commute a.mat b.mat := commute_of_n2Sp_comm t ha.1 hb.1 h1
    have hac : Commute a.mat c.mat := commute_of_n2Sp_comm t ha.1 hc.1 h2
    have habc : Commute a.mat (b + c).mat := by
      rw [HermitianMat.mat_add]; exact hab.add_right hac
    have hTb : twistSeq (n2Tau t a) a b = twistSeq (n2Tau t a) b a :=
      twistSeq_comm_of_commute ha.1 hb.1 hab _
    have hTc : twistSeq (n2Tau t a) a c = twistSeq (n2Tau t a) c a :=
      twistSeq_comm_of_commute ha.1 hc.1 hac _
    unfold n2Sp
    rw [twistSeq_n2Tau_eq t (_root_.add_nonneg hb.1 hc.1)
      (fun hx => n2Tau_eq_of_commute t habc.symm hx hane) a]
    exact twistSeq_compat_add _ ha.1 hb.1 hc.1 hTb hTc

theorem n2Sp_compat_sp (t : C(RP2, ℝ)) {a b c : HermitianMat (Fin 2) ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hc : IsEffect c)
    (h1 : n2Sp t a b = n2Sp t b a) (h2 : n2Sp t a c = n2Sp t c a) :
    n2Sp t a (n2Sp t b c) = n2Sp t (n2Sp t b c) a := by
  by_cases hane : blochHerm a = 0
  · obtain ⟨γ, hγ0, rfl⟩ := exists_smul_one_of_blochHerm_eq_zero ha.1 hane
    rw [n2Sp_smul_one_left t hγ0,
      n2Sp_smul_one_right t
        (show (0 : HermitianMat (Fin 2) ℂ) ≤ n2Sp t b c from twistSeq_nonneg _ b hc.1) γ]
  · have hab : Commute a.mat b.mat := commute_of_n2Sp_comm t ha.1 hb.1 h1
    have hac : Commute a.mat c.mat := commute_of_n2Sp_comm t ha.1 hc.1 h2
    have hbc : Commute a.mat (twistSeq (n2Tau t a) b c).mat := by
      rw [twistSeq_mat]
      refine ((commute_twistFactor hab _).mul_right hac).mul_right ?_
      rw [twistFactor_conjTranspose]
      exact commute_twistFactor hab _
    have hTb : twistSeq (n2Tau t a) a b = twistSeq (n2Tau t a) b a :=
      twistSeq_comm_of_commute ha.1 hb.1 hab _
    have hTc : twistSeq (n2Tau t a) a c = twistSeq (n2Tau t a) c a :=
      twistSeq_comm_of_commute ha.1 hc.1 hac _
    unfold n2Sp
    rw [twistSeq_n2Tau_eq t hb.1 (fun hx => n2Tau_eq_of_commute t hab.symm hx hane) c,
      twistSeq_n2Tau_eq t (twistSeq_nonneg _ b hc.1)
        (fun hx => n2Tau_eq_of_commute t hbc.symm hx hane) a]
    exact twistSeq_compat_sp _ ha.1 hb.1 hc.1 hTb hTc

/-- **`prop:n2-sufficiency`, algebraic core**: every continuous `t : ℝP² → ℝ` gives an
S1, S3–S7 sequential product on `H_2(ℂ)` whose twist parameter is read off the left argument's
frame. -/
def n2SequentialProduct (t : C(RP2, ℝ)) : SequentialProductOn (HermitianMat (Fin 2) ℂ) where
  sp := n2Sp t
  sp_add_right := fun _ _ _ _ => twistSeq_add_right _ _ _ _
  sp_unit_left := fun _ => twistSeq_one_left _ _
  sp_zero_symm := fun ha hb h => twistSeq_zero_symm_param ha.1 hb.1 h
  sp_assoc_of_compatible := fun ha hb _ hcomm => n2Sp_assoc t ha hb hcomm
  compatible_ortho := fun ha hb hcomm => n2Sp_compat_ortho t ha hb hcomm
  compatible_add := fun ha hb hc _ h1 h2 => n2Sp_compat_add t ha hb hc h1 h2
  compatible_sp := fun ha hb hc h1 h2 => n2Sp_compat_sp t ha hb hc h1 h2
  sp_effect := fun ha hb => twistSeq_isEffect _ ha.1 ha.2 hb.1 hb.2

/-! ### The bridge: the Bloch axis of a spectral effect is the tree's `blochFrame`

★★ ARC-8 block 8.1(b).  Without this the file would only be *stating* that the parameter is
read off "the frame of `a`"; with it, the frame in question is the one the tree already
constructed — the `ℝP²` image under `blochFrame` of the first-column ray of a diagonalizing
unitary.  So `n2Sp` is `prop:n2-sufficiency`'s operation and not a lookalike. -/

/-- The first column of a `2×2` unitary, as a vector of `ℂ²`. -/
def firstCol (U : Matrix.unitaryGroup (Fin 2) ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)

theorem firstCol_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ) : firstCol U ≠ 0 := by
  intro h
  have hf : ∀ i, (U : Matrix (Fin 2) (Fin 2) ℂ) i 0 = 0 := by
    intro i
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa [firstCol] using this
  have hU : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h00 := congrFun (congrFun hU 0) 0
  rw [Matrix.mul_apply] at h00
  simp only [Matrix.star_apply, hf, star_zero, mul_zero, Finset.sum_const_zero,
    Matrix.one_apply_eq] at h00
  exact one_ne_zero h00.symm

/-- The unordered spectral frame presented by a unitary, as a point of `ℂP¹`. -/
def colFrame (U : Matrix.unitaryGroup (Fin 2) ℂ) : QubitFrame :=
  Projectivization.mk ℂ (firstCol U) (firstCol_ne_zero U)

/-- The entries of the first spectral projection: it is the rank-one projection of the first
column. -/
theorem frameMap_mat_apply (U : Matrix.unitaryGroup (Fin 2) ℂ) (i j : Fin 2) :
    (Necessity.frameMap U).mat i j
      = (U : Matrix (Fin 2) (Fin 2) ℂ) i 0 * star ((U : Matrix (Fin 2) (Fin 2) ℂ) j 0) := by
  rw [Necessity.frameMap, Necessity.adU_apply, HermitianMat.conj_apply_mat,
    Necessity.frameProj_mat_eq_single]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.conjTranspose_apply]

/-- **The Bloch axis of the first spectral projection is the Bloch vector of the first
column.** -/
theorem blochHerm_frameMap (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    blochHerm (Necessity.frameMap U) = blochE (firstCol U) := by
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  have e01 : (Necessity.frameMap U) 0 1
      = (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0) :=
    frameMap_mat_apply U 0 1
  have e00 : (Necessity.frameMap U) 0 0
      = (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) :=
    frameMap_mat_apply U 0 0
  have e11 : (Necessity.frameMap U) 1 1
      = (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * star ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0) :=
    frameMap_mat_apply U 1 1
  fin_cases i <;>
    simp [blochHerm, blochE, blochVec, firstCol, e01, e00, e11, Complex.star_def,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring

/-- The two-level family, split off the frame projection. -/
theorem diagFamily_fin2_eq (r : Fin 2 → ℝ) :
    Necessity.diagFamily r
      = (Real.exp (r 1)) • (1 : HermitianMat (Fin 2) ℂ)
        + (Real.exp (r 0) - Real.exp (r 1)) • Necessity.frameProj (0 : Fin 2) := by
  ext1
  rw [Necessity.diagFamily_mat, HermitianMat.mat_add, HermitianMat.mat_smul,
    HermitianMat.mat_smul, HermitianMat.mat_one, Necessity.frameProj_mat, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Complex.real_smul] <;> ring

theorem adU_smul (U : Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ) (x : HermitianMat (Fin 2) ℂ) :
    Necessity.adU U (c • x) = c • Necessity.adU U x :=
  map_smul (HermitianMat.conjLinear ℝ U) c x

/-- **The Bloch axis of a spectral effect is a real multiple of the frame's Bloch vector.** -/
theorem blochHerm_adU_diagFamily (U : Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 2 → ℝ) :
    blochHerm (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r))
      = (Real.exp (r 0) - Real.exp (r 1)) • blochE (firstCol U) := by
  rw [diagFamily_fin2_eq, Necessity.adU_add, adU_smul, adU_smul,
    Necessity.adU_unital (Necessity.unitaryGroup_mul_conjTranspose U),
    blochHerm_add, blochHerm_smul, blochHerm_smul, blochHerm_one, smul_zero, zero_add]
  rw [show Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.frameProj (0 : Fin 2))
      = Necessity.frameMap U from rfl, blochHerm_frameMap]

theorem blochE_firstCol_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    blochE (firstCol U) ≠ 0 := blochE_ne_zero (firstCol_ne_zero U)

/-- **A spectral effect with distinct eigenvalues has the frame's `ℝP²` point.** -/
theorem blochHerm_adU_diagFamily_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ) {r : Fin 2 → ℝ}
    (hr : r 0 ≠ r 1) :
    blochHerm (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) ≠ 0 := by
  rw [blochHerm_adU_diagFamily]
  refine smul_ne_zero ?_ (blochE_firstCol_ne_zero U)
  rw [sub_ne_zero, ne_eq, Real.exp_eq_exp]
  exact hr

theorem n2Tau_adU_diagFamily (t : C(RP2, ℝ)) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    {r : Fin 2 → ℝ} (hr : r 0 ≠ r 1) :
    n2Tau t (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r))
      = t (blochFrame (colFrame U)) := by
  rw [n2Tau_of_ne_zero t (blochHerm_adU_diagFamily_ne_zero U hr)]
  congr 1
  rw [colFrame, blochFrame_mk]
  refine (RP2.mk_eq_mk_iff _ (blochE_firstCol_ne_zero U)).mpr
    ⟨Real.exp (r 0) - Real.exp (r 1), ?_⟩
  rw [blochHerm_adU_diagFamily]

/-- **`prop:n2-sufficiency`, the article's statement of the operation**: at every spectral
effect the product is the twist product whose parameter is `t` evaluated at that effect's
frame — including at the degenerate spectra, where the effect is a scalar and the parameter is
invisible to the operation. -/
theorem n2Sp_eq_twistSeq_at_frame (t : C(RP2, ℝ)) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (r : Fin 2 → ℝ) (b : HermitianMat (Fin 2) ℂ) :
    n2Sp t (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b
      = HermitianMat.twistSeq (t (blochFrame (colFrame U)))
        (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b := by
  rcases eq_or_ne (r 0) (r 1) with hr | hr
  · -- degenerate spectrum: the effect is a scalar, so no parameter is visible
    have hscal : Necessity.diagFamily r
        = (Real.exp (r 0)) • (1 : HermitianMat (Fin 2) ℂ) := by
      rw [diagFamily_fin2_eq, hr, sub_self, zero_smul, add_zero]
    have hA : Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)
        = (Real.exp (r 0)) • (1 : HermitianMat (Fin 2) ℂ) := by
      rw [hscal, adU_smul, Necessity.adU_unital (Necessity.unitaryGroup_mul_conjTranspose U)]
    rw [hA, n2Sp_smul_one_left t (Real.exp_nonneg _),
      HermitianMat.twistSeq_smul_one_left (Real.exp_nonneg _)]
  · rw [n2Sp, n2Tau_adU_diagFamily t U hr]

/-- **`prop:n2-sufficiency`, algebraic core, in the article's existential form.**  Every
continuous `t : ℝP² → ℝ` is realized by an S1, S3–S7 sequential product on `H_2(ℂ)` whose
value at each spectral effect is the twist product at that effect's frame parameter.

★ S2 is NOT part of this statement; see the module docstring. -/
theorem exists_sequentialProduct_of_continuous_moduli (t : C(RP2, ℝ)) :
    ∃ P : SequentialProductOn (HermitianMat (Fin 2) ℂ),
      ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 2 → ℝ) (b : HermitianMat (Fin 2) ℂ),
        P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b
          = HermitianMat.twistSeq (t (blochFrame (colFrame U)))
            (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b :=
  ⟨n2SequentialProduct t, fun U r b => n2Sp_eq_twistSeq_at_frame t U r b⟩

end RankTwo
