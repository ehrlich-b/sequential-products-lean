/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.Bloch
import RadicalRelativity.Necessity.FrameConstancy
import RadicalRelativity.Hermitian.CfcSqrtContinuous
import RadicalRelativity.Necessity.OrderUnitS2

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

**S2 is here too** (`n2SequentialProduct_firstArgContinuous`), so this file supplies the whole of
`prop:n2-sufficiency`.  ★ An earlier version of this docstring said S2 was left open because "the
article's argument that the product is nonetheless continuous there is a genuine estimate rather
than plumbing".  There *is* a genuine analytic input — joint continuity in (parameter, matrix) — but
the predicted near-the-scalars comparison is **not needed**: at a scalar the product does not depend
on the parameter, so it is *constant in the parameter* there, and joint continuity plus compactness
of `[-K,K] × effects` gives a modulus of continuity in the matrix that is uniform in the parameter.
**The parameter never has to converge**, and the scalar lemma that made the algebra free makes the
analysis free.
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

/-! ### Non-collapse: the frame-dependent product is not a constant twist

★★★ New 2026-08-09 (ARC-8 checkpoint 1), and it exists because a cold reviewer named its absence as
the most dangerous thing about this row.  Everything above certifies that the *axioms* hold for an
arbitrary `t`; nothing above rules out that the resulting operation is secretly some single
`twistSeq s`, in which case row 30 would carry none of its intended force.

★ **Why the tree's existing frame-dependence theorem did not cover it.**
`RankTwo.sp_luders_ne_unit_twist` (`RankTwo/Separation.lean`) is `thm:qubit-boundary`(iii) — "frame
dependence is real at the level of the operation" — but it lives in the **entry-level encoding**
`MasterTheorem.RankTwo.sp = Fdiag · b · Fdiagᴴ`, and no theorem in the tree identifies that family
with `HermitianMat.twistSeq`.  So rows 30 and 31 were statements about two objects the tree never
linked, and a reader combining them would have concluded more than was proved.  The separation below
is in the `twistSeq` encoding, which is the one row 30 uses.

★ Scope, stated so it is not overread: this proves the product is not **literally** any constant
twist product.  The article's clause (iii) is stronger — no pair `(Φ, t)` with `Φ` a unital order
automorphism conjugates it to a constant twist — and that stronger form is not proved here. -/

/-- **The twist product separates its parameter**, on the diagonal family with a freely chosen
spectral gap.  The gap is chosen so the phase difference is exactly `π`, which is why no `2π`
ambiguity survives. -/
theorem exists_twistSeq_diagFamily_ne {t₁ t₂ : ℝ} (h : t₁ ≠ t₂) :
    ∃ (r : Fin 2 → ℝ) (b : HermitianMat (Fin 2) ℂ),
      HermitianMat.twistSeq t₁ (Necessity.diagFamily r) b
        ≠ HermitianMat.twistSeq t₂ (Necessity.diagFamily r) b := by
  have hd : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h
  set δ : ℝ := Real.pi / (t₁ - t₂) with hδ
  have hphase : (t₁ - t₂) * δ = Real.pi := by
    rw [hδ]; field_simp
  refine ⟨fun k => if k = 0 then δ else 0, Necessity.pairProj 0 1, ?_⟩
  intro hcon
  have hentry := congrFun (congrFun (congrArg HermitianMat.mat hcon) 0) 1
  rw [Necessity.twistSeq_diagFamily_entry, Necessity.twistSeq_diagFamily_entry] at hentry
  simp only [if_pos, if_neg (by decide : ¬ (1 : Fin 2) = 0), Real.exp_zero, Real.sqrt_one,
    Complex.ofReal_one, one_mul, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    star_one] at hentry
  -- cancel the (nonzero) amplitude and the (nonzero) probe entry
  have hamp : ((Real.sqrt (Real.exp δ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Real.exp_pos _)))
  have hb : (Necessity.pairProj (0 : Fin 2) 1) 0 1 ≠ 0 := by
    have := Necessity.pairProj_entry (by decide : (0 : Fin 2) ≠ 1)
    rw [show (Necessity.pairProj (0 : Fin 2) 1) 0 1
        = (Necessity.pairProj (0 : Fin 2) 1).mat 0 1 from rfl, this]
    norm_num
  have hexp : Complex.exp (((t₁ * δ : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t₂ * δ : ℝ) : ℂ) * Complex.I) := by
    have h1 : ((Real.sqrt (Real.exp δ) : ℝ) : ℂ)
          * (Complex.exp (((t₁ * δ : ℝ) : ℂ) * Complex.I)
            * (Necessity.pairProj (0 : Fin 2) 1) 0 1)
        = ((Real.sqrt (Real.exp δ) : ℝ) : ℂ)
          * (Complex.exp (((t₂ * δ : ℝ) : ℂ) * Complex.I)
            * (Necessity.pairProj (0 : Fin 2) 1) 0 1) := by
      linear_combination hentry
    exact mul_right_cancel₀ hb (mul_left_cancel₀ hamp h1)
  -- but the two phases differ by exactly `e^{iπ} = −1`
  have hdiff : Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    have h3 : Complex.exp ((((t₁ - t₂) * δ : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show (((t₁ - t₂) * δ : ℝ) : ℂ) * Complex.I
          = ((t₁ * δ : ℝ) : ℂ) * Complex.I - ((t₂ * δ : ℝ) : ℂ) * Complex.I from by
        push_cast; ring, Complex.exp_sub, hexp]
      exact div_self (Complex.exp_ne_zero _)
    rwa [hphase] at h3
  rw [Complex.exp_pi_mul_I] at hdiff
  norm_num at hdiff

/-- **The frame-dependent product is not a constant twist product**, whenever the frame function
takes a value at some presented frame other than the constant. -/
theorem exists_n2Sp_ne_twistSeq (t : C(RP2, ℝ)) (U : Matrix.unitaryGroup (Fin 2) ℂ) {s : ℝ}
    (hne : t (blochFrame (colFrame U)) ≠ s) :
    ∃ a b : HermitianMat (Fin 2) ℂ, n2Sp t a b ≠ HermitianMat.twistSeq s a b := by
  obtain ⟨r, b, hrb⟩ := exists_twistSeq_diagFamily_ne hne
  have hUc : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Necessity.unitaryGroup_conjTranspose_mul U
  refine ⟨Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r),
    Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) b, ?_⟩
  intro hcon
  rw [n2Sp_eq_twistSeq_at_frame] at hcon
  -- conjugation is injective, so the two parameters would have to agree at `(r, b)`
  refine hrb ?_
  have key : ∀ τ : ℝ, Necessity.adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
      (HermitianMat.twistSeq τ (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ)
        (Necessity.diagFamily r)) (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) b))
      = HermitianMat.twistSeq τ (Necessity.diagFamily r) b := by
    intro τ
    rw [Necessity.adU_conj_twistSeq τ hUc, Necessity.adU_cancel hUc]
  rw [← key (t (blochFrame (colFrame U))), ← key s, hcon]

/-! ### Every frame is presented, so the separation is unconditional -/

/-- Every point of `ℂP¹` is the first-column ray of a unitary — `Necessity.frameU` writes one
down, and its first column is the vector itself. -/
theorem surjective_colFrame : Function.Surjective colFrame := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    have hw : HermitianMat.nsq (WithLp.ofLp v) ≠ 0 :=
      Necessity.nsq_ne_zero_of_ne_zero (fun h => hv ((WithLp.ofLp_eq_zero (p := 2)).mp h))
    have hnsq : HermitianMat.nsq (Necessity.unitVec hw) = 1 := by
      have h1 := Necessity.unitVec_unit hw
      rw [HermitianMat.dot_self_eq_nsq] at h1
      exact_mod_cast h1
    refine ⟨⟨Necessity.frameU (Necessity.unitVec hw), Necessity.frameU_unitary hnsq⟩, ?_⟩
    refine (Projectivization.mk_eq_mk_iff' ℂ _ v (firstCol_ne_zero _) hv).mpr
      ⟨(((Real.sqrt (HermitianMat.nsq (WithLp.ofLp v)))⁻¹ : ℝ) : ℂ), ?_⟩
    apply (WithLp.ofLp_injective (p := 2) (V := Fin 2 → ℂ))
    funext i
    fin_cases i <;> simp [firstCol, Necessity.frameU, Necessity.unitVec]

theorem surjective_blochFrame_colFrame :
    Function.Surjective (fun U : Matrix.unitaryGroup (Fin 2) ℂ => blochFrame (colFrame U)) :=
  blochFrame_surjective.comp surjective_colFrame

/-- **The frame-dependent product of a nonconstant moduli function is not ANY constant twist
product.**  Unconditional: every `ℝP²` point is presented by some unitary
(`surjective_blochFrame_colFrame`), so a nonconstant `t` must differ from `s` at a presented
frame. -/
theorem exists_n2Sp_ne_twistSeq_of_nonconstant (t : C(RP2, ℝ)) {p q : RP2} (hpq : t p ≠ t q)
    (s : ℝ) :
    ∃ a b : HermitianMat (Fin 2) ℂ, n2Sp t a b ≠ HermitianMat.twistSeq s a b := by
  have hex : ∃ x : RP2, t x ≠ s := by
    by_contra hc
    push_neg at hc
    exact hpq (by rw [hc p, hc q])
  obtain ⟨x, hx⟩ := hex
  obtain ⟨U, hU⟩ := surjective_blochFrame_colFrame x
  refine exists_n2Sp_ne_twistSeq t U ?_
  rw [show blochFrame (colFrame U) = x from hU]
  exact hx

/-- **`thm:qubit-boundary`(iii), in the `twistSeq` encoding row 30 uses.**  The article's own `τ`
family — `RankTwo.tauModuliRP2`, which is defined *through* `MasterTheorem.RankTwo.tau` — gives a
product that is not any constant twist product.  This is the statement that was missing when rows
30 and 31 sat side by side in two unlinked encodings. -/
theorem exists_n2Sp_tau_ne_twistSeq (s : ℝ) :
    ∃ a b : HermitianMat (Fin 2) ℂ,
      n2Sp tauModuliRP2 a b ≠ HermitianMat.twistSeq s a b := by
  obtain ⟨p, q, hpq⟩ := tauModuliRP2_nonconstant
  exact exists_n2Sp_ne_twistSeq_of_nonconstant tauModuliRP2 hpq s

/-! ### S2 for the frame-dependent product

★★★ New 2026-08-09 (ARC-8 block 8.1(b), second pass).  The module docstring above said S2 was "a
genuine estimate rather than plumbing" and did not attempt it.  That judgement was **half right**:
there is one genuine analytic input, but it is *joint* continuity of the twist product in
`(parameter, matrix)`, not the delicate near-the-scalars comparison the certificate predicted.

★ **Why the predicted estimate is not needed.**  The certificate's picture was: near a scalar the
parameter jumps, so one must show `twistSeq s a b` converges to `√a·b·√a` uniformly in `s` by
factoring out a global phase `e^{is log c}` and bounding the residual by the closing spectral gap.
The cheap route instead observes that **at a scalar the product does not depend on the parameter at
all** (`twistSeq_smul_one_left`), so `G(s, a₀)` is *constant in `s`*; then joint continuity plus
compactness of `[-K,K] × effects` (Heine–Cantor) gives a modulus of continuity in `a` that is
uniform in `s`, and that is exactly what the jump needs.  **The parameter never has to converge.**
So the scalar lemma that made the algebra free makes the analysis free too, and no global-phase
factorization appears anywhere.

★ `K` exists because `ℝP²` is compact and `t` is continuous, so the parameter is *bounded* — the
same compactness that makes the moduli object `C(ℝP², ℝ)` well behaved. -/

theorem continuous_blochHerm : Continuous blochHerm := by
  have hmat : ∀ p q : Fin 2, Continuous fun a : HermitianMat (Fin 2) ℂ => a p q :=
    fun p q => (continuous_apply q).comp
      ((continuous_apply p).comp HermitianMat.continuous_mat)
  have hre : ∀ p q : Fin 2, Continuous fun a : HermitianMat (Fin 2) ℂ => (a p q).re :=
    fun p q => Complex.continuous_re.comp (hmat p q)
  have him : ∀ p q : Fin 2, Continuous fun a : HermitianMat (Fin 2) ℂ => (a p q).im :=
    fun p q => Complex.continuous_im.comp (hmat p q)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [blochHerm]
  · exact continuous_const.mul (hre 0 1)
  · exact (continuous_const.mul (him 0 1)).neg
  · exact (hre 0 0).sub (hre 1 1)

theorem isOpen_blochHerm_ne_zero :
    IsOpen {a : HermitianMat (Fin 2) ℂ | blochHerm a ≠ 0} :=
  isOpen_compl_iff.mpr (isClosed_singleton.preimage continuous_blochHerm)

/-- **The parameter is continuous away from the scalars.** -/
theorem continuousOn_n2Tau (t : C(RP2, ℝ)) :
    ContinuousOn (n2Tau t) {a : HermitianMat (Fin 2) ℂ | blochHerm a ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  have hres : (Set.restrict {a : HermitianMat (Fin 2) ℂ | blochHerm a ≠ 0} (n2Tau t))
      = fun a => t (Projectivization.mk' ℝ ⟨blochHerm a.val, a.property⟩) := by
    funext a
    exact n2Tau_of_ne_zero t a.property
  rw [hres]
  exact t.continuous.comp (Projectivization.continuous_mk'.comp
    ((continuous_blochHerm.comp continuous_subtype_val).subtype_mk _))

/-- **The parameter is bounded**, because `ℝP²` is compact. -/
theorem exists_n2Tau_bound (t : C(RP2, ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : HermitianMat (Fin 2) ℂ, |n2Tau t a| ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_univ (X := RP2)).exists_bound_of_continuousOn
    t.continuous.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun a => ?_⟩
  by_cases h : blochHerm a = 0
  · rw [n2Tau_of_eq_zero t h]
    simpa using le_max_right K 0
  · rw [n2Tau_of_ne_zero t h]
    exact le_trans (by simpa using hK _ (Set.mem_univ _)) (le_max_left _ _)

/-- Joint continuity of `(s, x) ↦ √x · c(s · log x)` for bounded continuous `c`.  At `x = 0` the
squeeze `|√x·c| ≤ √x` is **uniform in `s`**, which is exactly why the parameter is allowed to jump
there. -/
theorem continuous_sqrt_mul_bounded_joint {c : ℝ → ℝ} (hc : Continuous c)
    (hbd : ∀ y, |c y| ≤ 1) :
    Continuous (fun p : ℝ × ℝ => Real.sqrt p.2 * c (p.1 * Real.log p.2)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, x₀⟩
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · have h0 : (fun p : ℝ × ℝ => Real.sqrt p.2 * c (p.1 * Real.log p.2)) (s₀, 0) = 0 := by simp
    unfold ContinuousAt
    rw [h0]
    have hten : Filter.Tendsto (fun p : ℝ × ℝ => Real.sqrt p.2)
        (nhds ((s₀, 0) : ℝ × ℝ)) (nhds 0) := by
      have hca : Filter.Tendsto (fun p : ℝ × ℝ => Real.sqrt p.2) (nhds ((s₀, 0) : ℝ × ℝ))
          (nhds (Real.sqrt ((s₀, 0) : ℝ × ℝ).2)) :=
        Real.continuous_sqrt.continuousAt.comp' continuousAt_snd
      simpa using hca
    refine squeeze_zero_norm (fun p => ?_) hten
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg p.2)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg p.2) (hbd _)
  · have hsq : ContinuousAt (fun p : ℝ × ℝ => Real.sqrt p.2) ((s₀, x₀) : ℝ × ℝ) :=
      Real.continuous_sqrt.continuousAt.comp' continuousAt_snd
    have hlog : ContinuousAt (fun p : ℝ × ℝ => Real.log p.2) ((s₀, x₀) : ℝ × ℝ) :=
      continuousAt_snd.log hx₀
    have hcc : ContinuousAt (fun p : ℝ × ℝ => c (p.1 * Real.log p.2)) ((s₀, x₀) : ℝ × ℝ) :=
      hc.continuousAt.comp' (continuousAt_fst.mul hlog)
    exact hsq.mul hcc

/-- Conjugation is continuous in the conjugating matrix. -/
theorem continuous_conj_matrix (b : HermitianMat (Fin 2) ℂ) :
    Continuous (fun M : Matrix (Fin 2) (Fin 2) ℂ => b.conj M) := by
  have hmat : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => (b.conj M).mat := by
    simp only [HermitianMat.conj_apply_mat]
    have h2 : Continuous fun M : Matrix (Fin 2) (Fin 2) ℂ => Mᴴ := by
      simp only [← Matrix.star_eq_conjTranspose]; exact continuous_star
    exact (continuous_id.matrix_mul continuous_const).matrix_mul h2
  exact hmat.subtype_mk _

/-- **Joint continuity of the twist factor in `(parameter, matrix)`, over the effects.**  This is
the one genuine analytic input S2 needs. -/
theorem continuousOn_twistFactor_joint :
    ContinuousOn (fun p : ℝ × HermitianMat (Fin 2) ℂ => HermitianMat.twistFactor p.2 p.1)
      (Set.univ ×ˢ {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a}) := by
  have hspec : ∀ x ∈ (Set.univ ×ˢ {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a}),
      spectrum ℝ ((fun p : ℝ × HermitianMat (Fin 2) ℂ => p.2) x).mat ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    exact HermitianMat.spectrum_subset_Icc_of_isEffect hx.2
  have hA₂ : ContinuousOn (fun p : ℝ × HermitianMat (Fin 2) ℂ => p.2)
      (Set.univ ×ˢ {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a}) :=
    continuous_snd.continuousOn
  have hRe := HermitianMat.continuous_cfc_joint
    (f := fun (x : ℝ × HermitianMat (Fin 2) ℂ) (y : ℝ) =>
      Real.sqrt y * Real.cos (x.1 * Real.log y))
    (A := fun p : ℝ × HermitianMat (Fin 2) ℂ => p.2)
    (T := Set.Icc (0 : ℝ) 1)
    (((continuous_sqrt_mul_bounded_joint Real.continuous_cos
      (fun y => Real.abs_cos_le_one y)).comp
      (continuous_fst.fst'.prodMk continuous_snd)).continuousOn) hspec hA₂
  have hIm := HermitianMat.continuous_cfc_joint
    (f := fun (x : ℝ × HermitianMat (Fin 2) ℂ) (y : ℝ) =>
      Real.sqrt y * Real.sin (x.1 * Real.log y))
    (A := fun p : ℝ × HermitianMat (Fin 2) ℂ => p.2)
    (T := Set.Icc (0 : ℝ) 1)
    (((continuous_sqrt_mul_bounded_joint Real.continuous_sin
      (fun y => Real.abs_sin_le_one y)).comp
      (continuous_fst.fst'.prodMk continuous_snd)).continuousOn) hspec hA₂
  have hgoal : ∀ p : ℝ × HermitianMat (Fin 2) ℂ,
      HermitianMat.twistFactor p.2 p.1
        = (p.2.cfc (fun y => Real.sqrt y * Real.cos (p.1 * Real.log y))).mat
          + Complex.I • (p.2.cfc (fun y => Real.sqrt y * Real.sin (p.1 * Real.log y))).mat :=
    fun _ => rfl
  simp only [hgoal]
  exact ((HermitianMat.continuous_mat.comp_continuousOn hRe).add
    ((HermitianMat.continuous_mat.comp_continuousOn hIm).const_smul Complex.I))

/-- **Joint continuity of the twist product in `(parameter, first argument)`, over the effects.** -/
theorem continuousOn_twistSeq_joint (b : HermitianMat (Fin 2) ℂ) :
    ContinuousOn (fun p : ℝ × HermitianMat (Fin 2) ℂ => HermitianMat.twistSeq p.1 p.2 b)
      (Set.univ ×ˢ {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a}) :=
  (continuous_conj_matrix b).comp_continuousOn continuousOn_twistFactor_joint

/-- **S2 for the frame-dependent product.**  The parameter jumps at the scalars, and it does not
matter: there the product does not depend on the parameter, and joint continuity plus compactness of
`[−K,K] × effects` supplies a modulus of continuity in the matrix that is uniform in the parameter. -/
theorem n2SequentialProduct_firstArgContinuous (t : C(RP2, ℝ)) :
    (n2SequentialProduct t).FirstArgContinuous := by
  intro b _
  obtain ⟨K, hK0, hKb⟩ := exists_n2Tau_bound t
  have hG := continuousOn_twistSeq_joint b
  intro a₀ ha₀
  show ContinuousWithinAt (fun a => HermitianMat.twistSeq (n2Tau t a) a b)
    {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a} a₀
  have hmem : ∀ a : HermitianMat (Fin 2) ℂ, n2Tau t a ∈ Set.Icc (-K) K := fun a =>
    Set.mem_Icc.mpr (abs_le.mp (hKb a))
  by_cases hsc : blochHerm a₀ = 0
  · -- the scalar case: the product is parameter-blind at `a₀`
    obtain ⟨γ, hγ0, hγ⟩ := exists_smul_one_of_blochHerm_eq_zero ha₀.1 hsc
    have hconst : ∀ s : ℝ, HermitianMat.twistSeq s a₀ b = γ • b := by
      intro s
      rw [hγ]
      exact HermitianMat.twistSeq_smul_one_left hγ0 s b
    have hcomp : IsCompact (Set.Icc (-K) K
        ×ˢ {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a}) :=
      isCompact_Icc.prod HermitianMat.isCompact_setOf_isEffect
    have huc := hcomp.uniformContinuousOn_of_continuous
      (hG.mono (Set.prod_mono (Set.subset_univ _) le_rfl))
    rw [Metric.uniformContinuousOn_iff] at huc
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := huc ε hε
    refine ⟨δ, hδ, fun {a} ha hda => ?_⟩
    have h1 := hball (n2Tau t a, a) ⟨hmem a, ha⟩ (n2Tau t a, a₀) ⟨hmem a, ha₀⟩ (by
      rw [Prod.dist_eq]
      simpa using hda)
    show dist (HermitianMat.twistSeq (n2Tau t a) a b)
      (HermitianMat.twistSeq (n2Tau t a₀) a₀ b) < ε
    rw [hconst (n2Tau t a₀)]
    rw [hconst (n2Tau t a)] at h1
    exact h1
  · -- the non-scalar case: the parameter is continuous here, so it is a composition
    have hnb : {a : HermitianMat (Fin 2) ℂ | blochHerm a ≠ 0} ∈ nhds a₀ :=
      isOpen_blochHerm_ne_zero.mem_nhds hsc
    have hτ : ContinuousAt (n2Tau t) a₀ := (continuousOn_n2Tau t).continuousAt hnb
    have hpair : ContinuousWithinAt (fun a : HermitianMat (Fin 2) ℂ => (n2Tau t a, a))
        {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a} a₀ :=
      (hτ.continuousWithinAt).prodMk continuousWithinAt_id
    have hcomp : ContinuousWithinAt
        ((fun p : ℝ × HermitianMat (Fin 2) ℂ => HermitianMat.twistSeq p.1 p.2 b)
          ∘ (fun a : HermitianMat (Fin 2) ℂ => (n2Tau t a, a)))
        {a : HermitianMat (Fin 2) ℂ | OrderUnitSpace.IsEffect a} a₀ :=
      ContinuousWithinAt.comp (f := fun a : HermitianMat (Fin 2) ℂ => (n2Tau t a, a))
        (hG (n2Tau t a₀, a₀) ⟨Set.mem_univ _, ha₀⟩) hpair
        (fun a ha => ⟨Set.mem_univ _, ha⟩)
    exact hcomp

/-- **`prop:n2-sufficiency`, the article's statement.**  Every continuous `t : ℝP² → ℝ` is
realized by a **norm-continuous** S1–S7 sequential product on `H_2(ℂ)` whose value at each
spectral effect is the twist product at that effect's frame parameter.

★ The `FirstArgContinuous` conjunct is S2; it is supplied by
`n2SequentialProduct_firstArgContinuous`, proved further down this file — so this statement is the
row's, not a weakened form of it. -/
theorem exists_sequentialProduct_of_continuous_moduli (t : C(RP2, ℝ)) :
    ∃ P : SequentialProductOn (HermitianMat (Fin 2) ℂ), P.FirstArgContinuous ∧
      ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 2 → ℝ) (b : HermitianMat (Fin 2) ℂ),
        P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b
          = HermitianMat.twistSeq (t (blochFrame (colFrame U)))
            (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b :=
  ⟨n2SequentialProduct t, n2SequentialProduct_firstArgContinuous t,
    fun U r b => n2Sp_eq_twistSeq_at_frame t U r b⟩


/-! ### Toward `lem:n2-descent`: the ray-to-projection dictionary

★★ New 2026-08-09 (ARC-8 block 8.1(d)).  Row 34 records its residue as "assembly only: a map
`U(2) → ℂP¹` (first-column ray), the step *same ray ⟹ the unitaries differ by a monomial matrix*,
and the quotient construction of `C(ℝP², ℝ)`".  The first is `colFrame`, built above for
`prop:n2-sufficiency`.  This block does the second — and it turns out the monomial-matrix detour is
**not needed**: what the transfer actually requires is that equal rays give the *same first spectral
projection*, which follows from `rankOne`'s quadratic homogeneity plus the fact that a unitary's
column is a unit vector.  No statement about monomial matrices appears. -/

/-- **The first spectral projection is the rank-one projection of the first column.** -/
theorem frameMap_eq_rankOne_firstCol (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Necessity.frameMap U
      = HermitianMat.rankOne (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0) := by
  ext1
  rw [HermitianMat.rankOne_mat]
  ext i j
  rw [frameMap_mat_apply, Matrix.vecMulVec_apply, Pi.star_apply]

/-- A unitary's first column is a unit vector. -/
theorem nsq_firstCol (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    HermitianMat.nsq (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0) = 1 := by
  have hU := Necessity.unitaryGroup_conjTranspose_mul U
  have h := congrFun (congrFun hU 0) 0
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_two] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.one_re, Matrix.conjTranspose_apply,
    Complex.star_def, Complex.conj_re, Complex.conj_im] at h2
  rw [HermitianMat.nsq, Fin.sum_univ_two, Complex.normSq_apply, Complex.normSq_apply]
  linarith [h2]

/-- **Equal first-column rays give the same first spectral projection.** -/
theorem frameMap_eq_of_colFrame_eq {U V : Matrix.unitaryGroup (Fin 2) ℂ}
    (h : colFrame U = colFrame V) : Necessity.frameMap U = Necessity.frameMap V := by
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (firstCol_ne_zero U)
    (firstCol_ne_zero V)).mp h
  have hvec : (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)
      = c • (fun i => (V : Matrix (Fin 2) (Fin 2) ℂ) i 0) := by
    have := congrArg WithLp.ofLp hc
    simpa [firstCol] using this.symm
  have hc1 : Complex.normSq c = 1 := by
    have h1 := nsq_firstCol U
    rw [hvec, HermitianMat.nsq_smul, nsq_firstCol V, mul_one] at h1
    exact h1
  rw [frameMap_eq_rankOne_firstCol, frameMap_eq_rankOne_firstCol, hvec,
    HermitianMat.rankOne_smul, hc1, one_smul]

/-- **Complementary first-column rays give complementary spectral projections.** -/
theorem frameMap_eq_one_sub_of_colFrame_eq_ortho {U V : Matrix.unitaryGroup (Fin 2) ℂ}
    (h : colFrame U = orthoFrame (colFrame V)) :
    Necessity.frameMap U = 1 - Necessity.frameMap V := by
  simp only [colFrame] at h
  rw [orthoFrame_mk] at h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (firstCol_ne_zero U)
    (orthoE_ne_zero (firstCol_ne_zero V))).mp h
  have hvec : (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)
      = c • orthoVec (fun i => (V : Matrix (Fin 2) (Fin 2) ℂ) i 0) := by
    have h1 := congrArg WithLp.ofLp hc
    simp only [WithLp.ofLp_smul, ofLp_orthoE, firstCol, WithLp.ofLp_toLp] at h1
    exact h1.symm
  have hn : HermitianMat.nsq (orthoVec (fun i => (V : Matrix (Fin 2) (Fin 2) ℂ) i 0)) = 1 := by
    rw [nsq_orthoVec]; exact nsq_firstCol V
  have hc1 : Complex.normSq c = 1 := by
    have h1 := nsq_firstCol U
    rw [hvec, HermitianMat.nsq_smul, hn, mul_one] at h1
    exact h1
  rw [frameMap_eq_rankOne_firstCol, frameMap_eq_rankOne_firstCol, hvec,
    HermitianMat.rankOne_smul, hc1, one_smul, rankOne_orthoVec (nsq_firstCol V)]

/-- **The frame parameter is constant on the fibres of `blochFrame ∘ colFrame`** — the descent
hypothesis `lem:n2-descent` needs.  The two cases are exactly the two halves of `blochFrame_eq_iff`:
same ray (fibre-constancy) and complementary ray (frame reversal). -/
theorem n2FrameTwist_eq_of_blochFrame_colFrame_eq
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
    {U V : Matrix.unitaryGroup (Fin 2) ℂ}
    (h : blochFrame (colFrame U) = blochFrame (colFrame V)) :
    Necessity.n2FrameTwist P hS2 U = Necessity.n2FrameTwist P hS2 V := by
  rcases (blochFrame_eq_iff (colFrame U) (colFrame V)).mp h with hsame | hortho
  · exact Necessity.n2FrameTwist_eq_of_frameMap_eq P V U hS2
      (frameMap_eq_of_colFrame_eq hsame)
  · have hcompl : Necessity.frameMap U = Necessity.frameMap (V * Necessity.swapU) := by
      rw [Necessity.frameMap_mul_swap]
      exact frameMap_eq_one_sub_of_colFrame_eq_ortho hortho
    rw [Necessity.n2FrameTwist_eq_of_frameMap_eq P (V * Necessity.swapU) U hS2 hcompl,
      Necessity.n2FrameTwist_reverse]

/-! ### `lem:n2-descent`: the frame parameter as a continuous function on `ℝP²`

★★★ New 2026-08-09 (ARC-8 block 8.1(d)).  Row 34's residue was "assembly only", and this is the
assembly.  The presentation map `U(2) → ℝP²` is `blochFrame ∘ colFrame`; it is continuous and
surjective from a **compact** group to a **Hausdorff** space, hence a quotient map, so a function on
`ℝP²` is continuous exactly when its pullback is — and the pullback is `n2FrameTwist`, whose
continuity is row 33.  ★ Boundedness, which the row also asks for, is then automatic from `ℝP²`'s
compactness rather than a separate estimate. -/

theorem continuous_firstCol : Continuous firstCol := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
  apply continuous_pi
  intro i
  exact (continuous_apply 0).comp ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_colFrame : Continuous colFrame :=
  Projectivization.continuous_mk'.comp (continuous_firstCol.subtype_mk _)

/-- The presentation map: a unitary to the `ℝP²` point of the unordered frame it presents. -/
noncomputable def frameRP2 (U : Matrix.unitaryGroup (Fin 2) ℂ) : RP2 :=
  blochFrame (colFrame U)

theorem continuous_frameRP2 : Continuous frameRP2 :=
  blochFrame_continuous.comp continuous_colFrame

theorem surjective_frameRP2 : Function.Surjective frameRP2 :=
  surjective_blochFrame_colFrame

theorem isQuotientMap_frameRP2 : Topology.IsQuotientMap frameRP2 :=
  (continuous_frameRP2.isClosedMap).isQuotientMap continuous_frameRP2 surjective_frameRP2

/-- **The article's `t̃` as a function on `ℝP²`**, for an arbitrary rank-two product. -/
noncomputable def n2ModuliRP2 (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) : RP2 → ℝ :=
  fun p => Necessity.n2FrameTwist P hS2 (Function.surjInv surjective_frameRP2 p)

@[simp]
theorem n2ModuliRP2_frameRP2 (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2ModuliRP2 P hS2 (frameRP2 U) = Necessity.n2FrameTwist P hS2 U :=
  n2FrameTwist_eq_of_blochFrame_colFrame_eq P hS2
    (Function.surjInv_eq surjective_frameRP2 (frameRP2 U))

theorem continuous_n2ModuliRP2 (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) : Continuous (n2ModuliRP2 P hS2) := by
  rw [isQuotientMap_frameRP2.continuous_iff]
  have hcomp : (n2ModuliRP2 P hS2) ∘ frameRP2 = Necessity.n2FrameTwist P hS2 :=
    funext fun U => n2ModuliRP2_frameRP2 P hS2 U
  rw [hcomp]
  exact Necessity.continuous_n2FrameTwist P hS2

/-- **`lem:n2-descent`.**  The frame parameter of an arbitrary norm-continuous S1–S7 product on
`H_2(ℂ)` descends to a genuine element of the moduli object `C(ℝP², ℝ)` — continuous, and bounded
because `ℝP²` is compact. -/
noncomputable def n2QubitModuli (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) : C(RP2, ℝ) :=
  ⟨n2ModuliRP2 P hS2, continuous_n2ModuliRP2 P hS2⟩

@[simp]
theorem n2QubitModuli_apply (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2QubitModuli P hS2 (frameRP2 U) = Necessity.n2FrameTwist P hS2 U :=
  n2ModuliRP2_frameRP2 P hS2 U

/-- **The descended function represents the product**: at every spectral effect, the product is the
twist product with parameter read off the effect's `ℝP²` frame.  This is `prop:n2-necessity` stated
against the moduli object rather than against a unitary. -/
theorem sp_eq_twistSeq_n2QubitModuli (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) {r : Fin 2 → ℝ}
    (hr : ∀ i, r i ≤ 0) {b : HermitianMat (Fin 2) ℂ} (hb : IsEffect b) :
    P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b
      = HermitianMat.twistSeq (n2QubitModuli P hS2 (frameRP2 U))
        (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b := by
  rw [n2QubitModuli_apply]
  exact Necessity.n2_sp_eq_twistSeq_frame P hS2 U hr rfl hb

/-- **`lem:n2-descent`, boundedness clause** — automatic from compactness. -/
theorem exists_n2QubitModuli_bound (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) :
    ∃ C : ℝ, ∀ p : RP2, |n2QubitModuli P hS2 p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := RP2)).exists_bound_of_continuousOn
    (continuous_n2ModuliRP2 P hS2).continuousOn
  exact ⟨C, fun p => by simpa using hC p (Set.mem_univ p)⟩

/-! ### `cor:qubit-classification`: the correspondence is a bijection

★★★ New 2026-08-09 (ARC-8 block 8.1(f)).  Row 35 is rows 29/30/32/33/34 assembled, and with the
`ℝP²` moduli object built above the assembly is short.  The two halves:

* **every product determines a unique moduli function** — existence is `n2QubitModuli`, uniqueness is
  surjectivity of the presentation map;
* **and the round trip is the identity** — the moduli function recovered from `n2SequentialProduct t`
  is `t` itself, because `n2FrameTwist_unique_param` says the frame parameter is the *unique* real at
  which the product acts as a twist at that frame, and `n2Sp_eq_twistSeq_at_frame` exhibits
  `t (frameRP2 U)` as such a real. -/

/-- **Every rank-two product determines a unique element of the moduli object.** -/
theorem exists_unique_qubitModuli (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) :
    ∃! t : C(RP2, ℝ), ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      t (frameRP2 U) = Necessity.n2FrameTwist P hS2 U := by
  refine ⟨n2QubitModuli P hS2, fun U => n2QubitModuli_apply P hS2 U, ?_⟩
  intro t' ht'
  ext p
  obtain ⟨U, hU⟩ := surjective_frameRP2 p
  rw [← hU, ht' U, n2QubitModuli_apply]

/-- **The moduli value at a presented frame IS the frame parameter of the product it builds.** -/
theorem apply_frameRP2_eq (t : C(RP2, ℝ)) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    t (frameRP2 U) = Necessity.n2FrameTwist (n2SequentialProduct t)
      (n2SequentialProduct_firstArgContinuous t) U :=
  (Necessity.n2FrameTwist_unique_param (n2SequentialProduct t)
    (n2SequentialProduct_firstArgContinuous t) U).unique
      (fun r _ b _ => n2Sp_eq_twistSeq_at_frame t U r b)
      (fun r hr b hb => Necessity.n2_sp_eq_twistSeq_frame _ _ U hr rfl hb)

/-- **The round trip is the identity**: the moduli function of the product built from `t` is `t`. -/
theorem n2QubitModuli_n2SequentialProduct (t : C(RP2, ℝ)) :
    n2QubitModuli (n2SequentialProduct t) (n2SequentialProduct_firstArgContinuous t) = t := by
  ext p
  obtain ⟨U, hU⟩ := surjective_frameRP2 p
  rw [← hU, n2QubitModuli_apply]
  exact (apply_frameRP2_eq t U).symm

/-- **`cor:qubit-classification`.**  The map `t ↦ ∘_t` is a bijection from `C(ℝP², ℝ)` onto the
norm-continuous S1–S7 products on `H_2(ℂ)`, presented as a two-sided correspondence: the forward map
is injective, and every norm-continuous product determines a unique moduli function. -/
theorem qubit_classification :
    (Function.Injective fun t : C(RP2, ℝ) => (n2SequentialProduct t).sp)
      ∧ ∀ (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous),
        ∃! t : C(RP2, ℝ), ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
          t (frameRP2 U) = Necessity.n2FrameTwist P hS2 U := by
  refine ⟨?_, exists_unique_qubitModuli⟩
  intro t₁ t₂ hsp
  have hsp' : (n2SequentialProduct t₁).sp = (n2SequentialProduct t₂).sp := hsp
  ext p
  obtain ⟨U, hU⟩ := surjective_frameRP2 p
  rw [← hU]
  refine (Necessity.n2FrameTwist_unique_param (n2SequentialProduct t₁)
    (n2SequentialProduct_firstArgContinuous t₁) U).unique
      (fun r _ b _ => n2Sp_eq_twistSeq_at_frame t₁ U r b) (fun r _ b _ => ?_)
  show (n2SequentialProduct t₁).sp _ _ = _
  rw [hsp']
  exact n2Sp_eq_twistSeq_at_frame t₂ U _ _

/-! ### Two corrections from checkpoint 2, both from cold review

★★★ **(1) THE NON-COLLAPSE THEOREM ABOVE IS TRUE BUT ITS WITNESS IS NOT AN EFFECT.**  A reviewer
found that `exists_twistSeq_diagFamily_ne` chooses `δ = π/(t₁ − t₂)`, which is **positive** whenever
`t₁ > t₂`, so the separating first argument `diagFamily (δ, 0)` has an eigenvalue `e^δ > 1` and lies
*outside* the effect interval (`Necessity.diagFamily_isEffect` needs `∀ i, r i ≤ 0`).  Since S1–S7 and
the article's operation constrain **effects only**, the theorems above do not by themselves exclude
that `n2Sp t` and `twistSeq s` agree on every effect and differ only on the total extension — which is
exactly the reading "a genuinely frame-dependent product satisfies all seven axioms" needs.
★ The content was present but unstated; the effect-level statement below is the one to cite, and it
does not go through the entry probe at all — it uses `n2FrameTwist_unique_param`, whose own
quantifiers are already `r ≤ 0` and `IsEffect b`.
★ **Transferable: a separation theorem is only as strong as the class its witnesses live in.**  "∃ a b"
with no `IsEffect` guard reads as a separation of the operations and is a separation of their
extensions.

★★ **(2) S2 was proved in the carried (Frobenius) topology; the article's S2 is the ORDER-UNIT norm.**
The bridge is generic and already in the tree (`Necessity.firstArgContinuousOu_iff`), but nothing
connected the rank-two product to it.  Instantiated below, so row 30's "norm-continuous" is the
article's norm and not merely a topology that happens to agree. -/

/-- **`prop:n2-sufficiency`'s S2 in the ARTICLE'S norm** — the order-unit norm, via the tree's
generic equivalence. -/
theorem n2SequentialProduct_firstArgContinuousOu (t : C(RP2, ℝ)) :
    Necessity.FirstArgContinuousOu (n2SequentialProduct t) :=
  (Necessity.firstArgContinuousOu_iff _).mpr (n2SequentialProduct_firstArgContinuous t)

/-- **NON-COLLAPSE, AT THE EFFECTS.**  For a nonconstant moduli function the frame-dependent product
does not agree with any constant twist product **on the effects** — which is the class the axioms and
the article's operation are about. -/
theorem not_forall_effects_eq_twistSeq (t : C(RP2, ℝ)) {p q : RP2} (hpq : t p ≠ t q) (s : ℝ) :
    ¬ (∀ a b : HermitianMat (Fin 2) ℂ, IsEffect a → IsEffect b →
        n2Sp t a b = HermitianMat.twistSeq s a b) := by
  intro hall
  have hconst : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, t (frameRP2 U) = s := by
    intro U
    rw [apply_frameRP2_eq t U]
    refine (Necessity.n2FrameTwist_unique_param (n2SequentialProduct t)
      (n2SequentialProduct_firstArgContinuous t) U).unique
        (fun r hr b hb => Necessity.n2_sp_eq_twistSeq_frame _ _ U hr rfl hb)
        (fun r hr b hb => ?_)
    exact hall _ b (Necessity.adU_isEffect (Necessity.unitaryGroup_conjTranspose_mul U)
      (Necessity.unitaryGroup_mul_conjTranspose U) (Necessity.diagFamily_isEffect hr)) hb
  obtain ⟨U, hU⟩ := surjective_frameRP2 p
  obtain ⟨V, hV⟩ := surjective_frameRP2 q
  rw [← hU, ← hV, hconst U, hconst V] at hpq
  exact hpq rfl

/-- **`thm:qubit-boundary`(iii) at the effects**, for the article's own `τ`.  This is the statement
row 31 should be read against; the entry-probe version above separates the total extensions. -/
theorem not_forall_effects_tau_eq_twistSeq (s : ℝ) :
    ¬ (∀ a b : HermitianMat (Fin 2) ℂ, IsEffect a → IsEffect b →
        n2Sp tauModuliRP2 a b = HermitianMat.twistSeq s a b) := by
  obtain ⟨p, q, hpq⟩ := tauModuliRP2_nonconstant
  exact not_forall_effects_eq_twistSeq tauModuliRP2 hpq s

/-! ### The totality obstruction: "onto the products" is FALSE, not unwritten

★★★ New 2026-08-09 (ARC-8 checkpoint 2, from a cold reviewer, and it corrects a claim I had made).
Row 35's residue was recorded as "the onto half at **singular effects** — and that is the whole
residue", with the implication that one writable limiting argument stands between the tree and the
article's bijection.  **That is wrong, and the tree already contained the refutation.**

`Necessity.badP t` is a genuine S1–S7 product with S2 (`Necessity.badP_S2`) that equals the twist
product **on effects** and is `0` off them — it exists precisely because every axiom of
`SequentialProductOn` is `IsEffect`-guarded.  So it has the *same* element of `C(ℝP², ℝ)` as
`n2SequentialProduct (const t)` and a *different* `.sp`.  Hence `product ↦ moduli` is **not
injective on `SequentialProductOn` values**, and no bijection onto the products-as-`.sp`-functions
can exist.

★ **The honest target is therefore products up to agreement on effects**, which is what the article
means and what the axioms can see.  ★★ And the lesson is one already on this project's record:
**a totalizing phrase inside a residual claim is where the error lives.**  "…and that is the whole
residue" was the false part of that sentence, exactly as it was the last time. -/

/-- `badP t`'s frame parameter is the constant `t` at every frame. -/
theorem badP_frameTwist (t : ℝ) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Necessity.n2FrameTwist (Necessity.badP t) (Necessity.badP_S2 t) U = t := by
  refine (Necessity.n2FrameTwist_unique_param (Necessity.badP t) (Necessity.badP_S2 t) U).unique
    (fun r hr b hb => Necessity.n2_sp_eq_twistSeq_frame _ _ U hr rfl hb) ?_
  intro r hr b hb
  have ha : IsEffect (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) :=
    Necessity.adU_isEffect (Necessity.unitaryGroup_conjTranspose_mul U)
      (Necessity.unitaryGroup_mul_conjTranspose U) (Necessity.diagFamily_isEffect hr)
  rw [Necessity.badP_sp, Necessity.badSp_eq ha hb, Necessity.twistProductOn_sp]

/-- **Two distinct products with the same moduli function.** -/
theorem moduli_collide (t : ℝ) :
    n2QubitModuli (Necessity.badP t) (Necessity.badP_S2 t)
      = n2QubitModuli (n2SequentialProduct (ContinuousMap.const RP2 t))
        (n2SequentialProduct_firstArgContinuous _) := by
  rw [n2QubitModuli_n2SequentialProduct]
  ext p
  obtain ⟨U, hU⟩ := surjective_frameRP2 p
  rw [← hU, n2QubitModuli_apply, badP_frameTwist]
  rfl

theorem not_isEffect_two_smul_one : ¬ IsEffect ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) := by
  intro h
  have h0 : (0 : HermitianMat (Fin 2) ℂ) ≤ 1 - (2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ) :=
    sub_nonneg.mpr (le_of_le_of_eq h.2 HermitianMat.ousUnit_eq_one)
  have hd : (0 : ℂ) ≤ (1 - (2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)).mat 0 0 :=
    Matrix.PosSemidef.diag_nonneg (HermitianMat.zero_le_iff.mp h0)
  have hval : (1 - (2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)).mat 0 0 = (-1 : ℂ) := by
    rw [HermitianMat.mat_sub, HermitianMat.mat_smul, HermitianMat.mat_one,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    norm_num
  rw [hval] at hd
  have := (Complex.le_def.mp hd).1
  norm_num at this

/-- The two products differ at a **non-effect** first argument, where the axioms say nothing. -/
theorem badP_sp_differs (t : ℝ) :
    (Necessity.badP t).sp ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) 1
      ≠ (n2SequentialProduct (ContinuousMap.const RP2 t)).sp
          ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) 1 := by
  rw [Necessity.badP_sp, Necessity.badSp_eq_zero (fun h => not_isEffect_two_smul_one h.1)]
  show (0 : HermitianMat (Fin 2) ℂ) ≠ n2Sp _ _ _
  rw [n2Sp_smul_one_left _ (by norm_num : (0 : ℝ) ≤ 2)]
  intro hcon
  have h00 : (0 : HermitianMat (Fin 2) ℂ).mat 0 0
      = ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)).mat 0 0 := by rw [hcon]
  rw [HermitianMat.mat_zero, HermitianMat.mat_smul, HermitianMat.mat_one,
    Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq] at h00
  norm_num at h00

/-- ★★★ **The article's "bijection ONTO the norm-continuous products" is FALSE for this encoding of
"product".**  `badP t` is an S1–S7 + S2 product on `H_2(ℂ)` that is `n2SequentialProduct t'` for no
`t'` whatsoever.  So row 35's target must be *products up to agreement on effects*, and the residue
recorded as "singular effects only" was incomplete. -/
theorem not_exists_moduli_of_badP (t : ℝ) :
    ¬ ∃ t' : C(RP2, ℝ), (Necessity.badP t).sp = (n2SequentialProduct t').sp := by
  rintro ⟨t', h⟩
  have ht' : t' = ContinuousMap.const RP2 t := by
    ext p
    obtain ⟨U, hU⟩ := surjective_frameRP2 p
    have huniq :=
      (Necessity.n2FrameTwist_unique_param (Necessity.badP t) (Necessity.badP_S2 t) U).unique
        (fun r hr b hb => Necessity.n2_sp_eq_twistSeq_frame (Necessity.badP t)
          (Necessity.badP_S2 t) U hr rfl hb)
        (fun r _ b _ => by rw [h]; exact n2Sp_eq_twistSeq_at_frame t' U r b)
    rw [badP_frameTwist] at huniq
    rw [← hU]
    exact huniq.symm
  rw [ht'] at h
  exact badP_sp_differs t (congrFun (congrFun h _) _)

/-- **The `n2Sp` bridge a reviewer found missing**: `sp_eq_twistSeq_n2QubitModuli` equates `P.sp`
with the CONSTANT-parameter `twistSeq`, not with `n2Sp`.  This is the two-line statement that the two
*products* agree at every spectral first argument, which is what row 35's positive-definite half
actually asserts. -/
theorem sp_eq_n2Sp_of_moduli (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) {r : Fin 2 → ℝ}
    (hr : ∀ i, r i ≤ 0) {b : HermitianMat (Fin 2) ℂ} (hb : IsEffect b) :
    P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b
      = n2Sp (n2QubitModuli P hS2)
        (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b := by
  rw [n2Sp_eq_twistSeq_at_frame]
  exact sp_eq_twistSeq_n2QubitModuli P hS2 U hr hb

end RankTwo
