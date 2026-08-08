/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.FrameConstancy

set_option linter.style.longLine false

/-!
# Every unitary is a product of axis-fixing unitaries  (the ℂ row's connectivity input)

The complex row's frame graph is connected.  This file proves the group-theoretic fact behind
that: **every `U ∈ U(N)`, `N ≥ 3`, is a product of three unitaries each of which fixes a
coordinate axis.**

The tool is the Householder reflection `R_w = 1 − 2·ww*/⟪w,w⟫`.  Two facts make it fit:

* a reflection *fixes every axis its vector misses* — if `w m = 0` then `R_w` is block
  diagonal for `{m} ⊕ {m}ᶜ`, since `(R_w)_{ij} = δ_{ij} − 2 w_i \bar w_j` vanishes whenever
  exactly one of `i, j` is `m`.  So an arbitrary reflection is usable as long as its vector
  has *one* zero coordinate;
* a reflection can carry any vector onto any axis, provided the target's phase is matched to
  the vector's (`house_mulVec_align`).

So: clear the first column of `U` in two reflections — the first has `w m = 0` at `m = 1` and
concentrates the coordinates other than `1` onto coordinate `0`, leaving a vector supported on
`{0, 1}`; the second has `w m = 0` at `m = 2` (this is where `N ≥ 3` enters) and carries that
onto coordinate `0`.  A unitary whose first column is supported on `{0}` already fixes the axis
`0` (`axisFixing_of_col`), and reflections are involutions, so the two reflections and the
residue multiply back to `U`.

No square roots appear in the reflection itself — the `2/⟪w,w⟫` normalization is carried
instead — and `house 0 = 1`, so the degenerate case needs no separate branch.
-/

noncomputable section

open scoped Matrix
open ComplexOrder

namespace Necessity

variable {N : ℕ}

/-! ## Coordinate vectors -/

/-- The `i`-th coordinate vector. -/
def axisVec (i : Fin N) : Fin N → ℂ := Pi.single i 1

theorem axisVec_self (i : Fin N) : axisVec i i = 1 := by
  rw [axisVec, Pi.single_eq_same]

theorem axisVec_ne {i k : Fin N} (h : k ≠ i) : axisVec i k = 0 := by
  rw [axisVec, Pi.single_eq_of_ne h]

theorem star_axisVec (i : Fin N) : star (axisVec i) = axisVec i := by
  ext k
  rw [Pi.star_apply]
  by_cases hk : k = i
  · rw [hk, axisVec_self, star_one]
  · rw [axisVec_ne hk, star_zero]

theorem axisVec_dotProduct (i : Fin N) (v : Fin N → ℂ) : axisVec i ⬝ᵥ v = v i := by
  rw [axisVec, single_dotProduct, one_mul]

theorem dotProduct_axisVec (i : Fin N) (v : Fin N → ℂ) : v ⬝ᵥ axisVec i = v i := by
  rw [axisVec, dotProduct_single, mul_one]

/-- Applying a matrix to a coordinate vector reads off that column. -/
theorem mulVec_axisVec (M : Matrix (Fin N) (Fin N) ℂ) (j k : Fin N) :
    (M *ᵥ axisVec j) k = M k j := by
  rw [axisVec, Matrix.mulVec_single_one, Matrix.col_apply]

/-! ## Axis-fixing matrices -/

/-- `M` **fixes the axis** `m` when its row `m` and column `m` vanish off the diagonal — i.e.
`M` is block diagonal for the coordinate splitting `{m} ⊕ {m}ᶜ`. -/
def AxisFixing (m : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ i j : Fin N, i ≠ j → (i = m ∨ j = m) → M i j = 0

theorem axisFixing_one (m : Fin N) : AxisFixing m (1 : Matrix (Fin N) (Fin N) ℂ) :=
  fun _ _ hij _ => Matrix.one_apply_ne hij

/-- **A unitary whose `m`-th column is supported on `m` fixes the axis `m`.**  The column
condition gives one half outright; the other half is orthogonality of columns, since the
diagonal entry has modulus one and so cannot vanish. -/
theorem axisFixing_of_col {M : Matrix (Fin N) (Fin N) ℂ} (hM : Mᴴ * M = 1) {m : Fin N}
    (hcol : ∀ k, k ≠ m → M k m = 0) : AxisFixing m M := by
  have hentry : ∀ j : Fin N,
      star (M m m) * M m j = (1 : Matrix (Fin N) (Fin N) ℂ) m j := by
    intro j
    have hsum : ∑ k : Fin N, star (M k m) * M k j = star (M m m) * M m j := by
      refine Finset.sum_eq_single m (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ m) h)
      rw [hcol k hk, star_zero, zero_mul]
    have h1 : ((Mᴴ * M) : Matrix (Fin N) (Fin N) ℂ) m j
        = ∑ k : Fin N, star (M k m) * M k j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [Matrix.conjTranspose_apply]
    rw [← hsum, ← h1, hM]
  have hne : star (M m m) ≠ 0 := by
    intro h
    have h1 := hentry m
    rw [h, zero_mul, Matrix.one_apply_eq] at h1
    exact one_ne_zero h1.symm
  intro i j hij hm
  rcases hm with hi | hj
  · subst hi
    have h1 := hentry j
    rw [Matrix.one_apply_ne hij] at h1
    exact (mul_eq_zero.mp h1).resolve_left hne
  · subst hj
    exact hcol i hij

/-! ## The squared norm, without square roots -/

/-- The squared norm of a complex vector, as a real number. -/
def nrm2 (w : Fin N → ℂ) : ℝ := ∑ k, Complex.normSq (w k)

theorem star_dotProduct_self_eq (w : Fin N → ℂ) :
    star w ⬝ᵥ w = ((nrm2 w : ℝ) : ℂ) := by
  rw [nrm2, Complex.ofReal_sum, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.normSq_eq_conj_mul_self]
  rfl

theorem nrm2_eq_zero_iff (w : Fin N → ℂ) : nrm2 w = 0 ↔ w = 0 := by
  rw [← Complex.ofReal_eq_zero, ← star_dotProduct_self_eq]
  exact dotProduct_star_self_eq_zero

theorem nrm2_ne_zero {w : Fin N → ℂ} (hw : w ≠ 0) : nrm2 w ≠ 0 :=
  fun h => hw ((nrm2_eq_zero_iff w).mp h)

theorem nrm2_nonneg (w : Fin N → ℂ) : 0 ≤ nrm2 w :=
  Finset.sum_nonneg fun k _ => Complex.normSq_nonneg (w k)

theorem ofReal_nrm2_ne_zero {w : Fin N → ℂ} (hw : nrm2 w ≠ 0) :
    ((nrm2 w : ℝ) : ℂ) ≠ 0 := by
  simpa only [ne_eq, Complex.ofReal_eq_zero] using hw

/-! ## Householder reflections -/

/-- The orthogonal projection onto the line spanned by `w` (zero when `w = 0`). -/
def lineProj (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ((((nrm2 w)⁻¹ : ℝ)) : ℂ) • Matrix.vecMulVec w (star w)

/-- **The Householder reflection** in the hyperplane orthogonal to `w`; the identity when
`w = 0`. -/
def house (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1 - (2 : ℂ) • lineProj w

theorem lineProj_apply (w : Fin N → ℂ) (i j : Fin N) :
    lineProj w i j = ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * (w i * star (w j)) := by
  rw [lineProj, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]

theorem house_apply (w : Fin N → ℂ) (i j : Fin N) :
    house w i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j
      - (2 : ℂ) * (((((nrm2 w)⁻¹ : ℝ)) : ℂ) * (w i * star (w j))) := by
  rw [house, Matrix.sub_apply, Matrix.smul_apply, lineProj_apply, smul_eq_mul]

theorem house_zero : house (0 : Fin N → ℂ) = 1 := by
  ext i j
  rw [house_apply]
  simp

/-- **A reflection fixes every axis its vector misses.** -/
theorem house_axisFixing {m : Fin N} {w : Fin N → ℂ} (hw : w m = 0) :
    AxisFixing m (house w) := by
  intro i j hij hm
  rw [house_apply, Matrix.one_apply_ne hij]
  rcases hm with hi | hj
  · rw [hi, hw, zero_mul, mul_zero, mul_zero, sub_zero]
  · rw [hj, hw, star_zero, mul_zero, mul_zero, mul_zero, sub_zero]

theorem lineProj_mul_self {w : Fin N → ℂ} (hw : nrm2 w ≠ 0) :
    lineProj w * lineProj w = lineProj w := by
  have hP : Matrix.vecMulVec w (star w) * Matrix.vecMulVec w (star w)
      = ((nrm2 w : ℝ) : ℂ) • Matrix.vecMulVec w (star w) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, star_dotProduct_self_eq]
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply,
      smul_eq_mul]
    ring
  have hscal : ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * ((nrm2 w : ℝ) : ℂ)
      = ((((nrm2 w)⁻¹ : ℝ)) : ℂ) := by
    have h := ofReal_nrm2_ne_zero hw
    push_cast
    field_simp
  rw [lineProj, Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, smul_smul, hscal]

theorem lineProj_conjTranspose (w : Fin N → ℂ) : (lineProj w)ᴴ = lineProj w := by
  ext i j
  rw [Matrix.conjTranspose_apply, lineProj_apply, lineProj_apply, star_mul', star_mul',
    star_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem house_conjTranspose (w : Fin N → ℂ) : (house w)ᴴ = house w := by
  rw [house, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    lineProj_conjTranspose]
  norm_num

/-- **A reflection is an involution** (for `w ≠ 0`; for `w = 0` it is the identity). -/
theorem house_mul_self {w : Fin N → ℂ} (hw : nrm2 w ≠ 0) : house w * house w = 1 := by
  have h := lineProj_mul_self hw
  simp only [house, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, h]
  module

theorem house_mul_self' (w : Fin N → ℂ) : house w * house w = 1 := by
  by_cases hw : nrm2 w = 0
  · rw [(nrm2_eq_zero_iff w).mp hw, house_zero, Matrix.one_mul]
  · exact house_mul_self hw

theorem house_unitary (w : Fin N → ℂ) : (house w)ᴴ * house w = 1 := by
  rw [house_conjTranspose]
  exact house_mul_self' w

theorem house_unitary' (w : Fin N → ℂ) : house w * (house w)ᴴ = 1 := by
  rw [house_conjTranspose]
  exact house_mul_self' w

theorem house_mem_unitaryGroup (w : Fin N → ℂ) :
    house w ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact house_unitary' w

/-! ## What a reflection does to a vector -/

theorem house_mulVec (w v : Fin N → ℂ) :
    house w *ᵥ v = v - ((2 : ℂ) * ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * (star w ⬝ᵥ v)) • w := by
  rw [house, Matrix.sub_mulVec, Matrix.one_mulVec, lineProj, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul, smul_smul]

/-- A reflection fixes any vector orthogonal to its own. -/
theorem house_mulVec_of_orthogonal {w v : Fin N → ℂ} (h : star w ⬝ᵥ v = 0) :
    house w *ᵥ v = v := by
  rw [house_mulVec, h, mul_zero, zero_smul, sub_zero]

/-- **The reflection that aligns a vector with an axis.**

If `λ` has the same modulus as `v` and `\bar λ · v i` is real, then the reflection in
`v − λ e_i` sends `v` to `λ e_i`.  The second hypothesis is the phase matching: it is exactly
what makes `⟪w,w⟫ = 2⟪w,v⟫`, so the reflection coefficient is `1` and `v ↦ v − w`. -/
theorem house_mulVec_align {v : Fin N → ℂ} {i : Fin N} {lam : ℂ}
    (hnorm : star lam * lam = star v ⬝ᵥ v)
    (hreal : star lam * v i = star (v i) * lam) :
    house (v - lam • axisVec i) *ᵥ v = lam • axisVec i := by
  set z : Fin N → ℂ := lam • axisVec i with hz
  set w : Fin N → ℂ := v - z with hw
  -- the four inner products
  have hstarz : star z = star lam • axisVec i := by
    rw [hz, star_smul, star_axisVec]
  have hzv : star z ⬝ᵥ v = star lam * v i := by
    rw [hstarz, smul_dotProduct, axisVec_dotProduct, smul_eq_mul]
  have hvz : star v ⬝ᵥ z = star (v i) * lam := by
    rw [hz, dotProduct_smul, dotProduct_axisVec, Pi.star_apply, smul_eq_mul, mul_comm]
  have hzz : star z ⬝ᵥ z = star lam * lam := by
    rw [hstarz, hz, smul_dotProduct, dotProduct_smul, axisVec_dotProduct, axisVec_self,
      smul_eq_mul, smul_eq_mul, mul_one]
  have hwv : star w ⬝ᵥ v = star v ⬝ᵥ v - star lam * v i := by
    rw [hw, star_sub, sub_dotProduct, hzv]
  have hexp : star w ⬝ᵥ w
      = star v ⬝ᵥ v - star v ⬝ᵥ z - (star z ⬝ᵥ v - star z ⬝ᵥ z) := by
    rw [hw, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  have hww : star w ⬝ᵥ w = (2 : ℂ) * (star w ⬝ᵥ v) := by
    rw [hexp, hwv, hzv, hvz, hzz, ← hnorm, hreal]
    ring
  by_cases hw0 : w = 0
  · -- `v` is already on the axis
    have hvz' : v = z := by
      rw [hw] at hw0
      exact sub_eq_zero.mp hw0
    rw [hw0, house_zero, Matrix.one_mulVec, hvz']
  · have hn : nrm2 w ≠ 0 := nrm2_ne_zero hw0
    have hq : star w ⬝ᵥ w = ((nrm2 w : ℝ) : ℂ) := star_dotProduct_self_eq w
    have hcoef : (2 : ℂ) * ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * (star w ⬝ᵥ v) = 1 := by
      have h2 : (2 : ℂ) * (star w ⬝ᵥ v) = ((nrm2 w : ℝ) : ℂ) := by rw [← hww, hq]
      calc (2 : ℂ) * ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * (star w ⬝ᵥ v)
          = ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * ((2 : ℂ) * (star w ⬝ᵥ v)) := by ring
        _ = ((((nrm2 w)⁻¹ : ℝ)) : ℂ) * ((nrm2 w : ℝ) : ℂ) := by rw [h2]
        _ = 1 := by rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
    rw [house_mulVec, hcoef, one_smul, hw, sub_sub_cancel]

/-! ## A phase-matched target always exists -/

/-- **The alignment hypotheses can always be met.**  For any `v` and any index `i` there is a
`λ` of the same modulus as `v` with `\bar λ · v i` real: rotate `‖v‖` onto the phase of `v i`.
(When `v i = 0` any phase will do, and `λ = ‖v‖` is taken.) -/
theorem exists_alignTarget (v : Fin N → ℂ) (i : Fin N) :
    ∃ lam : ℂ, star lam * lam = star v ⬝ᵥ v ∧ star lam * v i = star (v i) * lam := by
  classical
  -- take the two square roots opaquely, so no rewrite can reach inside them
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ((a : ℝ) : ℂ) * ((a : ℝ) : ℂ) = star v ⬝ᵥ v :=
    ⟨Real.sqrt (nrm2 v), by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (nrm2_nonneg v), star_dotProduct_self_eq]⟩
  by_cases hvi : v i = 0
  · refine ⟨((a : ℝ) : ℂ), ?_, ?_⟩
    · rw [Complex.star_def, Complex.conj_ofReal, ha]
    · rw [hvi, mul_zero, star_zero, zero_mul]
  · have hp : (0 : ℝ) < Complex.normSq (v i) := Complex.normSq_pos.mpr hvi
    obtain ⟨b, hbne, hb⟩ : ∃ b : ℝ, b ≠ 0 ∧ b * b = Complex.normSq (v i) :=
      ⟨Real.sqrt (Complex.normSq (v i)), Real.sqrt_ne_zero'.mpr hp,
        Real.mul_self_sqrt (le_of_lt hp)⟩
    have hstarvi : star (v i) * v i = ((b * b : ℝ) : ℂ) := by
      rw [hb, Complex.normSq_eq_conj_mul_self]
      rfl
    have hcs : star (((a / b : ℝ)) : ℂ) = (((a / b : ℝ)) : ℂ) := by
      rw [Complex.star_def]
      exact Complex.conj_ofReal _
    refine ⟨(((a / b : ℝ)) : ℂ) * v i, ?_, ?_⟩
    · rw [star_mul', hcs]
      rw [show (((a / b : ℝ)) : ℂ) * star (v i) * ((((a / b : ℝ)) : ℂ) * v i)
            = ((((a / b : ℝ)) : ℂ) * (((a / b : ℝ)) : ℂ)) * (star (v i) * v i) from by ring]
      rw [hstarvi, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        show (a / b) * (a / b) * (b * b) = a * a from by field_simp,
        Complex.ofReal_mul, ha]
    · rw [star_mul', hcs]
      ring

/-! ## Clearing a column -/

/-- **One reflection concentrates everything off an axis onto another axis.**  The reflection's
vector misses `m`, so the `m` component of `v` survives untouched while the rest is aligned
with `e_i`. -/
theorem exists_align_off_axis (v : Fin N → ℂ) (i m : Fin N) (him : m ≠ i) :
    ∃ (w : Fin N → ℂ) (lam : ℂ), w m = 0 ∧
      house w *ᵥ v = lam • axisVec i + (v m) • axisVec m := by
  obtain ⟨lam, hn, hr⟩ := exists_alignTarget (v - (v m) • axisVec m) i
  have hwm : ((v - (v m) • axisVec m) - lam • axisVec i) m = 0 := by
    rw [Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, axisVec_self,
      axisVec_ne him, smul_eq_mul, smul_eq_mul, mul_one, mul_zero, sub_zero, sub_self]
  refine ⟨(v - (v m) • axisVec m) - lam • axisVec i, lam, hwm, ?_⟩
  have hfix : house ((v - (v m) • axisVec m) - lam • axisVec i) *ᵥ ((v m) • axisVec m)
      = (v m) • axisVec m := by
    refine house_mulVec_of_orthogonal ?_
    rw [dotProduct_smul, dotProduct_axisVec, Pi.star_apply, hwm, star_zero, smul_zero]
  -- split `v` by linearity of `mulVec`, without rewriting `v` inside the reflection vector
  have hlin : house ((v - (v m) • axisVec m) - lam • axisVec i) *ᵥ (v - (v m) • axisVec m)
        + house ((v - (v m) • axisVec m) - lam • axisVec i) *ᵥ ((v m) • axisVec m)
      = house ((v - (v m) • axisVec m) - lam • axisVec i) *ᵥ v := by
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  rw [← hlin, hfix, house_mulVec_align hn hr]

/-- **Two reflections clear a vector onto one axis.**  The first leaves the vector supported on
`{i₀, i₁}`; that frees the axis `i₂`, which is what the second reflection's vector must miss.
Three distinct indices is exactly the `N ≥ 3` hypothesis of the complex row. -/
theorem exists_clear_column (v : Fin N → ℂ) {i₀ i₁ i₂ : Fin N}
    (h10 : i₁ ≠ i₀) (h20 : i₂ ≠ i₀) (h21 : i₂ ≠ i₁) :
    ∃ (w₁ w₂ : Fin N → ℂ) (lam : ℂ), w₁ i₁ = 0 ∧ w₂ i₂ = 0 ∧
      (house w₂ * house w₁) *ᵥ v = lam • axisVec i₀ := by
  obtain ⟨w₁, lam₁, hw₁, hstep₁⟩ := exists_align_off_axis v i₀ i₁ h10
  obtain ⟨w₂, lam₂, hw₂, hstep₂⟩ :=
    exists_align_off_axis (lam₁ • axisVec i₀ + (v i₁) • axisVec i₁) i₀ i₂ h20
  refine ⟨w₁, w₂, lam₂, hw₁, hw₂, ?_⟩
  have hzero : (lam₁ • axisVec i₀ + (v i₁) • axisVec i₁) i₂ = 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, axisVec_ne h20, axisVec_ne h21,
      smul_zero, smul_zero, add_zero]
  rw [← Matrix.mulVec_mulVec, hstep₁, hstep₂, hzero, zero_smul, add_zero]

/-! ## The factorization -/

/-- **Every unitary is a product of three axis-fixing unitaries** (`N ≥ 3`).

Clear the `i₀` column with two reflections; the residue is a unitary whose `i₀` column is
supported on `i₀`, hence fixes that axis.  Reflections are involutions, so multiplying back
recovers the original unitary. -/
theorem exists_axisFixing_factor (hN : 3 ≤ N) (W : Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ V₁ V₂ V₃ : Matrix.unitaryGroup (Fin N) ℂ,
      (∃ m, AxisFixing m (V₁ : Matrix (Fin N) (Fin N) ℂ)) ∧
      (∃ m, AxisFixing m (V₂ : Matrix (Fin N) (Fin N) ℂ)) ∧
      (∃ m, AxisFixing m (V₃ : Matrix (Fin N) (Fin N) ℂ)) ∧
      W = V₁ * V₂ * V₃ := by
  have h0 : (0 : ℕ) < N := by omega
  have h1 : (1 : ℕ) < N := by omega
  have h2 : (2 : ℕ) < N := by omega
  obtain ⟨w₁, w₂, lam, hw₁, hw₂, hclear⟩ :=
    exists_clear_column ((W : Matrix (Fin N) (Fin N) ℂ) *ᵥ axisVec ⟨0, h0⟩)
      (i₀ := ⟨0, h0⟩) (i₁ := ⟨1, h1⟩) (i₂ := ⟨2, h2⟩)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
      (by simp only [ne_eq, Fin.mk.injEq]; omega)
  set R₁ : Matrix.unitaryGroup (Fin N) ℂ := ⟨house w₁, house_mem_unitaryGroup w₁⟩ with hR₁def
  set R₂ : Matrix.unitaryGroup (Fin N) ℂ := ⟨house w₂, house_mem_unitaryGroup w₂⟩ with hR₂def
  have hR₁ : R₁ * R₁ = 1 := by
    apply Subtype.ext
    exact house_mul_self' w₁
  have hR₂ : R₂ * R₂ = 1 := by
    apply Subtype.ext
    exact house_mul_self' w₂
  refine ⟨R₁, R₂, R₂ * R₁ * W, ⟨⟨1, h1⟩, house_axisFixing hw₁⟩,
    ⟨⟨2, h2⟩, house_axisFixing hw₂⟩, ⟨⟨0, h0⟩, ?_⟩, ?_⟩
  · -- the residue's `i₀` column is supported on `i₀`
    refine axisFixing_of_col (unitaryGroup_conjTranspose_mul (R₂ * R₁ * W)) ?_
    intro k hk
    have hcol : ((R₂ * R₁ * W : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        *ᵥ axisVec ⟨0, h0⟩ = lam • axisVec ⟨0, h0⟩ := by
      have hco : ((R₂ * R₁ * W : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
          = house w₂ * house w₁ * (W : Matrix (Fin N) (Fin N) ℂ) := rfl
      rw [hco, ← Matrix.mulVec_mulVec, hclear]
    have hk' := congrFun hcol k
    rw [mulVec_axisVec, Pi.smul_apply, axisVec_ne hk, smul_zero] at hk'
    exact hk'
  · have hfac : R₁ * R₂ * (R₂ * R₁ * W) = W := by
      calc R₁ * R₂ * (R₂ * R₁ * W)
          = R₁ * ((R₂ * R₂) * (R₁ * W)) := by simp only [mul_assoc]
        _ = W := by rw [hR₂, one_mul, ← mul_assoc, hR₁, one_mul]
    exact hfac.symm

/-! ## Connectivity of the frame graph -/

/-- Right multiplication by an axis-fixing unitary is one adjacency step: the connecting
unitary `F*(FV) = V` is the factor itself. -/
theorem adjAxis_mul_right (F : Matrix.unitaryGroup (Fin N) ℂ)
    {V : Matrix.unitaryGroup (Fin N) ℂ} {m : Fin N}
    (hV : AxisFixing m (V : Matrix (Fin N) (Fin N) ℂ)) : AdjAxis F (F * V) := by
  refine ⟨m, fun i j hij hm => ?_⟩
  have hcoe : ((F : Matrix (Fin N) (Fin N) ℂ))ᴴ
        * ((F * V : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
      = (V : Matrix (Fin N) (Fin N) ℂ) := by
    have h : ((F * V : Matrix.unitaryGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        = (F : Matrix (Fin N) (Fin N) ℂ) * (V : Matrix (Fin N) (Fin N) ℂ) := rfl
    rw [h, ← Matrix.mul_assoc, unitaryGroup_conjTranspose_mul F, Matrix.one_mul]
  rw [hcoe]
  exact hV i j hij hm

/-- **The frame graph is connected** (`N ≥ 3`).  Any two frames are joined by a walk of three
axis adjacencies, one per factor of `F⁻¹G`. -/
theorem adjAxis_connected (hN : 3 ≤ N) (F G : Matrix.unitaryGroup (Fin N) ℂ) :
    Relation.ReflTransGen (MasterTheorem.Globalization.SymmStep AdjAxis) F G := by
  obtain ⟨V₁, V₂, V₃, ⟨m₁, h₁⟩, ⟨m₂, h₂⟩, ⟨m₃, h₃⟩, hfac⟩ :=
    exists_axisFixing_factor hN (F⁻¹ * G)
  have hG : G = F * V₁ * V₂ * V₃ := by
    have hstep : F * (V₁ * V₂ * V₃) = G := by
      rw [← hfac]
      group
    rw [← hstep]
    simp only [mul_assoc]
  rw [hG]
  exact Relation.ReflTransGen.tail (Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (Or.inl (adjAxis_mul_right F h₁)))
    (Or.inl (adjAxis_mul_right (F * V₁) h₂)))
    (Or.inl (adjAxis_mul_right (F * V₁ * V₂) h₃))

/-! ## `AdjAxis` is a proper relation, not a total one

`adjAxis_connected` would be empty of content if `AdjAxis` held of every pair — the walk
could always be taken in one step, and the Householder factorization it rests on would be
doing no work.  Until now that this is *not* the case was asserted in prose (an adversarial
review on 2026-08-07 checked it in a throwaway file); the caveat list in the supplementary
material recorded it as "asserted in a docstring but not itself a theorem of the tree".
It is now a theorem.

The witness is the Householder reflection in the **all-ones** direction.  Its off-diagonal
entries are all `-2/N`, uniformly nonzero, so it fixes no coordinate axis at all — which is
exactly the negation of `AdjAxis` against the identity frame. -/

/-- The all-ones vector: a Householder axis that meets every coordinate axis. -/
def onesVec (N : ℕ) : Fin N → ℂ := fun _ => 1

theorem nrm2_onesVec : nrm2 (onesVec N) = (N : ℝ) := by
  simp [nrm2, onesVec]

/-- **`AdjAxis` is not total** (`N ≥ 2`): the identity frame is not axis-adjacent to the
Householder reflection in the all-ones direction, because every off-diagonal entry of that
reflection is `-2/N ≠ 0`, so no axis `m` can have its row and column vanish off the
diagonal. -/
theorem not_adjAxis_one_house (hN : 2 ≤ N) :
    ¬ AdjAxis (1 : Matrix.unitaryGroup (Fin N) ℂ)
      ⟨house (onesVec N), house_mem_unitaryGroup _⟩ := by
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
  rintro ⟨m, hm⟩
  obtain ⟨j, hj⟩ := exists_ne m
  have hentry := hm m j (Ne.symm hj) (Or.inl rfl)
  simp only [Submonoid.coe_one, Matrix.conjTranspose_one, Matrix.one_mul] at hentry
  rw [house_apply, Matrix.one_apply_ne (Ne.symm hj), nrm2_onesVec] at hentry
  simp only [onesVec, star_one, mul_one, zero_sub, neg_eq_zero, mul_eq_zero] at hentry
  rcases hentry with h | h
  · norm_num at h
  · rw [Complex.ofReal_eq_zero, inv_eq_zero, Nat.cast_eq_zero] at h
    omega

/-- **The non-vacuity of the connectivity theorem, stated as such.**  `AdjAxis` is a proper
subrelation of the total relation on frames, so `adjAxis_connected` asserts something. -/
theorem adjAxis_not_total (hN : 2 ≤ N) :
    ∃ F G : Matrix.unitaryGroup (Fin N) ℂ, ¬ AdjAxis F G :=
  ⟨1, ⟨house (onesVec N), house_mem_unitaryGroup _⟩, not_adjAxis_one_house hN⟩

end Necessity
