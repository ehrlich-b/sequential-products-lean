/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealRayMap
import RadicalRelativity.Necessity.ProjectionOrder

set_option linter.style.longLine false

/-!
# Real rank-one projections span  (the ℝ bridge to real Kadison, part 2)

The bridge's second step: **agreement on rank-one projections is agreement everywhere.**
That is what converts "the ray map is induced by an orthogonal matrix" (real Wigner) into
"the comparison map IS conjugation by that matrix", which is what makes it a Jordan
automorphism.

* `eq_zero_of_quadratic_zeroR` — a symmetric matrix with identically vanishing quadratic
  form is zero.  Over ℝ this is one line per direction: the form being both `≥ 0` and `≤ 0`
  pins `y` between `0` and `0`.
* `inner_rankOneR` — the trace pairing against `ψψᵀ` is the quadratic form.  Over ℝ there is
  no `RCLike.re` to strip and no conjugate to move.
* `span_rankOneR_eq_top` — the rank-one projections of unit vectors span, because a matrix
  orthogonal to all of them has vanishing quadratic form.  The normalization step is where
  ℝ is markedly shorter than ℂ: rescaling multiplies the form by `c²` with `c` real, so
  there is no `normSq` computation at all.
* `linearMap_eq_of_eq_on_rankOneR` — the consequence the bridge consumes.
-/

noncomputable section

open RealInnerProductSpace
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A vanishing quadratic form kills the matrix -/

omit [DecidableEq n] in
/-- If the quadratic form of a symmetric matrix vanishes identically then the matrix is
zero: the form being `≥ 0` gives `0 ≤ y`, being `≤ 0` gives `y ≤ 0`. -/
theorem eq_zero_of_quadratic_zeroR {y : HermitianMat n ℝ}
    (h : ∀ v : n → ℝ, v ⬝ᵥ y.mat *ᵥ v = 0) : y = 0 := by
  have key : ∀ v : n → ℝ, star v ⬝ᵥ y.mat *ᵥ v = 0 := by
    intro v
    rw [star_trivial]
    exact h v
  have hpos : (0 : HermitianMat n ℝ) ≤ y := by
    rw [HermitianMat.le_iff_mulVec_le_mulVec]
    intro v
    rw [key v, HermitianMat.mat_zero, Matrix.zero_mulVec, dotProduct_zero]
  have hneg : y ≤ 0 := by
    rw [HermitianMat.le_iff_mulVec_le_mulVec]
    intro v
    rw [key v, HermitianMat.mat_zero, Matrix.zero_mulVec, dotProduct_zero]
  exact le_antisymm hneg hpos

/-! ## The trace pairing is the quadratic form -/

omit [DecidableEq n] in
/-- `⟪y, ψψᵀ⟫ = ψᵀ y ψ`. -/
theorem inner_rankOneR (y : HermitianMat n ℝ) (ψ : n → ℝ) :
    (inner ℝ y (rankOneR ψ) : ℝ) = ψ ⬝ᵥ y.mat *ᵥ ψ := by
  rw [HermitianMat.inner_eq_re_trace, Matrix.trace_mul_comm, trace_rankOneR_mul]
  simp

/-! ## The span -/

/-- The set of rank-one projections of unit vectors. -/
def rankOneSetR (n : Type*) [Fintype n] [DecidableEq n] : Set (HermitianMat n ℝ) :=
  {p | ∃ ψ : n → ℝ, ψ ⬝ᵥ ψ = 1 ∧ rankOneR ψ = p}

omit [DecidableEq n] in
theorem dotProduct_self_nonnegR (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- **The rank-one projections span.**  A matrix orthogonal to all of them has vanishing
quadratic form (rescale each vector to a unit vector), hence is zero; in finite dimensions
a subspace with trivial orthogonal complement is everything. -/
theorem span_rankOneR_eq_top :
    Submodule.span ℝ (rankOneSetR n) = ⊤ := by
  have hbot : (Submodule.span ℝ (rankOneSetR n))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hgen : ∀ ψ : n → ℝ, ψ ⬝ᵥ ψ = 1 → (inner ℝ y (rankOneR ψ) : ℝ) = 0 := by
      intro ψ hψ
      have h0 := hy _ (Submodule.subset_span ⟨ψ, hψ, rfl⟩)
      rw [real_inner_comm] at h0
      exact h0
    apply eq_zero_of_quadratic_zeroR
    intro v
    by_cases hv : v ⬝ᵥ v = 0
    · rw [dotProduct_self_eq_zero.mp hv, Matrix.mulVec_zero, dotProduct_zero]
    · -- rescale to a unit vector; over ℝ the form just picks up `c²`
      have hpos : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonnegR v) (Ne.symm hv)
      have hcne : ((Real.sqrt (v ⬝ᵥ v))⁻¹ : ℝ) ≠ 0 :=
        inv_ne_zero (Real.sqrt_ne_zero'.mpr hpos)
      have hcsq : ((Real.sqrt (v ⬝ᵥ v))⁻¹ : ℝ) ^ 2 = (v ⬝ᵥ v)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hpos.le]
      have hunit : ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) = 1 := by
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          ← sq, hcsq, inv_mul_cancel₀ hv]
      have hq := hgen _ hunit
      rw [inner_rankOneR] at hq
      -- the form at the rescaled vector is `c²` times the form at `v`
      have hscale : ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v) ⬝ᵥ y.mat *ᵥ ((Real.sqrt (v ⬝ᵥ v))⁻¹ • v)
          = ((Real.sqrt (v ⬝ᵥ v))⁻¹ : ℝ) ^ 2 * (v ⬝ᵥ y.mat *ᵥ v) := by
        rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          ← mul_assoc, ← sq]
      rw [hscale] at hq
      exact (mul_eq_zero.mp hq).resolve_left (pow_ne_zero 2 hcne)
  exact Submodule.orthogonal_eq_bot_iff.mp hbot

/-! ## The consequence the bridge uses -/

/-- **Agreement on rank-ones is agreement everywhere.** -/
theorem linearMap_eq_of_eq_on_rankOneR {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S T : HermitianMat n ℝ →ₗ[ℝ] W)
    (h : ∀ ψ : n → ℝ, ψ ⬝ᵥ ψ = 1 → S (rankOneR ψ) = T (rankOneR ψ)) :
    S = T := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℝ (rankOneSetR n) := by
    rw [span_rankOneR_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨ψ, hψ, rfl⟩ := hp
      exact h ψ hψ
  | zero => rw [map_zero, map_zero]
  | add a b _ _ iha ihb => rw [map_add, map_add, iha, ihb]
  | smul c a _ ih => rw [map_smul, map_smul, ih]

end Necessity
