/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.JordanWitness

set_option linter.style.longLine false

/-!
# Rank-one projections span  (M3, 3.2d)

The rank-one projections span `H_n(ℂ)` over `ℝ`, so two `ℝ`-linear maps that
agree on them are equal.  This is what upgrades "`Φ` acts as a unitary /
antiunitary on rank-ones" (the Wigner output) to "`Φ` *is* that Jordan
automorphism", finishing M3.

The proof avoids the spectral theorem entirely.  The vendored trace inner
product makes `H_n(ℂ)` a real inner product space, and

`⟪y, ψψ*⟫ = Re tr(y ψψ*) = Re (ψ* y ψ)`,

so a `y` orthogonal to every rank-one projection has identically vanishing
quadratic form; then `0 ≤ y` and `y ≤ 0` both hold, so `y = 0`.  A finite
-dimensional subspace with trivial orthogonal complement is everything.

* `eq_zero_of_quadratic_zero` — the two-sided-positivity kill.
* `inner_rankOne` — the trace pairing against a rank-one is the quadratic form.
* `span_rankOne_eq_top` — the span is `⊤`.
* `linearMap_eq_of_eq_on_rankOne` — the consequence used by M3.
-/

noncomputable section

open ComplexOrder RealInnerProductSpace
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## A vanishing quadratic form kills the matrix -/

omit [DecidableEq n] in
/-- If the quadratic form of a Hermitian matrix vanishes identically then the
matrix is zero: the form being `≥ 0` gives `0 ≤ y`, being `≤ 0` gives `y ≤ 0`. -/
theorem eq_zero_of_quadratic_zero {y : HermitianMat n ℂ}
    (h : ∀ v : n → ℂ, star v ⬝ᵥ y.mat *ᵥ v = 0) : y = 0 := by
  have hpos : (0 : HermitianMat n ℂ) ≤ y := by
    rw [le_iff_mulVec_le_mulVec]
    intro v
    rw [h v, mat_zero, Matrix.zero_mulVec, dotProduct_zero]
  have hneg : y ≤ 0 := by
    rw [le_iff_mulVec_le_mulVec]
    intro v
    rw [h v, mat_zero, Matrix.zero_mulVec, dotProduct_zero]
  exact le_antisymm hneg hpos

/-! ## The trace pairing against a rank-one -/

omit [DecidableEq n] in
/-- `⟪y, ψψ*⟫ = Re (ψ* y ψ)`: the trace pairing against a rank-one projection is
the quadratic form. -/
theorem inner_rankOne (y : HermitianMat n ℂ) (ψ : n → ℂ) :
    ⟪y, rankOne ψ⟫ = RCLike.re (star ψ ⬝ᵥ y.mat *ᵥ ψ) := by
  rw [inner_eq_re_trace]
  congr 1
  rw [rankOne_mat]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-! ## The span -/

/-- The set of rank-one projections of unit vectors. -/
def rankOneSet (n : Type*) [Fintype n] [DecidableEq n] :
    Set (HermitianMat n ℂ) :=
  {p | ∃ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ p = rankOne ψ}

set_option maxHeartbeats 1600000 in
/-- **The rank-one projections span `H_n(ℂ)` over `ℝ`.**  A vector orthogonal to
all of them has vanishing quadratic form (rescale an arbitrary vector to a unit
vector), hence is zero; in finite dimensions a subspace with trivial orthogonal
complement is everything. -/
theorem span_rankOne_eq_top :
    Submodule.span ℝ (rankOneSet n) = ⊤ := by
  have hbot : (Submodule.span ℝ (rankOneSet n))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hgen : ∀ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 → ⟪y, rankOne ψ⟫ = 0 := by
      intro ψ hψ
      have h0 := hy _ (Submodule.subset_span ⟨ψ, hψ, rfl⟩)
      rw [real_inner_comm] at h0
      exact h0
    apply eq_zero_of_quadratic_zero
    intro v
    -- the quadratic form is real; rescale `v` to a unit vector
    have hreal : ∃ r : ℝ, star v ⬝ᵥ y.mat *ᵥ v = (r : ℂ) := by
      refine ⟨RCLike.re (star v ⬝ᵥ y.mat *ᵥ v), ?_⟩
      have hy' : (star v ⬝ᵥ y.mat *ᵥ v) = star (star v ⬝ᵥ y.mat *ᵥ v) := by
        have hH : (y.mat)ᴴ = y.mat := y.H
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum,
          star_mul', star_star, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        have hij : star (y.mat i j) = y.mat j i := by
          have hc := congrArg (fun M : Matrix n n ℂ => M j i) hH
          simpa [Matrix.conjTranspose_apply] using hc
        rw [← hij]
        ring
      have := Complex.conj_eq_iff_re.mp hy'.symm
      exact this.symm
    obtain ⟨r, hr⟩ := hreal
    by_cases hv : nsq v = 0
    · -- `v = 0`
      have hz : v = 0 := by
        funext i
        have hle : Complex.normSq (v i) ≤ nsq v :=
          Finset.single_le_sum (f := fun j => Complex.normSq (v j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
        have h2 := Complex.normSq_nonneg (v i)
        exact Complex.normSq_eq_zero.mp (by linarith [hv ▸ hle])
      rw [hz]
      simp
    · have hpos : 0 < nsq v := lt_of_le_of_ne (nsq_nonneg v) (Ne.symm hv)
      set c : ℝ := (Real.sqrt (nsq v))⁻¹ with hc
      set u : n → ℂ := (c : ℂ) • v with hu
      have hunit : star u ⬝ᵥ u = 1 := by
        rw [hu, dot_self_eq_nsq, nsq_smul]
        have hnn : Complex.normSq (c : ℂ) = c ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.ofReal_re, Complex.ofReal_im]
          ring
        rw [hnn, hc, inv_pow, Real.sq_sqrt hpos.le,
          show (nsq v)⁻¹ * nsq v = 1 from inv_mul_cancel₀ hv]
        norm_num
      have hq := hgen u hunit
      rw [inner_rankOne] at hq
      -- the form at `u` is `c²` times the form at `v`
      have hscale : star u ⬝ᵥ y.mat *ᵥ u
          = ((c ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ y.mat *ᵥ v) := by
        rw [hu, Matrix.mulVec_smul, dotProduct_smul]
        rw [show star ((c : ℂ) • v) = star (c : ℂ) • star v from star_smul _ _]
        rw [smul_dotProduct, smul_eq_mul, smul_eq_mul, Complex.star_def,
          Complex.conj_ofReal]
        push_cast
        ring
      rw [hscale, hr] at hq
      rw [show ((c ^ 2 : ℝ) : ℂ) * ((r : ℝ) : ℂ) = ((c ^ 2 * r : ℝ) : ℂ) from by
        push_cast; ring] at hq
      rw [show RCLike.re ((c ^ 2 * r : ℝ) : ℂ) = c ^ 2 * r from Complex.ofReal_re _] at hq
      have hcne : c ^ 2 ≠ 0 := by
        rw [hc]
        positivity
      have hr0 : r = 0 := by
        have : c ^ 2 * r = 0 := by linarith [hq]
        exact (mul_eq_zero.mp this).resolve_left hcne
      rw [hr, hr0]
      norm_num
  exact Submodule.orthogonal_eq_bot_iff.mp hbot

/-! ## The consequence M3 uses -/

/-- **Agreement on rank-ones is agreement everywhere.** -/
theorem linearMap_eq_of_eq_on_rankOne {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S T : HermitianMat n ℂ →ₗ[ℝ] W)
    (h : ∀ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 → S (rankOne ψ) = T (rankOne ψ)) :
    S = T := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℝ (rankOneSet n) := by
    rw [span_rankOne_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨ψ, hψ, rfl⟩ := hp
      exact h ψ hψ
  | zero => rw [map_zero, map_zero]
  | add a b _ _ iha ihb => rw [map_add, map_add, iha, ihb]
  | smul c a _ ih => rw [map_smul, map_smul, ih]

end HermitianMat
