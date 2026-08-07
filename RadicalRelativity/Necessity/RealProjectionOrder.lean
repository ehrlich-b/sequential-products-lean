/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealStrength

set_option linter.style.longLine false

/-!
# Atoms of the real projection order  (the ℝ bridge to real Kadison, part 5a)

Unit 5's only prerequisite is **rank-one transport**: an order automorphism carries rank-one
projections to rank-one projections.  That needs rank-ones to be exactly the *atoms* of the
projection order, since atomicity is what an order automorphism can see.

**Route note — this does NOT port the ℂ proof.**  The ℂ argument (`ProjectionOrder` 136-268)
manipulates `vecMulVec` factorizations directly.  Over ℝ there is a shorter conceptual route,
and it is worth writing down because it is the reason this step is not a boulder:

* for a projection `q`, the quadratic form IS a squared norm: `v·qv = |qv|²`
  (`quadForm_isProjection` below, using `q² = q` and `qᵀ = q`);
* so `q ≤ ψψᵀ` forces `qv = 0` for every `v ⊥ ψ`, because `v·qv ≤ (ψ·v)² = 0`;
* hence `range q ⊆ span{qψ}`, and idempotence applied to `qψ = aψ + v₀` gives `a = 1` or
  `qψ = 0`;
* the first case forces `v₀ = 0` by comparing `|qψ|² = ψ·qψ = 1` with `|ψ|² + |v₀|²`, so
  `q = ψψᵀ`; the second gives `q = 0`.

This file supplies the definition and the engine (`quadForm_isProjection`, plus the
nonvanishing of a rank-one); the two-case argument above is the remaining step.
-/

noncomputable section

open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An **atom** of the real projection order: a nonzero projection with no proper nonzero
subprojection. -/
def IsAtomProjectionR (p : HermitianMat n ℝ) : Prop :=
  p.IsProjection ∧ p ≠ 0 ∧
    ∀ q : HermitianMat n ℝ, q.IsProjection → q ≤ p → q = 0 ∨ q = p

/-- **For a projection the quadratic form is a squared norm.**  This is the engine of the
atom argument: it converts an order bound `q ≤ a` into the *vanishing* of `q` on vectors
where `a`'s form vanishes, which is much stronger than an inequality. -/
theorem quadForm_isProjection {q : HermitianMat n ℝ} (hq : q.IsProjection) (v : n → ℝ) :
    v ⬝ᵥ (q.mat *ᵥ v) = (q.mat *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) := by
  have hmul : q.mat * q.mat = q.mat := HermitianMat.isProjection_iff_mat_mul_self.mp hq
  have hsym : q.matᵀ = q.mat := by
    have h : q.matᴴ = q.mat := q.H
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  calc v ⬝ᵥ (q.mat *ᵥ v)
      = v ⬝ᵥ ((q.mat * q.mat) *ᵥ v) := by rw [hmul]
    _ = v ⬝ᵥ (q.mat *ᵥ (q.mat *ᵥ v)) := by rw [Matrix.mulVec_mulVec]
    _ = (q.matᵀ *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) := by
        rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    _ = (q.mat *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) := by rw [hsym]

/-- A subprojection of `ψψᵀ` annihilates everything orthogonal to `ψ`. -/
theorem mulVec_eq_zero_of_le_rankOneR {q : HermitianMat n ℝ} (hq : q.IsProjection)
    {ψ : n → ℝ} (hle : q ≤ rankOneR ψ) {v : n → ℝ} (hv : ψ ⬝ᵥ v = 0) :
    q.mat *ᵥ v = 0 := by
  have hform := (HermitianMat.le_iff_mulVec_le_mulVec _ _).mp hle v
  rw [star_trivial, quadForm_rankOneR, hv] at hform
  rw [quadForm_isProjection hq] at hform
  have hz : (q.mat *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) = 0 :=
    le_antisymm (by simpa using hform) (dotProduct_self_nonnegR _)
  exact dotProduct_self_eq_zero.mp hz

theorem rankOneR_ne_zero {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) : rankOneR ψ ≠ 0 := by
  intro h
  have hq := quadForm_rankOneR ψ ψ
  rw [h, HermitianMat.mat_zero, Matrix.zero_mulVec, dotProduct_zero, hψ] at hq
  norm_num at hq

end Necessity
