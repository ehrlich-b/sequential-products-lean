/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealRankOneSpan
import RadicalRelativity.Necessity.ThetaCocycle

set_option linter.style.longLine false

/-!
# Orthogonal conjugation is a Jordan automorphism  (the ℝ bridge to real Kadison, part 3)

The bridge's third step, and the reason the ℝ chain is shorter than the ℂ one: real Wigner
produces an **orthogonal** map, and conjugation by an orthogonal matrix already preserves the
Jordan product.  The ℂ lane needs a second branch here — its `JordanWitness` also builds
`transposeMap` and proves the *antiunitary* case, because complex Wigner allows a
conjugate-linear alternative.  **Over ℝ that branch does not exist**, so this file is the
whole of the step.

* `orthConj U` — conjugation `x ↦ U x Uᵀ` as an ℝ-linear map on symmetric matrices.
* `orthConj_preservesJordan` — `UᵀU = 1` cancels in the middle of each product.
* `orthConj_rankOneR` — conjugation moves rank-ones to rank-ones, `U(ψψᵀ)Uᵀ = (Uψ)(Uψ)ᵀ`.
  This is the compatibility that lets the span argument of part 2 be applied to a conjugation.

Note on duplication: the ℂ `unitaryConj` and its Jordan lemma happen to have no ℂ-specific
content and could be generalized in place, but they live in a file that is ℂ-bound elsewhere
(`rankOne`), and that file is finished and banked.  Re-deriving thirty lines here is cheaper
than reopening it, and keeps the campaign's rule of not touching completed rows.
-/

noncomputable section

open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Conjugation as a linear map -/

/-- Conjugation by a real matrix, as an ℝ-linear map. -/
def orthConj (U : Matrix n n ℝ) : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ where
  toFun x := x.conj U
  map_add' x y := map_add (HermitianMat.conj U) x y
  map_smul' c x := by
    ext1
    rw [HermitianMat.conj_apply_mat, HermitianMat.mat_smul, HermitianMat.mat_smul,
      HermitianMat.conj_apply_mat, Matrix.mul_smul, Matrix.smul_mul]
    rfl

omit [DecidableEq n] in
@[simp]
theorem orthConj_apply (U : Matrix n n ℝ) (x : HermitianMat n ℝ) :
    orthConj U x = x.conj U := rfl

/-! ## It preserves the Jordan product -/

/-- **Orthogonal conjugation is a Jordan automorphism**: `UᵀU = 1` cancels in the middle of
each product.  Over ℝ this is the ONLY branch — there is no antiunitary alternative. -/
theorem orthConj_preservesJordan {U : Matrix n n ℝ} (hU : Uᴴ * U = 1) :
    PreservesJordan (orthConj U) := by
  intro x y
  ext1
  rw [orthConj_apply, HermitianMat.conj_apply_mat, HermitianMat.symmMul_toMat,
    HermitianMat.symmMul_toMat, orthConj_apply, orthConj_apply,
    HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · calc U * (x.mat * y.mat) * Uᴴ
        = U * x.mat * (Uᴴ * U) * y.mat * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * x.mat * Uᴴ * (U * y.mat * Uᴴ) := by noncomm_ring
  · calc U * (y.mat * x.mat) * Uᴴ
        = U * y.mat * (Uᴴ * U) * x.mat * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * y.mat * Uᴴ * (U * x.mat * Uᴴ) := by noncomm_ring

/-! ## It moves rank-ones to rank-ones -/

omit [DecidableEq n] in
/-- **`U(ψψᵀ)Uᵀ = (Uψ)(Uψ)ᵀ`.**  So a conjugation is determined on the rank-ones by its
action on vectors, which is exactly the hypothesis shape that part 2's span argument
consumes. -/
theorem orthConj_rankOneR (U : Matrix n n ℝ) (ψ : n → ℝ) :
    orthConj U (rankOneR ψ) = rankOneR (U *ᵥ ψ) := by
  ext1
  rw [orthConj_apply, HermitianMat.conj_apply_mat, rankOneR_mat, rankOneR_mat]
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, star_trivial, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end Necessity
