/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.StrengthProbe
import RadicalRelativity.Necessity.ThetaCocycle

set_option linter.style.longLine false

/-!
# The two Jordan witnesses: conjugation and transpose-conjugation  (M3, 3.2d)

The Wigner dichotomy hands back a unitary or an antiunitary.  Both branches
land on Jordan automorphisms, which is the last step of M3:

* `unitaryConj` — `x ↦ U x U*` as an ℝ-linear map on `H_n(ℂ)`, and
  `unitaryConj_preservesJordan`: it preserves the symmetrized product for any
  `U` with `U* U = 1` (the `U* U` cancellation in the middle of the two
  products).
* `transposeMap` — `x ↦ xᵗ` on `H_n(ℂ)` (well defined: the transpose of a
  Hermitian matrix is Hermitian), and `transposeMap_preservesJordan`: the
  transpose is an *anti*-automorphism of matrix multiplication, hence an
  automorphism of the *symmetrized* product.
* `antiunitaryConj_preservesJordan` — the composite `x ↦ U xᵗ U*`, the
  antiunitary branch.

Together: whichever branch `Projectivization.wigner_rigidity` returns, the
induced order-automorphism satisfies `PreservesJordan`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Unitary conjugation -/

/-- Conjugation by a matrix, as an ℝ-linear map. -/
def unitaryConj (U : Matrix n n ℂ) : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ where
  toFun x := x.conj U
  map_add' x y := map_add (HermitianMat.conj U) x y
  map_smul' c x := by
    ext1
    rw [HermitianMat.conj_apply_mat, HermitianMat.mat_smul, HermitianMat.mat_smul,
      HermitianMat.conj_apply_mat, Matrix.mul_smul, Matrix.smul_mul]
    rfl

@[simp]
theorem unitaryConj_apply (U : Matrix n n ℂ) (x : HermitianMat n ℂ) :
    unitaryConj U x = x.conj U := rfl

/-- **The unitary branch is a Jordan automorphism**: `U* U = 1` cancels in the
middle of each product. -/
theorem unitaryConj_preservesJordan {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    PreservesJordan (unitaryConj U) := by
  intro x y
  ext1
  rw [unitaryConj_apply, HermitianMat.conj_apply_mat, HermitianMat.symmMul_toMat,
    HermitianMat.symmMul_toMat, unitaryConj_apply, unitaryConj_apply,
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

/-! ## Transposition -/

omit [Fintype n] [DecidableEq n] in
/-- The transpose of a Hermitian matrix is Hermitian. -/
theorem transpose_isHermitian (x : HermitianMat n ℂ) :
    (x.mat.transpose).IsHermitian := by
  show _ᴴ = _
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.transpose_apply]
  have h := congrFun₂ x.property j i
  rw [Matrix.star_apply] at h
  exact h

/-- Transposition as an ℝ-linear map on `H_n(ℂ)`. -/
def transposeMap : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ where
  toFun x := ⟨x.mat.transpose, transpose_isHermitian x⟩
  map_add' x y := by
    ext1
    show (x + y).mat.transpose = _
    rw [HermitianMat.mat_add, Matrix.transpose_add]
    rfl
  map_smul' c x := by
    ext1
    show (c • x).mat.transpose = _
    rw [HermitianMat.mat_smul, Matrix.transpose_smul, HermitianMat.mat_smul]
    rfl

@[simp]
theorem transposeMap_mat (x : HermitianMat n ℂ) :
    (transposeMap x).mat = x.mat.transpose := rfl

/-- **Transposition is a Jordan automorphism**: it reverses matrix products, but
the symmetrized product is invariant under reversal. -/
theorem transposeMap_preservesJordan :
    PreservesJordan (transposeMap (n := n)) := by
  intro x y
  ext1
  rw [transposeMap_mat, HermitianMat.symmMul_toMat, HermitianMat.symmMul_toMat,
    transposeMap_mat, transposeMap_mat]
  rw [Matrix.transpose_smul]
  congr 1
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]
  exact add_comm _ _

/-! ## The antiunitary branch -/

/-- **The antiunitary branch is a Jordan automorphism**: the composite of the
two witnesses. -/
theorem antiunitaryConj_preservesJordan {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    PreservesJordan ((unitaryConj U).comp (transposeMap (n := n))) := by
  intro x y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    transposeMap_preservesJordan x y, unitaryConj_preservesJordan hU]

end Necessity
