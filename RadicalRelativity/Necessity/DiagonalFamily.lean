/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.SharpEffects

set_option linter.style.longLine false

/-!
# The exponential diagonal family  (campaign LEDGER 2.6, instantiation data)

The concrete objects behind the `ComparisonSetup` fields `p` (the frame) and
`aOf` (the parametrized diagonal effects) on `H_n(ℂ)`:

* `frameProj i` — the diagonal unit projections (the standard Jordan frame);
* `diagFamily r := diag (exp (r i))` — the exponential family, with
  `diagFamily 0 = 1`, the semigroup law
  `diagFamily r · diagFamily r' = diagFamily (r + r')`, positive definiteness
  everywhere, effect-ness on the negative orthant, commutation with the frame,
  and the frame decomposition `diagFamily r = ∑ exp (r i) • frameProj i`.

Everything here is product-independent matrix bookkeeping over the vendored
`HermitianMat.diagonal` kit.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The standard diagonal frame: `frameProj i = diag (δ_i)`. -/
def frameProj (i : n) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun j => if j = i then 1 else 0)

/-- The exponential diagonal family `aOf r = diag (exp (r i))`. -/
def diagFamily (r : n → ℝ) : HermitianMat n ℂ :=
  HermitianMat.diagonal ℂ (fun i => Real.exp (r i))

@[simp]
theorem diagFamily_mat (r : n → ℝ) :
    (diagFamily r).mat = Matrix.diagonal (fun i => (Real.exp (r i) : ℂ)) :=
  HermitianMat.diagonal_mat _

theorem diagFamily_zero : diagFamily (0 : n → ℝ) = 1 := by
  rw [show diagFamily (0 : n → ℝ) = (HermitianMat.diagonal ℂ 1 : HermitianMat n ℂ) from by
    unfold diagFamily
    congr 1
    funext i
    simp [Real.exp_zero]]
  exact HermitianMat.diagonal_one

/-- The multiplicative law of the family. -/
theorem diagFamily_mul (r r' : n → ℝ) :
    (diagFamily r).mat * (diagFamily r').mat = (diagFamily (r + r')).mat := by
  rw [diagFamily_mat, diagFamily_mat, diagFamily_mat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  show (Real.exp (r i) : ℂ) * (Real.exp (r' i) : ℂ) = (Real.exp ((r + r') i) : ℂ)
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  rfl

theorem diagFamily_commute (r r' : n → ℝ) :
    Commute (diagFamily r).mat (diagFamily r').mat := by
  show _ * _ = _ * _
  rw [diagFamily_mul, diagFamily_mul, add_comm]

/-- The family is positive definite everywhere. -/
theorem diagFamily_posDef (r : n → ℝ) : (diagFamily r).mat.PosDef := by
  rw [diagFamily_mat]
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast Real.exp_pos (r i)

/-- On the negative orthant the family consists of effects. -/
theorem diagFamily_isEffect {r : n → ℝ} (hr : ∀ i, r i ≤ 0) :
    IsEffect (diagFamily r) := by
  constructor
  · rw [HermitianMat.zero_le_iff, diagFamily_mat]
    apply Matrix.PosSemidef.diagonal
    intro i
    show (0 : ℂ) ≤ (Real.exp (r i) : ℂ)
    exact_mod_cast le_of_lt (Real.exp_pos (r i))
  · have hsub : (1 : HermitianMat n ℂ) - diagFamily r
        = HermitianMat.diagonal ℂ (fun i => 1 - Real.exp (r i)) := by
      rw [show (fun i : n => 1 - Real.exp (r i))
          = (1 : n → ℝ) - fun i => Real.exp (r i) from rfl,
        HermitianMat.diagonal_sub, HermitianMat.diagonal_one]
      rfl
    have hpos : (0 : HermitianMat n ℂ) ≤ 1 - diagFamily r := by
      rw [HermitianMat.zero_le_iff, hsub, HermitianMat.diagonal_mat]
      apply Matrix.PosSemidef.diagonal
      intro i
      have h1 : Real.exp (r i) ≤ 1 := Real.exp_le_one_iff.mpr (hr i)
      show (0 : ℂ) ≤ ((1 - Real.exp (r i) : ℝ) : ℂ)
      exact_mod_cast sub_nonneg.mpr h1
    exact sub_nonneg.mp hpos

/-! ## The frame -/

theorem frameProj_mat (i : n) :
    (frameProj i).mat = Matrix.diagonal (fun j => if j = i then (1 : ℂ) else 0) := by
  rw [frameProj, HermitianMat.diagonal_mat]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

theorem frameProj_isProjection (i : n) : (frameProj i).IsProjection := by
  rw [HermitianMat.isProjection_iff_mat_mul_self, frameProj_mat,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

theorem frameProj_orth {i j : n} (hij : i ≠ j) :
    (frameProj i).mat * (frameProj j).mat = 0 := by
  rw [frameProj_mat, frameProj_mat, Matrix.diagonal_mul_diagonal]
  rw [show (fun k => (if k = i then (1:ℂ) else 0) * (if k = j then 1 else 0))
      = fun _ => (0 : ℂ) from by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [hij]
    · simp [hk]]
  simp

theorem sum_frameProj : ∑ i : n, frameProj i = (1 : HermitianMat n ℂ) := by
  ext1
  rw [mat_finsetSum]
  simp only [frameProj_mat]
  rw [show (∑ i : n, Matrix.diagonal (fun j => if j = i then (1:ℂ) else 0))
      = Matrix.diagonal (∑ i : n, fun j => if j = i then (1:ℂ) else 0) from
    (map_sum (Matrix.diagonalAddMonoidHom n ℂ) _ Finset.univ).symm]
  rw [show (∑ i : n, fun j => if j = i then (1:ℂ) else 0) = fun _ => (1:ℂ) from
    funext fun j => by
      rw [Finset.sum_apply]
      simp [Finset.sum_ite_eq]]
  rw [HermitianMat.mat_one, Matrix.diagonal_one]

/-- The frame decomposition of the family. -/
theorem diagFamily_eq_sum_frameProj (r : n → ℝ) :
    diagFamily r = ∑ i : n, Real.exp (r i) • frameProj i := by
  ext1
  rw [mat_finsetSum, diagFamily_mat]
  simp only [HermitianMat.mat_smul, frameProj_mat, ← Matrix.diagonal_smul]
  rw [show (∑ i : n, Matrix.diagonal (Real.exp (r i) • fun k => if k = i then (1:ℂ) else 0))
      = Matrix.diagonal (∑ i : n, Real.exp (r i) • fun k => if k = i then (1:ℂ) else 0) from
    (map_sum (Matrix.diagonalAddMonoidHom n ℂ) _ Finset.univ).symm]
  congr 1
  funext j
  rw [Finset.sum_apply]
  rw [show (fun i : n => (Real.exp (r i) • fun k => if k = i then (1:ℂ) else 0) j)
      = fun i : n => if j = i then (Real.exp (r i) : ℂ) else 0 from funext fun i => by
    simp only [Pi.smul_apply]
    by_cases h : j = i <;> simp [h, Complex.real_smul]]
  rw [Finset.sum_ite_eq]
  simp

/-- The family commutes with every frame projection. -/
theorem diagFamily_commute_frameProj (r : n → ℝ) (i : n) :
    Commute (diagFamily r).mat (frameProj i).mat := by
  show _ * _ = _ * _
  rw [diagFamily_mat, frameProj_mat, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  ring

end Necessity
