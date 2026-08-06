/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.SharpEffects

set_option linter.style.longLine false

/-!
# The exponential diagonal family, over any `RCLike` field  (M4.1 foundation)

The concrete objects behind the `ComparisonSetup` fields `p` (the frame) and
`aOf` (the parametrized diagonal effects) on `H_n(𝕜)`:

* `frameProjG 𝕜 i` — the diagonal unit projections (the standard Jordan frame);
* `diagFamilyG 𝕜 r := diag (exp (r i))` — the exponential family, with
  `diagFamilyG 𝕜 0 = 1`, the semigroup law
  `diagFamilyG 𝕜 r · diagFamilyG 𝕜 r' = diagFamilyG 𝕜 (r + r')`, positive definiteness
  everywhere, effect-ness on the negative orthant, commutation with the frame,
  and the frame decomposition `diagFamilyG 𝕜 r = ∑ exp (r i) • frameProjG 𝕜 i`.

Everything here is product-independent matrix bookkeeping over the vendored
`HermitianMat.diagonal` kit, and it is stated over an arbitrary `RCLike 𝕜` with
the scalar **explicit** — `frameProjG 𝕜 i`, `diagFamilyG 𝕜 r` — because the entry
lemmas (`frameProjG_mat` and friends) mention the scalar only inside the
definition, so an implicit one would be undetermined.

`Necessity/DiagonalFamily.lean` keeps the ℂ-specialized names the complex lane
uses; this file is the field-general twin the real branch (M4.1) consumes, added
alongside rather than by generalizing in place so that every complex-row proof
keeps compiling untouched (generalizing in place leaks into downstream proofs at
unconstrained intermediate `have` statements — e.g. `Chi.lean`'s square-root
step, where nothing pins the scalar).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The standard diagonal frame: `frameProjG 𝕜 i = diag (δ_i)`. -/
def frameProjG (𝕜 : Type*) [RCLike 𝕜] (i : n) : HermitianMat n 𝕜 :=
  HermitianMat.diagonal 𝕜 (fun j => if j = i then 1 else 0)

/-- The exponential diagonal family `aOf r = diag (exp (r i))`. -/
def diagFamilyG (𝕜 : Type*) [RCLike 𝕜] (r : n → ℝ) : HermitianMat n 𝕜 :=
  HermitianMat.diagonal 𝕜 (fun i => Real.exp (r i))

@[simp]
theorem diagFamilyG_mat (r : n → ℝ) :
    (diagFamilyG 𝕜 r).mat = Matrix.diagonal (fun i => (Real.exp (r i) : 𝕜)) :=
  HermitianMat.diagonal_mat _

theorem diagFamilyG_zero : diagFamilyG 𝕜 (0 : n → ℝ) = 1 := by
  rw [show diagFamilyG 𝕜 (0 : n → ℝ) = (HermitianMat.diagonal 𝕜 1 : HermitianMat n 𝕜) from by
    unfold diagFamilyG
    congr 1
    funext i
    simp [Real.exp_zero]]
  exact HermitianMat.diagonal_one

/-- The multiplicative law of the family. -/
theorem diagFamilyG_mul (r r' : n → ℝ) :
    (diagFamilyG 𝕜 r).mat * (diagFamilyG 𝕜 r').mat
      = (diagFamilyG 𝕜 (r + r')).mat := by
  rw [diagFamilyG_mat, diagFamilyG_mat, diagFamilyG_mat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  show (Real.exp (r i) : 𝕜) * (Real.exp (r' i) : 𝕜) = (Real.exp ((r + r') i) : 𝕜)
  rw [← RCLike.ofReal_mul, ← Real.exp_add]
  rfl

theorem diagFamilyG_commute (r r' : n → ℝ) :
    Commute (diagFamilyG 𝕜 r).mat (diagFamilyG 𝕜 r').mat := by
  show _ * _ = _ * _
  rw [diagFamilyG_mul, diagFamilyG_mul, add_comm]

/-- The family is positive definite everywhere. -/
theorem diagFamilyG_posDef (r : n → ℝ) : (diagFamilyG 𝕜 r).mat.PosDef := by
  rw [diagFamilyG_mat]
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast Real.exp_pos (r i)

/-- On the negative orthant the family consists of effects. -/
theorem diagFamilyG_isEffect {r : n → ℝ} (hr : ∀ i, r i ≤ 0) :
    IsEffect (diagFamilyG 𝕜 r) := by
  constructor
  · rw [HermitianMat.zero_le_iff, diagFamilyG_mat]
    apply Matrix.PosSemidef.diagonal
    intro i
    show (0 : 𝕜) ≤ (Real.exp (r i) : 𝕜)
    exact_mod_cast le_of_lt (Real.exp_pos (r i))
  · have hsub : (1 : HermitianMat n 𝕜) - diagFamilyG 𝕜 r
        = HermitianMat.diagonal 𝕜 (fun i => 1 - Real.exp (r i)) := by
      rw [show (fun i : n => 1 - Real.exp (r i))
          = (1 : n → ℝ) - fun i => Real.exp (r i) from rfl,
        HermitianMat.diagonal_sub, HermitianMat.diagonal_one]
      rfl
    have hpos : (0 : HermitianMat n 𝕜) ≤ 1 - diagFamilyG 𝕜 r := by
      rw [HermitianMat.zero_le_iff, hsub, HermitianMat.diagonal_mat]
      apply Matrix.PosSemidef.diagonal
      intro i
      have h1 : Real.exp (r i) ≤ 1 := Real.exp_le_one_iff.mpr (hr i)
      show (0 : 𝕜) ≤ ((1 - Real.exp (r i) : ℝ) : 𝕜)
      exact_mod_cast sub_nonneg.mpr h1
    exact sub_nonneg.mp hpos

/-! ## The frame -/

theorem frameProjG_mat (i : n) :
    (frameProjG 𝕜 i).mat
      = Matrix.diagonal (fun j => if j = i then (1 : 𝕜) else 0) := by
  rw [frameProjG, HermitianMat.diagonal_mat]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

theorem frameProjG_isProjection (i : n) : (frameProjG 𝕜 i).IsProjection := by
  rw [HermitianMat.isProjection_iff_mat_mul_self, frameProjG_mat,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]

theorem frameProjG_orth {i j : n} (hij : i ≠ j) :
    (frameProjG 𝕜 i).mat * (frameProjG 𝕜 j).mat = 0 := by
  rw [frameProjG_mat, frameProjG_mat, Matrix.diagonal_mul_diagonal]
  rw [show (fun k => (if k = i then (1:𝕜) else 0) * (if k = j then 1 else 0))
      = fun _ => (0 : 𝕜) from by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [hij]
    · simp [hk]]
  simp

theorem sum_frameProjG : ∑ i : n, frameProjG 𝕜 i = (1 : HermitianMat n 𝕜) := by
  ext1
  rw [mat_finsetSum]
  simp only [frameProjG_mat]
  rw [show (∑ i : n, Matrix.diagonal (fun j => if j = i then (1:𝕜) else 0))
      = Matrix.diagonal (∑ i : n, fun j => if j = i then (1:𝕜) else 0) from
    (map_sum (Matrix.diagonalAddMonoidHom n 𝕜) _ Finset.univ).symm]
  rw [show (∑ i : n, fun j => if j = i then (1:𝕜) else 0) = fun _ => (1:𝕜) from
    funext fun j => by
      rw [Finset.sum_apply]
      simp [Finset.sum_ite_eq]]
  rw [HermitianMat.mat_one, Matrix.diagonal_one]

/-- The frame decomposition of the family. -/
theorem diagFamilyG_eq_sum_frameProj (r : n → ℝ) :
    diagFamilyG 𝕜 r = ∑ i : n, Real.exp (r i) • frameProjG 𝕜 i := by
  ext1
  rw [mat_finsetSum, diagFamilyG_mat]
  simp only [HermitianMat.mat_smul, frameProjG_mat, ← Matrix.diagonal_smul]
  rw [show (∑ i : n, Matrix.diagonal (Real.exp (r i) • fun k => if k = i then (1:𝕜) else 0))
      = Matrix.diagonal (∑ i : n, Real.exp (r i) • fun k => if k = i then (1:𝕜) else 0) from
    (map_sum (Matrix.diagonalAddMonoidHom n 𝕜) _ Finset.univ).symm]
  congr 1
  funext j
  rw [Finset.sum_apply]
  rw [show (fun i : n => (Real.exp (r i) • fun k => if k = i then (1:𝕜) else 0) j)
      = fun i : n => if j = i then (Real.exp (r i) : 𝕜) else 0 from funext fun i => by
    simp only [Pi.smul_apply]
    by_cases h : j = i <;> simp [h, RCLike.real_smul_eq_coe_mul]]
  rw [Finset.sum_ite_eq]
  simp

/-- The family commutes with every frame projection. -/
theorem diagFamilyG_commute_frameProj (r : n → ℝ) (i : n) :
    Commute (diagFamilyG 𝕜 r).mat (frameProjG 𝕜 i).mat := by
  show _ * _ = _ * _
  rw [diagFamilyG_mat, frameProjG_mat, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  ring

end Necessity
