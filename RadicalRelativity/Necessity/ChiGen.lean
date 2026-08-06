/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.DiagonalFamilyGen
import RadicalRelativity.Necessity.ThetaCocycle

set_option linter.style.longLine false

/-!
# The comparison character on the diagonal family, over any `RCLike` field

Field-general twin of `Necessity/Chi.lean` (M4.1). Declarations carry a `G`
suffix and consume the scalar-explicit frame/family layer
(`Necessity/DiagonalFamilyGen.lean`).

It is a *twin* rather than a generalization-in-place because these statements
mention the family CONSTANT `diagFamilyG 𝕜 r`, so generalizing `Chi.lean` itself
would force rewriting every ℂ-lane use of `diagFamily` (234 sites across 19
files, including the finished complex capstones). The complex row is the
submission artifact; it is deliberately left untouched, and the duplication here
can be collapsed later once the real row is closed.

The orthant-level pieces of the character `χ̃ : r ↦ Θ_{a(r)}`:

* `theta_congrG` — base-point congruence (the hypothesis slots are proofs).
* `sp_diagFamilyG` — the unknown product takes the matrix-product value on the
  exponential diagonal family: `a(r) ◦' a(r') = a(r + r')`.
* `thetaD_zeroG` — `χ̃(0) = 1` (through `theta_base_one`).
* `thetaD_mulG` — **the χ̃ cocycle on the negative orthant** (conditional on
  Jordan preservation, i.e. on the M3 `Θ_jordan` field):
  `Θ_{a(r+r')} = Θ_{a(r)} ∘ Θ_{a(r')}`.

Part 2 (next unit) extends χ̃ to all of `ℝⁿ`, proves line-continuity from S2,
and applies `multiParameter_eq_exp` to obtain the linear differential `dχ`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
variable (P : SequentialProductOn (HermitianMat n 𝕜))

/-- Base-point congruence for Θ. -/
theorem theta_congrG {a b : HermitianMat n 𝕜} (hab : a = b)
    (ha : IsEffect a) (hbda : a.mat.PosDef) (hb : IsEffect b) (hbdb : b.mat.PosDef) :
    theta P ha hbda = theta P hb hbdb := by
  subst hab
  rfl

/-- **The unknown product on the diagonal family is the family itself**:
`a(r) ◦' a(r') = a(r + r')`. -/
theorem sp_diagFamilyG (hS2 : P.FirstArgContinuous) {r r' : n → ℝ}
    (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    P.sp (diagFamilyG 𝕜 r) (diagFamilyG 𝕜 r') = diagFamilyG 𝕜 (r + r') := by
  rw [sp_eq_quadRep_of_commute P hS2 (diagFamilyG_isEffect hr) (diagFamilyG_posDef r)
    (diagFamilyG_isEffect hr') (diagFamilyG_commute r r')]
  ext1
  rw [quadRepEquiv_apply, HermitianMat.conj_apply_mat, ((diagFamilyG 𝕜 r).cfc Real.sqrt).H]
  have hsq : ((diagFamilyG 𝕜 r).cfc Real.sqrt).mat * ((diagFamilyG 𝕜 r).cfc Real.sqrt).mat
      = (diagFamilyG 𝕜 r).mat := by
    rw [← HermitianMat.mat_cfc_mul_apply]
    have hcongr : (diagFamilyG 𝕜 r).cfc (fun x => Real.sqrt x * Real.sqrt x)
        = (diagFamilyG 𝕜 r).cfc (fun x => x) :=
      HermitianMat.cfc_congr_of_nonneg (diagFamilyG_isEffect hr).1
        fun x hx => Real.mul_self_sqrt hx
    rw [hcongr, HermitianMat.cfc_id']
  have hcomm : Commute (diagFamilyG 𝕜 r').mat (((diagFamilyG 𝕜 r).cfc Real.sqrt).mat) :=
    Commute.cfc_right _ (diagFamilyG_commute r' r)
  calc ((diagFamilyG 𝕜 r).cfc Real.sqrt).mat * (diagFamilyG 𝕜 r').mat
        * ((diagFamilyG 𝕜 r).cfc Real.sqrt).mat
      = (diagFamilyG 𝕜 r').mat * (((diagFamilyG 𝕜 r).cfc Real.sqrt).mat
        * ((diagFamilyG 𝕜 r).cfc Real.sqrt).mat) := by
        rw [← hcomm.eq, Matrix.mul_assoc]
    _ = (diagFamilyG 𝕜 r').mat * (diagFamilyG 𝕜 r).mat := by rw [hsq]
    _ = (diagFamilyG 𝕜 (r + r')).mat := by rw [diagFamilyG_mul r' r, add_comm r' r]

/-- `χ̃(0) = 1`: Θ at `a(0) = 1` is the identity. -/
theorem thetaD_zeroG (hr0 : ∀ i, (0 : n → ℝ) i ≤ 0) :
    theta P (diagFamilyG_isEffect hr0) (diagFamilyG_posDef 0) = LinearMap.id := by
  have h1e : IsEffect (1 : HermitianMat n 𝕜) := isEffect_unit
  have h1bd : (1 : HermitianMat n 𝕜).mat.PosDef := by
    rw [show (1 : HermitianMat n 𝕜) = diagFamilyG 𝕜 0 from diagFamilyG_zero.symm]
    exact diagFamilyG_posDef 0
  rw [theta_congrG P diagFamilyG_zero (diagFamilyG_isEffect hr0) (diagFamilyG_posDef 0)
    h1e h1bd]
  exact theta_base_one P h1e h1bd

/-- **The χ̃ cocycle on the negative orthant** (vdW 5.7 on the diagonal family;
conditional on Jordan preservation at the left base point, discharged by the M3
`Θ_jordan` field): `Θ_{a(r+r')} = Θ_{a(r)} ∘ Θ_{a(r')}`. -/
theorem thetaD_mulG (hS2 : P.FirstArgContinuous) {r r' : n → ℝ}
    (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0)
    (hjord : PreservesJordan (theta P (diagFamilyG_isEffect hr) (diagFamilyG_posDef r))) :
    theta P (diagFamilyG_isEffect (fun i => add_nonpos (hr i) (hr' i)))
        (diagFamilyG_posDef (r + r'))
      = (theta P (diagFamilyG_isEffect hr) (diagFamilyG_posDef r)).comp
        (theta P (diagFamilyG_isEffect hr') (diagFamilyG_posDef r')) := by
  apply LinearMap.ext
  intro x
  have h := theta_cocycle_of_preservesJordan P hS2
    (diagFamilyG_isEffect hr) (diagFamilyG_isEffect hr')
    (diagFamilyG_posDef r) (diagFamilyG_posDef r')
    (diagFamilyG_commute r r')
    ((sp_diagFamilyG P hS2 hr hr').symm)
    (diagFamilyG_isEffect (fun i => add_nonpos (hr i) (hr' i)))
    (diagFamilyG_posDef (r + r'))
    ((diagFamilyG_mul r r').symm) hjord x
  simpa using h

end Necessity
