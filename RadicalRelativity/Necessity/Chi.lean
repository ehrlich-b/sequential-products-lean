/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.DiagonalFamily
import RadicalRelativity.Necessity.ThetaCocycle

set_option linter.style.longLine false

/-!
# The comparison character on the diagonal family  (campaign LEDGER 2.6, χ̃ part 1)

The orthant-level pieces of the character `χ̃ : r ↦ Θ_{a(r)}`:

* `theta_congr` — base-point congruence (the hypothesis slots are proofs).
* `sp_diagFamily` — the unknown product takes the matrix-product value on the
  exponential diagonal family: `a(r) ◦' a(r') = a(r + r')`.
* `thetaD_zero` — `χ̃(0) = 1` (through `theta_base_one`).
* `thetaD_mul` — **the χ̃ cocycle on the negative orthant** (conditional on
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
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- Base-point congruence for Θ. -/
theorem theta_congr {a b : HermitianMat n ℂ} (hab : a = b)
    (ha : IsEffect a) (hbda : a.mat.PosDef) (hb : IsEffect b) (hbdb : b.mat.PosDef) :
    theta P ha hbda = theta P hb hbdb := by
  subst hab
  rfl

/-- **The unknown product on the diagonal family is the family itself**:
`a(r) ◦' a(r') = a(r + r')`. -/
theorem sp_diagFamily (hS2 : P.FirstArgContinuous) {r r' : n → ℝ}
    (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    P.sp (diagFamily r) (diagFamily r') = diagFamily (r + r') := by
  rw [sp_eq_quadRep_of_commute P hS2 (diagFamily_isEffect hr) (diagFamily_posDef r)
    (diagFamily_isEffect hr') (diagFamily_commute r r')]
  ext1
  rw [quadRepEquiv_apply, HermitianMat.conj_apply_mat, ((diagFamily r).cfc Real.sqrt).H]
  have hsq : ((diagFamily r).cfc Real.sqrt).mat * ((diagFamily r).cfc Real.sqrt).mat
      = (diagFamily r).mat := by
    rw [← HermitianMat.mat_cfc_mul_apply]
    have hcongr : (diagFamily r).cfc (fun x => Real.sqrt x * Real.sqrt x)
        = (diagFamily r).cfc (fun x => x) :=
      HermitianMat.cfc_congr_of_nonneg (diagFamily_isEffect hr).1
        fun x hx => Real.mul_self_sqrt hx
    rw [hcongr, HermitianMat.cfc_id']
  have hcomm : Commute (diagFamily r').mat (((diagFamily r).cfc Real.sqrt).mat) :=
    Commute.cfc_right _ (diagFamily_commute r' r)
  calc ((diagFamily r).cfc Real.sqrt).mat * (diagFamily r').mat
        * ((diagFamily r).cfc Real.sqrt).mat
      = (diagFamily r').mat * (((diagFamily r).cfc Real.sqrt).mat
        * ((diagFamily r).cfc Real.sqrt).mat) := by
        rw [← hcomm.eq, Matrix.mul_assoc]
    _ = (diagFamily r').mat * (diagFamily r).mat := by rw [hsq]
    _ = (diagFamily (r + r')).mat := by rw [diagFamily_mul r' r, add_comm r' r]

/-- `χ̃(0) = 1`: Θ at `a(0) = 1` is the identity. -/
theorem thetaD_zero (hr0 : ∀ i, (0 : n → ℝ) i ≤ 0) :
    theta P (diagFamily_isEffect hr0) (diagFamily_posDef 0) = LinearMap.id := by
  have h1e : IsEffect (1 : HermitianMat n ℂ) := isEffect_unit
  have h1bd : (1 : HermitianMat n ℂ).mat.PosDef := by
    rw [show (1 : HermitianMat n ℂ) = diagFamily 0 from diagFamily_zero.symm]
    exact diagFamily_posDef 0
  rw [theta_congr P diagFamily_zero (diagFamily_isEffect hr0) (diagFamily_posDef 0)
    h1e h1bd]
  exact theta_base_one P h1e h1bd

/-- **The χ̃ cocycle on the negative orthant** (vdW 5.7 on the diagonal family;
conditional on Jordan preservation at the left base point, discharged by the M3
`Θ_jordan` field): `Θ_{a(r+r')} = Θ_{a(r)} ∘ Θ_{a(r')}`. -/
theorem thetaD_mul (hS2 : P.FirstArgContinuous) {r r' : n → ℝ}
    (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0)
    (hjord : PreservesJordan (theta P (diagFamily_isEffect hr) (diagFamily_posDef r))) :
    theta P (diagFamily_isEffect (fun i => add_nonpos (hr i) (hr' i)))
        (diagFamily_posDef (r + r'))
      = (theta P (diagFamily_isEffect hr) (diagFamily_posDef r)).comp
        (theta P (diagFamily_isEffect hr') (diagFamily_posDef r')) := by
  apply LinearMap.ext
  intro x
  have h := theta_cocycle_of_preservesJordan P hS2
    (diagFamily_isEffect hr) (diagFamily_isEffect hr')
    (diagFamily_posDef r) (diagFamily_posDef r')
    (diagFamily_commute r r')
    ((sp_diagFamily P hS2 hr hr').symm)
    (diagFamily_isEffect (fun i => add_nonpos (hr i) (hr' i)))
    (diagFamily_posDef (r + r'))
    ((diagFamily_mul r r').symm) hjord x
  simpa using h

end Necessity
