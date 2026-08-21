/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ChiContinuity
import RadicalRelativity.Necessity.CoalescenceInstance

set_option linter.style.longLine false

/-!
# Differentiated coalescence: `dχ(r)` kills coalesced corners  (LEDGER 2.6, u4)

The differential shadow of `lem:coalescence`, in the **strong pointwise form**:
when `r_i = r_j`, the differential `dχ(r)` annihilates every element of the
Peirce-2 corner `J₂(q)`, `q = p_i + p_j`.

Mechanism: both canonical exponents `r ⊓ 0` and `(r ⊓ 0) − r` of
`χ̃(r) = Θ_{r⊓0} Θ_{(r⊓0)−r}⁻¹` inherit the coalescence `r_i = r_j`, so by
`corner_commute` + the fixing theorem both factors (and the inverse) fix each
corner element; hence `χ̃(t•r) x = x` for every `t`, and differentiating
`exp(t • dχ(r)) x ≡ x` at `t = 0` (`hasDerivAt_exp_smul_const` + `clm_apply` +
uniqueness against the constant curve) gives `dχ(r) x = 0`.

This is stronger than the abstract `DiagonalHomSetup.coalescence_diff` field
(`ρ_{ij}(dχ r) = 0`), which follows for *any* block compression `ρ`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace Topology NormedSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## Fixing through `thetaNorm`, `thetaUnit`, and `chiTilde` -/

/-- `thetaNorm` fixes anything matrix-commuting with the base point (the
`Commute`-shaped variant of `thetaNorm_fix`). -/
theorem thetaNorm_fix_of_commute (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) {x : HermitianMat n ℂ} (hc : Commute a.mat x.mat) :
    thetaNorm P hS2 a x = x := by
  rw [thetaNorm_of_posDef P hS2 h, thetaEquiv_apply]
  apply theta_fix_general P hS2 _ _ x
  rw [HermitianMat.mat_smul]
  exact hc.smul_left _

theorem thetaUnit_fix (hS2 : P.FirstArgContinuous) (r : n → ℝ) {x : HermitianMat n ℂ}
    (hc : Commute (diagFamily r).mat x.mat) :
    (thetaUnit P hS2 r).val x = x := by
  rw [thetaUnit_val_apply]
  exact thetaNorm_fix_of_commute P hS2 (diagFamily_posDef r) hc

theorem thetaUnit_inv_fix (hS2 : P.FirstArgContinuous) (r : n → ℝ) {x : HermitianMat n ℂ}
    (hc : Commute (diagFamily r).mat x.mat) :
    ((thetaUnit P hS2 r)⁻¹).val x = x := by
  have hfix : thetaNorm P hS2 (diagFamily r) x = x :=
    thetaNorm_fix_of_commute P hS2 (diagFamily_posDef r) hc
  show LinearMap.toContinuousLinearMap
    (thetaNorm P hS2 (diagFamily r)).symm.toLinearMap x = x
  rw [LinearMap.coe_toContinuousLinearMap']
  calc (thetaNorm P hS2 (diagFamily r)).symm.toLinearMap x
      = (thetaNorm P hS2 (diagFamily r)).symm (thetaNorm P hS2 (diagFamily r) x) := by
        rw [hfix]; rfl
    _ = x := LinearEquiv.symm_apply_apply _ _

/-- **χ̃ fixes coalesced corners**: when `r_i = r_j`, the character fixes every
element of the Peirce-2 corner, for *every* `r` (both canonical exponents
inherit the coalescence). -/
theorem chiTilde_fix_corner (hS2 : P.FirstArgContinuous) {r : n → ℝ} {i j : n}
    (h : r i = r j) {x : HermitianMat n ℂ} (hx : cornerJ2 i j x) :
    (chiTilde P hS2 r).val x = x := by
  have h1 : (r ⊓ 0) i = (r ⊓ 0) j := by
    simp only [Pi.inf_apply, Pi.zero_apply, h]
  have h2 : ((r ⊓ 0) - r) i = ((r ⊓ 0) - r) j := by
    simp only [Pi.sub_apply, Pi.inf_apply, Pi.zero_apply, h]
  have hc1 : Commute (diagFamily (r ⊓ 0)).mat x.mat :=
    corner_commute (diagFamily_scalarOn h1) hx
  have hc2 : Commute (diagFamily ((r ⊓ 0) - r)).mat x.mat :=
    corner_commute (diagFamily_scalarOn h2) hx
  show ((thetaUnit P hS2 (r ⊓ 0)) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val x = x
  rw [Units.val_mul, ContinuousLinearMap.mul_apply,
    thetaUnit_inv_fix P hS2 _ hc2, thetaUnit_fix P hS2 _ hc1]

/-! ## The exp-differentiation kill -/

/-- If `exp(t • A)` fixes `x` for every `t`, then `A x = 0` (differentiate the
constant curve at `t = 0`). -/
theorem exp_apply_const_kill {A : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ}
    {x : HermitianMat n ℂ} (h : ∀ t : ℝ, exp (t • A) x = x) : A x = 0 := by
  have hd : HasDerivAt (fun t : ℝ => exp (t • A) x) (A x) 0 := by
    have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
    have hu : HasDerivAt (fun _ : ℝ => x) 0 (0 : ℝ) := hasDerivAt_const 0 x
    have hcomb := hc.clm_apply hu
    -- At v4.33 neither `rw` nor `simp only` matches the pre-formed `exp (0 • A)` slots in
    -- `hcomb`, so discharge the derivative value as an explicit equation instead.
    have hval : (exp ((0 : ℝ) • A) * A) x + (exp ((0 : ℝ) • A)) 0 = A x := by
      simp [show ((0 : ℝ) • A) = 0 from zero_smul ℝ A]
    exact hval ▸ hcomb
  have hconst : HasDerivAt (fun t : ℝ => exp (t • A) x) 0 0 := by
    rw [show (fun t : ℝ => exp (t • A) x) = fun _ => x from funext h]
    exact hasDerivAt_const 0 x
  exact hd.unique hconst

/-! ## Differentiated coalescence, strong form -/

/-- **`coalescence_diff` (strong pointwise form, machine-checked).** When
`r_i = r_j`, the differential `dχ(r)` annihilates every element of the Peirce-2
corner `J₂(p_i + p_j)`. Any block compression `ρ_{ij}` then satisfies the
abstract `DiagonalHomSetup.coalescence_diff` field. -/
theorem dChi_kills_corner (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {r : n → ℝ} {i j : n} (h : r i = r j) {x : HermitianMat n ℂ}
    (hx : cornerJ2 i j x) :
    dChi P hS2 hjord r x = 0 := by
  apply exp_apply_const_kill
  intro t
  have hexp : exp (t • dChi P hS2 hjord r) = ((chiTilde P hS2 (t • r)).val) := by
    rw [← map_smul (dChi P hS2 hjord) t r]
    exact (chiTilde_eq_exp_dChi P hS2 hjord (t • r)).symm
  rw [hexp]
  exact chiTilde_fix_corner P hS2
    (by simp only [Pi.smul_apply, smul_eq_mul, h]) hx

end Necessity
