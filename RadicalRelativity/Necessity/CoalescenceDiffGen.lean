/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ChiContinuityGen
import RadicalRelativity.Necessity.CoalescenceInstanceGen

set_option linter.style.longLine false

/-!
# Differentiated coalescence: `dχ(r)` kills coalesced corners  (LEDGER 2.6, u4)

The differential shadow of `lem:coalescence`, in the **strong pointwise form**:
when `r_i = r_j`, the differential `dχ(r)` annihilates every element of the
Peirce-2 corner `J₂(q)`, `q = p_i + p_j`.

Mechanism: both canonical exponents `r ⊓ 0` and `(r ⊓ 0) − r` of
`χ̃(r) = Θ_{r⊓0} Θ_{(r⊓0)−r}⁻¹` inherit the coalescence `r_i = r_j`, so by
`corner_commuteG` + the fixing theorem both factors (and the inverse) fix each
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
variable {𝕜 : Type*} [RCLike 𝕜]
variable (P : SequentialProductOn (HermitianMat n 𝕜))

/-! ## Fixing through `thetaNormG`, `thetaUnitG`, and `chiTildeG` -/

/-- `thetaNormG` fixes anything matrix-commuting with the base point (the
`Commute`-shaped variant of `thetaNorm_fixG`). -/
theorem thetaNorm_fix_of_commuteG (hS2 : P.FirstArgContinuous) {a : HermitianMat n 𝕜}
    (h : a.mat.PosDef) {x : HermitianMat n 𝕜} (hc : Commute a.mat x.mat) :
    thetaNormG P hS2 a x = x := by
  rw [thetaNorm_of_posDefG P hS2 h, thetaEquiv_apply]
  apply theta_fix_generalG P hS2 _ _ x
  rw [HermitianMat.mat_smul]
  exact hc.smul_left _

theorem thetaUnit_fixG (hS2 : P.FirstArgContinuous) (r : n → ℝ) {x : HermitianMat n 𝕜}
    (hc : Commute (diagFamilyG 𝕜 r).mat x.mat) :
    (thetaUnitG P hS2 r).val x = x := by
  rw [thetaUnit_val_applyG]
  exact thetaNorm_fix_of_commuteG P hS2 (diagFamilyG_posDef r) hc

theorem thetaUnit_inv_fixG (hS2 : P.FirstArgContinuous) (r : n → ℝ) {x : HermitianMat n 𝕜}
    (hc : Commute (diagFamilyG 𝕜 r).mat x.mat) :
    ((thetaUnitG P hS2 r)⁻¹).val x = x := by
  have hfix : thetaNormG P hS2 (diagFamilyG 𝕜 r) x = x :=
    thetaNorm_fix_of_commuteG P hS2 (diagFamilyG_posDef r) hc
  show LinearMap.toContinuousLinearMap
    (thetaNormG P hS2 (diagFamilyG 𝕜 r)).symm.toLinearMap x = x
  rw [LinearMap.coe_toContinuousLinearMap']
  calc (thetaNormG P hS2 (diagFamilyG 𝕜 r)).symm.toLinearMap x
      = (thetaNormG P hS2 (diagFamilyG 𝕜 r)).symm (thetaNormG P hS2 (diagFamilyG 𝕜 r) x) := by
        rw [hfix]; rfl
    _ = x := LinearEquiv.symm_apply_apply _ _

/-- **χ̃ fixes coalesced corners**: when `r_i = r_j`, the character fixes every
element of the Peirce-2 corner, for *every* `r` (both canonical exponents
inherit the coalescence). -/
theorem chiTilde_fix_cornerG (hS2 : P.FirstArgContinuous) {r : n → ℝ} {i j : n}
    (h : r i = r j) {x : HermitianMat n 𝕜} (hx : cornerJ2G i j x) :
    (chiTildeG P hS2 r).val x = x := by
  have h1 : (r ⊓ 0) i = (r ⊓ 0) j := by
    simp only [Pi.inf_apply, Pi.zero_apply, h]
  have h2 : ((r ⊓ 0) - r) i = ((r ⊓ 0) - r) j := by
    simp only [Pi.sub_apply, Pi.inf_apply, Pi.zero_apply, h]
  have hc1 : Commute (diagFamilyG 𝕜 (r ⊓ 0)).mat x.mat :=
    corner_commuteG (diagFamilyG_scalarOn h1) hx
  have hc2 : Commute (diagFamilyG 𝕜 ((r ⊓ 0) - r)).mat x.mat :=
    corner_commuteG (diagFamilyG_scalarOn h2) hx
  show ((thetaUnitG P hS2 (r ⊓ 0)) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val x = x
  rw [Units.val_mul, ContinuousLinearMap.mul_apply,
    thetaUnit_inv_fixG P hS2 _ hc2, thetaUnit_fixG P hS2 _ hc1]

/-! ## The exp-differentiation kill -/

/-- If `exp(t • A)` fixes `x` for every `t`, then `A x = 0` (differentiate the
constant curve at `t = 0`). -/
theorem exp_apply_const_killG {A : HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜}
    {x : HermitianMat n 𝕜} (h : ∀ t : ℝ, exp (t • A) x = x) : A x = 0 := by
  have hd : HasDerivAt (fun t : ℝ => exp (t • A) x) (A x) 0 := by
    have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
    have hu : HasDerivAt (fun _ : ℝ => x) 0 (0 : ℝ) := hasDerivAt_const 0 x
    have hcomb := hc.clm_apply hu
    have h0 : exp ((0 : ℝ) • A) = (1 : HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜) := by
      rw [show (0 : ℝ) • A = 0 from zero_smul ℝ A]
      exact exp_zero
    rw [h0] at hcomb
    simpa using hcomb
  have hconst : HasDerivAt (fun t : ℝ => exp (t • A) x) 0 0 := by
    rw [show (fun t : ℝ => exp (t • A) x) = fun _ => x from funext h]
    exact hasDerivAt_const 0 x
  exact hd.unique hconst

/-! ## Differentiated coalescence, strong form -/

/-- **`coalescence_diff` (strong pointwise form, machine-checked).** When
`r_i = r_j`, the differential `dχ(r)` annihilates every element of the Peirce-2
corner `J₂(p_i + p_j)`. Any block compression `ρ_{ij}` then satisfies the
abstract `DiagonalHomSetup.coalescence_diff` field. -/
theorem dChi_kills_cornerG (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    {r : n → ℝ} {i j : n} (h : r i = r j) {x : HermitianMat n 𝕜}
    (hx : cornerJ2G i j x) :
    dChiG P hS2 hjord r x = 0 := by
  apply exp_apply_const_killG
  intro t
  have hexp : exp (t • dChiG P hS2 hjord r) = ((chiTildeG P hS2 (t • r)).val) := by
    rw [← map_smul (dChiG P hS2 hjord) t r]
    exact (chiTilde_eq_exp_dChiG P hS2 hjord (t • r)).symm
  rw [hexp]
  exact chiTilde_fix_cornerG P hS2
    (by simp only [Pi.smul_apply, smul_eq_mul, h]) hx

end Necessity
