/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComparisonInstanceGen
import Mathlib.Tactic.Group

set_option linter.style.longLine false

/-!
# χ̃: the diagonal character extended to `ℝⁿ`  (campaign LEDGER 2.6, χ̃ part 2a)

The paper's `χ̃(s − t) := Θ_s Θ_t⁻¹` extension, constructed concretely on
`H_n(𝕜)`:

* `thetaUnitG r` — the comparison map at `a(r)` as a **unit** of the endomorphism
  algebra `H_n(𝕜) →L[ℝ] H_n(𝕜)` (total in `r`: the family is PosDef everywhere;
  the inverse is carried by the `LinearEquiv`, so no operator inversion is
  needed).
* `thetaUnit_mulG` / `thetaUnit_commuteG` — the orthant cocycle and its abelian
  image, at the units level (conditional on the M3 field, as everywhere in this
  lane).
* `thetaUnit_div_eqG` — representative-freedom of `Θ_s Θ_t⁻¹` (the paper's
  well-definedness argument, machine-checked in the units group).
* `chiTildeG r := thetaUnitG (r ⊓ 0) * (thetaUnitG (r ⊓ 0 − r))⁻¹` — the canonical
  representative: both parts lie in the negative orthant for *every* `r`, so no
  case split is ever needed.
* `chiTilde_addG` / `chiTilde_zeroG` / `chiTilde_of_nonposG` — χ̃ is a monoid
  homomorphism `(ℝⁿ, +) → (End H_n(𝕜))ˣ` extending the orthant character.

Part 2b (next): line-continuity of `t ↦ (chiTildeG (t • v)).val` from S2 and the
explicit diagonal form of `Q_{√a(r)}⁻¹`; then `multiParameter_eq_exp` yields the
linear differential `dχ`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
variable (P : SequentialProductOn (HermitianMat n 𝕜))

/-! ## The units-valued comparison map on the diagonal family -/

/-- The comparison map at `a(r)`, packaged as a unit of the endomorphism algebra.
Total in `r` — `a(r)` is positive definite for every `r`, and `thetaNormG` carries
its own inverse as a `LinearEquiv`. -/
def thetaUnitG (hS2 : P.FirstArgContinuous) (r : n → ℝ) :
    (HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜)ˣ where
  val := LinearMap.toContinuousLinearMap (thetaNormG P hS2 (diagFamilyG 𝕜 r)).toLinearMap
  inv := LinearMap.toContinuousLinearMap (thetaNormG P hS2 (diagFamilyG 𝕜 r)).symm.toLinearMap
  val_inv := by
    ext x
    simp [ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap']
  inv_val := by
    ext x
    simp [ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap']

theorem thetaUnit_val_applyG (hS2 : P.FirstArgContinuous) (r : n → ℝ)
    (x : HermitianMat n 𝕜) :
    (thetaUnitG P hS2 r).val x = thetaNormG P hS2 (diagFamilyG 𝕜 r) x := by
  simp [thetaUnitG, LinearMap.coe_toContinuousLinearMap']

/-- `thetaNormG` at the unit base point is the identity (through `theta_base_one`). -/
theorem thetaNorm_base_oneG (hS2 : P.FirstArgContinuous) (x : HermitianMat n 𝕜) :
    thetaNormG P hS2 (1 : HermitianMat n 𝕜) x = x := by
  have h1e : IsEffect (1 : HermitianMat n 𝕜) := isEffect_unit
  have h1bd : (1 : HermitianMat n 𝕜).mat.PosDef := by
    rw [show (1 : HermitianMat n 𝕜) = diagFamilyG 𝕜 0 from diagFamilyG_zero.symm]
    exact diagFamilyG_posDef 0
  rw [thetaNorm_apply_eq_thetaG P hS2 h1e h1bd, theta_base_one P h1e h1bd]
  rfl

theorem thetaUnit_zeroG (hS2 : P.FirstArgContinuous) : thetaUnitG P hS2 0 = 1 := by
  apply Units.ext
  ext x
  rw [thetaUnit_val_applyG, diagFamilyG_zero, thetaNorm_base_oneG]
  simp

/-- The orthant cocycle at the units level. -/
theorem thetaUnit_mulG (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    {r r' : n → ℝ} (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    thetaUnitG P hS2 (r + r') = thetaUnitG P hS2 r * thetaUnitG P hS2 r' := by
  apply Units.ext
  rw [Units.val_mul]
  ext x
  rw [ContinuousLinearMap.mul_apply, thetaUnit_val_applyG, thetaUnit_val_applyG,
    thetaUnit_val_applyG, add_comm r r']
  have hc := thetaNorm_cocycleG P hS2 hjord hr' hr
  rw [hc, LinearEquiv.trans_apply]

/-- The abelian image: the diagonal comparison units commute pairwise. -/
theorem thetaUnit_commuteG (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    {r r' : n → ℝ} (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    Commute (thetaUnitG P hS2 r) (thetaUnitG P hS2 r') := by
  show _ * _ = _ * _
  rw [← thetaUnit_mulG P hS2 hjord hr hr', ← thetaUnit_mulG P hS2 hjord hr' hr, add_comm]

/-- **Representative-freedom of `Θ_s Θ_t⁻¹`** (the paper's well-definedness
argument for the `χ̃` extension, machine-checked in the units group): if
`s + t' = s' + t` (all in the orthant), then `Θ_s Θ_t⁻¹ = Θ_{s'} Θ_{t'}⁻¹`. -/
theorem thetaUnit_div_eqG (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    {s t s' t' : n → ℝ} (hs : ∀ i, s i ≤ 0) (ht : ∀ i, t i ≤ 0)
    (hs' : ∀ i, s' i ≤ 0) (ht' : ∀ i, t' i ≤ 0) (hsum : s + t' = s' + t) :
    thetaUnitG P hS2 s * (thetaUnitG P hS2 t)⁻¹
      = thetaUnitG P hS2 s' * (thetaUnitG P hS2 t')⁻¹ := by
  have hlaw : thetaUnitG P hS2 s * thetaUnitG P hS2 t'
      = thetaUnitG P hS2 s' * thetaUnitG P hS2 t := by
    rw [← thetaUnit_mulG P hS2 hjord hs ht', ← thetaUnit_mulG P hS2 hjord hs' ht, hsum]
  have hcomm : Commute (thetaUnitG P hS2 t) ((thetaUnitG P hS2 t')⁻¹) :=
    (thetaUnit_commuteG P hS2 hjord ht ht').inv_right
  calc thetaUnitG P hS2 s * (thetaUnitG P hS2 t)⁻¹
      = (thetaUnitG P hS2 s * thetaUnitG P hS2 t')
        * ((thetaUnitG P hS2 t')⁻¹ * (thetaUnitG P hS2 t)⁻¹) := by group
    _ = (thetaUnitG P hS2 s' * thetaUnitG P hS2 t)
        * ((thetaUnitG P hS2 t')⁻¹ * (thetaUnitG P hS2 t)⁻¹) := by rw [hlaw]
    _ = thetaUnitG P hS2 s' * ((thetaUnitG P hS2 t * (thetaUnitG P hS2 t')⁻¹)
        * (thetaUnitG P hS2 t)⁻¹) := by group
    _ = thetaUnitG P hS2 s' * (((thetaUnitG P hS2 t')⁻¹ * thetaUnitG P hS2 t)
        * (thetaUnitG P hS2 t)⁻¹) := by rw [hcomm.eq]
    _ = thetaUnitG P hS2 s' * (thetaUnitG P hS2 t')⁻¹ := by group

/-! ## The extension `χ̃` -/

theorem inf_zero_nonposG (r : n → ℝ) : ∀ i, (r ⊓ 0) i ≤ 0 := by
  intro i
  rw [Pi.inf_apply]
  exact inf_le_right

theorem inf_zero_sub_nonposG (r : n → ℝ) : ∀ i, ((r ⊓ 0) - r) i ≤ 0 := by
  intro i
  rw [Pi.sub_apply, Pi.inf_apply]
  exact sub_nonpos.mpr inf_le_left

/-- **The character `χ̃ : ℝⁿ → (End H_n(𝕜))ˣ`**, by the canonical orthant
representative `χ̃(r) := Θ_{r ⊓ 0} Θ_{(r ⊓ 0) − r}⁻¹` — both exponents lie in the
negative orthant for every `r`, so the definition is case-free; on the orthant it
collapses to `Θ_r` (`chiTilde_of_nonposG`). -/
def chiTildeG (hS2 : P.FirstArgContinuous) (r : n → ℝ) :
    (HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜)ˣ :=
  thetaUnitG P hS2 (r ⊓ 0) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹

theorem chiTilde_zeroG (hS2 : P.FirstArgContinuous) : chiTildeG P hS2 0 = 1 := by
  unfold chiTildeG
  rw [show (0 : n → ℝ) ⊓ 0 = 0 from inf_idem 0, sub_zero, thetaUnit_zeroG]
  simp

/-- On the negative orthant, `χ̃` is the comparison unit itself. -/
theorem chiTilde_of_nonposG (hS2 : P.FirstArgContinuous) {r : n → ℝ}
    (hr : ∀ i, r i ≤ 0) : chiTildeG P hS2 r = thetaUnitG P hS2 r := by
  unfold chiTildeG
  have h1 : r ⊓ 0 = r := inf_eq_left.mpr (by intro i; exact hr i)
  rw [h1, sub_self, thetaUnit_zeroG]
  simp

/-- **χ̃ is a homomorphism `(ℝⁿ, +) → (End H_n(𝕜))ˣ`** — the paper's extension of
the orthant cocycle to the whole parameter space, via representative-freedom. -/
theorem chiTilde_addG (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    (r r' : n → ℝ) :
    chiTildeG P hS2 (r + r') = chiTildeG P hS2 r * chiTildeG P hS2 r' := by
  have hB : ∀ i, ((r ⊓ 0) - r) i ≤ 0 := inf_zero_sub_nonposG r
  have hC : ∀ i, (r' ⊓ 0) i ≤ 0 := inf_zero_nonposG r'
  have hD : ∀ i, ((r' ⊓ 0) - r') i ≤ 0 := inf_zero_sub_nonposG r'
  have hS' : ∀ i, ((r ⊓ 0) + (r' ⊓ 0)) i ≤ 0 :=
    fun i => add_nonpos (inf_zero_nonposG r i) (inf_zero_nonposG r' i)
  have hT' : ∀ i, (((r ⊓ 0) - r) + ((r' ⊓ 0) - r')) i ≤ 0 :=
    fun i => add_nonpos (inf_zero_sub_nonposG r i) (inf_zero_sub_nonposG r' i)
  -- collapse the right-hand side to a single `Θ_S Θ_T⁻¹` representative
  have hcollapse : chiTildeG P hS2 r * chiTildeG P hS2 r'
      = thetaUnitG P hS2 ((r ⊓ 0) + (r' ⊓ 0))
        * (thetaUnitG P hS2 (((r ⊓ 0) - r) + ((r' ⊓ 0) - r')))⁻¹ := by
    unfold chiTildeG
    rw [thetaUnit_mulG P hS2 hjord (inf_zero_nonposG r) hC,
      thetaUnit_mulG P hS2 hjord hB hD, mul_inv_rev]
    have hswap1 : (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹ * thetaUnitG P hS2 (r' ⊓ 0)
        = thetaUnitG P hS2 (r' ⊓ 0) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹ :=
      ((thetaUnit_commuteG P hS2 hjord hB hC).inv_left).eq
    have hswap2 : (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹ * (thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹
        = (thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹ * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹ :=
      (((thetaUnit_commuteG P hS2 hjord hB hD).inv_left).inv_right).eq
    calc thetaUnitG P hS2 (r ⊓ 0) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹
          * (thetaUnitG P hS2 (r' ⊓ 0) * (thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹)
        = thetaUnitG P hS2 (r ⊓ 0) * ((thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹
          * thetaUnitG P hS2 (r' ⊓ 0)) * (thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹ := by
          group
      _ = thetaUnitG P hS2 (r ⊓ 0) * (thetaUnitG P hS2 (r' ⊓ 0)
          * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹) * (thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹ := by
          rw [hswap1]
      _ = thetaUnitG P hS2 (r ⊓ 0) * thetaUnitG P hS2 (r' ⊓ 0)
          * ((thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹ * (thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹) := by
          group
      _ = thetaUnitG P hS2 (r ⊓ 0) * thetaUnitG P hS2 (r' ⊓ 0)
          * ((thetaUnitG P hS2 ((r' ⊓ 0) - r'))⁻¹ * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹) := by
          rw [hswap2]
  rw [hcollapse]
  unfold chiTildeG
  -- representative-freedom: `S + T' = S' + T`
  apply thetaUnit_div_eqG P hS2 hjord (inf_zero_nonposG (r + r'))
    (inf_zero_sub_nonposG (r + r')) hS' hT'
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.zero_apply]
  ring

end Necessity
