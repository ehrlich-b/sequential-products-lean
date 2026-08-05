/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComparisonInstance
import Mathlib.Tactic.Group

set_option linter.style.longLine false

/-!
# χ̃: the diagonal character extended to `ℝⁿ`  (campaign LEDGER 2.6, χ̃ part 2a)

The paper's `χ̃(s − t) := Θ_s Θ_t⁻¹` extension, constructed concretely on
`H_n(ℂ)`:

* `thetaUnit r` — the comparison map at `a(r)` as a **unit** of the endomorphism
  algebra `H_n(ℂ) →L[ℝ] H_n(ℂ)` (total in `r`: the family is PosDef everywhere;
  the inverse is carried by the `LinearEquiv`, so no operator inversion is
  needed).
* `thetaUnit_mul` / `thetaUnit_commute` — the orthant cocycle and its abelian
  image, at the units level (conditional on the M3 field, as everywhere in this
  lane).
* `thetaUnit_div_eq` — representative-freedom of `Θ_s Θ_t⁻¹` (the paper's
  well-definedness argument, machine-checked in the units group).
* `chiTilde r := thetaUnit (r ⊓ 0) * (thetaUnit (r ⊓ 0 − r))⁻¹` — the canonical
  representative: both parts lie in the negative orthant for *every* `r`, so no
  case split is ever needed.
* `chiTilde_add` / `chiTilde_zero` / `chiTilde_of_nonpos` — χ̃ is a monoid
  homomorphism `(ℝⁿ, +) → (End H_n(ℂ))ˣ` extending the orthant character.

Part 2b (next): line-continuity of `t ↦ (chiTilde (t • v)).val` from S2 and the
explicit diagonal form of `Q_{√a(r)}⁻¹`; then `multiParameter_eq_exp` yields the
linear differential `dχ`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The units-valued comparison map on the diagonal family -/

/-- The comparison map at `a(r)`, packaged as a unit of the endomorphism algebra.
Total in `r` — `a(r)` is positive definite for every `r`, and `thetaNorm` carries
its own inverse as a `LinearEquiv`. -/
def thetaUnit (hS2 : P.FirstArgContinuous) (r : n → ℝ) :
    (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ where
  val := LinearMap.toContinuousLinearMap (thetaNorm P hS2 (diagFamily r)).toLinearMap
  inv := LinearMap.toContinuousLinearMap (thetaNorm P hS2 (diagFamily r)).symm.toLinearMap
  val_inv := by
    ext x
    simp [ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap']
  inv_val := by
    ext x
    simp [ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap']

theorem thetaUnit_val_apply (hS2 : P.FirstArgContinuous) (r : n → ℝ)
    (x : HermitianMat n ℂ) :
    (thetaUnit P hS2 r).val x = thetaNorm P hS2 (diagFamily r) x := by
  simp [thetaUnit, LinearMap.coe_toContinuousLinearMap']

/-- `thetaNorm` at the unit base point is the identity (through `theta_base_one`). -/
theorem thetaNorm_base_one (hS2 : P.FirstArgContinuous) (x : HermitianMat n ℂ) :
    thetaNorm P hS2 (1 : HermitianMat n ℂ) x = x := by
  have h1e : IsEffect (1 : HermitianMat n ℂ) := isEffect_unit
  have h1bd : (1 : HermitianMat n ℂ).mat.PosDef := by
    rw [show (1 : HermitianMat n ℂ) = diagFamily 0 from diagFamily_zero.symm]
    exact diagFamily_posDef 0
  rw [thetaNorm_apply_eq_theta P hS2 h1e h1bd, theta_base_one P h1e h1bd]
  rfl

theorem thetaUnit_zero (hS2 : P.FirstArgContinuous) : thetaUnit P hS2 0 = 1 := by
  apply Units.ext
  ext x
  rw [thetaUnit_val_apply, diagFamily_zero, thetaNorm_base_one]
  simp

/-- The orthant cocycle at the units level. -/
theorem thetaUnit_mul (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {r r' : n → ℝ} (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    thetaUnit P hS2 (r + r') = thetaUnit P hS2 r * thetaUnit P hS2 r' := by
  apply Units.ext
  rw [Units.val_mul]
  ext x
  rw [ContinuousLinearMap.mul_apply, thetaUnit_val_apply, thetaUnit_val_apply,
    thetaUnit_val_apply, add_comm r r']
  have hc := thetaNorm_cocycle P hS2 hjord hr' hr
  rw [hc, LinearEquiv.trans_apply]

/-- The abelian image: the diagonal comparison units commute pairwise. -/
theorem thetaUnit_commute (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {r r' : n → ℝ} (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    Commute (thetaUnit P hS2 r) (thetaUnit P hS2 r') := by
  show _ * _ = _ * _
  rw [← thetaUnit_mul P hS2 hjord hr hr', ← thetaUnit_mul P hS2 hjord hr' hr, add_comm]

/-- **Representative-freedom of `Θ_s Θ_t⁻¹`** (the paper's well-definedness
argument for the `χ̃` extension, machine-checked in the units group): if
`s + t' = s' + t` (all in the orthant), then `Θ_s Θ_t⁻¹ = Θ_{s'} Θ_{t'}⁻¹`. -/
theorem thetaUnit_div_eq (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {s t s' t' : n → ℝ} (hs : ∀ i, s i ≤ 0) (ht : ∀ i, t i ≤ 0)
    (hs' : ∀ i, s' i ≤ 0) (ht' : ∀ i, t' i ≤ 0) (hsum : s + t' = s' + t) :
    thetaUnit P hS2 s * (thetaUnit P hS2 t)⁻¹
      = thetaUnit P hS2 s' * (thetaUnit P hS2 t')⁻¹ := by
  have hlaw : thetaUnit P hS2 s * thetaUnit P hS2 t'
      = thetaUnit P hS2 s' * thetaUnit P hS2 t := by
    rw [← thetaUnit_mul P hS2 hjord hs ht', ← thetaUnit_mul P hS2 hjord hs' ht, hsum]
  have hcomm : Commute (thetaUnit P hS2 t) ((thetaUnit P hS2 t')⁻¹) :=
    (thetaUnit_commute P hS2 hjord ht ht').inv_right
  calc thetaUnit P hS2 s * (thetaUnit P hS2 t)⁻¹
      = (thetaUnit P hS2 s * thetaUnit P hS2 t')
        * ((thetaUnit P hS2 t')⁻¹ * (thetaUnit P hS2 t)⁻¹) := by group
    _ = (thetaUnit P hS2 s' * thetaUnit P hS2 t)
        * ((thetaUnit P hS2 t')⁻¹ * (thetaUnit P hS2 t)⁻¹) := by rw [hlaw]
    _ = thetaUnit P hS2 s' * ((thetaUnit P hS2 t * (thetaUnit P hS2 t')⁻¹)
        * (thetaUnit P hS2 t)⁻¹) := by group
    _ = thetaUnit P hS2 s' * (((thetaUnit P hS2 t')⁻¹ * thetaUnit P hS2 t)
        * (thetaUnit P hS2 t)⁻¹) := by rw [hcomm.eq]
    _ = thetaUnit P hS2 s' * (thetaUnit P hS2 t')⁻¹ := by group

/-! ## The extension `χ̃` -/

theorem inf_zero_nonpos (r : n → ℝ) : ∀ i, (r ⊓ 0) i ≤ 0 := by
  intro i
  rw [Pi.inf_apply]
  exact inf_le_right

theorem inf_zero_sub_nonpos (r : n → ℝ) : ∀ i, ((r ⊓ 0) - r) i ≤ 0 := by
  intro i
  rw [Pi.sub_apply, Pi.inf_apply]
  exact sub_nonpos.mpr inf_le_left

/-- **The character `χ̃ : ℝⁿ → (End H_n(ℂ))ˣ`**, by the canonical orthant
representative `χ̃(r) := Θ_{r ⊓ 0} Θ_{(r ⊓ 0) − r}⁻¹` — both exponents lie in the
negative orthant for every `r`, so the definition is case-free; on the orthant it
collapses to `Θ_r` (`chiTilde_of_nonpos`). -/
def chiTilde (hS2 : P.FirstArgContinuous) (r : n → ℝ) :
    (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ :=
  thetaUnit P hS2 (r ⊓ 0) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹

theorem chiTilde_zero (hS2 : P.FirstArgContinuous) : chiTilde P hS2 0 = 1 := by
  unfold chiTilde
  rw [show (0 : n → ℝ) ⊓ 0 = 0 from inf_idem 0, sub_zero, thetaUnit_zero]
  simp

/-- On the negative orthant, `χ̃` is the comparison unit itself. -/
theorem chiTilde_of_nonpos (hS2 : P.FirstArgContinuous) {r : n → ℝ}
    (hr : ∀ i, r i ≤ 0) : chiTilde P hS2 r = thetaUnit P hS2 r := by
  unfold chiTilde
  have h1 : r ⊓ 0 = r := inf_eq_left.mpr (by intro i; exact hr i)
  rw [h1, sub_self, thetaUnit_zero]
  simp

/-- **χ̃ is a homomorphism `(ℝⁿ, +) → (End H_n(ℂ))ˣ`** — the paper's extension of
the orthant cocycle to the whole parameter space, via representative-freedom. -/
theorem chiTilde_add (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r r' : n → ℝ) :
    chiTilde P hS2 (r + r') = chiTilde P hS2 r * chiTilde P hS2 r' := by
  have hB : ∀ i, ((r ⊓ 0) - r) i ≤ 0 := inf_zero_sub_nonpos r
  have hC : ∀ i, (r' ⊓ 0) i ≤ 0 := inf_zero_nonpos r'
  have hD : ∀ i, ((r' ⊓ 0) - r') i ≤ 0 := inf_zero_sub_nonpos r'
  have hS' : ∀ i, ((r ⊓ 0) + (r' ⊓ 0)) i ≤ 0 :=
    fun i => add_nonpos (inf_zero_nonpos r i) (inf_zero_nonpos r' i)
  have hT' : ∀ i, (((r ⊓ 0) - r) + ((r' ⊓ 0) - r')) i ≤ 0 :=
    fun i => add_nonpos (inf_zero_sub_nonpos r i) (inf_zero_sub_nonpos r' i)
  -- collapse the right-hand side to a single `Θ_S Θ_T⁻¹` representative
  have hcollapse : chiTilde P hS2 r * chiTilde P hS2 r'
      = thetaUnit P hS2 ((r ⊓ 0) + (r' ⊓ 0))
        * (thetaUnit P hS2 (((r ⊓ 0) - r) + ((r' ⊓ 0) - r')))⁻¹ := by
    unfold chiTilde
    rw [thetaUnit_mul P hS2 hjord (inf_zero_nonpos r) hC,
      thetaUnit_mul P hS2 hjord hB hD, mul_inv_rev]
    have hswap1 : (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹ * thetaUnit P hS2 (r' ⊓ 0)
        = thetaUnit P hS2 (r' ⊓ 0) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹ :=
      ((thetaUnit_commute P hS2 hjord hB hC).inv_left).eq
    have hswap2 : (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹ * (thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹
        = (thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹ * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹ :=
      (((thetaUnit_commute P hS2 hjord hB hD).inv_left).inv_right).eq
    calc thetaUnit P hS2 (r ⊓ 0) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹
          * (thetaUnit P hS2 (r' ⊓ 0) * (thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹)
        = thetaUnit P hS2 (r ⊓ 0) * ((thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹
          * thetaUnit P hS2 (r' ⊓ 0)) * (thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹ := by
          group
      _ = thetaUnit P hS2 (r ⊓ 0) * (thetaUnit P hS2 (r' ⊓ 0)
          * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹) * (thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹ := by
          rw [hswap1]
      _ = thetaUnit P hS2 (r ⊓ 0) * thetaUnit P hS2 (r' ⊓ 0)
          * ((thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹ * (thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹) := by
          group
      _ = thetaUnit P hS2 (r ⊓ 0) * thetaUnit P hS2 (r' ⊓ 0)
          * ((thetaUnit P hS2 ((r' ⊓ 0) - r'))⁻¹ * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹) := by
          rw [hswap2]
  rw [hcollapse]
  unfold chiTilde
  -- representative-freedom: `S + T' = S' + T`
  apply thetaUnit_div_eq P hS2 hjord (inf_zero_nonpos (r + r'))
    (inf_zero_sub_nonpos (r + r')) hS' hT'
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.inf_apply, Pi.zero_apply]
  ring

end Necessity
