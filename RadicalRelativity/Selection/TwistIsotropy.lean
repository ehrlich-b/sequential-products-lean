/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SpinFactor
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option linter.style.longLine false

open scoped InnerProductSpace

/-!
# Twist geometry on the rank-two block cone (`prop:boost`, `prop:isotropy`)

This file formalizes the two twist-geometry propositions of the twist-normal-form
paper's `sec:sp-twist` / `\S`~`sec:twist-geometry` (the audited standalone
extraction; a companion manuscript in preparation carries the same statements):

* **`prop:boost` (Boost criterion).**  On a rank-two Peirce block, the cone is the
  spin-factor ("ice-cream") cone `α, β ≥ 0 ∧ ‖w‖² ≤ αβ` in coordinates
  `α p + β q + w`, `w ∈ W = V₁(p,q)`.  The *boost* is
  `H(s) : (α, β, w) ↦ (e^{s/2}α, e^{-s/2}β, φ w)` (with `φ = e^{sT}` in the
  manuscript).  Its diagonal part preserves the cone quantity `αβ` exactly, since
  `(e^{s/2}α)(e^{-s/2}β) = αβ`; consequently the boost preserves the block cone for
  every effect iff its `W`-action is a contraction, `‖φ w‖ ≤ ‖w‖`.

* **`prop:isotropy` (Twist isotropy).**  Once all seven sequential axioms hold the
  block is a Euclidean Jordan algebra with its trace inner product; cone-preservation
  for all `s` (both signs) forces each `e^{sT}` to be an isometry of `W`, and an
  isometric one-parameter flow with generator `T` has `T` skew-adjoint,
  `T ∈ 𝔰𝔬(W)`.  This is the residual "twist" freedom: the local twist group is
  `SO(W)`.

## Main results

* `Selection.TwistIsotropy.boost_diag_prod` — the diagonal boost preserves `αβ`
  (`(e^{s/2}α)(e^{-s/2}β) = αβ`); the algebraic core of `prop:boost`.
* `Selection.TwistIsotropy.boost_preserves_blockCone_iff` — the **boost criterion**:
  `H(s)` preserves the block cone on all cone points iff its `W`-action `φ` is a
  contraction (`prop:boost`).
* `Selection.TwistIsotropy.isometry_of_contraction_group` — a contraction that is a
  one-parameter group (both signs) is an isometry: the "both signs" upgrade in the
  proof of `prop:isotropy`.
* `Selection.TwistIsotropy.isSkewAdjoint_iff_inner_self` — polarization: a real
  linear map is skew-adjoint iff `⟪T w, w⟫ = 0` for all `w`, i.e. `T ∈ 𝔰𝔬(W)`.
* `Selection.TwistIsotropy.inner_generator_self_zero` — the generator of an isometric
  one-parameter flow satisfies `⟪T w, w⟫ = 0`.
* `Selection.TwistIsotropy.twist_isotropy` — the **capstone** (`prop:isotropy`):
  a block whose boost preserves the cone at every `s` (a one-parameter group with
  generator `T`) has `T` skew-adjoint, `T ∈ 𝔰𝔬(W)`.
* `Selection.TwistIsotropy.spinFactor_isNonneg_iff_blockCone` — reuse of
  `SpinFactor`'s cone: the concrete `M₂(ℝ)ˢᵃ` cone is the abstract block cone at
  `W = ℝ` (the `d = 1` "real" row of `prop:type-table`, twist group trivial).
* `Selection.TwistIsotropy.exp_skew_isometry` — a skew-adjoint generator's operator
  exponential is an isometry, `‖exp(s • T) w‖ = ‖w‖`.
* `Selection.TwistIsotropy.blockCone_preserved_of_skew` — the **converse** of
  `prop:isotropy` at the block level: every `T ∈ 𝔰𝔬(W)` yields, via `exp(s • T)`, a
  boost that preserves the block cone at every `s`.  With `twist_isotropy` and
  `boost_preserves_blockCone_iff` this closes the equivalence *cone-preserving
  one-parameter groups ↔ `𝔰𝔬(W)` generators* — the manuscript's "the local twist group
  is exactly `SO(W)`" (Paper A Prop 5.2).

## Faithfulness notes

The block cone is stated in the manuscript's `α, β, w` coordinates (matching
`prop:isotropy`'s displayed cone `‖w‖² ≤ αβ`) over an abstract real inner product
space `W`, which is what the propositions quantify over; the concrete `SpinFactor`
of `SpinFactor.lean` is imported and recovered as the `W = ℝ` instance.  The forward
direction (`twist_isotropy`) keeps the flow `φ` **abstract** (`φ : ℝ → W → W` with the
group law, `φ 0 = id`, and derivative `T` at `0`), capturing exactly the content the
manuscript proof uses; the converse (`blockCone_preserved_of_skew`) realizes the flow
concretely as the operator exponential `exp(s • T)` and proves the missing
`skew-adjoint ⟹ e^{sT} isometric` step (`exp_skew_isometry`), so the block-level
equivalence is now complete.  The converse takes `W` complete (the finite-dimensional
case), so that the exponential converges.  Zero `sorry`, zero custom axioms.
-/

namespace Selection.TwistIsotropy

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-! ## The rank-two block cone and the boost -/

/-- The rank-two Peirce block cone in `α p + β q + w` coordinates
(`v = (α, β, w) : ℝ × ℝ × W`): the spin-factor cone
`α ≥ 0 ∧ β ≥ 0 ∧ ‖w‖² ≤ αβ`.  Matches the displayed cone of
`prop:isotropy`. -/
def BlockCone (v : ℝ × ℝ × W) : Prop :=
  0 ≤ v.1 ∧ 0 ≤ v.2.1 ∧ ‖v.2.2‖ ^ 2 ≤ v.1 * v.2.1

/-- The **boost** `H(s)` of the twist-geometry section, with an abstract `W`-action
`φ` (the manuscript's `e^{sT}` on the Peirce `1`-space):
`(α, β, w) ↦ (e^{s/2}α, e^{-s/2}β, φ w)`. -/
noncomputable def boost (φ : W → W) (s : ℝ) (v : ℝ × ℝ × W) : ℝ × ℝ × W :=
  (Real.exp (s / 2) * v.1, Real.exp (-(s / 2)) * v.2.1, φ v.2.2)

/-- The diagonal part of the boost preserves the cone quantity `αβ` exactly:
`(e^{s/2}α)(e^{-s/2}β) = αβ`.  This is the algebraic heart of the boost criterion
(`prop:boost`), the step "`(e^{s/2}α)(e^{-s/2}β) = αβ`: the diagonal part preserves
the product `αβ`". -/
theorem boost_diag_prod (s α β : ℝ) :
    Real.exp (s / 2) * α * (Real.exp (-(s / 2)) * β) = α * β := by
  have h : Real.exp (s / 2) * Real.exp (-(s / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (α * β) * h

/-! ## The boost criterion (`prop:boost`) -/

omit [InnerProductSpace ℝ W] in
/-- **Boost criterion (`prop:boost`).**  The boost `H(s)` maps the block cone into
itself on *every* cone point iff its `W`-action `φ` is a contraction,
`‖φ w‖ ≤ ‖w‖`.  The forward direction extracts the contraction by testing on the
extremal cone point `(‖w‖, ‖w‖, w)`; the reverse uses that the diagonal preserves
`αβ` (`boost_diag_prod`). -/
theorem boost_preserves_blockCone_iff (φ : W → W) (s : ℝ) :
    (∀ v : ℝ × ℝ × W, BlockCone v → BlockCone (boost φ s v)) ↔ ∀ w, ‖φ w‖ ≤ ‖w‖ := by
  constructor
  · intro hpres w
    have hv : BlockCone ((‖w‖, ‖w‖, w) : ℝ × ℝ × W) :=
      ⟨norm_nonneg w, norm_nonneg w, (pow_two ‖w‖).le⟩
    have hb := hpres _ hv
    simp only [boost, BlockCone] at hb
    obtain ⟨_, _, h3⟩ := hb
    rw [boost_diag_prod, ← pow_two] at h3
    calc ‖φ w‖ = Real.sqrt (‖φ w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt h3
      _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)
  · intro hcontract v hv
    obtain ⟨hα, hβ, hw⟩ := hv
    simp only [boost, BlockCone]
    refine ⟨mul_nonneg (Real.exp_pos _).le hα, mul_nonneg (Real.exp_pos _).le hβ, ?_⟩
    rw [boost_diag_prod]
    calc ‖φ v.2.2‖ ^ 2 ≤ ‖v.2.2‖ ^ 2 := by
            nlinarith [hcontract v.2.2, norm_nonneg (φ v.2.2), norm_nonneg v.2.2]
      _ ≤ v.1 * v.2.1 := hw

omit [InnerProductSpace ℝ W] in
/-- Reverse-direction convenience: an *isometric* `W`-flow makes every boost
cone-preserving.  The remaining step of the manuscript converse,
`T ∈ 𝔰𝔬(W) ⟹ e^{sT}` isometric, is discharged below by `exp_skew_isometry`, which
feeds this lemma in `blockCone_preserved_of_skew`. -/
theorem boost_preserves_blockCone_of_isometry {φ : W → W} {s : ℝ}
    (hiso : ∀ w, ‖φ w‖ = ‖w‖) :
    ∀ v : ℝ × ℝ × W, BlockCone v → BlockCone (boost φ s v) :=
  (boost_preserves_blockCone_iff φ s).mpr fun w => (hiso w).le

omit [InnerProductSpace ℝ W] in
/-- The "both signs" upgrade in the proof of `prop:isotropy`: a contraction that is a
one-parameter group (so `φ (-s)` inverts `φ s`) is in fact an isometry.  Holding for
all `s ∈ ℝ` forces `‖φ s w‖ = ‖w‖`. -/
theorem isometry_of_contraction_group {φ : ℝ → W → W}
    (hcontract : ∀ s w, ‖φ s w‖ ≤ ‖w‖) (hgroup : ∀ s w, φ (-s) (φ s w) = w) :
    ∀ s w, ‖φ s w‖ = ‖w‖ := by
  intro s w
  refine le_antisymm (hcontract s w) ?_
  calc ‖w‖ = ‖φ (-s) (φ s w)‖ := by rw [hgroup]
    _ ≤ ‖φ s w‖ := hcontract (-s) (φ s w)

/-! ## Skew-adjointness `T ∈ 𝔰𝔬(W)` (`prop:isotropy`) -/

/-- A real linear operator is *skew-adjoint* (`T ∈ 𝔰𝔬(W)`, the Lie algebra of the
orthogonal group of the trace inner product) when `⟪T x, y⟫ = -⟪x, T y⟫`.  This is the
conclusion `T ∈ 𝔰𝔬(W)` of `prop:isotropy`. -/
def IsSkewAdjoint (T : W →ₗ[ℝ] W) : Prop :=
  ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ

/-- Polarization: `T` is skew-adjoint iff `⟪T w, w⟫ = 0` for every `w`.  This is the
real content of "`e^{sT}` isometric ⟹ `T ∈ 𝔰𝔬(W)`": once the generator kills the
quadratic form `w ↦ ⟪T w, w⟫`, skew-adjointness follows by the polarization identity. -/
theorem isSkewAdjoint_iff_inner_self (T : W →ₗ[ℝ] W) :
    IsSkewAdjoint T ↔ ∀ w, ⟪T w, w⟫_ℝ = 0 := by
  constructor
  · intro hT w
    have h := hT w w
    rw [real_inner_comm (T w) w] at h
    linarith
  · intro h x y
    have hxy := h (x + y)
    have hx := h x
    have hy := h y
    rw [map_add, inner_add_left, inner_add_right, inner_add_right,
        ← real_inner_comm (T y) x] at hxy
    linarith

/-- The generator `T` of an isometric one-parameter flow `φ` (with `φ 0 = id` and
`d/ds φ s w |₀ = T w`) kills the quadratic form: `⟪T w, w⟫ = 0`.  Differentiate the
constant `s ↦ ⟪φ s w, φ s w⟫ = ‖w‖²` at `s = 0`. -/
theorem inner_generator_self_zero {φ : ℝ → W → W} {T : W →ₗ[ℝ] W}
    (hgen : ∀ w, HasDerivAt (fun s => φ s w) (T w) 0)
    (hid : ∀ w, φ 0 w = w) (hiso : ∀ s w, ‖φ s w‖ = ‖w‖) :
    ∀ w, ⟪T w, w⟫_ℝ = 0 := by
  intro w
  -- `s ↦ ⟪φ s w, φ s w⟫` is the constant `‖w‖²`, hence has derivative `0` at `0`.
  have hd0 : HasDerivAt (fun s => ⟪φ s w, φ s w⟫_ℝ) 0 0 := by
    have hcst : (fun s => ⟪φ s w, φ s w⟫_ℝ) = fun _ => ‖w‖ ^ 2 := by
      funext s; rw [real_inner_self_eq_norm_sq, hiso s w]
    rw [hcst]; exact hasDerivAt_const 0 _
  -- the product rule gives the derivative as `⟪φ 0 w, T w⟫ + ⟪T w, φ 0 w⟫`.
  have hdi : HasDerivAt (fun s => ⟪φ s w, φ s w⟫_ℝ)
      (⟪φ 0 w, T w⟫_ℝ + ⟪T w, φ 0 w⟫_ℝ) 0 :=
    HasDerivAt.inner (𝕜 := ℝ) (hgen w) (hgen w)
  have huniq : ⟪φ 0 w, T w⟫_ℝ + ⟪T w, φ 0 w⟫_ℝ = 0 := (hd0.unique hdi).symm
  rw [hid, real_inner_comm (T w) w] at huniq
  linarith

/-- **Twist isotropy (`prop:isotropy`).**  Let `φ` be a one-parameter group of
`W`-actions (`φ 0 = id`, `φ (-s)` inverts `φ s`) with generator `T` at `s = 0`, and
suppose the associated boost preserves the rank-two block cone at every `s` (the
Euclidean Jordan cone-preservation hypothesis).  Then the twist generator is
skew-adjoint, `T ∈ 𝔰𝔬(W)`.

The proof chains the boost criterion (`boost_preserves_blockCone_iff`: cone-preservation
gives a contraction at each `s`), the both-signs upgrade
(`isometry_of_contraction_group`: an invertible contraction is an isometry), and the
polarization/derivative bridge (`inner_generator_self_zero` +
`isSkewAdjoint_iff_inner_self`). -/
theorem twist_isotropy {φ : ℝ → W → W} {T : W →ₗ[ℝ] W}
    (hgen : ∀ w, HasDerivAt (fun s => φ s w) (T w) 0)
    (hid : ∀ w, φ 0 w = w) (hgroup : ∀ s w, φ (-s) (φ s w) = w)
    (hcone : ∀ s, ∀ v : ℝ × ℝ × W, BlockCone v → BlockCone (boost (φ s) s v)) :
    IsSkewAdjoint T := by
  have hcontract : ∀ s w, ‖φ s w‖ ≤ ‖w‖ := fun s =>
    (boost_preserves_blockCone_iff (φ s) s).mp (hcone s)
  have hiso : ∀ s w, ‖φ s w‖ = ‖w‖ := isometry_of_contraction_group hcontract hgroup
  rw [isSkewAdjoint_iff_inner_self]
  exact inner_generator_self_zero hgen hid hiso

/-! ## Reuse of `SpinFactor`: the `d = 1` (real) row of the type table -/

/-- Reuse of `SpinFactor.lean`'s cone development.  The concrete spin factor
`V₃ ≅ M₂(ℝ)ˢᵃ` cone `SpinFactor.IsNonneg` is exactly the abstract block cone at
`W = ℝ`, in coordinates `α = a₀ + a₂`, `β = a₀ - a₂`, `w = a₁`: the two diagonal
matrix entries and the single off-diagonal Peirce `1`-space coordinate.  This is the
`d = 1` "real" row of `prop:type-table` (`H_n(ℝ)`, `dim W = 1`, twist group
`SO(1) = {1}` trivial), where the axioms force the Lüders scalar outright. -/
theorem spinFactor_isNonneg_iff_blockCone (a : SpinFactor) :
    SpinFactor.IsNonneg a ↔
      BlockCone (W := ℝ) (a.1 + a.2.2, a.1 - a.2.2, a.2.1) := by
  simp only [SpinFactor.IsNonneg, SpinFactor.blochNormSq, BlockCone,
    Real.norm_eq_abs, sq_abs]
  constructor
  · rintro ⟨h0, hbn⟩
    exact ⟨by nlinarith [sq_nonneg a.2.1], by nlinarith [sq_nonneg a.2.1],
      by nlinarith⟩
  · rintro ⟨hα, hβ, hw⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-! ## The converse leg (`prop:isotropy` "⟸"): skew generator ⟹ cone-preserving flow

Completes the abstract-block equivalence of `prop:isotropy` in the "every
`T ∈ 𝔰𝔬(W)` makes every boost an order automorphism" direction, backing the
manuscript's "the local twist group is exactly `SO(W)`" claim.  We realize the flow
as the operator exponential `φ s = exp(s • T)` (finite-dimensional `W` is complete, so
the exponential converges); differentiating `s ↦ ⟪φ s w, φ s w⟫` gives derivative
`2⟪T (φ s w), φ s w⟫ = 0` for skew `T`, so the squared norm is constant and the flow is
isometric — then `boost_preserves_blockCone_of_isometry` finishes.  `W` is taken complete
(the finite-dimensional case). -/

section Converse

variable [CompleteSpace W]

/-- The operator exponential of a skew-adjoint generator is an isometry:
`‖exp(s • T) w‖ = ‖w‖` for all `s`.  This is the core of `prop:isotropy`'s converse.
Proof: `s ↦ ⟪exp(s•T) w, exp(s•T) w⟫` has derivative `2⟪T(exp(s•T)w), exp(s•T)w⟫`, which
vanishes for skew `T`, so the squared norm is constant equal to its value `‖w‖²` at
`s = 0`. -/
theorem exp_skew_isometry (T : W →L[ℝ] W) (hT : ∀ v : W, ⟪T v, v⟫_ℝ = 0) (s : ℝ) (w : W) :
    ‖(NormedSpace.exp (s • T)) w‖ = ‖w‖ := by
  -- the squared norm `s ↦ ⟪exp(s•T)w, exp(s•T)w⟫` has derivative `0` at every `t`.
  have hHD : ∀ t : ℝ, HasDerivAt
      (fun u : ℝ => ⟪(NormedSpace.exp (u • T)) w, (NormedSpace.exp (u • T)) w⟫_ℝ) 0 t := by
    intro t
    have hexp : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • T))
        (T * NormedSpace.exp (t • T)) t := hasDerivAt_exp_smul_const' T t
    -- differentiate `u ↦ exp(u•T) w`; the derivative is `T (exp(t•T) w)` (primed variant
    -- puts `T` on the left, avoiding a commuting step).
    have hvec : HasDerivAt (fun u : ℝ => (NormedSpace.exp (u • T)) w)
        (T ((NormedSpace.exp (t • T)) w)) t := by
      have h := hexp.clm_apply (hasDerivAt_const t w)
      simpa [ContinuousLinearMap.mul_apply] using h
    have hi := HasDerivAt.inner (𝕜 := ℝ) hvec hvec
    have hz : ⟪(NormedSpace.exp (t • T)) w, T ((NormedSpace.exp (t • T)) w)⟫_ℝ
        + ⟪T ((NormedSpace.exp (t • T)) w), (NormedSpace.exp (t • T)) w⟫_ℝ = 0 := by
      rw [real_inner_comm (T ((NormedSpace.exp (t • T)) w)) ((NormedSpace.exp (t • T)) w)]
      have := hT ((NormedSpace.exp (t • T)) w)
      linarith
    rwa [hz] at hi
  -- a real function with derivative `0` everywhere is constant, so its value at `s`
  -- equals its value at `0`.
  have hconst := is_const_of_deriv_eq_zero
    (fun t => (hHD t).differentiableAt) (fun t => (hHD t).deriv) s 0
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hconst
  have h0 : (NormedSpace.exp ((0 : ℝ) • T)) w = w := by
    rw [zero_smul, NormedSpace.exp_zero]; rfl
  rw [h0] at hconst
  -- `‖exp(s•T) w‖² = ‖w‖²` with both nonnegative gives `‖exp(s•T) w‖ = ‖w‖`.
  have hsqrt := congrArg Real.sqrt hconst
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- **Converse of `prop:isotropy` (abstract block level).**  A skew-adjoint generator
`T ∈ 𝔰𝔬(W)` produces, via the operator exponential `φ s = exp(s • T)`, a flow whose
boost preserves the rank-two block cone at every `s`.  Together with the forward
direction (`twist_isotropy`) and the two-way `boost_preserves_blockCone_iff`, this
completes the equivalence *cone-preserving one-parameter groups ↔ `𝔰𝔬(W)` generators*
at the block level — the content of the manuscript's "the local twist group is exactly
`SO(W)`". -/
theorem blockCone_preserved_of_skew (T : W →L[ℝ] W)
    (hT : IsSkewAdjoint (T : W →ₗ[ℝ] W)) (s : ℝ) :
    ∀ v : ℝ × ℝ × W,
      BlockCone v → BlockCone (boost (fun w => (NormedSpace.exp (s • T)) w) s v) := by
  have hv : ∀ v : W, ⟪T v, v⟫_ℝ = 0 := fun v => by
    simpa using (isSkewAdjoint_iff_inner_self (T : W →ₗ[ℝ] W)).mp hT v
  exact boost_preserves_blockCone_of_isometry fun w => exp_skew_isometry T hv s w

end Converse

end Selection.TwistIsotropy
