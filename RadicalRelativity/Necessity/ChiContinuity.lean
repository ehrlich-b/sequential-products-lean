/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ChiExtension
import RadicalRelativity.Necessity.OneParameter
import Mathlib.Analysis.Normed.Ring.Lemmas

set_option linter.style.longLine false

/-!
# Line-continuity of χ̃ and the differential `dχ`  (campaign LEDGER 2.6, χ̃ parts 2b–2c)

The analytic half of `lem:homomorphism`, machine-checked on `H_n(ℂ)`:

* **Continuity ladder** — S2 (`FirstArgContinuous`) composed with the continuous
  effect-valued curve `t ↦ a(γ t)` gives continuity of the `L'`-part
  (`continuous_seqLeftMul_comp`); the `Q_{√a}⁻¹`-part is an *explicit diagonal*
  (`cfc_diagonal`: `Q⁻¹`-conjugation by `diag((√exp γᵢ)⁻¹)`), continuous by
  inspection; together: `continuous_theta_apply`, then `continuous_thetaUnit_val`
  by the finite-dimensional reduction `continuous_clm_apply`. The inverse factor
  rides `NormedRing.inverse_continuousAt` through the units.
* **`continuous_chiTilde_line`** — `t ↦ χ̃(t • v)` is continuous for every
  direction `v`: the canonical-representative exponents `(tv) ⊓ 0` and
  `(tv) ⊓ 0 − tv` are continuous orthant-valued curves, so both factors are
  continuous.
* **`chiTilde_eq_exp` / `dChi`** — `multiParameter_eq_exp` applied to
  `r ↦ (χ̃ r).val`: there is a unique linear `dχ : ℝⁿ →ₗ End(H_n(ℂ))` with
  `χ̃(r) = exp(dχ(r))` — the differential of the character, with linearity (hence
  additivity and continuity of the would-be `dχAdd` field) *proved*, not imported.

Everything involving the cocycle is conditional on `ThetaPreservesJordan` (M3),
as everywhere in this lane.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace Topology NormedSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Topology bridge**: the ambient (strong) topology on the endomorphism algebra
of the finite-dimensional `HermitianMat n ℂ` is definitionally the operator-norm
topology, but typeclass search will not unfold that far — so the norm-derived
`IsTopologicalRing` is registered here at the ambient instance explicitly. (A
`Prop`-valued mixin: no diamond risk.) Everything downstream — `Continuous.mul`,
`NormedSpace.exp` — needs it. -/
instance : IsTopologicalRing (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) := by
  exact @NonUnitalSeminormedRing.toIsTopologicalRing
    (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) _

variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## Continuity transfer between `HermitianMat` and its matrix part -/

theorem continuous_of_mat_continuous {X : Type*} [TopologicalSpace X]
    {f : X → HermitianMat n ℂ} (h : Continuous fun t => (f t).mat) :
    Continuous f :=
  IsInducing.subtypeVal.continuous_iff.mpr h

theorem continuous_mat {X : Type*} [TopologicalSpace X]
    {f : X → HermitianMat n ℂ} (h : Continuous f) :
    Continuous fun t => (f t).mat :=
  continuous_subtype_val.comp h

/-- The diagonal family along a continuous parameter curve. -/
theorem continuous_diagFamily {X : Type*} [TopologicalSpace X]
    {γ : X → (n → ℝ)} (hγ : Continuous γ) :
    Continuous fun t => diagFamily (γ t) := by
  apply continuous_of_mat_continuous
  show Continuous fun t => (diagFamily (γ t)).mat
  simp only [diagFamily_mat]
  apply Continuous.matrix_diagonal
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_apply i).comp hγ))

/-! ## The continuity ladder: S2 up through Θ -/

/-- S2 composed with a continuous effect-valued curve. -/
theorem continuous_sp_comp (hS2 : P.FirstArgContinuous) {X : Type*} [TopologicalSpace X]
    {g : X → HermitianMat n ℂ} (hg : Continuous g) (hgeff : ∀ t, IsEffect (g t))
    {e : HermitianMat n ℂ} (he : IsEffect e) :
    Continuous fun t => P.sp (g t) e :=
  (hS2 he).comp_continuous hg hgeff

/-- The positive extension `spPos` in its first argument along an effect curve. -/
theorem continuous_spPos_comp (hS2 : P.FirstArgContinuous) {X : Type*} [TopologicalSpace X]
    {g : X → HermitianMat n ℂ} (hg : Continuous g) (hgeff : ∀ t, IsEffect (g t))
    {x : HermitianMat n ℂ} (hx : 0 ≤ x) :
    Continuous fun t => spPos P (g t) x := by
  show Continuous fun t => (‖x‖ + 1) • P.sp (g t) ((‖x‖ + 1)⁻¹ • x)
  exact (continuous_sp_comp P hS2 hg hgeff
    (norm_smul_inv_effect hx (by positivity) (le_norm_add_one_smul_one x))).const_smul _

/-- The extended left multiplication applied to a fixed vector, along an effect
curve (the `L'`-part of Θ). -/
theorem continuous_seqLeftMul_comp (hS2 : P.FirstArgContinuous) {X : Type*}
    [TopologicalSpace X] {g : X → HermitianMat n ℂ} (hg : Continuous g)
    (hgeff : ∀ t, IsEffect (g t)) (x : HermitianMat n ℂ) :
    Continuous fun t => seqLeftMul P (g t) (hgeff t) x := by
  show Continuous fun t => spPos P (g t) (x⁺) - spPos P (g t) (x⁻)
  exact (continuous_spPos_comp P hS2 hg hgeff (HermitianMat.posPart_nonneg x)).sub
    (continuous_spPos_comp P hS2 hg hgeff (HermitianMat.negPart_nonneg x))

/-- **Θ applied to a fixed vector is continuous along the diagonal family over any
continuous orthant-valued curve.** The `L'`-part is S2; the `Q_{√a}⁻¹`-part is the
explicit diagonal conjugation `y ↦ D y Dᴴ`, `D = diag((√exp γᵢ)⁻¹)`. -/
theorem continuous_theta_apply (hS2 : P.FirstArgContinuous) {X : Type*}
    [TopologicalSpace X] {γ : X → (n → ℝ)} (hγ : Continuous γ)
    (hγ0 : ∀ t i, γ t i ≤ 0) (x : HermitianMat n ℂ) :
    Continuous fun t =>
      theta P (diagFamily_isEffect (hγ0 t)) (diagFamily_posDef (γ t)) x := by
  have hA : Continuous fun t =>
      seqLeftMul P (diagFamily (γ t)) (diagFamily_isEffect (hγ0 t)) x :=
    continuous_seqLeftMul_comp P hS2 (continuous_diagFamily hγ)
      (fun t => diagFamily_isEffect (hγ0 t)) x
  show Continuous fun t =>
    (quadRepEquiv (diagFamily (γ t)) (diagFamily_posDef (γ t))).symm
      (seqLeftMul P (diagFamily (γ t)) (diagFamily_isEffect (hγ0 t)) x)
  simp only [quadRepEquiv_symm_apply]
  apply continuous_of_mat_continuous
  simp only [HermitianMat.conj_apply_mat]
  have hD : Continuous fun t =>
      ((diagFamily (γ t)).cfc fun s => (Real.sqrt s)⁻¹).mat := by
    have hrw : ∀ t, ((diagFamily (γ t)).cfc fun s => (Real.sqrt s)⁻¹)
        = HermitianMat.diagonal ℂ (fun i => (Real.sqrt (Real.exp (γ t i)))⁻¹) := by
      intro t
      show (HermitianMat.diagonal ℂ fun i => Real.exp (γ t i)).cfc _ = _
      rw [HermitianMat.cfc_diagonal]
      rfl
    simp only [hrw, HermitianMat.diagonal_mat]
    apply Continuous.matrix_diagonal
    apply continuous_pi
    intro i
    apply Complex.continuous_ofReal.comp
    apply Continuous.inv₀
    · exact Real.continuous_sqrt.comp
        (Real.continuous_exp.comp ((continuous_apply i).comp hγ))
    · exact fun t => ne_of_gt (Real.sqrt_pos.mpr (Real.exp_pos _))
  exact (hD.matrix_mul (continuous_mat hA)).matrix_mul hD.matrix_conjTranspose

/-! ## Continuity of the units-valued character -/

theorem continuous_thetaUnit_val (hS2 : P.FirstArgContinuous) {X : Type*}
    [TopologicalSpace X] {γ : X → (n → ℝ)} (hγ : Continuous γ)
    (hγ0 : ∀ t i, γ t i ≤ 0) :
    Continuous fun t =>
      ((thetaUnit P hS2 (γ t) : (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ) :
        HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) := by
  rw [continuous_clm_apply]
  intro x
  have hval : ∀ t, ((thetaUnit P hS2 (γ t)).val) x
      = theta P (diagFamily_isEffect (hγ0 t)) (diagFamily_posDef (γ t)) x := by
    intro t
    rw [thetaUnit_val_apply, thetaNorm_apply_eq_theta P hS2
      (diagFamily_isEffect (hγ0 t)) (diagFamily_posDef (γ t))]
  simp only [hval]
  exact continuous_theta_apply P hS2 hγ hγ0 x

theorem continuous_thetaUnit_inv_val (hS2 : P.FirstArgContinuous) {X : Type*}
    [TopologicalSpace X] {γ : X → (n → ℝ)} (hγ : Continuous γ)
    (hγ0 : ∀ t i, γ t i ≤ 0) :
    Continuous fun t =>
      (((thetaUnit P hS2 (γ t))⁻¹ : (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ) :
        HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) := by
  have hval := continuous_thetaUnit_val P hS2 hγ hγ0
  have hrw : ∀ t, (((thetaUnit P hS2 (γ t))⁻¹ :
      (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ) :
        HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)
      = Ring.inverse ((thetaUnit P hS2 (γ t)).val) := by
    intro t
    rw [Ring.inverse_unit]
  simp only [hrw]
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  have hinv : ContinuousAt
      (Ring.inverse : (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)
        → (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ))
      ((fun t => (thetaUnit P hS2 (γ t)).val) t₀) := by
    exact NormedRing.inverse_continuousAt
      (⟨(thetaUnit P hS2 (γ t₀)).val, (thetaUnit P hS2 (γ t₀)).inv,
        (thetaUnit P hS2 (γ t₀)).val_inv, (thetaUnit P hS2 (γ t₀)).inv_val⟩)
  exact ContinuousAt.comp (f := fun t => (thetaUnit P hS2 (γ t)).val) (x := t₀)
    hinv hval.continuousAt

/-- **Line-continuity of the character**: `t ↦ χ̃(t • v)` is continuous for every
direction `v` — the hypothesis `multiParameter_eq_exp` consumes. -/
theorem continuous_chiTilde_line (hS2 : P.FirstArgContinuous) (v : n → ℝ) :
    Continuous fun t : ℝ =>
      ((chiTilde P hS2 (t • v) : (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ) :
        HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) := by
  have hγ1 : Continuous fun t : ℝ => ((t • v) ⊓ 0 : n → ℝ) := by
    apply continuous_pi
    intro i
    show Continuous fun t : ℝ => min (t * v i) 0
    exact (continuous_id.mul continuous_const).min continuous_const
  have hγ2 : Continuous fun t : ℝ => (((t • v) ⊓ 0) - t • v : n → ℝ) := by
    apply continuous_pi
    intro i
    show Continuous fun t : ℝ => min (t * v i) 0 - t * v i
    exact ((continuous_id.mul continuous_const).min continuous_const).sub
      (continuous_id.mul continuous_const)
  have h1 := continuous_thetaUnit_val P hS2 hγ1 (fun t => inf_zero_nonpos (t • v))
  have h2 := continuous_thetaUnit_inv_val P hS2 hγ2 (fun t => inf_zero_sub_nonpos (t • v))
  simp only [chiTilde, Units.val_mul]
  exact h1.mul h2

/-! ## The differential `dχ` -/

/-- **The character is an exponential** (`lem:homomorphism`, analytic half): there
is a unique linear `dχ : ℝⁿ →ₗ End(H_n(ℂ))` with `χ̃(r) = exp(dχ(r))`. Linearity —
hence the additivity and continuity that the abstract `DiagonalHomSetup` carries
as its `dχAdd`/`dχAdd_cont` fields — is *proved*, not imported. Conditional on
S2 and the M3 field, exactly as the paper's proof is. -/
theorem chiTilde_eq_exp (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    ∃! D : (n → ℝ) →ₗ[ℝ] (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ),
      ∀ r : n → ℝ, ((chiTilde P hS2 r :
        (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ) :
          HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) = exp (D r) :=
  multiParameter_eq_exp (fun r => ((chiTilde P hS2 r).val))
    (fun r r' => by
      show ((chiTilde P hS2 (r + r')).val)
        = ((chiTilde P hS2 r).val) * ((chiTilde P hS2 r').val)
      rw [chiTilde_add P hS2 hjord r r', Units.val_mul])
    (by
      show ((chiTilde P hS2 0).val) = 1
      rw [chiTilde_zero P hS2, Units.val_one])
    (fun v => continuous_chiTilde_line P hS2 v)

/-- The differential of the character, as data. -/
def dChi (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    (n → ℝ) →ₗ[ℝ] (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) :=
  (chiTilde_eq_exp P hS2 hjord).exists.choose

theorem chiTilde_eq_exp_dChi (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) :
    ((chiTilde P hS2 r : (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)ˣ) :
      HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) = exp (dChi P hS2 hjord r) :=
  (chiTilde_eq_exp P hS2 hjord).exists.choose_spec r

end Necessity
