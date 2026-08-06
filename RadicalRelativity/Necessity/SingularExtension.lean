/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SequentialProduct
import RadicalRelativity.Hermitian.OrderUnit
import RadicalRelativity.MasterTheorem.Master

set_option linter.style.longLine false

/-!
# `prop:singular` wired on the concrete carrier  (LEDGER 2.9)

The positive-definite (invertible) effects are dense in the effect interval of
`H_n(ℂ)` — the paper's boundary sequence `a_ε = a + ε(𝟙 − a) → a` — and S2
makes `a ↦ a ∘ b` continuous on effects.  The standalone `prop_singular`
kernel (`Set.EqOn.closure`) therefore extends any agreement of two S1–S7+S2
sequential products on positive-definite effects to **all** effects:

* `isEffect_interp` / `posDef_interp` — the boundary sequence stays in the
  effect interval and is positive definite for `ε > 0`.
* `dense_posDef_effects` — density in the effect subtype.
* `sp_eq_on_effects_of_eq_on_posDef` — **`prop:singular`, wired**: the
  typewise classification, proved on invertible effects (where `Θ_a` lives),
  determines the product everywhere.
-/

noncomputable section

open ComplexOrder
open OrderUnitSpace Filter Topology

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Interpolation toward the unit stays in the effect interval. -/
theorem isEffect_interp {a : HermitianMat n ℂ} (ha : IsEffect a) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsEffect (a + t • (1 - a)) := by
  have h1a : (0 : HermitianMat n ℂ) ≤ 1 - a :=
    sub_nonneg.mpr (le_of_le_of_eq ha.2 HermitianMat.ousUnit_eq_one)
  constructor
  · exact _root_.add_nonneg ha.1 (smul_nonneg ht0 h1a)
  · have key : (𝟙 : HermitianMat n ℂ) - (a + t • (1 - a)) = (1 - t) • (1 - a) := by
      rw [HermitianMat.ousUnit_eq_one, sub_smul, one_smul]
      abel
    have hpos : (0 : HermitianMat n ℂ) ≤ (1 - t) • (1 - a) :=
      smul_nonneg (sub_nonneg.mpr ht1) h1a
    exact sub_nonneg.mp (key ▸ hpos)

/-- Interpolation strictly toward the unit is positive definite. -/
theorem posDef_interp {a : HermitianMat n ℂ} (ha : IsEffect a) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) : (a + t • (1 - a)).mat.PosDef := by
  have key : a + t • (1 - a) = t • (1 : HermitianMat n ℂ) + (1 - t) • a := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  rw [key, HermitianMat.mat_add]
  have h1 : ((t • (1 : HermitianMat n ℂ)).mat).PosDef := by
    rw [HermitianMat.mat_smul]
    exact Matrix.PosDef.one.smul ht0
  have h2 : (((1 - t) • a).mat).PosSemidef := by
    rw [HermitianMat.mat_smul]
    exact (HermitianMat.zero_le_iff.mp ha.1).smul (by linarith)
  exact h1.add_posSemidef h2

/-- **Density of the invertible effects** in the effect interval: the boundary
sequence `a + (1/(k+1))(𝟙 − a) → a`. -/
theorem dense_posDef_effects :
    Dense {x : {a : HermitianMat n ℂ // IsEffect a} | x.val.mat.PosDef} := by
  rintro ⟨a, ha⟩
  have hle : ∀ k : ℕ, (1 / ((k : ℝ) + 1)) ≤ 1 := by
    intro k
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hseq : ∀ k : ℕ, IsEffect (a + (1 / ((k : ℝ) + 1)) • (1 - a)) := fun k =>
    isEffect_interp ha (by positivity) (hle k)
  have htend : Tendsto (fun k : ℕ => a + (1 / ((k : ℝ) + 1)) • (1 - a))
      atTop (nhds a) := by
    have h0 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1))) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ)) |>.add
      (h0.smul_const (1 - a))
    simpa using h
  apply mem_closure_of_tendsto
    (f := fun k : ℕ => (⟨a + (1 / ((k : ℝ) + 1)) • (1 - a), hseq k⟩ :
      {a : HermitianMat n ℂ // IsEffect a}))
    (b := atTop)
  · exact tendsto_subtype_rng.mpr htend
  · filter_upwards with k
    exact posDef_interp ha (by positivity) (hle k)

/-- **`prop:singular`, WIRED (LEDGER 2.9).**  Two S1–S7 sequential products
with S2 that agree on the positive-definite effects agree on **all** effects:
the standalone `prop_singular` kernel applied over the effect subtype with the
density of invertible effects.  This is the paper's extension of the typewise
classification from invertible effects (where `Θ_a` is defined) to the entire
effect interval. -/
theorem sp_eq_on_effects_of_eq_on_posDef
    (P Q : SequentialProductOn (HermitianMat n ℂ))
    (hP : P.FirstArgContinuous) (hQ : Q.FirstArgContinuous)
    {b : HermitianMat n ℂ} (hb : IsEffect b)
    (hagree : ∀ a : HermitianMat n ℂ, IsEffect a → a.mat.PosDef →
      P.sp a b = Q.sp a b) :
    ∀ a : HermitianMat n ℂ, IsEffect a → P.sp a b = Q.sp a b := by
  have hf : Continuous fun x : {a : HermitianMat n ℂ // IsEffect a} =>
      P.sp x.val b :=
    continuousOn_iff_continuous_restrict.mp (hP hb)
  have hg : Continuous fun x : {a : HermitianMat n ℂ // IsEffect a} =>
      Q.sp x.val b :=
    continuousOn_iff_continuous_restrict.mp (hQ hb)
  have hkey := MasterTheorem.prop_singular dense_posDef_effects
    (fun x : {a : HermitianMat n ℂ // IsEffect a} => P.sp x.val b)
    (fun x => Q.sp x.val b) hf hg
    (fun x hx => hagree x.val x.property hx)
  intro a ha
  exact congrFun hkey ⟨a, ha⟩

end Necessity
