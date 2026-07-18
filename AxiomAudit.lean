import RadicalRelativity.MasterTheorem.Master
import RadicalRelativity.MasterTheorem.Central
import RadicalRelativity.MasterTheorem.Globalization
import RadicalRelativity.MasterTheorem.Adapter
import RadicalRelativity.MasterTheorem.RankTwo
import RadicalRelativity.PaperA.Statement

/-! # Axiom-closure allowlist

Each `#guard_msgs`-guarded `#print axioms` below fails elaboration unless the
named theorem's axiom closure is exactly Lean's three core axioms
(`propext`, `Classical.choice`, `Quot.sound`).  The list is not just the
`master_chain` capstone: it covers one principal advertised result per module
family (the four produced branches, the central decomposition, the two
globalization results, the adapter globalizer, and the rank-two classification
endpoints), so a stray `axiom`, `sorry`, or `native_decide` anywhere in their
cones turns the audit red.  The two cited-import axioms
(`aczel_continuous_multiplicative`, `bgw_canonical_composite`) live in the
normal-form and composition legs, outside every cone probed here. -/

/-- info: 'MasterTheorem.master_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.master_chain

/-- info: 'MasterTheorem.luders_real_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.luders_real_produced

/-- info: 'MasterTheorem.luders_quaternionic_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.luders_quaternionic_produced

/-- info: 'MasterTheorem.luders_albert_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.luders_albert_produced

/-- info: 'MasterTheorem.complex_perFrame_produced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.complex_perFrame_produced

/-- info: 'MasterTheorem.Central.central_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.Central.central_decomposition

/-- info: 'MasterTheorem.Globalization.ComplexGlobalizationData.t_eq_globalT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.Globalization.ComplexGlobalizationData.t_eq_globalT

/-- info: 'MasterTheorem.Globalization.real_character_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.Globalization.real_character_unique

/-- info: 'MasterTheorem.global_twist_of_perFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.global_twist_of_perFrame

/-- info: 'MasterTheorem.RankTwo.n2_necessity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.RankTwo.n2_necessity

/-- info: 'MasterTheorem.RankTwo.sp_tau_had_is_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.RankTwo.sp_tau_had_is_luders

/-- info: 'MasterTheorem.RankTwo.sp_tau_std_is_unit_twist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MasterTheorem.RankTwo.sp_tau_std_is_unit_twist

/-! ## Statement-fidelity compile gates

These do not claim the classification theorem; they make the audit fail if the
public S2 predicate or the two product-level target shapes silently change.  The
Lüders and unique-twist gates pin the **complete** definitions by definitional
equality (`rfl`), so replacing either body by `True` — or dropping a quantifier
or the effect-product equality — breaks the audit. -/

example {V : Type*} [SequentialProduct V] {b : V}
    (hb : OrderUnitSpace.IsEffect b) :
    ContinuousOn
      (fun a : V => SequentialProductCore.sp a b)
      {a : V | OrderUnitSpace.IsEffect a} :=
  PaperA.s2_first_argument hb

example {V : Type*} [SequentialProduct V] (luders : PaperA.EffectProduct V) :
    PaperA.LudersConclusion V luders
      = ∀ a b, PaperA.effectProduct V a b = luders a b :=
  rfl

example {V : Type*} [SequentialProduct V] (twist : ℝ → PaperA.EffectProduct V) :
    PaperA.UniqueTwistConclusion V twist
      = ∃! t : ℝ, ∀ a b, PaperA.effectProduct V a b = twist t a b :=
  rfl
