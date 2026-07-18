import RadicalRelativity.MasterTheorem.Master
import RadicalRelativity.PaperA.Statement

/--
info: 'MasterTheorem.master_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MasterTheorem.master_chain

/-! The following terms are statement-fidelity compile gates.  They do not
claim the classification theorem; they make the audit fail if the public S2 or
product-level target shapes silently change. -/

example {V : Type*} [SequentialProduct V] {b : V}
    (hb : OrderUnitSpace.IsEffect b) :
    ContinuousOn
      (fun a : V => SequentialProductCore.sp a b)
      {a : V | OrderUnitSpace.IsEffect a} :=
  PaperA.s2_first_argument hb

example {V : Type*} [SequentialProduct V]
    (luders : PaperA.EffectProduct V) : Prop :=
  PaperA.LudersConclusion V luders

example {V : Type*} [SequentialProduct V]
    (twist : ℝ → PaperA.EffectProduct V) : Prop :=
  PaperA.UniqueTwistConclusion V twist
