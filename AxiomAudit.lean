import RadicalRelativity

open Lean

/-! # Axiom census, closure allowlist, and statement-fidelity gates

Three layers, all enforced by elaborating this file
(`lake env lean AxiomAudit.lean`):

1. a **project-wide axiom census** — every declaration defined in a
   `RadicalRelativity.*` module may depend only on Lean's three core axioms
   (`propext`, `Classical.choice`, `Quot.sound`) and the two disclosed
   cited-literature axioms (`Selection.aczel_continuous_multiplicative`,
   `TwistNormalForm.bgw_canonical_composite`).  A `sorryAx`, `native_decide`,
   or any other axiom anywhere in the tree fails elaboration.  This is the
   global no-`sorry`/no-stray-axiom gate;
2. **exact-closure sentinels** — one principal advertised result per module
   family, each pinned by `#guard_msgs` to *exactly* the three core axioms
   (i.e. not even the two cited axioms enter these cones);
3. **statement-fidelity pins** — the public S2 predicate, the two product-level
   conclusion shapes, and the effect-level product, pinned by definitional
   equality so a `True` body or a dropped quantifier fails elaboration.
-/

-- Layer 1: project-wide axiom census.
run_cmd do
  let env ← getEnv
  let allowed : List Name :=
    [``propext, ``Classical.choice, ``Quot.sound,
     ``Selection.aczel_continuous_multiplicative,
     ``TwistNormalForm.bgw_canonical_composite]
  let isProject := fun (n : Name) =>
    match env.getModuleFor? n with
    | some m => (`RadicalRelativity).isPrefixOf m
    | none => false
  -- fast union pass over all project declarations (shared, memoised state)
  let mut st : Lean.CollectAxioms.State := {}
  for (n, _) in env.constants.toList do
    if isProject n then
      st := (((Lean.CollectAxioms.collect n).run env).run st).2
  let bad := st.axioms.filter (fun a => !allowed.contains a)
  if bad.isEmpty then
    logInfo m!"Axiom census PASS: every RadicalRelativity declaration depends only on {allowed}"
  else
    -- attribute offenders (this second pass runs only on failure)
    let mut offenders : Array Name := #[]
    for (n, _) in env.constants.toList do
      if isProject n then
        let (_, s) := ((Lean.CollectAxioms.collect n).run env).run {}
        if s.axioms.any (fun a => !allowed.contains a) then
          offenders := offenders.push n
    throwError m!"Project-wide axiom census FAILED. Unpermitted axioms: {bad}. Offending declarations: {offenders}"

/-! ## Layer 2: exact-closure sentinels

Each `#guard_msgs (whitespace := lax)` fails elaboration unless the named
theorem's axiom closure is *exactly* Lean's three core axioms.  The list covers
one principal advertised result per module family (the four produced branches,
the central decomposition, the two globalization results, the adapter
globalizer, and the rank-two classification endpoints).  The project-wide census
above already bounds *every* declaration; these sentinels additionally certify
that the advertised endpoints do not lean on the two cited axioms. -/

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

/-! ## Layer 3: statement-fidelity pins

These do not claim the classification theorem; they make the audit fail if the
public S2 predicate, the two product-level target shapes, or the effect-level
product silently change.  The Lüders and unique-twist gates pin the **complete**
definitions by definitional equality (`rfl`). -/

example {V : Type*} [SequentialProduct V] {b : V}
    (hb : OrderUnitSpace.IsEffect b) :
    ContinuousOn
      (fun a : V => SequentialProductCore.sp a b)
      {a : V | OrderUnitSpace.IsEffect a} :=
  PaperA.s2_first_argument hb

example {V : Type*} [SequentialProduct V] (a b : PaperA.Effect V) :
    (PaperA.effectProduct V a b : V) = SequentialProductCore.sp a.1 b.1 :=
  rfl

example {V : Type*} [SequentialProduct V] (luders : PaperA.EffectProduct V) :
    PaperA.LudersConclusion V luders
      = ∀ a b, PaperA.effectProduct V a b = luders a b :=
  rfl

example {V : Type*} [SequentialProduct V] (twist : ℝ → PaperA.EffectProduct V) :
    PaperA.UniqueTwistConclusion V twist
      = ∃! t : ℝ, ∀ a b, PaperA.effectProduct V a b = twist t a b :=
  rfl
