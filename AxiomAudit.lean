import RadicalRelativity

open Lean System

/-! # Axiom census, closure allowlist, coverage, and statement-fidelity gates

Six layers, all enforced by elaborating this file
(`lake env lean AxiomAudit.lean`):

1. a **tracked-tree census** — over every *persisted* declaration whose defining
   module has prefix `RadicalRelativity` (this file, `AxiomAudit.lean`, and any
   future package-root module outside that prefix are not visited; an anonymous
   `example := by sorry` persists no declaration and is not visited either) it
   enforces three things at once:
   (a) the axiom closure depends only on Lean's three core axioms
   (`propext`, `Classical.choice`, `Quot.sound`) — the tree carries NO custom
   axioms (`Selection.aczel_continuous_multiplicative` was DISCHARGED into a
   theorem 2026-08-05 via `Necessity/OneParameter.lean`; the former
   `TwistNormalForm.bgw_canonical_composite` was eliminated 2026-08-04 into
   the proved-table definition `bgwComposite`) — a `sorryAx`,
   `native_decide`, or any other axiom fails elaboration; (b) NO custom axiom
   declaration exists in the tracked tree — any stray `axiom`
   in any tracked module fails; and
   (c) **source coverage + frozen manifest**: the set of `RadicalRelativity`
   modules on disk equals the set imported here *and* equals a pinned 118-name
   manifest, so a new unimported module, a removed root import, a name-colliding
   source path, or a coordinated module+import deletion (which preserves
   `disk == imported`) fails, closing both the "invisible module" and the
   "shrink-both-sets" escapes.  The source→module map is first checked to reject
   dotted path segments and to be injective, so a file like `PaperA.Statement.lean`
   cannot collide with the nested module `PaperA/Statement`;
2. **exact-closure sentinels** — one principal advertised result per module
   family, each pinned by `#guard_msgs` to *exactly* the three core axioms
   (i.e. not even the cited axiom enters these cones);
3. **statement-fidelity pins** — the public S2 predicate, the two product-level
   conclusion shapes, and the effect-level product, are named, persisted
   theorems in `RadicalRelativity.PaperA.AuditPins` (so the census in Layer 1
   visits them: a `sorry` or stray axiom substituted for a pin's direct proof
   fails the census); here each is additionally exact-closure guarded;
4. **cited-axiom type pin** — the exact printed type of the custom axiom is
   frozen by `#guard_msgs`, so a silent statement drift under its name fails.
5. **S1--S7 / effect-boundary freezes** — the printed *types* of the S1, S3--S7
   fields and `sp_effect`, plus *body pins* for the S2 predicate, `IsEffect`,
   `Effect`, and `EffectProduct` (named `rfl`/`Iff.rfl` theorems in `AuditPins`,
   each type-frozen), plus *constructor freezes* for `SequentialProductCore.mk`,
   `SequentialProduct.mk`, and the S2 projection.  Together these make the small
   boundary deterministic against three body/class escapes that a type-only
   freeze misses: conjoining `False` onto S2, replacing `Effect` by an empty
   subtype, and adding a hidden impossible field to the `SequentialProduct`
   class (the last is caught by the changed constructor type).  This does *not*
   claim `master_chain`'s statement is frozen — Layer 2 guards its axiom closure
   only; the paper discloses it as a conditional skeleton.
6. **interface constructor freezes** — the printed constructor types of the five
   master-chain interface structures (`ComparisonSetup`, `CoalescenceSetup`,
   `DiagonalHomSetup`, `StabilizerCoupling`, `IsAlbertModel`) are frozen, so
   silent field drift on the §2 import ledger fails.  Body-hollowing of the
   helpers those types name opaquely (the `OpCommute`-to-`False` escape) is
   separately caught by the constructed witnesses in
   `RadicalRelativity.MasterTheorem.Witnesses`, and neither guard claims the
   fields are *true* on the intended EJA instances (see `LEDGER.md`).
-/

-- A recursive `.lean` source enumeration for the coverage check in Layer 1(c).
partial def auditCollectLeanFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut acc : Array FilePath := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if (← p.isDir) then
      acc := acc ++ (← auditCollectLeanFiles p)
    else if p.extension == some "lean" then
      acc := acc.push p
  return acc

-- Map a source path like `RadicalRelativity/PaperA/Statement.lean` to the module
-- name `RadicalRelativity.PaperA.Statement`.
def auditPathToModule (p : FilePath) : Name :=
  let s := p.toString
  let s := if s.endsWith ".lean" then s.take (s.length - 5) else s
  (s.replace "/" ".").toName

-- Layer 1: tracked-tree census (closure allowlist + custom-axiom set + coverage).
run_cmd do
  let env ← getEnv
  let allowed : List Name :=
    [``propext, ``Classical.choice, ``Quot.sound]
  let citedAxioms : List Name := []
  let isProject := fun (n : Name) =>
    match env.getModuleFor? n with
    | some m => (`RadicalRelativity).isPrefixOf m
    | none => false
  -- (a) closure census + custom-axiom collection: one shared, memoised pass.
  let mut st : Lean.CollectAxioms.State := {}
  let mut projectAxiomDecls : Array Name := #[]
  for (n, info) in env.constants.toList do
    if isProject n then
      st := (((Lean.CollectAxioms.collect n).run env).run st).2
      match info with
      | .axiomInfo _ => projectAxiomDecls := projectAxiomDecls.push n
      | _ => pure ()
  let bad := st.axioms.filter (fun a => !allowed.contains a)
  if !bad.isEmpty then
    let mut offenders : Array Name := #[]
    for (n, _) in env.constants.toList do
      if isProject n then
        let (_, s) := ((Lean.CollectAxioms.collect n).run env).run {}
        if s.axioms.any (fun a => !allowed.contains a) then
          offenders := offenders.push n
    throwError m!"Tracked-tree axiom census FAILED. Unpermitted axioms: {bad}. Offending declarations: {offenders}"
  -- (b) exactly the disclosed custom-axiom set exists.
  let unexpectedAx := projectAxiomDecls.toList.filter (fun a => !citedAxioms.contains a)
  let missingAx := citedAxioms.filter (fun a => !projectAxiomDecls.contains a)
  if !unexpectedAx.isEmpty || !missingAx.isEmpty then
    throwError m!"Custom-axiom set drift. Unexpected project axioms: {unexpectedAx}. Missing disclosed axioms: {missingAx}"
  -- (c) source coverage: disk `RadicalRelativity` modules == imported ones.
  let rrDir : FilePath := "RadicalRelativity"
  unless (← rrDir.isDir) do
    throwError m!"Module-coverage gate: run from the package root ('RadicalRelativity/' not found in the current directory)"
  let files ← auditCollectLeanFiles rrDir
  -- (c0) reject malformed source paths: below the `.lean` suffix every path
  -- segment must be a single module identifier with no embedded dot.  Otherwise a
  -- file like `RadicalRelativity/PaperA.Statement.lean` rewrites under the `/`→`.`
  -- map to the SAME name as the nested module `RadicalRelativity/PaperA/Statement`,
  -- and an unimported `sorry`/`axiom` source could hide behind that collision.
  for p in files do
    let s := p.toString
    for seg in s.splitOn "/" do
      let dots := (seg.toList.filter (fun c => c == '.')).length
      let ok := if seg.endsWith ".lean" then dots == 1 else dots == 0
      unless ok do
        throwError m!"Module-coverage gate FAILED: source path with a dotted segment (module-name collision hazard): {p}"
  -- (c1) the source-path → module-name map must be injective on the source tree,
  -- so two distinct files can never collapse to one name and mask an unimported
  -- source before the `eraseDups` below.
  let mappedMods : List Name := files.toList.map auditPathToModule
  if mappedMods.length ≠ mappedMods.eraseDups.length then
    throwError m!"Module-coverage gate FAILED: source-path→module map is not injective; distinct source files share a module name: {mappedMods}"
  let diskMods : List Name := (`RadicalRelativity :: mappedMods).eraseDups
  let importedMods : List Name :=
    (env.header.moduleNames.toList.filter (fun m => (`RadicalRelativity).isPrefixOf m)).eraseDups
  -- (c2) frozen expected-module manifest.  `disk == imported` alone is preserved
  -- by deleting a module AND its sole root import together (both sets shrink
  -- equally), so the tracked surface is additionally pinned to this exact 118-name
  -- list: any coordinated deletion, replacement (a count-preserving swap), or
  -- addition fails against `expectedMods`.
  let expectedMods : List Name :=
    [`RadicalRelativity,
     `RadicalRelativity.LocalTomography,
     `RadicalRelativity.OrderUnitSpace,
     `RadicalRelativity.SequentialProduct,
     `RadicalRelativity.SpinFactor,
     `RadicalRelativity.TwistNormalForm,
     `RadicalRelativity.MasterTheorem.Adapter,
     `RadicalRelativity.MasterTheorem.Central,
     `RadicalRelativity.MasterTheorem.Coalescence,
     `RadicalRelativity.MasterTheorem.DiagonalHom,
     `RadicalRelativity.MasterTheorem.Globalization,
     `RadicalRelativity.MasterTheorem.Interface,
     `RadicalRelativity.MasterTheorem.Master,
     `RadicalRelativity.MasterTheorem.RankTwo,
     `RadicalRelativity.MasterTheorem.Witnesses,
     `RadicalRelativity.Hermitian.OrderUnit,
     `RadicalRelativity.Hermitian.ExtremeEffects,
     `RadicalRelativity.Hermitian.Twist,
     `RadicalRelativity.Hermitian.Resolution,
     `RadicalRelativity.Hermitian.SqrtMul,
     `RadicalRelativity.Hermitian.CommutantHermitian,
     `RadicalRelativity.Hermitian.Sequential,
     `RadicalRelativity.Necessity.LeftMultiplication,
     `RadicalRelativity.Necessity.FirstArgument,
     `RadicalRelativity.Necessity.SharpEffects,
     `RadicalRelativity.Necessity.PseudoInverse,
     `RadicalRelativity.Necessity.Theta,
     `RadicalRelativity.Necessity.ThetaFix,
     `RadicalRelativity.Necessity.ThetaCocycle,
     `RadicalRelativity.Necessity.OneParameter,
     `RadicalRelativity.Necessity.DiagonalFamily,
     `RadicalRelativity.Necessity.DiagonalFamilyGen,
     `RadicalRelativity.Necessity.ChiGen,
     `RadicalRelativity.Necessity.ComparisonInstanceGen,
     `RadicalRelativity.Necessity.ChiExtensionGen,
     `RadicalRelativity.Necessity.ChiContinuityGen,
     `RadicalRelativity.Necessity.CoalescenceInstanceGen,
     `RadicalRelativity.Necessity.Chi,
     `RadicalRelativity.Necessity.ComparisonInstance,
     `RadicalRelativity.Necessity.ChiExtension,
     `RadicalRelativity.Necessity.ChiContinuity,
     `RadicalRelativity.Necessity.CoalescenceInstance,
     `RadicalRelativity.Necessity.CoalescenceDiff,
     `RadicalRelativity.Necessity.ThetaIsometry,
     `RadicalRelativity.Necessity.BlockInvariance,
     `RadicalRelativity.Necessity.BlockModel,
     `RadicalRelativity.Necessity.BlockTransport,
     `RadicalRelativity.Necessity.BlockChi,
     `RadicalRelativity.Necessity.BlockSkew,
     `RadicalRelativity.Necessity.StabilizerInstance,
     `RadicalRelativity.Necessity.PhaseCocycle,
     `RadicalRelativity.Necessity.JordanDerivation,
     `RadicalRelativity.Necessity.PhaseAnchor,
     `RadicalRelativity.Necessity.SingularExtension,
     `RadicalRelativity.Necessity.ProjectionOrder,
     `RadicalRelativity.Necessity.Strength,
     `RadicalRelativity.Necessity.StrengthProbe,
     `RadicalRelativity.Necessity.JordanWitness,
     `RadicalRelativity.Necessity.RankOneSpan,
     `RadicalRelativity.Necessity.WignerBridge,
     `RadicalRelativity.Necessity.RayMap,
     `RadicalRelativity.Necessity.KadisonDischarge,
     `RadicalRelativity.Necessity.ConjTransport,
     `RadicalRelativity.Necessity.TorusAction,
     `RadicalRelativity.Necessity.FrameBlockSpan,
     `RadicalRelativity.Necessity.TwistIdentification,
     `RadicalRelativity.Necessity.BlockCharacter,
     `RadicalRelativity.Necessity.MulEmbedding,
     `RadicalRelativity.Necessity.BlockRotation,
     `RadicalRelativity.Necessity.BlockAngle,
     `RadicalRelativity.Necessity.TwistPower,
     `RadicalRelativity.Necessity.TwistUniqueness,
     `RadicalRelativity.Necessity.TwistGeneral,
     `RadicalRelativity.Necessity.ComplexClassification,
     `RadicalRelativity.Necessity.RateFromCoupling,
     `RadicalRelativity.Necessity.ComplexMaster,
     `RadicalRelativity.RankTwo.Lifting,
     `RadicalRelativity.RankTwo.RealProjective,
     `RadicalRelativity.RankTwo.FrameFunction,
     `RadicalRelativity.RankTwo.Complementation,
     `RadicalRelativity.RankTwo.Separation,
     `RadicalRelativity.MasterTheorem.Branches.Albert,
     `RadicalRelativity.MasterTheorem.Branches.Complex,
     `RadicalRelativity.MasterTheorem.Branches.Quaternionic,
     `RadicalRelativity.MasterTheorem.Branches.Real,
     `RadicalRelativity.PaperA.AuditPins,
     `RadicalRelativity.PaperA.Statement,
     `RadicalRelativity.Selection.BaseEquality,
     `RadicalRelativity.Selection.Descent,
     `RadicalRelativity.Selection.Equidistribution,
     `RadicalRelativity.Selection.NormalFormExistence,
     `RadicalRelativity.Selection.SelectorEquivalence,
     `RadicalRelativity.Selection.TwistIsotropy,
     `RadicalRelativity.Vendor.Matrix,
     `RadicalRelativity.Vendor.Isometry,
     `RadicalRelativity.Vendor.Misc,
     `RadicalRelativity.Vendor.LinearEquiv,
     `RadicalRelativity.Vendor.ContinuousLinearMap,
     `RadicalRelativity.Vendor.IsMaximalSelfAdjoint,
     `RadicalRelativity.Vendor.Tactic.Commutes,
     `RadicalRelativity.Vendor.Tactic.Commutes.Attribute,
     `RadicalRelativity.Vendor.HermitianMat.Basic,
     `RadicalRelativity.Vendor.HermitianMat.Order,
     `RadicalRelativity.Vendor.HermitianMat.Inner,
     `RadicalRelativity.Vendor.HermitianMat.Trace,
     `RadicalRelativity.Vendor.HermitianMat.CFC,
     `RadicalRelativity.Vendor.HermitianMat.NonSingular,
     `RadicalRelativity.Vendor.HermitianMat.Reindex,
     `RadicalRelativity.Vendor.HermitianMat.Jordan,
     `RadicalRelativity.Vendor.HermitianMat.Proj,
     `RadicalRelativity.Vendor.Wigner.Topology,
     `RadicalRelativity.Vendor.Wigner.Unitary,
     `RadicalRelativity.Vendor.Wigner.UnitaryCompact,
     `RadicalRelativity.Vendor.Wigner.UnitaryHaar,
     `RadicalRelativity.Vendor.Wigner.MeasureSpace,
     `RadicalRelativity.Vendor.Wigner.FubiniStudy,
     `RadicalRelativity.Vendor.Wigner.TransitionProbability,
     `RadicalRelativity.Vendor.Wigner.WignerRigidity]
  let missExpDisk := expectedMods.filter (fun m => !diskMods.contains m)
  let extraDisk   := diskMods.filter (fun m => !expectedMods.contains m)
  let missExpImp  := expectedMods.filter (fun m => !importedMods.contains m)
  let extraImp    := importedMods.filter (fun m => !expectedMods.contains m)
  if !missExpDisk.isEmpty || !extraDisk.isEmpty || !missExpImp.isEmpty || !extraImp.isEmpty then
    throwError m!"Module-manifest gate FAILED (expected surface drifted). Expected-but-missing on disk: {missExpDisk}. Unexpected on disk: {extraDisk}. Expected-but-missing in imports: {missExpImp}. Unexpected in imports: {extraImp}"
  let onlyDisk := diskMods.filter (fun m => !importedMods.contains m)
  let onlyImported := importedMods.filter (fun m => !diskMods.contains m)
  if !onlyDisk.isEmpty || !onlyImported.isEmpty then
    throwError m!"Module-coverage gate FAILED. On disk but not imported (unimported source): {onlyDisk}. Imported but absent from disk (removed source / stale build): {onlyImported}"
  logInfo m!"Census PASS: {diskMods.length} tracked RadicalRelativity modules (== frozen 118-name manifest), custom axioms exactly {citedAxioms}, every tracked persisted declaration's closure ⊆ {allowed}"

/-! ## Layer 2: exact-closure sentinels

Each `#guard_msgs (whitespace := lax)` fails elaboration unless the named
theorem's axiom closure is *exactly* Lean's three core axioms.  The list covers
one principal advertised result per module family (the four produced branches,
the central decomposition, the two globalization results, the adapter
globalizer, and the selected rank-two algebraic endpoints — which do not
formalize the rank-two classification).  The tracked-tree census above already
bounds every tracked persisted declaration; these sentinels additionally certify
that the advertised endpoints depend on the three core axioms alone. -/

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

The four fidelity statements are named, persisted theorems in
`RadicalRelativity.PaperA.AuditPins` (visited by the Layer 1 census).  Each is
additionally exact-closure guarded below (so a pin proof weakened to `sorry` or a
stray axiom fails both the census and its sentinel) **and type-frozen** by a
`#guard_msgs`/`#check` pair (so a silent change to a pin's *statement* — even one
carried by a matching core-only direct proof — changes the printed type and fails
elaboration). -/

/-- info: 'PaperA.auditPin_s2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_s2

/-- info: 'PaperA.auditPin_effectProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_effectProduct

/-- info: 'PaperA.auditPin_luders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_luders

/-- info: 'PaperA.auditPin_uniqueTwist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_uniqueTwist

-- Type freezes: the exact printed statement of each fidelity pin.
/-- info: @PaperA.auditPin_s2 : ∀ {V : Type u_1} [inst : SequentialProduct V] {b : V},
  OrderUnitSpace.IsEffect b → ContinuousOn (fun a => SequentialProductCore.sp a b) {a | OrderUnitSpace.IsEffect a} -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_s2

/-- info: @PaperA.auditPin_effectProduct : ∀ {V : Type u_1} [inst : SequentialProduct V] (a b : PaperA.Effect V),
  ↑(PaperA.effectProduct V a b) = SequentialProductCore.sp ↑a ↑b -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_effectProduct

/-- info: @PaperA.auditPin_luders : ∀ {V : Type u_1} [inst : SequentialProduct V] (luders : PaperA.EffectProduct V),
  PaperA.LudersConclusion V luders = ∀ (a b : PaperA.Effect V), PaperA.effectProduct V a b = luders a b -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_luders

/-- info: @PaperA.auditPin_uniqueTwist : ∀ {V : Type u_1} [inst : SequentialProduct V] (twist : ℝ → PaperA.EffectProduct V),
  PaperA.UniqueTwistConclusion V twist = ∃! t, ∀ (a b : PaperA.Effect V), PaperA.effectProduct V a b = twist t a b -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_uniqueTwist

/-! ## Layer 4: statement pin for the discharged Aczél lemma

`Selection.aczel_continuous_multiplicative` is a THEOREM since 2026-08-05
(discharged via `Necessity/OneParameter.lean`); this pin now freezes the
theorem's statement so the discharged lemma cannot silently drift from the
paper's `lem:mult-rep` wording.  (The former Barnum–Graydon–Wilce axiom was
eliminated 2026-08-04 into the proved-table definition
`TwistNormalForm.bgwComposite`, so no pin for it remains.) -/

/-- info: @Selection.aczel_continuous_multiplicative : ∀ {W : Type u_1} [inst : NormedAddCommGroup W] [inst_1 : NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [CompleteSpace W] (h : ℝ → W →L[ℝ] W),
  ContinuousOn h (Set.Ioi 0) →
    (∀ (x : ℝ), 0 < x → ∀ (y : ℝ), 0 < y → h (x * y) = h x * h y) →
      h 1 = 1 → ∃! A, ∀ (x : ℝ), 0 < x → h x = NormedSpace.exp (Real.log x • A) -/
#guard_msgs (whitespace := lax) in
#check @Selection.aczel_continuous_multiplicative

/-! ## Layer 5: S1--S7 interface type freezes

The seven paper axioms (S1, S3--S7), the effect-closure rider, the S2 predicate,
and the `IsEffect`/`Effect` boundary are the small surface whose *statements* must
not silently drift.  Each printed type is frozen here (parallel to the fidelity
pins and cited axioms); a change to any field's shape changes the printed type and
fails elaboration even if the build stays green.  `open SequentialProduct` so the
`&` sequential-product notation prints as it does in the source.  (The census in
Layer 1 already bounds every tracked persisted declaration's *axioms*; these freezes
lock the S1--S7 *shapes* against a source comparison drifting silently.) -/

open SequentialProduct

/-- info: @SequentialProductCore.sp_add_right : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b c : V},
  OrderUnitSpace.IsEffect a →
    OrderUnitSpace.IsEffect b → OrderUnitSpace.IsEffect c → b + c ≤ OrderUnitSpace.ousUnit → a & (b + c) = a & b + a & c -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.sp_add_right

/-- info: @SequentialProductCore.sp_unit_left : ∀ {V : Type u_1} [self : SequentialProductCore V] {a : V},
  OrderUnitSpace.IsEffect a → OrderUnitSpace.ousUnit & a = a -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.sp_unit_left

/-- info: @SequentialProductCore.sp_zero_symm : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b : V},
  OrderUnitSpace.IsEffect a → OrderUnitSpace.IsEffect b → a & b = 0 → b & a = 0 -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.sp_zero_symm

/-- info: @SequentialProductCore.sp_assoc_of_compatible : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b c : V},
  OrderUnitSpace.IsEffect a →
    OrderUnitSpace.IsEffect b → OrderUnitSpace.IsEffect c → a & b = b & a → a & (b & c) = a & b & c -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.sp_assoc_of_compatible

/-- info: @SequentialProductCore.compatible_ortho : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b : V},
  OrderUnitSpace.IsEffect a →
    OrderUnitSpace.IsEffect b → a & b = b & a → a & (OrderUnitSpace.ousUnit - b) = (OrderUnitSpace.ousUnit - b) & a -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.compatible_ortho

/-- info: @SequentialProductCore.compatible_add : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b c : V},
  OrderUnitSpace.IsEffect a →
    OrderUnitSpace.IsEffect b →
      OrderUnitSpace.IsEffect c →
        b + c ≤ OrderUnitSpace.ousUnit → a & b = b & a → a & c = c & a → a & (b + c) = (b + c) & a -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.compatible_add

/-- info: @SequentialProductCore.compatible_sp : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b c : V},
  OrderUnitSpace.IsEffect a →
    OrderUnitSpace.IsEffect b → OrderUnitSpace.IsEffect c → a & b = b & a → a & c = c & a → a & (b & c) = b & c & a -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.compatible_sp

/-- info: @SequentialProductCore.sp_effect : ∀ {V : Type u_1} [self : SequentialProductCore V] {a b : V},
  OrderUnitSpace.IsEffect a → OrderUnitSpace.IsEffect b → OrderUnitSpace.IsEffect (a & b) -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.sp_effect

/-- info: @FirstArgContinuous : {V : Type u_1} → [SequentialProductCore V] → Prop -/
#guard_msgs (whitespace := lax) in
#check @SequentialProduct.FirstArgContinuous

/-- info: @OrderUnitSpace.IsEffect : {V : Type u_1} → [OrderUnitSpace V] → V → Prop -/
#guard_msgs (whitespace := lax) in
#check @OrderUnitSpace.IsEffect

/-- info: PaperA.Effect : (V : Type u_1) → [OrderUnitSpace V] → Type u_1 -/
#guard_msgs (whitespace := lax) in
#check @PaperA.Effect

/-! ### Layer 5b: boundary *body* pins and class-constructor freezes

The type freezes above lock each definition's *outer* type but not its *body*:
`FirstArgContinuous : … → Prop` is unchanged by replacing its body with
`(…) ∧ False`, `IsEffect : … → V → Prop` is unchanged by a body drift, and
`PaperA.Effect : … → Type` is unchanged by an empty subtype.  The four `_body`
pins in `PaperA.AuditPins` state each body by `Iff.rfl`/`rfl`, and the four
exact type-freezes below make any silent edit of those pins visible.  The three
constructor freezes then close the last escape: because the tree constructs no
concrete full `SequentialProduct` instance, a hidden impossible extra field on
that class would pass every field/type guard, but it changes `SequentialProduct.mk`'s
printed type.  (A hidden field on `SequentialProductCore` is separately caught by
the concrete `SpinFactor` core instance failing to build; `SequentialProductCore.mk`
is frozen too for uniformity.)  The `_body` pins are also visited by the Layer-1
census and exact-closure guarded here. -/

/-- info: 'PaperA.auditPin_firstArgContinuous_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_firstArgContinuous_body

/-- info: 'PaperA.auditPin_isEffect_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_isEffect_body

/-- info: 'PaperA.auditPin_effect_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_effect_body

/-- info: 'PaperA.auditPin_effectProduct_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PaperA.auditPin_effectProduct_body

/-- info: @PaperA.auditPin_firstArgContinuous_body : ∀ {V : Type u_1} [inst : SequentialProductCore V],
  FirstArgContinuous ↔
    ∀ ⦃b : V⦄, OrderUnitSpace.IsEffect b → ContinuousOn (fun a => a & b) {a | OrderUnitSpace.IsEffect a} -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_firstArgContinuous_body

/-- info: @PaperA.auditPin_isEffect_body : ∀ {V : Type u_1} [inst : OrderUnitSpace V] (a : V),
  OrderUnitSpace.IsEffect a ↔ 0 ≤ a ∧ a ≤ OrderUnitSpace.ousUnit -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_isEffect_body

/-- info: PaperA.auditPin_effect_body : ∀ (V : Type u_1) [inst : OrderUnitSpace V],
  PaperA.Effect V = { a // OrderUnitSpace.IsEffect a } -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_effect_body

/-- info: PaperA.auditPin_effectProduct_body : ∀ (V : Type u_1) [inst : OrderUnitSpace V],
  PaperA.EffectProduct V = (PaperA.Effect V → PaperA.Effect V → PaperA.Effect V) -/
#guard_msgs (whitespace := lax) in
#check @PaperA.auditPin_effectProduct_body

-- Constructor freezes.  Under `open SequentialProduct` the full class constructor
-- `SequentialProduct.mk` prints as `@mk` and the S2 projection as `@sp_continuous_left`.
/-- info: @SequentialProductCore.mk : {V : Type u_1} →
  [toOrderUnitSpace : OrderUnitSpace V] →
    (sp : V → V → V) →
      (∀ {a b c : V},
          OrderUnitSpace.IsEffect a →
            OrderUnitSpace.IsEffect b →
              OrderUnitSpace.IsEffect c → b + c ≤ OrderUnitSpace.ousUnit → sp a (b + c) = sp a b + sp a c) →
        (∀ {a : V}, OrderUnitSpace.IsEffect a → sp OrderUnitSpace.ousUnit a = a) →
          (∀ {a b : V}, OrderUnitSpace.IsEffect a → OrderUnitSpace.IsEffect b → sp a b = 0 → sp b a = 0) →
            (∀ {a b c : V},
                OrderUnitSpace.IsEffect a →
                  OrderUnitSpace.IsEffect b →
                    OrderUnitSpace.IsEffect c → sp a b = sp b a → sp a (sp b c) = sp (sp a b) c) →
              (∀ {a b : V},
                  OrderUnitSpace.IsEffect a →
                    OrderUnitSpace.IsEffect b →
                      sp a b = sp b a → sp a (OrderUnitSpace.ousUnit - b) = sp (OrderUnitSpace.ousUnit - b) a) →
                (∀ {a b c : V},
                    OrderUnitSpace.IsEffect a →
                      OrderUnitSpace.IsEffect b →
                        OrderUnitSpace.IsEffect c →
                          b + c ≤ OrderUnitSpace.ousUnit →
                            sp a b = sp b a → sp a c = sp c a → sp a (b + c) = sp (b + c) a) →
                  (∀ {a b c : V},
                      OrderUnitSpace.IsEffect a →
                        OrderUnitSpace.IsEffect b →
                          OrderUnitSpace.IsEffect c →
                            sp a b = sp b a → sp a c = sp c a → sp a (sp b c) = sp (sp b c) a) →
                    (∀ {a b : V},
                        OrderUnitSpace.IsEffect a → OrderUnitSpace.IsEffect b → OrderUnitSpace.IsEffect (sp a b)) →
                      SequentialProductCore V -/
#guard_msgs (whitespace := lax) in
#check @SequentialProductCore.mk

/-- info: @mk : {V : Type u_1} →
  [toSequentialProductCore : SequentialProductCore V] → FirstArgContinuous → SequentialProduct V -/
#guard_msgs (whitespace := lax) in
#check @SequentialProduct.mk

/-- info: @sp_continuous_left : ∀ {V : Type u_1} [self : SequentialProduct V], FirstArgContinuous -/
#guard_msgs (whitespace := lax) in
#check @SequentialProduct.sp_continuous_left

/-! ### Layer 6: master-chain interface constructor freezes

The five interface structures of `THEOREM-MAP.md` §2 (`ComparisonSetup`,
`CoalescenceSetup`, `DiagonalHomSetup`, `StabilizerCoupling`, `IsAlbertModel`)
carry the cited imports as *fields*, so their constructor types ARE the import
ledger: a silently added, removed, or re-typed field changes the printed
constructor type and fails the corresponding freeze below.  Two escapes remain
outside a type-only freeze and are closed elsewhere: (i) a frozen constructor
names helper definitions opaquely — redefining a helper *body* (e.g.
`MasterTheorem.OpCommute` to `False`) leaves every printed type unchanged while
making fields unsatisfiable, so the skeleton would go vacuous silently; the
constructed witnesses in `RadicalRelativity.MasterTheorem.Witnesses` (visited by
the Layer-1 census) consume those bodies through real proofs, so that edit class
now fails the build there; (ii) no freeze speaks to the *truth* of the fields on
the intended EJA instances — the witnesses are explicitly degenerate, and
discharging the fields on the intended algebras is the formalization campaign
(`LEDGER.md`). -/

/-- info: @MasterTheorem.ComparisonSetup.mk : {J : Type u_1} →
  [inst : NormedAddCommGroup J] →
    [inst_1 : InnerProductSpace ℝ J] →
      (jordan : J →ₗ[ℝ] J →ₗ[ℝ] J) →
        (e : J) →
          (∀ (x y : J), (jordan x) y = (jordan y) x) →
            (∀ (x : J), (jordan e) x = x) →
              (n : ℕ) →
                3 ≤ n →
                  (p : Fin n → J) →
                    (nonneg Inv : J → Prop) →
                      (aOf : (Fin n → ℝ) → J) →
                        (∀ (r : Fin n → ℝ), Inv (aOf r)) →
                          (Θ : J → J ≃ₗ[ℝ] J) →
                            (∀ (a : J), Inv a → (Θ a) e = e) →
                              (∀ (a : J), Inv a → ∀ (x : J), nonneg x ↔ nonneg ((Θ a) x)) →
                                (∀ (a : J), Inv a → ∀ (x y : J), (Θ a) ((jordan x) y) = (jordan ((Θ a) x)) ((Θ a) y)) →
                                  (∀ (a : J), Inv a → ∀ (b : J), MasterTheorem.OpCommute jordan a b → (Θ a) b = b) →
                                    (∀ (r : Fin n → ℝ) (i : Fin n), MasterTheorem.OpCommute jordan (aOf r) (p i)) →
                                      (∀ (r r' : Fin n → ℝ),
                                          (∀ (i : Fin n), r i ≤ 0) →
                                            (∀ (i : Fin n), r' i ≤ 0) → Θ (aOf (r + r')) = Θ (aOf r) ≪≫ₗ Θ (aOf r')) →
                                        MasterTheorem.ComparisonSetup J -/
#guard_msgs (whitespace := lax) in
#check @MasterTheorem.ComparisonSetup.mk

/-- info: @MasterTheorem.StabilizerCoupling.mk : {n : ℕ} →
  {Stab : Type u_1} →
    [inst : AddCommGroup Stab] →
      [inst_1 : _root_.Module ℝ Stab] →
        {V : Type u_2} →
          [inst_2 : NormedAddCommGroup V] →
            [inst_3 : InnerProductSpace ℝ V] →
              (ρ : Fin n → Fin n → Stab →ₗ[ℝ] V →ₗ[ℝ] V) →
                (∀ (i j : Fin n) (ξ : Stab) (x : V), inner ℝ (((ρ i j) ξ) x) x = 0) →
                  (dχ : (Fin n → ℝ) →ₗ[ℝ] Stab) →
                    (T : Fin n → Fin n → V →ₗ[ℝ] V) →
                      (∀ (i j : Fin n) (r : Fin n → ℝ), (ρ i j) (dχ r) = (r i - r j) • T i j) →
                        3 ≤ n → MasterTheorem.StabilizerCoupling n Stab V -/
#guard_msgs (whitespace := lax) in
#check @MasterTheorem.StabilizerCoupling.mk

/-- info: @MasterTheorem.CoalescenceSetup.mk : {J : Type u_1} →
  [inst : NormedAddCommGroup J] →
    [inst_1 : InnerProductSpace ℝ J] →
      (toComparisonSetup : MasterTheorem.ComparisonSetup J) →
        (J2 ScalarOn : Fin toComparisonSetup.n → Fin toComparisonSetup.n → J → Prop) →
          (∀ (i j : Fin toComparisonSetup.n) (a b : J),
              ScalarOn i j a → J2 i j b → MasterTheorem.OpCommute toComparisonSetup.jordan a b) →
            (∀ (r : Fin toComparisonSetup.n → ℝ) (i j : Fin toComparisonSetup.n),
                r i = r j → ScalarOn i j (toComparisonSetup.aOf r)) →
              (∀ (i j : Fin toComparisonSetup.n) (x : J),
                  MasterTheorem.IsBlockElt toComparisonSetup.jordan toComparisonSetup.p i j x → J2 i j x) →
                MasterTheorem.CoalescenceSetup J -/
#guard_msgs (whitespace := lax) in
#check @MasterTheorem.CoalescenceSetup.mk

/-- info: @MasterTheorem.DiagonalHomSetup.mk : {J : Type u_1} →
  [inst : NormedAddCommGroup J] →
    [inst_1 : InnerProductSpace ℝ J] →
      {Stab : Type u_2} →
        [inst_2 : NormedAddCommGroup Stab] →
          [inst_3 : NormedSpace ℝ Stab] →
            {V : Type u_3} →
              [inst_4 : NormedAddCommGroup V] →
                [inst_5 : InnerProductSpace ℝ V] →
                  (toCoalescenceSetup : MasterTheorem.CoalescenceSetup J) →
                    (ρ : Fin toCoalescenceSetup.n → Fin toCoalescenceSetup.n → Stab →ₗ[ℝ] V →ₗ[ℝ] V) →
                      (∀ (i j : Fin toCoalescenceSetup.n) (ξ : Stab) (x : V), inner ℝ (((ρ i j) ξ) x) x = 0) →
                        (dχAdd : (Fin toCoalescenceSetup.n → ℝ) →+ Stab) →
                          Continuous ⇑dχAdd →
                            (∀ (i j : Fin toCoalescenceSetup.n) (r : Fin toCoalescenceSetup.n → ℝ),
                                r i = r j → (ρ i j) (dχAdd r) = 0) →
                              MasterTheorem.DiagonalHomSetup J Stab V -/
#guard_msgs (whitespace := lax) in
#check @MasterTheorem.DiagonalHomSetup.mk

/-- info: @MasterTheorem.IsAlbertModel.mk : ∀ {Stab : Type u_1} [inst : AddCommGroup Stab] [inst_1 : _root_.Module ℝ Stab]
  {V : Type u_2} [inst_2 : NormedAddCommGroup V] [inst_3 : InnerProductSpace ℝ V]
  {S : MasterTheorem.StabilizerCoupling 3 Stab V},
  (∀ (i j : Fin 3), i ≠ j → Function.Injective ⇑(S.ρ i j)) → MasterTheorem.IsAlbertModel S -/
#guard_msgs (whitespace := lax) in
#check @MasterTheorem.IsAlbertModel.mk
