import RadicalRelativity

open Lean System

/-! # Axiom census, closure allowlist, coverage, and statement-fidelity gates

Four layers, all enforced by elaborating this file
(`lake env lean AxiomAudit.lean`):

1. a **project-wide census** — over every declaration defined in a
   `RadicalRelativity.*` module it enforces three things at once:
   (a) the axiom closure depends only on Lean's three core axioms
   (`propext`, `Classical.choice`, `Quot.sound`) and the two disclosed
   cited-literature axioms (`Selection.aczel_continuous_multiplicative`,
   `TwistNormalForm.bgw_canonical_composite`) — a `sorryAx`, `native_decide`,
   or any other axiom fails elaboration; (b) those two are the *only* custom
   axiom declarations in the project — a new stray `axiom` anywhere fails; and
   (c) **source coverage**: the set of `RadicalRelativity` modules on disk
   equals the set imported here, so a new unimported module or a removed root
   import fails, closing the "invisible module" escape;
2. **exact-closure sentinels** — one principal advertised result per module
   family, each pinned by `#guard_msgs` to *exactly* the three core axioms
   (i.e. not even the two cited axioms enter these cones);
3. **statement-fidelity pins** — the public S2 predicate, the two product-level
   conclusion shapes, and the effect-level product, are named, persisted
   theorems in `RadicalRelativity.PaperA.AuditPins` (so the census in Layer 1
   visits them: a `sorry` or stray axiom substituted for a pin's direct proof
   fails the census); here each is additionally exact-closure guarded;
4. **cited-axiom type pins** — the exact printed types of the two custom axioms
   are frozen by `#guard_msgs`, so a silent statement drift under either name
   fails.
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

-- Layer 1: project-wide census (closure allowlist + custom-axiom set + coverage).
run_cmd do
  let env ← getEnv
  let allowed : List Name :=
    [``propext, ``Classical.choice, ``Quot.sound,
     ``Selection.aczel_continuous_multiplicative,
     ``TwistNormalForm.bgw_canonical_composite]
  let citedAxioms : List Name :=
    [``Selection.aczel_continuous_multiplicative,
     ``TwistNormalForm.bgw_canonical_composite]
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
    throwError m!"Project-wide axiom census FAILED. Unpermitted axioms: {bad}. Offending declarations: {offenders}"
  -- (b) exactly the two disclosed custom axioms exist.
  let unexpectedAx := projectAxiomDecls.toList.filter (fun a => !citedAxioms.contains a)
  let missingAx := citedAxioms.filter (fun a => !projectAxiomDecls.contains a)
  if !unexpectedAx.isEmpty || !missingAx.isEmpty then
    throwError m!"Custom-axiom set drift. Unexpected project axioms: {unexpectedAx}. Missing disclosed axioms: {missingAx}"
  -- (c) source coverage: disk `RadicalRelativity` modules == imported ones.
  let rrDir : FilePath := "RadicalRelativity"
  unless (← rrDir.isDir) do
    throwError m!"Module-coverage gate: run from the package root ('RadicalRelativity/' not found in the current directory)"
  let files ← auditCollectLeanFiles rrDir
  let diskMods : List Name := (`RadicalRelativity :: files.toList.map auditPathToModule).eraseDups
  let importedMods : List Name :=
    (env.header.moduleNames.toList.filter (fun m => (`RadicalRelativity).isPrefixOf m)).eraseDups
  let onlyDisk := diskMods.filter (fun m => !importedMods.contains m)
  let onlyImported := importedMods.filter (fun m => !diskMods.contains m)
  if !onlyDisk.isEmpty || !onlyImported.isEmpty then
    throwError m!"Module-coverage gate FAILED. On disk but not imported (unimported source): {onlyDisk}. Imported but absent from disk (removed source / stale build): {onlyImported}"
  logInfo m!"Census PASS: {diskMods.length} RadicalRelativity modules, custom axioms exactly {citedAxioms}, every declaration's closure ⊆ {allowed}"

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

The four fidelity statements are named, persisted theorems in
`RadicalRelativity.PaperA.AuditPins` (visited by the Layer 1 census).  Each is
additionally exact-closure guarded below, so a pin proof weakened to `sorry` or
a stray axiom fails both the census and its sentinel. -/

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

/-! ## Layer 4: cited-axiom type pins

The exact printed type of each disclosed custom axiom is frozen.  A silent
statement drift under either allowlisted name changes the printed type and fails
elaboration.  (Fidelity to Aczel and to Barnum-Graydon-Wilce remains a human
citation audit, as the paper states.) -/

/-- info: @Selection.aczel_continuous_multiplicative : ∀ {W : Type u_1} [inst : NormedAddCommGroup W] [inst_1 : NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [CompleteSpace W] (h : ℝ → W →L[ℝ] W),
  ContinuousOn h (Set.Ioi 0) →
    (∀ (x : ℝ), 0 < x → ∀ (y : ℝ), 0 < y → h (x * y) = h x * h y) →
      h 1 = 1 → ∃! A, ∀ (x : ℝ), 0 < x → h x = NormedSpace.exp (Real.log x • A) -/
#guard_msgs (whitespace := lax) in
#check @Selection.aczel_continuous_multiplicative

/-- info: TwistNormalForm.bgw_canonical_composite : { comp //
  (∀ (m n : ℕ),
      comp (LocalTomography.EJAType.real m) (LocalTomography.EJAType.real n) = LocalTomography.EJAType.real (m * n)) ∧
    (∀ (m n : ℕ),
        comp (LocalTomography.EJAType.real m) (LocalTomography.EJAType.complex n) =
          LocalTomography.EJAType.complex (m * n)) ∧
      (∀ (m n : ℕ),
          comp (LocalTomography.EJAType.real m) (LocalTomography.EJAType.quatern n) =
            LocalTomography.EJAType.quatern (m * n)) ∧
        (∀ (m n : ℕ),
            comp (LocalTomography.EJAType.complex m) (LocalTomography.EJAType.real n) =
              LocalTomography.EJAType.complex (m * n)) ∧
          (∀ (m n : ℕ),
              comp (LocalTomography.EJAType.complex m) (LocalTomography.EJAType.complex n) =
                LocalTomography.EJAType.complex (m * n)) ∧
            (∀ (m n : ℕ),
                comp (LocalTomography.EJAType.complex m) (LocalTomography.EJAType.quatern n) =
                  LocalTomography.EJAType.complex (2 * m * n)) ∧
              (∀ (m n : ℕ),
                  comp (LocalTomography.EJAType.quatern m) (LocalTomography.EJAType.real n) =
                    LocalTomography.EJAType.quatern (m * n)) ∧
                (∀ (m n : ℕ),
                    comp (LocalTomography.EJAType.quatern m) (LocalTomography.EJAType.complex n) =
                      LocalTomography.EJAType.complex (2 * m * n)) ∧
                  ∀ (m n : ℕ),
                    comp (LocalTomography.EJAType.quatern m) (LocalTomography.EJAType.quatern n) =
                      LocalTomography.EJAType.real (4 * m * n) } -/
#guard_msgs (whitespace := lax) in
#check @TwistNormalForm.bgw_canonical_composite
