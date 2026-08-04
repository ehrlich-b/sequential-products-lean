# Campaign discharge ledger — Paper A full verification

**Created 2026-08-04 (M0 design pass). Route:** `research/PAPER-A-LEAN-ROUTE.md`
(blog repo). **Division of labor:** `THEOREM-MAP.md` states what the tree IS
(the governing honesty ledger, updated every milestone); this file states what
REMAINS and how each item discharges. An item leaves this ledger only when
THEOREM-MAP's corresponding row moves to "machine-checked."

**Target restated:** zero-sorry per-type proofs of `mthm:master`
(H_n(ℝ), H_n(ℂ) n≥3, H_n(ℍ), H₃(𝕆)), `cor:qubit-classification`,
`mthm:omnibus`; closure = Lean core + at most JvNW as disclosed import; every §2
interface structure instantiated on the intended algebras.

**M0 status (day 1, complete by evening):** witnesses for all five interface
structures constructed (`MasterTheorem/Witnesses.lean`) and audit Layer 6
(interface constructor freezes) added — six-layer audit green at 27 modules.
Albert import expected to DISCHARGE via the unit-slot argument
(`ALBERT-KERNEL-MEMO.md`), demoting the route file's "6–12 months with Albert"
to the 3–5 month track. Mathlib inventory COMPLETE (all areas, v4.28.0-era
checkout) — [INV✓] markers below are settled; see H5 for the scoping gotcha
that cost the most to discover. Landscape check COMPLETE: Nuccio lead DEAD
(his "octonions" repo is a mathlib mirror by that name); live octonions effort
= mathlib4 PR #41919 (Cayley-Dickson, defers alternativity, no Albert — do not
wait for it); EJA/Peirce/Kadison/FTPG/effect-algebras are greenfield in EVERY
prover. WILDCARD: `zblore/csd-lean4` (Apache-2.0, solo, CI green) claims a
sorry-free Wigner rigidity — see 3.0.

---

## M1 — Complex sufficiency (twists satisfy S1–S7 on H_n(ℂ))

- **1.1 Carrier + instances.** `Matrix.IsHermitian` subtype (or selfAdjoint
  submodule) as the order unit space; Loewner order; effects. [INV✓]:
  `Matrix.PosSemidef` API full (incl. `PosSemidef.sqrt := CFC.sqrt` with
  uniqueness `sqrt_unique`/`eq_sqrt_iff_sq_eq`); Loewner order + StarOrderedRing
  EXIST but SCOPED — `open scoped MatrixOrder` mandatory (H5). No Jordan product
  on `selfAdjoint A` anywhere; HARVEST: physlib `HermitianMat` + its
  `Jordan.lean` `symmMul` (leanprover-community/physlib, active 2026-08) is the
  closest existing special-EJA substrate — evaluate as pattern source or
  dependency before hand-building the carrier. Risk LOW.
- **1.2 Twist definition.** `a^{1/2+it} b a^{1/2-it}` via CFC. [INV✓]: matrix
  CFC instance is `Matrix.IsHermitian.instContinuousFunctionalCalculus` (over ℝ,
  predicate `IsSelfAdjoint`, real file `Analysis/Matrix/
  HermitianFunctionalCalculus.lean` — the LinearAlgebra path is a deprecated
  stub); **NO cpow for positive elements exists** (only `CFC.rpow`/`nnrpow`/
  `sqrt`). Two routes for the complex power: (a) pair-of-real-cfc,
  `a^{1/2+it} := hA.cfc (x^{1/2}cos(t log x)) + i·hA.cfc (x^{1/2}sin(t log x))`
  — identities become manual but bonus applies: `hA.cfc_eq` carries NO
  continuity hypothesis (finite spectrum), so 0-eigenvalue conventions are
  free; (b) `CStarMatrix` type copy + the ℂ-CFC over `IsStarNormal`. Pick at M1
  start. Risk MED (was LOW-MED; the gap is confirmed, the routes are clear).
- **1.3 S1–S7 verification.** [INV✓]: cfc identity suite is rich (`cfc_mul`,
  `cfc_comp'`, `cfc_pow`, order lemmas `cfc_mono`/`cfc_le_iff`, commutation
  `Commute.cfc`, norms `norm_cfc`). The SymPy V1–V10 checks are the
  computational shadow; each becomes a lemma. Risk LOW, volume moderate.
- **1.4 (S2) norm caveat discharge.** Prove order-unit norm ≡ carried norm on
  the finite-dim instance (all norms equivalent, Mathlib has finite-dim
  equivalence) — closes THEOREM-MAP's S2 literal-fidelity caveat. Risk LOW.

## M2 — Complex necessity core

- **2.1 Θ construction (vdW Prop 5.2/5.3).** Define `Θ_a := Q_{√a}⁻¹ ∘ L_a` on
  invertible effects; prove unital linear order-iso. Matrix-concrete. Risk MED.
- **2.2 Θ_fix (vdW 5.5) + span extension.** Effect-level fixing + extension to
  J by linearity (the span argument the paper supplies). Risk MED.
- **2.3 cone-ext (Θ_{λq} = Θ_q normalization).** Cheap once 2.1 lands. LOW.
- **2.4 Θ_cocycle (vdW 5.7, commuting diagonal family).** Matrix-concrete
  computation in the joint eigenbasis. Risk MED.
- **2.5 frame_opCommute + simDiag_opCommute (FK facts).** Direct block-form
  computations on matrices. LOW.
- **2.6 THE ANALYTIC CORE: dχAdd + continuity + coalescence_diff.** Construct
  the character χ̃ from Θ on the orthant (group-level pieces `chi_hom`,
  `chi_comm`, `chi_extend_wellDefined` already proved), extend to ℝⁿ,
  differentiate. Continuous-additive⟹linear is PRESENT
  (`AddMonoidHom.toRealLinearMap` [INV✓]); the differentiation/smoothing of χ̃
  itself is bespoke analysis — the single largest M2 line-count risk. Risk
  HIGH (budget, not feasibility).
- **2.7 Aczél axiom DISCHARGE (`Selection.aczel_continuous_multiplicative`).**
  Scalar Cauchy machinery present [INV✓ area 7a]; multiplicative classification
  absent [INV✓ 7d — build it]: continuous hom (0,∞)→ℂ* via log/exp covering
  (Complex.isCoveringMap_exp [INV✓]) reduction to additive case. Operator-valued
  form [INV✓ area 6]: NO one-parameter-group theory exists anywhere in Mathlib
  (no Stone, no "continuous hom ℝ → GL is exp(tA)", zero generator-extraction);
  raw material = `hasDerivAt_exp_smul_const` + the local unitary log
  `Unitary.argSelfAdjoint` (`Analysis/CStarAlgebra/Unitary/Connected.lean`).
  Precedent: PR #33813 (Cauchy-log characterization) was closed unmerged
  2026-01 — build in-repo, harvest to Mathlib later (T4). ~200–350 lines
  estimate stands, lean high. Risk MED.
- **2.8 `bgw_canonical_composite` ELIMINATION — DONE 2026-08-04.** Replaced the
  axiom (a constructible existence claim, hence not falsifiable) with the
  pattern-match definition `bgwComposite` + `rfl`-proved `bgwComposite_table`;
  non-matrix rows = documented junk-total `.real 0`, consumed nowhere. Audit
  updated (allowlist + citedAxioms to one, Layer-4 bgw pin removed, docstrings);
  README / THEOREM-MAP §2 / NormalFormExistence / Interface docstrings updated.
  **Custom-axiom count: 2 → 1** (Aczél alone); → 0 after 2.7.
- **2.9 prop:singular (singular-effect extension).** Boundary continuity
  argument; standalone lemma exists but is unwired. Risk MED, tail item.

## M3 — THE BOULDER: Θ_jordan (Kadison/vIR rigidity)

- **3.0 DUE DILIGENCE: DONE 2026-08-04 — VERDICT CLEAN.** Built
  `zblore/csd-lean4`'s `WignerRigidity` module from source (2588 jobs, green);
  `#print axioms Projectivization.wigner_rigidity` (and
  `wigner_rigidity_unitaryGroup`) = **[propext, Classical.choice, Quot.sound]
  exactly** — the transitive proof tree contains no custom axiom, no sorry, no
  native_decide, which clears every claim-shaped-placeholder concern for THIS
  theorem regardless of the repo's other layers. Statement fidelity verified
  at the definition level: `TransProbPreserving f = ∀ p q, transProb (f p)
  (f q) = transProb p q` with `transProbVec ψ φ = ‖⟪ψ,φ⟫_ℂ‖²/(‖ψ‖²·‖φ‖²)`
  (genuine Fubini–Study), conclusion the honest unitary/antiunitary dichotomy
  (`e : ≃ₗᵢ[ℂ]`, `conjProj` = standard-basis conjugation), NO surjectivity
  hypothesis needed. **Vendor surface** (Apache-2.0, files self-labeled
  "1-Mathlib, CSD-free upstream candidates" under `namespace Projectivization`):
  8 files ≈ 4.8kL — WignerRigidity ← TransitionProbability ← FubiniStudy ←
  {Unitary, MeasureSpace, Matrix/UnitaryHaar} ← {Topology, Matrix/
  UnitaryCompact}. Caveat: written in the NEW module system (`module` +
  `public import` + `@[expose] public section`, toolchain v4.33.0-rc1) — our
  tree is v4.28.0, so either (i) bump our toolchain+mathlib (whole-tree
  re-elaboration risk) or (ii) mechanical backport (strip module keywords,
  absorb Mathlib API drift). Decide at M3 start. Their `EffectGleason.lean`
  (Busch, de-axiomatized per their AXIOMS.md) remains UNAUDITED — same audit
  procedure before ever citing it.
- **3.1** Unital order-autos of H_n(ℂ)sa are Jordan autos, matrix-concrete,
  n ≥ 3. No prover has Kadison/Uhlhorn/FTPG (landscape-confirmed 08-04:
  Magaud/Narboux Coq and AFP Projective_Geometry are incidence-axiomatic only,
  no coordinatization). **Route A (if 3.0 audits clean):** (i) bridge 1 —
  order-auto Φ preserves extreme effects ⟹ maps rank-1 projections to rank-1
  projections; NOTE [INV✓ area 5]: "extreme points of [0,I] = projections" is
  FROM SCRATCH (Mathlib has `IsStarProjection`, generic `extremePoints`,
  `CStarAlgebra.mem_Icc_iff_norm_le_one`, and NOTHING joining them); (ii)
  bridge 2 — Φ preserves transition probabilities via the Busch–Gudder strength
  function: λ(p, a) = sup{t : t·p ≤ a} is order-definable, and for rank-1 p
  the family a = q + ε(1−q) gives λ = ε/(ε·τ + (1−τ)) with τ = tr(pq), so a
  unital LINEAR order-iso preserves τ (matrix-concrete PSD computation); (iii)
  apply `wigner_rigidity` to the induced ray map; (iv) unitary/antiunitary ⟹
  Jordan auto (both branches: conjugation and transpose-conjugation preserve
  the symmetrized product). **Route B (fallback, original):** coordinates
  Uhlhorn from orthogonality alone — build the unitary column-by-column, phase
  gauge, antiunitary casework. Risk: **MED (was HIGH)** — 3.0 audited clean, so
  M3 = extreme-effects-are-projections + the strength-function bridge + the
  vendor/backport of an already-machine-checked rigidity theorem; Route B and
  the disclosed-axiom exit remain pre-registered fallbacks.

## M4 — Real + quaternionic branches

- **4.1 Real.** Rides M2 machinery over ℝ; discreteness kill (characters into
  O(1) trivial — `real_character_unique` pattern already proved). Risk LOW.
- **4.2 Quaternionic.** H_n(ℍ) ↪ H_{2n}(ℂ) symplectic embedding. [INV✓ area
  10]: ℍ itself is well-developed (NormedDivisionRing, CStarRing,
  InnerProductSpace ℝ) but **matrices over ℍ are total greenfield — zero
  declarations — and ℍ is not RCLike, so NONE of the areas-1-4 matrix stack
  applies to H_n(ℍ) directly.** The embedding route is therefore the only
  route: everything happens in the J-invariant complex picture
  (`LinearAlgebra/SymplecticGroup.lean` has `Matrix.J`, `J_squared`,
  `symplecticGroup` — isolated but present) and transports back through an
  explicit ℝ-linear iso. Risk MED, estimate leans to the high end of +1-2mo.

## M5 — Rank-two classification (parallelizable with M2–M4)

- **5.1 Lifting step (lem in prop:n2-necessity).** Continuous hom ℝ² → SO(2)
  lifts to a linear functional. ALL ingredients present [INV✓ area 8]:
  `Circle.isCoveringMap_exp`, `existsUnique_continuousMap_lifts` (simply
  connected + loc path-conn domain, Hatcher 1.33), hom-normalization via
  ker exp = 2πℤ discreteness, then `AddMonoidHom.toRealLinearMap`. Risk LOW
  (was MED pre-inventory).
- **5.2 ℝP² + descent (lem:n2-bounded/continuity/descent).** ℝP² absent from
  Mathlib in any form [INV✓ area 9]; build S²/± via orbit-quotient machinery
  (complete: ProperlyDiscontinuous free for finite Γ, T2, open quotient,
  compactness inherit [INV✓]). Two small genuine gaps to write: MulAction of a
  2-element group packaging `InvolutiveNeg`/`ContinuousNeg` on the sphere, and
  the `Function.Even → Function.FactorsThrough` bridge; then
  `IsQuotientMap.liftEquiv` gives C(ℝP²,ℝ) ↔ even C(S²,ℝ) [INV✓]. HARVEST
  option (08-04): csd-lean4's `Projectivization/Topology.lean` (466L, general
  `[DivisionRing K]`, Mathlib-staged, inside the audited 3.0 vendor closure)
  gives `ℙ ℝ ℝ³` a quotient topology directly — evaluate using it as the ℝP²
  carrier instead of a bespoke sphere quotient. Risk MED (volume), no unknowns.
- **5.3 Assembly (cor:qubit-classification).** Bijection between the M₂(ℂ)
  algebraic core (sp_blockForm etc., already proved) and the parameter space.
  Risk MED.

## M6 — Albert branch

- **6.1 block_injective discharge.** See `ALBERT-KERNEL-MEMO.md`: unit-slot
  argument (elementary; inputs = matrix-unit identities (I)/(II), Peirce
  bookkeeping (P1)/(P2), nucleus(𝕆) = ℝ finite check). Fallbacks: 128-unknown
  kernel certificate; disclosed axiom. Risk MED (was HIGH; validity verified at
  sketch level in the standard convention — re-derive (I)/(II) in the chosen
  model). Weeks, not months.
- **6.2 H₃(𝕆) construction.** On the existing octonion formalization
  (`~/repos/research/lean/Octonions.lean`, 0 sorries). Landscape-settled
  08-04: the "Nuccio octonions WIP" lead is DEAD (a mathlib mirror named
  "octonions", last activity 2023; zero octonion PRs by him); the live effort
  is mathlib4 PR #41919 (junjihashimoto, Cayley-Dickson tower, explicitly
  defers alternativity and the multiplicative norm, no Jordan/Albert,
  awaiting-author) — track it for eventual T4 alignment, do NOT wait for it.
  Only other prover artifact: Isabelle AFP `Octonions` (2018). Bryan's
  Octonions.lean is the mainline foundation. Risk MED.
- **6.3 Albert-instance analytic data.** Θ/dχ/ρ on H₃(𝕆) = M2 machinery
  specialized (rank exactly 3, no globalization needed). Risk MED-HIGH,
  shared shape with 2.6.

## M7 — Omnibus + statement upgrade + re-audit

- **7.1 mthm:omnibus.** Direct-sum assembly; summand inheritance of S1–S7 +
  converse (the documented paper-only halves of prop:central). Risk LOW-MED.
- **7.2 prop:pseudo-transfer.** Small. Risk LOW.
- **7.3 Statement upgrade.** Replace the skeleton capstone with concrete
  per-type theorems; rewrite `PaperA/Statement.lean`, AuditPins, THEOREM-MAP,
  README, paper §App + disclosure paragraph to the certified configuration.
- **7.4 Full audit re-elaboration** at every milestone boundary, not just M7
  (`lake env lean AxiomAudit.lean`; never truncate its output — tail-truncation
  hid a real failure on 2026-08-04 day 1).

## Cross-cutting / hygiene

- **H1. Stale `PLAN.md` references.** Interface/Coalescence docstrings cite a
  `PLAN.md` that does not exist in this repo (predates the public deposit).
  Point them at `THEOREM-MAP.md` + this ledger. ~30 min.
- **H2. Interface evolution discipline.** Any field change during instantiation
  work must update: the structure, Layer-6 freeze, witnesses, THEOREM-MAP §2,
  this ledger — in one commit.
- **H3. No `native_decide` anywhere** (audit census rejects it); certificates
  must be kernel-`decide` scale or structured proofs.
- **H4. Audit-your-own-corrections:** diff-audit every round; verify verifiers
  saw data (print counts; no `| head` on gate output).
- **H5. Scoped-instance gotcha (the costliest inventory discovery).** The
  Loewner order + `StarOrderedRing` on `Matrix` require `open scoped
  MatrixOrder` (`Analysis/Matrix/Order.lean`); the matrix C*-norm requires
  `open scoped Matrix.Norms.L2Operator` (or use the `CStarMatrix` type copy,
  which carries the instances globally). Neither is discoverable from
  declaration names. Also: `LinearAlgebra/Matrix/HermitianFunctionalCalculus
  .lean` is a deprecated stub — the real module is
  `Analysis/Matrix/HermitianFunctionalCalculus.lean`. Put the `open scoped`
  lines in every M1/M2 file header from day one.
