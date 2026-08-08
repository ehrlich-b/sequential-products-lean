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

---

## ★★ ARC-4 RESULT (2026-08-08) — **the asset is truthful, sharper, and PR-staged. All six items landed.**

Gates at the end of the arc: `lake build` green at **3106 jobs**; `AxiomAudit.lean`
PASS at **149 tracked modules** (== frozen 149-name manifest); **custom axioms exactly
`[]`**; every tracked persisted declaration's closure ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}. All commits LOCAL. Frozen review tag `paperA-arc4-review`.

Commits: `8727fff` (4.1) · `0d2fec9` (4.2) · `3f89c8f` (4.3) · `7cdf690` (4.4) ·
blog `fb65b07` (4.5).

**4.1 Truth sweep — DONE, and it found more than the orders listed.** Six stale
docstrings, not four: the four named plus `RealRigidity.lean:209` ("real Kadison being
unavailable in any prover") and `RealProjectionOrder.lean:29` ("the two-case argument is
the remaining step" — it is `rankOneR_isAtom`, in the same file), plus the root import
comment calling `prop:real` "in progress", plus `THEOREM-MAP.md`'s own real-row preamble,
which said the ℝ Jordan property is "carried, not derived" while its own table two lines
below said the row is unconditional. **`RealWigner.lean` de-vendored** to
`RadicalRelativity/Wigner/RealWigner.lean`; its `Vendor.Wigner.TransitionProbability`
import was dropped and replaced by two Mathlib imports, confirming the audit's
declaration-level finding that the import was dead. README now has a provenance section
naming Meiburg / Lessa / Blore with upstream pins and line counts (41,135 total, 12,409
vendored), a directory-level completion of the module map (the old map listed ~25 of 147
modules), and `master_chain` is billed as an abstract skeleton rather than a capstone.
`VENDOR.md`'s stale "one disclosed axiom" / census-44 lines are annotated, not rewritten.

**4.2 S2 order-unit-norm bridge — DONE, and it closed the caveat for the necessity
direction, not just for sufficiency.** New module `Necessity/OrderUnitS2.lean`. The
insight that made it tractable: `ContinuousOn` *cannot* express order-unit-norm continuity,
because the carrier has exactly one `TopologicalSpace` instance and it is the Frobenius
one — so the paper's S2 has to be written out in ε–δ form against `ouNorm` on both sides
(`HermitianMat.ContinuousOnOu`) and proved equivalent
(`continuousOnOu_iff_continuousOn`, from the two-sided sandwich, one ε-rescaling in each
direction). `abs_eigenvalues_le_ouNorm` and `norm_le_sqrt_card_mul_ouNorm` were ℂ-only
and are now `RCLike 𝕜`-general (one-token change; they never used ℂ). Both rows are
restated with the paper's S2 verbatim: `real_classification_ouNorm`,
`complex_classification_unconditional_ouNorm`, both Lean-core.
`twistProductOn_firstArgContinuousOu` pins the hypothesis class inhabited.

**4.3 Kadison classifications EXPOSED — DONE, and the ℝ one is EXACT.**
* ℝ: `orderAutoR_eq_orthConj` — every unital order-automorphism of `H_N(ℝ)` **is** `Ad_O`
  for an orthogonal `O`. `orderAutoR_preservesJordan` is now a two-line corollary of it.
  **Plus the converse** (`orthConj_le_iff`, `orthConj_one`, `orthConj_surjective`,
  packaged as `orthConj_orderAuto`), so the order-automorphism group of `H_N(ℝ)` is
  characterized as exactly `{Ad_O : OᵀO = 1}`, not merely embedded in it.
* ℂ: `orderAuto_classification` — `∃ U, UᴴU = 1 ∧ (Φ = Ad_U ∨ Φ = Ad_U ∘ ᵗ)`. Landed by
  extracting the rank-one agreement each Wigner branch already established
  (`agrees_unitaryConj_of_rayMap_eq_projMap`,
  `agrees_antiunitaryConj_of_rayMap_eq_projMap_conj`) and drawing *two* conclusions from
  it instead of one. No proof was weakened: the old `preservesJordan_of_*` theorems are
  now one-liners over the extracted lemmas.
* **BOTH classifications are EXACT** (`orthConj_orderAuto` over ℝ;
  `unitaryConj_orderAuto` + `antiunitaryConj_orderAuto` + `orderAuto_classification_realized`
  over ℂ), so each order-automorphism group is *characterized*, not merely embedded.
  ★ **The ℂ antiunitary converse landed only because the cold review refuted me.** I wrote
  that it was blocked on a "`PosSemidef`-under-transpose lemma Mathlib does not have"; the
  reviewer grep-checked and produced a compiling proof — `Matrix.posSemidef_transpose_iff`
  is in Mathlib (`LinearAlgebra/Matrix/PosDef.lean:91`) and the branch follows in a dozen
  lines. **Lesson, now binding: a claimed library obstruction is a claim. Grep the library
  before writing "Mathlib does not have X" into a docstring** — the cost of being wrong is
  that real work gets deferred as impossible.

**4.4 Real-Wigner Mathlib PR package — STAGED in `upstream/`, NOT SUBMITTED.**
`upstream/Wigner.lean` (Mathlib naming, Mathlib-shaped docstring, Mathlib license header)
compiles with **zero warnings under `-Dlinter.mathlibStandardSet=true`**; the `longLine`
suppression turned out to be vestigial (no line exceeds 100 *characters* — the earlier
count was bytes). Verified by diff that the PR copy and the in-tree twin differ only in the
capstone docstring. `upstream/README.md` records the collision check with evidence:
**Mathlib master has no Wigner's theorem and no Uhlhorn in any field** (the one `wigner`
hit is the unformalized *Wigner–Eckart* wishlist entry in `docs/1000.yaml`), `zblore/csd-lean4`
is ℂ-only with no real track in its backlog, `physlib` has nothing. Best argument for the
PR, found while checking: **the real case needs no missing Mathlib prerequisites** — it
imports `Analysis.InnerProductSpace.PiL2` and `LinearAlgebra.Projectivization.Basic` and
nothing else, where the ℂ case needs projective topology plus Fubini–Study measure theory.
Pre-submission list (rebase onto master; add `wigner1959`/`uhlhorn1963` to
`docs/references.bib`, which currently has neither; agree the file path; contact the ℂ
author) is in that README. `upstream/` is outside the census and outside `lake build` by
construction, and says so.

**4.5 Supplementary rewrite DRAFT — DONE**, blog `research/paperA-supplementary-rewrite-draft.md`.
Manuscript untouched. **The 5/17/14 coverage split was re-derived independently and agrees
with the 08-08 audit exactly** (36 = the 43 numbered environments minus 7 `remark`s, which
share the theorem counter): formalized = `prop:real`, `thm:complex`, `prop:per-frame`,
`prop:singular`, `lem:twist-sufficiency`. Both flagship rows are FORMALIZED **at the
article's own generality** — verified at source: the article states `prop:real` on
`H_n(ℝ)`, `n ≥ 2` (Lean: `0 < N`) and `thm:complex` on `H_n(ℂ)`, `n ≥ 3` (Lean: `3 ≤ N`).
The draft itemizes eight stale/false disclosure claims with line numbers, the five fidelity
caveats, and the re-pin off `b7db3e8`.

**Banked follow-ups (small, ordinary, not blocking anything):**
1. `AdjAxis` non-vacuity is asserted in a docstring but is not a theorem of the tree. The
   arc-3 reviewer proved `¬ AdjAxis 1 cycU` in a scratch file; making that an in-tree lemma
   would turn the last load-bearing prose assertion in the ℂ row's story into a proof.
2. ~~The ℂ antiunitary converse~~ — **CLOSED 2026-08-08** by the cold review's refutation;
   see 4.3 above. Left listed so the correction is visible, not silently dropped.
3. `THEOREM-MAP.md` cites only 20 of the paper's 36 labels; 4 more have Lean counterparts
   under unlabelled names (`lem:frame-fix`, `lem:coalescence`, `lem:homog`, `prop:bridge`
   appear in `.lean` docstrings but not in the map). Adding those rows would make the map's
   own coverage match the tree's.
4. `upstream/` and the in-tree twin are two copies of one proof with nothing enforcing
   sync; regeneration is five `sed` substitutions, recorded in `upstream/README.md`.

---

## ★★ ARC-4 ORDERS (2026-08-08, Fable handoff — Bryan funded a second 18h Opus arc)

**Provenance.** Tri-agent adversarial audit 2026-08-08 (isolated cold agents:
coverage, upstream, holistic skeptic; all reviewed frozen `ba317b8`; key claims
re-verified at source by the orchestrator). Verdicts that bind this arc:

- **"Fully formalized" is FALSE and must never appear in prose: 5 of 36
  numbered results in main.tex FORMALIZED, 17 PARTIAL, 14 ABSENT.** What IS
  banked survived a hostile audit untouched: both flagship rows unconditional,
  Lean-core closure re-verified by the auditor's own scratch probes, zero live
  sorry, zero axiom declarations tree-wide.
- **The campaign's original target (this file's "Target restated," all four
  rows + omnibus) is SUPERSEDED — unreachable on any controlled timeline**
  (ℍ needs quaternionic Wigner, 𝕆 needs octonions; neither exists in any
  prover). No new rows. Marginal Lean toward the old target ≈ 0.
- **Every disclosure surface understates the tree** (paper pins `b7db3e8` =
  07-19 skeleton, 27 files; supplementary claims two `axiom` declarations that
  are now theorems). All overstatement risk is internal; all public staleness
  is in the understating direction.
- **Upstream: one clear YES (real Wigner, S-friction), real Kadison behind it
  (M).** A third of the tree (12,409 L) is Meiburg's/Blore's, both already on
  their own Mathlib tracks — not ours to PR. ITP/CPP paper: skip.

**ARC-4 GOAL: convert the verified asset into a truthful, sharper, ship-ready
one.** Six items, in order. All commits LOCAL. Outward actions (push, PR
submission, manuscript edits, sync.sh) remain Bryan-gated and OUT OF SCOPE.

### 4.1 Truth sweep (docs only; ~3h)
- `Vendor/Wigner/RealWigner.lean:14-33` — header still says the rigidity is
  unproved and needs a bijection; the file proves the full theorem at :1041
  with no bijectivity hypothesis. Rewrite.
- `Necessity/RealRigidity.lean:35-38` — "real Kadison/Uhlhorn is not available
  in any prover" is FALSE in this tree (`RealKadison.orderAutoR_preservesJordan`,
  discharged into the row via `RealRowUnconditional.thetaPreservesJordanR_of_S2`).
- `MasterTheorem/Interface.lean:195` — "no concrete instance is constructed in
  this tree" is FALSE since `Necessity.comparisonSetup`
  (`ComparisonInstance.lean:363`, 08-05).
- `THEOREM-MAP.md:~380-395` — the n2-descent entry contradicts its own ★ note:
  descent is machine-checked for the CONCRETE Bloch example only; the
  classification map does not exist (`grep -c SequentialProductOn RankTwo/*.lean`
  = 0 across all seven files, verified). Make the ★ note's reading govern the row.
- `README.md` — add a Vendor/provenance section pointing at
  `RadicalRelativity/Vendor/VENDOR.md` and naming Meiburg (physlib @ `ad1d812`),
  Blore (csd-lean4 @ `2287f45`), Lessa (`Proj.lean`); grep for any residual
  "capstone" billing of `master_chain` and align with THEOREM-MAP §3.
- `Vendor/VENDOR.md:31-45` — "the one disclosed axiom" / census-44 lines are
  stale; annotate (axiom discharged 08-05, `Necessity/OneParameter.lean:220`;
  custom axioms now exactly []). Annotate, don't rewrite history.
- **De-vendor RealWigner**: move `Vendor/Wigner/RealWigner.lean` (Bryan's
  copyright, misfiled) to `RadicalRelativity/Wigner/RealWigner.lean`; drop its
  only import (`Vendor.Wigner.TransitionProbability` — VERIFIED dead at
  declaration level: zero island declarations, zero instances, zero
  topology/measure used; the one grep hit is docstring prose) and let the
  compiler dictate the replacement Mathlib imports. Update root imports,
  `AxiomAudit.lean` manifest (module rename), and every importer
  (grep `Vendor.Wigner.RealWigner`).

### 4.2 S2 order-unit-norm bridge (~2h)
The auditor's one real fidelity gap: `FirstArgContinuous` is `ContinuousOn` in
the CARRIED norm; the paper's S2 is the ORDER-UNIT norm. The two-sided bound
(`ouNorm ≤ ‖·‖ ≤ √(card n)·ouNorm`, `Hermitian/OrderUnit.lean`) is proved but
never converted into a `ContinuousOn` equivalence. Prove the bridge (equivalent
norms ⇒ same topology ⇒ same `ContinuousOn`) and add wrapper capstones
(`real_classification_ouNorm`, `complex_classification_unconditional_ouNorm`)
whose hypothesis is order-unit-norm continuity verbatim. `twistSeq_continuousAt_ouNorm`
already exists as material. New module → root import + AxiomAudit manifest.

### 4.3 Expose the Kadison classifications (~4-5h)
Both proofs derive the classification internally and discard it, exposing only
`PreservesJordan`. State it: ℝ (`Necessity/RealKadison.lean`) — ∃ orthogonal U,
Φ = Ad_U; ℂ (`Necessity/KadisonDischarge.lean`, rewire
`preservesJordan_of_rayMap_eq_projMap`/`_conj` at :159/:223 to surface the
witness from `rayMap_dichotomy` :102) — ∃ unitary U, Φ = Ad_U ∨ Φ = Ad_U∘transpose.
Converse witnesses already exist (`JordanWitness.lean:59,111,126`,
`RealJordanWitness.lean:61`) — package the iff if cheap. Strengthens the banked
theorem AND is the statement shape Mathlib demands. If a genuine wall: bank the
measured remainder here and move on.

### 4.4 Real-Wigner PR package (staged at the gate; ~3-4h)
On the de-vendored file: Mathlib-idiom rename pass (kill the `R` suffixes),
longline fixes, standalone PR-shaped copy + PR description in `upstream/`
(new dir, in-repo). MUST include collision check against Mathlib master and
`zblore/csd-lean4` and `leanprover-community/physlib` (read-only web/GitHub —
Blore's `WignerRigidity.lean:190-195` self-stages the ℂ side; his header cites
a v4.33 `Projectivization/Topology.lean` that may have landed). Prepared answer
for the inevitable reviewer question "unify over RCLike": over ℝ there is no
antiunitary branch; the ℂ case belongs to its own author. NO submission — the
package parks at Bryan's gate.

### 4.5 Supplementary §S1/§S3 rewrite DRAFT (~3h)
Staged in the BLOG repo as `research/paperA-supplementary-rewrite-draft.md`
(draft, NOT applied — `main.tex`/`supplementary.tex` are Bryan-gated). Contents:
corrected "What Is Machine-Checked" + "Lean skeleton" sections against the
arc-4 final SHA; the honest 5/17/14 coverage table; axiom-claims corrections
(zero axioms; Aczél + BGW now theorems; vIR DERIVED for both rows); re-pin
instruction (fresh frozen tag replacing `b7db3e8`); the auditor's fidelity
caveats stated once each (OrderUnitSpace `archimedean` = boundedness;
`AdjAxis` ≠ the paper's frame graph, discharges the same residue; `sp_effect`
as field). Never "fully formalized."

### 4.6 Compaction + gates + cold review (~1h)
Compact this file's M1–M7 history (keep top blocks, six-targets table, arc
records; archive the rest — THEOREM-MAP is the asset). Full gates after 4.1–4.3:
`lake build` green + `AxiomAudit` custom axioms exactly `[]`. Freeze a SHA and
run ONE isolated cold review over the 4.2 + 4.3 diffs (machine-checked probes
allowed, scratchpad only). Bank everything; single-sentence local commits.

**OUT OF SCOPE (do not relitigate):** ℍ/𝕆 rows, rank-two classification map,
`prop:central` discharge, `mthm:omnibus`, any manuscript edit, any push/PR
submission, T1/T2 (PARKED), the frozen tag `paperA-jpa-submitted`.

---

## ★★ ARC-3 RESULT (2026-08-07) — **THE ℂ ROW IS HYPOTHESIS-FREE. GOAL MET.**

`Necessity.complex_classification_unconditional` (`Necessity/ComplexRowUnconditional.lean`)
carries exactly `{3 ≤ N, P : SequentialProductOn (HermitianMat (Fin N) ℂ), hS2}` — verified by
`#check`, not prose — and `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Gates at the end of the arc (all four units in): `lake build` green **3105 jobs**,
`AxiomAudit` PASS at **148** tracked modules, custom axioms exactly `[]`.

**What was built** (three new modules, 811 lines, no new capstone — the existing one was
instantiated, exactly as the attack plan called for):
* `Necessity/FrameConstancy.lean` — `sp_eq_twistSeq_frame` (the workhorse: `ComplexMaster`'s
  chain with the frame a FREE parameter, not `a.H.eigenvectorUnitary` — this is the unlock,
  and it worked because `sp_eq_twistSeq_transport` already took the unitary as a parameter);
  `twistSeq_adU_mat` / `twistSeq_eq_of_adU` (conjugation cancels); `star_phase_factor`,
  `exp_eq_of_twistSeq_diagFamily_eq`, `twist_param_unique_of_scaled` (uniqueness against a
  prescribed scaled family — `twist_param_unique` generalized from its fixed probe);
  `axisSplit`, `AdjAxis`, `diag_commute_of_axis`, `adU_eq_of_commute`,
  **`frameTwist_eq_of_adjAxis`** (cross-coherence).
* `Necessity/UnitaryGeneration.lean` — `axisVec` helpers; `AxisFixing`, `axisFixing_of_col`;
  `nrm2` (squared norm as a real, so no square root enters the reflection); `lineProj`,
  `house` and its involution/Hermitian/unitary lemmas; `house_axisFixing` (a reflection fixes
  every axis its vector misses — the fact that makes reflections usable as adjacency steps);
  `house_mulVec_align`; `exists_alignTarget`; `exists_align_off_axis`;
  `exists_clear_column`; **`exists_axisFixing_factor`**; **`adjAxis_connected`**.
* `Necessity/ComplexRowUnconditional.lean` — **`frameTwistConst`**,
  **`complex_classification_unconditional`**, plus two **in-tree non-vacuity certificates**:
  `twistProductOn_classified` (the hypothesis class is inhabited — `3 ≤ N` + S1-S7 + S2 are
  simultaneously satisfiable, witnessed by M1's twist product, so the row is not vacuous) and
  `complex_classification_sharp` (run the capstone on `twistProductOn t` and the unique
  parameter it returns is `t` itself — the twist family is faithfully parameterized and the
  `∃!` is not met by some unrelated value). These answer the vacuity question *in the tree*
  rather than by argument, which is the same discipline that killed the OpCommute escape class.

**Design decisions that mattered, for anyone extending this:**
* Adjacency was defined as "`F* G` fixes a coordinate axis" (`AdjAxis`), NOT as the general
  coordinate-splitting relation the plan sketched. The two-level spectrum `axisSplit m` is
  all the cross-coherence argument needs, and the singleton form makes both the commutation
  check and the Householder connectivity argument shorter.
* Connectivity went through **Householder reflections**, not Givens rotations. A reflection
  whose vector has one zero coordinate is automatically axis-fixing, so an *arbitrary*
  reflection can be an adjacency step; that turns the plan's "~150-300 line elementary
  induction" into a fixed 2-step column clear with no induction at all. Within the NEW material
  `N ≥ 3` is needed in exactly one place — it frees the axis the second reflection's vector must
  miss (three distinct indices in `exists_clear_column`). Precision: the row as a whole needs
  `N ≥ 3` for a second, PRE-EXISTING reason as well, namely the per-frame theorem
  `complex_perFrame_unconditional`, which is the paper's own rank-≥3 hypothesis. So do not read
  "enters exactly once" as "the ℂ row would work at `N = 2` but for connectivity" — it would
  not, and rank two is a genuinely different theorem (`cor:qubit-classification`).
* Two `rw`-nesting traps cost time and will recur: rewriting `v` inside a term that also
  *defines* the reflection vector (fixed by proving linearity as a separate `have` instead of
  rewriting `v`), and `rw [← hsp]` reaching inside `√(normSq …)` (fixed by obtaining the
  square roots opaquely via `obtain ⟨b, hbne, hb⟩`).
* `frameTwistConst` needs `intro F G` + explicit `(Adj := …) (t := …)`; term-mode with
  implicit unification times out at `whnf` on `frameTwist`'s `Classical.choose` body.
* ★ **A prediction in the ORDERS below was WRONG, and the record must not imply otherwise.**
  The orders said `frameTwist_unique` (built 08-06) would be the tool that ties the transported
  parameter to `frameTwist` "without fighting `choose`". **It is not used at all** — verified by
  grep: nothing outside its own definition site references it. The reason is that the winning
  route compares PRODUCT VALUES (`twistSeq t_F a b = twistSeq t_G a b`, then strip the
  conjugation and probe) rather than comparing stabilizer couplings, so `choose` never had to
  be fought: `frameTwist_spec` is applied at each frame separately and the two conclusions are
  chained through `P.sp a b`. `frameTwist_unique` remains a true and worthwhile theorem — it is
  what makes `frameTwist` an invariant rather than a choice artefact — but it is **not
  load-bearing for the unconditional capstone**, and anyone budgeting future work should not
  assume the coupling-comparison route was the one that worked.

**Item 7.3 (statement layer) — also DONE for the ℝ and ℂ rows.**
`RadicalRelativity/PaperA/CertifiedConfiguration.lean`: both reference maps instantiated
concretely with effect closure proved, the pinned-product→class bridge built, and both frozen
shapes discharged (`PaperA.real_meets_ludersConclusion`,
`PaperA.complex_meets_uniqueTwistConclusion`, both Lean-core). Final gates: `lake build` green
**3105 jobs**, `AxiomAudit` PASS at **148** modules, custom axioms exactly `[]`. See item 7.3
in the roadmap below for what is still open there (ℍ/𝕆 shapes, README, paper §App).

**★ COLD ADVERSARIAL REVIEW (2026-08-07, isolated agent, refute-first charter): ALL SIX ATTACK
VECTORS SOUND; verdict "the claim is justified as stated."** Vectors run: vacuity, circularity,
junk/stub, conclusion strength, the interval argument, `N ≥ 3` usage. What it independently
machine-checked rather than argued: `AdjAxis` is satisfiable (`AdjAxis F F`) **and not total**
(`¬ AdjAxis 1 cycU` for the 3-cycle permutation unitary on `Fin 3`) — so connectivity is real
content, not a disguised tautology; and `frameTwist hN (twistProductOn t) _ U = t` at EVERY frame,
so `frameTwist` computes the right number on a known model rather than being a `choose` artefact.
It confirmed no `sorry`/`axiom`/`native_decide` anywhere in the closure, that the conclusion has
no `PosDef` (all effects, singular included, and the invertible→all step is genuine density plus
S2), and that `ExistsUnique` is the real thing. Three DOC-ONLY items were raised and all three
are now FIXED in the source:
* the file-header gloss "which is why the family, and not a single base point, is the object
  being compared" overstated: that is true of THIS probe (one entry ⟹ one phase equation ⟹ mod
  `2π/Δ`), not a mathematical necessity — for `N ≥ 3` a single base point with incommensurable
  gaps read at two index pairs would also force exactness. Reworded; **if that sentence ever
  migrates into the manuscript, weaken it to "a single phase equation cannot pin `t`."**
* the `Adj := True` instantiation LOOKS like it assumes connectivity away. It does not, and the
  ORDERING is what makes it non-circular: constancy is established first from the genuine
  `AdjAxis` walk, and only then is the capstone reused with the cheapest adjacency. Now
  pre-empted in `ComplexRowUnconditional`'s docstring — say this before a referee asks.
* `a^{1/2+it}` at singular `a`: under Lean's `Real.log 0 = 0` the factor vanishes on the kernel,
  which is the intended continuous extension. Now stated in the docstring.
**The one seam no `#print axioms` can certify** (reviewer's words, and correct): "hypothesis-free"
means free relative to the Lean ENCODING of van de Wetering Def 2 — `SequentialProductOn`
(S1, S3-S7, plus `sp_effect` as codomain) + `FirstArgContinuous` as S2. That mapping is a human
judgment. The reviewer read it as faithful. This is the honest residue of the whole campaign and
must never be described as machine-checked.
**PROCESS LESSON (cost the reviewer a re-read):** the tree moved under the cold reviewer mid-review
(HEAD advanced and `ComplexRowUnconditional.lean` gained the two non-vacuity certificates between
its first read and its greps), so its verdict was briefly about a state that no longer existed.
**Freeze the tree or hand the reviewer a tag/SHA next time** — do not run a cold review against a
live edit session.

**ARC-3 SCORECARD.** U1 cross-coherence ✓ · U2 connectivity ✓ · U4 capstone ✓ · U5 statement
layer ✓ (ℝ/ℂ). Nothing in the arc hit a wall; no out-of-scope row was touched. Total: five new
declarations of record (`sp_eq_twistSeq_frame`, `frameTwist_eq_of_adjAxis`, `adjAxis_connected`,
`frameTwistConst`, `complex_classification_unconditional`) plus the statement-layer pair.

---

## ARC-3 ORDERS (2026-08-07, Fable handoff — Bryan funded 18h of Opus and delegated scoping)

*All four units (U1, U2, U4, U5) are DONE — see the RESULT block above, which supersedes the
attack plan below wherever they differ (notably: Householder rather than Givens for
connectivity, and axis adjacency rather than the general splitting relation). This block is
retained for its SCOPE DECISIONS, which still bind, and as the record of what was planned
versus what the mathematics actually wanted.*

**THE GOAL OF THIS ARC:** make the ℂ row hypothesis-free. Deliver
`Necessity.complex_classification_unconditional` whose signature carries ONLY
`{3 ≤ N, P : SequentialProductOn (HermitianMat (Fin N) ℂ), hS2 : P.FirstArgContinuous}`
and concludes `∃! t, ∀ a b effects, P.sp a b = twistSeq t a b`. Then re-point the
certified-configuration statement layer (item 7.3) at the ℝ and ℂ capstones. Verify with
`#check` + `#print axioms` in-transcript; both gates green after every unit.

**SCOPE DECISIONS, made under delegated authority — do not relitigate this arc:**
* ℍ refactor: DEFERRED. Even after the 7-file abstract-carrier lift, the row needs
  quaternionic Wigner rigidity — a second from-scratch classical theorem. Cannot close in
  any near window; the refactor's real payoff (ℝ/ℂ/ℍ as one theorem) is post-submission work.
* H₃(𝕆): out of scope (no octonions in any prover — separately fundable program).
* `prop:central`, rank-two classification map: out of scope (open mathematics).
* Standing gates unchanged: all commits LOCAL, no push, no sync.sh, frozen tag untouched,
  JMP reserved, T1/T2 parked.

**THE ATTACK PLAN (verified against source 08-07 — every named ingredient exists):**
The capstone `complex_classification` already takes `(Adj, connected, overlap)`. Do NOT build
a new globalization: INSTANTIATE it. Define
`AdjSplit F G := ∃ (S : Finset (Fin N)), S.Nonempty ∧ Sᶜ.Nonempty ∧ (F⁻¹*G preserves the
coordinate splitting S ⊕ Sᶜ)` and discharge the two hypotheses:

* **U1 (overlap = cross-coherence, the crux).** If `W := F⁻¹G` preserves a splitting, both
  frames diagonalize the common scaled family `a_x = diag(exp(x·s))` (s constant on each part,
  distinct across, s ≤ 0 so a_x is a posdef effect for x > 0 — the `log_eigenvalues_nonpos`
  trick). Route via PRODUCT VALUES, not couplings: the per-frame product formula
  (`ComplexMaster.lean:78-79` — `sp_eq_twistSeq_transport` + `sp_eq_twistSeq_diagFamily` +
  `eq_adU_diagFamily`) gives `P.sp a_x b = twistSeq t_F a_x b = twistSeq t_G a_x b` for ALL b.
  Evaluate both twistSeq at a block b with distinct part-eigenvalues: entries carry
  `exp(i·t·x·(s_i − s_j))`, agreement on an interval of x, then
  `MasterTheorem.real_character_unique` (Globalization.lean:98) forces `t_F = t_G` EXACTLY
  (single-point agreement only pins t mod 2π — the interval is not optional).
  Tie the transported t to `frameTwist` via `frameTwist_unique` (built 08-07 for exactly this:
  it converts "some parameter works" into "the parameter equals" without fighting `choose`).
  FALLBACK ROUTE if the product-value route jams: compare stabilizer couplings directly
  through `conjProduct` composition (`Ad` functoriality; add `SequentialProductOn.ext` by
  sp-equality — all other fields are Props over sp).
* **U2 (connected = Givens generation, the only new development).** Every `U ∈ U(N)` is a
  finite product of plane unitaries (supported on `span{e_k, e_l}`) and a diagonal phase.
  Constructive induction on N: zero out the first column with plane rotations, recurse.
  ~150-300 lines, elementary. Each factor step preserves the `({k,l}, rest)` splitting —
  nonempty complement needs only N ≥ 3 ✓. Chain: `U_{p+1} = U_p · (plane factor)` gives
  `Relation.ReflTransGen (SymmStep AdjSplit) F G` for all F, G.
* **U3 (cheap invariances, do first as warm-up).** Permutation W: per-frame t is
  label-independent (the per-frame theorem is one t across ALL blocks). Diagonal-phase W:
  fixes every diagonal matrix; its block action is an SO(2) rotation commuting with `rotJ`.
* **U4 (assembly).** `complex_classification_unconditional := complex_classification hN P hS2
  AdjSplit (U2) (U1)`. One-liner once U1/U2 land.
* **U5 (packaging, item 7.3).** Instantiate `PaperA/Statement.lean`'s parameterized
  `LudersConclusion`/`UniqueTwistConclusion` with the CONCRETE references (conj-Lüders,
  `twistSeq`), prove the ℝ and ℂ capstones meet them, refresh AuditPins/THEOREM-MAP/README
  and this file's state-of-six block. Mechanical.

**Estimate:** U3 0.5-1h · U1 4-6h · U2 3-5h · U4 <1h · U5 2-3h · banking ~1h ≈ 12-17h.
P(complete) ≈ 0.8 at demonstrated velocity. **Failure protocol:** if a component hits a
genuine wall, bank the measured remainder declaration-by-declaration here (as the ℝ bridge
did), finish U5 against whatever IS certified, and say plainly which conjunct failed.
Documented failure ≠ completion; do not grind past a measured wall, and do not touch
out-of-scope rows to manufacture progress.

**Working discipline that produced the last two rows — keep all of it:** unit-by-unit with
both gates after each; single-sentence commits with explicit paths; bank each unit to the
blog route file + memory; THEOREM-MAP wins over this file on any disagreement; check
hypothesis lists with `#check`, never prose; no vacuous stub theorems; when a rewrite target
sits under a dependent proof argument, look for the defeq.

---

## ★ STATE OF THE SIX TARGETS — as of 2026-08-08 (read this first)

Tree: `lake build` green at 3106 jobs; `AxiomAudit.lean` PASS at 149 tracked modules;
**custom axioms exactly `[]`**, every tracked declaration's closure ⊆
{`propext`, `Classical.choice`, `Quot.sound`}. All commits LOCAL (repo is public;
pushing is Bryan-gated).

**Coverage of the paper, stated as a count so it is never overstated: 5 of the 36 numbered
results are FORMALIZED at the article's own generality, 17 PARTIAL, 14 ABSENT.** Never
write "fully formalized". Itemization: blog `research/paperA-supplementary-rewrite-draft.md`
§3; per-statement evidence: `THEOREM-MAP.md`, which governs.

| Row | Status | Capstone |
| --- | --- | --- |
| `H_N(ℂ)`, N ≥ 3 | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `∃! t`, twist on ALL effects; both frame-graph facts DISCHARGED in-tree (cross-coherence + connectivity). Carries only S1-S7 + S2 + `3 ≤ N`. **08-08: also stated with S2 in the ORDER-UNIT norm** (`complex_classification_unconditional_ouNorm`), so the paper's S2 is the literal hypothesis | `Necessity.complex_classification_unconditional` |
| `H_n(ℝ)` | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `a•b = √a·b·√a` on ALL effects, no twist; Jordan hypothesis DISCHARGED by real Kadison proved in-tree, now stated as the full **classification** (`orderAutoR_eq_orthConj`, exact — converse packaged). **08-08: also stated with S2 in the ORDER-UNIT norm** (`real_classification_ouNorm`) | `Necessity.real_classification` |
| `H_n(ℍ)` | **FOUNDATION COMPLETE + `Q_{√a}` restricts** (carrier, order-unit, unital Jordan subalgebra, positivity, cfc-closure, `quatQuadRepEquiv`); **NOT a short lane — see the carrier-genericity finding in `LEDGER-ARCHIVE-M1-M7.md`** | `QuatCarrier`, `quatQuadRepEquiv` |
| `H₃(𝕆)` | **BLOCKED** — octonions exist in no prover (verified: zero files) | — |
| `cor:qubit-classification` | moduli space + one nonconstant element + certified `ℂP¹→ℝP²` descent + separation; **classification map `product ↦ moduli` ABSENT** | `RankTwo.tauModuliRP2`, `RankTwo.tauRP2_blochFrame` |
| `mthm:omnibus` | **carrier + BOTH assembly halves** (sufficiency `prod`, determination `sp_eq_of_prod_eq`); conditional on the SPLITTING (`prop:central`, paper proof) | `SequentialProductOn.prod` |

★★**THE ℝ ROW'S CONDITION IS GONE (2026-08-07).** `Necessity.real_classification`
(`Necessity/RealRowUnconditional.lean`) proves: for any S1-S7 product with S2 on
`H_N(ℝ)`, `N > 0`, `P.sp a b = b.conj (a.cfc sqrt).mat` on ALL effects. Hypothesis list
is exactly the paper's; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
The discharge chain, all in-tree:
  * `Wigner/RealWigner.exists_isometry_of_transProbPreservingR` (de-vendored 08-08; first-party) — real Wigner
    rigidity, PROVED (the theorem that existed in no library);
  * `Necessity/RealInducedMap.lean` — `rayMapR` (order automorphism ⟹ ray self-map via
    choice) + `rayMapR_transProbPreservingR` (it preserves transition probability, by
    `tprobR_preserved`) + `isometryMatrixR` (the orthogonal MATRIX of the isometry, with
    `isometryMatrixR_orthogonal`) + `rankOneR_eq_of_mk_eq` (ray equality ⟹ rank-one
    equality: the sign cancels because `rankOneR` is quadratic — this is the step that
    has no ℂ analogue and is why ℝ needs no dichotomy);
  * `Necessity/RealKadison.orderAutoR_preservesJordan` — REAL KADISON RIGIDITY: every
    unital ℝ-linear order-automorphism of `H_N(ℝ)` is conjugation by an orthogonal matrix,
    hence Jordan;
  * `Necessity/RealRowUnconditional.thetaPreservesJordanR_of_S2` — `theta` is a unital
    surjective linear order-iso (`theta_le_iff`/`theta_one`/`thetaEquiv`, all already
    field-general), so real Kadison applies in every eigenframe.
**CORRECTION to an earlier framing in this ledger and in the new files' first drafts:**
the ℂ row's Wigner step is a vendored *proof* (`Vendor/Wigner/WignerRigidity.lean`), NOT
an axiom — `#print axioms Necessity.complex_classification` is Lean core too. The ℝ row's
gap was never a cited axiom that ℂ also had; it was a MISSING THEOREM. Do not write "ℝ is
better founded than ℂ" anywhere: both rows now close over Lean core alone.
Scope note: the unconditional statement is at `n := Fin N` (the paper's `H_N(ℝ)`);
`sp_eq_luders_of_effect` remains stated at generic `[Fintype n] [DecidableEq n]` and the
Kadison bridge is `Fin N`-bound because it needs `Matrix.toEuclideanLin`. Generalizing the
bridge to arbitrary `n` is mechanical (nothing uses `Fin`'s order) but was not done.

★★**LABEL CORRECTION 2026-08-07 — the ℂ row was mislabelled in THIS TABLE, and the mislabel
was repeated in session reports. Verified by `#check`, not by reading prose.**
```
@Necessity.real_classification    : ∀ {N}, 0 < N → ∀ P, P.FirstArgContinuous → … (nothing else)
@Necessity.complex_classification : ∀ {N}, 3 ≤ N → ∀ P, P.FirstArgContinuous →
                                      ∀ (Adj), (connected …) → (overlap …) → ∃! t, …
```
The ℂ row takes `Adj` plus `connected` plus `overlap` as CALLER-SUPPLIED arguments. Those are
paper-proved and located, never axioms — but a theorem with located hypotheses is **not
unconditional**, which is exactly the standard this ledger applied to the ℝ row when it read
"modulo the cited Jordan property". Applying one standard to ℝ and another to ℂ is the error.
`THEOREM-MAP.md` was RIGHT throughout (it calls the two "the honest residue of this row");
only this summary table and the session reports drifted. THEOREM-MAP remains the governing
honesty ledger — **when the two disagree, THEOREM-MAP wins.**
The lesson generalizes and still binds: **check hypothesis lists with `#check`, never by
reading prose**, and apply one standard to every row.

★★**SUPERSEDED LATER THE SAME DAY — do not cite the two paragraphs that stood here.** They
read "`H_n(ℝ)` is the ONLY row that carries nothing beyond S1-S7 + S2 … On CARRIED HYPOTHESES
ℝ is now strictly cleaner" and "to make ℂ genuinely hypothesis-free, `connected` and `overlap`
must be discharged … Neither is started." Both were true when written and are now FALSE: the
ℂ row's two frame-graph facts were discharged on 2026-08-07 (see the ARC-3 RESULT block at the
top of this file). **Current standing: `H_N(ℂ)` for `N ≥ 3` and `H_n(ℝ)` are BOTH
hypothesis-free, and they are equally well founded on both axes** — identical axiom closure
(Lean core) and identical carried hypotheses (S1-S7 + S2 + a dimension bound). Never rank one
above the other on either axis.

## Milestone history M1–M7 — ARCHIVED

The arc-2/arc-3 narrative and the full M1–M7 discharge records (about 3,000
lines) were moved to **`LEDGER-ARCHIVE-M1-M7.md`** on 2026-08-08 (item 4.6).
They are provenance, not orders: every milestone whose row in `THEOREM-MAP.md`
reads machine-checked has left this ledger, and THEOREM-MAP is the asset.

Two pointers that other parts of this file still make, now resolved there:

* the **ℍ carrier-genericity finding** referenced by the six-targets table
  (`H_n(ℍ)` row) — archive, "SECOND CORRECTION TO THE ℍ ESTIMATE";
* the **ℂ residue** sharpening that preceded its discharge — archive,
  "ℂ RESIDUE SHARPENED 2026-08-07".

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
- **H6. `HermitianMat.Matrix` namespace shadow (vendor-inherited parser trap).**
  The vendored island declares `Matrix.*` lemmas inside `namespace HermitianMat`
  (`Vendor/HermitianMat/Inner.lean:405`, `NonSingular.lean:18`), so an
  `open scoped Matrix` written INSIDE `namespace HermitianMat` resolves to the
  notation-free `HermitianMat.Matrix` and silently fails to activate `*ᵥ` — the
  parser then lexes `*ᵥ` as `*` + a subscript-term `ᵥ…`, yielding baffling
  "`Mathlib.Tactic.subscriptTerm` has not been implemented" errors. Always
  `open scoped Matrix` BEFORE entering the namespace (or write
  `open scoped _root_.Matrix`). Diagnosed 2026-08-04 (order-unit layer).
  Same family (2026-08-05): the vendor also declares `HermitianMat.pow_zero`
  (Basic.lean:275), which shadows the ROOT `pow_zero` inside the namespace and
  makes `simp only [pow_zero]` a silent no-op on `Matrix`/ℝ powers — write
  `_root_.pow_zero`. Audit any bare root-algebra simp name used inside
  `namespace HermitianMat` against the vendor's declarations.
- **H7. Expected-type elaboration of resolution-shaped lemmas times out.**
  Applying `mat_cfc_of_resolution` with `(R := fun q => …)`/`(c := fun q => …)`
  named AND a type-ascribed `have` makes the unifier grind through `specProj`
  bodies (cfc → eigendecomposition) — deterministic whnf timeout even at 800k
  heartbeats. The fix is forward inference:
  `have hres := fun f => mat_cfc_of_resolution hidem horth hsum hM f` with NO
  type ascription and NO named lambdas — instant, and the (β-unreduced) inferred
  type rewrites fine downstream. Diagnosed 2026-08-05 (S1–S7 unit, bisected via
  probe file).
- **H5. Scoped-instance gotcha (the costliest inventory discovery).** The
  Loewner order + `StarOrderedRing` on `Matrix` require `open scoped
  MatrixOrder` (`Analysis/Matrix/Order.lean`); the matrix C*-norm requires
  `open scoped Matrix.Norms.L2Operator` (or use the `CStarMatrix` type copy,
  which carries the instances globally). Neither is discoverable from
  declaration names. Also: `LinearAlgebra/Matrix/HermitianFunctionalCalculus
  .lean` is a deprecated stub — the real module is
  `Analysis/Matrix/HermitianFunctionalCalculus.lean`. Put the `open scoped`
  lines in every M1/M2 file header from day one.

