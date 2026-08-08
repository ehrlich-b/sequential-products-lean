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

## ★ STATE OF THE SIX TARGETS — as of 2026-08-07 (read this first)

Tree: `lake build` green at 3105 jobs; `AxiomAudit.lean` PASS at 148 tracked modules;
**custom axioms exactly `[]`**, every tracked declaration's closure ⊆
{`propext`, `Classical.choice`, `Quot.sound`}. All commits LOCAL (repo is public;
pushing is Bryan-gated).

| Row | Status | Capstone |
| --- | --- | --- |
| `H_N(ℂ)`, N ≥ 3 | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `∃! t`, twist on ALL effects; both frame-graph facts DISCHARGED in-tree (cross-coherence + connectivity). Carries only S1-S7 + S2 + `3 ≤ N` | `Necessity.complex_classification_unconditional` |
| `H_n(ℝ)` | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `a•b = √a·b·√a` on ALL effects, no twist; Jordan hypothesis DISCHARGED by real Kadison proved in-tree. **The only row carrying nothing beyond S1-S7 + S2** | `Necessity.real_classification` |
| `H_n(ℍ)` | **FOUNDATION COMPLETE + `Q_{√a}` restricts** (carrier, order-unit, unital Jordan subalgebra, positivity, cfc-closure, `quatQuadRepEquiv`); **NOT a short lane — see the carrier-genericity finding below** | `QuatCarrier`, `quatQuadRepEquiv` |
| `H₃(𝕆)` | **BLOCKED** — octonions exist in no prover (verified: zero files) | — |
| `cor:qubit-classification` | moduli space + one nonconstant element + certified `ℂP¹→ℝP²` descent + separation; **classification map `product ↦ moduli` ABSENT** | `RankTwo.tauModuliRP2`, `RankTwo.tauRP2_blochFrame` |
| `mthm:omnibus` | **carrier + BOTH assembly halves** (sufficiency `prod`, determination `sp_eq_of_prod_eq`); conditional on the SPLITTING (`prop:central`, paper proof) | `SequentialProductOn.prod` |

★★**THE ℝ ROW'S CONDITION IS GONE (2026-08-07).** `Necessity.real_classification`
(`Necessity/RealRowUnconditional.lean`) proves: for any S1-S7 product with S2 on
`H_N(ℝ)`, `N > 0`, `P.sp a b = b.conj (a.cfc sqrt).mat` on ALL effects. Hypothesis list
is exactly the paper's; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
The discharge chain, all in-tree:
  * `Vendor/Wigner/RealWigner.exists_isometry_of_transProbPreservingR` — real Wigner
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

★**ℂ RESIDUE SHARPENED 2026-08-07** (`Necessity/ComplexResidue.lean`, census 144, gates green
3101 jobs, axioms Lean core). `complex_classification` let the CALLER pick `Adj`. Taking
`Adj := fun _ _ => True` makes `connected` free (`ReflTransGen.single (Or.inl trivial)`) and
turns `overlap` into exactly "any two frames' characters agree on an interval" = `frameTwist F
= frameTwist G`. So `complex_classification_of_frameTwistConst` carries ONE hypothesis,
`FrameTwistConst`, a statement about THIS development's own `frameTwist` — no caller-supplied
relation, no citation to two manuscript lemmas. Two reasons this is worth having: a
caller-chosen `Adj` could always be instantiated to make the row look stronger than it is, and
the residue is now internal rather than a citation.
**SCOPE — do not overstate.** This is SUFFICIENT, packaged from the existing capstone. Still
say "suffices for", never "equivalent to".
**PER-FRAME UNIQUENESS NOW PROVED (same day):** `frameTwist_unique` — two parameters satisfying
the coupling identity at one frame are equal (evaluate at `i ≠ j` and the indicator of `i`, so
`r i − r j = 1`, then cancel via `smul_left_injective ℝ rotJ_ne_zero`). This makes `frameTwist`
a genuine INVARIANT of the frame rather than an artefact of `choose`, and it is the key input to
the converse. **What the converse still needs beyond it:** that the twist product's OWN
per-frame parameter is `t` (i.e. compute `stabilizerCoupling` for `twistProductOn t`). Until
that is done the reduction is not lossless. (I first wrote a `True`-valued stub for the converse and
deleted it — same junk-stub failure mode as `prod_sp_inj`; never ship a vacuous theorem to make
a docstring read better.)
**So the ℂ row's remaining work is exactly one theorem, and it is ORDINARY work** — nothing it
needs is missing from Mathlib, unlike the octonion wall or the ℍ carrier decision.
★★**THAT WORK IS NOW DONE (same day).** `FrameTwistConst` is discharged by
`Necessity.frameTwistConst`; the row's capstone is `complex_classification_unconditional`. The
"suffices for, never equivalent to" caution above applied to `FrameTwistConst` as a *carried*
hypothesis and no longer governs the row — but it DOES still govern any statement about the
converse, which remains unproved (the twist product's own per-frame parameter is still not
computed). This block is retained because its diagnosis of the residue is what the discharge
was built against, and because the junk-stub lesson stands.

**Field-general infrastructure now standing** (none of it in Mathlib):
`HermitianMat.sqrt_mul_of_commute`, `eq_zero_of_commute_hermitian_of_trace_zero`,
`continuous_cfc_polynomial`, `continuousOn_cfc_sqrt_effects`, plus the whole Θ chain,
spectral resolution, and character/coalescence layers over arbitrary `RCLike 𝕜`.

★★**SECOND CORRECTION TO THE ℍ ESTIMATE — verified at source 2026-08-07. READ BEFORE
BUDGETING THE ℍ ROW.** The 08-06 note below concluded the ℍ row is "plausibly a LANE, not a
foundational program" because the symplectic embedding puts the CARRIER inside complex
Hermitian matrices. The carrier claim is right and is now built (`quatQuadRepEquiv`, below).
**The conclusion drawn from it is wrong.** Checked by grepping the `variable` line of every
stage of the Θ chain:
```
LeftMultiplication    variable (P : SequentialProductOn (HermitianMat n 𝕜))
Theta                 variable (P : SequentialProductOn (HermitianMat n 𝕜))
ComparisonInstanceGen variable (P : SequentialProductOn (HermitianMat n 𝕜))
BlockChiGen           variable (P : SequentialProductOn (HermitianMat n 𝕜))
ChiContinuityGen      variable (P : SequentialProductOn (HermitianMat n 𝕜))
```
**The Θ apparatus is generic in the FIELD (`𝕜 : RCLike`) and CONCRETE in the CARRIER
(`HermitianMat n 𝕜`).** `QuatCarrier n` is a `Submodule`, not a `HermitianMat`, so it can
consume NONE of that chain no matter how field-general the chain is. Concretely `seqLeftMul`
— the first link — is built from `posPart`/`negPart`, spectral machinery that exists on
`HermitianMat` and not on a submodule. So the ℍ row needs one of:
  * **(A) an abstract-carrier refactor**: lift the Θ chain from `HermitianMat n 𝕜` to an
    interface (order-unit space + cfc + Jordan product + positive/negative parts), then
    instantiate it twice. Seven files, and it touches two BANKED rows — high risk, real value
    (it would also make the ℝ and ℂ rows instances of one theorem);
  * **(B) a transfer argument** carrying the ℂ classification onto the subalgebra. No route
    known: a product on `H_n(ℍ)` has no reason to extend to `H_{2n}(ℂ)`.
Do NOT describe the ℍ row as "a lane" or quote a short estimate for it until (A) or (B) is
chosen. The 08-06 text below is kept for provenance; its Mathlib facts are correct and its
scheduling conclusion is superseded by this block.
**LANDED 2026-08-07** (`Hermitian/QuatQuadRep.lean`, NEW, census 143, gates green 3100 jobs,
custom axioms exactly []): `quatConjH_conj` — **the intertwining** `Φ (x.conj A) = (Φ x).conj A`
for quaternionic `A` and EVERY `x`; `IsQuaternionic.conj`; `IsQuaternionic.sqrt`;
`IsQuaternionic.quadRep`; `IsQuaternionic.quadRepInv`; and `quatQuadRep`/`quatQuadRepInv`/
**`quatQuadRepEquiv`** — `Q_{√a}` is an ℝ-linear AUTOMORPHISM of `H_n(ℍ)`.
KEY TRICK, reusable: the inverse branch conjugates by `a.cfc (fun x => (√x)⁻¹)`, and **that
function is not continuous at 0**, so `IsQuaternionic.cfc_of_effect` cannot reach it. Stating
the intertwining for EVERY `x` (not just quaternionic ones) makes the inverse branch free:
`Q` is injective and `Q (Φ x) = Φ (Q x) = Φ y = y = Q x` forces `Φ x = x`. No functional
calculus needed on the inverse side at all.
Trap: `Matrix.PosDef` in a statement needs `open ComplexOrder` (else `PartialOrder ℂ` fails).

★★**CORRECTION to the ℍ assessment, verified against the pinned Mathlib 2026-08-06.**
Earlier notes (including this session's) said "matrices over ℍ exist in no prover" and
budgeted the row at months. Checked at source:
* **Quaternions ARE well supported**: `Algebra/Quaternion.lean`,
  `Algebra/QuaternionBasis.lean`, `Analysis/Quaternion.lean`,
  `Analysis/Normed/Algebra/QuaternionExponential.lean` — including `StarRing ℍ`, the
  norm, and the exponential.
* **ℍ is NOT `RCLike`** (grep: zero hits) — necessarily, since `RCLike` demands
  commutativity. **That, not the absence of quaternions, is the actual blocker**: the
  whole `HermitianMat n 𝕜` layer this campaign is built on is `RCLike`-based.
* Octonions: **genuinely absent** (zero files matching `Octonion`/`CayleyDickson`), and
  no Jordan-algebra or Albert-algebra files at all. The H₃(𝕆) row's assessment stands.
**Consequence — the ℍ row should be re-planned around the symplectic embedding, which the
route file already names**: `H_n(ℍ) ↪ H_{2n}(ℂ)` as the fixed points of a conjugate-linear
involution `J`. That route lives ENTIRELY inside complex Hermitian matrices — i.e. inside
the machinery this campaign already has field-general and, at ℂ, fully developed — and
never needs a `HermitianMat` layer over a noncommutative ring. So the ℍ row is plausibly
a LANE (like the ℝ row turned out to be), not a foundational program. It should be
re-scoped before anyone budgets months for it.
**STARTED 2026-08-06** (`Hermitian/Symplectic.lean`, NEW, census 132, gates green, tree
at 3089 jobs, custom axioms exactly `[]`; `quatConj_mul` and `IsQuaternionic.symmMul`
axiom-checked = Lean core only): `symplecticJ` (`J₀ = [[0,−1],[1,0]]` via
`Matrix.fromBlocks`) with `symplecticJ_transpose_mul`/`_mul_transpose` (`J₀ᵀJ₀ = 1`),
the involution **`quatConj A = J₀ Ā J₀ᵀ`** with **`quatConj_mul` (MULTIPLICATIVE — this
is where `J₀ᵀJ₀ = 1` is used)**, `quatConj_add`, `quatConj_real_smul`,
`quatConj_smul_of_conj_eq` (homogeneity for any self-conjugate scalar, which is what
covers the Jordan product's `2⁻¹`), the predicate `IsQuaternionic` and its closure
lemmas — culminating in **`IsQuaternionic.symmMul`: the fixed set is closed under the
JORDAN PRODUCT, i.e. `H_n(ℍ)` is a Jordan subalgebra of `H_{2n}(ℂ)`**.
Traps: `symmMul` lives in `Vendor/HermitianMat/Jordan.lean` (import it, `OrderUnit`
alone is not enough); `Matrix.add_mul`/`smul_mul` rewrites do not fire on the
`J₀ * _ * J₀ᵀ` sandwich — use `noncomm_ring`; and `(starRingEnd ℂ) 2 = 2` wants routing
through `Complex.conj_ofReal` after `show (2:ℂ) = ((2:ℝ):ℂ)`.
Also landed (same day): **`symplecticJ_sq` (`J₀² = −1`)**, **`quatConj_involutive`**
(`Φ∘Φ = id` — `J₀` is real, so double conjugation returns `J₀²A(J₀ᵀ)²` and both squares
are `−1`), and **`isQuaternionic_one`** (the unit is quaternionic, from `J₀J₀ᵀ = 1`), all
axiom-checked = Lean core only. So `Φ` is a genuine conjugate-linear ALGEBRA INVOLUTION
fixing the unit, and the quaternionic set is a unital Jordan subalgebra.
Traps: block identities like `fromBlocks (-1) 0 0 (-1) = -1` want `ext i j` +
`rcases i with i | i` and `simp [Matrix.fromBlocks, Matrix.one_apply, apply_ite]`, not
`fromBlocks_neg` juggling (a stray `-0` blocks the rewrite); and double conjugation needs
an explicit `ext`-level lemma (`Complex.conj_conj`) — `Matrix.map_map` +
`RingHomCompTriple.comp_eq` makes no progress.
Also landed: `isQuaternionic_zero`, **`quatSubmodule : Submodule ℝ (HermitianMat (n⊕n) ℂ)`**
(the fixed set as a real subspace — this is what lets the quaternionic carrier INHERIT its
normed and order structure instead of being built from scratch over a noncommutative ring),
`mem_quatSubmodule`, and `one_mem_quatSubmodule`. Axiom-checked = Lean core only.
★★**THE QUATERNIONIC CARRIER IS AN ORDER-UNIT SPACE — 2026-08-06** (compiled FIRST
TRY): `QuatCarrier n := quatSubmodule` with **`instance : OrderUnitSpace (QuatCarrier n)`**
— every field inherited from `H_{2n}(ℂ)` (order = the restriction, `ousUnit := ⟨1, _⟩`,
`archimedean` = the ambient bound relativized), plus `quatCarrier_ousUnit_coe`. Verified
by probe: **`SequentialProductOn (HermitianMat.QuatCarrier n)` TYPECHECKS.** So the ℍ
row's statement is now expressible in the tree, on a carrier built entirely from complex
Hermitian matrices — no algebra over a noncommutative ring anywhere.
Also landed: `map_conj_eq_transpose` (for a Hermitian matrix, entrywise conjugation IS
transposition), `symplecticJ_transpose_eq_conjTranspose` (`J₀` is real), and
**`quatConj_posSemidef` — `Φ` PRESERVES POSITIVE SEMIDEFINITENESS**, since for Hermitian
`A` it is the congruence `J₀ Aᵀ J₀ᴴ`. Axiom-checked = Lean core only. (Needs
`open ComplexOrder` in scope — the PSD order does not resolve without it.)
**POLYNOMIAL HALF OF THE CFC CLOSURE DONE (same day)**: `quatConj_one`,
`quatConj_sub`, and **`quatConj_pow` — `Φ` fixes every power of a quaternionic matrix**
(short induction on `quatConj_mul`). Axiom-checked = Lean core only. Combined with
`quatConj_add`/`quatConj_smul_of_conj_eq`, `Φ` therefore fixes `p(A)` for every real
polynomial `p`.
**AND THE BRIDGE LEMMA IS NOW IN** (`Hermitian/CfcPoly.lean`, compiled first try,
axiom-checked = Lean core only): **`mat_cfc_polynomial : (A.cfc (p.eval ·)).mat =
Polynomial.aeval A.mat (p.map (algebraMap ℝ 𝕜))`** — the functional calculus at a
polynomial IS the matrix polynomial. That is exactly what transfers `quatConj_pow` +
additivity to `Φ (A.cfc p) = A.cfc p`, and it is stated over any `RCLike 𝕜`, so it is
reusable well beyond this row.
★**NOTE for the next session — the remaining ANALYTIC half of the gap**: the fixed set's
closure under the FUNCTIONAL CALCULUS (`IsQuaternionic a → IsQuaternionic (a.cfc f)`) is
NOT yet proved, and there is **no square-root uniqueness lemma in the tree or Mathlib** to
get it cheaply (checked). **`quatConj_aeval` AND `quatConj_continuous` NOW DONE** (axiom-checked = Lean core
only): `Φ` fixes every real matrix polynomial in a quaternionic matrix (via
`Polynomial.induction_on'`, `quatConj_pow`, and the fact that real coefficients are
self-conjugate — note `aeval_monomial`'s `algebraMap` lands in the MATRIX algebra, so
convert with `← Algebra.smul_def` rather than casting to ℂ), and `Φ` is continuous (via
`continuous_matrix` entrywise + `Continuous.matrix_mul`).
With those, what is left is the
transfer: `Φ` is continuous and additive (`quatConj_add`/`quatConj_sub`), so a
three-ε estimate against a Weierstrass approximant plus `norm_cfc_sub_le_of_sup_le`
gives `Φ (a.cfc f) = a.cfc f` — the SAME skeleton as
`continuousOn_cfc_sqrt_effects`, which is already in the tree to copy from. ★★**THE REAL SHAPE OF THE REMAINING GAP — found by two backed-out attempts
2026-08-06, and it is a STRUCTURAL point, not a missing lemma.** The transfer needs a
NORM on the objects being estimated, and:
* **bare `Matrix (n⊕n) (n⊕n) ℂ` has NO `Norm` instance in scope** (the Frobenius norm is
  scoped; `HermitianMat` carries its own norm, `Matrix` does not). So an ε-argument
  cannot even be *stated* about `quatConj` as it currently is — a matrix-level map.
* the fix is to restate the whole closure **at the `HermitianMat` level**: `Φ` PRESERVES
  HERMITIAN-NESS (for Hermitian `A` it is the congruence `J₀ Aᵀ J₀ᴴ`, and congruence of a
  Hermitian matrix is Hermitian — `quatConj_posSemidef`'s proof already contains this
  computation), so define `quatConjH : HermitianMat (n⊕n) ℂ → HermitianMat (n⊕n) ℂ` and
  work there, where the norm, the ℝ-linear structure, and `norm_cfc_sub_le_of_sup_le` all
  live.
* with `quatConjH` in hand the bound is FREE and needs no Frobenius computation: `Φ` is
  ℝ-linear (conjugate-linear over ℂ IS ℝ-linear — `quatConj_add` +
  `quatConj_real_smul` are already proved), and an ℝ-linear map on a finite-dimensional
  normed space is automatically continuous and bounded
  (`LinearMap.toContinuousLinearMap` + `le_opNorm`). **Do not attempt the entrywise
  Frobenius-invariance computation** recommended a moment ago — it is unnecessary once the
  statement moves to the Hermitian level.
**AND THAT FIX IS NOW IN, 2026-08-06** (axiom-checked = Lean core only):
`quatConj_isHermitian` (`Φ` preserves Hermitian-ness — for Hermitian `A` it is the
congruence `J₀AᵀJ₀ᴴ` and `Aᵀ` is Hermitian too), **`quatConjH`** (the involution as a
self-map of `H_{2n}(ℂ)`) with `quatConjH_mat`/`_add`/`_smul`, the ℝ-linear packaging
**`quatConjHLm`**, and **`quatConjH_bound` : `∃ K > 0, ∀ A, ‖Φ A‖ ≤ K‖A‖`** — obtained
exactly as predicted, for free from `LinearMap.toContinuousLinearMap` + `le_opNorm` on a
finite-dimensional space, with no Frobenius computation anywhere.
Note on file order: `quatConj_isHermitian` needs `map_conj_eq_transpose` and
`symplecticJ_transpose_eq_conjTranspose`, so the Hermitian-level section must sit AFTER
the positivity section (a first placement before it failed on unknown identifiers).
★★**AND THE CLOSURE IS DONE — 2026-08-06.**
**`HermitianMat.IsQuaternionic.cfc_of_effect` : for a quaternionic effect `A` and `f`
continuous on `[0,1]`, `Φ (A.cfc f) = A.cfc f`** (axiom-checked = Lean core only).
Assembled exactly as forecast: `quatConjH_bound` + `mat_cfc_polynomial` +
`quatConj_aeval` + `norm_cfc_sub_le_of_sup_le` + `exists_polynomial_near_of_continuousOn`,
in the shape of `continuousOn_cfc_sqrt_effects`, closed by `le_of_forall_pos_le_add` and
`norm_le_zero_iff`.
**So `√a` and hence `Q_{√a}` stay inside the quaternionic carrier — the last STRUCTURAL
fact the `H_n(ℍ)` row needed. That row's foundation is now complete**: carrier +
order-unit structure + unital Jordan subalgebra + positivity + functional-calculus
closure, all machine-checked, all inside complex Hermitian matrices.
File-order lesson (hit twice): this file's sections have real dependencies —
`quatConj_isHermitian` needs the positivity section's lemmas, and the closure needs the
Hermitian-level section. Append new sections at the END and move them up only if needed.
★**CORRECTION to the sentence that stood here (my own, one commit earlier): "what remains
is no longer structural" was TOO OPTIMISTIC.** Verified at source: every file in
`Necessity/` states its results over `HermitianMat n 𝕜` — `grep` for an abstract
`[OrderUnitSpace V]` carrier in `Necessity/*.lean` returns **nothing**. So **the Θ chain is
not available on `QuatCarrier`**, and the ℍ row's remaining work is a GENERALIZATION job of
the same kind as the ℝ port, not a short argument.
**What the ℍ row actually needs now, honestly scoped:**
* the Θ construction re-derived over the quaternionic carrier. Two architectures:
  (i) generalize the `Necessity/` chain from `HermitianMat n 𝕜` to an abstract
  "Jordan-subalgebra carrier" (clean, reusable, but touches the ℂ lane — apply the
  submission-artifact rule and use `…Gen` twins, per the 234-site decision); or
  (ii) restrict the existing complex operators to the carrier one at a time —
  `Q_{√a}` DOES restrict (Φ is multiplicative and the carrier is cfc-closed, both now
  proved), so this is viable and touches nothing finished.
* Architecture (ii) is the recommended start: it needs `seqLeftMul` and `quadRepEquiv`
  restricted, which the completed foundation already justifies.
* THEN the ℝ-shaped ending applies, and `eq_one_of_sq_eq_one_of_continuous` from
  `RealRigidity` is reusable verbatim (quaternionic Peirce block is `ℍ`, centre `ℝ`).
**Net: the ℍ row's FOUNDATION is complete and machine-checked; its ARGUMENT is a lane.**
★**Superseded note (kept for provenance), the earlier framing of this gap**: the transfer needs
`Φ` to be norm-BOUNDED, not merely continuous, and neither a Frobenius-invariance lemma
nor a linear-map-bound route is cheaply available here (`Φ` is conjugate-linear, so the
`ℂ`-linear `exists_bound` machinery does not apply, and the vendored `Inner.lean` has
`frobenius_norm_def` but no congruence invariance). A draft using it was written and
REMOVED rather than left with `sorry`s. Two clean options for the next pass: (a) prove
`‖quatConj X‖ = ‖X‖` directly from `frobenius_norm_def` — entrywise, the map permutes and
conjugates entries, so the sum of squared moduli is literally unchanged; that is an
`ext`-level computation, not an operator-theory one; or (b) treat `Φ` as ℝ-linear (it IS
ℝ-linear) and use the real bound machinery. Option (a) is the recommended one and is the
smaller job.
Do NOT reach for PSD-square-root uniqueness: it is absent from both the tree and Mathlib
(checked), so that route costs an extra lemma for no gain.
**Next for the ℍ row**: that cfc closure, then transport a `SequentialProductOn` on the
carrier and run the ℝ-shaped argument — the quaternionic Peirce block is `ℍ`, whose CENTRE is `ℝ`, so the
same "no continuous character into a discrete sign group" kill applies and
**`eq_one_of_sq_eq_one_of_continuous` (from `RealRigidity`) is reusable VERBATIM.**

**If the deliverable needs scoping**: the two finished rows are a defensible artifact —
an unconditional complex classification plus a real row resting on one published
citation. Of the remainder, only H₃(𝕆) is a genuine foundational program.

---

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

- **1.1 Carrier + instances — DECIDED 2026-08-04: VENDOR physlib's HermitianMat
  island** (evaluation report banked; not `lake require` — physlib pins mathlib
  v4.32 and is fast-moving, which would chain our zero-sorry claim to a live
  upstream; not reimplement — their design is the one we'd pick and the CFC
  plumbing is ~2kL already done). Vendored 2026-08-04: 17 files ≈ 7kL from
  physlib @ `ad1d812` (Apache-2.0, headers retained) into
  `RadicalRelativity/Vendor/` — carrier `HermitianMat n α :=
  selfAdjoint (Matrix n n α)` (opaque def synonym), Loewner `PartialOrder` via
  scoped MatrixOrder, trace inner product + Frobenius `NormedSpace ℝ` +
  `CompleteSpace`, `HermitianMat.cfc` (ℝ→ℝ) with continuity block,
  `symmMul` Jordan product + scoped `HermMul` `IsCommJordan` instance,
  `Proj.lean` (projectors, posPart/negPart, `{A ≤ₚ B}`). Provenance + edit log:
  `RadicalRelativity/Vendor/VENDOR.md`. **Backport v4.32→v4.28 DONE 2026-08-04**
  (drift log in VENDOR.md; zero statement changes; gates verified first-hand:
  build green, census 44 modules / one axiom). **What the vendor does NOT give (= 1.1's
  remaining work):** order-unit norm (the `Norm` slot is occupied by Frobenius
  — the OU norm must be an unbundled def or type synonym, NEVER a competing
  instance), order unit + Archimedean statements (`le_trace_smul_one`,
  `lt_smul_of_norm_lt` are the starting bounds), an effect-interval object
  (only `unitInterval_IsCompact` exists), extreme-points-are-projections
  (feeds M3 bridge 1), and everything Jordan-structural past the `IsCommJordan`
  mixin. Risk LOW-MED (backport residue).
  **Order-unit layer DONE 2026-08-04** (`Hermitian/OrderUnit.lean` +
  `Hermitian/ExtremeEffects.lean`; census green at 46 modules, one axiom): the
  OU norm as an unbundled def with the defining infimum ATTAINED via the closed
  PSD cone (`isClosed_nonneg` + `IsClosed.csInf_mem` — no eigenvalue
  bookkeeping, `RCLike`-uniform) plus minimality / `ouNorm ≤ Frobenius` / neg /
  triangle / definiteness; order-unit boundedness with witness `r = ‖a‖`
  (`lt_smul_of_norm_lt`); the FULL Archimedean property over ℂ (eigenvalue
  route); `instance OrderUnitSpace (HermitianMat n 𝕜)` whose parents are the
  existing vendored instances (no second normed/order structure) and under
  which `OrderUnitSpace.IsEffect` is DEFINITIONALLY the Loewner `[0,1]`
  (`isEffect_iff := Iff.rfl`; `unitInterval_IsCompact` restates verbatim; the
  abstract `Effect V` subtype now instantiates on the carrier); and
  extreme-points-of-`[0,1]` = projections (`p^2 = p`): forward direction
  𝕜-uniform (quadratic-form kernel pinch, `dotProduct_mulVec_zero_iff`),
  converse over ℂ fully CFC-native (perturb by `± min(x, 1-x)` through
  `HermitianMat.cfc`; extremeness kills the perturbation; spectrum lands in
  `{0,1}` — zero eigenvector-basis bookkeeping). Feeds M3 bridge 1.
  **1.1 is CLOSED**; the only norm item left anywhere is the 1.4 equivalence.
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
  **DECIDED 2026-08-04: route (a), pair-of-real-cfc** — the S1–S7 statements
  live on `HermitianMat` (the 1.1 `OrderUnitSpace` instance), so route (b)
  would add a parallel carrier plus an order/positivity transfer layer while
  offering no cpow API to harvest (inventory-confirmed absent); and the
  vendored `HermitianMat.conj` AddMonoidHom makes the twist product
  `b.conj (twistFactor a t)` with S1-additivity, monotonicity, positivity, and
  effect closure riding `map_add`/`conj_mono`/`conj_nonneg` directly. The
  paper's `0^{1/2±it} = 0` convention is DEFINITIONAL on this route: every
  component is `√x·(…)`, which vanishes at `x = 0` regardless of the
  `Real.log 0 = 0` junk value. Implemented in `Hermitian/Twist.lean`:
  `twistRe`/`twistIm`/`twistFactor` (= `a^{1/2+it}` as a plain matrix),
  `twistSeq t a b := b.conj (twistFactor a t)`, with `Xᴴ = twistFactor a (-t)`,
  `X·Xᴴ = Xᴴ·X = a.mat` (on `0 ≤ a`; Pythagorean cancellation through
  `cfc_self_commute` + `cfc_congr_of_nonneg`), `twistFactor 1 t = 1`,
  unit laws `a &ₜ 1 = a` / `1 &ₜ b = b`, positivity, right-additivity,
  right-monotonicity, effect closure, and `twistSeq 0 a b = √a·b·√a` (Lüders).
  **1.2 definitional layer DONE 2026-08-04** (census 47, gates green). What
  moves to 1.3: S4 zero-symmetry, S5 compatible associativity, S6a/S6b, S7,
  and packaging as a `SequentialProductCore (HermitianMat n ℂ)` instance
  (plus S2 continuity from `conj` continuity in the carried norm).
- **1.3 S1–S7 verification.** [INV✓]: cfc identity suite is rich (`cfc_mul`,
  `cfc_comp'`, `cfc_pow`, order lemmas `cfc_mono`/`cfc_le_iff`, commutation
  `Commute.cfc`, norms `norm_cfc`). The SymPy V1–V10 checks are the
  computational shadow; each becomes a lemma. Risk LOW, volume moderate.
  **DONE 2026-08-05** (`Hermitian/Resolution.lean` + `Hermitian/Sequential.lean`;
  census green at 49 modules, one axiom; paper row `lem:twist-sufficiency` now in
  THEOREM-MAP §1, unconditional — no §2 interface structures in its closure).
  Proof architecture, chosen to avoid ALL simultaneous-diagonalization machinery
  (none exists in Mathlib for matrices):
  (i) *Resolution layer*: `specProj a μ := a.cfc 1_{x=μ}` (matrix cfc needs no
  continuity, so indicators are legal), `mat_cfc_eq_sum_specProj` (every cfc
  expands over the value-indexed family, by cfc-congruence on the spectrum plus
  linearity), and `mat_cfc_of_resolution` — cfc respects ANY pairwise-orthogonal
  idempotent presentation `M = Σ cᵢ•Rᵢ`, by Lagrange interpolation at the nodes
  `{cᵢ} ∪ σ(M)` (`Mathlib.LinearAlgebra.Lagrange`) reducing to the polynomial
  case, which is ring algebra.
  (ii) *Compat ⟹ commute* (the Gudder–Nagy trick at general twist): from
  `a &ₜ b = b &ₜ a`, the Frobenius certificate `C := b^{1/2+it}·a − a·b^{1/2+it}`
  has `tr(C·Cᴴ) = 2tr(ba²) − τ − τ̄ = 0` (where `τ = tr((b &ₜ a)·a)` equals
  `tr(ba²)` by the hypothesis plus the one-variable identity
  `tr((a &ₜ b)·a) = tr(ba²)`), so `C = 0` via
  `Matrix.trace_mul_conjTranspose_self_eq_zero_iff`; conjugate-transposing gives
  commutation with `b^{1/2-it}` too, and their product is `b`. No Fuglede, no
  spectral theory.
  (iii) *Commute ⟹ compat + value*: `a &ₜ b = a·b` for commuting pairs rides the
  vendored `Commute.cfc_right` — free.
  (iv) *S5*: reduces to `(ab)^{1/2+it} = a^{1/2+it}·b^{1/2+it}` on commuting
  positives (`twistFactor_mul_of_commute`): present `ab` by the JOINT family
  `P_μ·Q_ν` (products of the two spectral-projection families — commuting
  orthogonal idempotents summing to 1), apply the resolution lemma, and finish
  with the scalar character law `g(μν) = g(μ)g(ν)` on `[0,∞)` — the paper's
  `g(0) = 0` convention makes the zero-eigenvalue cases definitional.
  (v) *S4*: trace route — `tr(a &ₜ b) = tr(b·a)`, trace symmetry, PSD +
  trace-zero ⟹ zero (eigenvalue sum). (vi) *S6a/S6b/S7*: one-line consequences
  of (ii)+(iii) and `Commute` algebra. (vii) *S2*: GLOBAL norm continuity of
  `a ↦ a &ₜ b` — the component functions `√x·cos/sin(t·log x)` are continuous on
  all of ℝ (squeeze `|√x·c| ≤ √x` at the spectral origin; the junk values for
  `x < 0` vanish identically), then the vendored `HermitianMat.cfc_continuous` +
  `Continuous.matrix_mul`. Packaged as `twistSequentialProductCore t` /
  `twistSequentialProduct t` (defs per twist parameter, parents = the 1.1
  instance; `IsEffect`/`ousUnit` discharge definitionally). The V1–V10 shadow is
  superseded pointwise by these lemmas on the n≥3 side; V9/V10's rank-two content
  was already in `MasterTheorem/RankTwo.lean`.
- **1.4 (S2) norm caveat discharge.** Prove order-unit norm ≡ carried norm on
  the finite-dim instance (all norms equivalent, Mathlib has finite-dim
  equivalence) — closes THEOREM-MAP's S2 literal-fidelity caveat. Risk LOW.
  Half done 2026-08-04: `ouNorm_le_norm` (OU ≤ Frobenius) is proved.
  **DONE 2026-08-05** (same-day as 1.3; census unchanged at 49): the reverse
  comparison `norm_le_sqrt_card_mul_ouNorm : ‖a‖ ≤ √(card n) · ouNorm a` via
  `abs_eigenvalues_le_ouNorm` (upper bound from the attained `le_ouNorm_smul_one`
  + vendored `le_smul_one_imp_eigenvalues_le`; lower bound through `-a` and the
  `cfc_eigenvalues` permutation — no new spectral machinery) and
  `norm_eq_sum_eigenvalues_sq`; plus the paper-facing transfer
  `twistSeq_continuousAt_ouNorm` (ε–δ first-argument continuity of the twist
  product IN THE ORDER-UNIT NORM, `Hermitian/Sequential.lean`), which is the
  literal (S2) reading on the concrete carrier. smul homogeneity of `ouNorm`
  was NOT needed (the ε–δ route uses only the two inequalities) — not proved,
  by design. **M1 IS COMPLETE.**

## M2 — Complex necessity core

- **2.1 Θ construction (vdW Prop 5.2/5.3) — CLOSED 2026-08-05 (all six units
  2.1a–2.1f below).** Define `Θ_a := Q_{√a}⁻¹ ∘ L_a` on
  invertible effects; prove unital linear order-iso. Matrix-concrete. Risk MED.
  **First unit DONE 2026-08-05 — `lem:homog`(i)** (`Necessity/LeftMultiplication.lean`,
  census 50, gates green): for an ARBITRARY product on the carrier, `seqLeftMul P a`
  is the positive linear extension of `b ↦ P.sp a b` to all of `H_n(ℂ)`, with
  effect-agreement, positivity, monotonicity, and the unit law
  `seqLeftMul P a 1 = a`. Ladder: ℕ→ℚ homogeneity by finite additivity (S1 only),
  ℝ-homogeneity by the rational order squeeze closed with
  `le_zero_of_forall_le_smul_one` (this is where the full Archimedean property
  earns its keep), cone extension normalized by `‖x‖+1` with normalization
  independence, and the `posPart/negPart` difference construction with a
  representation-independence lemma (`spPos_sub_congr`). NO S2 used — matches the
  paper's hypothesis accounting for lem:homog(i).
  **DESIGN DECISION (binding for all of M2–M5): the unknown product is
  `SequentialProductOn V` — the S1/S3–S7 fields over the AMBIENT `[OrderUnitSpace V]`
  (added to `SequentialProduct.lean`, with `toCore` bridging to the derived-lemma
  layer; parent definitionally the ambient instance).** An instance-quantified
  `[SequentialProductCore (HermitianMat n ℂ)]` is WRONG for necessity statements:
  it bundles its own `toOrderUnitSpace`, which the elaborator treats as unrelated
  to the carrier's canonical instance, so no carrier order/norm/spectral lemma
  applies (discovered as an instance-mismatch wall at the first 2.1 build). The
  final per-type `mthm:master` statements must quantify over
  `SequentialProductOn (HermitianMat n ℂ)` + unbundled S2 for the same reason.
  **(2.1b) DONE 2026-08-05** (`Necessity/FirstArgument.lean`, census 51, gates
  green): `sp_smul_left` = lem:homog(ii), first-argument homogeneity for
  `t ∈ [0,1]`, with the compat ladder `sp_comm_nat_smul` (iterated S6b),
  `sp_comm_rat_smul_self` (1/k-piece ladder both directions),
  `sp_comm_rat_one_smul` (orthocomplement + S6a flip + S6b assembly),
  `sp_rat_one_smul_left` (rational value law), and `sp_smul_one_left` = the
  SINGLE S2 use (rational sequence in the first argument, ContinuousWithinAt
  composed with `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`,
  `tendsto_nhds_unique` closes). Traps: interface fields produce `ousUnit`
  forms — rewrite `HermitianMat.ousUnit_eq_one` before matching, and phrase
  effect-of-1 / unit-law facts as `have h : … (1 : HermitianMat n ℂ) … := ⟨abstract⟩`
  so unification binds `1` not `ousUnit`; pin
  `tendsto_one_div_add_atTop_nhds_zero_nat`'s carrier by ascription before use.
  Remaining in 2.1 — **PROOF PLAN DECODED AT SOURCE 2026-08-05**
  (arXiv:1803.08453 = Wetering2018three, fetched via curl+pdftotext; §3.9, §4.17–4.22,
  §5.2–5.7 read in full). Unit ladder, in dependency order:
  (2.1b) **lem:homog(ii) = first-argument homogeneity** `(λa)◦'b = λ(a◦'b)`,
  λ ∈ [0,1] — vdW 3.9 adapted: (i) rational-multiples self-compat ladder
  `qa |' a` by iterated S6b from `(1/n)a |' (1/n)a`; (ii) `qa⊥ |' a⊥` same, then
  S6a gives `qa⊥ |' a`; (iii) S6b: `a |' (qa + qa⊥) = q·1`, and
  `(q1)◦'a = a◦'(q1) = qa` by second-arg homogeneity (HAVE) + unit law;
  (iv) the ONLY S2 use: `(λ1)◦'b = λb` by rational approximation in the first
  argument (qᵢ1 → λ1 in norm, S2 passes the limit); `a |' λ1` then holds since
  both sides equal λa by (iii)-style computation, NO normality needed;
  (v) S5 with `a |' λ1`: `(λa)◦'b = (a◦'(λ1))◦'b = a◦'((λ1)◦'b) = a◦'(λb) = λ(a◦'b)`.
  (2.1c) **Sharp-effect base layer — DONE 2026-08-05**
  (`Necessity/SharpEffects.lean`, census 52, gates green): `proj_pinch`
  (product-independent sharpness of projections by two conjugation pinches +
  the √e Frobenius kill), `sp_proj_compl`/`sp_proj_self` (p◦'(1−p) = 0 and
  p◦'p = p — S6a applied to the TRIVIAL self-compat `p |' p` makes the two S1
  splittings pinch it; this is the whole Gudder–Greechie sharpness theorem in
  ~20 lines on the carrier), `orth_compl_isProjection`/`proj_orth_le_one_sub`
  (1−p−q is a projection when pq = 0), `sp_proj_orth`/`sp_proj_orth'` (S4 for
  the flip), `sp_comm_proj_orth`. No S2 anywhere in this unit.
  (2.1d) **vdW 5.2 transfer on matrices — DONE 2026-08-05** (appended to
  `Necessity/SharpEffects.lean`, census unchanged 52, gates green):
  `sp_orthFamily_value` — over any pairwise-orthogonal projection family,
  `(∑λᵢ•pᵢ) ◦' (∑μᵢ•pᵢ) = ∑(λᵢμᵢ)•pᵢ` (the STANDARD value) for any S1–S7+S2
  product — and `sp_orthFamily_comm` (compatibility transfer). Supporting:
  `sum_proj_isProjection` (rides Resolution's `resolution_mul` with x=y=1),
  `sum_smul_proj_isEffect`, `sp_sum_right` (S1 over families, dominated-sum
  side conditions via `Finset.sum_le_sum_of_subset_of_nonneg`),
  `sp_add_left_of_comm` + `sp_comm_sum` + `sp_sum_left_of_comm` (first-argument
  additivity over compatible summands: S6b-fold then S1-flip — NOT an axiom).
  S2 enters only through `sp_smul_left`. The pseudo-inverse compatibility
  `b |' ν` is now an instantiation: both are diagonal in b's `specProj` family
  (2.1e wires it).
  (2.1e) **Pseudo-inverse + order reflection — DONE 2026-08-05**
  (`Necessity/PseudoInverse.lean`, census 53, gates green): `pseudoInv b :=
  ∑(c/μ)•specProj b μ` with the normalization `c := ∏ μ` (0 < c ≤ μ with NO
  nonemptiness split — the erase-product trick); `sp_pseudoInv_eq_smul_one`
  (`ν◦'b = c•1` via the 2.1d value law after `rw [sum_smul_specProj] at hval`
  — conv-rewriting b would loop the pattern into pseudoInv's own b);
  `sp_pseudoInv_cancel` (S5 + first-arg homog + S3); `span_isEffect_eq_top`;
  `seqLeftMul_pseudoInv_comp` (`L'_ν ∘ L'_b = c·id` via `LinearMap.ext_on`,
  which at this pin takes `span = ⊤` directly); `seqLeftMul_reflectsNonneg` +
  `seqLeftMul_injective`. Surjectivity deferred to 2.1f (finite-dim
  injective ⟹ bijective at the LinearEquiv packaging).
  (2.1f) **Θ assembly — DONE 2026-08-05, and with it 2.1 IS CLOSED**
  (`Necessity/Theta.lean`, census 54, gates green; compiled clean on the first
  pass): `quadRepEquiv` (`Q_{√a}` as a `LinearEquiv` via vendored `conjLinear`;
  inverse = conj at `(√·)⁻¹` through `cfc_congr_of_posDef`, no `NonSingular`
  machinery needed — `conj_conj_mat` composes conjugations); `theta P ha hbd :=
  Q⁻¹ ∘ₗ seqLeftMul`, `quadRep_theta` (the paper's defining equation
  `L'_a = Q_{√a} Θ_a`), `thetaEquiv` (injective from 2.1e cancellation,
  surjective by `LinearMap.injective_iff_surjective` + the vendored
  `FiniteDimensional` instance), `theta_one` (UNITAL, vdW 5.3), and
  `theta_nonneg_iff`/`theta_le_iff` (ORDER ISO both directions: forward =
  2.1e reflection, backward = conj positivity). `Θ_fix` (vdW 5.5) = 2.2 next
  (via the JOINT specProj family of two commuting effects, both diagonal in it —
  same construction as M1's `twistFactor_mul_of_commute` family);
  `Θ_cocycle` = 2.4 (needs only Lüders invariance, no Kadison). `Θ_jordan`
  stays M3. vdW 5.3's quotient universal property was never needed; 5.4
  (`Θ_{λq} = Θ_q`) is 2.3 and falls out of (2.1b).
- **2.2 Θ_fix (vdW 5.5) + span extension.** Effect-level fixing + extension to
  J by linearity (the span argument the paper supplies). Risk MED.
  **Effect-level fixing DONE 2026-08-05** (`Necessity/ThetaFix.lean`, census 55,
  gates green): `jointProj` (the joint spectral family `P_μ·Q_ν` of a commuting
  pair — Hermitian by commutation, projections, pairwise orthogonal), the padding
  lemmas (`sum_smul_specProj_pad`/`_pad_left`: any `cfc` of one factor is
  diagonal in the joint family), `a_eq_sum_jointProj`/`b_eq_sum_jointProj`,
  `sp_eq_quadRep_of_commute` (**the unknown product takes the standard Lüders
  value on commuting pairs**: unknown side = 2.1d value law over the joint
  family; standard side = two `resolution_mul` passes + `√μ·ν·√μ = μν`), and
  `theta_fix : Θ_a b = b` by cancelling `Q_{√a}` through `quadRep_theta`.
  The span extension to all of J is definitionally free here (Θ is already a
  total linear map — vdW needed the span argument only because his Θ lived on
  an order ideal). Traps: no `Finset.sum_product_comm` at this pin (use
  `Finset.sum_product` + `Finset.sum_comm`); inside a `set s := …` scope, state
  `show`-terms over `s` so `rw` matches syntactically (ascription checks by
  defeq, rewriting does not).
- **2.3 cone-ext (Θ_{λq} = Θ_q normalization).** Cheap once 2.1 lands. LOW.
  **DONE 2026-08-05** (appended to `Necessity/Theta.lean` + `Hermitian/Resolution.lean`,
  census unchanged 55, gates green): `theta_smul : Θ_{t•a} = Θ_a` for `t ∈ (0,1]`
  (vdW 5.4), by cancelling through `quadRepEquiv_smul` (`Q_{√(t•a)} = t•Q_{√a}`,
  via the NEW general `HermitianMat.cfc_smul_arg : (r•a).cfc f = a.cfc (f (r·))`
  — another resolution-lemma payoff, no sign hypothesis) and `seqLeftMul_smul`
  (first-argument homogeneity at the linear-map level, ext_on the effect span).
  So Θ extends scale-invariantly to the whole positive-definite cone.
- **2.4 Θ_cocycle (vdW 5.7, commuting diagonal family).** Matrix-concrete
  computation in the joint eigenbasis. Risk MED.
  **DONE 2026-08-05** (`Necessity/ThetaCocycle.lean`, census 56, gates green) —
  with the honest hypothesis accounting made explicit: vdW's 5.7(1) exchange
  consumes invariance of the standard product under unital order isos, which IS
  the Kadison content the campaign carries as `Θ_jordan` (M3). So the file
  proves unconditionally: `conj_eq_jordan` (the fundamental identity
  `s·y·s = 2 s∘(s∘y) − (s∘s)∘y`, closed by the `module` tactic after
  association-normalization), `sqrt_isEffect`, `sp_comm_of_commute` (commuting
  effects are ◦'-compatible, joint family, no PosDef), `seqLeftMul_mul_of_commute`
  (the S5 splitting `L'_{a◦'b} = L'_a∘L'_b`), `quadRepEquiv_mul_of_commute`
  (`Q_{√(ab)} = Q_{√a}∘Q_{√b}` — DIRECT REUSE of M1's
  `twistFactor_mul_of_commute` at `t = 0`); and conditionally on
  `PreservesJordan Θ`: `theta_conj_exchange` (5.7(1)) and
  `theta_cocycle_of_preservesJordan` (5.7(2), `Θ_m = Θ_a∘Θ_b`). At
  instantiation the condition is fed by the same `Θ_jordan` field the
  ComparisonSetup already carries — no NEW import, no circularity (both fields
  discharged independently: Θ_jordan by M3, Θ_cocycle by this + M3).
- **2.5 frame_opCommute + simDiag_opCommute (FK facts).** Direct block-form
  computations on matrices. LOW.
  **Concrete kit DONE 2026-08-05** (appended to `Necessity/ThetaCocycle.lean`,
  census unchanged 56, gates green): `symmMul_opCommute_of_commute` (matrix
  commutation ⟹ Jordan operator commutation `a∘(b∘·) = b∘(a∘·)` — targeted
  assoc-rewrites + `module`; this discharges BOTH opCommute fields since the
  concrete frame/diagonal/scalar elements all matrix-commute) and
  `conj_eq_self_of_symmMul_eq_self` (Peirce compression: `e∘x = x ⟹ e·x·e = x`,
  the `J₂(e)`-membership normal form for `block_mem_J2`). Instantiation-time
  predicate choices recorded: `J2 i j b := q·b·q = b`, `ScalarOn i j a :=
  ∃ lam a₀, a = lam•q + a₀ ∧ q·a₀ = 0 ∧ a₀·q = 0` (q = pᵢ+pⱼ), under which
  `simDiag_opCommute` reduces to a two-line matrix-commute check and
  `aOf_scalarOn` is the diagonal split at `rᵢ = rⱼ`.
- **2.6 THE ANALYTIC CORE: dχAdd + continuity + coalescence_diff.** Construct
  the character χ̃ from Θ on the orthant (group-level pieces `chi_hom`,
  `chi_comm`, `chi_extend_wellDefined` already proved), extend to ℝⁿ,
  differentiate. Continuous-additive⟹linear is PRESENT
  (`AddMonoidHom.toRealLinearMap` [INV✓]); the differentiation/smoothing of χ̃
  itself is bespoke analysis — the single largest M2 line-count risk. Risk
  HIGH (budget, not feasibility).
  **GENERIC CORE DONE 2026-08-05** (appended to `Necessity/OneParameter.lean`,
  census 57 unchanged, gates green — closure pure Lean core):
  `multiParameter_eq_exp` — a multiplicative family `χ : E → 𝔸` (E any real
  vector space) with `χ 0 = 1` and continuity ALONG LINES equals
  `r ↦ exp (D r)` for a unique LINEAR `D`. **The risk-HIGH item collapsed**:
  the line generators from `oneParameter_eq_exp` are ℝ-homogeneous and
  additive BY THE UNIQUENESS CLAUSE (reparametrize / merge commuting
  exponentials via `commute_of_commute_exp`, generators of commuting flows
  commute by differentiating twice), so linearity needs NO continuity input —
  Cartan smoothness is free, and `dχAdd_cont` is then automatic on the
  finite-dimensional source (`LinearMap.continuous_of_finiteDimensional`).
  REMAINING in 2.6 (instantiation side): build χ̃ from Θ on the concrete
  carrier (2.4's cocycle + `thetaEquiv` inverses per `chi_extend_wellDefined`),
  verify line-continuity from S2, choose the concrete ρ/Stab, and derive
  `coalescence_diff` from the group-level coalescence by differentiating the
  fixed-subspace property (the derivative of a curve constant on V_ij has
  vanishing V_ij-component). First instantiation ingredient DONE 2026-08-05:
  `theta_base_one` (`Necessity/Theta.lean`) — `Θ_1 = id` (χ̃(0) = 1), from S3
  and `cfc_apply_one`. Second ingredient DONE 2026-08-05:
  `Necessity/DiagonalFamily.lean` (census 58) — `frameProj` (standard frame:
  projections, orthogonality, `∑ = 1` via `Matrix.diagonalAddMonoidHom`
  map_sum) and `diagFamily r = diag(exp rᵢ)` (semigroup law `diagFamily_mul`,
  PosDef everywhere, effects on the negative orthant, frame decomposition
  `diagFamily_eq_sum_frameProj`, frame commutation) — the concrete `p`/`aOf`
  data for ComparisonSetup. Traps: vendored `HermitianMat.diagonal 𝕜 f` takes
  𝕜 explicitly but `diagonal_mat`/`diagonal_one` take it implicitly; no
  `Matrix.diagonal_sum` at pin — use `map_sum diagonalAddMonoidHom`;
  `Matrix.PosSemidef.diagonal` wants the Pi-order `0 ≤ d` (show-normalize
  `0 i`); rw cannot rewrite under `∑`-binders — `simp only [show …]`.
  **WIRING EXECUTED 2026-08-05** (`Necessity/ComparisonInstance.lean`, census 60,
  gates green): `comparisonSetup {N} (hN : 3 ≤ N) (P) (hS2) (hjord :
  ThetaPreservesJordan P) : ComparisonSetup (HermitianMat (Fin N) ℂ)` — every
  interface field discharged by a proved theorem except `Θ_jordan := hjord` (the
  isolated M3 import). Upgraded-from-cited-to-PROVED along the way: the FK/vdW
  **compatibility bridge** `opCommute_iff_commute` (quarter identity
  `[L_a,L_b]y = ¼[[a,b],y]`; commutator commutes with all Hermitians ⟹ scalar via
  `Matrix.mem_range_scalar_of_commute_single` ⟹ traceless ⟹ 0), the
  **span-extended vdW 5.5** `theta_fix_general` (posPart/negPart + normalization
  cancel), and `thetaNorm` (Θ total on PosDef via the 2.3 normalization law —
  vdW 5.4's raison d'être). Downstream abstract layers (`Coalescence`,
  `DiagonalHom`) now instantiate on the concrete carrier through this def.
  Traps: HermitianMat is a subtype ⟹ posPart dot-notation resolves to `Subtype.*`
  (use `b⁺`/`b⁻` notation; lemmas are `posPart_eq_cfc_max`/`negPart_eq_cfc_min`);
  `dite` on PosDef needs `letI := Classical.dec`; the (r+r')-orthant proof must be
  ascribed `∀ i, (r + r') i ≤ 0` or unification pins `fun i => r i + r' i` (H7).

  **χ̃ PART 2a DONE 2026-08-05** (`Necessity/ChiExtension.lean`, census 61, gates
  green): `thetaUnit r` (comparison map as a UNIT of End(H_n(ℂ)) — total in r,
  inverse carried by the LinearEquiv, no operator inversion), units-level
  cocycle + abelian image, `thetaUnit_div_eq` (representative-freedom of
  Θ_s Θ_t⁻¹ — the paper's well-definedness argument, done in the units group
  with `group` + two Commute-swaps), and `chiTilde r := thetaUnit (r ⊓ 0) *
  (thetaUnit (r ⊓ 0 − r))⁻¹` — case-free canonical representative — with
  `chiTilde_add` (homomorphism on all of ℝⁿ), `chiTilde_zero`,
  `chiTilde_of_nonpos`. All conditional on `ThetaPreservesJordan` where the
  cocycle enters, as everywhere in this lane. Remaining for 2.6:
  part 2b = line-continuity of `t ↦ (chiTilde (t•v)).val` (S2 for the L'-part
  on effects; explicit diagonal cfc for the Q⁻¹-part; `Ring.inverse`-continuity
  at units for the inverse factor; `continuous_clm_apply` findim reduction),
  part 2c = `multiParameter_eq_exp` ⟹ linear dχ with `χ̃ r = exp (dχ r)`;
  then ρ/coalescence_diff/Setup instantiations.

  **χ̃ PARTS 2b+2c DONE 2026-08-05** (`Necessity/ChiContinuity.lean`, census 62,
  gates green): the ANALYTIC HALF of `lem:homomorphism`, which the interface
  docstrings explicitly scope out of the abstract tree, is now machine-checked
  on the concrete carrier. Continuity ladder: S2 `ContinuousOn` composed with
  the effect-valued diagonal curve (`comp_continuous`) → `spPos` → `seqLeftMul`
  (posPart-split, all `show`-rfl unfolds) → `theta` (Q⁻¹-part = EXPLICIT
  diagonal conj via `cfc_diagonal`, `Continuous.matrix_diagonal/_mul/
  _conjTranspose`) → `thetaUnit.val` (`continuous_clm_apply` findim reduction)
  → inverse factor (`Ring.inverse_unit` + `NormedRing.inverse_continuousAt`) →
  `continuous_chiTilde_line`. Then `chiTilde_eq_exp` = `multiParameter_eq_exp`
  at 𝔸 := End(H_n(ℂ)): ∃! LINEAR dχ with χ̃(r) = exp(dχ(r)); `dChi` = the data.
  The abstract `dχAdd`/`dχAdd_cont` fields are thereby PROVED for the intended
  instance (a linear map is additive; findim linear is continuous).
  TRAPS (all resolved, remember these): (1) CLM's ambient TopologicalSpace =
  strong topology ≠ (syntactically) the norm topology — `IsTopologicalRing`/
  `ContinuousMul` DO NOT synthesize although plain-`rfl` proves the topologies
  defeq at default transparency; registered a local Prop-mixin instance
  `IsTopologicalRing (H →L H)` via `by exact @NonUnitalSeminormedRing.
  toIsTopologicalRing _ _` (explicit type arg, else stuck metas). (2) The Units
  instance diamond: `ˣ` elaborates over `ContinuousLinearMap.monoidWithZero`,
  `NormedRing.inverse_continuousAt` over `NormedRing.toRing`-path — rigid
  unification REFUSES though `Ring.inverse`-A = `Ring.inverse`-B by plain rfl;
  fix = repackage the unit field-by-field ⟨val, inv, val_inv, inv_val⟩ inside
  `by exact`. (3) `ContinuousAt.comp` higher-order unification grabs
  `f := Units.val` from a coerced point — pin `(f := …) (x := t₀)` explicitly.
  (4) `import Mathlib.Analysis.Normed.Ring.Lemmas` required for the
  seminormed→topological-ring instance at all.
  Remaining for 2.6: coalescence_diff (differentiate the fixed-subspace
  property: exp(t·dχ(r)) fixes the {i,j}-block when rᵢ = rⱼ ⟹ dχ(r) kills it),
  concrete ρ (block compression), CoalescenceSetup/DiagonalHomSetup wiring.

  **COALESCENCE INSTANCE DONE 2026-08-05** (`Necessity/CoalescenceInstance.lean`,
  census 63, gates green): `coalescenceSetup` extends `comparisonSetup`; all
  three FK fields DISCHARGED. `cornerQ i j` = diagonal indicator of {i,j}
  (idempotent for ALL i j incl. i = j — this dodges the i=j degenerate case the
  abstract field quantifies over); `simDiag_opCommute` (the FK
  simultaneous-diagonalization citation) reduced to: q absorbs J2(q)-elements
  (qbq = b + q² = q ⟹ qb = bq = b), so (λq + a₀)b = λb = b(λq + a₀);
  `aOf_scalarOn` = diagonal split-off; `block_mem_J2` = PURE RING ALGEBRA:
  Σ_{k∉{i,j}} Peirce-annihilations give (1−q)x + x(1−q) = 0 ⟹ qx + xq = 2x,
  then q-multiplications + idempotence give qxq = qx = xq ⟹ 2qxq = 2x. The
  abstract `coalescence_J2q`/`coalescence_block`/`block_preserved` now hold
  concretely. Trap notes: `Matrix.diagonal_add` is stated sum-on-LEFT (use
  FORWARD rw to merge diagonal sums); `IsBlockElt` is Fin-hardwired (state
  concrete lemmas over general index n via the raw relations, wrap at Fin N);
  mixed ℝ/ℂ-smul chains — convert (1/2:ℝ)• to (2:ℂ)⁻¹• entrywise
  (`Complex.real_smul`) BEFORE cancelling; rw rewrites ALL occurrences (use
  nth_rewrite when combining hqx/hxq). Remaining 2.6: DiagonalHomSetup's
  differential face (ρ, ρ_skew, coalescence_diff — the Stab-design question in
  the memory note) + dχAdd/dχAdd_cont (ALREADY PROVED via dChi: linear ⟹
  additive, findim ⟹ continuous).

  **ℂ-LANE ENDGAME DESIGN (banked 2026-08-05, after reading
  Branches/Complex.lean consumption).** `complex_perFrame_rho` consumes a
  StabilizerCoupling + the TORUS MODEL `hmodel : ρ_{ij}(dχ r) = (θᵢ(r) −
  θⱼ(r)) • J` — the model is MORE than the coupling (per-index characters θᵢ,
  not per-pair). Decoded discharge route, in order:
  (u1) **ouNorm-isometry of Θ** (order-iso + unital ⟹ preserves order-unit
  intervals ⟹ ouNorm-isometric) — cheap, uses the M1 ouNorm kit.
  (u2) **Block ouNorm = Euclidean**: on V_{ij}, x = zE_ij + z̄E_ji has
  x² = |z|²(E_ii + E_jj), so ouNorm x = |z| — the block order-unit norm IS the
  ℝ²-norm. Skewness mechanism: exp(t·dχ) preserves blocks + is
  ouNorm-isometric ⟹ block restriction is a Euclidean isometry group ⟹
  generator skew (d/dt ‖exp(tT)v‖² = 0 at t = 0). NO trace-preservation, NO
  compactness import.
  (u3) **dχ(r) preserves blocks** (differentiate concrete block-preservation).
  (u4) **coalescence_diff — STRONG form** (dχ(r) kills the block pointwise
  when rᵢ = rⱼ): χ̃(t•r) fixes corner elements ∀t (corner_commute +
  thetaNorm-fix at both canonical exponents, which inherit rᵢ = rⱼ), and
  exp(t•dχ(r))x ≡ x differentiates to dχ(r)x = 0 (hasDerivAt_exp_smul_const +
  CLM-apply + constant-curve uniqueness).
  (u5) **Stab := the submodule of block-skew CLMs**; ρ i j := block
  compression via ε_{ij}/β_{ij} (ℝ² coordinates a+bi ↦ zE_ij + z̄E_ji);
  ρ_skew holds ∀ξ ∈ Stab BY MEMBERSHIP; dχ(r) ∈ Stab by u2/u3.
  DiagonalHomSetup instance: dχAdd := (dChi …).toAddMonoidHom, dχAdd_cont by
  findim, coalescence_diff from u4 (compression of a pointwise-killed block).
  (u6) **hmodel via the phase cocycle**: V_ij ∘ V_jk ⊆ V_ik with the ℂ-mult
  formula (zE_ij + z̄E_ji)∘(wE_jk + w̄E_kj) = ½(zwE_ik + conj), so hjord forces
  the block rotations to satisfy R_ik(zw) = R_ij(z)·R_jk(w); orthogonal +
  multiplicative + connected-to-identity ⟹ R_ij = rotation by φ_{ij} with
  φ_{ij} + φ_{jk} = φ_{ik} ⟹ φ_{ij} = θᵢ − θⱼ (anchor θᵢ := φ_{i,i₀}). This is
  the paper's torus identification, machine-checkable without classifying
  Aut(H_n(ℂ)).

  **u4 (coalescence_diff) DONE 2026-08-05** (`Necessity/CoalescenceDiff.lean`,
  census 64, gates green): `dChi_kills_corner` — when rᵢ = rⱼ the differential
  ANNIHILATES the Peirce-2 corner pointwise (strong form; any compression ρ
  then discharges the abstract field). Chain: both canonical exponents of
  χ̃(t•r) inherit the coalescence → `corner_commute` + `thetaNorm_fix_of_commute`
  (+ inverse-fix through the LinearEquiv) → χ̃(t•r) x ≡ x → `exp_apply_const_kill`
  (hasDerivAt_exp_smul_const + HasDerivAt.clm_apply against the constant curve).
  Trap: `rw [zero_smul]` will NOT match `(0:ℝ) • A` inside exp (OfNat-vs-Zero
  zero forms); use `rw [show (0:ℝ) • A = 0 from zero_smul ℝ A]`. Remaining for
  2.6: u1/u2 (ouNorm-isometry + block-Euclidean skewness), u3 (block
  invariance of dχ), u5 (Stab submodule + DiagonalHomSetup instance), u6
  (phase-cocycle torus model).

  **u1 (ouNorm-isometry) DONE 2026-08-05** (`Necessity/ThetaIsometry.lean`,
  census 65, gates green): `ouNorm_thetaNorm`/`ouNorm_thetaUnit`(+inv)/
  `ouNorm_chiTilde` — a unital order-iso transports the ouNorm defining set
  verbatim (thetaNorm_le_iff from nonneg_iff by sub; the two interval bounds
  via map_smul + thetaNorm_one); inverse-factor isometry by applying the
  forward isometry at the image and cancelling with `Units.mul_inv` (rw
  [← ContinuousLinearMap.mul_apply, Units.mul_inv]; rfl — do NOT try congrArg
  on val_inv, simp collapses it to True). Remaining: u2 (block-Euclidean +
  skewness), u3 (block invariance of dχ), u5, u6.

  **u3 (block invariance) DONE 2026-08-05** (`Necessity/BlockInvariance.lean`,
  census 66, gates green): `cornerJ2 ⟺ q∘x = x` (Jordan eigenrelation; forward
  by absorption, backward via `cornerJ2_of_double`, which was refactored out of
  `blockElt_cornerJ2` for reuse); `thetaNorm_preserves_cornerJ2` (+ .symm via
  the 5-line inverse-Jordan argument `thetaNorm_symm_jordan`, injectivity +
  apply_symm_apply — NO dimension plumbing) → `chiTilde_preserves_cornerJ2` →
  `dChi_preserves_corner` (cornerConjCLM kernel-characterization + the same
  exp-differentiation pattern as u4, now against the invariance curve).
  Traps: stale .olean — after refactoring a lemma into an imported file, `lake
  build` the import BEFORE `lake env lean` on the consumer; `hasDerivAt_const`
  with a CLM-valued constant hits a zero-instance-path mismatch when the
  derivative slot is ascribed `0` — drop the ascription and let simpa
  normalize. Remaining: u2 (block-Euclidean + skewness), u5 (Stab +
  DiagonalHomSetup), u6 (phase cocycle → hmodel).

  **u2 PART 1 (block model) DONE 2026-08-05** (`Necessity/BlockModel.lean`,
  census 67, gates green): `blockHerm i j z = z E_ij + z̄ E_ji`; the SQUARE LAW
  `blockHerm_symmMul_self : x∘x = |z|²•(pᵢ+pⱼ)` (four single-products, the
  e1–e4 haves by simp with the ne-facts); entry helpers
  `single_one_mul_apply`/`mul_single_one_apply`; and the SUPPORT
  CHARACTERIZATION `eq_blockHerm_of_peirce` (Peirce relations ⟹
  x = blockHerm i j x_{ij}; rows/cols kill via the annihilations, diagonals
  via the ½-relations + linear_combination, 7-case entry bash subst-free with
  eq_true/eq_false condition facts + conv_lhs). TRAPS: `subst` on ext-locals
  can eliminate THEOREM PARAMETERS (i became a — later i-references break) —
  case-bash subst-free; lambdas in simp-arg lists parse badly — use
  eq_false/eq_true `have`s; `Complex.mul_conj` is stated with starRingEnd —
  `rw [Complex.star_def]` first; `if_pos rfl` may be pre-reduced to `if True`
  by the rewriting lemma — `simp only [if_true]`.
  REMAINING u2 part 2 (next stretch, plan): `thetaNorm_fixes_frameProj`
  (fix_of_commute + diagFamily_commute_frameProj), blockHerm Peirce relations
  (frameProj∘blockHerm computations, same four products), Θ-transport of the
  relations (hjord 3-line pattern) ⟹ `thetaNorm_block : Θ(blockHerm z) =
  blockHerm (entry)`, then the CAPSTONE `normSq_thetaNorm_block`: square law
  on both sides + Θ(x∘x) = Θx∘Θx + Θ fixes pᵢ+pⱼ ⟹ |w|² = |z|² by the (i,i)
  entry (ofReal_inj). Then u5: V := EuclideanSpace ℝ (Fin 2), blockCoord/
  blockEmbed CLMs, R(t) := coord∘χ̃(t•r)∘embed norm-preserving ⟹ generator
  skew (differentiate ‖R(t)v‖² via exp_apply_hasDerivAt), Stab := submodule of
  block-skew CLMs, DiagonalHomSetup instance, toStabilizerCoupling. Then u6.

  **u2 COMPLETE 2026-08-05** (`Necessity/BlockTransport.lean`, census 68,
  gates green): `thetaNorm_fixes_frameProj`; the three blockHerm Peirce
  relations (per-relation four single-products by simp with ne-facts; the
  ½-coefficient by entrywise push_cast + ring); `thetaNorm_block` (Θ maps
  blocks to blocks — eq_blockHerm_of_peirce fed by the hjord 3-line transport
  ×3); and the CAPSTONE `normSq_thetaNorm_block`: |w|² = |z|² by comparing the
  square law on both sides of Θ(x∘x) = Θx∘Θx with Θ fixing pᵢ+pⱼ, read off at
  the (i,i) entry (if_true again — the ite pre-reduces; ofReal cast via
  exact_mod_cast). **Θ acts on every off-diagonal block by a Euclidean
  isometry — no ouNorm, no trace, no compactness.** Remaining: u5 (V :=
  EuclideanSpace ℝ (Fin 2), blockCoord/blockEmbed, R(t) := coord∘χ̃(t•r)∘embed
  isometric ⟹ skew generator via exp_apply_hasDerivAt differentiation of
  ‖R(t)v‖², Stab := block-skew submodule, DiagonalHomSetup instance,
  toStabilizerCoupling), u6 (phase cocycle ⟹ hmodel ⟹ complex_perFrame_rho).

  **u5a DONE 2026-08-05** (`Necessity/BlockChi.lean`, census 69, first-pass
  clean): `blockHerm_entry` (coordinate readback), `thetaNorm_block_exists` /
  `thetaNorm_symm_block_exists` (inverse via inverse-Jordan relation transport
  + forward-isometry-at-image + Θ∘Θ⁻¹-cancel), and
  **`chiTilde_block_exists`: χ̃(r) acts on every off-diagonal block by a
  Euclidean isometry, for every r** (chain the two factors through the
  canonical exponents). REMAINING u5b/c (plan in memory later-25): entryLm/
  blockCoord/blockEmbed over V := ℝ × ℝ (avoid EuclideanSpace PiLp friction;
  Prod has the ℝ-inner instance), the skew punchline `v.1*w.re + v.2*w.im = 0`
  for w := entry of dχ(r)(blockEmbed v) — differentiate F(t) := normSq(entry
  of χ̃(t•r)(blockEmbed v)) ≡ normSq z₀ at t = 0 (exp_apply_hasDerivAt ∘
  entryCLM, re/im split, HasDerivAt.mul/add, unique vs const) — then Stab :=
  block-skew submodule, ρ := coord∘ξ∘embed, DiagonalHomSetup instance
  (dχAdd := toAddMonoidHom, cont := findim, coalescence_diff := block⊆corner ∘
  dChi_kills_corner), toStabilizerCoupling fires. Then u6.

  **u5b DONE 2026-08-05** (`Necessity/BlockSkew.lean`, census 70, gates
  green): `dChi_block_skew` — **prop:isotropy machine-checked**: for
  z₀ = v₁ + v₂i and w := entry of dχ(r)(blockHerm z₀), the Euclidean dot
  v₁·w.re + v₂·w.im = 0. Proof: entry curve c(t) := entryCLM(exp(t•A)x) has
  derivative w at 0 (exp_apply_hasDerivAt + const.clm_apply); re/im components
  via Complex.reCLM/imCLM the same way; F := re·re + im·im is CONSTANT ≡
  normSq z₀ (chiTilde_block_exists + blockHerm_entry readback); (hre.mul
  hre).add (him.mul him) + unique-vs-const + hval0 (exp(0) = 1) ⟹
  2(v₁w.re + v₂w.im) = 0. No compactness, no invariant measure — the square
  law + one-variable calculus. `entryLm`/`entryCLM` + `entryCLM_apply` built
  here. REMAINING u5c: Stab := block-skew submodule of the CLM space, ρ i j ξ
  := blockCoord ∘ ξ ∘ blockEmbed over V := ℝ × ℝ, dχ ∈ Stab (this theorem),
  DiagonalHomSetup instance (dχAdd := toAddMonoidHom of dChi-linear, cont by
  findim, coalescence_diff := blockHerm ∈ cornerJ2 + dChi_kills_corner) →
  toStabilizerCoupling. Then u6 (phase cocycle → hmodel).

  **u5c DONE 2026-08-05 — 2.6 COMPLETE, THE COUPLING IS PRODUCED**
  (`Necessity/StabilizerInstance.lean`, census 71, gates green):
  `blockCoordLm`/`blockEmbedLm` (ℝ-linear block coordinates), `IsBlockSkew` +
  `blockSkewSubmodule` (Stab; dχ ∈ it by prop:isotropy), `rhoField` (the
  compression, 0 on diagonal pairs — dodges the field's unrestricted
  quantifier), `dChiStab` (+continuity by findim), `rhoField_dChi_coalesced`
  (through blockElt_cornerJ2 + dChi_kills_corner), the `diagonalHomSetup`
  instance over **BlockV := WithLp 2 (ℝ × ℝ)** (bare ℝ × ℝ has NO inner
  product — sup norm! — the L2 synonym does; `WithLp.prod_inner_apply` is
  rfl-simp), and **`stabilizerCoupling` := `.toStabilizerCoupling` — the
  coupling ρ_{ij}(dχ(r)) = (r_i − r_j)•T_{ij} is now a machine-checked THEOREM
  on H_N(ℂ)**, conditional only on S2 + ThetaPreservesJordan (M3). TRAPS: the
  setup's index type is `Fin (setup.n)` — defeq to Fin N but rw is syntactic:
  pin every helper-lemma use with `(n := Fin N)` and open field proofs with
  `show`-retyped goals; final skew goal closes by `exact hs` (pure defeq —
  ofLp/toLp/linearEquiv all reduce) after prod_inner_apply + RCLike.inner_apply
  + star_trivial; coalescence via pointwise `LinearMap.ext` + `show` + rw of
  the vanishing map (never rewrite under the composition form). REMAINING for
  the ℂ-lane: u6 (phase cocycle ⟹ hmodel ⟹ complex_perFrame_rho), then
  Globalization wiring, then the per-type statement. M2 else: 2.9.

  **u6a DONE 2026-08-05** (`Necessity/PhaseCocycle.lean`, census 72, gates
  green): (1) `skew_linear_eq_I_smul` — the 2×2 skew classification: ℝ-linear
  `T : ℂ → ℂ` with `z.re*(Tz).re + z.im*(Tz).im = 0` everywhere equals
  `z ↦ (T 1).im • (I*z)` (polarization at 1, I, 1+I; decompose z by
  `z = z.re•1 + z.im•I` in a `conv_lhs`-scoped `have` — a bare `rw [hz]`
  rewrites the RHS z too and strands mixed `(↑z.re).im` terms). (2)
  `blockHerm_symmMul_blockHerm` — cross-block product: for pairwise distinct
  i,j,k, `blockHerm i j z ∘ blockHerm j k v = (1/2:ℝ) • blockHerm i k (z*v)`
  (eight single-products, only E_ij·E_jk and E_kj·E_ji survive; `star_mul`
  aligns the z̄v̄ coefficient; ℝ-vs-ℂ ½ via entrywise push_cast+ring).
  REMAINING u6: (6c) dχ(r) is a Jordan derivation (differentiate the
  Jordan-preservation of χ̃(t•r) at t=0 via exp_apply_hasDerivAt + the
  bilinear symmMul CLM), (6d) entry maps T_ij := (D(blockHerm i j ·)).mat i j,
  Leibniz across blocks ⟹ cocycle t_ik = t_ij + t_jk, antisymmetry, anchor
  θ_i := t_{i,i₀} ⟹ hmodel ⟹ `complex_perFrame_rho` fires on H_N(ℂ).

  **u6c DONE 2026-08-05** (`Necessity/JordanDerivation.lean`, census 73, gates
  green): `chiTilde_jordan` (χ̃(r) is a Jordan automorphism at every r —
  forward factor by thetaNorm_jordan, inverse factor by thetaNorm_symm_jordan,
  through the two-factor unit definition via a `show`-unfolded hval),
  `exp_smul_dChi_symmMul` (exp(t•dχ(r)) = χ̃(t•r) via map_smul on dChi),
  `exp_entry_hasDerivAt` (entry functions of a flow differentiate to the
  generator's entry: entryCLM.hasFDerivAt.comp_hasDerivAt, two-step have to
  dodge the ∘-vs-λ HO-unification), and **`dChi_jordan_derivation` — dχ(r) is
  a Jordan derivation, D(x∘y) = Dx∘y + x∘Dy, machine-checked**. TRAP (major):
  the curried-bilinear route `jordanCLM : E →L (E →L E)` is DEAD —
  `ContinuousLinearMap.hasFDerivAt` at codomain `E →L E` requires unifying the
  ambient strong-topology instance with the operator-norm topology path at
  depth 2; the defeq check exhausts 1.6M heartbeats and then fails as a type
  mismatch. Route around it ENTRYWISE: all calculus in ℂ (HasDerivAt.mul +
  HasDerivAt.fun_sum — NOT .sum, which in current Mathlib is the
  function-valued-sum form with a Finset metavariable — + const_mul with
  (2:ℂ)⁻¹), then one funext to χ̃'s automorphism property and
  HasDerivAt.unique; entry extraction via BlockSkew's entryCLM whose codomain
  ℂ has a unique instance path. Import chain: JordanDerivation imports
  BlockSkew (for entryCLM), not PhaseCocycle; the u6d file will import both.

  **u6d DONE 2026-08-05 — LEDGER 2.6 FULLY COMPLETE, `complex_perFrame_rho`
  FIRES** (`Necessity/PhaseAnchor.lean`, census 74, gates green):
  `symmMul_blockHerm_entry`/`blockHerm_symmMul_entry` (the (i,k)-entry of a
  cross-block Jordan product — the blockHerm factor's structure does all the
  killing, NO corner-support lemma needed), `blockHermLm` (z ↦ blockHerm z
  ℝ-linear), `dChiEntry` (the block entry map as ℂ →ₗ[ℝ] ℂ),
  `dChiEntry_eq` (skew classification: multiplication by i·t_{ij}(r)),
  `tvalLm` (the phase rate, linear in r), **`tval_cocycle`
  (t_{ik} = t_{ij} + t_{jk} — Leibniz + cross-block product at the (i,k)
  entry)**, `tval_antisymm` (Hermiticity), `thetaAnchor`/`tval_eq_theta_sub`
  (anchor at i₀ collapses pairs to characters), `cMatrix`/`thetaAnchor_expand`
  (θ_i(r) = Σ_l c_{il} r_l via univ_sum_single + map_sum), `rotJ` (+ ≠ 0),
  the `stabilizerCoupling_rho_dChi` bridge, and
  **`complex_perFrame_concrete`: for any S1–S7 sequential product on H_N(ℂ)
  (N ≥ 3, S2, M3-hjord) there is a single per-frame t_F with
  ρ_{ij}(dχ(r)) = (t_F(r_i − r_j)) • J — the paper's `thm:complex` per-frame
  half, PRODUCED on the concrete carrier.** TRAPS: `unfold A B` processes
  sequentially — a constant B whose body mentions A must be unfolded FIRST
  (`unfold cMatrix thetaAnchor`, not the reverse); norm_num at a hypothesis
  re-normalizes HermitianMat entry atoms into a coe-form that no longer
  matches the goal's mat-form (drop norm_num, use smul_eq_mul + linarith);
  `set u := equiv v` fights simp's WithLp.fst/snd normal form — unfold via
  `simp [hu]` at the end; Finset.sum_eq_single side goals arrive with the
  ∧-condition pre-reduced (provide `Ne.symm hm`, not the ∧-shaped eq_false).
  REMAINING for the ℂ-lane per-type statement: Globalization wiring (adjacent
  frames, global t) — check `Globalization.lean` for what it consumes — then
  assemble mthm:master (ℂ) with M1's twistSequentialProduct as sufficiency
  witness. M2 else: 2.9 (prop:singular wiring). Then M3–M7.

  **WIRING DESIGN (banked 2026-08-05, before χ̃ part 2):** build the
  `ComparisonSetup (HermitianMat (Fin N) ℂ)` instance NEXT — the abstract
  DiagonalHom layer then supplies `chi_hom`/`chi_comm`/`chi_extend_wellDefined`
  (the ℝⁿ-extension bookkeeping) FOR FREE. Field discharge map: jordan :=
  symmMul-bilinear (build the bilinear map; vendored comm/one lemmas);
  e := 1; p := frameProj; aOf := diagFamily; nonneg := (0 ≤ ·);
  **Inv := (·.mat.PosDef)** (aOf_inv must hold for ALL r, so effects cannot
  enter Inv); **Θ total via normalization**: `Θ a := thetaEquiv at
  ((‖a‖+1)⁻¹ • a)` when PosDef (always an effect by `norm_smul_inv_effect`,
  PosDef preserved), `LinearEquiv.refl` otherwise — the 2.3 law `theta_smul`
  makes every Θ-property scale-invariantly inherited and is WHY vdW 5.4
  exists; Θ_unital/Θ_orderIso/Θ_fix/Θ_cocycle from the 2.1f/2.2/2.4+Chi
  theorems (cocycle threads the Θ_jordan hypothesis, which is also the
  Θ_jordan field — take a global `hjord` parameter); frame_opCommute :=
  `symmMul_opCommute_of_commute` + `diagFamily_commute_frameProj`; rank_ge =
  parameter. Then χ̃ part 2 = the abstract extension applied at the instance +
  line-continuity from S2 + `multiParameter_eq_exp`.
  Third ingredient (χ̃ part 1) DONE 2026-08-05 (`Necessity/Chi.lean`, census
  59, compiled clean first pass): `theta_congr` (base-point congruence, subst +
  proof irrelevance), `sp_diagFamily` (`a(r) ◦' a(r') = a(r+r')` — the 2.2
  value identity + the √-collapse on the commuting diagonal), `thetaD_zero`
  (χ̃(0) = 1 via `theta_base_one`), and `thetaD_mul` (**the orthant cocycle**,
  conditional on the M3 Jordan field). Part 2 = the ℝⁿ-extension +
  line-continuity from S2 + `multiParameter_eq_exp` ⟹ dχ.
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
  **PROOF PLAN (banked 2026-08-05, design pass done).** Substitute
  `g t := h (Real.exp t)`: continuous everywhere (exp lands in Ioi 0),
  `g (s+t) = g s * g t`, `g 0 = 1` — a continuous one-parameter semigroup in
  the Banach algebra `W →L[ℝ] W`. Classify `g = exp(t • A)` by the classical
  integral-regularization argument, ALL ingredients inventory-confirmed:
  (i) choose δ > 0 with `‖g s − 1‖ ≤ 1/2` on `[0, δ]` (continuity at 0);
  `J := ∫ s in 0..δ, g s` satisfies `‖J − δ•1‖ ≤ δ/2` <
  (`intervalIntegral.norm_integral_le_of_norm_le_const`), so `δ⁻¹•J = 1 − t`
  with `‖t‖ < 1` is a unit (`Units.oneSub`, geometric series);
  (ii) `g t * J = ∫ s in t..(t+δ), g` (translation/`integral_comp_add_left` +
  the semigroup law pulled through `intervalIntegral.integral_const_mul`-style
  linearity — g t is a CONSTANT operator factor, use `ContinuousLinearMap`
  composition under the integral or `intervalIntegral.integral_smul`-analogue
  via `ContinuousLinearMap.integral_comp_comm`), so
  `g t = (F (t+δ) − F t) * J⁻¹` with `F u := ∫ 0..u, g` — differentiable by
  FTC-2 (`intervalIntegral.integral_hasDerivAt_right`), hence g is C¹;
  (iii) `A := deriv g 0`; the difference quotient factorization
  `g (t+h) − g t = g t * (g h − 1)` gives `HasDerivAt g (g t * A) t`;
  (iv) `d/dt [g t * exp(−t•A)] = 0` via `hasDerivAt_exp_smul_const`, product
  rule, and `Commute A (exp (−t•A))` (`Commute.exp_right`-style, from
  self-commutation) ⟹ constant = `g 0 = 1` ⟹ `g t = exp (t•A)`
  (`is_const_of_deriv_eq_zero` on ℝ, or `Constant.of_hasDerivAt_zero`);
  (v) back-substitute `x = exp (log x)` for `x > 0`; uniqueness: from
  `∀ x > 0, exp (log x • A) = exp (log x • B)`, take `x := exp t` ⟹
  `exp (t•A) = exp (t•B)` ∀t, differentiate at 0 ⟹ `A = B`.
  Then DELETE the axiom, replace with the theorem (same name/signature so the
  two call sites in NormalFormExistence.lean are untouched), drop it from the
  audit allowlist — **custom-axiom count 1 → 0; closure = pure Lean core.**
  **CORE LEMMA DONE 2026-08-05** (`Necessity/OneParameter.lean`, census 57,
  gates green): `oneParameter_eq_exp` — continuous one-parameter semigroups in
  a real Banach algebra are `t ↦ exp (t•A)` with unique generator, by exactly
  the banked plan (all five steps; the opaque-generator trick
  `obtain ⟨A, hA0⟩ := ⟨_, hg' 0⟩` avoids `set`-folding fragility in the ODE
  step). Lean notes: the 𝕂-free `exp` refactor puts `exp_add_of_commute` in a
  `[NormedAlgebra ℚ 𝔸]` section with NO instance path from ℝ — route through
  `exp_add_of_commute_of_mem_ball (𝕂 := ℝ)` + `expSeries_radius_eq_top ℝ`;
  `Commute.exp_right` is unconditional (the no-ℚ case has `exp = 1` by
  definition); FTC-2 = `intervalIntegral.integral_hasDerivAt_right` +
  `Continuous.stronglyMeasurable.stronglyMeasurableAtFilter` (no explicit
  args); constancy via `is_const_of_fderiv_eq_zero` (needs the MeanValue
  import; no deriv-named variant exists at pin).
  **2.7 COMPLETE 2026-08-05: THE TREE IS AT ZERO CUSTOM AXIOMS.** The wrapper
  `aczel_multiplicative_classification` (same file) substitutes
  `g := h ∘ Real.exp`; `Selection.aczel_continuous_multiplicative` is now a
  THEOREM aliasing it (name + signature preserved, both call sites untouched);
  audit surgery done (allowlist = the three core axioms, citedAxioms = [],
  Layer-4 pin refrozen on the theorem, prose in AxiomAudit/README/THEOREM-MAP).
  Gate verified first-hand: "custom axioms exactly [], every tracked persisted
  declaration's closure ⊆ [propext, Classical.choice, Quot.sound]".
- **2.8 `bgw_canonical_composite` ELIMINATION — DONE 2026-08-04.** Replaced the
  axiom (a constructible existence claim, hence not falsifiable) with the
  pattern-match definition `bgwComposite` + `rfl`-proved `bgwComposite_table`;
  non-matrix rows = documented junk-total `.real 0`, consumed nowhere. Audit
  updated (allowlist + citedAxioms to one, Layer-4 bgw pin removed, docstrings);
  README / THEOREM-MAP §2 / NormalFormExistence / Interface docstrings updated.
  **Custom-axiom count: 2 → 1** (Aczél alone); → 0 after 2.7.
- **2.9 prop:singular (singular-effect extension) — DONE 2026-08-05, M2
  COMPLETE** (`Necessity/SingularExtension.lean`, census 75, gates green):
  `isEffect_interp`/`posDef_interp` (the boundary sequence a + t(𝟙−a) is an
  effect for t ∈ [0,1] and PosDef for t ∈ (0,1] — split as t•𝟙 + (1−t)•a,
  PosDef.one.smul + zero_le_iff/PosSemidef.smul + add_posSemidef),
  `dense_posDef_effects` (density in the effect SUBTYPE via
  mem_closure_of_tendsto + tendsto_subtype_rng; sequence 1/(k+1)),
  `sp_eq_on_effects_of_eq_on_posDef` — **prop_singular is now INVOKED**: two
  S1–S7 products with S2 agreeing on PosDef effects agree on ALL effects
  (continuousOn_iff_continuous_restrict turns S2 into subtype-continuity).
  TRAP: Matrix.PosDef over ℂ needs `open ComplexOrder` (scoped PartialOrder ℂ)
  — without it the statements themselves fail to elaborate; and
  OrderUnitSpace shadows `add_nonneg` (qualify `_root_.add_nonneg`).

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
- **3.0b VENDOR EXECUTED 2026-08-05 (research f22dbd3).** Route decided:
  **mechanical backport, NOT a toolchain bump** (bumping to v4.33 would force
  whole-tree re-elaboration of 3000+ jobs for one theorem). The exact
  8-file import closure of `WignerRigidity` is vendored at
  `RadicalRelativity/Vendor/Wigner/` (≈4.8kL from `zblore/csd-lean4` @
  `2287f45`, Apache 2.0, headers retained). Module-system strip (`module`,
  `public import`, `@[expose] public section`) + **only FOUR API-drift renames
  in the whole 4.8kL**: `Set.mem_ofPred_eq` → `Set.mem_setOf_eq`,
  `isOpen_setOfPred_linearIndependent` → `isOpen_setOf_linearIndependent`,
  `push Not` → `push_neg` (all three in Topology.lean's
  `isClosed_collinearity_relation`), `PiLp.ofLp_single` →
  `EuclideanSpace.ofLp_single` (WignerRigidity.lean's
  `unitaryOfIsometry_apply`). ZERO statement changes, zero deletions, zero
  sorry/axiom added. Verified first-hand after vendoring: full build green;
  `#print axioms Projectivization.wigner_rigidity` and
  `…wigner_rigidity_unitaryGroup` both `[propext, Classical.choice,
  Quot.sound]`; `#check` confirms the dichotomy statement is unchanged (no
  surjectivity hypothesis, antiunitary branch present, the `≃ₗᵢ[ℂ]` witness an
  OUTPUT). The island is **TRACKED** (root-imported + in the frozen manifest,
  now 84 names), so the census runs over every declaration in it — vendoring
  did not shrink the audited surface. Provenance in `Vendor/VENDOR.md`.
- **3.1a bridge 1 (atoms) DONE 2026-08-05** (`Necessity/ProjectionOrder.lean`,
  census 76 pre-Wigner): `IsProjection.le_iff_mul_eq` — the **absorption
  order** `q ≤ p ↔ q·p = q` (forward: conjugate by 1−p, `hpz` kills p, order
  squeeze gives `q.conj (1−p) = 0`, then `XᴴX = 0 ⟹ X = 0` via
  `conjTranspose_mul_self_eq_zero`; backward: p−q is a projection hence ≥ 0);
  `rankOne ψ` = `vecMulVec ψ (star ψ)` (+ isProjection, ≠ 0);
  `IsAtomProjection` (order-theoretic: nonzero projection with no proper
  nonzero subprojection); `rankOne_isAtom` (a subprojection is `wψ*` by
  absorption, idempotence pins `ψ*⬝w = 1` by entrywise cancellation at a
  nonzero coordinate, Hermiticity gives `w = (w*⬝ψ)•ψ`, the two scalars agree
  ⟹ `w = ψ`); `IsAtomProjection.exists_rankOne` (normalize a range vector,
  `rankOne ψ ≤ p` by absorption via `star_mulVec`, squeeze with atomicity).
  TRAPS: `vecMulVec_mulVec` lands in `MulOpposite.op c • u` — need
  `MulOpposite.op_one`/`op_smul_eq_smul` (root, NOT `MulOpposite.`-prefixed);
  `dotProduct`/`smul_dotProduct`/`dotProduct_smul` are ROOT names, not
  `Matrix.`-prefixed in v4.28; the normalization identity is cleanest as a
  standalone real `have c * (c * R) = 1` closed by `mul_self_sqrt` + field_simp,
  then `exact_mod_cast` (letting field_simp loose on the ℂ-side goal generates
  nested-sqrt garbage). NEXT (3.1b): the Busch–Gudder strength function
  λ(p,a) = sup{t | t·p ≤ a}, order-definable, with the rank-one computation
  λ(p, q + ε(1−q)) = ε/(ε·τ + (1−τ)), τ = tr(pq) ⟹ a unital linear order-iso
  preserves transition probabilities; then feed `wigner_rigidity`.
- **3.1b strength function DONE 2026-08-05** (`Necessity/Strength.lean`,
  census 85, gates green): `rankOne_quadratic` (the rank-one quadratic form is
  ⟪v,ψ⟫⟪ψ,v⟫); `rankOne_smul_le_iff` — the geometric core, `t·ψψ* ≤ a` iff
  vectorwise `t⟪v,ψ⟫⟪ψ,v⟫ ≤ ⟪v,av⟫`, through the vendored
  `le_iff_mulVec_le_mulVec` (the whole Loewner order reduces to quadratic
  forms in ℂ — no a^{-1/2} machinery needed for the ORDER side);
  `strength p a := sSup {t | t•p ≤ a}` with nonemptiness (0 ∈ S) and
  boundedness (test `t•ψψ* ≤ 𝟙` at ψ); **`strength_map` — every ℝ-linear
  order-isomorphism preserves the strength** (the defining set is transported
  literally by `map_smul` + the order equivalence: THE reason the strength is
  the right bridge); plus the `le_strength`/`strength_le` certificates.
  FORMULA VERIFIED NUMERICALLY BEFORE CODING (numpy, N=4, random rank-ones):
  λ(ψψ*, a) = 1/⟪ψ, a⁻¹ψ⟫, and on the probe family a_ε = q + ε(𝟙−q) with
  τ = tr(pq) this is ε/(ετ + 1 − τ); at **ε = 1/2** it is 1/(2 − τ), so
  **τ = 2 − 1/Str(p, a_{1/2})** — a single-ε inversion, no ε-limit needed.
  **NEXT UNIT 3.1c — FULLY DECODED, PROOF COMPLETE ON PAPER, VERIFIED
  NUMERICALLY (numpy N=4, random rank-ones; all four identities below checked
  to 1e-16).** Target: `strength (rankOne ψ) (probe φ) = (2 − τ)⁻¹` with
  `probe φ := (1/2 : ℝ) • (1 + rankOne φ)` and
  `τ := Complex.normSq (star φ ⬝ᵥ ψ)`, for unit ψ, φ.  Then order-invariance
  (`strength_map`) transfers τ, i.e. gives `TransProbPreserving`.
  * Probe facts: a_{1/2} = (1/2)(𝟙+q) so **a⁻¹ = 2·𝟙 − q** (because q² = q:
    (𝟙+q)(𝟙 − q/2) = 𝟙); probe is an effect (0 ≤ ·, and ≤ 𝟙 since q ≤ 𝟙).
  * `(rankOne φ) *ᵥ ψ = (star φ ⬝ᵥ ψ) • φ` — the one mulVec identity needed
    (vecMulVec_mulVec + op_smul_eq_smul, as in `rankOne_quadratic`).
  * **Forward bound (Str ≤ (2−τ)⁻¹)**: feed `rankOne_smul_le_iff` the single
    test vector **v := 2•ψ − (star φ ⬝ᵥ ψ) • φ = a⁻¹ψ**.  Then
    `star ψ ⬝ᵥ v = 2 − τ` (unit ψ + c·conj c = normSq c) and **a v = ψ**
    (the (1/2)(𝟙+q)(2−q) = 𝟙 collapse), so `star v ⬝ᵥ a *ᵥ v = 2 − τ` too;
    the criterion reads t(2−τ)² ≤ (2−τ) ⟹ t ≤ (2−τ)⁻¹ (note 1 ≤ 2−τ ≤ 2
    since 0 ≤ τ ≤ 1 by Cauchy–Schwarz, so no division-by-zero case).
  * **Backward bound ((2−τ)⁻¹ ∈ the set)**: show
    `M := (2−τ)•(𝟙 + q) − 2•p ⪰ 0` vectorwise, i.e. for all v with
    α := star φ ⬝ᵥ v: `2|star ψ ⬝ᵥ v|² ≤ (2−τ)(‖v‖² + |α|²)`.  Decompose
    ψ = c•φ + χ (c := star φ ⬝ᵥ ψ, χ := ψ − c•φ, ‖χ‖² = 1 − τ, χ ⊥ φ) and
    v = α•φ + v⊥ (‖v⊥‖² = ‖v‖² − |α|²); then
    |star ψ ⬝ᵥ v| ≤ √τ·|α| + √(1−τ)·‖v⊥‖ and the SHARP weighted
    Cauchy–Schwarz with weights (2, 1) closes it:
    (√τ x + √(1−τ) y)² ≤ (τ/2 + (1−τ))(2x² + y²) = ((2−τ)/2)(2x² + y²),
    and (2−τ)(‖v‖² + |α|²) = (2−τ)(2|α|² + ‖v⊥‖²) — EXACT match, no slack.
    (Plain unweighted CS is too lossy — it needs τ ≤ 0; the weight 2 on the
    α-slot is what makes it tight.  Do not "simplify" this step.)
  **3.1c FORWARD HALF DONE 2026-08-05** (`Necessity/StrengthProbe.lean`,
  census 86, gates green): `probe`/`tprob`; `rankOne_mulVec`;
  **`probe_mulVec_witness`** (the collapse probe(φ)·(2ψ − ⟪φ,ψ⟫φ) = ψ — the
  inverse's action with NO inverse constructed); `dot_witness` (⟪ψ,w⟫ = 2 − τ);
  `tprob_le_one` (Cauchy–Schwarz for free: test φφ* ≤ 𝟙 at ψ through
  `le_iff_mulVec_le_mulVec`) + `one_le_two_sub_tprob`; `probe_nonneg`/
  `probe_le_one` (probe is an effect); and **`strength_probe_le` — the forward
  bound Str ≤ (2−τ)⁻¹**, both criterion slots evaluating to 2 − τ at the
  witness. TRAPS: `dotProduct_sub`/`dotProduct_comm` are ROOT names in v4.28
  (not `Matrix.`-prefixed); `omit` must precede the docstring, and cannot be
  used when the instance IS referenced (probe needs DecidableEq via `1`);
  `Complex.normSq_eq_conj_mul_self` has the conj on the LEFT — state the cast
  as its own `have` in the direction you need rather than rewriting in place;
  rank-one PSD comes from `posSemidef_conjTranspose_mul_self` on
  `replicateRow` + `vecMulVec_eq (Fin 1)`; none of `le_inv_iff_mul_le` /
  `le_inv_iff_one_le_mul₀` / `le_inv_comm₀` exist here — close `t ≤ c⁻¹` from
  `t·c ≤ 1` by an explicit three-step `calc` through `t·c·c⁻¹`.
  **3.1c COMPLETE 2026-08-05 — τ IS ORDER DATA** (same file, census 86, gates
  green, zero sorries): `weighted_cs_sharp` (slack is exactly
  (√τ·y − 2√(1−τ)·x)², so ONE nlinarith hint closes it and no sign hypotheses
  are needed); `nsq` + `dot_self_eq_nsq`/`nsq_smul`; `rankOne_smul` (quadratic
  homogeneity); `rankOne_le_nsq_smul_one`; **`cs_dot` — Cauchy–Schwarz on
  n → ℂ derived from `rankOne ψ ≤ ‖ψ‖²•𝟙` tested at the second vector**, i.e.
  from the unit case plus homogeneity, with NO inner-product-space bridging;
  `probe_quadratic`; **`probe_ge_inv_smul_rankOne` — the backward bound**
  (decompose ψ = cφ + χ and v = αφ + w, both orthogonality facts by direct
  dotProduct expansion, then `cs_dot` on the χ-w pairing feeds
  `weighted_cs_sharp` whose (2,1) weights match the probe form exactly);
  **`strength_probe_eq` : Str(ψψ*, probe φ) = (2−τ)⁻¹**;
  `tprob_eq_of_strength` (τ = 2 − Str⁻¹); and the payoff
  **`tprob_preserved`: a unital ℝ-linear order-automorphism carrying rank-ones
  to rank-ones PRESERVES the transition probability** — pure transport through
  `strength_map`, since the probe is built from the unit and a rank-one. That
  is precisely the `TransProbPreserving` input of the vendored
  `Projectivization.wigner_rigidity`. TRAPS: left-argument dotProduct lemmas
  are `sub_dotProduct`/`add_dotProduct` (the `dotProduct_sub` family only
  matches the RIGHT slot) — prefer a `simp only` with all four over ordered
  `rw`; `star_sub`/`star_add` are root, NOT `Pi.`-prefixed; ℂ-order casts need
  `Complex.real_le_real` (`exact_mod_cast` cannot see the ComplexOrder cast);
  `Complex.normSq_eq_norm_sq` is the normSq↔‖·‖² bridge; `pow_le_pow_left` is
  `pow_le_pow_left₀` here; keep `nsq w` SYMBOLIC through the nlinarith chain
  (rewriting it to `nsq v − normSq α` in only one hypothesis desynchronizes
  linarith's atoms).
  **NEXT (3.2, the last M3 leg): the ray map + wigner_rigidity + Jordan.**
  (a) From a unital ℝ-linear order-auto Φ on H_N(ℂ): bridge 1 says Φ permutes
  atoms (`IsAtomProjection` is order-theoretic — needs Φ's order-iso property
  both ways, which the `hΦ` iff already gives), and `exists_rankOne` extracts a
  unit vector, so define `rayMap : ℙ ℂ (EuclideanSpace ℂ (Fin N)) → ℙ ℂ (...)`
  by p ↦ mk (the vector of Φ (rankOne p.rep-normalized)); well-definedness =
  independence of the representative, which follows because rankOne of a
  rescaled vector is the same projection (`rankOne_smul` + normalization).
  (b) `TransProbPreserving rayMap` = `tprob_preserved` transported through
  `transProbVec ψ φ = ‖⟪ψ,φ⟫‖²/(‖ψ‖²‖φ‖²)`, which on unit vectors is exactly
  `tprob` (careful: their inner is `inner ℂ ψ φ` on EuclideanSpace = star-first
  convention; check against `dotProduct` by `EuclideanSpace.inner_eq` or
  expand both as sums). (c) Apply `Projectivization.wigner_rigidity` to get
  e : ≃ₗᵢ[ℂ] with Φ's ray action = projMap e, or the conjProj branch.
  (d) **DONE 2026-08-05** (`Necessity/JordanWitness.lean`, census 87, gates
  green, FIRST-PASS CLEAN): `unitaryConj U` (x ↦ U x U* as an ℝ-linear map) +
  **`unitaryConj_preservesJordan`** (only `Uᴴ*U = 1` needed — the cancellation
  is two `calc` steps with `noncomm_ring`); `transpose_isHermitian` +
  `transposeMap` + **`transposeMap_preservesJordan`** (transposition REVERSES
  matrix products, and the symmetrized product is invariant under reversal, so
  it closes by `add_comm` on the two transposed terms); and
  **`antiunitaryConj_preservesJordan`** for the composite x ↦ U xᵗ U*. So BOTH
  branches of the Wigner dichotomy land on Jordan automorphisms.
  **(a) DONE 2026-08-05** (same file): `isProjection_map` — a unital linear
  order-automorphism preserves being a projection, via
  `mem_extremePoints_iff_isProjection` (projections ARE the extreme points, so
  this is order data; the segment is pulled back through surjectivity +
  injectivity-from-order-reflection); `isAtomProjection_map` — atoms go to
  atoms (the backward direction of the subprojection clause needs the extreme
  property transported the OTHER way, done inline); and
  **`exists_rankOne_map` — Φ carries each rank-one projection to a rank-one
  projection with an explicit unit vector**, i.e. bridge 1 composed with atom
  transport. TRAP: in this Mathlib, `Set.extremePoints`'s condition concludes
  `x₁ = x` ONLY (not the pair `x₁ = x ∧ x₂ = x`) — an `obtain ⟨he1, he2⟩`
  against it fails with a confusing "Eq.refl has no explicit fields" error.
  REMAINING for M3: (b) the ray map on `ℙ ℂ (EuclideanSpace ℂ (Fin N))` built
  from `exists_rankOne_map` (needs a choice function + representative
  independence, the latter from `rankOne_smul` since rescaling a vector does
  not change its rank-one projection) and the `transProbVec`-vs-`tprob`
  identification (`PiLp.inner_apply` makes `inner ℂ ψ φ = star ψ ⬝ᵥ φ`
  definitionally, and on unit vectors `transProbVec = tprob` since
  normSq is conjugation-invariant; mind the `WithLp.toLp/ofLp` wrapper);
  (c) apply `wigner_rigidity`; then agreement-on-rank-ones ⟹ equality needs
  **rank-one projections to span H_N(ℂ) over ℝ**.  ENTRY POINTS LOCATED AND
  CHECKED 2026-08-05 (do not re-search):
   * `Vendor/HermitianMat/Proj.lean` `projector_eq_sum_rankOne` states
     `(projector S).mat = ∑ i, vecMulVec (S.subtype (b i)) (star (S.subtype (b i)))`
     over an `OrthonormalBasis ι 𝕜 S` — **syntactically the same shape as our
     `rankOne`** (`rankOne v = ⟨vecMulVec v (star v), _⟩`), so it plugs in
     directly for the projection case.
   * The general Hermitian case: Mathlib's
     `Matrix.IsHermitian.spectral_theorem` lives in
     `Mathlib/Analysis/Matrix/Spectrum.lean` and is stated in the
     **`conjStarAlgAut` form**: `A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
     (diagonal (RCLike.ofReal ∘ hA.eigenvalues))`, i.e. `A = U D U*`, NOT as a
     sum of rank-ones.  The remaining work is exactly the bookkeeping identity
     `U · diagonal λ · U* = ∑ i, λ i • (col i)(col i)*` with
     `col i = hA.eigenvectorBasis i`; nearby usable facts in the same file:
     `eigenvalues_eq` (eigenvalues as `RCLike.re (star (eigenvectorBasis i) ⬝ᵥ
     A *ᵥ eigenvectorBasis i)`) and `conjStarAlgAut_star_eigenvectorUnitary`.
  **SPAN LEMMA DONE 2026-08-05 — and the spectral theorem was NOT needed**
  (`Necessity/RankOneSpan.lean`, census 88, gates green): the vendored trace
  inner product (`Vendor/HermitianMat/Inner.lean` supplies a real
  `InnerProductSpace` instance) pairs `y` against a rank-one as the quadratic
  form — `inner_rankOne : ⟪y, ψψ*⟫ = Re (ψ* y ψ)` — so a `y` orthogonal to
  every rank-one has identically vanishing quadratic form (rescale an arbitrary
  vector to a unit one), whence `0 ≤ y` AND `y ≤ 0`, whence `y = 0`
  (`eq_zero_of_quadratic_zero`, the two-sided-positivity kill via
  `le_iff_mulVec_le_mulVec`). Then
  `Submodule.orthogonal_eq_bot_iff` gives **`span_rankOne_eq_top`**, and
  **`linearMap_eq_of_eq_on_rankOne`** (by `Submodule.span_induction`) is the
  form M3 consumes: two ℝ-linear maps agreeing on rank-ones are equal.
  So `projector_eq_sum_rankOne` and the `U D U*` bookkeeping are BOTH
  unnecessary — do not build them. TRAPS: `y.property`/`congrFun₂` states
  Hermiticity about `y.val`, which is defeq but NOT syntactically `y.mat`, so a
  `rw` with it fails against a goal in `mat` form — restate through
  `congrArg (fun M => M j i) y.H` + `simpa [Matrix.conjTranspose_apply]`;
  the orthogonal-complement machinery on this carrier needs
  `maxHeartbeats 1600000` (the InnerProductSpace instance chain is deep);
  `real_inner_comm` is needed because `Submodule.mem_orthogonal` gives the
  pairing in the opposite slot order.
  **3.2b DONE 2026-08-05** (`Necessity/WignerBridge.lean`, census 89, gates
  green): `inner_eq_dotProduct` (on `EuclideanSpace ℂ (Fin N)` the inner
  product IS the star-first dot product of the underlying functions — via
  `PiLp.inner_apply` + `RCLike.inner_apply`, closing with a `mul_comm` under
  the sum, NOT `rfl`); `norm_sq_eq_nsq`; **`transProbVec_eq_tprob`** — on unit
  vectors the vendored `Projectivization.transProbVec` equals the
  order-recovered `HermitianMat.tprob` (the two differ by a conjugation inside
  a norm, killed by `RCLike.norm_conj`); plus `unitVec`/`unitVec_unit` and
  `rankOne_smul_unit` (a unit-modulus rescale leaves the rank-one projection
  fixed — the representative-independence input for the ray map).
  TRAP: `((x : ℝ) : ℂ)⁻¹`-style ascriptions parse as coe-then-inv; write the
  inverse INSIDE the real ascription or downstream `normSq` rewrites won't
  match.
  **3.2c DONE 2026-08-05** (`Necessity/RayMap.lean`, census 90): `repUnit`
  (normalized canonical representative) + `rankOneP`; `rankOne_normalize_smul`
  (normalizing a nonzero multiple of a UNIT vector recovers its rank-one — the
  scalar becomes unit-modulus, which `rankOne_smul` absorbs);
  `rankOneP_mk` (representative independence, via the vendored
  `rep_mk_eq_smul`); **`rayMap`** (choice over `exists_rankOne_map`, nonzero
  side from unitarity) and **`rayMap_rankOne`** — the ray map IMPLEMENTS Φ on
  rank-one projections; `transProb_eq_tprob_repUnit`; and
  **`rayMap_transProbPreserving`** — literally `wigner_rigidity`'s hypothesis,
  by pure transport through `rayMap_rankOne` + `tprob_preserved`.
  TRAPS: `rw [someDef]` fails on plain `def`s with no equation lemmas — use
  `unfold`; to apply `mk_eq_mk_iff'` first rewrite the RHS into `mk` form with
  `conv_rhs => rw [← Projectivization.mk_rep _]`; the residual
  `toLp (c • ofLp v) = c • v` goals close by `rfl`, not `funext`+`simp`;
  `unitVec`'s proof argument is UNUSED in its body (named `_hv`), which is what
  makes rewriting the vector underneath it legal.
  **3.2 ASSEMBLY DONE 2026-08-05** (`Necessity/KadisonDischarge.lean`,
  census 91, gates green): **`rayMap_dichotomy`** — the vendored
  `Projectivization.wigner_rigidity` FIRES on our induced ray map, at exactly
  the interface the order-theoretic bridges produce; and the two branch
  assemblies `preservesJordan_of_unitary_on_rankOne` /
  `preservesJordan_of_antiunitary_on_rankOne`, each of which turns
  "Φ acts as the witness on rank-ones" into `PreservesJordan Φ` via
  `linearMap_eq_of_eq_on_rankOne` (this is where the spanning lemma earns its
  keep: it makes the conclusion about Φ ITSELF, not about its action on
  rank-ones).
  **UNITARY BRANCH CLOSED END TO END 2026-08-05** (same file, census 91,
  gates green, zero sorries): `rankOne_mulVec_eq_conj` ((Uψ)(Uψ)* = U(ψψ*)U*,
  entrywise);
  `unitaryOfIsometry_conjTranspose_mul` (Uᴴ U = 1 from the vendored
  `unitaryOfIsometry_mem` + `mem_unitaryGroup_iff'`);
  `isometry_apply_eq_mulVec` (the isometry acts on coordinates as its matrix,
  through `unitaryOfIsometry_toEuclideanLin`); and
  **`preservesJordan_of_rayMap_eq_projMap` — if the induced ray map is
  `projMap e` then Φ preserves the Jordan product**, i.e. the whole chain
  bridge-1 → strength/probe → rayMap → wigner_rigidity → witness → spanning
  runs to `PreservesJordan Φ` on the unitary branch.
  TRAPS: `rw` of a `toLp/ofLp` coercion INSIDE a `Projectivization.mk` fails
  ("motive is not type correct") because the nonzero proof depends on the
  vector — add a wrapper lemma stated for an arbitrary Euclidean vector
  (`rankOneP_mk'`, proved from `rankOneP_mk` by `rfl` on the round-trip)
  instead of rewriting; and after editing an imported file, `lake build
  <that module>` BEFORE `lake env lean` on the consumer or the stale .olean
  reports the new lemma as an unknown identifier.
  **★★ M3 MATHEMATICAL CONTENT COMPLETE 2026-08-05 ★★** (same file, census 91,
  gates green, zero sorries): the antiunitary branch closed with
  `rankOne_star_eq_transpose` ((star ψ)(star ψ)* = (ψψ*)ᵗ) and `star_unit`,
  through the vendored `conjProj_mk`; and the capstone
  **`orderAuto_preservesJordan : (∀ x y, x ≤ y ↔ Φ x ≤ Φ y) → Φ 1 = 1 →
  Surjective Φ → PreservesJordan Φ`** on `H_N(ℂ)`.  VERIFIED FIRST-HAND:
  `#print axioms Necessity.orderAuto_preservesJordan` = `[propext,
  Classical.choice, Quot.sound]`.  This is the paper's `prop:theta` /
  van Imhoff–Roelands import, now a THEOREM of this development (modulo the
  vendored, separately axiom-audited `wigner_rigidity`).
  **★★★ M3 COMPLETE 2026-08-05 — THE BOULDER IS DOWN ★★★** (same file,
  census 91, gates green, zero sorries).  The plumbing landed in three lines:
  `thetaPreservesJordan_of_S2` feeds `orderAuto_preservesJordan` the existing
  `theta_le_iff` (NOTE: it already existed with the OPPOSITE orientation —
  `.symm` it, do not re-prove), `theta_one`, and
  `(thetaEquiv …).surjective`.  Then
  **`complex_perFrame_unconditional`**: for ANY S1–S7 product on `H_N(ℂ)` with
  `N ≥ 3` and S2 there is a single per-frame `t_F` with
  `ρ_{ij}(dχ(r)) = (t_F(r_i − r_j)) • J`.  VERIFIED FIRST-HAND: both
  `#print axioms Necessity.thetaPreservesJordan_of_S2` and
  `#print axioms Necessity.complex_perFrame_unconditional` =
  `[propext, Classical.choice, Quot.sound]`, and the printed hypothesis list is
  exactly the paper's (S1–S7 product, S2, N ≥ 3 — no Jordan hypothesis).
  **Every M2 result is now UNCONDITIONAL**, modulo only the vendored,
  separately axiom-audited `Projectivization.wigner_rigidity`.
  Expected final disclosed-import count for the ℂ lane: ONE (Wigner), in place
  of the paper's vIR/Kadison citation.
  **GLOBALIZATION INGREDIENT DONE 2026-08-05** (`Necessity/ConjTransport.lean`,
  census 92, gates green, zero sorries): `adU U x := x.conj U` with the full
  transport kit (`adU_unital`, `adU_cancel`/`adU_cancel'` — BOTH directions
  are needed and they use DIFFERENT unitarity halves, `adU_nonneg_iff`,
  `adU_le_iff`, `adU_isEffect`, `adU_continuous` via `conjLinear` +
  findim); **`conjProduct` — all NINE S1–S7 fields verified** for
  `(P ▷ U).sp a b := Ad_{U*} (P.sp (Ad_U a) (Ad_U b))`;
  **`conjProduct_firstArgContinuous`** (S2 transports: `ContinuousOn.comp` with
  the `MapsTo` from `adU_isEffect`, then `Continuous.comp_continuousOn`); and
  **`conjProduct_perFrame`** — each unitary yields its own per-frame parameter
  from `complex_perFrame_unconditional`.  Since `Ad_U` carries the standard
  Jordan frame to `U`'s columns, this is the CONCRETE `t` field of
  `ComplexGlobalizationData` (previously only hypothetical).
  TRAPS: `rw [← sub_nonneg (a := ...)]` mis-binds — do the order-iso by two
  explicit `sub_nonneg` steps instead; the compatibility hypotheses transport
  by `congrArg (adU U)` + `adU_cancel'` (NOT `adU_cancel` — the composite runs
  the other way).
  **GLOBALIZATION INSTANTIATED 2026-08-05** (same file): the unitary group
  indexes the frames, `unitaryGroup_conjTranspose_mul`/`_mul_conjTranspose`
  extract both unitarity halves in `ᴴ` form from membership (via
  `mem_unitaryGroup_iff'`/`iff` + `Matrix.star_eq_conjTranspose`),
  **`frameTwist`** is the per-frame parameter as an honest FUNCTION of the
  frame (choose over `conjProduct_perFrame`) with `frameTwist_spec`, and
  **`complex_global_twist_concrete`** collapses them to a SINGLE global `t`
  through the machine-checked `global_twist_of_perFrame` (hence
  `Globalization.global_t`, hence the 2π-ambiguity-free
  `real_character_unique`).  The two frame-graph inputs are explicit
  hypotheses, matching the paper's own accounting: `connected` =
  lem:frame-connectivity (paper-proved, located, never an axiom) and `overlap`
  = cross-coherence.  Axioms verified first-hand: `[propext,
  Classical.choice, Quot.sound]`.
  **PRODUCT-LEVEL STRUCTURAL THEOREM DONE 2026-08-05**
  (`Necessity/KadisonDischarge.lean`, census 97, gates green): note that
  `L_a = Q_{√a}∘Θ_a` was ALREADY definitional here — `Necessity/Theta.lean`
  defines `theta := Q_{√a}⁻¹ ∘ seqLeftMul` and `quadRep_theta` states the
  factorization — so the only missing piece was reading it at the PRODUCT level
  rather than through the linear extension.  Now
  **`sp_eq_quadRep_theta` : `P.sp a b = Q_{√a}(Θ_a b)`** for an invertible
  effect `a` and any effect `b` (via `seqLeftMul_apply_effect`), and
  **`sp_eq_quadRep_jordanAuto`** — the same with M3 attached, so the product is
  `Q_{√a}` applied to a certified **Jordan automorphism**.  Axioms verified
  first-hand: core only.
  **TORUS TARGET DONE 2026-08-05** (`Necessity/TorusAction.lean`, census 98,
  gates green, zero sorries): `torusU t r := diagonal (e^{i t r_k})` with
  `torusU_conjTranspose`, `torusU_diag_cancel`, `torusU_unitary` (BOTH ᴴ-orders);
  **`adU_torusU_entry`** — the whole conjugation in one line, because
  `Matrix.diagonal_mul`/`mul_diagonal` give entry formulas directly (do NOT go
  through `mul_apply` sums: the sum route was tried and is far worse);
  **`torusU_fixes_frameProj`**; and **`torusU_block`** — `Ad_{U_t(r)}` rotates
  the `(i,j)` block by exactly the angle `t(r_i − r_j)`, i.e. the SAME angle
  `complex_perFrame_unconditional` produces for the comparison map's block
  generator.  So both sides of the identification are now computed.
  TRAPS: `Matrix.diagonal_conjTranspose` leaves a diagonal-of-star, so the
  matrix equality needs `congr 1` BEFORE `funext` (a bare `funext k` on a
  matrix equality leaves a function-valued goal); the subst trap recurs —
  `subst hai` with `hai : a = i` eliminates the THEOREM PARAMETER `i`, breaking
  every later mention, so use `rw [hai, hbj]` (safe direction) instead; and
  exponential combining must be done in an explicit `calc` (the goal has the
  `+ star(...) * 0` tail from the block expansion, so `rw [← Complex.exp_add]`
  cannot find its pattern in place).
  NEXT for the ℂ lane (the genuinely remaining paper-analytic step): identify
  that Jordan automorphism with `Ad_{a^{it_F}}`.  All the pieces are in the
  tree — `Θ_a` fixes the frame (`thetaNorm_fixes_frameProj`), acts on each
  block by a rotation whose angle is `t_F(r_i − r_j)`
  (`complex_perFrame_unconditional`), and `χ̃(r) = exp(dχ(r))`
  (`chiTilde_eq_exp_dChi`) — so the remaining work is exponentiating the
  block-generator statement back to the group level and comparing with the
  twist conjugation entrywise (M1's `Hermitian/Twist.lean` supplies
  `a^{1/2+it}`).
  **SPANNING LEMMA DONE 2026-08-05** (`Necessity/FrameBlockSpan.lean`,
  census 99, gates green, zero sorries): `sum_eq_two_of_support` (no Mathlib
  lemma for a sum with two-element support — built from `Finset.sum_pair` +
  `Finset.sum_subset`), `mat_sum`, `diag_eq_ofReal`, and
  **`eq_frame_add_blocks` : `x = Σ_i x_ii • p_i + ½ Σ_{i≠j} blockHerm i j
  (x_ij)`** — the ½ because the ordered `offDiag` sum visits each unordered pair
  twice; hence **`linearMap_eq_of_frame_block`**: two ℝ-linear maps agreeing on
  the frame and on every block are equal.  NOTE: the rank-one spanning lemma
  (`span_rankOne_eq_top`) does NOT substitute — different spanning set.
  **TWIST IDENTIFICATION ASSEMBLED 2026-08-05**
  (`Necessity/TwistIdentification.lean`, census **100**, gates green, zero
  sorries, FIRST-PASS CLEAN): `thetaNorm_symm_fixes_frameProj` and
  **`chiTilde_fixes_frameProj`** — the comparison character fixes every frame
  projection UNCONDITIONALLY (both factors of χ̃ do); then
  **`chiTilde_eq_adU_of_block`** — given χ̃'s GROUP-level block action,
  `χ̃(r) = Ad_{U_t(r)}` as ℝ-linear maps, i.e. the paper's `Θ_a = Ad_{a^{it}}`,
  via `linearMap_eq_of_frame_block` (frame half discharged here, torus half by
  `torusU_fixes_frameProj`/`torusU_block`); and
  **`sp_eq_quadRep_adU` : `a • b = Q_{√a}(Ad_{U_t(r)} b)`** — the shape of
  mthm:master's complex case at the product level.  Axioms verified first-hand
  on all three: core only.
  **REMAINING for the ℂ lane: exactly ONE input** — the group-level block action
  of χ̃, i.e. exponentiate `complex_perFrame_unconditional`'s GENERATOR statement
  (`ρ_{ij}(dχ(r)) = (t_F(r_i−r_j))•rotJ`) to the group level.  Two viable routes:
  (i) `chiTilde_eq_exp_dChi` + the fact that dχ(r) preserves each block
  (`dChi_preserves_corner`) and acts there as the rotation generator, so `exp`
  restricted to the block is the rotation — needs `exp` of a restriction to an
  invariant 2-dim subspace; (ii) CHEAPER — `chiTilde_block_exists` already says
  χ̃(r) acts on each block by a UNIT-MODULUS scalar, and `chiTilde_add` +
  line-continuity make `r ↦ that scalar` a continuous character of ℝⁿ into the
  circle, so **M5's `circleCharacter_linear_functional` applies directly** and
  gives `exp(i·ψ_{ij}(r))` with ψ_{ij} ℝ-linear; matching ψ against the
  generator identifies it with `t_F(r_i − r_j)`.  Route (ii) reuses the rank-two
  lifting step and avoids all operator-exponential work — TRY IT FIRST.
  **BLOCK CHARACTER PACKAGED 2026-08-05** (`Necessity/BlockCharacter.lean`,
  census 101, gates green, zero sorries, FIRST-PASS CLEAN):
  `chiEntry r i j : ℂ →ₗ[ℝ] ℂ` (the block action as a map);
  **`chiTilde_block_eq`** — upgrades the EXISTENCE statement
  `chiTilde_block_exists` to a COMPUTED value (the block's `(i,j)` entry reads
  the parameter back by `blockHerm_entry`), which is what makes the action
  usable rather than merely existent; `chiEntry_normSq` (isometry);
  `chiEntry_zero` (identity at `r = 0`); **`chiEntry_add`** (multiplicativity in
  `r`, from `chiTilde_add` + block invariance); and `chiEntry_isCharacter`
  bundling the three laws.
  **REMAINING to close the ℂ lane — one step, and it is now purely algebraic**:
  `r ↦ chiEntry r i j` is a continuous one-parameter family of ℝ-linear
  ISOMETRIES of ℂ with `chiEntry 0 = id`.  Two ways to finish: (α) feed it to
  `multiParameter_eq_exp` in the real Banach algebra `ℂ →L[ℝ] ℂ`, then note the
  generator is the entry map of `dχ` which `dChiEntry_eq` already shows is
  multiplication by `i·t_{ij}(r)`, and `exp` of a ℂ-multiplication is the
  ℂ-multiplication of `exp` (needs `NormedSpace.map_exp` along the algebra
  embedding `ℂ → (ℂ →L[ℝ] ℂ)`); (β) show each `chiEntry r i j` is
  ℂ-multiplication directly (an ℝ-linear isometry of ℂ fixing orientation is
  multiplication by a unit-modulus scalar — orientation follows from
  connectedness to `id` at `r = 0`), then M5's
  `circleCharacter_linear_functional` applies verbatim.  (α) has no topological
  side conditions and reuses `dChiEntry_eq`; prefer it.
  **EXP-TRANSFER SUB-STEP DONE 2026-08-05** (`Necessity/MulEmbedding.lean`,
  census 102, gates green, zero sorries): `mulByCLM`/`mulBy : ℂ →+* (ℂ →L[ℝ] ℂ)`
  (the embedding of ℂ in its own ℝ-linear endomorphisms), `mulBy_continuous`
  (ℝ-linear between finite-dimensional spaces), and
  **`exp_mulBy` : `exp (mulBy w) = mulBy (exp w)`** via Mathlib's
  `NormedSpace.map_exp` (which DOES exist, for any continuous ring hom — no need
  to hand-roll a power-series argument), plus `exp_mulBy_I` /
  `exp_generator_is_rotation` for the case the identification uses: the
  exponential of the skew generator `z ↦ (c·i) z` is the rotation
  `z ↦ e^{ic} z`.  TRAP: `Complex.exp_eq_exp_ℂ` must be rewritten in the
  FORWARD direction here (the `NormedSpace.exp` on ℂ is the one `map_exp`
  produces), the opposite of the `RankTwo/Lifting.lean` usage.
  **BOTH SUB-STEPS DONE 2026-08-05 — THE BLOCK ACTION IS A ROTATION**
  (`Necessity/BlockRotation.lean`, census 103, gates green, zero sorries):
  `chiEntryCLM` + `chiEntryCLM_zero`/`chiEntryCLM_mul`;
  **`chiEntryCLM_continuous_line`** (from `continuous_chiTilde_line` +
  `entryCLM`, then RECONSTRUCT the map from its values at `1` and `I` through an
  explicit ℝ-linear `ℂ × ℂ → (ℂ →L[ℝ] ℂ)` closed by
  `continuous_of_finiteDimensional` — the `smulRightL` route gets STUCK on
  `NormedSpace ℝ ?m` instance metavariables, do not use it);
  `exp_apply_hasDerivAt_gen` (the general-space form of the HermitianMat
  derivative lemma); **`chiEntry_eq_exp`/`chiEntryGen`** via
  `multiParameter_eq_exp` in `ℂ →L[ℝ] ℂ`; **`chiEntryGen_skew`** (differentiate
  the constant `chiEntry_normSq` at `0` — the `dChi_block_skew` pattern reused);
  and **`chiEntry_is_rotation` : `chiEntry r i j z = e^{i c(r)} z`** with
  `c(r) = (gen r 1).im`, via `skew_linear_eq_I_smul` + `exp_generator_is_rotation`.
  Axioms verified first-hand: core only.
  **COEFFICIENT BOOKKEEPING DONE + IDENTIFICATION FIRES 2026-08-05**
  (`Necessity/BlockAngle.lean`, census 104, gates green, zero sorries):
  **`chiEntryGen_eq_dChiEntry`** — the abstract generator of the block character
  and the entry map of `dχ` are the derivative at `0` of the SAME real function
  `t ↦ chiEntry (t•r) i j z`, so `HasDerivAt.unique` equates them (no new
  analysis, and it AVOIDS the exp-restricted-to-an-invariant-subspace problem
  entirely — that was the feared route); hence
  **`chiEntry_rotation_tval` : `chiEntry r i j z = e^{i t_{ij}(r)} z`** in closed
  form (via `dChiEntry_eq`'s skew classification), `chiTilde_block_rotation` at
  the HermitianMat level, and then **`chiTilde_eq_adU`** — given the collapsed
  rates `t_{ij}(r) = t (r_i − r_j)`, `χ̃(r) = Ad_{U_t(r)}`, i.e. the paper's
  `Θ_a = Ad_{a^{it}}` — plus **`sp_eq_quadRep_torus`**, the product-level form
  `a • b = Q_{√a}(Ad_{U_t(r)} b)` with the comparison map now IDENTIFIED rather
  than merely certified.  Axioms verified first-hand on both capstones: core only.
  **TORUS-FACTOR = MATRIX POWER DONE 2026-08-05 — THE ℂ LANE NOW REACHES THE
  PAPER'S LITERAL CONCLUSION SHAPE** (`Necessity/TwistPower.lean`, census 105,
  gates green, zero sorries, capstone axioms verified first-hand = core only):
  `ofReal_polar` (the scalar polar identity, stated in `Complex.ofReal`) and
  **`twistFactor_diagFamily` : `√a · U_t(r) = a^{1/2+it}`** on the diagonal
  family — pure spectral bookkeeping, because the character parameter already IS
  the log-spectrum (`diagFamily r = diag(e^{r_k})`, so `Real.log_exp` supplies
  `log λ_k = r_k`); no cfc multiplicativity, no spectral theorem. Hence
  **`sp_eq_twistSeq_diagFamily` : `a • b = a^{1/2+it} b a^{1/2−it}` = M1's
  `twistSeq t`**, for every effect `b`, with the comparison-map hypothesis
  discharged internally (`chiTilde_of_nonpos` + `thetaNorm_apply_eq_theta`) so
  the only inputs are S2, the M3 Jordan property, and the rate collapse.
  TRAPS: the carrier's diagonal coercion is `RCLike.ofReal`, the trig lemmas'
  is `Complex.ofReal` — they DISPLAY IDENTICALLY and are defeq but NOT
  syntactically equal, so `ring`/`rw` fail on a goal that looks like `A+B=B+A`
  while `exact` (defeq-tolerant) closes it: state the scalar identity as its own
  lemma in `Complex.ofReal` and discharge the matrix goal by `exact`. Also:
  `push_cast` un-merges `Complex.cos ↑(t*x)` into `Complex.cos (↑t*↑x)` and
  breaks the match — do the cast bookkeeping inside the scalar lemma only.
  ★OPS TRAP (cost a restore): `Necessity/TwistIdentification.lean` was ALREADY a
  tracked file (it holds `chiTilde_eq_adU_of_block`/`sp_eq_quadRep_adU`, which
  BlockAngle consumes); writing a new file under that name silently overwrote it
  and STILL compiled, because `lake env lean` on the new file read the STALE
  .olean of the old one. `git status` (M vs ??) is the only cheap tell — check it
  BEFORE writing any "new" file, and run a full `lake build`, not just
  `lake env lean`, before believing a new module is green.
  **UNIQUENESS HALF DONE 2026-08-06** (`Necessity/TwistUniqueness.lean`, census
  106, gates green, capstone axioms verified first-hand = core only):
  `twistFactor_diagFamily_diagonal` (the twist factor merged into ONE diagonal
  matrix `diag(√(e^{r_k})e^{i t r_k})`), `twistSeq_diagFamily_entry` (so the
  twist product reads off entrywise: `g_k · b_{kl} · conj g_l`), the probe
  effect `pairProj i j` = the rank-one projection `½(e_i+e_j)(e_i+e_j)*` with
  `pairProj_isProjection`/`isEffect`/`entry = ½` (built on ProjectionOrder's
  `rankOne`; idempotence from `(rankOne ψ)² = (ψ*ψ)•rankOne ψ` with `ψ*ψ = 2`),
  and **`twist_param_unique`: agreement of `twistSeq t₁` and `twistSeq t₂` on
  all effects forces `t₁ = t₂`** — probe at `a = diag(e^x,1,…)` for
  `x ∈ (−1,0)`, cancel the positive factor, and `real_character_unique` (M2's
  A3-discharge) collapses the parameters with no 2π ambiguity. Needs only
  `2 ≤ N`, so it also serves the rank-two lane. TRAPS: a bare `= 2` on the RHS
  of a `⬝ᵥ` equation makes the scalar type infer as ℕ and every `Pi.single`
  argument then mis-elaborates — ascribe `(2 : ℂ)`; `Pi.single_star` is stated
  `Pi.single i (star a) = star (Pi.single i a)` so you need `←` to simplify
  `star (Pi.single i 1)`; `add_dotProduct`/`single_dotProduct`/`smul_dotProduct`
  live in the ROOT namespace, not `Matrix` (same for `dotProduct` itself);
  `star` of a lambda needs `Pi.star_apply` before `ring` can see the entry.
  REMAINING for the ℂ lane — **(ii) uniqueness is now DONE (see above)**; two
  items left, and the general-`a` route is DECODED AT SOURCE (all API verified
  present 2026-08-06):
  **(i) general PosDef `a` — DONE 2026-08-06** (`Necessity/TwistGeneral.lean`,
  census 107, gates green, zero sorries, NO heartbeat bumps, capstone axioms
  verified first-hand = core only): `diagFamily_log_eigenvalues` (the two
  diagonal spellings agree, `Real.exp_log` on `PosDef.eigenvalues_pos`),
  `eq_adU_diagFamily` (the spectral theorem in the shape the lane consumes:
  `a = Ad_U (diagFamily (log ∘ eigenvalues))`), `log_eigenvalues_nonpos` (an
  effect's eigenvalues are ≤ 1 by the vendored
  `le_smul_one_imp_eigenvalues_le`, so the diagonal base point is itself an
  effect), **`twistFactor_adU`** (unitary covariance
  `(Ad_U a)^{1/2+it} = U a^{1/2+it} Uᴴ`, both real cfc legs by
  `cfc_conj_unitary`) plus its matrix-form corollary `twistFactor_adU_mat`, and
  **`sp_eq_twistSeq_transport` — the twist form transports from a diagonal base
  point to any positive-definite one** (conjugations cancel via `conjProduct_sp`
  + `conj_conj`; the unitary is a PARAMETER so the statement stays cheap).
  ★★TRAPS (three whnf timeouts, none fixed by raising heartbeats — raising the
  budget is the WRONG move for all three): (1) a `show` whose term has
  `HermitianMat.conj`'s arguments in the wrong order sends elaboration flailing
  into a 1.6M-heartbeat timeout instead of erroring — prefer syntactic
  `rw [adU, HermitianMat.twistSeq, conj_conj, …]` over any `show` on conj/cfc
  terms; (2) `rw [show U = ↑(⟨U, hmem⟩ : unitaryGroup) from rfl]` rewrites a
  variable by a term CONTAINING that variable — self-referential motive, blows
  up; state a matrix-form corollary instead; (3) closing a unitaryGroup-form
  lemma against a matrix-form goal by `exact` forces the defeq check THROUGH
  `cfc` (spectral machinery) and explodes — get the coercion out of the way
  first with `have hco : ↑⟨U, hmem⟩ = U := rfl; rw [hco] at h`. Also: pinning a
  `conjProduct` at `a.H.eigenvectorUnitary` inside a hypothesis makes the
  STATEMENT itself time out; generalize the unitary to a parameter.
  HISTORICAL decode (superseded by the above, all confirmed at source): the spectral theorem in
  conjugation form is `HermitianMat.eq_conj_diagonal`
  (`A = (diagonal 𝕜 A.H.eigenvalues).conj A.H.eigenvectorUnitary` —
  Vendor/HermitianMat/Basic.lean:555), and `.conj U` IS `adU U`, so
  `a = adU U (diagonal ℂ eigenvalues)` for free. Bridge the two diagonal
  spellings with `diagFamily (Real.log ∘ eigenvalues) = diagonal ℂ eigenvalues`
  (`Real.exp_log` on `Matrix.PosDef.eigenvalues_pos`). Get `r ≤ 0` from
  effect-ness transported backwards (adU Uᴴ inverts adU U, so `diagFamily r` is
  itself an effect, and its `(i,i)` entry gives `e^{r_i} ≤ 1`; the only name to
  find is the PSD-diagonal-entry-nonneg lemma). Transport the product with
  `conjProduct_sp` (`(conjProduct P hU hU').sp a b = adU Uᴴ (P.sp (adU U a)
  (adU U b))`, an `rfl`-simp lemma) + `conjProduct_firstArgContinuous`, apply
  `sp_eq_twistSeq_diagFamily` to the conjugated product, and push the twist
  factor back through `HermitianMat.cfc_conj_unitary`
  (`(A.conj U.val).cfc f = (A.cfc f).conj U` — CFC.lean:209), which is exactly
  the unitary covariance `twistFactor (adU U D) t = U · twistFactor D t · Uᴴ`.
  The rate-collapse hypothesis at each frame comes from `frameTwist_spec`, and
  the SINGLE global `t` from `complex_global_twist_concrete` (its two frame-graph
  inputs stay located hypotheses). NOTE: M3 is discharged, so
  `ThetaPreservesJordan` is no longer a hypothesis to carry —
  `thetaPreservesJordan_of_S2` (KadisonDischarge.lean:324) supplies it from S2.
  **(iii) singular extension + the `∃!` capstone — DONE 2026-08-06**
  (`Necessity/ComplexClassification.lean`, census 108, gates green, zero
  sorries, capstone axioms verified first-hand = core only): `twistProductOn`
  (M1's twist product repackaged as a PINNED `SequentialProductOn` — its core
  already takes `toOrderUnitSpace := inferInstance`, so
  `.toSequentialProductOn` typechecks against the ambient instance by defeq,
  which is exactly what the M2 design decision anticipated) with S2
  (`twistProductOn_firstArgContinuous`), `sp_eq_twistSeq_of_effect` (2.9 applied:
  agreement on INVERTIBLE effects extends to ALL effects), and
  **`exists_unique_twist` — a product with S2 on `H_N(ℂ)` (N ≥ 2) agreeing with
  some twist product on the invertibles has a UNIQUE `t` with
  `a • b = a^{1/2+it} b a^{1/2−it}` on every pair of effects.**  That is
  `PaperA.UniqueTwistConclusion`'s shape over the pinned interface (the
  instance-quantified spelling is the one the M2 design decision rules out).
  **★★ THE ℂ ROW OF `mthm:master` IS MACHINE-CHECKED — 2026-08-06**
  (`Necessity/RateFromCoupling.lean` + `Necessity/ComplexMaster.lean`, census
  110, gates green, zero sorries, axioms verified first-hand = Lean core only).
  `tvalLm_of_coupling` is the one missing bookkeeping link: evaluate the abstract
  coupling equation `ρ_{ij}(dχ r) = (c(r_i−r_j))•J` at the block vector `z = 1`
  and read the second coordinate — the left side is `(0, t_{ij}(r))` by
  `dChiEntry_eq`, the right is `(0, c(r_i−r_j))` because `J(1,0) = (0,1)`, so the
  abstract per-frame parameter IS the concrete phase rate.  Then
  `sp_eq_twistSeq_of_frameGraph` (one global `t` governs every invertible
  effect: diagonalize into the eigenframe, read the rate there via
  `frameTwist_spec` + `hglob`, apply the diagonal theorem, transport back) and
  **`complex_classification` : for an S1–S7 product with S2 on `H_N(ℂ)`, N ≥ 3,
  there is a UNIQUE real `t` with `a • b = a^{1/2+it} b a^{1/2−it}` on EVERY
  pair of effects, singular ones included.**  Carried hypotheses, exactly: the
  `SequentialProductOn` fields (S1, S3–S7), S2, `N ≥ 3`, and the paper's two
  frame-graph facts as located hypotheses (`connected` =
  `lem:frame-connectivity`, `overlap` = cross-coherence).  The Jordan property
  of the comparison map is DERIVED (M3), not assumed; zero custom axioms.
  ℂ-lane status (historical): the necessity chain was complete end-to-end — S1–S7 + S2 (+
  the frame-graph located hypotheses feeding the global `t`) ⟹ the unique twist
  form on all effects, with M1 supplying sufficiency. What remains for the ℂ
  per-type `mthm:master` row is the *bookkeeping* assembly that threads
  `frameTwist_spec` + `complex_global_twist_concrete` into
  `sp_eq_twistSeq_transport`'s `hform` slot to discharge `exists_unique_twist`'s
  `hsome` hypothesis unconditionally.
  **ℂ-lane status (historical):** the identification chain is complete.  What remains to reach
  `PaperA.UniqueTwistConclusion` is bookkeeping between the character parameter
  `r` and the spectrum of `a` (i.e. `r = log spec a`, so that `U_t(r) = a^{it}`
  literally), the uniqueness half (two twist parameters agreeing on all effects
  are equal — the `t ↦ e^{it log λ}` injectivity, same shape as
  `real_character_unique`), M1's `twistSequentialProduct` as the sufficiency
  witness, and 2.9's `sp_eq_on_effects_of_eq_on_posDef` to extend from
  invertibles.  HISTORICAL: identify `c(r) = (chiEntryGen … r 1).im` with
  `t_F (r_i − r_j)`.  Both are ℝ-linear in
  `r` (the former because `chiEntryGen` is linear), both vanish on the
  coalescence hyperplane, and `complex_perFrame_unconditional` pins the
  proportionality; so this is `angle_factor`-style linear algebra
  (`MasterTheorem/RankTwo.lean` has the rank-two analogue already), NOT further
  analysis.  Then `chiTilde_eq_adU_of_block` fires and `sp_eq_quadRep_adU` gives
  mthm:master's complex shape.
  HISTORICAL (superseded by the above, kept for provenance) — the two sub-steps
  were: (1) feed
  `chiEntry_isCharacter`'s laws to `multiParameter_eq_exp` in `ℂ →L[ℝ] ℂ` to get
  `chiEntry r i j = exp (E r)` for a unique ℝ-linear `E` (needs the line
  continuity of `chiEntry`, which follows from `continuous_chiTilde_line` +
  `entryLm`/`blockHermLm` continuity); (2) show `E r` is skew — the SAME
  differentiate-the-constant-norm pattern already used for `dChi_block_skew`,
  since `chiEntry_normSq` gives the constant — and then
  `skew_linear_eq_I_smul` writes `E r = mulBy (i·c(r))` with `c` ℝ-linear
  (linearity of `c` from linearity of `E`), so `exp_generator_is_rotation`
  finishes and `chiTilde_eq_adU_of_block` fires.
  TRAPS: the subst trap AGAIN (`subst hab` with `hab : a = b` kills the ext-local
  needed later) — use `rw [if_pos hab]` and derive the index facts by hand;
  `x.H` gives `star (x_ba) = x_ab` at index `(a,b)` (NOT `(b,a)` — the
  orientation flips and costs a `star_star`); `Complex.real_smul` is needed to
  turn `(1/2 : ℝ) • (z : ℂ)` into a product before `ring`.  Then `PaperA.UniqueTwistConclusion` is reachable with M1's
  `twistSequentialProduct` as the sufficiency witness and 2.9's
  `sp_eq_on_effects_of_eq_on_posDef` extending from invertibles.
  Then M4–M7.
  * Then: τ-preservation ⟹ build the ray map `ℙ ℂ (EuclideanSpace ℂ (Fin N))`
    → itself from Φ's action on atoms (bridge 1: `IsAtomProjection` is
    order-theoretic, so Φ permutes rank-ones; `exists_rankOne` extracts the
    vector), check `TransProbPreserving` against
    `transProbVec ψ φ = ‖⟪ψ,φ⟫‖²/(‖ψ‖²‖φ‖²)` (for unit vectors = τ), apply
    the vendored `Projectivization.wigner_rigidity`, and finish
    unitary/antiunitary ⟹ Jordan automorphism (both branches: conjugation and
    transpose-conjugation preserve the symmetrized product).
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

- **4.1 Real — SCOPED AT SOURCE 2026-08-06: it is a GENERALIZATION REFACTOR of
  the M2 chain, not a fresh development.** Measured ℂ-dependence of the 16
  `Necessity/` files the ℝ row needs (count of `ℂ` tokens vs count of genuinely
  complex constructs `Complex.I`/`Complex.exp`/`normSq`/`star_def`/`starRingEnd`):
  DiagonalFamily 26/0, Theta 39/0, ThetaCocycle 30/0, ChiExtension 14/0,
  ChiContinuity 34/0, CoalescenceInstance 40/0, CoalescenceDiff 10/0,
  BlockInvariance 17/0, LeftMultiplication 38/0, PseudoInverse 21/0,
  SharpEffects 28/0, FirstArgument 27/0, OneParameter 0/0 — **thirteen files use
  ℂ only as "the scalar field"**; only ComparisonInstance (68/13, the quarter
  identity + field-transfer star bookkeeping), BlockModel (25/6) and
  BlockTransport (18/6, both the square law's `normSq`) carry real complex
  content, and all three generalize to `‖z‖²`/`RCLike.normSq`. The vendored
  substrate is ALREADY RCLike-general (Basic/Order/CFC are stated over
  `[RCLike 𝕜]`, e.g. `zero_le_iff : 0 ≤ A ↔ A.mat.PosSemidef`), so the port is
  `ℂ ⇝ 𝕜` with `[RCLike 𝕜]` plus three square-law rewrites. **The ℝ row needs
  NONE of the phase machinery** (BlockSkew, PhaseCocycle, PhaseAnchor,
  BlockAngle, BlockRotation, TorusAction, TwistPower, TwistUniqueness,
  TwistGeneral, RateFromCoupling): over ℝ the Peirce block is
  ONE-dimensional, so the skew block generator is 0 outright, `χ̃ = id`, and the
  product is Lüders `a • b = Q_{√a} b` — the kill is `real_luders`'s concrete
  analogue and costs a lemma, not a lane. Recommended order: generalize
  DiagonalFamily → ComparisonInstance → Theta/ThetaCocycle → Chi* →
  Coalescence* (mechanical, compiler-driven), then the 1-dimensional-block kill.
  Risk LOW (was LOW), effort MEASURED rather than guessed — **but see the
  correction below before trusting the token counts.**

  **FIRST STEP TAKEN 2026-08-06 + AN HONEST CORRECTION TO THE ESTIMATE.**
  Done and green (whole tree rebuilt, 3067 jobs, census 110, custom axioms still
  exactly `[]`): the two vendored eigenvalue↔order lemmas
  `HermitianMat.le_smul_one_imp_eigenvalues_le` and
  `eigenvalues_le_imp_le_smul_one` are now stated over `RCLike 𝕜` instead of `ℂ`,
  and the first one's 15-line by-hand `ComplexOrder` quadratic-form proof
  collapsed to ONE line — both are just the two directions of
  `Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff`, which was **already**
  `𝕜`-general in `Vendor/Matrix.lean`. Every existing ℂ call site still
  typechecks unchanged (a more general lemma applies at ℂ). Drift recorded in the
  file's docstrings.
  ★**DIAGNOSIS, and a correction of a correction (both recorded, 2026-08-06).**
  First attempt at generalizing `Hermitian/OrderUnit.lean`'s
  `le_zero_of_forall_le_smul_one` and `eigenvalues_mem_Icc_of_effect` produced
  `whnf`/`isDefEq` timeouts, and I first wrote that up as "generic RCLike
  instance resolution is inherently expensive here". **That was wrong.**  Retried
  with the scalar pinned at the call sites and both generalize with NO timeout and
  NO heartbeat bump (whole tree green, 3067 jobs, census 110, custom axioms still
  exactly `[]`).  The real mechanism: the generalized lemmas' scalar binder is
  AUTO-BOUND, so it cannot be named — `(𝕜 := …)` is an invalid argument name —
  and if the scalar is left to be inferred through a postponed tactic block
  (`by simpa using h1`), it stays a metavariable, universe defaulting picks
  universe 0 (i.e. ℂ) while the surrounding context is at `u_2`, and the ensuing
  instance searches over an unknown scalar flail into a whnf timeout.  **The
  idiom that works: pin the carrier argument explicitly, `(A := a)`, and replace
  postponed `simpa using` glue with an explicit `have` + `linarith`/`rw`.**  A
  whnf timeout in a generalization step is therefore a signal to look for an
  unpinned scalar metavariable FIRST, before reaching for `maxHeartbeats` (which
  would not have helped: 1.6M failed).  With this idiom the 13/16
  "zero genuinely-complex tokens" measurement DOES translate into effort: the port
  is mechanical, leaf-first, one file per commit with a full `lake build` after
  each.  Carrier layer status: `le_zero_of_forall_le_smul_one` and
  `eigenvalues_mem_Icc_of_effect` are now `𝕜`-general (`abs_eigenvalues_le_ouNorm`
  and `norm_le_sqrt_card_mul_ouNorm` deliberately left at ℂ — they belong to the
  order-unit-norm comparison, not to the Θ chain's critical path).

  ★**DESIGN CONSTRAINT discovered by attempting `Necessity/DiagonalFamily.lean`
  (2026-08-06, attempt reverted, tree left green).**  Generalizing the frame/family
  DEFINITIONS is not a token substitution, for a structural reason: lemmas like
  `frameProj_mat (i : n) : (frameProj i).mat = Matrix.diagonal …` mention the
  scalar ONLY inside `frameProj`, so with an implicit scalar nothing determines it
  and every such lemma fails with "typeclass instance problem is stuck, it is often
  due to metavariables" (ten of them in that one file).  The vendored layer already
  solved this: `HermitianMat.diagonal 𝕜 f` takes the scalar **explicitly**, and the
  generalized `frameProj`/`diagFamily` must do the same.  Two routes, pick before
  starting:
  (A) make the scalar explicit in place — `frameProj 𝕜 i`, `diagFamily 𝕜 r` — and
      mechanically rewrite every ℂ call site (`frameProj i` ⇝ `frameProj ℂ i`)
      across the ~20 `Necessity/` files that use them.  Wide but shallow; one sed
      plus compiler-driven cleanup.
  (B) **RECOMMENDED — zero blast radius**: add scalar-explicit general versions
      alongside (`frameProjK 𝕜 i`, `diagFamilyK 𝕜 r`) and redefine the existing ℂ
      names as abbreviations of them; each existing ℂ lemma then becomes its
      general counterpart instantiated at ℂ (proof bodies move, statements don't),
      so the ℂ row keeps compiling untouched at every step and the ℝ row consumes
      the `K` versions.  This also keeps every ℂ-row proof as a live regression
      test on each generalization.
  Either way the work is mechanical; route (B) is the one to take, and route (A)
  was TESTED AND REJECTED with evidence (below).

  **ROUTE (A) TESTED AND REJECTED, ROUTE (B) STARTED — 2026-08-06.**
  Generalizing `DiagonalFamily.lean` in place (implicit scalar + pinning the ten
  ambiguous statements) *does* compile the file itself, but the full build then
  fails downstream at `Necessity/Chi.lean:55` — an intermediate `have` inside a
  ℂ-lane proof (`((diagFamily r).cfc Real.sqrt).mat * … = (diagFamily r).mat`)
  has nothing to pin the scalar, so it goes stuck. That is the general shape of
  the leak: every unconstrained intermediate statement in a downstream proof
  needs a pin, an unbounded scatter across the ℂ lane. Route (A) is therefore
  rejected, with `Chi.lean:55` as the recorded witness.
  **DONE instead (census 111, gates green, whole tree rebuilt at 3068 jobs):**
  * `Necessity/SharpEffects.lean`'s `mat_finsetSum` generalized ℂ → `RCLike 𝕜`
    (backward-compatible; note its `omit [Fintype n] in` had to go — with the new
    instance binder the section variable becomes referenced).
  * **`Necessity/DiagonalFamilyGen.lean` (NEW)**: the whole frame/family layer over
    an arbitrary `RCLike 𝕜` with the scalar EXPLICIT — `frameProjG 𝕜 i`,
    `diagFamilyG 𝕜 r` — carrying every lemma the ℂ file has (mat, zero, mul,
    commute, posDef, isEffect, frame projections, orthogonality, `sum_frameProjG`,
    the frame decomposition, commutation with the frame). Proofs are the ℂ ones with
    `Complex.ofReal_mul ⇝ RCLike.ofReal_mul` and
    `Complex.real_smul ⇝ RCLike.real_smul_eq_coe_mul`; nothing else changed, which
    is the concrete confirmation that this layer's content was never complex.
  The ℂ-specialized `DiagonalFamily.lean` is untouched, so the complex row still
  compiles exactly as before. **Next file for the same treatment: the Θ layer
  (`ComparisonInstance.lean` → `…Gen`), then `Theta`/`ThetaCocycle`, `Chi*`,
  `Coalescence*`; then the ℝ-specific ending, which is short — over ℝ the Peirce
  block is 1-dimensional so the skew generator vanishes and `χ̃ = id`.**
  Traps for the next pass: in `unfold`/`rw` argument position use the BARE name
  (`unfold diagFamilyG`), never the applied form (`unfold diagFamilyG 𝕜` is a
  syntax error).

  ★★**RECIPE REFINED 2026-08-06 — two file KINDS, and only one needs a twin.**
  `Necessity/LeftMultiplication.lean` (394 lines, the whole `seqLeftMul`
  construction: ℕ/ℚ/ℝ-homogeneity, the cone extension `spPos`, the linear map and
  its positivity/monotonicity/unit law) and `Necessity/FirstArgument.lean`
  (lem:homog(ii)) are now generalized to `RCLike 𝕜` **IN PLACE**, and the whole
  tree still builds (3068 jobs, census 111, custom axioms exactly `[]`) with
  **zero downstream edits**. Reason: their statements are parameterized by
  `P : SequentialProductOn (HermitianMat n 𝕜)`, so every downstream use passes a
  concrete ℂ-typed `P` and the scalar is pinned automatically. So:
  * **P-parameterized files ⇒ generalize IN PLACE** (cheap, no duplication).
  * **files defining carrier CONSTANTS** (`frameProj`, `diagFamily`) ⇒ need the
    scalar explicit and a `…Gen` twin, because downstream intermediate `have`s
    don't pin them (witness `Chi.lean:55`).
  Mind multi-`namespace` files: `SharpEffects.lean` has two `namespace Necessity`
  blocks each with their own `variable` line — a single-shot insertion of the
  scalar variable leaves the second block with an auto-bound `𝕜` and the failure
  reads "failed to synthesize AddGroup 𝕜".
  ★**THE NEXT BLOCKER IS NOT IN `Necessity/` AT ALL**: `SharpEffects` and
  `PseudoInverse` do NOT generalize yet because they ride
  `Hermitian/Resolution.lean`, whose spectral layer is ℂ-pinned
  (`variable {ι} {R : ι → Matrix n n ℂ}` and `{M : HermitianMat n ℂ}`, so
  `resolution_mul` and `specProj` are ℂ-only). **Generalize
  `Hermitian/Resolution.lean` first** — it is the gate for the whole
  sharp-effects/pseudo-inverse/Θ half of the chain.

  **GATE OPENED + TWO MORE FILES LANDED 2026-08-06** (census 111, gates green,
  tree at 3068 jobs, custom axioms exactly `[]`):
  * `Hermitian/Resolution.lean` generalized to `RCLike 𝕜` **in place** — 240 lines,
    13 ℂ tokens, zero genuinely-complex constructs, and it went through on the
    first compile with no proof edits at all. This was the gate.
  * `Necessity/SharpEffects.lean` (the whole Gudder–Greechie sharpness layer plus
    the vdW 5.2 orthogonal-family value law) then generalized in place, unblocked
    by Resolution exactly as predicted.
  Running total generalized to `RCLike 𝕜`: the two vendored eigenvalue↔order
  lemmas, two carrier lemmas in `Hermitian/OrderUnit.lean`, `Hermitian/Resolution.lean`,
  `Necessity/LeftMultiplication.lean`, `Necessity/FirstArgument.lean`,
  `Necessity/SharpEffects.lean`, plus the new `Necessity/DiagonalFamilyGen.lean`.
  ★**NEXT FILE AND ITS DIAGNOSIS — `Necessity/PseudoInverse.lean` (reverted, do
  this one deliberately).** It is the first file whose generalization does NOT fall
  out of a sed. Two distinct causes, both diagnosed:
  (1) higher-order unification gives up on the projection family — the elaborator
      shows `sum_smul_proj_isEffect (fun μ x => ?m.34) …`, i.e. `?p μ = b.specProj μ`
      is left unsolved. Fix: pass it explicitly, `(p := fun μ => b.specProj μ)`
      (also needed for `sp_orthFamily_value`).
  (2) even with the family pinned, `whnf` still times out, because the goal
      `IsEffect (pseudoInv b)` has to be made defeq to the lemma's conclusion
      `IsEffect (∑ i ∈ s, lam i • p i)` — that unfolding of `pseudoInv` through the
      spectral machinery is cheap at concrete ℂ and expensive generically.
      **Fix: rewrite `pseudoInv` into its explicit sum form FIRST (`rw [pseudoInv]`
      or a `show`), then apply the lemma — do not make the elaborator discover the
      sum by unfolding.**  Raising `maxHeartbeats` does not help (800k tried, and it
      only made the metavariable flail longer, which is what exposed cause (1)).
  **`PseudoInverse.lean` DONE 2026-08-06** — both diagnosed fixes worked exactly as
  written (pin `(p := fun μ => b.specProj μ)` on `sum_smul_proj_isEffect`,
  `sp_orthFamily_value` and `sp_orthFamily_comm`; convert `pseudoInv_isEffect` from
  term mode to `by rw [pseudoInv]; exact …` so the sum form is *given* rather than
  discovered). Tree green, census 111, custom axioms exactly `[]`.

  **`Theta.lean` + `ThetaFix.lean` DONE 2026-08-06 — and the previously recorded
  "failure signatures" for them were CASCADE ARTIFACTS.** Once `PseudoInverse` was
  generalized and committed, both files fell out of the plain sed with **zero** pins
  and zero proof edits (`Theta.lean` needed only an `omit [DecidableEq n] in`, and
  note that modifier goes BEFORE the docstring — after it, Lean reports
  "unexpected token 'omit'; expected 'lemma'"). LESSON for the remaining files:
  **do not diagnose a file until its dependencies are generalized** — errors seen in
  a file whose imports are still ℂ-pinned are mostly noise about the boundary, not
  about the file.

  ★**`ThetaCocycle.lean` — THE FIRST GENUINE (non-elaboration) OBSTACLE OF THE PORT,
  reverted, with all three remaining items pinned down:**
  (1) `sp_orthFamily_comm` at :93 needs its family pinned (`(p := …)`), the same
      higher-order-unification fix as `PseudoInverse`;
  (2) ten `(2 : ℂ)` scalars in the Peirce-style computation at :206–:249 survive the
      sed and become `(2 : 𝕜)`;
  (3) **the real content**: it routes the cocycle through
      `HermitianMat.twistFactor_mul_of_commute … 0`, and `twistFactor` is
      *intrinsically* complex (`twistRe + Complex.I • twistIm`).  At `t = 0` the
      complex structure is inessential — `twistFactor a 0 = √a` — so the ℝ row wants
      a small NEW lemma over `RCLike 𝕜`: for commuting positives with
      `m.mat = a.mat * b.mat`, `√m = √a · √b` stated via `cfc Real.sqrt` directly
      instead of via `twistFactor _ 0`. That is the one place in the Θ chain where
      the port needs mathematics rather than substitution, and it is a one-lemma job.
      **THAT LEMMA IS NOW WRITTEN AND GREEN 2026-08-06**
      (`Hermitian/SqrtMul.lean`, NEW, census 112, gates green, axioms core only):
      `HermitianMat.sqrt_mul_of_commute` — `√(ab) = √a·√b` for commuting positives
      over any `RCLike 𝕜`, compiled FIRST TRY. Mathlib has no square-root
      multiplicativity for commuting positive matrices (checked), so it is from
      scratch; the proof keeps `twistFactor_mul_of_commute`'s joint-spectral
      scaffolding — which is entirely field-generic now that
      `Hermitian/Resolution.lean` is generalized — drops the complex structure, and
      needs exactly one scalar input, `Real.sqrt_mul`. Note the proof turns out to
      need only `a`'s positivity (`b`'s is kept in the signature to mirror the twist
      lemma and document scope).
  **`ThetaCocycle.lean` DONE 2026-08-06 — THE WHOLE Θ LAYER IS NOW FIELD-GENERAL**
  (census 112, gates green, tree at 3069 jobs, custom axioms exactly `[]`): all three
  items discharged exactly as recorded — the joint family pinned
  (`(p := fun q => jointProj hab q)`), the ten `(2 : ℂ)` scalars and `two_smul ℂ`
  turned into `𝕜`, and the cocycle's square-root step rerouted from
  `twistFactor_mul_of_commute … 0` (plus its three `twistFactor_zero` rewrites)
  straight to the new `HermitianMat.sqrt_mul_of_commute` — which also SHORTENED the
  proof, since the twist route needed the `t = 0` rewrites and the direct route does
  not. (One extra import needed: `Hermitian.SqrtMul`.)
  **Θ-chain status: `LeftMultiplication`, `FirstArgument`, `SharpEffects`,
  `PseudoInverse`, `Theta`, `ThetaFix`, `ThetaCocycle`, `Resolution`, `SqrtMul`, the
  two vendored eigenvalue↔order lemmas and the two carrier lemmas are all
  `RCLike 𝕜`-general; `DiagonalFamilyGen` supplies the frame/family layer.
  REMAINING for M4.1: `Chi`, `ComparisonInstance`, `ChiExtension`, `ChiContinuity`,
  `CoalescenceInstance` — and there is a ROUTE DECISION to make first (below).**

  ★**THE M4.1 ENDGAME DECISION (analyzed at source 2026-08-06, decide before writing
  code).** Two facts, both checked:
  (1) **The abstract lane gives no shortcut.** `Branches/Real.real_kill` takes
      `ρ`, `dχ`, `T`, `ρ_skew` and `coupling` *directly as arguments* (that is how it
      avoids `rank_ge` and covers `n = 2`). So instantiating it concretely needs the
      whole differential face — χ̃, `dχ`, coalescence, the stabilizer coupling — i.e.
      the ℝ analogue of all of LEDGER 2.6. There is no way to reach `prop:real`
      concretely through the existing abstract kill without that machinery.
  (2) **The five remaining files are exactly the ones that CANNOT be generalized in
      place**, because unlike the Θ layer they mention the frame/family CONSTANTS in
      their statements (`diagFamily r`, `frameProj i`). Generalizing them forces
      either the rejected 281-site sed (`diagFamily ⇝ diagFamilyG ℂ` across ~20 ℂ-lane
      files) or five parallel `…Gen` files. The Θ layer was cheap precisely because it
      is parameterized by `P`; this layer is not.
  **Hence a third option worth pricing before paying for either: a GROUP-LEVEL ℝ
  ending that skips χ̃/dχ/coalescence entirely.** Over ℝ the Peirce block `V_ij` is
  ONE-dimensional, so a Θ that fixes the frame and preserves each block
  isometrically acts on each block as `±1` — no differentiation needed to see this.
  Ruling out `−1` is then a connectedness/continuity argument from `Θ_1 = id` (S2
  gives continuity in the base point; the positive-definite cone is connected).
  Ingredients that argument needs: the ℝ block model (`blockHerm i j (t : ℝ)`,
  markedly simpler than the ℂ one — no phase), the block-isometry statement (the
  `normSq_thetaNorm_block` analogue, whose proof is the square law + frame fixing and
  contains nothing complex), and continuity of `a ↦ Θ_a`. If that works it replaces
  five duplicated files with roughly one, and it never touches `dχ`. **Price both
  routes before continuing; do not start duplicating files by default.**

  ★★**AND THE DECISION-CRITICAL FACT, verified at source 2026-08-06: THE ℝ ROW HAS
  ITS OWN M3 BOULDER, so it cannot be unconditional the way the ℂ row is.** Both
  candidate endings need Θ to preserve the Jordan product (block preservation and the
  block isometry are what transport the Peirce relations, and both take `hjord`). For
  ℂ that is now DERIVED — `thetaPreservesJordan_of_S2` → `orderAuto_preservesJordan`
  → `Projectivization.wigner_rigidity` — but every one of those is stated on
  `HermitianMat (Fin N) ℂ`, and the vendored rigidity theorem is intrinsically complex
  (it is about `ℙ ℂ (EuclideanSpace ℂ (Fin N))` and its unitary/antiunitary
  dichotomy). Over ℝ the corresponding statement is real Kadison/Uhlhorn — unital
  order-automorphisms of `H_n(ℝ)` are `x ↦ O x Oᵀ` for orthogonal `O` — which is in NO
  prover (the 08-04 landscape check covers this) and which the vendored artifact does
  not supply.
  **Consequences, and they are shape-level, not effort-level:**
  * The honest ℝ deliverable is **conditional on `ThetaPreservesJordan` over ℝ carried
    as a located hypothesis**, exactly as the ℂ row stood before M3 closed and exactly
    how the manuscript cites van Imhoff–Roelands for it. That is a legitimate,
    disclosed configuration — but it must be stated as such in THEOREM-MAP, never
    described as "the real row is machine-checked" without the qualifier.
  * ★★**ESTIMATE SHARPENED AT SOURCE 2026-08-06 — making ℝ unconditional needs ONE
    THEOREM, not a redo of M3.** Measured: the ENTIRE M3 chain
    (`Strength`, `StrengthProbe`, `RankOneSpan`, `RayMap`, `WignerBridge`,
    `JordanWitness`, `KadisonDischarge`, `ProjectionOrder`) contains **zero** uses of
    `Complex.I` or `Complex.exp` — the only field-specific content is `Complex.normSq`
    (⇝ `RCLike.normSq`) and a couple of `starRingEnd ℂ` (⇝ `𝕜`), i.e. exactly the
    substitutions this session has performed ~20 times. The Busch–Gudder strength
    function is order-definable and therefore field-blind by construction; the probe,
    the rank-one span, the ray map and the Kadison discharge are all algebra over the
    carrier.
    **The single genuinely complex input is the vendored
    `Projectivization.wigner_rigidity`** (`Vendor/Wigner/WignerRigidity.lean`, ~3.2k
    lines): a transition-probability-preserving self-map of `ℂP^{N-1}` is
    `projMap e` or `projMap e ∘ conj` for a ℂ-linear isometry. Its real analogue is
    **Uhlhorn's theorem over ℝ** — an orthogonality-preserving bijection of `ℝP^{n-1}`
    (`n ≥ 3`) is induced by an orthogonal map — and there is no antiunitary branch to
    handle, since conjugation is trivial over ℝ, so the real statement is *strictly
    simpler* than the complex one already vendored.
    **So the work is: (1) prove real Uhlhorn/Wigner FROM SCRATCH; (2) run the
    established `ℂ ⇝ 𝕜` recipe over the eight M3 files.** Step (2) is mechanical.
    ★**Step (1) cannot be a port — measured 2026-08-06**: the vendored
    `WignerRigidity.lean` is 3179 lines with **85 uses of `Complex.I`, 117 circle/phase
    references and 179 conjugation/antiunitary references**. That bulk IS the phase
    structure: the unit-circle gauge freedom and the unitary-vs-antiunitary dichotomy.
    None of it exists over ℝ, so the file is not portable — **but by the same token the
    real proof is far shorter than 3179 lines**, because those three ingredients are
    exactly what makes the complex proof long. The real argument is the classical one:
    a transition-probability-preserving bijection carries an orthonormal basis to an
    orthonormal basis, the preserved inner products pin the candidate orthogonal map on
    that basis, and over ℝ the only residual freedom is a global sign (no circle, no
    conjugation branch). Estimate: a few hundred lines, self-contained, no dependence on
    the vendored artifact.
    **STARTED 2026-08-06** (`Vendor/Wigner/RealWigner.lean`, NEW, census 131, gates
    green, tree at 3088 jobs, custom axioms exactly `[]`;
    `projMapR_transProbPreservingR` axiom-checked = Lean core only): the setup and the
    EASY inclusion — `transProbVecR` (`|⟨ψ,φ⟩|²/(‖ψ‖²‖φ‖²)` over ℝ) with scale
    invariance in each slot, `transProbR` on `ℝP(E)`, `transProbVecR_isometry`,
    `projMapR` (+ `projMapR_mk`), `TransProbPreservingR`, and
    **`projMapR_transProbPreservingR` : every orthogonal map preserves transition
    probabilities**. Stated over a general real inner-product space, not just
    `EuclideanSpace ℝ (Fin n)`.
    Trap: the representative bookkeeping produces an `ℝˣ`-action, and the scale-invariance
    lemmas take a plain `ℝ` — normalize with `simp only [Units.smul_def]` before
    rewriting, or the pattern will not match.
    **STEP 1 OF THE RIGIDITY DONE (same day)**: `transProbVecR_eq_zero_iff`,
    `transProbR_eq_zero_iff` (`transProb = 0` ⟺ the rays are orthogonal),
    **`TransProbPreservingR.orthogonal`** and `.orthogonal_iff` — a TP-preserving map
    preserves orthogonality of rays, in both directions. Axiom-checked = Lean core only.
    That is the input to the basis argument.
    **STEP 2 DONE (same day)**: `inner_rep_eq_zero_iff` (orthogonality of rays is visible
    on ANY representatives — the `.rep` bookkeeping discharged once and for all),
    `TransProbPreservingR.image_pairwise_orthogonal`, and
    **`TransProbPreservingR.image_orthonormal` — the normalized representatives of the
    image rays form an orthonormal family**. Axiom-checked = Lean core only. So the
    candidate isometry's data now exists: feed an orthonormal basis in, get an orthonormal
    family out.
    Trap: over ℝ use `real_inner_smul_left`/`real_inner_smul_right` and let
    `simp [ha', hb', mul_eq_zero]` finish — going through `inner_smul_left` +
    `starRingEnd` produces coerced disjuncts whose `≠ 0` facts no longer match.
    **STEP 3 DONE (same day)**: `transProbVecR_of_norm_one` (against a UNIT vector the
    transition probability is literally the squared coordinate `⟨ψ,φ⟩²/‖ψ‖²` — over ℝ
    there is no modulus to take, which is exactly why the residual freedom is a sign and
    not a phase) and **`TransProbPreservingR.coord_sq_transfer`** — for a preserving `f`
    carrying a unit `φ` to the ray of a unit `φ'`, the image's squared coordinate against
    `φ'` equals the source's against `φ`. Axiom-checked = Lean core only. **That is the
    identity the sign-fixing step consumes: every coordinate of the image is now pinned
    up to sign.**
    **STEP 2b DONE (same day)**: **`TransProbPreservingR.imageOrthonormalBasis`** — in
    finite dimension, with the index type of cardinality `finrank`, the image family is
    an `OrthonormalBasis` (orthonormal from step 2, spanning from
    `LinearIndependent.span_eq_top_of_card_eq_finrank`; note it needs `[Nonempty ι]`).
    Axiom-checked = Lean core only. This is what lets step 4 expand an image vector in
    the image basis and conclude its coordinates vanish outside the expected slots.
    **STEP 4a DONE (same day)**: `TransProbPreservingR.abs_coord_transfer` and its
    self-contained form **`abs_inner_image`** — with everything normalized, the image
    ray's coordinate against the normalized image of a unit `φ` has the SAME ABSOLUTE
    VALUE as the source's coordinate against `φ`. Step 3 pinned coordinates squared; this
    takes the unique nonnegative square root (`sq_eq_sq₀`), which is the form the sign
    argument runs on. `abs_inner_image` carries **no side hypothesis about the image at
    all** — taking `φ'` to be the normalized image of `φ` discharges it, via the three
    ray-bookkeeping lemmas `mk_smul_eq` / `mk_normalize_rep` / `norm_normalize`.
    Applied to an orthonormal basis with `b' = imageOrthonormalBasis`, the content is
    exactly: **every coordinate of the image is ± the corresponding source coordinate.**
    So the residual freedom is now a per-coordinate sign PATTERN, and all that remains of
    the real rigidity is that the pattern is a single GLOBAL sign. Axiom-checked = Lean
    core only.
    **STEP 4b part 1 DONE (same day)**: `eq_sum_over_support` (a vector equals its
    expansion over any set carrying all its coordinates) and `eq_pair_expansion` (the
    two-slot case). This is the machine that turns step 4a's "the other coordinates
    vanish" into a finite expansion: the image of `b i + b j` has coordinate modulus
    `1/√2` at `i, j` and `0` elsewhere, hence equals `a • b' i + d • b' j`, so its RAY
    depends only on the relative sign — which is the object the sign-fixing argument
    manipulates. TRAP recorded: `rw [← b.sum_repr' v]` rewrites the `v` inside the
    coordinates too; chain with `.trans` instead of rewriting. `OrthonormalBasis.coe_mk`
    exists, so the bridge from `imageOrthonormalBasis` back to the explicit normalized
    family is available for the next unit. Axiom-checked = Lean core only.
    **STEP 4b part 2 DONE (same day)**: `imgBasis` (the image of an orthonormal basis as
    an orthonormal basis on the SAME index type), `imgBasis_apply` (the bridge back to the
    explicit normalized family — `OrthonormalBasis.coe_mk`, with `hon` supplied EXPLICITLY
    or the family metavariable cannot be solved), `abs_inner_imgBasis` (step 4a against
    the basis: every image coordinate is ± the source's), and **`image_two_slot`**: the
    normalized image of `b i + b j` equals `a • b' i + d • b' j` with
    `|a| = |d| = ‖b i + b j‖⁻¹`. **No `√2` is ever computed** — the modulus *is* the
    inverse norm, which is why this is short. So the two-slot image ray is pinned except
    for the RELATIVE SIGN of `a` and `d`, and comparing relative signs across pairs is all
    that is left. TRAPS: `set x := e with h` did not orient usably here (use
    `obtain ⟨u, hu⟩ : ∃ u, u = e := ⟨_, rfl⟩` and `rw [← hu]`); the two-slot `if` guards
    are `i = k` / `j = k`, so branch 1 needs `if_neg (Ne.symm hij)` and branch 2 `if_neg
    hij` — I had them swapped; and `omit ... in` must precede the DOCSTRING, so dropping
    `[DecidableEq ι]` from the section and using `classical` in the one proof that needs
    it is cleaner. Axiom-checked = Lean core only.
    **STEP 4c part 1 DONE (same day)**: `orthonormal_signAdjust`, `signAdjustBasis`,
    `signAdjustBasis_apply`, **`mk_signAdjustBasis`** — rescaling an orthonormal basis by
    any pattern of signs gives an orthonormal basis representing THE SAME RAYS. This is the
    structural reason the sign-fixing step is not a search: it does not choose signs out of
    nothing, it ABSORBS them into a re-choice of the image basis, and the projective
    classification cannot see the difference. What is left is therefore to exhibit one
    working pattern (from the pairs `(i₀, i)` via `image_two_slot`), not to justify that a
    pattern may be used. TRAPS: `OrthonormalBasis.coe_mk` needs its `hon` argument by NAME,
    so the orthonormality must be a top-level theorem, not a `have` inside the def's
    tactic block; and `rw` on the ray of a sign-adjusted vector fails with "motive is not
    type correct" because the nonzero proof depends on the rewritten term — go through
    `mk_eq_mk_iff` instead. Axiom-checked = Lean core only.
    **STEP 4c part 2 DONE (same day)**: **`sign_pair_of_abs`** — the engine of the entire
    sign-fixing argument, and it is PURE REAL ARITHMETIC: from `|x| = |p|`, `|y| = |q|` and
    `|x + y| = |p + q|` with `p·q ≠ 0`, conclude `(x,y) = (p,q)` or `(x,y) = (-p,-q)` — ONE
    sign for both. The mixed case is killed because `|p - q| = |p + q|` forces `pq = 0`.
    That is exactly why the global pattern is consistent rather than merely pointwise: a
    nonvanishing pair of source coordinates TRANSMITS its relative sign. Also
    `basis_add_ne_zero` (distinct orthonormal basis vectors have nonzero sum), which removes
    the side hypothesis from every two-slot construction downstream. Axiom-checked = Lean
    core only.
    **STEP 4c part 3 DONE (same day)**: **`abs_inner_two_slot`** — the third input to
    `sign_pair_of_abs`. The image's coordinate against the image of `b i + b j` reproduces
    the SUM of the source's two coordinates, with the same factor `‖b i + b j‖⁻¹` that
    `image_two_slot` produced. So all three hypotheses of the common-sign lemma are now
    machine-checked facts about `f`: `|x| = |p|` and `|y| = |q|` from `abs_inner_imgBasis`,
    and `|x + y| = |p + q|` from this. Axiom-checked = Lean core only.
    **STEP 4d part 1 DONE (same day)**: `basisIsometry` (`b.repr.trans c.repr.symm`),
    `basisIsometry_apply` and `projMapR_basisIsometry` — the candidate isometry matching two
    orthonormal bases slot for slot, and the fact that its induced projective map matches
    them as RAYS. Pure plumbing, which is the point: the rigidity's content was never
    *building* the isometry, it is showing `f` agrees with the induced map, and that is
    exactly where the sign pattern gets consumed. Axiom-checked = Lean core only.
    **STEP 4d part 2a DONE (same day)**: `normImg` (the normalized representative of the
    image ray, with `norm_normImg`, `normImg_ne_zero` and `mk_normImg` showing it loses
    nothing) — the assembly manipulates this object constantly, so naming it is what keeps
    the remaining statements readable. Plus `inner_basis_eq_ite` (hoisted out of
    `image_two_slot`'s local proof) and **`abs_inner_imgBasis_pair` /
    `inner_imgBasis_pair_ne_zero`**: each coordinate of the image of `b i + b j` has modulus
    `‖b i + b j‖⁻¹` and is therefore NONZERO — which is what gives the sign pattern
    something to be the sign OF, and is exactly `sign_pair_of_abs`'s `p·q ≠ 0` hypothesis at
    the pair level. Axiom-checked = Lean core only.
    **STEP 4d part 2b DONE (same day)**: **`signPattern`** — the sign pattern, DEFINED (no
    choice: the coordinates are inner products, and `inner_imgBasis_pair_ne_zero` plus the
    new `..._pair_right_ne_zero` make their product nonzero, so `c / |c|` is a genuine sign)
    — together with `abs_signPattern` (`|σ i| = 1`, which is all `signAdjustBasis` needs).
    Recorded asymmetry: the `(i,j)`-swapped instance of `abs_inner_imgBasis_pair` is about
    the vector `b j + b i`, a DIFFERENT TERM, so the right slot genuinely needs its own
    statement — hence `abs_inner_imgBasis_pair_right`. Axiom-checked = Lean core only.
    **STEP 4d part 2c DONE (same day)**: `normBasis` (the sign-normalized image basis),
    `normBasis_apply`, `signPattern_self`, `signPattern_of_ne`, `mul_sign_mul_pos`, and
    **`pair_coord_mul_pos`** — against `normBasis`, the two coordinates of the image of
    `b i₀ + b i` have the SAME SIGN. That is the point of the whole construction: it means
    `sign_pair_of_abs`, applied to a general ray and the pair `(i₀, i)`, becomes a statement
    about coordinates in ONE fixed basis, with no per-pair bookkeeping left. Axiom-checked =
    Lean core only.
    **STEP 4d part 2d DONE (same day)**: `eq_of_abs_eq_of_mul_pos` (equal moduli + positive
    product ⟹ EQUAL), `abs_inner_normBasis` (step 4a survives the sign adjustment, since
    `|σ| = 1`), and **`two_slot_normBasis`**: in the normalized basis the image of
    `b i₀ + b i` is `A • (b'' i₀ + b'' i)` with `|A| = ‖b i₀ + b i‖⁻¹` — the two-slot image
    has become SYMMETRIC. That symmetry is the payoff of the whole `signPattern`
    construction: it is what lets the transition probability between an arbitrary ray and
    `b i₀ + b i` be read directly as `|x + y|` in the ray's own coordinates, which is
    `sign_pair_of_abs`'s third hypothesis in usable form. Axiom-checked = Lean core only.
    **STEP 4d part 2e DONE (same day)**: `normImg_def` (the folding lemma — the earlier
    step-4a statements are in expanded form, so folding is what lets them meet the new ones),
    **`abs_add_coord_transfer`** (`sign_pair_of_abs`'s third hypothesis for an ARBITRARY ray,
    in the normalized basis: the moduli of the coordinate SUMS agree — obtained by cancelling
    the common factor `‖b i₀ + b i‖⁻¹`), and **`abs_inner_normImg`**: the transfer in FULL
    GENERALITY, for any two rays. That last one is the structural simplification of the
    remaining work — every specific transfer (two-slot, three-slot) is now a computation of
    its right-hand side, so the pair-consistency argument is mechanical rather than novel.
    Axiom-checked = Lean core only.
    **SCOPE OF WHAT IS LEFT, stated precisely (this replaces the earlier vaguer note).** With
    `p_k = ⟨ψ̂, b k⟩` and `x_k = ⟨ψ', b'' k⟩`: `abs_inner_normBasis` gives `|x_k| = |p_k|` and
    `abs_add_coord_transfer` gives `|x_{i₀} + x_i| = |p_{i₀} + p_i|`, so `sign_pair_of_abs`
    yields `x_k = ε·p_k` for ALL k with ONE ε — **whenever `p_{i₀} ≠ 0`**. That case is
    finished mathematically. The residual case `p_{i₀} = 0` cannot be anchored at `i₀`, and it
    needs PAIR CONSISTENCY: that the `i₀`-normalization also symmetrizes pairs `(i,j)` with
    neither index `i₀`. The route is a THREE-slot vector `b i₀ + b i + b j` (all three source
    coordinates nonzero, so both pairs `(i₀,i)` and `(i₀,j)` transmit and share the anchor's
    sign) plus an equality-in-the-triangle-inequality step. Estimated 3-4 units, all of the
    same kind as those already banked. **Per-anchor isometries are NOT a shortcut** — anchoring
    at a different index per ray gives a different isometry, which does not prove the single-`e`
    statement; that dead end is recorded so it is not retried.
    **★ STEP 4d part 2f DONE (same day) — THE MAIN CASE IS MACHINE-CHECKED.**
    **`eq_projMapR_of_anchor`**: for any ray with `⟨ψ̂, b i₀⟩ ≠ 0`,
    `f [ψ] = projMapR (basisIsometry b (hf.normBasis b i₀)) [ψ]`. The global sign is
    `ε = x_{i₀}/p_{i₀}` (defined outright, not chosen), `sign_pair_of_abs` propagates it to
    every other coordinate, and coordinates where `p_k = 0` are handled by `|x_k| = |p_k| = 0`.
    Also `eq_of_inner_basis_eq`, proved from `sum_repr'` because
    `InnerProductSpace.ext_inner_right_basis` lives in `Analysis.InnerProductSpace.Dual`,
    which this development does not import. **The assembly needs NO SUMS**: two vectors
    agreeing in every coordinate against an orthonormal basis are equal, and `e` being an
    isometry turns `⟨e ψ̂, b'' k⟩` into `⟨ψ̂, b k⟩` in one step. Axiom-checked = Lean core only.
    TRAPS (both cost a round): `real_inner_comm (x y) : ⟪y,x⟫ = ⟪x,y⟫` — the arguments read
    BACKWARDS from the goal; and `rw [hvec]` where `hvec`'s RHS mentions the rewritten term
    inside its own scalar rewrites it there too (the self-reference trap, third occurrence
    this campaign) — chain with `.trans`/`exact ….symm` instead.
    **★★ STEP 4 COMPLETE (same day) — REAL WIGNER RIGIDITY IS MACHINE-CHECKED,
    UNCONDITIONAL.** `eq_projMapR_of_anchor_zero` (the residual case), `eq_projMapR` (every
    ray, by case split), and **`exists_isometry_of_transProbPreservingR`**: for
    finite-dimensional nontrivial real `E`, every transition-probability preserving map on
    `ℙ ℝ E` is induced by a linear isometry. Axioms = Lean core only. Unlike the COMPLEX
    Wigner theorem, which this development VENDORS, the real one is now PROVED here.
    **The residual case did NOT need pair consistency, and this kills the estimate that stood
    for most of the campaign.** Instead of a three-slot vector plus an
    equality-in-the-triangle-inequality argument (~3-4 units), shift the ANCHOR: apply the main
    case to `ψ̂ + b i₀`, whose anchor coordinate is `1`. Because the image of `ψ` has vanishing
    `i₀` coordinate, the overlap with the shifted ray is FULL, so
    `|⟨ψ', e ψ̂⟩| = ‖ψ'‖·‖e ψ̂‖`, and `norm_inner_eq_norm_iff` (the equality case of
    Cauchy-Schwarz) forces proportionality outright. **Fifth instance of the campaign's
    recurring lesson**: before building the machinery, check whether the obstruction dissolves
    under a change of reference point. TRAPS: `Projectivization.mk_eq_mk_iff` returns a `ℝˣ`
    scalar, so `rw [Units.smul_def] at ha` FIRST or every later rewrite misses; and
    `norm_inner_eq_norm_iff` is stated with `‖·‖` on the scalar, so `Real.norm_eq_abs` is
    needed to meet `|·|`.

    **ℝ BRIDGE UNIT 1 DONE (same day)** — `Necessity/RealRayMap.lean` (NEW, census 133 →
    **134**): `rankOneR` (the projection `ψψᵀ`), `vecMulVec_mul_vecMulVec`,
    `rankOneR_isProjection`, **`trace_rankOneR_mul`** (the trace pairing against `ψψᵀ` IS the
    quadratic form `ψᵀyψ` — this is what makes rank-ones a separating family, hence the span
    argument) and **`trace_rankOneR_mul_rankOneR`** (`= (ψ ⬝ᵥ φ)²`, exactly the real
    transition probability, with no modulus to take). Gates green at 3091 jobs, custom axioms
    exactly [].
    **ℝ BRIDGE UNIT 2 DONE (same day)** — `Necessity/RealRankOneSpan.lean` (NEW, census 134
    → **135**): `eq_zero_of_quadratic_zeroR` (a symmetric matrix with identically vanishing
    quadratic form is zero — the form being both `≥ 0` and `≤ 0` pins it), `inner_rankOneR`,
    `span_rankOneR_eq_top` (the rank-one projections of unit vectors SPAN, via trivial
    orthogonal complement) and **`linearMap_eq_of_eq_on_rankOneR`** — agreement on rank-ones
    is agreement everywhere. **This is the step that converts "the ray map is induced by an
    orthogonal matrix" (real Wigner) into "the comparison map IS conjugation by it",** which
    is what makes it a Jordan automorphism. Confirmation of the native-route bet: the ℂ
    version's normalization step needs a `Complex.normSq` computation and a "the form is real"
    lemma with conjugate-swapping; over ℝ rescaling just multiplies the form by `c²` and both
    disappear. Gates green at 3092 jobs, custom axioms exactly []. Name trap:
    `dotProduct_self_eq_zero` is ROOT namespace, not `Matrix.`.
    **ℝ BRIDGE UNIT 3 DONE (same day)** — `Necessity/RealJordanWitness.lean` (NEW, census 135
    → **136**): `orthConj` (conjugation `x ↦ U x Uᵀ` as an ℝ-linear map),
    **`orthConj_preservesJordan`** (`UᵀU = 1` cancels in the middle of each product) and
    **`orthConj_rankOneR`** (`U(ψψᵀ)Uᵀ = (Uψ)(Uψ)ᵀ` — the compatibility that lets unit 2's span
    argument be applied to a conjugation). Gates green at 3093 jobs, custom axioms exactly [].
    **This unit is where the native route's structural saving shows up most.** The ℂ lane's
    `JordanWitness` needs a SECOND branch here — `transposeMap` plus the antiunitary case —
    because complex Wigner permits a conjugate-linear alternative. Real Wigner yields an
    ORTHOGONAL map, so that branch has no ℝ counterpart and this one file is the whole step.
    Recorded honestly: the ℂ `unitaryConj` and its Jordan lemma have no ℂ-specific content and
    could have been generalized in place, but they sit in a file that is ℂ-bound elsewhere
    (`rankOne`) and is finished and banked — thirty re-derived lines beat reopening a completed
    row.
    **ℝ BRIDGE UNIT 4a DONE (same day)** — `Necessity/RealStrength.lean` (NEW, census 136 →
    **137**): `vecMulVec_mulVec`, `quadForm_smul_rankOneR` (the quadratic form of `t·ψψᵀ` at a
    unit `ψ` is exactly `t`), `strengthR` (Busch-Gudder: `sup {t | t·p ≤ a}`),
    `strengthR_set_nonempty`, `strengthR_set_bddAbove` (`t·ψψᵀ ≤ a ≤ 𝟙` forces `t ≤ 1`, by
    testing the form at `ψ`) and **`strengthR_map` — order isomorphisms preserve the
    strength.** Gates green at 3094 jobs, custom axioms exactly [].
    **ℝ BRIDGE UNIT 4b DONE (same day)** — appended to `RealStrength.lean`: `probeR`
    (`½(𝟙 + φφᵀ)`) and **`probe_key_ineqR`**, the tight inequality that IS the `≥` half of
    `Str(ψψᵀ, Pr(φ)) = (2 − τ)⁻¹`, isolated as pure arithmetic in the five scalars the geometric
    decomposition produces (`v = αφ + w`, `ψ = sφ + χ`, `d = χ ⬝ᵥ w`, `W = w ⬝ᵥ w`). Same tactic
    as `sign_pair_of_abs`: get the content out of the API. **The certificate, recorded because
    `nlinarith` will NOT find it unaided:** after clearing `4(1−τ)` the gap is exactly
    `2(2(1−τ)α − sd)²`, using `s² = τ` to turn `2τd²` into `2s²d²`; the bound is two-term
    Cauchy-Schwarz with weights `1` and `½` and it is TIGHT, which is why the strength equals
    `(2 − τ)⁻¹` on the nose. Also noted: `0 ≤ τ` is NOT needed as a hypothesis — `s² = τ`
    forces it, and the linter caught the redundancy. Gates green at 3094 jobs, axioms Lean core.
    **ℝ BRIDGE UNIT 4c DONE (same day)** — appended to `RealStrength.lean`:
    `quadForm_smul_rankOneR_apply`, **`rankOneR_smul_le_iff`** (`t·ψψᵀ ≤ a` is exactly a
    statement about quadratic forms), `quadForm_probeR`, `dotProduct_sq_le` (Cauchy-Schwarz for
    the real dot product, proved DIVISION-FREE from
    `(‖y‖²x − ⟨x,y⟩y)·(same) = ‖y‖²(‖y‖²‖x‖² − ⟨x,y⟩²)` — cheaper than transporting `n → ℝ` to
    `EuclideanSpace` to quote the abstract version), and **`probe_ge_inv_smul_rankOneR`**:
    `(2 − τ)⁻¹·ψψᵀ ≤ Pr(φ)`. That is the ADMISSIBILITY half of
    `Str(ψψᵀ, Pr(φ)) = (2 − τ)⁻¹`. Gates green at 3094 jobs, custom axioms exactly [].
    **TRAP, fourth occurrence, now with a stated rule.** The bilinear expansions must rewrite
    only the DEFINED vectors (`w = v − (φ⬝v)φ`, `χ = ψ − (ψ⬝φ)φ`) and never `v` or `ψ`, because
    those occur inside the coefficients and `rw` hits them there too. Concretely: prove
    `w ⬝ᵥ w = v ⬝ᵥ v − (φ⬝v)²` (expanding `w`), NOT `v ⬝ᵥ v = (φ⬝v)² + w ⬝ᵥ w` (which would
    expand `v`). Same fix as `hvec` in the main case and `eq_sum_over_support`. Rule of thumb
    now recorded: **orient every expansion so the rewritten symbol does not appear on the
    right-hand side.**
    **★ ℝ BRIDGE UNIT 4 COMPLETE (same day)** — appended to `RealStrength.lean`:
    `quadForm_rankOneR`, `probeR_nonneg`, `probeR_le_one`, **`strengthR_probe_le`**,
    **`strengthR_probe_eq`** (`Str(ψψᵀ, Pr(φ)) = (2 − τ)⁻¹` EXACTLY),
    **`tprobR_eq_of_strength`** (`τ = 2 − Str⁻¹`, i.e. the transition probability IS order data)
    and **`tprobR_preserved`** — a unital ℝ-linear order automorphism carrying rank-ones to
    rank-ones preserves the transition probability. **That last one is exactly the
    `TransProbPreservingR` input that `exists_isometry_of_transProbPreservingR` consumes**, so
    the ℝ chain now runs from an order automorphism all the way to real Wigner. Everything after
    the test vector compiled first try. Gates green at 3094 jobs, custom axioms exactly [].
    **The `≤` half's trick, recorded so it is never re-derived:** maximizing
    `(ψ⬝v)²/(½(v⬝v + (φ⬝v)²))` over the plane spanned by `φ` and `ψ − (ψ⬝φ)φ` puts the optimum
    at **`v* = 2ψ − (ψ⬝φ)φ`**, where `ψ⬝v* = 2 − τ`, `φ⬝v* = ψ⬝φ`, `v*⬝v* = 4 − 3τ`, so the test
    reads `t(2 − τ)² ≤ 2 − τ`. With that vector written down the proof is arithmetic; without it
    there is nothing to do.
    **ℝ BRIDGE UNIT 5a DONE (same day)** — `Necessity/RealProjectionOrder.lean` (NEW, census
    137 → **138**): `IsAtomProjectionR`, **`quadForm_isProjection`** (for a projection the
    quadratic form IS a squared norm, `v·qv = |qv|²`, from `q² = q` and `qᵀ = q`),
    **`mulVec_eq_zero_of_le_rankOneR`** (a subprojection of `ψψᵀ` ANNIHILATES everything
    orthogonal to `ψ`) and `rankOneR_ne_zero`. Gates green at 3095 jobs, axioms Lean core.
    **★ THIS REPLACES THE ℂ PROOF RATHER THAN PORTING IT, and that is the point.** The ℂ
    argument (`ProjectionOrder` 136-268, ~130 lines) manipulates `vecMulVec` factorizations
    directly. The ℝ route is conceptual: because the form of a projection is a squared norm, the
    order bound `q ≤ ψψᵀ` UPGRADES to vanishing — `v·qv ≤ (ψ·v)² = 0` forces `qv = 0` — which is
    far stronger than an inequality and is what collapses the argument. The remaining two-case
    step is then short: write `qψ = aψ + v₀`; idempotence gives `a = 1` or `qψ = 0`; the first
    forces `v₀ = 0` by comparing `|qψ|² = ψ·qψ = 1` against `|ψ|² + |v₀|²`, giving `q = ψψᵀ`, and
    the second gives `q = 0`. **So the 60-line "genuinely spectral step" in the measurement
    above is now the cheapest part of unit 5, not the boulder.** That correction matters: the
    earlier estimate treated it as the one piece needing real thought.
    TRAP: `q.H` has type `(↑q).IsHermitian`, which `rw` cannot see through — ascribe it
    (`have h : q.matᴴ = q.mat := q.H`) before rewriting. `Matrix.mulVec_transpose`, not
    `vecMul_eq_mulVec_transpose`.
    **ℝ BRIDGE UNIT 5b DONE (same day)** — `matrix_ext_of_mulVec` and **`rankOneR_isAtom`**:
    rank-one projections ARE atoms of the real projection order. Gates green at 3095 jobs, axioms
    Lean core. The proof is the conceptual route, and it came out ~25 lines against the ℂ
    version's ~50: `q ≤ ψψᵀ` kills `ψ`'s orthogonal complement, so `q` is determined by `u = qψ`
    via `qv = (ψ·v)u`; idempotence gives `u = (ψ·u)u`; then either `u = 0`, so `q` annihilates
    everything and `q = 0`, or `ψ·u = u·u = 1`. **The last step is the slick one**: instead of
    decomposing `u` and killing a component, compare `|ψ − u|² = 1 − 2(ψ·u) + u·u = 0` directly,
    which gives `u = ψ` in one line.
    **ℝ BRIDGE UNIT 5c DONE (same day)** — **`IsAtomProjectionR.exists_rankOne`**: every atom
    IS a rank-one. So over ℝ, rank-one projections and atoms of the projection order COINCIDE,
    which is the whole content of rank-one transport's algebraic side. ~35 lines against the ℂ
    lane's 60: take any nonzero range vector, normalize to `ψ`; then `pψ = ψ`, and symmetry of
    `p` plus Cauchy-Schwarz give `(ψ·w)² = (ψ·pw)² ≤ (ψ·ψ)(pw·pw) = w·pw`, i.e. `ψψᵀ ≤ p`;
    atomicity leaves only `ψψᵀ = p`. TRAP worth recording: the normalization constant must be
    given an OPAQUE local name (`obtain ⟨c, hc⟩ : ∃ c, c = …`), because `hmove`'s pattern
    `x ⬝ᵥ (p *ᵥ y)` otherwise matches the `(p*ᵥv) ⬝ᵥ (p*ᵥv)` sitting inside `√(…)` and rewrites
    there too — the same class of failure as the self-reference trap, and the same fix
    (make the thing you do not want rewritten opaque).
    **★★ ℝ BRIDGE UNIT 5d DONE (same day) — RANK-ONE TRANSPORT AT ℝ IS COMPLETE.**
    `isProjection_mapR`, `isAtomProjection_mapR`, **`exists_rankOneR_map`**: a unital ℝ-linear
    order automorphism carries each rank-one projection to a rank-one projection with an explicit
    unit vector. Both transport lemmas are DIRECT ports of the ℂ arguments with `ℂ → 𝕜`; nothing
    about the scalar field enters, exactly as predicted.
    **★ AND A GENERALIZATION THAT PAID OFF, recorded because it contradicts this campaign's own
    default.** The ports were blocked on `HermitianMat.mem_extremePoints_iff_isProjection`, which
    was stated at **ℂ only** (its docstring even said "(ℂ)") — the single ℂ holdout in an
    otherwise 𝕜-generic file that already had `variable {𝕜} [RCLike 𝕜]` in scope. Inspection
    showed its 99-line proof uses `ℂ` ONLY as a type annotation: no `Complex.*`, no `normSq`,
    everything through `a.cfc` and the order. So it was generalized IN PLACE — 16 lines touched,
    the proof went through at `𝕜` unchanged, and **the full build stayed green at 3095 jobs with
    every downstream ℂ consumer untouched.** Contrast with `StrengthProbe` (60 `Complex.normSq`
    uses, 11 consumers), where in-place generalization was correctly rejected. **The rule is not
    "never generalize in place" but "measure the ℂ-specific surface first":** one type annotation
    is free, sixty normSq uses are not.
    **ℝ BRIDGE UNIT 5e DONE (same day)** — `Necessity/RealWignerBridge.lean` (NEW, census 138 →
    **139**): `inner_eq_dotProductR` (on `EuclideanSpace ℝ (Fin N)` the inner product IS the dot
    product — no conjugation, which is the whole simplification over ℂ),
    `norm_sq_eq_dotProduct_self`, **`transProbVecR_eq_sq_dotProduct`** (on unit vectors the
    vendored transition probability is `(ψ ⬝ᵥ φ)²`, exactly the quantity `tprobR_preserved`
    transports), plus the normalization helpers `unitVecR` / `unitVecR_unit` /
    `rankOneR_unitVecR`. Gates green at 3096 jobs, custom axioms exactly []. **This closes the
    vocabulary gap**: real Wigner speaks `EuclideanSpace` + `inner`, the Kadison side speaks
    `Fin N → ℝ` + `dotProduct`, and the two are now identified, so `tprobR_preserved` and
    `exists_isometry_of_transProbPreservingR` can be composed.
    **ℝ BRIDGE UNIT 5f DONE (same day)** — appended to `RealWignerBridge.lean`:
    `ofLp_rep_ne_zero`, **`repUnitR`** (a unit representative of a ray, AS A FUNCTION `Fin N → ℝ`
    — which is the form `exists_rankOneR_map` consumes), `repUnitR_unit`, `repUnitR_ne_zero` and
    **`mk_repUnitR`** (the unit representative represents the ray it came from). Gates green at
    3096 jobs, axioms Lean core. TRAP, and the same class as the self-reference one:
    `rw [hscale] at hne ⊢` fails with "motive is not type correct" because the ray's nonzero proof
    DEPENDS on the term being rewritten — but no rewrite is needed, since
    `toLp (repUnitR p)` IS `c • p.rep` definitionally, so `exact` with `(c := …)` pinned goes
    straight through. **General form of the rule: when a rewrite target sits under a dependent
    proof argument, look for the defeq instead of the rewrite.**
    **REMAINING FOR THE ℝ ROW — the assembly only.** All five inputs are banked
    (`exists_rankOneR_map`, `tprobR_preserved`, `exists_isometry_of_transProbPreservingR`,
    `linearMap_eq_of_eq_on_rankOneR`, `orthConj_preservesJordan` + `orthConj_rankOneR`). What the
    assembly still needs is plumbing, not mathematics: (1) the `EuclideanSpace ℝ (Fin N)` ↔
    `dotProduct` bridge (ℝ analogue of `WignerBridge`, ~100 lines at ℂ, shorter at ℝ since
    `star = id`); (2) the ray map built from `exists_rankOneR_map` via choice, shown
    `TransProbPreservingR` by `tprobR_preserved` (ℝ analogue of `RayMap`); (3) extracting the
    orthogonal MATRIX from the `LinearIsometryEquiv` real Wigner returns, so that
    `Φ (rankOneR ψ) = rankOneR (U *ᵥ ψ) = orthConj U (rankOneR ψ)`; then
    `linearMap_eq_of_eq_on_rankOneR` gives `Φ = orthConj U` and `orthConj_preservesJordan`
    finishes. (ii-old)
    `isProjection_map` / `isAtomProjection_map` at ℝ (**purely order-theoretic — port by changing
    ℂ to ℝ**); (iii) unit 5's assembly, whose five inputs are ALL banked (`rankOneR_isAtom`,
    `tprobR_preserved`, `exists_isometry_of_transProbPreservingR`,
    `linearMap_eq_of_eq_on_rankOneR`, `orthConj_preservesJordan` + `orthConj_rankOneR`).
    TRAPS: `matrix_ext_of_mulVec` needs `DecidableEq` (for `Pi.single`) — do not omit it; and
    `field_simp` on `(ψ·u)(u·u) = u·u` produces a disjunction that is awkward to case on — use
    `mul_right_cancel₀` instead.
    **★ ℝ BRIDGE — WHAT IS LEFT, MEASURED (do not re-measure; execute).** Unit 5 is the
    discharge, and its only prerequisite is rank-one TRANSPORT: that an order automorphism
    carries rank-one projections to rank-one projections. At ℂ that is four declarations, and
    they were counted, not estimated:
      * `IsAtomProjection` + `rankOne_isAtom` (`ProjectionOrder`, ~30 lines) — rank-ones are
        atoms of the projection order;
      * `IsAtomProjection.exists_rankOne` (`ProjectionOrder` 208-268, **60 lines**) — conversely
        every atom is a rank-one. This is the only genuinely spectral step: pick a nonzero range
        vector, and atomicity forces the range to be one-dimensional;
      * `isProjection_map` (`JordanWitness` 142-182, ~40 lines) and `isAtomProjection_map`
        (183-235, ~55 lines) — order automorphisms preserve projections and atoms. **Both are
        purely order-theoretic**, so they port with ℂ → ℝ and nothing else.
    Total ≈ 185 lines, of which only the 60-line spectral step needs thought. Then unit 5 itself
    is short: build `rayMapR` from rank-one transport, feed `tprobR_preserved` to get
    `TransProbPreservingR`, apply `exists_isometry_of_transProbPreservingR` for an orthogonal
    `U`, use `linearMap_eq_of_eq_on_rankOneR` with `orthConj_rankOneR` to conclude
    `Φ = orthConj U`, and finish with `orthConj_preservesJordan`. Every one of those five inputs
    is already banked.
    **Why this is the load-bearing unit for what remains.** Real Wigner needs a
    transition-probability preserving ray map, so the transition probability has to be ORDER
    DATA. The strength is the device: it is defined from the order and the real scalar action
    alone, so it transports along any order isomorphism, and the ℂ lane recovers
    `τ = 2 − Str⁻¹` from it (`tprob_eq_of_strength`). With `strengthR_map` banked, the
    remaining ℝ work in unit 4 is the COMPUTATIONAL half: `probeR φ = ½(𝟙 + φφᵀ)` and
    `strengthR (rankOneR ψ) (probeR φ) = (2 − (ψ ⬝ᵥ φ)²)⁻¹`, which in the ℂ lane is three
    lemmas (`strength_probe_le`, `probe_le_one`, `probe_ge_inv_smul_rankOne`). Then unit 4b is
    `exists_rankOneR_map` (an order automorphism carries atoms to atoms) and unit 5 assembles.
    NAME TRAPS: `Matrix.smul_mulVec` (not `smul_mulVec_assoc`); and `omit` placement is
    load-bearing here — `DecidableEq` IS referenced by the bddAbove statement (through the
    order on `HermitianMat`) but not by the nonempty one.
    **★ ROUTE DECISION FOR THE ℝ BRIDGE — NATIVE, NOT A PORT, and here is the measurement.**
    The ℂ chain is phrased via `rankOne`/`tprob`/`nsq`, defined at ℂ in `ProjectionOrder` and
    `StrengthProbe`. Those primitives' scalars ARE inferable from their arguments, so in-place
    generalization is *possible* — but `StrengthProbe` alone has **60 `Complex.normSq` uses**
    and there are **eleven downstream consumers, several finished and banked** (`RankTwo/*`,
    `TwistUniqueness`). Generalizing would destabilize completed rows. So the ℝ bridge is
    written natively. Two reasons this is genuinely CHEAPER and not merely safer: over ℝ
    `star = id`, so the conjugation bookkeeping vanishes; and **there is no antiunitary
    branch** — real Wigner yields an orthogonal map and conjugation by it is already a Jordan
    automorphism, so the ℂ lane's `transposeMap` half of `JordanWitness` has NO ℝ counterpart.
    Expect well under ℂ's 1150 lines.
    **WHAT THE RIGIDITY DOES AND DOES NOT DISCHARGE — read before claiming the ℝ row.** The ℝ row's
    carried hypothesis is `hjordAll : ∀ U unitary, ThetaPreservesJordanG (conjProductG P …)` —
    the JORDAN property of the comparison map (real Kadison), not the Wigner statement. Real
    Wigner is the classical INPUT to it, not the same theorem. The ℂ lane bridges the gap
    across five files — `RayMap` (227) → `WignerBridge` (100) → `RankOneSpan` (184) →
    `JordanWitness` (249) → `KadisonDischarge` (390), 1150 lines total, and a grep shows they
    are written at ℂ with ZERO `RCLike`/`𝕜` occurrences, so they are NOT scalar-generic and
    would need the same twin treatment as the M4 files. **So: the ℝ row is still conditional,
    and the honest statement is that its one missing CLASSICAL THEOREM is now proved, with the
    remaining work being an ℝ port of the known five-file bridge.** That is a much better
    position than "gated on a theorem available in no prover", but it is not unconditional.
    **(superseded) the residual case `p_{i₀} = 0`** — see the scope
    note above: three-slot pair consistency, ~3-4 units of the same kind. The main case being
    done means the theorem's mathematical content is banked; what is left is the coverage of
    rays orthogonal to the anchor.
    **(superseded note) 4d part 2f — the pattern from the pairs `(i₀, i)`
    (the coordinates are inner products, so no choice is needed), prove pair-consistency for
    arbitrary `(i,j)` via a THREE-slot vector, and assemble the isometry. The inputs are now
    all in place: `image_two_slot` supplies the moduli, `sign_pair_of_abs` the common sign,
    `signAdjustBasis` the absorption, `eq_sum_over_support` the expansion.** Use a
    reference vector (e.g. `Σ eᵢ`, or successively the vectors `eᵢ + eⱼ`) to pin the
    relative signs, and check consistency via the transition probabilities with those
    mixed vectors; then assemble the isometry and conclude
    `f = projMapR e`. in the complex development the analogous phase-fixing step
    is what accounts for most of the 3179 lines, and over ℝ it is a sign rather than a
    circle.
    Net: the ℝ row is ONE self-contained classical theorem from unconditional — this
    supersedes both the earlier "new boulder of M3's kind" estimate and any reading that
    the vendored artifact could be reused.
  * This corrects the earlier "the real row is perhaps a session away" estimate a
    second time: the *machinery* is nearly ported, but an unconditional ℝ row is
    gated on real Kadison. Decide explicitly which of the two deliverables is wanted
    before writing the ending.

  **ROUTE DECIDED AND STARTED 2026-08-06 — TWINS, NOT A SED, AND HERE IS WHY.** The
  in-place alternative was measured exactly: `diagFamily`/`frameProj` occur at **234
  standalone sites across 19 files** (regex `\bdiagFamily\b` verified not to touch
  `sp_diagFamily`/`diagFamily_mat`), and those 19 files include the FINISHED complex
  capstones (`TwistPower`, `TwistUniqueness`, `TwistGeneral`, `TwistIdentification`,
  `BlockChi`, `BlockInvariance`, …). Judgment call, recorded deliberately: **the ℂ row
  is the submission artifact, so it does not get refactored to serve an in-progress
  row.** "The build still passes after touching 19 files of a finished proof" is a
  weaker guarantee than "the finished proof was never touched". The duplication is
  ~4 files and can be collapsed after the ℝ row closes.
  * **`Necessity/ChiGen.lean` DONE** (census 113, gates green, tree at 3070 jobs,
    custom axioms exactly `[]`): field-general twin of `Chi.lean` —
    `theta_congrG`, `sp_diagFamilyG` (the product on the diagonal family is the
    family), `thetaD_zeroG`, `thetaD_mulG` (the χ̃ cocycle) — **compiled first try**,
    consuming `DiagonalFamilyGen`. Recipe for the twins: copy, add
    `variable {𝕜} [RCLike 𝕜]`, `HermitianMat n ℂ ⇝ 𝕜`, `\bdiagFamily\b ⇝
    diagFamilyG 𝕜`, `diagFamily_ ⇝ diagFamilyG_`, suffix every declaration name with
    `G`, and repoint the import at `DiagonalFamilyGen`.
  * REMAINING twins, in dependency order: **`ComparisonInstanceGen` (386 lines, the
    Θ/`thetaNorm` layer — the gate for the other three)**, then `ChiExtensionGen`
    (209), `ChiContinuityGen` (247), `CoalescenceInstanceGen` (309). Then the ℝ
    ending, conditional on the real Jordan property as a located hypothesis.
  ★**`ComparisonInstanceGen`'s ONE genuine obstacle, scoped 2026-08-06 (the port's
    second, after `sqrt_mul_of_commute`) — and it has a UNIFORM fix.**  Of that file's
    25 declarations only `commute_of_opCommute` (Jordan-operator commutation ⟺ matrix
    commutation) is field-dependent, and the dependence is in the *generator set*, not
    the mathematics: the existing proof forms `C := [a,b]`, shows `[C, y] = 0` for
    every Hermitian `y` via the quarter identity, and then kills `C` using the
    **anti-Hermitian generators `I·E_ij − I·E_ji`** (lines 139–160: `Complex.I`,
    `Complex.conj_I`, `Complex.I_mul_I`). Those do not exist over ℝ.
    **Uniform replacement, valid over any `RCLike 𝕜`**: use only generators that are
    Hermitian over *every* field — the real diagonals and the symmetric off-diagonals
    `E_ij + E_ji`. Commuting with diagonals carrying distinct entries forces `C`
    diagonal; commuting with `E_ij + E_ji` then equates all diagonal entries, so
    `C = λ·1`; and `C = [a,b]` with `a, b` Hermitian is anti-Hermitian, while `λ·1` is
    Hermitian, so `C = 0`. That argument never mentions `I` and replaces the
    ℂ-specific step in ~40 lines.
    **DONE 2026-08-06** (`Hermitian/CommutantHermitian.lean`, NEW, census 114, gates
    green, axioms core only): `indexDiag` (a real diagonal with distinct entries, via
    `Fintype.equivFin`), `symGen` (the `E_ij + E_ji` generator, Hermitian over every
    field), `eq_diagonal_of_commute_hermitian`, `diag_eq_of_commute_hermitian`, and the
    capstone **`eq_zero_of_commute_hermitian_of_trace_zero`** — a traceless matrix
    commuting with every Hermitian matrix is zero, over any `RCLike 𝕜`.
    ★**A CORRECTION to the sketch above, found while writing it**: anti-Hermitian-ness
    does NOT close the argument (`i • 1` is anti-Hermitian and nonzero over ℂ), so the
    uniform statement must take **tracelessness** instead — which is exactly what the
    caller has, since `C = [a,b]` is a commutator. The `C = λ•1` step is the shared
    part; the kill is `card • λ = 0` in characteristic zero. Traps: `single_conjTranspose`
    is a ℂ-only repo lemma — use Mathlib's `Matrix.conjTranspose_single`; entry
    computations want `Matrix.mul_single_apply_same`/`single_mul_apply_of_ne` with
    **explicitly pinned index arguments** (`(c := (1 : 𝕜)) j i i j (Ne.symm hij) C`),
    not hand-rolled `Finset.sum_eq_single` bashes; and pin the matrix type at the entry
    (`(… : Matrix n n 𝕜) i j`) or elaboration reports "function expected".
    With this the remaining `ComparisonInstanceGen` work is pure recipe.
  * **`Necessity/ComparisonInstanceGen.lean` DONE 2026-08-06 — THE GATE TWIN IS IN**
    (census 115, gates green, tree at 3072 jobs, custom axioms exactly `[]`): all 25
    declarations of the Θ/`thetaNorm` layer over an arbitrary `RCLike 𝕜`, including
    `jordanBilinG`, the quarter-identity bridge `commute_of_opCommuteG` /
    `opCommute_iff_commuteG`, `theta_fix_generalG`, the totalized `thetaNormG` with its
    laws, `ThetaPreservesJordanG` (the ℝ row's located hypothesis), `thetaNorm_jordanG`,
    `thetaNorm_cocycleG`, and **`comparisonSetupG : ComparisonSetup (HermitianMat (Fin N) 𝕜)`**.
    The field-dependent step is gone: `commute_of_opCommuteG` now reads
    quarter-identity → `Matrix.trace_mul_comm` for tracelessness →
    `HermitianMat.eq_zero_of_commute_hermitian_of_trace_zero`, and is SHORTER than the ℂ
    original (77 lines of `Complex.I` generator bookkeeping deleted).
    TRAP worth repeating: a `def` returning a *bilinear map* needs the scalar EXPLICIT
    (`jordanBilinG 𝕜`), for the same reason `diagFamilyG`/`frameProjG` do — with an
    implicit scalar the coercion-to-function cannot fire and every use reports
    "Function expected … HermitianMat ?m.5 ?m.8 →ₗ …".
  * **ALL FOUR TWINS DONE 2026-08-06 — THE DIFFERENTIAL FACE EXISTS OVER ANY
    `RCLike` FIELD** (census 118, gates green, tree at 3075 jobs, custom axioms exactly
    `[]`; `coalescenceSetupG` and `dChiG` axiom-checked individually = core only):
    `ChiExtensionGen` (`thetaUnitG`, the ℝⁿ-extension `chiTildeG` with `chiTilde_addG`
    — compiled FIRST TRY), `ChiContinuityGen` (the continuity ladder,
    `continuous_chiTilde_lineG`, the one-parameter classification `chiTilde_eq_expG`
    and **`dChiG`**), and `CoalescenceInstanceGen` (corner geometry + **
    `coalescenceSetupG : CoalescenceSetup (HermitianMat (Fin N) 𝕜)`**).
    Fix list for these three, all instances of rules already banked:
    `Complex.continuous_ofReal ⇝ RCLike.continuous_ofReal`;
    `HermitianMat.diagonal ℂ ⇝ 𝕜`; `cornerQG` needs the scalar EXPLICIT (its scalar
    appears only in the result type — third instance of that rule, after
    `diagFamilyG`/`frameProjG`/`jordanBilinG`); `unfold cornerQG` takes the BARE name;
    `(2 : ℂ)`/`(lam : ℂ)`/`diagonalAddMonoidHom n ℂ ⇝ 𝕜`; and the half-scalar identity
    wants `(2:𝕜)⁻¹ = ((1/2 : ℝ) : 𝕜)` proved FIRST (`RCLike.ofReal_div`,
    `ofReal_ofNat`) and rewritten BEFORE going entrywise — going entrywise first
    leaves an `algebraMap ℝ 𝕜 2` disjunct that `norm_num` cannot see.
  * ★★**THE ℝ ENDING, DESIGNED IN FULL 2026-08-06 — four steps, every ingredient
    named, no mathematical unknowns left.** The route deliberately avoids needing
    `dχ`/`real_kill` at all, because the continuity that kills the sign is already
    built:
    1. **Blocks are scalar-acted.** `χ̃(r)` fixes the frame (`chiTilde_fixes_frameProj`'s
       twin) and, being a Jordan automorphism (the located `ThetaPreservesJordanG`),
       preserves each Peirce block. Over ℝ the block `V_ij` is **one-dimensional**
       (`blockHerm i j t`, `t : ℝ` — no phase), so `χ̃(r)(blockHerm i j 1) =
       c_{ij}(r) • blockHerm i j 1` for a real scalar.
    2. **The scalar is ±1.** The square law `blockHerm_symmMul_self` gives
       `x ∘ x = |t|²(p_i + p_j)`; applying it on both sides of Jordan-multiplicativity
       and using frame-fixing forces `c_{ij}(r)² = 1`.
    3. **The sign is +1, by continuity — and this is why no differentiation is needed.**
       `c_{ij}` is multiplicative in `r` (the `chiTilde_addG` character law) with
       `c_{ij}(0) = 1` (`chiTilde_zeroG`), and `r ↦ χ̃(r)` is continuous along lines
       (`continuous_chiTilde_lineG`, already twinned). A continuous character of ℝⁿ into
       the **discrete** group `{±1}` with value 1 at 0 is identically 1.
    4. **Hence `χ̃(r) = id`, so `Θ = id` and the product is Lüders.** Step 3 plus
       frame-fixing means `χ̃(r)` agrees with the identity on the frame and on every
       block, and `linearMap_eq_of_frame_block` (twin needed:
       `FrameBlockSpanGen`) upgrades that to equality. Then
       `sp_eq_quadRep_theta`-style unfolding gives `a • b = Q_{√a} b` on the diagonal
       family, and `sp_eq_twistSeq_transport`'s ℝ analogue (or `twistFactor … 0 = √a`)
       carries it to every invertible effect; `sp_eq_on_effects_of_eq_on_posDef`
       extends to all effects.
    **TWINS FOR IT: TWO OF THREE DONE 2026-08-06** (census 120, gates green, tree at
    3077 jobs, custom axioms exactly `[]`; `blockHerm_symmMul_selfG` and
    `linearMap_eq_of_frame_blockG` axiom-checked = core only):
    * `BlockModelGen` — `blockHermG`, the **square law** `blockHerm_symmMul_selfG`
      (`x ∘ x = ‖z‖²(p_i+p_j)`), and the Peirce support characterization
      `eq_blockHerm_of_peirceG`. Fixes: `Complex.normSq ⇝ RCLike.normSq`,
      `(starRingEnd ℂ) ⇝ 𝕜`, and the square law now closes with
      `simp [RCLike.normSq_eq_def']` because `RCLike.mul_conj` yields `‖z‖^2` where the
      statement says `normSq`.
    * `FrameBlockSpanGen` — the frame-and-block decomposition and the agreement
      principle `linearMap_eq_of_frame_blockG` (step 4 of the design). Fixes:
      `(x.mat i i).re ⇝ RCLike.re (x.mat i i)`,
      `Complex.conj_eq_iff_re ⇝ RCLike.conj_eq_iff_re`, drop the two `omit`s (the new
      instance binder makes those section variables referenced).
    ★**TRAP, new and nasty**: a twin must G-suffix **every** declaration in the file, not
      just the ones you plan to use — Lean's auto-generated `match_*` auxiliaries collide
      otherwise, and the error surfaces at IMPORT time in an unrelated file
      ("environment already contains 'Necessity.eq_frame_add_blocks.match_1_1'"), not at
      compile time in the twin. Enumerate declarations with a grep before renaming.
    * `CoalescenceDiffGen` DONE too (census 121, gates green, tree at 3078 jobs) — the
      differentiated coalescence layer (`thetaNorm_fix_of_commuteG`,
      `dChi_kills_cornerG`). Name-mapping note that cost a round: the upstream twins
      name their lemmas `diagFamilyG_posDef`, `frameProjG_mat`,
      `frameProj_mat_eq_singleG` — i.e. the `G` sits where the *definition* was
      renamed, NOT uniformly at the end — so a blind `X ⇝ XG` pass produces
      `diagFamily_posDefG` and fails. Regex-remap `\bdiagFamily_(\w+)G ⇝
      diagFamilyG_\1` after the suffix pass, and grep the twin for its真 names.
    * **ALL THREE REMAINING BLOCK TWINS DONE 2026-08-06** (census 124, gates green, tree
      at 3081 jobs, custom axioms exactly `[]`; `chiTilde_block_existsG` and
      `normSq_thetaNorm_blockG` axiom-checked = core only): `BlockInvarianceGen`
      (corner/block invariance of Θ, Θ⁻¹ and χ̃), `BlockTransportGen` (block transport
      plus **`normSq_thetaNorm_blockG`** — Θ acts on each block by a Euclidean isometry,
      which over ℝ is exactly design step 2's `c² = 1`), and `BlockChiGen`
      (**`chiTilde_block_existsG`** — χ̃ acts block-isometrically at every parameter,
      design step 1).
      The self-inflicted blocker was the import chain, exactly as diagnosed: repointing
      `BlockModelGen` from `CoalescenceInstanceGen` to `BlockInvarianceGen` — mirroring
      the ℂ chain `BlockModel ← BlockInvariance ← CoalescenceDiff` — unblocked all three.
      Fifth instance of the explicit-scalar rule: `cornerConjCLMG` (a def returning a
      continuous linear map) needed `(𝕜 : Type*) [RCLike 𝕜]` explicitly.
      Also: apply the upstream remap `\bdiagFamily_(\w+) ⇝ diagFamilyG_\1` as a
      GENERAL rule, not from a hand-maintained list — the list is what kept going stale.
    * **ℝ CAPSTONE OPENED 2026-08-06** (`Necessity/RealRigidity.lean`, census 125,
      gates green, tree at 3082 jobs, custom axioms exactly `[]`) — **design steps 1
      and 2 are machine-checked**: `blockScalar` (the single real scalar by which
      `χ̃(r)` acts on the one-dimensional block, extracted from
      `chiTilde_block_existsG`), **`blockScalar_sq`** (it squares to one — the block
      isometry plus `RCLike.normSq` over ℝ being `x·x`), `blockScalar_ne_zero`,
      `blockScalar_zero` (it is `1` at the origin, from `chiTilde_zeroG`), and
      `blockScalar_eq_entry` (it reads off as a matrix entry, which is how continuity
      in `r` will be obtained).
      Traps: the upstream lemma is `blockHerm_matG` (G at the end — it is a *lemma*
      about a renamed def, not the def itself); and `rw` on a `.choose`-valued
      hypothesis fails with "motive is not type correct" — use
      `simpa [blockScalar, RCLike.normSq_apply] using h` so the choice term is
      unfolded on both sides rather than rewritten under.
    * ★★**STEPS 3 AND 4 DONE 2026-08-06 — `prop:real`'s CHARACTER STATEMENT IS
      MACHINE-CHECKED: `Necessity.chiTilde_eq_id`, the comparison character on
      `H_n(ℝ)` IS THE IDENTITY** (census 125, gates green, tree at 3082 jobs, custom
      axioms exactly `[]`; `chiTilde_eq_id` and `blockScalar_eq_one` axiom-checked =
      Lean core only). Both steps compiled FIRST TRY.
      - `eq_one_of_sq_eq_one_of_continuous` — the connectedness kernel: a continuous
        real function squaring to one and equal to `1` at the origin is identically
        `1` (if it reached `−1`, `intermediate_value_Icc`/`Icc'` forces a zero, which a
        square-root-of-one cannot be). Pure real analysis; no Jordan input.
      - **`blockScalar_eq_one`** (step 3) via `blockScalar_eq_entry` +
        `continuous_chiTilde_lineG.clm_apply` + `continuous_matG` + two
        `continuous_apply` compositions for the entry.
      - `chiTilde_fixes_frameProjG` (inline from `thetaNorm_fixes_frameProjG` on both
        factors, as planned — `TwistIdentification` never needed twinning) and
        `blockHermG_real_smul` (over ℝ the block is one-dimensional,
        `blockHerm i j z = z • blockHerm i j 1`, by `star_trivial`).
      - **`chiTilde_eq_id`** (step 4) by `linearMap_eq_of_frame_blockG`.
      **Consequence: `Θ_a = id` on `H_n(ℝ)`** — the product is Lüders and the real type
      admits no twist, i.e. the manuscript's `prop:real` on the concrete carrier,
      conditional only on S2 and the located `ThetaPreservesJordanG`.
      **PRODUCT LEVEL DONE TOO 2026-08-06**: `sp_eq_luders_diagFamily` — on the
      diagonal family of `H_n(ℝ)`, `a • b = Q_{√a} b = √a·b·√a`, i.e. **the real
      product IS the Lüders product, with no twist parameter** (axiom-checked = Lean
      core only). Route: `quadRepEquiv_apply` + `quadRep_theta` +
      `seqLeftMul_apply_effect` for the structural identity (all three already
      generalized in place), then collapse `Θ` with `chiTilde_eq_id` via
      `chiTilde_of_nonposG` + `thetaNorm_apply_eq_thetaG`. Trap: build the structural
      identity as a separate `have` and rewrite once — a `rw … at *` on the goal fails
      to find the pattern.
      **EVERY INVERTIBLE EFFECT DONE 2026-08-06** (census 126, gates green, tree at
      3083 jobs, custom axioms exactly `[]`; `sp_eq_luders_of_posDef` axiom-checked =
      Lean core only): `ConjTransportGen` (the transport half of `ConjTransport` only —
      the per-frame/globalization tail is ℂ-specific and was cut, so the twin is ~230
      lines and compiled FIRST TRY), then `eq_adUG_diagFamilyG`,
      `log_eigenvalues_nonposR`, and **`sp_eq_luders_of_posDef` — for EVERY
      positive-definite effect `a` of `H_n(ℝ)`, `a • b = Q_{√a} b`.**  Route:
      diagonalize with the vendored (already `𝕜`-general) `eq_conj_diagonal`, apply the
      diagonal-family result to the conjugated product, and transport back through the
      unitary covariance of the functional calculus
      (`HermitianMat.cfc_conj_unitary`) — the same covariance the ℂ lane used for the
      twist factor. Traps: the twin names are `adU_cancelG'` (prime AFTER the G, since
      the source is `adU_cancel'`), and `rw [← hadiag]` must fold the base point back
      BEFORE the cancellation rewrite or the pattern is not found.
      ★**REMAINING for the ℝ row: ONLY the singular-effect extension, and its one
      dependency is now pinned down (probed 2026-08-06, attempt reverted, tree green).**
      Two routes, both needing the same missing piece:
      (a) via `prop_singular` directly — needs `a ↦ Q_{√a} b` continuous, i.e. continuity
          of the functional calculus in the MATRIX argument;
      (b) via `sp_eq_on_effects_of_eq_on_posDef` — needs the ℝ Lüders product packaged as
          a `SequentialProductOn`, whose S2 field is the same continuity.
      **The blocker is `HermitianMat.cfc_continuous` (Vendor/HermitianMat/CFC.lean:354,
      `@[fun_prop]`-tagged): it is stated for `HermitianMat d ℂ` only.** Good news, measured:
      the whole joint-continuity section (lines ~415–600: `norm_cfc_le_sqrt_card_mul_bound`,
      `norm_cfc_sub_cfc_le_sqrt_card`, `norm_cfc_sub_le_of_sup_le`,
      **`continuousOn_cfc_of_compact`**, `continuous_cfc_joint_compact`) contains **ZERO**
      `Complex.*` uses — only 7 `ℂ` tokens, all as the scalar type — so a plain `ℂ ⇝ 𝕜`
      substitution takes it, EXCEPT that its two `fun_prop` calls resolve through
      `cfc_continuous`, which must be generalized FIRST. That one is the real work
      (its proof goes through `LocallyCompactSpace.local_compact_nhds` on
      `HermitianMat d ℂ` and `_root_.cfc` continuity); expect it to be mechanical too,
      but it is a vendor-tree proof, so do it deliberately with `VENDOR.md` drift noted.
      ★★**AND THE OBSTACLE IS STRUCTURAL, NOT MECHANICAL — verified at source
      2026-08-06 (attempt reverted, tree green).**  `cfc_continuous`'s proof routes
      through `ContinuousOn.cfc` at `(A := CStarMatrix d d ℂ)`, i.e. through Mathlib's
      `CStarAlgebra` instance on matrices. But **Mathlib's `CStarAlgebra` class is
      COMPLEX BY DEFINITION** — `class CStarAlgebra (A) extends … NormedAlgebra ℂ A,
      StarModule ℂ A` (Analysis/CStarAlgebra/Classes.lean:36) — so `CStarMatrix d d ℝ`
      is not an instance and this route simply does not exist over ℝ. Note the
      DEFINITION `HermitianMat.cfc` is already `𝕜`-general (that is why every twin
      works); it is only this CONTINUITY proof that is complex-routed.
      **Consequences for closing the ℝ row:**
      * Do NOT attempt a `ℂ ⇝ 𝕜` pass on `cfc_continuous` — it cannot work.
      * Route (b) is now the better bet: prove S2 for the ℝ Lüders product directly,
        i.e. continuity of `a ↦ a.cfc Real.sqrt` on the effect interval, by an
        elementary argument that avoids the C⋆ machinery — e.g. via the vendored
        `norm_cfc_sub_le_of_sup_le`-style bound plus Stone–Weierstrass on `[0,1]`
        (polynomials in `a` are manifestly continuous in `a`, and the spectrum of an
        effect lies in the compact `[0,1]` by `eigenvalues_mem_Icc_of_effect`, which IS
        already `𝕜`-general). That is the same skeleton as
        `continuousOn_cfc_of_compact`, but with `fun_prop`'s appeal to `cfc_continuous`
        replaced by hand-rolled polynomial continuity — the one genuinely new proof
        obligation left in the whole real row.
      * Everything else in the joint-continuity section still measured clean
        (zero `Complex.*`), so once polynomial-cfc continuity exists over `𝕜` the rest
        of that section is a substitution.
      **FIRST PIECE BANKED 2026-08-06**: the three eigenvalue/norm bounds the elementary
      argument needs — `norm_cfc_le_sqrt_card_mul_bound`,
      `norm_cfc_sub_cfc_le_sqrt_card` and **`norm_cfc_sub_le_of_sup_le`** (`‖A.cfc f −
      A.cfc g‖ ≤ √card · sup_T ‖f−g‖` when `spectrum A ⊆ T`) — are now stated over
      `RCLike 𝕜` (Vendor/HermitianMat/CFC.lean ~418–478; pure `ℂ ⇝ 𝕜`, no proof edits,
      whole tree green at 3083 jobs, census 126, custom axioms exactly `[]`). They are
      the C⋆-free part: they go through `norm_eq_sum_eigenvalues_sq` and the eigenvalue
      bound, never through `CStarAlgebra`. So the remaining obligation is exactly:
      **continuity of `a ↦ a.cfc (polynomial)` over `𝕜`** — plus Stone–Weierstrass on
      `[0,1]` and these bounds. No C⋆ machinery anywhere in that route.
      **AND THAT PIECE IS NOW DONE 2026-08-06** (`Hermitian/CfcPoly.lean`, NEW, census
      127, gates green, tree at 3084 jobs, custom axioms exactly `[]`;
      `continuous_cfc_polynomial` axiom-checked = Lean core only):
      `mat_cfc_pow` (`(A.cfc (·^k)).mat = A.mat ^ k`, by induction through
      `mat_cfc_mul_apply` + `cfc_id'`), `continuous_cfc_pow`, and
      **`continuous_cfc_polynomial`** — `A ↦ A.cfc (p.eval ·)` is continuous for every
      real polynomial `p`, over ANY `RCLike 𝕜`. Proved by `Polynomial.induction_on'`,
      with the monomial case done at the MATRIX level (`c * x^k` via
      `mat_cfc_mul_apply` + `cfc_const`), because there is no `HermitianMat.cfc_smul`.
      Traps: `Continuous.subtype_mk` + an explicit `show` on `.mat` is the way into the
      subtype (`IsInducing.subtypeVal.continuous_iff` does not resolve here); and the
      `k = 0` case wants `symm; simp`, since `rw [pow_zero]` does not fire on
      `1 = ↑A ^ 0`.
      ★★★**THE ℝ ROW IS CLOSED — 2026-08-06.**
      `HermitianMat.continuousOn_cfc_sqrt_effects` (`Hermitian/CfcSqrtContinuous.lean`,
      NEW): `A ↦ A.cfc √` is continuous on the effect interval over ANY `RCLike 𝕜` —
      Weierstrass on `[0,1]` + `continuous_cfc_polynomial` + `norm_cfc_sub_le_of_sup_le`
      + a three-ε estimate; `spectrum_subset_Icc_of_isEffect` supplies the compact
      window. **No C⋆ machinery**, which is exactly why it goes where `cfc_continuous`
      cannot.
      Then in `Necessity/RealRigidity.lean`: `dense_posDef_effectsR` (the ℝ twin of the
      boundary-sequence density) and
      **`sp_eq_luders_of_effect` — every S1–S7 sequential product with S2 on `H_n(ℝ)`
      is the Lüders product `a • b = √a·b·√a` on ALL effects, singular ones included.
      The real type admits no twist parameter whatsoever.**
      Census 128, gates green, tree at 3085 jobs, custom axioms exactly `[]`;
      `sp_eq_luders_of_effect` and `continuousOn_cfc_sqrt_effects` axiom-checked
      individually = Lean core only.
      **Hypothesis accounting, exactly**: the `SequentialProductOn` fields (S1, S3–S7),
      S2, and `ThetaPreservesJordanG` in each eigenframe — the last carried as a
      LOCATED hypothesis because real Kadison/Uhlhorn exists in no prover, precisely as
      the manuscript cites it (and precisely as the ℂ row stood before M3). Record it
      that way in THEOREM-MAP; do not call the ℝ row unconditional. All three are pure recipe — the ℂ originals have zero genuinely
    complex content beyond `normSq`, which becomes `‖t‖²`/`RCLike.normSq`.
    NOTE the ℝ simplification worth exploiting: over ℝ, `blockHerm i j t` has no phase,
    so `BlockTransportGen`/`BlockChiGen`/`BlockSkewGen`/`PhaseCocycleGen`/`PhaseAnchorGen`
    — the entire phase apparatus of the ℂ lane — are **NOT** needed. The ℝ ending is
    ~3 twins plus one short file, not a re-run of LEDGER 2.6.
  * **M4.1 REMAINING: only the ℝ ending, per the four-step design above.** Everything the abstract `real_kill` needs
    (`ρ`, `dχ`, `T`, `ρ_skew`, `coupling`) is now constructible over `𝕜`; what is left is
    the ℝ-specific block layer (1-dimensional Peirce blocks) and the
    `DiagonalHomSetup`/`StabilizerCoupling` wiring, then `real_kill` fires. The
    deliverable is conditional on `ThetaPreservesJordanG` (real Kadison being
    unavailable — see above); state it that way in THEOREM-MAP.
    Then `Chi` (which must switch to the `…Gen` frame/family names) →
  `ComparisonInstance` → `Chi*`/`Coalescence*`; then the short ℝ ending.
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

- **5.1 Lifting step — DONE 2026-08-05, AND THE COVERING-SPACE ROUTE WAS NOT
  NEEDED** (`RankTwo/Lifting.lean`, census 93, gates green). The planned route
  (`Circle.isCoveringMap_exp` + `existsUnique_continuousMap_lifts` + ker-exp
  discreteness) is SUPERSEDED: M2's own `multiParameter_eq_exp` (built from
  scratch in 2.7 for the Aczél discharge) already says a continuous character
  of a real vector space into ANY real Banach algebra is `exp ∘ D` for a unique
  LINEAR `D`.  So: `character_eq_exp_linear` (the general restatement), and
  **`circleCharacter_linear_functional`** — modelling the rotation group as the
  unit circle in ℂ (a Banach algebra, so no matrix-norm instance friction),
  a continuous modulus-one character is `r ↦ exp (i φ r)` for a real-LINEAR
  functional φ: the modulus-one condition forces `(D r).re = 0` via
  `Complex.norm_exp` + `Real.exp_injective`, and φ := `(D ·).im` is linear
  because D is.  **No 2π ambiguity arises at all** — linearity is forced rather
  than chosen.  Plus `circleCharacter_functional_unique` (through
  `Globalization.real_character_unique` on the line through r).
  TRAPS: `Complex.exp_eq_exp_ℂ` rewrites `NormedSpace.exp → Complex.exp`, so
  the direction is the OPPOSITE of what the goal shape suggests; after
  `refine ⟨{ toFun := … }, ?_⟩` add `LinearMap.coe_mk, AddHom.coe_mk` to the
  simp set or the structure projection blocks `ring`; `map_smul` fires once for
  BOTH hypotheses when they share the shape — don't repeat it.
  Risk was LOW; realized cost ~90 lines.
- **5.2 ℝP² carrier — DONE 2026-08-05, AND THE HAND-BUILT QUOTIENT WAS NOT
  NEEDED** (`RankTwo/RealProjective.lean`, census 94, gates green). The planned
  route (S²/± via orbit-quotient machinery + a
  `Function.Even → FactorsThrough` bridge + `IsQuotientMap.liftEquiv`) is
  SUPERSEDED by the 08-04 HARVEST option, now executed: the vendored
  `Vendor/Wigner/Topology.lean` — already in the tree, inside the audited
  Wigner closure — is stated for `[RCLike K]`, which covers **K = ℝ**.  So
  `RP2 := ℙ ℝ (EuclideanSpace ℝ (Fin 3))` is **compact Hausdorff for free**
  (`instT2Space`, `instCompactSpace` both by `inferInstance`), with the
  quotient topology built in.  `RP2.mk_eq_mk_iff` gives the antipodal
  identification from the projective quotient (`RP2.mk_neg`: v and −v agree)
  rather than constructing it, and `QubitModuli := C(ℝP², ℝ)` is
  cor:qubit-classification's object, with its `CommRing` inherited and
  `QubitModuli_nontrivial` recorded.  TRAP: `mk_eq_mk_iff'` is stated with a
  BARE scalar `∃ a : K, a • w = v`, not `a : Kˣ` — don't ascribe units.
  REMAINING in M5: only 5.3, the assembly — connect
  `MasterTheorem/RankTwo.lean`'s existing algebraic core (`sp_blockForm`,
  `n2_necessity`, `angle_factor`, `sp_maps_effects`, the τ invariant
  `tau`/`tau_std_eq_one`/`tau_had_eq_zero`) to `QubitModuli`, i.e. exhibit the
  frame ↦ τ(F) assignment as an element of `C(ℝP², ℝ)`.  Note `tau` is ALREADY
  defined on pairs of rank-one projections and is swap-invariant
  (`tau_swap_invariant`) — that swap-invariance is exactly what makes it
  descend to the projective quotient, so the descent step should now be short.
- **5.3 Assembly (cor:qubit-classification) — FRAME FUNCTION DONE 2026-08-05**
  (`RankTwo/FrameFunction.lean`, census 95, gates green, zero sorries).
  `QubitFrame := ℙ ℂ (EuclideanSpace ℂ (Fin 2))` (compact Hausdorff free from
  the vendored topology, same harvest as 5.2); `tauVec` = the existing
  `MasterTheorem.RankTwo.tau` read off a nonzero vector via the normalized
  rank-one; **`tauVec_scale_invariant`** — it only sees the RAY (proof reuses
  `Necessity.rankOne_normalize_smul` from the M3 chain: write both vectors as
  scalar multiples of the same unit vector, then normalization absorbs the
  scalar into a unit-modulus factor that `rankOne` kills);
  **`tauVec_eq`** — the explicit formula `τ = (2|v₀|²/‖v‖² − 1)²`, because
  against `Rref = diag(1,0)` the trace `tr(PR)` is just `P₀₀`; hence
  `tauVec_continuous` is elementary; **`tauFrame`** (descended by the vendored
  `Projectivization.continuous_lift`), `tauFrame_continuous`, and
  **`tauModuli : C(QubitFrame, ℝ)`** — the moduli element of
  cor:qubit-classification, now an honest continuous function on the frame
  space rather than a prose claim.
  TRAPS: `set` does not fold occurrences created LATER by `unfold` — re-fold
  with `rw [← hN]`; `Real.sqrt_mul_self` vs `Real.mul_self_sqrt` differ in
  orientation and `rw` picks the wrong one silently; a `|>.re` pipe inside a
  `calc` step breaks parsing into a `Unit`-valued mess — write the projection
  explicitly; `fun_prop` has no continuity lemma for `HermitianMat.rankOne`, so
  derive an explicit coordinate formula first (this is why `tauVec_eq` exists).
  **COMPLEMENTATION INVARIANCE DONE 2026-08-05**
  (`RankTwo/Complementation.lean`, census 96, gates green, zero sorries):
  `orthoVec (a,b) := (−b̄, ā)` with `orthoVec_orthogonal`, `nsq_orthoVec`,
  `orthoVec_real_smul`; **`rankOne_orthoVec`** — the geometric identity that
  passing to the complement ray IS the complementation `P ↦ 𝟙 − P` (for a unit
  vector, `(orthoVec ψ)(orthoVec ψ)* = 𝟙 − ψψ*`); and **`tau_orthoVec_eq`** —
  composing it with the already-proved `tau_swap_invariant` shows τ does not
  distinguish a ray from its complement, i.e. **τ is a function of the FRAME**,
  not of the ray.  TRAP: after `fin_cases i` the index appears as `⟨0, ⋯⟩`,
  which the literal-indexed `@[simp]` lemmas do NOT match — use
  `refine funext ?_; rw [Fin.forall_fin_two]` (and `Matrix.ext` +
  nested `Fin.forall_fin_two` for matrices) instead of `fin_cases`; the cleanest
  uniform finish for the four entry goals is `apply Complex.ext` then
  `simp only [re/im lemmas]` then `linarith [hsum']` with the norm condition
  pre-expanded into real components.
  **FRAME DEPENDENCE SEPARATED AT THE OPERATION LEVEL 2026-08-05**
  (`RankTwo/Separation.lean`, census 97, gates green, zero sorries).  Gap
  closed: `MasterTheorem/RankTwo.lean` had `sp_tau_had_is_luders` and
  `sp_tau_std_is_unit_twist` but NEVER showed the two products differ, so
  "rank two escapes mthm:master's rigidity" rested on the dial alone.  Now
  `offCoeff_sep` and **`sp_luders_ne_unit_twist`**: at λ = (1,4) the Lüders
  member and the unit-twist member disagree on the coherence matrix `E₀₁`,
  because the off-diagonal phase is `e^{−i log 4}` and `0 < log 4 < 2π`
  (`log_four_pos`; `log_four_lt_two_pi` via `Real.log_le_sub_one_of_pos` giving
  log 4 ≤ 3, then `Real.pi_gt_three`).  TRAPS: `Real.pi_gt_three` needs
  `import Mathlib.Analysis.Real.Pi.Bounds` (not transitively present);
  `Complex.exp_eq_one_iff` yields `z = n * (2πI)` and `field_simp` cancels the
  `I` for you, so cast the REMAINING real equation, don't hand-cancel;
  `Real.log_lt_self` does not exist under that name.
  REMAINING in 5.3: the BIJECTION itself — that every rank-two S1–S7 product
  arises from exactly one `tauModuli`-style element, and conversely. Forward
  direction needs the frame-indexed family of `MasterTheorem.RankTwo.sp` glued
  over `QubitFrame`; the τ↦product direction is `sp_blockForm` +
  `sp_maps_effects` (both proved); injectivity is `tau_std_eq_one` vs
  `tau_had_eq_zero` separating frames (proved) plus `n2_necessity`'s
  one-parameter-per-frame rigidity (proved).  Also still open: the
  ℂP¹-modulo-complementation ≅ ℝP² identification (the `RP2` carrier from 5.2
  exists; `tau_swap_invariant` is the descent input).
  ★**RE-SCOPED AT SOURCE 2026-08-06** (after the ℝ row closed). What exists in
  `RankTwo/`: `QubitFrame`, `Vec`/`Frame` with their continuity (`Vec_continuous`,
  `Frame_continuous`), `Moduli`, the carrier `RP2 := ℙ ℝ (EuclideanSpace ℝ (Fin 3))`
  and **`QubitModuli := C(RP2, ℝ)`** with its ring structure and
  `QubitModuli_nontrivial`, the complementation kit (`Vec_orthogonal`,
  `orthoVec_eq`, `Vec_real_smul`), the lifting/character layer, and the separation
  (`Coeff_sep`, `sp_luders_ne_unit_twist`). On the abstract side
  `MasterTheorem.RankTwo.sp`/`sp_apply`/`sp_maps_effects`/`sp_blockForm` are proved.
  **PART 1 DONE 2026-08-06** (`RankTwo/Descent.lean`, NEW, census 129, gates green,
  tree at 3086 jobs, custom axioms exactly `[]`; `tauFrame_orthoFrame` axiom-checked =
  Lean core only): `orthoE` (complementation at the `EuclideanSpace` level) with
  `nsq_orthoE`/`orthoE_ne_zero`, **`orthoVec_smul` — `orthoVec` is CONJUGATE-linear
  (`orthoVec (t • v) = star t • orthoVec v`), which is exactly why complementation
  descends to projective space** (a scaling becomes its conjugate, still a unit),
  `orthoFrame` (the involution on `ℂP¹`, via `Projectivization.lift` with that
  conjugate-linearity as the well-definedness datum), and
  **`tauFrame_orthoFrame` — the frame function is complementation invariant, so `τ`
  factors through `ℂP¹ / complementation`.**
  Proved from `tauVec_eq`'s explicit formula rather than the abstract
  `tau_swap_invariant`: complementation swaps `|v₀|²` and `|v₁|²`, which negates
  `2|v₀|²/‖v‖² − 1`, and that bracket is squared. Much shorter than routing through
  the Jordan-level swap lemma.
  **PART 2 DONE 2026-08-06** (`RankTwo/Bloch.lean`, NEW, census 130, gates green, tree
  at 3087 jobs, custom axioms exactly `[]`; `blochVec_orthoVec` and `blochVec_ne_zero`
  axiom-checked = Lean core only): the Bloch map's vector layer,
  `blochVec v = (2 Re(v̄₀v₁), 2 Im(v̄₀v₁), |v₀|² − |v₁|²)`, with the three facts that
  make it the right bridge to `ℝP²`:
  * **`blochVec_normSq` : `‖B(v)‖² = ‖v‖⁴`** — hence `blochVec_ne_zero` on nonzero rays;
  * **`blochVec_orthoVec` : complementation NEGATES `B`** — and `ℝP²` identifies `x`
    with `−x` (`RP2.mk_neg`, already present), so the Bloch POINT is constant on
    complementation classes;
  * **`blochVec_smul` : `B(t•v) = |t|² • B(v)`** — the scaling is a POSITIVE real, so
    the Bloch point is a function of the ray.
  Proof note: `fin_cases i` on `Fin 3` produces goals indexed by `⟨0, _⟩` rather than the
  literal `0`, so `@[simp]` apply-lemmas stated at `0`/`1`/`2` do NOT fire — unfold
  `blochVec` (and `orthoVec`) directly in the `simp` set and close with `ring`.
  **PART 2b DONE (same commit day)**: the map is now packaged ON THE FRAME SPACE —
  `blochE`/`blochE_ne_zero`, **`blochFrame : QubitFrame → RP2`** (via
  `Projectivization.lift`, well-definedness = `blochVec_smul` since `|t|² ` is a
  positive real and `ℝP²` quotients by ALL real scalings),
  **`blochFrame_continuous`** (the same `Projectivization.continuous_lift` route as
  `tauFrame_continuous`, composed with the vendored `Projectivization.continuous_mk'`),
  and **`blochFrame_orthoFrame` — the Bloch map is complementation invariant** (via
  `RP2.mk_neg`). Both axiom-checked = Lean core only.
  So `τ` and the Bloch map are now a COMPATIBLE PAIR of descents ON THE FRAME SPACE:
  both continuous, both complementation invariant (`tauFrame_orthoFrame` +
  `blochFrame_orthoFrame`).
  Proof notes: `PiLp.continuous_toLp` is the name for the `WithLp` direction (there is
  no `WithLp.continuous_toLp`); and componentwise continuity needs FULL `simp [blochVec]`
  before `fun_prop`, because `fin_cases`'s `⟨0, ⋯⟩` indices block `Matrix.cons_val_*`.
  **SURJECTIVITY DONE 2026-08-06** — `blochVec_inverse` + **`blochFrame_surjective`**
  (axiom-checked = Lean core only). The inverse-Bloch construction avoids trigonometry
  and normalization entirely: for `w = (x,y,z) ≠ 0` put `r := z + ‖w‖` and take the ray
  `v = (r, x + iy)`; then `B(v) = 2r • w`, because `r` is precisely the positive root of
  `r² − 2zr − (x²+y²) = 0` (expand `r² − (x²+y²)` using `‖w‖² = x²+y²+z²`). The single
  degenerate branch is `x = y = 0, z < 0` (where `r = 0`), met by the south pole
  `v = (0,1)` with factor `−z⁻¹`. Two cases, no square roots beyond `‖w‖`, no charts.
  ★★**THE MODULI ELEMENT NOW LIVES IN THE PAPER'S CARRIER — 2026-08-06.**
  `tauRVec`/`tauRVec_scale_invariant`/**`tauRP2 : RP2 → ℝ`**/`tauRP2_continuous`/
  **`tauModuliRP2 : C(ℝP², ℝ)`** (axiom-checked = Lean core only).
  ★**The quotient-map machinery turned out to be UNNECESSARY.** `τ` has a closed form
  in Bloch coordinates: from `tauVec_eq`, `τ = (2|v₀|²/‖v‖² − 1)²`, and
  `2|v₀|²/‖v‖² − 1 = (|v₀|²−|v₁|²)/‖v‖² = B₃/‖B‖` (using `‖B(v)‖ = ‖v‖²`, i.e.
  `blochVec_normSq`).  So **`τ = (w₂/‖w‖)²` in Bloch coordinates** — a manifestly
  scale-invariant, manifestly continuous function of `w`, which lifts straight to
  `ℝP²` by `Projectivization.lift` + `continuous_lift`.  No compactness, no
  Hausdorffness, no closed-map argument, and **no injectivity-modulo-complementation
  needed** (that lemma was going to be required for the quotient route and is now moot).
  **BRIDGE IDENTITY DONE 2026-08-06**: `sqrt_blochVec_normSq` (`‖B(v)‖ = ‖v‖²`),
  `tauRVec_blochE`, and **`tauRP2_blochFrame : tauRP2 (blochFrame p) = tauFrame p`**
  (plus the `@[simp]` packaged form `tauModuliRP2_blochFrame`), axiom-checked = Lean
  core only. So `tauModuliRP2` is not merely *a* function on `ℝP²` — it is provably
  **the frame function itself**, expressed on the carrier `cor:qubit-classification`
  names. The whole descent `ℂP¹ → ℝP²` is now complete and certified:
  `blochFrame` (continuous, surjective, complementation invariant) together with
  `tauRP2_blochFrame`.
  **NONCONSTANCY DONE**: `tauVec_std` (τ = 1 at `[1:0]`), `tauVec_had` (τ = 0 at
  `[1:1]`) and **`tauModuliRP2_nonconstant`** — the distinguished element genuinely
  varies over `ℝP²`, so the carrier is exercised rather than decorative (the
  `ℝP²`-level form of the V9 separation). Axiom-checked = Lean core only.

  ★★**SCOPING CORRECTION, verified at source 2026-08-06 — read this before planning
  5.3.** `grep -c SequentialProductOn RadicalRelativity/RankTwo/*.lean` returns **0 for
  every file**: NOTHING in the rank-two lane is product-parameterized, and
  `MasterTheorem.RankTwo.n2_necessity` takes a *linear `angle`*, not a product. So what
  the lane currently contains is (a) the moduli SPACE `C(ℝP², ℝ)`, (b) ONE distinguished
  ELEMENT of it (`tauModuliRP2`, now known nonconstant), (c) the full certified descent
  `ℂP¹ → ℝP²`, and (d) the separation. **The classification MAP `product ↦ moduli` is
  entirely absent** — it is not "gluing an existing family", it is the whole forward
  direction. Building it needs per-frame parameter extraction from an ARBITRARY rank-two
  product, i.e. the `N = 2` analogue of the M2 lane; the `N ≥ 3` machinery does not apply
  (`StabilizerCoupling` carries `rank_ge : 3 ≤ n`). Earlier LEDGER text describing 5.3's
  remainder as "the frame-indexed family glued over `QubitFrame`" UNDERSTATED this;
  budget it as a lane, not an assembly.
  **REMAINING for M5.3: the classification map (above), i.e. the former "gluing"** — assembling the per-frame
  family of `MasterTheorem.RankTwo.sp` into a single product over `QubitFrame`, which
  is what makes the map `product ↦ τ` well defined in the first place. Injectivity of
  the classification is already free (`tau_std_eq_one` vs `tau_had_eq_zero` +
  `n2_necessity`).
  **The remaining pieces:**
  (i) **the descent** `ℂP¹ / complementation ≅ ℝP²` — a quotient-topology
      homeomorphism, with `tau_swap_invariant` as the descent datum; this is the
      real work of 5.3 and is a topology unit, not an algebra one;
  (ii) **the frame-indexed gluing** — assembling the per-frame family of
      `RankTwo.sp` into a single product over `QubitFrame`, which is what makes the
      map `product ↦ τ ∈ C(ℝP², ℝ)` well defined; `Frame_continuous` is the input
      that makes the glued τ continuous.
  Injectivity is then free (`tau_std_eq_one` vs `tau_had_eq_zero` +
  `n2_necessity`'s one-parameter-per-frame rigidity, all proved).
  NOTE the ℝ row's new field-general tools are available here and may shorten (ii):
  `continuousOn_cfc_sqrt_effects` is exactly the continuity a frame-function argument
  wants, and it holds at `N = 2` like everything else in that file.
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

★**FOUNDATION ATTEMPTED AND SCOPED 2026-08-06 (draft reverted, tree left green).** The
omnibus assembly needs a carrier for the simple-factor decomposition — the DIRECT SUM of
order-unit spaces — and that is the natural first unit, because the assembly theorem
("given the per-type rows, a product on a direct sum is determined factorwise") can be
proved INDEPENDENTLY of whether the rows are finished. Attempting
`instance : OrderUnitSpace (V × W)` surfaced two concrete obstacles, both plumbing:
* **`OrderUnitSpace` extends `PartialOrder`, so a product instance must SUPPLY that parent
  explicitly** (`toPartialOrder := Prod.instPartialOrder`). Without it Lean synthesizes an
  anonymous parent and then `h.1`/`h.2` on an order hypothesis fail with
  "Invalid projection … `instProd.toLE.1 0 a`". Same reason `prod_ousUnit`'s `rfl` fails.
* **The class has NO scalar-monotonicity-in-the-scalar lemma** (`r ≤ s → 0 ≤ x →
  r • x ≤ s • x`): grep for `smul_le_smul`/`smul_mono` in `OrderUnitSpace.lean` returns
  nothing. `archimedean` for the product needs exactly that (to compare against
  `max r₁ r₂`), so **write that lemma first** — from `smul_nonneg_mono` plus
  `sub_smul` and `ousUnit_nonneg` it is a few lines, and it is generally useful.
★★**STEPS (1)–(3) NOW DONE 2026-08-06** (census 133, gates green, tree at 3090 jobs,
custom axioms exactly `[]`; `instProd`, `isEffect_prod_iff` and
`smul_le_smul_of_le_of_nonneg` all axiom-checked = Lean core only):
* `OrderUnitSpace.le_of_sub_nonneg` and **`OrderUnitSpace.smul_le_smul_of_le_of_nonneg`**
  (monotonicity in the SCALAR — the companion to `smul_nonneg_mono`'s monotonicity in the
  element; the class had been missing it, and it is generally useful);
* **`OrderUnitSpace.instProd : OrderUnitSpace (V × W)`** — the direct-sum carrier, with
  the parent supplied as `Prod.instPartialOrder _ _` (note the EXPLICIT `_ _`: the bare
  name is a function of the two types and mismatches) and order-unit boundedness by
  comparing both components against `max r₁ r₂`;
* **`isEffect_prod_iff`** — an effect of a sum is exactly a pair of effects; the order
  hypotheses must be unfolded with `Prod.le_def` before projecting, exactly as the failed
  first attempt indicated.
**So M7's carrier now exists.** REMAINING for the omnibus: (4) the factorwise assembly —
restrict a `SequentialProductOn (V × W)` to each summand (well defined by
`isEffect_prod_iff`), then show a product is determined by its restrictions. That step is
independent of whether the per-type rows are finished, so it can be done now.


### M7 unit 2 — the factorwise assembly, both provable halves (DONE, 2026-08-06)

`RadicalRelativity/DirectSum.lean` (extended). The assembly splits into THREE statements,
and exactly two of them are provable without `prop:central`:

1. **Sufficiency — DONE.** `SequentialProductOn.prod P Q : SequentialProductOn (V × W)`,
   `sp a b := (P.sp a.1 b.1, Q.sp a.2 b.2)`. All nine S1–S7 fields discharged
   componentwise, first compile, zero errors. The reason it is this cheap is worth
   recording: **compatibility in this interface is not a side condition but literally the
   equation `a & b = b & a`**, and on a pair that equation splits into its two components
   via `Prod.mk.injEq`. So the four compatibility-hypothesis fields need no extra input —
   they destructure exactly like the algebraic ones. Order hypotheses (`b + c ≤ 𝟙`) split
   through `Prod.le_def`, effect hypotheses through `isEffect_prod_iff` (unit 1).
2. **Determination — DONE.** `prod_fst`/`prod_snd` (both `rfl`: the restriction to a
   summand is literally a projection) and `sp_eq_of_prod_eq : (P.prod Q).sp =
   (P'.prod Q').sp → P.sp = P'.sp ∧ Q.sp = Q'.sp`, by probing at `(a, 0)` and `(0, a')`.
   This is what makes the factorwise classification lossless: distinct summand products
   give distinct sums, so classifying the factors classifies the sum.
3. **The splitting — NOT DONE, and it is the paper's own citation boundary.** That *every*
   product on a direct sum has the form `P.prod Q`. This is `prop:central`: a product is
   compatible with each central idempotent, hence preserves the summands.
   `central_decomposition` machine-checks only the componentwise identity, not this.

**Honest statement of the omnibus row: the assembly is certified CONDITIONAL on the
splitting.** That is a different and much better position than "assembly remains" — the
two halves that were open combinatorial work are now machine-checked, and what is left is
one structural proposition that the manuscript already cites rather than proves. Gates
green at 3090 jobs, census 133, custom axioms exactly [].

- **7.1 mthm:omnibus.** Direct-sum assembly; summand inheritance of S1–S7 +
  converse (the documented paper-only halves of prop:central). Risk LOW-MED.
- **7.2 prop:pseudo-transfer.** Small. Risk LOW.
- **7.3 Statement upgrade. DONE for the ℝ and ℂ rows (2026-08-07).**
  `PaperA/CertifiedConfiguration.lean` instantiates both reference maps concretely —
  `ludersRefR` (conj-Lüders) and `twistRefC` (`twistSeq`), each with effect closure PROVED
  (`HermitianMat.luders_isEffect`, resting on the new field-general
  `HermitianMat.cfcSqrt_mul_self`: `√a·√a = a`) — bridges the carrier-pinned product to the
  statement layer's class (`SequentialProductOn.toSequentialProduct`), and discharges both
  frozen shapes: `PaperA.real_meets_ludersConclusion` and
  `PaperA.complex_meets_uniqueTwistConclusion`. So for these two rows the audited shape and
  the proved theorem are the SAME statement, which is the whole point of the boundary.
  `Statement.lean`'s now-false "the concrete reference maps do not yet exist" paragraph was
  corrected in place (docstring only — no printed type changed, so no audit pin moved).
  README updated the same day: it now names the two unconditional row capstones with their
  `#check` output, and no longer calls the abstract `master_chain` skeleton "the capstone
  theorem" (it says explicitly that a clean closure over quantified interface fields is not a
  verification of the paper's theorem).
  **Still open in 7.3:** the ℍ and 𝕆 rows have no theorems to point at, so their shapes
  remain shapes; the paper's §App + disclosure paragraph are NOT yet rewritten (that is a
  manuscript edit in `landing/papers/twist-normal-form/`, Bryan-gated, and it should be done
  in one pass when the next venue is chosen).
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
