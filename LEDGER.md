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

## ★★ ARC-6 ORDERS (2026-08-08, Fable design pass — the big-chunk climb). READ THIS FIRST.

**Sizing:** this is a ~24-hour-of-work campaign, set as ONE goal on purpose. Do not stop at
rung boundaries to report; continue until the ladder is exhausted or every remaining item
is banked with a measured wall. Every decision needed is pre-made below; anything
Bryan-gated is out of scope by definition, so there is nothing to ask mid-arc.

**Standing decision records — do not re-litigate:** literal 36/36 REJECTED and EJA-first
REJECTED (rationale in the ARC-5 block below); the six by-design-external rows are
`thm:vdw1` + `prop:bridge` (cited), `mthm:master`/`mthm:omnibus` one-theorem form (JvNW),
`prop:theta` at vIR generality, `thm:albert` (Albert M2). Interior ceiling 30, realistic
26–28. The count is an OUTPUT, not a quota — the census (`custom axioms exactly []`) and
`THEOREM-MAP.md` are the product. Baseline at these orders was **7 / 19 / 10**; **as executed the arc ended at 8 / 19 / 9** —
see the EXECUTION RECORD below and `STATEMENT-MANIFEST.md`, which is authoritative; the denominator stays pinned to blob `205fdf5a` — never re-pin.

**THE LADDER (in order; the wall protocol below governs every rung):**

* **6.0 Audit before build.** Two of arc-5's seven FORMALIZED rows were undercounted rows,
  not new proofs. Before any new proof this arc, for every row targeted below: (a) grep the
  WHOLE tree for the *ingredients*, not the assembled statement; (b) run the
  inert-hypothesis test on the nearest existing declaration (compile the conclusion with
  the hypothesis deleted). Specifically: re-price `lem:homomorphism` by reading what
  `chiTilde_eq_exp_dChi` actually proves (it exists and feeds `dChi_kills_corner`, so
  "Lean never differentiates Θ" may be another directory-scoped absence claim), and price
  `lem:simple-bridge` clause by clause (attempt later only the clauses this audit shows
  cheap). Verdicts recorded in `THEOREM-MAP.md` in one commit.
* **6.1 Close the rank-two lane — the crown.** In order: (a) diagonal-phase-fibre
  constancy of `n2FrameTwist` (the `U(2) → S²` gap in `prop:n2-necessity`);
  (b) `lem:n2-bounded`; (c) `lem:n2-continuity` — check Mathlib for topology/compactness
  instances on `Matrix.unitaryGroup` before hand-rolling anything, and if continuity plus
  compactness gives (b) for free, take that order; (d) the remaining descent clause of
  `lem:n2-descent` (a continuous function on `ℝP²`); (e) `prop:n2-sufficiency` —
  generalize the constant-`t` machinery of `lem:twist-sufficiency` to continuous
  `t : ℝP² → ℝ`, reusing the τ-family partials already banked under `thm:qubit-boundary`;
  (f) assemble `cor:qubit-classification` as the bijection; (g) discharge
  `thm:qubit-boundary`'s bundled S1–S7 clause as an instantiation of (e).
  ★ CHECKPOINT REVIEW after (f) — see the review protocol.
* **6.2 The differential trio.** `lem:homomorphism` (the carrier is a normed space, so
  Mathlib `fderiv` applies; pre-registered fallback = the pointwise-derivative version,
  banked as PARTIAL with the delta named), then `lem:coalescence` (identify the in-tree
  shadow WITH the article's differential — the identification is the open part, not the
  shadow), then `prop:stabilizers` (construct the representation from Θ; ℂ row first — it
  is the one the flagships consume; the ℝ/ℍ/𝕆 rows are bankable).
* **6.3 The abstract tier.** Supply the Archimedean property as an explicit `Prop`/mixin —
  NOT a change to `SequentialProductCore.mk` (`AxiomAudit.lean` Layer 5 freezes the
  printed constructor type). Then: abstract `lem:homog`(ii), abstract `lem:cone-ext`, and
  divide the `pseudoInvCoef` out of `prop:pseudo-transfer` to reach the article's
  `a·a⁻¹ = 𝟙` form. ★ **This next sentence was falsified during the arc and is retained only as
  the order as written:** "`lem:homog`(i) needs a positive-linear-extension construction:
  attempt it, bank on resistance." The construction **already existed** —
  `Necessity.seqLeftMul` — so what (i) actually needs is the abstract port, not a construction
  (see the EXECUTION RECORD and `THEOREM-MAP.md` §3b). ★ CHECKPOINT REVIEW after this rung.
* **6.4 The caveat sweep, in yield order.** `cor:selectors`(iii) — exactly one missing
  lemma, `(cfc f a)ᵀ = cfc f (aᵀ)`, recipe recorded in `ComplexRowUnconditional.lean` —
  then clause (i); `lem:normality` (f.d. order-unit space, S1+S2 ⟹ vdW-normal);
  `lem:frame-fix` general statement; `lem:frame-connectivity` via a Givens/Jacobi
  factorization into rank-two block rotations (`AdjBlock` is strictly finer than
  `AdjAxis` — the three Householder factors in the tree do NOT suffice); `lem:orientation`;
  `prop:central`'s summand inheritance + converse assembly; any `lem:simple-bridge`
  clauses that 6.0 priced cheap.
* **6.5 The ℍ row — stretch.** `thm:quaternionic` via `H_n(ℍ) ↪ H_{2n}(ℂ)` as the fixed
  points of a conjugate-linear involution (the blocker is ℍ ∉ `RCLike`, not missing
  quaternions — Mathlib has them); quaternionic Wigner may fall to the `RealWigner`
  rank-one technique. Bank freely; this rung is allowed to end as a measured remainder.

### ARC-6 EXECUTION RECORD (append per rung; the orders above stay as written)

**6.0 audit — DONE 2026-08-08, and it repriced the arc's biggest row before a line was
written.** Two verdicts:
* ★★ **`lem:homomorphism` was ABSENT for a false reason.** §2 of `THEOREM-MAP.md` said "Lean
  neither differentiates `Θ` nor proves `dχAdd` is its derivative"; that describes the
  *abstract skeleton* and was generalized to the whole tree. In fact `chiTilde` constructs the
  character by the article's own `min(x,0)` decomposition and `chiTilde_eq_exp` **proves** the
  real-linear differential exists and is unique, via `multiParameter_eq_exp` — no Lie theory,
  and needing only line continuity where the article assumes joint. Only the hyperplane
  factorization was genuinely missing, and rung 6.2 closed it the same day (below). §3's
  summary line "the construction of the comparison character and its differential from `Θ_a`"
  was removed for the same reason. Row: ABSENT → **PARTIAL**; detail in `THEOREM-MAP.md` §3c.
* **`lem:simple-bridge` priced per clause: it is ~3/4 cited.** The article's own proof assigns
  (i) to vdW Thm. A.6, (iii) to vdW Props. 4.19–4.20, (iv) to a vdW remark. Only (ii) is
  interior (the Jordan spectral theorem). Honest target = clause (ii) on the concrete carrier.
  This is the row the ceiling arithmetic flagged for honest pricing.

**6.1 rank-two lane — (a) CLOSED; (b)(c) BANKED with a named, available enabler.**
* **(a) DONE.** `n2FrameTwist_mul_diagonal` closes the `U(2) → S²` diagonal-phase-fibre gap
  the arc-5 cold review identified, so the frame function is a function of the ordered frame,
  and with `n2FrameTwist_reverse` of the *unordered* frame — a point of `ℝP²`. Both fall out
  of one new engine, `n2FrameTwist_eq_of_base_eq` (same base points ⟹ same parameter), plus
  `diagonal_conj_diagFamily`. `Necessity/FrameConstancy.lean`; no `2π` argument anywhere.
* **(b)/(c) BANKED — and the orders' own suggested reordering is REFUTED.** The orders said to
  try continuity first and take boundedness free from compactness of `U(2)`. Compactness *is*
  in-tree (`Vendor/Wigner/UnitaryCompact.lean`, vendored, axiom-clean), so that implication
  holds — but it runs the wrong way. Continuity needs a principal branch, which needs
  `sM < π`, which needs the bound. So the article's order (b then c) is forced. Three distinct
  routes to continuity were examined and all funnel through boundedness; the two that bypass
  it fail for stated reasons (a discontinuous section of a covering need not equal a
  continuous lift, even over the now-simply-connected `S²`; two incommensurable `δ`s pin the
  value but not continuity). Recorded per row in `STATEMENT-MANIFEST.md` rows 32/33.
* ★★ **The gate is one input, and it is NOT missing from Mathlib.** Both (b) and (c) reduce to
  **operator-norm continuity of `a ↦ Θ_a` in the matrix argument** — the dependency this
  project banked earlier as the real row's "final dependency … the functional calculus's
  continuity in the matrix argument". Mathlib has it:
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean` supplies
  `continuousOn_cfc` (`cfc f` continuous on elements whose spectrum lies in a fixed compact
  set), with `ContinuousAt.cfc` and `Filter.Tendsto.cfc` alongside; and this tree's carrier
  already goes through `HermitianMat.cfc` (`Hermitian/Twist.lean`). So the remainder is
  **ABSENT with a named route, never BLOCKED** — S2 gives `L_a` pointwise, finite dimension
  upgrades pointwise to operator norm, and `continuousOn_cfc` gives `a ↦ Q_{a^{-1/2}}`. Cost
  is the contradiction argument's plumbing, not a missing theorem. **This is the fourth time
  in two arcs that "Mathlib lacks X" was wrong: grep the library before writing it.**

**6.3 abstract tier — DONE, and it was much cheaper than rung 5.1 priced it.** Two rows moved:
* **`lem:homog`(ii) proved at abstract order-unit-space generality** —
  `SequentialProductOn.sp_smul_left`, carrying S1–S7 + the article's S2 +
  `OrderUnitSpace.IsArchimedean` as an explicit `Prop`. The full ten-step ladder is now
  abstract (second argument: `sp_natSmul_right`, `sp_divNat_smul_right`, `sp_ratSmul_right`,
  `sp_smul_right_of_unitInterval` ← Archimedean consumed here; first argument:
  `sp_comm_natSmul`, `sp_comm_ratSmul_self`, `sp_comm_ratOneSmul`, `sp_ratOneSmul_left`,
  `sp_smulOne_left` ← the single S2 use, `sp_comm_smulOne`, `sp_smul_left`), in
  `SequentialProduct.lean`. The concrete versions are untouched. ★ **Rung 5.1's obstruction
  was correctly diagnosed but wrongly priced.** It was right that the ε-squeeze *is* the
  Archimedean property and that the class carries only order-unit boundedness. It was wrong to
  conclude the work was large: with Archimedean supplied as a `Prop`, the ladder ports
  essentially verbatim, because it never used anything about matrices. Cost was three missing
  order lemmas (`sub_le_sub_right'`, `sub_le_sub_left'`, `le_of_sub_nonpos` — Mathlib's need
  ordered-group instances this class does not provide) and one Mathlib import.
* **`lem:cone-ext` FORMALIZED, with a norm-free admissibility condition** (the row still carries S2, which is a norm-topology hypothesis — ARC-6 review correction; do not call the row "norm-free") — `sp_coneNorm_indep` (independence of the
  normalization), `sp_coneNorm_smul` (positive homogeneity), `sp_coneNorm_eq_of_isEffect`
  (agreement on effects), `exists_isConeNorm` (existence). ★ **Better than the article's
  route**: the article's admissibility is `μ ≥ ‖v‖` and it derives `v ≤ μ𝟙` from that "in an
  order unit space", which presupposes the carrier's norm *is* the order-unit norm — a fact
  this class does not carry, and the reason arc-5 had to hedge `lem:span`'s abstract claim.
  `IsConeNorm v μ := 0 < μ ∧ IsEffect (μ⁻¹ • v)` states the same requirement without the norm,
  and the class's own order-unit boundedness supplies an admissible `μ`, so no norm hypothesis
  is needed at all. Self-caught: `sp_coneNorm_smul` had **inert** `IsArchimedean` and S2
  hypotheses; both were removed before landing (the inert-hypothesis test, applied to my own
  work rather than waiting for the reviewer to apply it).

**6.4 caveat sweep — the head item's ingredient landed.** `Necessity.cfc_transpose` /
`transposeMap_cfc`: **transposition commutes with the real functional calculus**, which
`ComplexRowUnconditional.lean` recorded as the *one* thing `cor:selectors`(iii) was missing,
with the sentence "Nothing in this tree has it" (now retired). Built exactly as that file's
recipe predicted: entrywise conjugation is an ℝ-star-algebra hom of `Matrix n n ℂ`
(`conjMatStarAlg`, from `AlgHom.mapMatrix Complex.conjAe.toAlgHom` plus `map_star'`), so
`StarAlgHomClass.map_cfc` applies; and `Aᵀ = conj A` for Hermitian `A` converts it. Clause
(iii) now needs assembly only, and the assembly is checked on paper:
`twistFactor (aᵀ) (-t) = conj (twistFactor a t)` because `cos` is even and `sin` is odd, so
`transposeMap (a ∘_t b) = (transposeMap a) ∘_{-t} (transposeMap b)`, and the `∃!` closes it as
in clause (ii).

**Coverage after 6.3/6.4: 8 FORMALIZED / 19 PARTIAL / 9 ABSENT** (`lem:cone-ext` is the new
row; `lem:homomorphism` moved ABSENT → PARTIAL earlier in the arc). Gates green at every
commit: 3106 jobs, census 149, custom axioms exactly `[]`.

**6.5 ℍ row — NOT ATTEMPTED, but PRICED, and this is the arc's one genuine BLOCKED.** Given
this arc's record (five false absence claims, four wrong "Mathlib lacks X"), the stated blocker
was checked at source rather than inherited. Result: **it holds, and for a stronger reason than
recorded.** Mathlib *does* have quaternions (`Quaternion`, `Mathlib/Algebra/Quaternion.lean`),
so that was never the obstacle. The obstacle is that the tree's field-general `Gen` layer is
written for `RCLike 𝕜`, and **ℍ can never be `RCLike`** — the class extends
`DenselyNormedField`, hence *commutative*, and its `re_add_im_ax` demands a **two**-dimensional
real decomposition `z = re z + (im z)·I`, while ℍ is noncommutative and four-dimensional. That
is an impossibility, not an absent instance. ★ **But the ARC-6 cold review corrected the
conclusion I drew from it:** the row stays **PARTIAL**, because what this blocks is the `Gen`
*layer*'s reuse at ℍ, not the row, which remains reachable by the embedding route — and because
"BLOCKED" is a fourth status word outside the FORMALIZED/PARTIAL/ABSENT taxonomy the coverage
count depends on, and row 32 already forbids that vocabulary ("ABSENT-with-a-named-route, never
BLOCKED"). Keep status words inside the taxonomy; put the obstruction in prose. Consequence: the `Gen` layer
cannot be reused at ℍ at any price, and the route is forced to be
`H_n(ℍ) ↪ H_{2n}(ℂ)` as the fixed points of a conjugate-linear involution — the quaternionic
structure carried by the involution instead of by a scalar field, exactly as the orders said.

### ★ ARC-6 REVIEW OUTCOME — attempt 1 failed, attempt 2 delivered (2 of 3), and the findings are applied

**Attempt 1 failed; attempt 2 SUCCEEDED, 2 reviewers of 3. This section was itself wrong for
several hours and is corrected here — see the note at the end, which is the most useful thing
in it.**

*Attempt 1 — failed.* One reviewer against frozen tag `paperA-arc6-review` (`9c2aa88`) with a
brief covering the whole arc. Asked five times, including "partial findings now beat complete
findings later". Nothing returned.

*Attempt 2 — succeeded.* Diagnosing attempt 1 as too broad a brief, **three** reviewers were
spawned in parallel, each narrowly scoped to finish inside ~25 tool calls: the abstract tier's
two FORMALIZED claims; the rank-two lane and the phase sign; the retractions plus documentation
consistency. **Two of the three delivered substantive reports; the rank-two reviewer went idle
without reporting.** So the narrowing worked, and the fix was real rather than cosmetic. One
reviewer also reported *why* its earlier attempts vanished: it had written them as plain text
instead of calling `SendMessage`. That is a mechanism worth knowing — a subagent's prose is not
delivered.

★★ **THE REVIEWS EARNED THEIR KEEP, AND CAUGHT THINGS SELF-REVIEW DID NOT.** Findings, all
verified at source before applying:

| Finding | Disposition |
| --- | --- |
| **`cfc_transpose`'s BOTH hypotheses are inert** — outside its domain `cfc` is junk-valued at `0` and degrades on both sides together, since `spectrum ℝ Aᵀ = spectrum ℝ A`. The reviewer supplied a compiled hypothesis-free proof. | **ADOPTED.** `spectrum_transpose` + `cfc_transpose_unconditional` are in the tree; `transposeMap_cfc` is unconditional too. **Third inert hypothesis this arc**, and the first found by someone other than me. |
| **`IsArchimedean` ⟺ the textbook ℕ-form** (Alfsen–Shultz / Paulsen–Tomforde), proved in both directions, unprompted. | **ADOPTED** as `OrderUnitSpace.arch_iff` (+ `IsArchNat`). This makes the "part of the definition, not a located hypothesis" defense of both FORMALIZED labels *machine-checked* instead of asserted. I would not have thought to ask for it. |
| "The *statement* of `sp_smul_left` never mentions the norm" — **FALSE**: `hS2` unfolds to `ContinuousOn` in the carried norm topology. | **RETRACTED.** Never call `lem:homog`(ii) "norm-free". The label survives on a different argument (S2 *is* the article's norm-continuity axiom, and `ouNorm_le_norm` makes the topologies agree on the carrier). |
| "`IsConeNorm` states the same requirement without the norm" — **FALSE**: strictly *weaker*, hence a *larger* admissible set, hence the independence clause is *stronger* than the article's. | **CORRECTED** in the docstring and the manifest row. |
| "covers every EJA" — **not machine-checked**: there is no Jordan/EJA class anywhere in the tree. | **CORRECTED** to "every EJA instantiates it by standard mathematics this tree does not itself formalize". |
| `mthm:master` listed under "no Lean counterpart" while the manifest rates it PARTIAL. | **RE-SCOPED** to the `master_chain` *declaration* — the same scope-loss the list corrects two bullets down. |
| The ORDERS block still ordered "`lem:homog`(i) needs a positive-linear-extension construction: attempt it, bank on resistance", falsified by my own retraction. | **FIXED** at both sites. |
| Three stale present-tense counts (`LEDGER` ×2, `THEOREM-MAP` ×1), one inside the SSOT block and one phrased as a standing rule. | **FIXED**; historical figures now dated. |
| `thm:quaternionic` called "genuinely BLOCKED, not ABSENT" while row 32 forbids that vocabulary, and BLOCKED is a fourth term outside the taxonomy the count depends on. Also: the RCLike argument blocks the `Gen` **layer**, not the row. | **CORRECTED**; row stays PARTIAL, obstruction described in prose. |
| `sp_coneNorm_smul`'s `IsConeNorm` hypothesis used only for `μ ≠ 0` — over-strong. | **WEAKENED** to `μ ≠ 0`. |

Both reviewers independently **CONFIRMED** the two retractions (`lem:homomorphism` wrongly
ABSENT; `lem:homog`(i) is `seqLeftMul`), that `multiParameter_eq_exp` is a genuine theorem with
no located hypothesis, that `conjMatStarAlg` is a real ℝ-star-algebra hom, that the
cos-even/sin-odd reasoning behind the banked `cor:selectors`(iii) assembly holds, that `spCone`'s
`else 0` branch is unreachable, that the coverage count is 8/19/9 (counted independently), and
that **both FORMALIZED labels stand**. One added a fact I did not have: the **real** lane also
discharges the Jordan hypothesis from S2 (`thetaPreservesJordanR_of_S2`).

★ **One nuance to preserve verbatim:** the tree contains **no `HasDerivAt`/`fderiv` statement
about `Θ` or `χ` anywhere** — the `exp`-generator route bypasses differentiation entirely. The
retracted sentence's *inference* was false, which is what mattered; but **never upgrade §3c to
"Lean differentiates Θ"**.

★★ **The lesson I got wrong, recorded because it is the most transferable thing here.** I wrote
"the review channel failed on BOTH attempts … this is a tooling failure, not a scoping failure"
— and then two reports arrived. **Both halves were wrong: attempt 2 worked, and the cause was
scoping (plus one reviewer not calling `SendMessage`).** I declared a systemic failure from two
data points while the second was still running, which is the same impatience that produces
premature absence claims. **A silent channel is not a dead channel; "no report yet" is not "no
report".** Wait, or say "not yet returned" — never "failed".

**Lint sweep over the five files this arc touched.** One warning was mine and is fixed
(`transpose_eq_conj_of_isHermitian` carried unused section variables; now `omit`ted). Two are
**pre-existing and left alone** rather than drive-by fixed, but recorded here so they are not
lost: `SequentialProduct.lean` `sp_sub_right` has an unused hypothesis `hle` — a small inert
hypothesis in the abstract derived layer, predating this arc — and `OrderUnitSpace.lean:73` has
two unused `simp` arguments. Neither is mine to fix silently; both are cheap when someone is in
those files.

★★ **The inert-hypothesis test has a STRONGER form, and it should be the default.** Instead of
trying to prove the conclusion without the hypothesis and reporting failure, **try to disprove
the hypothesis-free statement.** A compiled counterexample certifies the hypothesis is
load-bearing; a failed proof search certifies nothing. Demonstrated on
`abs_le_of_phase_near_one`: at `δ = 0` the premise ranges over `0 ≤ x ≤ 0` only, so it holds for
*every* `t`, while Lean's `π/(3*0) = 0` forces `|t| ≤ 0` — and `t = 1` refutes it. `hδ` is
therefore *proved* necessary. Use this form on every hypothesis whose necessity matters; the
weaker form is what left `cfc_transpose`'s two inert hypotheses standing until a reviewer
found them.

**Which hypotheses actually got the strong test — recorded, because the distinction is what let
`cfc_transpose` slip.** STRONG (disproved without it, hence *certified* load-bearing):
`abs_le_of_phase_near_one`'s `hδ`. FOUND SPURIOUS and removed: `n2FrameTwist_eq_of_base_eq`'s
`hs` (automatically true for every `m : Fin 2`, so it was an obligation no caller ever needed
to discharge). WEAK ONLY (reasoned load-bearing, not certified): `n2Readout_eq`'s `hb`/`hx`
and `adU_conj_twistSeq`'s `hU`/`hU'`. The obstacle for those four is real rather than laziness:
refuting them needs a *bespoke* product that agrees with the twist product on effects and
differs off them — for the twist product itself `sp = twistSeq` everywhere, so it cannot witness
the failure. On paper `adU_conj_twistSeq` does fail at `U = 2·1` (both sides scale by different
powers), which is the sketch to formalize if these ever need certifying.

**On the limits of the WEAK inert-hypothesis test, stated so the record is not overclaimed.** The
test has real teeth *when the conclusion is actually provable without the hypothesis*: that is
how `rhoChi_eq_smul_generator`'s `i ≠ j` was caught this arc (proof found, theorem strengthened)
and how `sp_coneNorm_smul`'s `IsArchimedean`/S2 were caught and removed. But a *failure* to find
such a proof is not a certificate of load-bearingness — Lean cannot certify that no proof
exists. For the abstract ladder I have only a mathematical argument that `IsArchimedean` is
load-bearing (it is the sole bridge from ℚ-homogeneity to ℝ-homogeneity; delete it and the
ε-squeeze has no replacement), plus positive controls confirming every new theorem does go
through with its stated hypotheses. **Do not read "inert test run" as "hypothesis proved
necessary".**

**Self-review is structurally weaker than cold review, and this arc is the proof — in both
directions.** Self-probing did real work: it caught `rhoChi_eq_smul_generator`'s inert
hypothesis, two doc rows still asserting superseded claims, and the one failure mode that would
have voided the FORMALIZED labels (`IsArchimedean` inhabited). But the reviewers produced two
things it structurally could not: a **compiled refutation** of hypotheses I believed were
load-bearing (`cfc_transpose`), and a **theorem I did not know to want** (`arch_iff`). An author
does not probe the claims he is confident in.

**REVIEW DEBT CARRIED FORWARD — this is the actionable remainder.** The **rank-two lane was
never reviewed**: its reviewer went idle without reporting, so `n2Readout_eq` (including the
phase sign), `n2FrameTwist_mul_diagonal`, `n2FrameTwist_eq_of_base_eq`, and
`abs_le_of_phase_near_one` carry **only my own probes**. I checked the sign three independent
ways (crown probe `n2FrameTwist (twistProductOn t) U = t`; `basePt x = diag(e^{−x},1)`;
log-ratio `−x`) and non-vacuity at `diag(i,1)`, the phase sign now has an **independent
derivation in the tree** (`readout_direct`: the same formula for the twist product at the standard
frame, derived straight from `twistSeq_diagFamily_entry` and nothing else — two routes, one
formula, so a refactor that flips either chain breaks the agreement), the `π/(3δ)` constant is now **derived as sharp** — the premise says
`cos(tx) > 1/2`, which as `x` sweeps `[0,δ]` in the principal branch forces `|t|δ < π/3`, so the
constant is right and the inequality is **strict**; `abs_lt_of_phase_near_one` now states that and
`abs_le_of_phase_near_one` is its corollary — and the constant is also (`normSq (exp(iπ/3) − 1) = 1` exactly, and at `t = π/(3δ)` the phase reaches
distance 1 at `x = δ` — so the strict hypothesis excludes that `t` and the `≤` conclusion is a
valid, if not sharp, bound). What remains unreviewed there is the *derivation as a whole*, not
any one constant. **The next
arc should cold-review the rank-two block first.** The abstract tier and the retractions are
reviewed and their findings applied; do not re-spend effort there.

**Process note for the next arc, corrected by what actually happened.** A narrowly-scoped
reviewer works; a whole-arc brief does not. And one reviewer's reports vanished because it
wrote them as **plain text instead of calling `SendMessage`** — a subagent's prose is not
delivered, so say so in the brief. Do ask for an early interim report, but **do not conclude
failure from silence**: two of these reviewers were still working when I wrote them off.

**Review protocol (binding).** Three isolated cold reviews: after 6.1(f), after 6.3, and
at end of arc. Each reviewer reads the diffs at source and COMPILES probes
(inert-hypothesis tests; strongest-available probe on any new map — arc-5's was
`n2FrameTwist (twistProductOn t) U = t`); ≤3 fix loops per review; every finding verified
at source before applying OR rejecting (reviewers have been confidently wrong in both
directions, and so have I — twice each, last arc). After every fix round, one diff-audit
pass: read the sentence after every inserted clause, grep each corrected file for the
claim being corrected, and rewrite EVERY summary instance (the fix-the-row rule; six
instances on record). Sub-agents for stuck proofs (repair/golf) are authorized; their
output goes through the same at-source verification.

**Gates per commit — all of them, every commit:** `lake build` green from
`/Users/ehrlich/repos/research/twist-normal-form-lean` (cwd matters: elsewhere `lake env
lean` resolves the wrong toolchain); `AxiomAudit.lean` census PASS with custom axioms
exactly `[]`; `#print axioms` on each new named result = `[propext, Classical.choice,
Quot.sound]`; `THEOREM-MAP.md` and `STATEMENT-MANIFEST.md` row updates in the SAME commit
as the proof they describe; single-sentence commit messages.

**Wall protocol:** a target that resists three genuinely distinct strategies gets its
measured remainder banked HERE — a named missing lemma or a named obstruction, ABSENT vs
BLOCKED vocabulary per the manifest — and the ladder continues. Absence claims carry
their scope and date, always.

**Hard boundaries:** all commits LOCAL (the repo is public; never push, never `sync.sh`);
`main.tex`/`supplementary.tex` and everything outward-facing untouched (frozen tags
inviolate; the supplementary APPLICATION and the Mathlib PR decision stay Bryan-gated);
never claim "fully formalized"; a row counts FORMALIZED only with no located hypothesis
at the article's own generality. Field hazards from arc-5, pre-paid so they cost zero
time now: `fin_cases` produces atoms `rw` cannot match — use `by decide` case
enumeration; one-sided rewrites need `conv_lhs`; the guardrail blocks `git checkout --` —
use `git stash push -- <abs path>`; destructive ops take absolute paths only.

**Expected landing, for calibration only:** a full-yield arc ends in the high teens
FORMALIZED of 36. The number is not the deliverable; the per-row honesty is.

---

## ARC-5 ORDERS (2026-08-08, Fable design pass — the coverage ladder). EXECUTED through 5.3 + cold review 2026-08-08; 5.4/5.5 carried into ARC-6 above; superseded as campaign SSOT.

**The question that produced this arc:** Bryan asked what it would take to reach 36/36 of
the paper's numbered results in Lean, and what the concerns are with setting exactly that
goal.

**Decision record — literal 36/36 REJECTED as the goal (do not re-litigate).** Verified at
source: the final ticks are FIVE separate research-scale programs, four of them other
people's mathematics: `thm:vdw1` (van de Wetering's Jordan representation theorem — the
paper's central import); **JvNW hiding inside `mthm:master`/`mthm:omnibus`** (both are
stated over an abstract simple EJA, so "one theorem at article generality" needs the
Jordan–von Neumann–Wigner classification — the campaign's pre-registered PERMANENT import,
see the target restated above: "Lean core + at most JvNW as disclosed import");
`prop:bridge` (cited external); `prop:theta` at vIR's JB-algebra generality; and the Albert
row's M2 machinery (unscoped since the 08-04 memo — the octonions themselves are NOT the
wall, see the H₃(𝕆) correction below). **Interior honest ceiling ≈ 26–28 of 36.** A 36/36
chased through located hypotheses or disclosed axioms would trade the census (`custom
axioms exactly []`) — the asset's entire distinguishing value — for a number. The count is
a LaTeX artifact (43 environments minus 7 remarks); the census and THEOREM-MAP are the
product.

**EJA-first also REJECTED for this arc.** The abstract-generality gaps an EJA layer closes
are supporting-lemma rows, not headline rows; several "abstract" rows (`lem:span`,
`lem:normality`, `lem:cone-ext`) are stated at ORDER-UNIT-SPACE generality, which the
skeleton already carries — no EJA needed. The EJA/Peirce/symmetric-cone layer remains what
the 07-19 scouting memo said: the high-leverage **Mathlib-upstream** project, run as its
own initiative later, never welded to this paper's count (it also drags toward JvNW).

**THE LADDER (execute in order; on a genuine wall, bank the measured remainder HERE and
continue with the next item — the ARC-4 rule):**

* **5.0 Freeze the denominator — DONE 2026-08-08.** `STATEMENT-MANIFEST.md` exists: all 36
  labels, one-line statements, per-row status and rung target, pinned to `main.tex` blob
  **`205fdf5a`** — which is *byte-identical* at frozen tag `paperA-jpa-submitted` (blog
  `035c337`) and in today's working copy, so the manifest pins one object, not two. The
  36 = 43 environments − 7 remarks derivation is written out and reproducible from a single
  grep. Coverage claims now cite the manifest, so a renumbering can't silently move the
  target. It also computes the ceiling arithmetic: 6 rows are outside this arc by design
  (2 cited external, 2 needing JvNW, 1 needing vIR at JB generality, 1 needing Albert M2)
  ⟹ interior ceiling **30**, realistic **26–28**. No manuscript edit. Side finding, fixed
  in the same pass: the staged supplementary rewrite (blog
  `research/paperA-supplementary-rewrite-draft.md`) still asserted "the octonions do not
  exist in any prover" in two places and "exists in no other proof assistant" for real
  Wigner — the retracted absence claims, sitting in text staged to enter the manuscript.
  Rewritten with their scope attached ("absent from Mathlib, checked 2026-08-08") and the
  ℍ/𝕆 rows changed from "cannot be" to "not built; not known to be out of reach".
* **5.1 Small-lemma tier — PARTLY DONE 2026-08-08, and the rung was mis-billed.** Landed:
  `lem:span`'s two load-bearing clauses at **full abstract order-unit generality**
  (`OrderUnitSpace.span_isEffect_eq_top`, `linearMap_eq_of_eq_on_effects`) — proved from
  order-unit boundedness alone, avoiding the article's norm route, which this interface
  cannot express; and `cor:selectors` **clause (ii)** at the article's own generality
  (`Necessity.selector_traceSymm`: trace-form symmetry makes `-t` a second representing
  parameter, so the classification's `∃!` forces `t = 0`). Also, and for free: the audit
  that writing 5.0 forced found **three rows carried as ABSENT that were already covered** —
  `lem:aone` was FORMALIZED all along (`SequentialProduct.sp_unit_right`, abstract, the
  article's own S1/S3/S4/S6 route), `lem:span` and `prop:pseudo-transfer` were PARTIAL. The
  coverage table drifts in *both* directions; every row now names a declaration or says
  ABSENT.
  **★ The mis-billing, banked: "machinery in hand" is false for the abstract sub-tier.**
  `lem:homog`(ii) and `lem:cone-ext` are stated by the article at EJA generality, so the
  concrete-carrier proofs cannot close them — and the concrete proof runs through
  `sp_smul_of_mem_unitInterval`, whose last step is an ε-squeeze that **is the Archimedean
  property**, which `OrderUnitSpace` does not carry (its `archimedean` field is boundedness
  only). Generalizing is therefore not a variable-block change; it needs Archimedean supplied
  as an explicit `Prop` (legitimate — it is part of the definition of the article's "order
  unit space", not a stand-in for a cited result) threaded through the six-step ladder, and
  `lem:homog`(i) *additionally* needs a positive-linear-extension construction that does not
  exist. Full recipe in `THEOREM-MAP.md` §3b. Not attempted this arc: `lem:normality`,
  `lem:orientation`, `lem:frame-fix` general statement, `cor:selectors` clauses (i)/(iii)
  (clause (iii) is blocked on exactly one absent lemma, `(cfc f a)ᵀ = cfc f (aᵀ)`, recipe
  recorded in `ComplexRowUnconditional.lean`).
* **5.2 Caveat + hygiene closure — DONE 2026-08-08, with one order corrected.**
  (a) **DONE.** `AdjAxis` non-vacuity is now a theorem (`Necessity.adjAxis_not_total`, witness
  `not_adjAxis_one_house`): the Householder reflection in the all-ones direction has every
  off-diagonal entry `-2/N`, so it fixes no axis. The caveat that said this was "asserted in a
  docstring but is not itself a theorem" is retired.
  (b) **RELABELLED after the cold review: this was an UNDERCOUNTED ROW, not new mathematics.**
  `lem:adjacent` is FORMALIZED, but its honest witness is **`frameTwistConst`**, already in the
  tree at tag `paperA-arc4`, which proves `frameTwist` constant across *all* frames — so the
  article's adjacent-frame case follows for any relation whatsoever. The reviewer compiled the
  conclusion of `frameTwist_eq_of_adjBlock` with the hypothesis **deleted**, and again with an
  arbitrary relation in its place. So this row belongs beside `lem:aone` (carried as unproved
  while a proof existed), *not* beside `cor:selectors`(ii) or the rank-two extraction. The
  commit message ("Close lem:adjacent at the article's own frame adjacency") overstates;
  `THEOREM-MAP.md` governs and now says so. `AdjBlock`, `adjAxis_of_adjBlock` and
  `frameTwist_eq_of_adjBlock` stay as documentation of the article's relation in the tree's
  coordinates; they add no provable content.
  ★ **The fidelity note written to justify the row was FALSE.** It said "`AdjBlock` is a
  *superset* of the article's relation, which makes the theorem stronger". Refuted by compiled
  counterexample: the 3-cycle permutation of the standard basis of `ℂ³` has *literally the
  standard frame* as its Jordan frame, yet fails `AdjBlock` — because `AdjBlock` forbids
  relabelling the shared atoms while the article's frames are **unordered** sets of atoms
  (verified at source, `main.tex`:1269–1273). `AdjBlock` is a relation on *labelled* frames,
  neither a superset nor a subset. Never repeat the superset claim.
  `lem:frame-connectivity` remains open and that reason stands: `AdjBlock` is strictly finer
  than `AdjAxis`, so connectivity for it is strictly stronger and needs a Givens/Jacobi
  factorization into rank-two block rotations.
  (c) **DONE.** `THEOREM-MAP.md` §3b now carries rows for `lem:homog`, `lem:cone-ext`,
  `lem:frame-fix`, and `prop:bridge`, so the map covers all 36 like the manifest does.
* **5.3 THE BOULDER — the rank-two classification map. THE INPUT NOW EXISTS (2026-08-08);
  the assembly does not.** Landed: `Necessity.n2FrameTwist : (P : SequentialProductOn
  (H₂(ℂ))) → P.FirstArgContinuous → U(2) → ℝ`, the frame function extracted from an
  **arbitrary** product, plus `n2_sp_eq_twistSeq_frame` — at every ordered frame `U` and
  every nonpositive `r`, `P.sp a b = twistSeq (n2FrameTwist P hS2 U) a b` for
  `a = Ad_U (diagFamily r)` and all effects `b`. Lean-core closure. In
  `Necessity/FrameConstancy.lean`, section `RankTwoExtraction`.
  **★ The pre-registered wall did not bite, and the reason is a corrected diagnosis.** The
  route was billed as needing the frame-function extraction built from scratch because "the
  `N ≥ 3` machinery cannot be reused (`StabilizerCoupling` carries `rank_ge : 3 ≤ n`)". In
  fact only 15 of 76 `Necessity/` modules carry a rank-3 hypothesis and **none of the needed
  pieces is among them**: `prop:theta` on the carrier is rank-free (correctly — unital order
  automorphisms of `H₂(ℂ)` are `O(3)` on the Bloch ball, still `{Ad_U} ∪ {Ad_U∘ᵗ}`; the
  dimension-3 requirement in this area is *Uhlhorn's*, whose hypothesis is weaker), and so
  are `dChi_kills_corner`, `conjProduct`, `sp_eq_twistSeq_transport`,
  `sp_eq_twistSeq_diagFamily`, `tval_antisymm`. The genuinely rank-3-gated step is
  `tvalLm_of_coupling` — the cross-frame constancy, which at rank two is *false*, which is
  exactly why the moduli space is `C(ℝP²,ℝ)` and not `ℝ`.
  **★ And the "lifting step" was never missing.** THEOREM-MAP said Lean "*assumes* `angle` is
  linear … the universal-cover lift `ℝ² → SO(2)` ⟹ linear functional is supplied by the
  paper." But `Necessity.tvalLm` is a **constructed** `(n → ℝ) →ₗ[ℝ] ℝ` with no rank
  hypothesis: the linear functional `n2_necessity` takes as a parameter was already in the
  tree, unused at rank two. The replacement argument is exact and `2π`-free — a linear
  functional on `ℝ²` vanishing on `⟨(1,1)⟩` factors through `r ↦ r 0 − r 1`.
  **Still open, exactly:** boundedness (`lem:n2-bounded`), continuity (`lem:n2-continuity`)
  and frame-reversal invariance/`ℝP²`-descent (`lem:n2-descent`) **of that function**, plus
  `prop:n2-sufficiency` for the reverse direction, before `cor:qubit-classification`
  assembles. Those three are now statements about a function that exists, which they were
  not this morning.
  ★ **Corrected by the cold review: "presentational only" was wrong.** Two real gaps remain in
  `prop:n2-necessity` — `U(2) → S²` is a quotient by the diagonal-phase fibre and nothing proves
  `n2FrameTwist` constant on those fibres, so Lean does not yet have a function of the *ordered
  frame*; and the equivalence between the article's `Θ_a|_{W_n}` form and Lean's product-level
  identity is the route, not a proved statement.
  **Two theorems adopted from the review, both now in the tree:** `n2_every_posDef_effect` (the
  `(U, r)` form covers **every invertible effect**, via the spectral theorem — the section proved
  this but never said it) and ★ **`n2FrameTwist_reverse`**, the **frame-reversal clause of
  `lem:n2-descent` for an arbitrary product**: `n2FrameTwist (U * swapU) = n2FrameTwist U`, so
  the frame function is order-blind and is a function of the *unordered* frame. That clause had
  been banked as remaining boulder work and was mispriced — it is ~35 lines given what landed.
  Open rank-two work is now **boundedness and continuity** of the frame function, plus
  `prop:n2-sufficiency`.
  **Lesson banked:** the old entry inferred "the classification map does not exist in Lean at
  all" from `grep -c SequentialProductOn RadicalRelativity/RankTwo/*.lean` → 0. The grep was
  accurate; the inference was wrong, because the map got built in `Necessity/`. Scoping an
  absence claim to a *directory* is the same error as scoping one to a library — the third
  instance of this failure in a week.
* **5.4 The differential trio.** `lem:homomorphism` (differentiate Θ in the matrix
  argument; prove `dχAdd` IS its derivative — the development currently *begins after*
  this transition), `lem:coalescence` identification, `prop:stabilizers` construction.
  Wall: Fréchet machinery on the carrier (a normed space, so Mathlib `fderiv` applies).
  Fallback: pointwise-derivative version, banked.
* **5.5 STRETCH — the ℍ row.** Route per the 08-06 correction: `H_n(ℍ) ↪ H_{2n}(ℂ)` as
  fixed points of a conjugate-linear involution (ℍ is not `RCLike`; that, not missing
  quaternions, is the blocker). Quaternionic Wigner may fall to the RealWigner rank-one
  technique. This is plausibly its own arc; any progress banks.

**Constraints (welded, not advisory):** a result counts FORMALIZED only with no located
hypothesis standing in for a cited result, at the article's own generality; custom axioms
stay exactly `[]` and the census+manifest run green at every commit; the THEOREM-MAP row
updates in the same commit as each proof; never write "fully formalized"; all commits
LOCAL (public repo, push Bryan-gated, NEVER sync.sh); manuscript, `upstream/` submission,
and everything outward untouched; T1/T2 PARKED; JMP RESERVED; frozen tags never touched.
End of arc: ONE isolated cold review of the arc's diffs against a frozen tag (ARC-4
pattern — it earned its keep), then compact this ledger's arc narrative.

**Expected movement if no wall bites:** 5/36 → ~14 after 5.1–5.2 → ~21 after 5.3 → ~24
after 5.4; the stretch adds ~1 plus a first-party quaternionic Wigner. Unlike ARC-4 (six
bounded refactors, one hour), 5.3 and 5.4 are NEW MATHEMATICS in Lean — expect walls, use
the fallbacks, report the remainder honestly.

**ACTUAL after 5.0–5.3 (2026-08-08): 5/36 → 7/36 formalized, 19 partial, 10 absent.** Short
of the ~14 projection, and the reason is a repricing, not a shortfall in effort: the 5.1
projection assumed the abstract sub-tier was mechanical, and it is not (the Archimedean
finding above). Two rows moved to FORMALIZED (`lem:aone`, by audit; `lem:adjacent`, by
proof), one row gained a clause at article generality (`cor:selectors`(ii)), one row was
upgraded from concrete to fully abstract (`lem:span`'s two load-bearing clauses), two rows
were corrected upward from ABSENT to PARTIAL, and two caveats were retired
(`AdjAxis` non-vacuity; the frame-adjacency mismatch, now narrowed to `lem:frame-connectivity`
alone). Every gate green throughout: `lake build` 3106 jobs, census 149 modules, **custom
axioms exactly `[]`**, every new declaration's closure = the three core axioms.
The count understates 5.3: the rank-two frame function is a new *capability* rather than a
row, and it is the input every remaining rank-two row consumes. Three superseded claims were
corrected on the record in the process (the abstract tier is not mechanical; `AdjBlock` is
finer than `AdjAxis` so connectivity does not follow; the rank-two lifting step was never
missing).

Commits: `6f2442a` (5.0) · `51cfbb9` (coverage corrections) · `287cff3` (selector ii) ·
`4e12d84` (abstract span + AdjAxis non-vacuity) · `88aba62` (article adjacency) · `9248f3d`
(5.2 close + 5.1 repricing) · `5e3e3e5` (5.3 rank-two extraction); blog `650aa12` · `326aedb` ·
`8900e4b` · `168e9a7` · `174e3ff` · `2d2c6cc`.

## ARC-5 COLD REVIEW — RAN, and it earned its keep twice over

One isolated adversarial reviewer, given frozen tag `paperA-arc5-review` @ `5e3e3e5`, read-only,
told to write its own Lean probes and to refute rather than confirm. It compiled six probe files
and re-ran both gates itself. Outcome:

**CONFIRMED, by its own compiled probes, not by reading:**
* `selector_traceSymm` — and it went further than asked: it proved the Lüders product *satisfies*
  trace symmetry (class inhabited), that the selector returns `t = 0` on it, and **that for
  `t ≠ 0` the twist product provably does NOT satisfy trace symmetry** — so the hypothesis is
  genuinely selective. That sharpness check was not in the orders and should have been.
* `adjAxis_not_total`, the abstract `lem:span` proof, `cornerJ2_all`, `n2_tval_eq`, and the
  arithmetic 7 + 19 + 10 = 36 against the manifest row by row.
* ★ **The crown probe on rung 5.3: `n2FrameTwist (twistProductOn t) U = t` for every `U`.** The
  extraction returns the *expected* parameter — no sign error, no factor of two, no frame
  confusion. This is the strongest available confirmation that `n2FrameTwist` is the right map and
  that its hypothesis class is inhabited at `N = 2`.
* `lem:aone` FORMALIZED — it read all nine fields of `SequentialProductCore` to confirm
  `sp a ousUnit = a` is not among them, i.e. genuinely derived rather than restated.

**REFUTED, both by compiled counterexample, both mine, both now corrected above:**
1. `lem:adjacent`'s adjacency hypothesis is **inert** (`frameTwistConst` already gave global
   constancy at the previous tag) — so 5.2(b) was an undercounted row, not new mathematics.
2. The "`AdjBlock` is a superset of the article's relation" fidelity note is **false** (3-cycle
   counterexample; the article's frames are unordered).

**OVERSTATED, corrected:** "full order-unit-space generality" for `lem:span` (the *interface*
extends `NormedAddCommGroup`, so the statement presupposes a norm even though the proof never
touches one); "presentational reason only" for `prop:n2-necessity` (the `U(2) → S²` phase fibre is
a real gap).

**MISPRICED IN THE CHEAP DIRECTION — and it just did the work:** the frame-reversal clause of
`lem:n2-descent` was banked as boulder work; the reviewer proved it for an arbitrary product in
~35 lines. Adopted as `n2FrameTwist_reverse`, with `n2_every_posDef_effect` alongside it.

**Three same-file contradictions found — the project's documented failure mode, and this diff
created them** (a summary cell and a note in the same file that cannot both be true):
`THEOREM-MAP.md`'s rank-two summary still said the extraction "remains" 60 lines below the
correction saying it exists; `LEDGER.md`'s `cor:qubit-classification` cell still said the map was
ABSENT; and `THEOREM-MAP.md` §3 ("no Lean counterpart") still listed `lem:n2-descent` and
`lem:n2-continuity`, which the manifest rates PARTIAL — taken literally the *governing* file
implied 7/17/12 against the manifest's 7/19/10. All three fixed. Plus two lint warnings the
reviewer caught in `adjBlock_one_house_pair`, also fixed.

**Could not check, flagged honestly:** the reviewer had no access to the blog repo, so every
"at the article's own generality" judgement it saw rested on the manifest's paraphrases. It asked
for finding 2 above to be re-checked against `main.tex`:1269 directly — **done, at source, and
the reviewer was right.**

**Rungs 5.4 (differential trio) and 5.5 (ℍ row) NOT STARTED.** They remain as written above.
5.4's `lem:homomorphism` is worth re-checking against the same lesson that just paid off
three times: read what `dChi`/`chiTilde` actually prove before accepting "Lean never
differentiates Θ" — `chiTilde_eq_exp_dChi` exists and is used by `dChi_kills_corner`, so the
exponential/differential relationship is at least partly in the tree already.

---

## ★★ ARC-4 RESULT (2026-08-08) — **the asset is truthful, sharper, and PR-staged. All six items landed.**

Gates at the end of the arc: `lake build` green at **3106 jobs**; `AxiomAudit.lean`
PASS at **149 tracked modules** (== frozen 149-name manifest); **custom axioms exactly
`[]`**; every tracked persisted declaration's closure ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}. All commits LOCAL. Frozen tags: `paperA-arc4-review` @ `7cdf690` (the state
the cold review read) and **`paperA-arc4` @ `53b32ee`** (the arc's final state, after the
review-driven fix below).

Commits: `8727fff` (4.1) · `0d2fec9` (4.2) · `3f89c8f` (4.3) · `7cdf690` (4.4) ·
`f4deb30` (4.6 compaction) · `0e1c366` (4.6 review fix) · `53b32ee` (4.6 review record);
blog `fb65b07` (4.5) · `f1a79b6` · `12e7c24`.

**The tree carries zero `sorry`.** The only two occurrences of the token live inside a
comment block in `Vendor/Misc.lean` (illustrative code for what those declarations should
become once a Mathlib `ConditionallyCompleteLattice` diamond is fixed) — they are not
declarations and reach no proof. Soundness of the tree and *coverage of the article* are
different questions: see the coverage count below.

**4.6 cold review — RAN, and it earned its keep.** One isolated adversarial reviewer, given
the frozen SHA and told to write its own Lean probes. It confirmed the 4.2/4.3 diffs on every
vector it checked — round-tripping both `_ouNorm` rows back to the originals, composing each
converse into its forward theorem, showing `ContinuousOnOu` on `univ` forces genuine global
continuity (so it is not satisfiable by a pathological map), showing the `√(card n)` factor
is *necessary* (`‖1‖ = √2 > 1 = ouNorm 1` on `H_2(ℝ)`) and *optimal*, checking that the
refactored Jordan capstones still prove their pre-refactor statements verbatim, and
exhibiting `O = !![2]` to show the orthogonality hypothesis in `orthConj_one` is
load-bearing rather than a `simp` artifact. **And it found one real defect** — see 4.3.

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

- **"Fully formalized" is FALSE and must never appear in prose.** ★ The counts in this
  ARC-4-era bullet (5 / 17 / 14) are **STALE — current is 8 / 19 / 9**, see
  `STATEMENT-MANIFEST.md`. The *rule* stands; the numbers do not. (Flagged by the ARC-6 cold
  review: the rule is phrased so a reader grepping for it lands on stale figures.) What IS
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

**Coverage of the paper, stated as a count so it is never overstated** — ★ the figures in this
ARC-4-era block (5 / 17 / 14) are **STALE; current is 8 / 19 / 9** per
`STATEMENT-MANIFEST.md`, which is authoritative. Historical figures are retained for
provenance only. Never
write "fully formalized". Itemization: blog `research/paperA-supplementary-rewrite-draft.md`
§3; per-statement evidence: `THEOREM-MAP.md`, which governs.

| Row | Status | Capstone |
| --- | --- | --- |
| `H_N(ℂ)`, N ≥ 3 | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `∃! t`, twist on ALL effects; both frame-graph facts DISCHARGED in-tree (cross-coherence + connectivity). Carries only S1-S7 + S2 + `3 ≤ N`. **08-08: also stated with S2 in the ORDER-UNIT norm** (`complex_classification_unconditional_ouNorm`), so the paper's S2 is the literal hypothesis | `Necessity.complex_classification_unconditional` |
| `H_n(ℝ)` | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `a•b = √a·b·√a` on ALL effects, no twist; Jordan hypothesis DISCHARGED by real Kadison proved in-tree, now stated as the full **classification** (`orderAutoR_eq_orthConj`, exact — converse packaged). **08-08: also stated with S2 in the ORDER-UNIT norm** (`real_classification_ouNorm`) | `Necessity.real_classification` |
| `H_n(ℍ)` | **FOUNDATION COMPLETE + `Q_{√a}` restricts** (carrier, order-unit, unital Jordan subalgebra, positivity, cfc-closure, `quatQuadRepEquiv`); **NOT a short lane — see the carrier-genericity finding in `LEDGER-ARCHIVE-M1-M7.md`** | `QuatCarrier`, `quatQuadRepEquiv` |
| `H₃(𝕆)` | **ABSENT, not blocked** (row corrected 08-08 — see below). Octonions are BUILT and sorry-free in the sibling project `~/repos/research/lean/`, same toolchain; the scary Yokota/triality import was re-scoped to an elementary argument by `ALBERT-KERNEL-MEMO.md` on 08-04, and **its one computational input `nucleus(𝕆) = ℝ` is now PROVED** (08-08). Remaining: the model, (I)/(II), and M2-for-Albert (unscoped) | `lean/…/Octonions.lean`, `Octonion.nucleus_real` (both out-of-tree) |
| `cor:qubit-classification` | moduli space + one nonconstant element + certified `ℂP¹→ℝP²` descent + separation; **the classification map's INPUT now exists (2026-08-08, see rung 5.3): `Necessity.n2FrameTwist` extracts the frame function from an arbitrary product, `n2FrameTwist_reverse` proves it order-blind. The bijection is still not assembled — boundedness and continuity of that function, plus `prop:n2-sufficiency`, remain** | `RankTwo.tauModuliRP2`, `RankTwo.tauRP2_blochFrame`, `Necessity.n2FrameTwist` |
| `mthm:omnibus` | **carrier + BOTH assembly halves** (sufficiency `prod`, determination `sp_eq_of_prod_eq`); conditional on the SPLITTING (`prop:central`, paper proof) | `SequentialProductOn.prod` |

★★**`H₃(𝕆)` ROW CORRECTED 2026-08-08 — "BLOCKED, octonions exist in no prover" was FALSE.**
Bryan challenged the claim; verified at source. The original check (archive line 104) was
scoped to **pinned Mathlib only** and its conclusion was then written down as a statement
about *every* prover. Both halves need retracting:
* Mathlib octonions: genuinely absent — the four `octonion` grep hits are prose comments.
  But Mathlib **does** have `IsJordan`/`IsCommJordan` (`Algebra/Jordan/Basic.lean`, 237
  lines, Jordan axioms + `L`/`R` commutation lemmas), so "no Jordan-algebra files at all"
  is retracted too.
* **Our own octonions exist and are sorry-free.** `~/repos/research/lean/RadicalRelativity/`
  `Octonions.lean`: 310 lines, 37 declarations, **0 sorries**, toolchain `v4.28.0` — the
  same toolchain this project pins, so it is portable, not a rewrite. Proved: explicit
  Cayley-table `mul`, `one_mul`/`mul_one`, `non_associative` (with witness),
  `left_alternative`, `right_alternative`, `norm_multiplicative`, `mul_eq_zero_iff`,
  `conj_mul` (anti-automorphism), `conj_conj`, `mul_conj`, all three Moufang identities,
  and full bilinearity (`mul_add`/`add_mul`/`smul_mul`/`mul_smul`). Compare
  `ALBERT-KERNEL-MEMO.md` §2's "inputs consumed, in full" — that list is **already met**
  except ingredient (N).
* `lean/…/Albert.lean` also exists (350 lines, 31 declarations) with `h3O` and `jordanMul`,
  but its 3 sorries include `jordan_identity` itself; all three are marked "expository, not
  referenced by any downstream file", so the carrier is scaffolding, not a usable Jordan
  algebra yet.

**Honest work list for the row** (nothing here is a wall; none of it is done):
1. Port `Octonions.lean` in-tree (same toolchain; it would enter the census and the manifest).
2. ~~`nucleus(𝕆) = ℝ` — memo ingredient (N)~~ **DONE 2026-08-08, same session as this
   correction.** `~/repos/research/lean/RadicalRelativity/OctonionNucleus.lean`,
   `Octonion.nucleus_real`, axioms `[propext, Classical.choice, Quot.sound]`, no
   `native_decide`, `lake build` green at 2862 jobs, zero warnings beyond the expected
   `setOption` note. Statement: if `c` associates with every pair then all seven imaginary
   coordinates vanish. Recipe, for whoever ports it: reduce the basis product FIRST
   (`tbl_i_j : e_i * e_j = e_k`, each by `ext m; fin_cases m <;> simp [mul, basisVec]`),
   then read off coordinates, then `simp only [mul, basisVec, Fin.isValue]` followed by
   `simp +decide only [...]` per triple — each imaginary coordinate outside the quaternion
   subalgebra falls out as `c.coords m = -c.coords m` and `linarith` finishes. Three
   triples suffice mathematically; all seven are used for margin.
   Two traps that cost most of the time: (a) unfolding `mul` against a symbolic `c` on
   both sides times out `simp`, and `norm_num [Fin.ext_iff]` blows the interpreter stack —
   reduce the basis product before touching coordinates; (b) `fin_cases i` on the goal
   `∀ i ≠ 0, c.coords i = 0` produces an index atom that does NOT match the `c.coords 1`
   in the hypotheses, so `linarith` fails with the winning equation sitting right there —
   state the conclusion as an explicit conjunction over numeral literals instead.
3. Build `H₃(𝕆)`: 27-dim ℝ-module, symmetrized product, frame `E_11,E_22,E_33`, Peirce
   blocks as `F_ij` images; prove the Jordan identity for real (not expository).
4. Identities (I)/(II) in the chosen convention (§4's caveat: re-derive, don't quote), plus
   (P1)/(P2) generically → the unit-slot argument discharges `block_injective` with **no
   Spin(8), no triality, no rank certificate**. Memo estimate: weeks of equational algebra.
5. **The genuinely unscoped part:** the M2 `DiagonalHomSetup` machinery (`Θ`, `dχ`, `ρ` from
   the actual sequential product) specialized to the Albert model. The memo explicitly puts
   this outside its own question and calls it "the heavy remaining Albert work". No estimate
   exists for it. This, not the octonions, is what stands between us and the row.

**Lesson, third occurrence of this exact shape** (see the `feedback-fix-the-row-not-just-the-footnote`
and "grep before claiming the library lacks X" rules): a library-absence check has a SCOPE,
and the scope must travel with the claim. "Absent from pinned Mathlib" became "exists in no
prover" became "BLOCKED", and a memo that superseded it four days earlier sat unread in the
same directory. Status words: use **ABSENT** for "nobody built it", **BLOCKED** only for a
named wall with evidence.

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

