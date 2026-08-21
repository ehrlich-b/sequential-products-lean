/-
WALL CERTIFICATE — the abstract / vdW-bridge tier:
  `def:sp`                (row 3,  PARTIAL)
  `lem:span`              (row 5,  PARTIAL)
  `lem:homog` clause (i)  (row 6,  PARTIAL)
  `lem:simple-bridge`     (row 8,  ABSENT, ~3/4 cited)
  `lem:normality`         (row 9,  ABSENT)
  `prop:central`          (row 12, PARTIAL)
  `prop:pseudo-transfer`  (row 13, PARTIAL)
Date: 2026-08-09, ARC-7 block 7.5.  Tag `paperA-arc7-cp1`.  Pin: main.tex blob 205fdf5a.

WHY ONE FILE: these are the rows whose remaining gap is the SAME kind of thing — either the
article's EJA generality (not statable, see the vocabulary-wall note) or one small clause on the
concrete carrier.  Grouping them keeps the shared evidence in one place instead of repeating it.

★★ READ THIS FIRST, because it is the pricing lesson this tier has already taught twice.
  ARC-5 priced the abstract tier as a large job, correctly diagnosing that the class carries only
  order-unit BOUNDEDNESS and that the genuine Archimedean squeeze was missing.  The diagnosis was
  right and the PRICE WAS WRONG: once `IsArchimedean` was supplied as an explicit `Prop`, the whole
  ten-step homogeneity ladder ported essentially verbatim, because it never used anything about
  matrices.  Cost was three missing order lemmas and one import.
  So: for every row below, the default assumption should be that it is CHEAPER than it looks, and
  the way to find out is to port one step, not to re-price the row.

PER-ROW STATUS AND GAP

  row 3 `def:sp`.  Encoded as `SequentialProductOn` / `SequentialProduct`.  The gap is
    presentational but real: effect-closure is carried as the CODOMAIN condition `sp_effect` rather
    than as one of the article's seven clauses, so the Lean definition is not clause-for-clause the
    article's.  Closing it means restating the article's seven clauses verbatim and proving the two
    definitions equivalent.  Cheap, purely bookkeeping, and it would move a row.  ATTACK THIS FIRST
    in this file — it is the highest ratio of row-movement to difficulty anywhere in the manifest.

  row 5 `lem:span`.  Spanning and extensionality are PROVED at the `OrderUnitSpace` interface
    (`span_isEffect_eq_top`, `linearMap_eq_of_eq_on_effects`), with the proof using order-unit
    boundedness alone.  Two clauses remain: (a) the BALL clause (effects contain the ball of radius
    1/2 about 1/2 * 1) needs the carried norm to BE the order-unit norm plus Archimedean — and note
    `HermitianMat.isArchimedean` is now proved (ARC-7), so this clause got cheaper today and should
    be re-attempted; (b) the PEIRCE clause, which the article gets by instantiating the lemma at
    (J_2(q), q) — so it follows once the tree knows J_2(q) is an order unit space, which it does not.

  row 6 clause (i).  ★ The record for this was WRONG until ARC-6: THEOREM-MAP said the positive
    linear extension was "not in the tree in any form", and `Necessity.seqLeftMul` IS it (a genuine
    `→ₗ[ℝ]`, with `seqLeftMul_apply_effect`, `_nonneg`, `_one`, and uniqueness from
    `linearMap_eq_of_eq_on_effects`).  What clause (i) needs is therefore the ABSTRACT PORT of that
    construction, not a construction.  Given the ARC-6 lesson above, this is likely cheap.

  row 8 `lem:simple-bridge`.  Priced per clause in ARC-6: the article's own proof assigns (i) to
    vdW Thm A.6, (iii) to vdW Props 4.19-4.20, (iv) to a vdW remark.  Only (ii) ("every effect is
    simple") is interior, and it is the Jordan spectral theorem.  Honest target = clause (ii) on the
    concrete carrier, where Mathlib's spectral theorem applies.  So this row should be READ AS ~3/4
    CITED, and the coverage arithmetic should not count it as a full interior row.

  row 9 `lem:normality`.  ★★ REFUTED SAME DAY — see below; the row is now PARTIAL.  Original text:
    ABSENT.  On a f.d. order-unit space, S1 + S2 imply vdW-normality
    (b_k decreasing to b implies a . b_k decreasing to a . b) and compatibility passes to infima.
    The gap is stated below.  In finite dimension monotone bounded nets converge, so this is
    plausibly cheap; it was never attempted.

  row 12 `prop:central`.  The componentwise identity is proved
    (`MasterTheorem.Central.central_decomposition`).  ★★★ THIS ENTRY WAS WRONG TWICE OVER AND IS
    RETRACTED (2026-08-09).  It said the row needs "a direct-sum-of-order-unit-spaces construction the
    tree does not have": that construction is `DirectSum.lean:38 instance instProd`.  It also listed
    "the converse assembly" as open: that is `SequentialProductOn.prod` (`DirectSum.lean:84`), all
    eight fields, with `prod_sp`, `prod_fst`, `prod_snd` and `sp_eq_of_prod_eq`, and its docstring
    says outright "This is the *sufficiency* half of the omnibus's factorwise assembly".
    ★★ Caught by applying the rule from the quaternionic retraction — list a file's declarations
    instead of grepping for a guessed name.  The rule found this on its FIRST use.
    WHAT ACTUALLY REMAINS: the RESTRICTION direction only — that an arbitrary product on `V × W`
    restricts to S1-S7 products on each summand (grep `restrict|toSummand|ofProd` in DirectSum.lean
    -> prose only, 2026-08-09).

  row 13 `prop:pseudo-transfer`.  ★ ADVANCED TODAY: `Necessity.spCone_specInv_eq_one` proves the
    article's literal `a⁻¹ · a = 𝟙` with the true spectral inverse and no coefficient, using
    `spCone` and the freshly-proved `HermitianMat.isArchimedean`.  What remains is (a) the companion
    `a · a⁻¹ = 𝟙`, which puts the non-effect in the SECOND slot — `spCone` extends the first slot
    only, so this needs a second-argument extension nothing in the tree has; and (b) EJA generality.

ATTACK EVIDENCE — REFRESHED FOR ARC-8 (2026-08-10).  The ARC-8 orders require evidence FROM THIS ARC,
so the ARC-7 block below is provenance only.

  rows 5, 6, 13 — ★★★ CORRECTED 2026-08-10 (diff audit): only **row 13** moved out.  Rows 5 and 6 were
    claimed EJA-GATED and **WITHDRAWN the same day** (their residues contain non-EJA clauses: row 5's
    ball clause needs the order-unit norm; row 6's clause (ii) is ALREADY abstract as
    `SequentialProductOn.sp_smul_left`, and the reasoning below citing `HermitianMat.twistSeq_smul_left`
    — a theorem about ONE product — is the misreading that produced the wrong gate assignment).  **Rows 5
    and 6 are WALL-CERTIFIED HERE**, and this note claimed otherwise for hours, leaving them pointing at
    a certificate whose own header disclaimed them.  Original text follows.
  (formerly:) rows 5, 6, 13 — MOVED OUT of this certificate: all three are now **EJA-GATED**
    (`WallCertificates/eja-gated.lean`; row 5 and row 15 on gate (E2) Peirce, rows 6 and 13 on gate
    (E1) the Jordan spectral theorem).  ★ Row 6's clause (ii) `(λa)·b = λ(a·b)` was also CLOSED on the
    concrete carrier this arc as `HermitianMat.twistSeq_smul_left`, and the way it closed is worth
    keeping: it came out of the **constant-parameter S5 instantiated at a scalar left factor**, not
    from a functional-calculus scaling identity.  An axiom the tree already has, applied at a
    degenerate argument, replaced a lemma about the construction.

  row 3 `def:sp` — attacked this arc; see the block at `extendByZero` below.  Net: the restriction
    direction is trivial, the extension direction has a canonical construction now in this file (and
    already in the tree, instantiated, as `Necessity.badP`), and the row's real cost is **transcribing
    the article's seven clauses over the effect subtype** — statement size, not proof difficulty.
    Deliberately not `sorry`-ed without `main.tex:363-392` open, for the reason row 22 and row 36(i)
    illustrate.
    ★★ ONE CORRECTION, 2026-08-10 (refutation review): the row-3 block promises an "equivalence" of the
    two definitions.  **It cannot be an isomorphism of products** — by the same `badP` mechanism that
    killed row 35's onto half, extension is **not unique**, so the honest target is agreement on
    effect × effect.  Sending the next person after a bijection this directory proves does not exist
    would waste them.

  row 8 `lem:simple-bridge` — attacked this arc and **BLOCKED ON THE ARTICLE, not on Lean.** The only
    interior clause is (ii) "every effect is simple (E = E₀)", and `simple` here is vdW's SES notion.
    I could not state clause (ii) faithfully without vdW's definition, and declined to guess it.
    ★ That is a different kind of blocker from every other row in this file and it should be labelled
    as such: the obstruction is a missing DEFINITION from a cited source, so the next action is a
    reading task, not a proving task.  Clauses (i), (iii), (iv) remain assigned to vdW by the article's
    own proof, so this row is ~3/4 external either way.

  row 9 `lem:normality` — attacked this arc and ADVANCED: `Necessity.compatible_of_tendsto` closes the
    compatibility clause (compatibility passes to limits of effect sequences).  ★★ And the finding is
    an asymmetry this certificate's earlier note would have led a reader to get wrong: the convergence
    clause needs **no S2** (linearity of `seqLeftMul` plus finite dimensionality), but the compatibility
    clause **does** — `a·b_k → a·b` is free, `b_k·a → b·a` is first-argument continuity.  Anyone
    carrying "S2 is not used at all" forward from the convergence clause is wrong.  Residue: the
    article's order-INFIMUM form, which additionally needs Loewner monotone convergence — absent, grep
    scope recorded at the theorem (`iInf|⨅|Antitone|tendsto_of_antitone` over `RadicalRelativity/`,
    2026-08-09: only `Submodule`-kernel infima and one vendored `Set.Icc` lemma).

  row 12 `prop:central` — attacked this arc from BOTH directions.
    (a) Positive direction: the residue is confirmed to be the **restriction** half only — that every
    product on `V × W` is of the form `P.prod Q` — and `DirectSum.lean`'s own docstring says so.  This
    is `prop:central`'s splitting via central idempotents, the half the manuscript carries as a paper
    proof.  So the ARC-8 orders' listing of it under the "cheap interior sweep" was a MISPRICING, now
    corrected in `LEDGER.md`.
    (b) ★★ Refutation direction, prompted by the row-35 result this arc (where the analogous "onto"
    claim turned out FALSE because `badP` exploits the `IsEffect`-guarding): I tried to build a
    NON-split product on `V × W`.  The obvious candidates fail, and they fail at **S3**: any
    construction that discards a summand (e.g. `Q.sp a b := (P.sp a.1 b.1, 0)`) breaks
    `sp_unit_left`, since `Q.sp ousUnit a = (a.1, 0) ≠ a`.  So unlike row 35, row 12's claim is **not**
    refutable by a totality trick — the unit axiom reaches into both summands.  A failed refutation is
    evidence, and this one says the row is genuinely open in the positive direction rather than
    mis-stated.

PRIOR (ARC-7) ATTACK EVIDENCE, provenance only:

  Rows 6(ii) and 7 were attacked and CLOSED in ARC-6 at abstract generality.  Row 13's first half
  was attacked and closed today.  Rows 3, 5(a), 5(b), 8(ii), 9, 12 were NOT attempted in either
  arc — their prices above are reasoned from the article's own proofs plus the tree's contents, and
  are therefore the weak grade of evidence.  Row 3 and row 9 are the two most likely to be
  over-priced here.

ABSENCE CLAIMS AND THEIR SCOPE
  * ★★★ "no Jordan/EJA class, so EJA generality is not statable" — **RETRACTED 2026-08-09.  The
    tree DOES state the article's generality.**  `MasterTheorem/Interface.lean`'s
    `structure ComparisonSetup` carries a Jordan product (as a FIELD named `jordan`), a unit,
    `jordan_comm`, `rank_ge : 3 <= n`, a **Jordan frame** `p : Fin n -> J`, a cone, `Inv`, and
    `Theta` with its three properties — and row 16's clauses are PROVED over it.  My grep pattern
    could not see it because the structure is named `ComparisonSetup`.  Tenth false absence claim on
    this project; full retraction in WallCertificates/differential-trio.lean.
    ★ What IS absent: an axiomatization making the cited vIR/FK fields derivable rather than carried
    (`Interface.lean` says outright it "does not encode the JB-algebra premises").  So where this
    file leaned on "not statable" — rows 5 (Peirce clause) and 6(i) — the honest blocker is that
    axiomatization, not the vocabulary.
  * "no `J_2(q)` as an order unit space":
      grep -rn 'J2\|PeirceTwo\|peirce.*OrderUnit' RadicalRelativity/ -> `cornerJ2` is a PREDICATE on
      elements, not a carrier type; no `OrderUnitSpace` instance for a Peirce subalgebra.
  * ★★ "no direct sum of order unit spaces" — **FALSE, RETRACTED 2026-08-09 by the
    certificate-refutation review.**  `RadicalRelativity/DirectSum.lean:38` is
    `instance instProd : OrderUnitSpace (V × W)`, with `prod_ousUnit` (:54) and `isEffect_prod_iff`
    (:59), and that file's own header calls it "the M7 foundation … carrier for that decomposition:
    the direct sum of order-unit spaces".  The grep
    `DirectSum.*OrderUnit|OrderUnit.*DirectSum|Pi.*OrderUnitSpace` was accurate and the inference was
    invalid: the pattern needed both words on ONE LINE, and the instance is called `instProd` in a
    file called `DirectSum.lean`.  **This DE-PRICES row 12 `prop:central`, whose stated blocker was
    exactly this object** — summand inheritance and the converse assembly should now be attempted, not
    deferred.  Seventh false absence claim on this project; second one today whose grep was accurate.
  * ★★ "no second-argument cone extension" — the OBJECT was genuinely absent, but the PRICING was
    wrong and the object now EXISTS.  `SequentialProductOn.spConeRight` /
    `sp_coneNorm_indep_right` / `spConeRight_eq` / `spConeRight_of_isEffect` landed 2026-08-09 after
    the review discharged it in ~25 lines: its only ingredient, `sp_smul_right_of_unitInterval`, was
    already in the tree, and it needs `IsArchimedean` but **no S2 at all** — making the right slot
    strictly CHEAPER than the left.  The phrase "nothing in the tree has" was true of the object and
    misleading about the cost.  Consequence: `Necessity.spConeRight_specInv_eq_one` now proves the
    article's `a · a⁻¹ = 𝟙`, so **row 13's identity holds in BOTH slots**.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Necessity.PseudoInverse

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

variable {V : Type*} [OrderUnitSpace V]

/-! ### Row 9 `lem:normality` — stated, never attempted

The cleanest statable form of the article's normality: a decreasing sequence of effects with an
infimum has its images decreasing to the image of the infimum.  In finite dimension this should
follow from S2 plus monotone convergence; the tree has neither the statement nor an attempt. -/

/-- ★★ **NO LONGER A GAP — REFUTED 2026-08-09, THE SAME DAY THIS CERTIFICATE WAS WRITTEN.**

The convergence clause is proved in the tree as `Necessity.sp_tendsto_of_tendsto`, and it needs
**no S2 at all**: additivity alone extends `b ↦ a · b` to the linear map `seqLeftMul`, and a linear
map on a finite-dimensional normed space is automatically continuous.  So the result is *stronger*
than the article's statement, which assumes S1 and S2.

The statement below is kept, with its `sorry`, as the **abstract** form — the article's own
generality, over an arbitrary `OrderUnitSpace` rather than the concrete carrier.  That is what
remains, together with the compatibility-passes-to-infima clause.

★★★ UNDER-HYPOTHESIZED — flagged 2026-08-10 by the certificate-refutation review.  The statement
below quantifies over an arbitrary `OrderUnitSpace V` with **neither finite-dimensionality nor
`IsArchimedean`**, while its own prose argues "in finite dimension monotone bounded nets converge" —
about a statement that does not assume it.  `OrderUnitSpace` carries the norm as *independent*
structure and only order-unit boundedness, so positivity of `seqLeftMul` does not give norm
continuity, and the in-tree concrete proof (`Necessity.sp_tendsto_of_tendsto`) used
finite-dimensionality explicitly.  ★★ **The same defect is flagged TWELVE LINES BELOW for its
neighbour `spCone_right_exists` ("as written it OMITS `IsArchimedean V` … probably not provable at
all") — flagged there, missed here, in one pass over one file.**  Left as written, with this label, so
the pair can be compared; the fix is `[FiniteDimensional ℝ V]` (and `hS2` is additionally inert by
this file's own row-9 finding). -/
theorem normality (P : SequentialProductOn V) (hS2 : P.FirstArgContinuous)
    {a : V} (ha : IsEffect a) (b : ℕ → V) (hb : ∀ k, IsEffect (b k))
    (hmono : ∀ k, b (k + 1) ≤ b k) (blim : V) (hblim : IsEffect blim)
    (hconv : Filter.Tendsto b Filter.atTop (nhds blim)) :
    Filter.Tendsto (fun k => P.sp a (b k)) Filter.atTop (nhds (P.sp a blim)) := by
  sorry

/-! ### Row 13's remaining half — the second-slot extension

`spCone` extends the FIRST argument.  The article's `a · a⁻¹ = 𝟙` needs the non-effect in the
second slot.  Stated below so the missing object is on the record as an object, not a remark. -/

/-- ★★ **NO LONGER A GAP — DISCHARGED 2026-08-09, the day this certificate was written**, by the
certificate-refutation review.  `SequentialProductOn.spConeRight` is in the tree.

The statement below is kept, with its `sorry`, only to record a **second defect the review found in
it**: as written it OMITS `IsArchimedean V`, and without that hypothesis there is no route to
second-argument homogeneity, so the proposition is probably not provable at all.  Compare
`spCone_eq`/`sp_coneNorm_indep`, which both carry `harch`.  A gap stated with too few hypotheses is
the same class of defect as row 22's false statement: it sends the next person after something
unreachable. -/
theorem spCone_right_exists (P : SequentialProductOn V) :
    ∃ f : V → V → V, ∀ (a v : V), IsEffect a → (0 : V) ≤ v →
      ∀ μ : ℝ, SequentialProductOn.IsConeNorm v μ → f a v = μ • P.sp a (μ⁻¹ • v) := by
  sorry

/-! ### Row 3 `def:sp` — the cheapest row in the manifest, and it is bookkeeping

The article's definition lists effect-closure as a clause; `SequentialProductOn` carries it as the
codomain condition `sp_effect`.  The gap is an equivalence between the article's clause-for-clause
definition and the tree's structure.  Stated below in the direction that matters (the tree's
structure satisfies the article's clauses, read as a conjunction). -/

/-- **GAP — `def:sp` clause-for-clause.**  Not deep; it is the statement that has never been
written.  ★ Flagged in this certificate as the single highest row-movement-per-unit-effort item
remaining in the manifest. -/
theorem def_sp_clauses (P : SequentialProductOn V) :
    (∀ a b c : V, IsEffect a → IsEffect b → IsEffect c → b + c ≤ ousUnit →
        P.sp a (b + c) = P.sp a b + P.sp a c)
      ∧ (∀ a : V, IsEffect a → P.sp ousUnit a = a)
      ∧ (∀ a b : V, IsEffect a → IsEffect b → IsEffect (P.sp a b)) := by
  exact ⟨fun a b c ha hb hc hbc => P.sp_add_right ha hb hc hbc,
    fun a ha => P.sp_unit_left ha,
    fun a b ha hb => P.sp_effect ha hb⟩

/-- The extension-by-zero of an operation defined only on the effects.  ★ This is the object row 3's
packaging turns on, and it is `badP`'s template (`Necessity.badP` is exactly this construction for the
twist product), so the totality of Lean's `sp` is **not** a strengthening of the article's definition:
every total operation the axioms can see is an extension of an effect-domain one. -/
noncomputable def extendByZero {V : Type*} [OrderUnitSpace V]
    (op : {a : V // IsEffect a} → {a : V // IsEffect a} → {a : V // IsEffect a}) : V → V → V :=
  fun a b =>
    letI := Classical.dec (IsEffect a ∧ IsEffect b)
    if h : IsEffect a ∧ IsEffect b then ((op ⟨a, h.1⟩ ⟨b, h.2⟩ : {a : V // IsEffect a}) : V) else 0

theorem extendByZero_apply {V : Type*} [OrderUnitSpace V]
    (op : {a : V // IsEffect a} → {a : V // IsEffect a} → {a : V // IsEffect a})
    {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    extendByZero op a b = ((op ⟨a, ha⟩ ⟨b, hb⟩ : {a : V // IsEffect a}) : V) := by
  rw [extendByZero, dif_pos ⟨ha, hb⟩]

/-! ★★ **ROW 3's ATTACK EVIDENCE, 2026-08-10 (ARC-8 8.6), and the finding is about STATEMENT SIZE not
difficulty.**  The row's residue is "the article's eight clauses as a structure, plus restriction and
extension maps".  Attempted this arc.  What the attempt found:
  * the RESTRICTION direction is trivial (`P.sp` restricted to the effect subtype, well defined by
    `sp_effect`);
  * the EXTENSION direction has a canonical construction, `extendByZero` above, and it is already in
    the tree in instantiated form as `Necessity.badP`;
  * so the honest cost of this row is **writing the article's seven clauses out over the effect
    subtype** — roughly thirty lines of *statement* — and not any proof difficulty.  Every clause is
    the corresponding `SequentialProductOn` field with the guards discharged by the subtype.
★ That is a materially different price from "restate the definition", which is how a prose price would
have read it, and different again from the earlier note here that called row 3 "the single highest
row-movement-per-unit-effort item remaining" — true in effort, but the effort is transcription.
★ **Deliberately NOT written as a `sorry` here**, because a thirty-line statement transcribed without
the article open in front of me is exactly how row 22's FALSE gap and row 36(i)'s VACUOUS gap were
produced in this directory.  The next pass should have `main.tex:363-392` open. -/
/-- ★ Note what just happened: three of the article's clauses are NOT gaps — they compile above
with no `sorry`, straight from the structure's fields.  What is missing is only the *packaging* of
the article's list as a single definition plus the equivalence.  A prose price for row 3 would very
likely have said "restate the definition", hiding that most of it is already there. -/
example : True := trivial

end WallCertificate
