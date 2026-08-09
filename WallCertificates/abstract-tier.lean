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

ATTACK EVIDENCE
  Rows 6(ii) and 7 were attacked and CLOSED in ARC-6 at abstract generality.  Row 13's first half
  was attacked and closed today.  Rows 3, 5(a), 5(b), 8(ii), 9, 12 were NOT attempted in either
  arc — their prices above are reasoned from the article's own proofs plus the tree's contents, and
  are therefore the weak grade of evidence.  Row 3 and row 9 are the two most likely to be
  over-priced here.

ABSENCE CLAIMS AND THEIR SCOPE
  * "no Jordan/EJA class, so EJA generality is not statable": see WallCertificates/differential-trio.lean
    for the grep; same scope, same date.
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
remains, together with the compatibility-passes-to-infima clause. -/
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

/-- ★ Note what just happened: three of the article's clauses are NOT gaps — they compile above
with no `sorry`, straight from the structure's fields.  What is missing is only the *packaging* of
the article's list as a single definition plus the equivalence.  A prose price for row 3 would very
likely have said "restate the definition", hiding that most of it is already there. -/
example : True := trivial

end WallCertificate
