/-
EJA-GATED CERTIFICATE — rows 13, 16, 17 of STATEMENT-MANIFEST.md
  (rows 5, 6, 15 were claimed here on 2026-08-10 and are WITHDRAWN the same day — see the
   WITHDRAWAL block below)
Date: 2026-08-10, ARC-8 block 8.6.  Tag at issue: `paperA-arc8-cp4` and later.
Denominator pin: main.tex blob 205fdf5a (never re-pinned).

WHAT THIS FILE IS, AND WHAT IT IS NOT

  The ARC-8 ORDERS define a terminal state EJA-GATED: a row whose ENTIRE remaining residue is the
  EJA axiomatization gap, evidenced by a compiling certificate that (a) confirms every non-EJA clause
  is closed in-tree, and (b) states the article-generality statement in Lean with `sorry` exactly at
  the axiomatization gap, NAMING which ingredient gates it.

  This file does (b) honestly by stating the three GATES THEMSELVES, once each, rather than restating
  six rows six ways.  That is deliberate and it is the more falsifiable choice: if a gate is wrong,
  it is wrong in one place, and every row that leans on it moves together.

  ★ WHAT THIS FILE DOES NOT DO, stated first so it cannot be misread: it does NOT prove any of the
  rows at the article's generality, and it does NOT prove the gates.  A reader who converts
  "EJA-GATED" into "FORMALIZED" has made the error this file exists to prevent.
  ★★ CORRECTED 2026-08-10: an earlier version of this paragraph said "discharging a gate below would
  make the corresponding `ComparisonSetup` FIELD derivable".  That is true only of (E3).  (E1) and
  (E2) correspond to **no field at all** — they are ingredients the fields are built from, and (E2)
  produces the three `CoalescenceSetup` FK fields rather than a `ComparisonSetup` one.  A tidy
  three-way parallel was asserted where the structure has none.

THE MISSING PREMISES, EXACTLY

  `MasterTheorem/Interface.lean`'s own docstring says `ComparisonSetup` "does not encode the
  JB-algebra premises (the Jordan identity, formal reality, the cone-of-squares reading of
  `nonneg`)".  `JBPremises` below is those three, and nothing else.  Every gate is stated as: from
  `ComparisonSetup` PLUS `JBPremises`, derive a fact the structure currently carries as a field.

THE THREE GATES (the names used throughout, and in EJA-DIVIDEND.md)

  (E1) JORDAN SPECTRAL THEOREM at f.d. formally-real generality — spectral resolution into a Jordan
       frame with real eigenvalues, and the functional calculus on it.
  (E2) PEIRCE DECOMPOSITION for a Jordan frame, with the Faraut–Korányi multiplication rules.
  (E3) `Theta_jordan` DERIVABLE — van Imhoff–Roelands: a unital order isomorphism of the cone
       preserves the Jordan product.

  ★★ (E3) AND THE STATUS ARITHMETIC — **CLAIM WEAKENED 2026-08-10 after the refutation review.**
  I had written: (E3) *is* `prop:theta` at vIR generality (row 14, pre-registered external), therefore
  rows 16/17 "terminate at EJA-GATED behind a named citation and NOT at FORMALIZED, no matter how much
  axiomatization work is done."  **That inference does not follow from the gate as stated.**
  `gate_E3_theta_jordan` assumes `Φ : J ≃ₗ[ℝ] J` — **linear** — so it is the classical
  unital-linear-order-isomorphism theorem (Koecher / Alfsen–Shultz 2.80), which `Interface.lean`
  itself cites as "classical corroboration" and which the tree already discharges concretely
  (`KadisonDischarge` / `RealKadison`).  vIR's external delta is the JB-algebra-generality version.
  Rows 16/17's article statements live on a f.d. **simple EJA**, where the classical linear fact is
  what is needed — so a Mathlib-grade f.d. EJA layer containing Koecher/AS-2.80 could discharge this
  gate in-tree, and rows 16/17 could then reach FORMALIZED.
  ★ Honest status: (E3) as stated is **not** obviously external, the load-bearing sentence of this
  file's first version was overstated, and whether rows 16/17 can reach FORMALIZED is **OPEN** pending
  a decision about which theorem row 14 actually reserves.
  ★ A citation inconsistency found in the same pass and NOT resolved: `external-rows.md` names the
  row-14 source "van Ittersum–Reijnders" while `Interface.lean` and this file name it "van
  Imhoff–Roelands" (arXiv:1904.09278).  Two names for the theorem that terminates two rows.  Not
  resolvable offline; flagged, not guessed.

★★★ WITHDRAWAL — ROWS 5, 6 AND 15 ARE **NOT** EJA-GATED (2026-08-10, certificate-refutation review)

  EJA-GATED requires that EVERY non-EJA clause be closed in-tree first.  For three of the six rows I
  claimed, that is false, and in each case the manifest's own cell said so:

    row 5  `lem:span` — the **ball clause** ("the effects contain the ½-ball about ½·e") is open, and
      the manifest records why: it "needs the norm to *be* the order-unit norm".  That is an
      order-unit-norm fact, **not** the EJA axiomatization.  ★ My per-row line below asserted the
      ½-ball clause was CLOSED; `OrderUnitSpace.span_isEffect_eq_top` proves *spanning* from
      order-unit boundedness WITHOUT the ball, which is what I mistook for it.
    row 6  `lem:homog` — clause (ii) is **already proved at abstract order-unit generality** as
      `SequentialProductOn.sp_smul_left` (S1–S7 + S2 + `IsArchimedean`), and the manifest cell says
      outright that this "covers the article's statement, whose ambient `J` is an EJA and hence an
      order unit space".  I cited `HermitianMat.twistSeq_smul_left` instead — a theorem about **one
      specific product**, the constant-parameter twist — and then assigned the row to gate (E1), the
      Jordan spectral theorem, on the strength of that misreading.  Clause (i)'s abstract port needs
      the order-unit route, not spectral theory.  ★ **Read the statement, not the name** — the two
      differ by exactly "for an arbitrary S1–S7 product" versus "for the twist product".
    row 15 `lem:frame-fix` — the article's statement includes "**and lies in Stab(F)°**", which needs
      the stabilizer as a group with an identity component.  Two other certificates in this directory
      already record that vocabulary as absent, and it is **not** the EJA axiomatization.  My
      move-out note silently narrowed the residue to "the Peirce-block clauses".

  ★★ **The shape of the error, since it is one error made three times: I classified each row by its
  BIGGEST residue and let that stand for its WHOLE residue.**  EJA-GATED is a claim about the
  complement — that nothing else remains — and a claim about a complement cannot be checked by looking
  at the largest item in it.  This is the same failure as row 35's "and that is the whole residue",
  which the same review process caught two days earlier.
  ★ Rows 5, 6, 15 revert to WALL-CERTIFIED with this arc's attack evidence, and their non-EJA residues
  are now named in the manifest.

PER-ROW: WHICH GATE, AND WHAT IS ALREADY CLOSED IN-TREE (rows 13, 16, 17; the three withdrawn rows'
lines are retained below with their defects marked, because the retraction is the content)

  row 5  [WITHDRAWN — see above; the ball clause is open and is NOT an EJA gap] `lem:span` — the order-unit half (effects contain the ½-ball about ½e, hence span, hence
                           linear maps agreeing on effects are equal) is CLOSED in-tree on the
                           concrete carrier.  The residue is the SECOND half: `[0,q]` spans the Peirce
                           subalgebra `J₂(q)`.  GATE (E2).
  row 6  [WITHDRAWN — see above; clause (ii) is already abstract, and the cited theorem was the wrong one] `lem:homog` — clause (i) (additive + order bounded ⟹ unique positive linear extension)
                           is `Necessity.seqLeftMul` in-tree; clause (ii) `(λa)·b = λ(a·b)` is in-tree
                           on the concrete carrier (ARC-8: `HermitianMat.twistSeq_smul_left`, obtained
                           from the constant-parameter S5 at a scalar left factor).  Residue = both at
                           EJA generality.  GATE (E1).
  row 13 `prop:pseudo-transfer` — proved in-tree on the concrete carrier in NORMALIZED form
                           (`Necessity/PseudoInverse.lean`).  Residue = the spectral inverse at EJA
                           generality.  GATE (E1).
  row 15 [WITHDRAWN — see above; the `Stab(F)°` clause is non-EJA and open] `lem:frame-fix` — the non-EJA content is closed in-tree.  Residue = the Peirce-block
                           statements (Θ_r preserves each block; L_{a(r)} is block-diagonal).
                           GATE (E2).
  row 16 `lem:coalescence` — ★ BOTH CLAUSES ARE ALREADY PROVED AT THE INTERFACE'S OWN ABSTRACT
                           GENERALITY (`MasterTheorem.CoalescenceSetup.coalescence_J2q` and
                           `coalescence_block`), and instantiated on the concrete carrier.  There is
                           NO missing mathematics.  Residue = that the FK fields and `Theta_jordan`
                           are CARRIED.  GATES (E2) + (E3).
  row 17 `lem:homomorphism` — same shape as row 16; the hyperplane clause closed in ARC-6.
                           GATES (E2) + (E3).

  ★ Note what the shape of this list means.  Four of the six rows have their mathematics done
  somewhere; what they lack is that the ARTICLE'S hypothesis class is not expressible.  That is a
  real gap against the standing bar ("FORMALIZED at the article's own generality, no located
  hypothesis") and it is NOT a gap in anyone's understanding of the mathematics.  A prose price for
  these rows that said "needs the Jordan spectral theorem" would be true and would hide that.

ABSENCE CLAIMS AND THEIR SCOPE
  * "no JB-algebra premises are encoded anywhere in the tree":
      grep -rn 'JordanIdentity\|jordan_identity\|FormallyReal\|formally_real\|coneOfSquares\|cone_of_squares' RadicalRelativity/
      -> no hits (whole first-party tree incl. Vendor/, 2026-08-10).
  * "no Jordan spectral theorem or Peirce decomposition at abstract generality":
      ★ SELF-CORRECTED on the same day, before this file was committed.  My first wording said the FK
      facts "appear ONLY as `CoalescenceSetup` fields", and that is WRONG: they are also DISCHARGED at
      the concrete carrier in `Necessity/CoalescenceInstanceGen.lean:306-309`
      (`simDiag_opCommute := …`, `aOf_scalarOn := …`, `block_mem_J2 := …`).  The accurate claim is:
      the three FK facts are **proved concretely and CARRIED abstractly** — each is documented in
      `MasterTheorem/Coalescence.lean` as "entering as a cited FK field" at the interface's
      generality.  So (E2) is not missing mathematics on `H_n(𝕜)`; it is missing at EJA generality.
      Read at source 2026-08-10.
      ★ Worth naming why the first version was wrong: "appears only as a field" was an inference from
      where I FIRST saw the identifier, not from the declaration list of every file that mentions it.
      The project's standing first move exists for exactly this, and I skipped it inside my own
      certificate.
  * "Mathlib has no EJA/Jordan layer": consistent with the 2026-07-19 landscape scout (memory
      `lean-formalization-landscape`); NOT re-verified against Mathlib v4.28.0 in this arc, and
      flagged as such rather than asserted.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.MasterTheorem.Coalescence

set_option linter.style.longLine false

namespace WallCertificate

open MasterTheorem

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-! ### The three missing premises -/

/-- **The JB-algebra premises `ComparisonSetup` does not encode.**  Exactly the three its own
docstring names, over an existing `ComparisonSetup`, so the gates below can be stated as "from these,
derive what the structure carries". -/
structure JBPremises (C : ComparisonSetup J) : Prop where
  /-- The Jordan identity `(x∘y)∘(x∘x) = x∘(y∘(x∘x))`. -/
  jordan_identity : ∀ x y : J,
    C.jordan (C.jordan x y) (C.jordan x x) = C.jordan x (C.jordan y (C.jordan x x))
  /-- Formal reality: a sum of squares vanishes only if each term does. -/
  formally_real : ∀ (m : ℕ) (f : Fin m → J),
    (∑ i, C.jordan (f i) (f i)) = 0 → ∀ i, f i = 0
  /-- The cone-of-squares reading of `nonneg`. -/
  nonneg_iff_squares : ∀ x : J,
    C.nonneg x ↔ ∃ (m : ℕ) (f : Fin m → J), x = ∑ i, C.jordan (f i) (f i)

/-! ### GATE (E1) — the Jordan spectral theorem

Gates rows 6 and 13.  Stated as the existence of a spectral resolution in a Jordan frame with real
eigenvalues, which is what a functional calculus (hence `aOf`'s inverse and the positive extension of
`L_a`) is built from. -/

/-- **GAP — GATE (E1), the Jordan spectral theorem.**  Gates: row 6 `lem:homog` at EJA generality,
row 13 `prop:pseudo-transfer` at EJA generality.

★ This is the large piece and it has no Mathlib support.  Its natural home is upstream of this paper
(a Mathlib-grade EJA layer), not inside `RadicalRelativity`.

★★★ **`[FiniteDimensional ℝ J]` ADDED 2026-08-10 after the certificate-refutation review, and without
it this gate was FALSE.**  `ComparisonSetup` requires only `NormedAddCommGroup` +
`InnerProductSpace ℝ`, so `J = ℝ[X]` with polynomial multiplication as `jordan`, `Θ = id`, and
`nonneg` the sums of squares satisfies every `ComparisonSetup` field AND all three `JBPremises` — yet
`ℝ[X]` is a domain, so its only idempotents are `0` and `1`, `∑ q i = e` forces all but one to vanish,
and `x = X` has no spectral resolution.  So as first written the gate could never be discharged by
anyone.  ★ The lesson is narrow and worth keeping: **an "at the article's generality" statement must
carry the article's STANDING hypotheses too, not only its premises.**  f.d. is standing for EJAs and I
transcribed only the three premises the interface docstring lists. -/
theorem gate_E1_spectral [FiniteDimensional ℝ J] (C : ComparisonSetup J) (_H : JBPremises C)
    (x : J) :
    ∃ (m : ℕ) (q : Fin m → J) (lam : Fin m → ℝ),
      (∀ i, C.jordan (q i) (q i) = q i) ∧
      (∀ i j, i ≠ j → C.jordan (q i) (q j) = 0) ∧
      (∑ i, q i) = C.e ∧
      x = ∑ i, lam i • q i := by
  sorry

/-! ### GATE (E2) — the Peirce decomposition

Gates rows 5 and 15, and half of rows 16/17.  The three `CoalescenceSetup` fields that currently
carry Faraut–Korányi are exactly what this would produce. -/

/-- **GAP — GATE (E2), the Peirce decomposition and its Faraut–Korányi rules.**  Gates: row 5
`lem:span`'s Peirce half, row 15 `lem:frame-fix`'s block statements, and the FK half of rows 16/17.

Stated as: the axiomatization **produces the three FK data** that `CoalescenceSetup` carries as fields
(`aOf_scalarOn`, `block_mem_J2`, `simDiag_opCommute`).  The first two conjuncts pin `ScalarOn` and `J2`
from below, so they cannot be cheated by `False`, and the third is the content.

★★★ **RESTATED 2026-08-10 after the certificate-refutation review, and the previous version was
FALSE — the worst defect in this arc, in the file written to prevent exactly this.**  It read
`(J2 ScalarOn : … → Prop) … (_ha : ScalarOn i j a) (_hb : J2 i j b) : OpCommute C.jordan a b` with the
two predicates as **free universally-quantified variables**.  Instantiate both at `fun _ _ _ => True`
and it says *every two elements of every JB-premised `ComparisonSetup` operator-commute*, which is
false on `H_n(𝕜)` (take `diag(1,0)` against the `(0,1)` block; the reviewer compiled this using the
tree's own `Necessity.opCommute_iff_commuteG`).  It also never used `i ≠ j`.
  ★★ **And it was SELF-DEFEATING in the exact sense this project has a test for:** discharging it as
  written would have proved that no JB-premised `ComparisonSetup` exists on the intended carriers —
  refuting the axiomatization programme the file exists to price.  Four of the six rows leaned on it.
  ★ **The transferable rule: a free predicate variable in a gap statement is an unconstrained
  hypothesis, and an unconstrained hypothesis is where vacuity and falsity both hide.**  In the field
  it was meant to reproduce, `J2`/`ScalarOn` are *fields constrained by two other fields*; dropping
  them to variables silently deleted those constraints.

★★★ **AND THE FIRST REPAIR WAS ALSO FALSE — caught by the diff audit of the repairs, hours later.
Second falsity on this one statement.**  Pinning `ScalarOn`/`J2` from below removed the vacuity and
thereby *created* a new falsity, because the existential is **antitone in its own witnesses**:
conjuncts 1 and 2 bound the predicates from below, conjunct 3 is contravariant in both, so the whole
thing is provable iff provable at the minimal choice — and **the minimal choice is built from `aOf` and
`p`, which are UNCONSTRAINED `ComparisonSetup` FIELDS.**  `Interface.lean` requires no idempotency, no
orthogonality, and no `aOf r = Σ exp(r_i) p_i`.  So take `J = H_3(ℝ)` with the genuine standard frame
but `aOf := fun _ => diag(1,1,0)`: every `ComparisonSetup` field and all three `JBPremises` hold (it is
a real EJA), conjunct 1 forces `ScalarOn 0 2 diag(1,1,0)`, conjunct 2 forces `J2 0 2 (E₀₂+E₂₀)`, and
conjunct 3 then demands an operator commutation that fails.  The reviewer machine-checked all three
tree-facing ingredients.
  ★★ **FIXED ABOVE by hypothesizing the standing facts about `p` and `aOf` — which is verbatim the
  lesson this same commit wrote down one declaration earlier for `gate_E1` ("an 'at the article's
  generality' statement must carry the article's STANDING hypotheses too") and did not apply here.**
  Writing a rule and applying it are separate acts, and the gap between them was under twenty lines.
  ★ Second consequence, also from the audit: **`[FiniteDimensional ℝ J]` is INERT in this gate** (the
  counterexample is finite-dimensional).  It was added by parallelism with `gate_E1`, where it is
  genuinely load-bearing — a hypothesis copied for symmetry rather than for need.
  ★ Note on the form of `haOf`: the article writes `a(r) = Σ e^{r_i} p_i`, and this file states instead
  that `aOf r` is a **strictly positive** combination of the frame.  Reason: `Real.exp` is not in this
  file's transitive imports, and strict positivity is exactly what blocks the counterexample (whose
  `diag(1,1,0)` is a frame combination with a **zero** coefficient).  Weaker than the article's form and
  sufficient for the purpose — recorded so nobody reads it as the article's clause verbatim.
  ★★★ **"SUFFICIENT FOR THE PURPOSE" IS WRONG — CORRECTED 2026-08-13 (ARC-9 block 9.23), and the
  instrument was an actual proof of this gate's conclusion.**  `EJA/InterfaceInstance.lean` discharges
  exactly this conclusion, and it **could not use `haOf` in this form**.  The reason is precise: the
  third conjunct `aOf_scalarOn` needs `r i = r j ⟹ aOf r` is scalar on the block, which requires the
  two block **coefficients to coincide**.  `haOf` gives some positive `c` with `aOf r = Σ c i • p i`
  and **nothing ties `c` to `r`** — so `r i = r j` yields no information about `c i` versus `c j`, and
  the conclusion does not follow.  Strict positivity blocks the *zero-coefficient* counterexample the
  note names; it does nothing about *unequal* coefficients, which is the case `aOf_scalarOn` is about.
  ★ The honest status: this gate is **UNDER-HYPOTHESISED**, and whether it is outright FALSE is open —
  no counter-model was built, and the claim here is only that the hypothesis cannot support the
  conclusion.  The repair is `haOf' : ∀ r, aOf r = ∑ i, Real.exp (r i) • p i`, or equivalently adding
  `∀ i j, r i = r j → c i = c j`.
  ★ And the stated *reason* for the weakening no longer holds: `Real.exp` is available —
  `EJA/InterfaceInstance.lean` imports `Mathlib.Analysis.SpecialFunctions.Exp` and uses exactly that
  form.  **A hypothesis weakened for an import-convenience reason, with the weakening's cost
  mis-assessed in the same sentence that recorded it.** -/
theorem gate_E2_peirce [FiniteDimensional ℝ J] (C : ComparisonSetup J) (_H : JBPremises C)
    (hp_idem : ∀ i, C.jordan (C.p i) (C.p i) = C.p i)
    (hp_orth : ∀ i j, i ≠ j → C.jordan (C.p i) (C.p j) = 0)
    (hp_sum : ∑ i, C.p i = C.e)
    (haOf : ∀ r : Fin C.n → ℝ, ∃ c : Fin C.n → ℝ, (∀ i, 0 < c i)
      ∧ C.aOf r = ∑ i, c i • C.p i) :
    ∃ J2 ScalarOn : Fin C.n → Fin C.n → J → Prop,
      (∀ (r : Fin C.n → ℝ) (i j : Fin C.n), r i = r j → ScalarOn i j (C.aOf r)) ∧
      (∀ (i j : Fin C.n) (x : J), IsBlockElt C.jordan C.p i j x → J2 i j x) ∧
      (∀ (i j : Fin C.n) (a b : J), ScalarOn i j a → J2 i j b → OpCommute C.jordan a b) := by
  sorry

/-! ### GATE (E3) — `Theta_jordan` derivable, AND IT IS EXTERNAL

Gates the other half of rows 16/17.  ★★ This is manifest row 14 `prop:theta` at van
Imhoff–Roelands generality, which is PRE-REGISTERED EXTERNAL.  Building the axiomatization makes it
statable; it does not prove it. -/

/-- **GAP — GATE (E3), van Imhoff–Roelands.**  A unital order isomorphism of the cone preserves the
Jordan product.  Gates: the `Theta_jordan` half of rows 16 and 17.

★★★ **CLAIM WEAKENED — see the header block; this paragraph contradicted it for 200 lines.**  It read
"THIS GATE IS PRE-REGISTERED EXTERNAL (row 14)", and the diff audit found the retraction had been applied
to the header and not here.  As stated this gate assumes `Φ` LINEAR, so it is the classical
Koecher/Alfsen–Shultz theorem, not vIR's JB-generality version; whether rows 16/17 can reach FORMALIZED
is **OPEN**.  Original text follows.
★★ (formerly:) **THIS GATE IS PRE-REGISTERED EXTERNAL (row 14).**  Discharging it is NOT in ARC-8's scope and
would not be in the scope of the axiomatization either — the axiomatization's contribution is that
this statement becomes expressible at the article's generality, so `ComparisonSetup.Θ_jordan` can be a
citation instead of an unexaminable field.  Rows 16 and 17 therefore terminate at EJA-GATED. — ★ SUPERSEDED, see above. -/
theorem gate_E3_theta_jordan (C : ComparisonSetup J) (_H : JBPremises C)
    (Φ : J ≃ₗ[ℝ] J) (_hunital : Φ C.e = C.e)
    (_horder : ∀ x, C.nonneg x ↔ C.nonneg (Φ x)) (x y : J) :
    Φ (C.jordan x y) = C.jordan (Φ x) (Φ y) := by
  sorry

/-! ### What is ALREADY closed, made self-evidencing

None of these is a gap.  They compile, so a reader who suspects the per-row reading above is
over-generous can check it here rather than take it on trust.  ★ In particular rows 16 and 17 have no
missing mathematics at the interface's own generality — which is why their residue is (E3), a
citation, and not a proof. -/

/-- Row 16's SECOND clause at the interface's abstract generality — **in the tree**. -/
example (C : CoalescenceSetup J) {a b : J} {i j : Fin C.n}
    (ha : C.Inv a) (hsc : C.ScalarOn i j a) (hb : C.J2 i j b) :
    C.Θ a b = b :=
  C.coalescence_J2q ha hsc hb

/-- The gate that would make `Θ_jordan` a theorem is stated against the very field it would replace:
here is that field, so the two can be compared side by side. -/
example (C : ComparisonSetup J) (a : J) (ha : C.Inv a) (x y : J) :
    C.Θ a (C.jordan x y) = C.jordan (C.Θ a x) (C.Θ a y) :=
  C.Θ_jordan a ha x y

end WallCertificate
