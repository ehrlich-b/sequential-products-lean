/-
EJA-GATED CERTIFICATE — rows 5, 6, 13, 15, 16, 17 of STATEMENT-MANIFEST.md
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
  six rows at the article's generality, and it does NOT prove the gates.  Discharging a gate below
  would make the corresponding `ComparisonSetup` FIELD derivable rather than carried — which is
  exactly the movement `EJA-DIVIDEND.md` prices.  A reader who converts "EJA-GATED" into
  "FORMALIZED" has made the error this file exists to prevent.

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

  ★★ (E3) IS THE ONE THAT MATTERS FOR THE STATUS ARITHMETIC, AND IT IS EXTERNAL.  (E3) is the
  content of `prop:theta` at vIR generality — manifest row 14, PRE-REGISTERED EXTERNAL.  So building
  the axiomatization does NOT prove it; it makes it statable at the right generality so it can be
  cited.  Rows 16 and 17, whose residue is exactly (E3), therefore terminate at EJA-GATED behind a
  named citation and NOT at FORMALIZED, no matter how much axiomatization work is done.  This is the
  single most likely misreading of `EJA-DIVIDEND.md` and it is why the dividend table says PARTIAL
  for row 14 rather than CLOSES.

PER-ROW: WHICH GATE, AND WHAT IS ALREADY CLOSED IN-TREE

  row 5  `lem:span`      — the order-unit half (effects contain the ½-ball about ½e, hence span, hence
                           linear maps agreeing on effects are equal) is CLOSED in-tree on the
                           concrete carrier.  The residue is the SECOND half: `[0,q]` spans the Peirce
                           subalgebra `J₂(q)`.  GATE (E2).
  row 6  `lem:homog`     — clause (i) (additive + order bounded ⟹ unique positive linear extension)
                           is `Necessity.seqLeftMul` in-tree; clause (ii) `(λa)·b = λ(a·b)` is in-tree
                           on the concrete carrier (ARC-8: `HermitianMat.twistSeq_smul_left`, obtained
                           from the constant-parameter S5 at a scalar left factor).  Residue = both at
                           EJA generality.  GATE (E1).
  row 13 `prop:pseudo-transfer` — proved in-tree on the concrete carrier in NORMALIZED form
                           (`Necessity/PseudoInverse.lean`).  Residue = the spectral inverse at EJA
                           generality.  GATE (E1).
  row 15 `lem:frame-fix` — the non-EJA content is closed in-tree.  Residue = the Peirce-block
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
(a Mathlib-grade EJA layer), not inside `RadicalRelativity`. -/
theorem gate_E1_spectral (C : ComparisonSetup J) (_H : JBPremises C) (x : J) :
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

Stated in the form the tree actually consumes: the simultaneous-diagonalization fact that
`CoalescenceSetup.simDiag_opCommute` carries as a field.  Naming it this way rather than as an
abstract direct-sum decomposition is deliberate — it is the consumed content, so discharging it is
what would move the rows. -/
theorem gate_E2_peirce (C : ComparisonSetup J) (_H : JBPremises C)
    (J2 ScalarOn : Fin C.n → Fin C.n → J → Prop) (i j : Fin C.n) (a b : J)
    (_ha : ScalarOn i j a) (_hb : J2 i j b) :
    OpCommute C.jordan a b := by
  sorry

/-! ### GATE (E3) — `Theta_jordan` derivable, AND IT IS EXTERNAL

Gates the other half of rows 16/17.  ★★ This is manifest row 14 `prop:theta` at van
Imhoff–Roelands generality, which is PRE-REGISTERED EXTERNAL.  Building the axiomatization makes it
statable; it does not prove it. -/

/-- **GAP — GATE (E3), van Imhoff–Roelands.**  A unital order isomorphism of the cone preserves the
Jordan product.  Gates: the `Theta_jordan` half of rows 16 and 17.

★★★ **THIS GATE IS PRE-REGISTERED EXTERNAL (row 14).**  Discharging it is NOT in ARC-8's scope and
would not be in the scope of the axiomatization either — the axiomatization's contribution is that
this statement becomes expressible at the article's generality, so `ComparisonSetup.Θ_jordan` can be a
citation instead of an unexaminable field.  Rows 16 and 17 therefore terminate at EJA-GATED. -/
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
