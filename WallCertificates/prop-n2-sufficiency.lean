/-
WALL CERTIFICATE — `prop:n2-sufficiency`  (row 30)  and  `cor:qubit-classification`  (row 35)
Date: 2026-08-09, ARC-7 block 7.5.  Tag `paperA-arc7-cp1`.  Pin: main.tex blob 205fdf5a.
Row status on this date: 30 = ABSENT, 35 = ABSENT.

★★★ SUPERSEDED, 2026-08-09 (ARC-8 block 8.1(b), second pass).  ROW 30 IS FORMALIZED.  The gap
statement below is now PROVED, not `sorry`-ed, with `RankTwo.n2SequentialProduct` and
`RankTwo.n2SequentialProduct_firstArgContinuous` in `RadicalRelativity/RankTwo/Sufficiency.lean`,
for an arbitrary `t : C(RP2, R)` — including the S2 conjunct, i.e. the word "norm-continuous" in the
article's statement.  Row 35 is still ABSENT.
  ★★ AND THIS FILE'S CENTRAL PREDICTION ABOUT S2 WAS WRONG IN THE USEFUL DIRECTION.  It said S2
  "needs the deviation to vanish fast enough at the scalars, which is a genuine estimate rather than
  plumbing".  There is a genuine analytic input, but it is JOINT continuity of the twist product in
  (parameter, matrix) — and the near-the-scalars comparison the file predicted is NOT NEEDED AT ALL,
  because at a scalar the product does not depend on the parameter (`twistSeq_smul_one_left`), so
  joint continuity plus compactness of `[-K,K] x effects` (Heine-Cantor) already gives a modulus of
  continuity in the matrix that is uniform in the parameter.  THE PARAMETER NEVER HAS TO CONVERGE.
  ★ So the same scalar lemma that made the algebra free made the analysis free.  A certificate that
  correctly identifies WHICH clause is hard can still be wrong about WHY it is hard, and the "why" is
  what a reader uses to price it.

★★★ AND THE MORE USEFUL FINDING, FROM THE CHECKPOINT-1 COLD REVIEW: THE GAP THIS CERTIFICATE NAMED
AS LOAD-BEARING IS NOT ON ROW 30'S PATH.  This file told the reader to attack
"compatible ==> same frame ==> same parameter" FIRST, and the ARC-8 work closed exactly that
(`Necessity.n2FrameTwist_eq_of_compatible`, cited below in place of the old `sorry`).  But that
theorem has ZERO consumers in the tree, and row 30 was closed by a DIFFERENT mechanism:
`RankTwo.n2Tau_eq_of_commute`, which is P-FREE.  It could not have been otherwise — the certificate's
form is quantified over a `SequentialProductOn P`, and the compatibility facts are needed BEFORE the
structure is assembled, so instantiating at `P := n2SequentialProduct t` is circular.
  ★ THE TRANSFERABLE RULE: a certificate's named gap can be closed, correctly and at the stated
  price, and still not be the thing the row needed.  `n2FrameTwist_eq_of_compatible` is a
  NECESSITY-side lemma (it extracts from an arbitrary product, which is rows 29/34/35 territory);
  this certificate mis-filed it under a SUFFICIENCY row.  So "the gap is closed" is not the same
  claim as "the row moved", and a certificate should say which of the two it is asserting.
  ★ A second observation from the same review, kept because it is uncomfortable: every instance of
  the `hcomm` hypothesis constructible in the tree today already has its conclusion available from
  `n2FrameTwist_eq_of_frameMap_eq`, `n2FrameTwist_reverse`, or `n2FrameTwist_mul_diagonal`.  The
  informative statement of the pair is `frameMap_eq_or_compl_of_compatible`, whose content is the
  contrapositive; the theorem this file cites is the weaker packaging.

WHAT THE ARTICLE ASSERTS
  (30) For every continuous t : RP^2 -> R the operation  a . b := a^{1/2+i t_a} b a^{1/2-i t_a}
       (t_a = t(fr a), and 0 for scalar a) is a norm-continuous S1-S7 sequential product on H_2(C).
  (35) t |-> o_t is a BIJECTION from C(RP^2, R) onto the norm-continuous S1-S7 products on H_2(C).

WHY THESE TWO SHARE A CERTIFICATE
  Row 35 is exactly rows 29/30/32/33/34 assembled: 30 gives the forward map is well defined,
  32+33+34 give the inverse (a product determines a bounded continuous RP^2 function), 29 gives
  that the inverse composed with the forward map is the identity.  So a certificate for 35 that
  did not also price 30 would be pricing a sum without one of its terms.

WHAT IS IN THE TREE
  * `HermitianMat.twistSequentialProduct` — all seven axioms for CONSTANT t (row 28, FORMALIZED).
    This is the machinery row 30 must generalize, and the generalization is where the difficulty is
    (below), not in re-doing the constant case.
  * `RankTwo.tauModuliRP2 : C(RP2, R)` and the tau family under `thm:qubit-boundary` (row 31):
    parts (i) and (iii) plus the cocycle, for ONE concrete frame-dependent t.  So a frame-dependent
    product IS constructed in the tree — but for a specific t, with the bundled S1-S7 verification
    itself still open (row 31).
  * rows 32/33 are FORMALIZED as of 2026-08-09 (`exists_n2FrameTwist_bound`,
    `continuous_n2FrameTwist`); row 34's remaining gap has its own certificate.

WHERE THE DIFFICULTY ACTUALLY IS — and it is NOT "seven axioms again"
  For constant t, every axiom is a computation with ONE twist factor.  For frame-dependent t the
  parameter attached to the left slot varies with the left argument, and the axioms that relate
  TWO left arguments stop being formal:
    - S5 (compatible associativity) relates  a . (b . c)  to  (a . b) . c  — the inner and outer
      products carry t_a and t_b, DIFFERENT numbers, and the article's proof needs that compatible
      effects share a spectral frame so that t_a = t_b.  "Compatible ==> same frame ==> same
      parameter" is the load-bearing step and nothing in the tree states it.
    - S7 (multiplicativity of compatibility) has the same shape.
    - S2 needs a |-> t_a continuous, i.e. the composite of the spectral-frame map with t.  The
      spectral-frame map is discontinuous exactly at the scalars, which is why the article defines
      t_a = 0 there; so S2 needs the deviation to vanish fast enough at the scalars, which is a
      genuine estimate rather than plumbing.
  CONCLUSION FOR PRICING: this row is a real build with one genuinely delicate clause (S2 near the
  scalars) and one that needs a new in-tree fact (compatible ==> same frame).  It should NOT be
  priced as "instantiate row 28 with a variable parameter".

ATTACK EVIDENCE
  Not attempted in ARC-7 (budget went to rows 32/33/34/36 and the abstract tier).  The pricing
  above is from reading the article's own proof of `prop:n2-sufficiency` at source plus the shape of
  `HermitianMat.twistSequentialProduct`'s seven clauses.  ★ Note this is exactly the kind of
  estimate-without-attempt that has been WRONG twice on this project about `lem:n2-bounded`, in both
  directions.
  ★★★ AND THE PRICING SURVIVED REVIEW WHILE THE STATEMENT DID NOT (2026-08-09).  The
  certificate-refutation review agreed with every judgement in this block — S2-near-the-scalars is the
  delicate clause, "compatible ==> same frame" is load-bearing, this is not "row 28 with a variable
  parameter" — and then showed the Lean statement written to carry that judgement was SELF-DEFEATING.
  See the retraction on `frame_param_eq_of_compatible` below.  The lesson is that a certificate's prose
  and its statement fail independently: getting the price right is no evidence that the proposition
  says it.  Attack "compatible ==> same frame" first, as originally advised, but attack the RESTATED
  version.

ABSENCE CLAIMS AND THEIR SCOPE
  * "no frame-dependent sequential-product structure is constructed for a general t":
      grep -rn 'SequentialProduct.*tau\|tauSeq\|frameDependent' RadicalRelativity/  -> no hits
      (whole first-party tree incl. Vendor/, 2026-08-09).
  * ★★★ "'compatible effects share a spectral frame' is not stated" — the grep is accurate and the
    INFERENCE IS FALSE.  **The hard half of it was already in the tree**:
    `HermitianMat.commute_of_twistSeq_comm` (`Hermitian/Sequential.lean`) is
    "twist-product compatibility ⟹ matrix commutation" — the Gudder–Nagy normality trick via the
    Frobenius certificate `C = b^{1/2+it}·a − a·b^{1/2+it}` — with the converse
    `twistSeq_comm_of_commute` alongside.  So twist-product compatibility is fully CHARACTERIZED.
    The grep pattern `Compatible.*frame|frame.*compatible` could not see it because the lemma is
    named after commutation, not frames.  **NINTH false absence claim on this project, and the
    third in one day whose grep was accurate and whose name-guess was wrong.**
    ★ What the rank-two application actually needed was the TWO-PARAMETER shape, because
    `n2_sp_eq_twistSeq_frame` gives the two orders with the parameters of *different* frames
    (`P.sp a b = twistSeq t_U a b` but `P.sp b a = twistSeq t_V b a`).  That generalization is now
    in the tree as `commute_of_twistSeq_comm_param`, and it was essentially free: the parameter
    enters the proof only through the Frobenius certificate, which lives on the `b`-side parameter,
    while the `a`-side appears in exactly one place supplying a trace value that is itself
    parameter-independent.
    ★★ THE CHAIN IS NOW MAPPED IN FOUR STEPS, TWO OF THEM IN THE TREE (2026-08-09).  With
    `a = Ad_U(diagFamily r)`, `b = Ad_V(diagFamily s)` non-scalar and `W = U^H V`:
      1. compatibility ⟹ `Commute a b`, via `n2_sp_eq_twistSeq_frame` then
         `commute_of_twistSeq_comm_param` (the two parameters differ, which is exactly why the
         one-parameter form did not suffice).  IN THE TREE.
      2. conjugating by `U^H`, `M := Ad_W (diagFamily s)` is DIAGONAL, because `diagFamily r` is
         diagonal with distinct entries — `Necessity.offdiag_zero_of_commute_diagonal`.  IN THE TREE.
      3. `M` is not a scalar (else conjugating back forces `s 0 = s 1`), so its entries are distinct,
         and `M (W e_0) = e^{s_0}(W e_0)` makes `W e_0` supported on one coordinate —
         `Necessity.eigen_diagonal_fin2`.  THE EIGENVECTOR STEP IS IN THE TREE; the "M is not a
         scalar" step is NOT.
      4. hence `Ad_W (frameProj 0)` is `frameProj 0` or `frameProj 1`, so the frame maps agree or
         complement, and `n2FrameTwist_eq_of_frameMap_eq` / `frameMap_mul_swap` +
         `n2FrameTwist_reverse` finish.  NOT ASSEMBLED.
    ★ So the remainder is steps 3(b) and 4: matrix plumbing over `Fin 2`, no new mathematics and no
    missing vocabulary.  Attempted 2026-08-09 and not finished — the two elementary lemmas landed, the
    assembly did not, and that is recorded as budget rather than resistance.
    ★★★ **DISCHARGED 2026-08-09, ARC-8 block 8.1(a).**  The chain is closed in the tree as
    `Necessity.n2FrameTwist_eq_of_compatible`, and the gap statement below is a citation rather than a
    `sorry`.  The price was right about size and WRONG ABOUT ROUTE: step 3's "`M` is not a scalar, so
    `eigen_diagonal_fin2` puts `W e₀` on one coordinate" is **not needed at all**.  Writing the two-level
    family as `e^{s₁}·𝟙 + (e^{s₀} − e^{s₁})·p₀` makes the conjugated frame projection an *affine*
    function of the conjugated family, so one invertible coefficient transfers the vanishing off-diagonal
    entry; then a diagonal projection of trace one over `Fin 2` is a frame projection
    (`eq_frameProj_of_diag_projection`).  So the mapped chain's step 3 named a longer route than the one
    that worked, and `eigen_diagonal_fin2` — landed the day before *for this very purpose* — is not on
    the path.
    ★ **The lesson, and this directory keeps re-learning it:** a four-step map written from the article's
    own proof is evidence about the article's route, not about the cheapest Lean route.  The map was
    still worth having — it turned the remainder into a stated size — but "no new mathematics and no
    missing vocabulary" was the load-bearing half of that estimate, and the step count was not.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Necessity.FrameConstancy
import RadicalRelativity.RankTwo.Bloch
import RadicalRelativity.RankTwo.Sufficiency

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

/-! ### A side condition the first version hid INSIDE two statements

★★ The reviewer found that two propositions below carried an inline `(by sorry)` **inside the
statement** (the `col₀ ≠ 0` obligation for `Projectivization.mk`).  Those attribute to the enclosing
declaration, so the file's `sorry` warning count **understated it by two** — and, worse, meant those
two propositions were **not fully written down** and could not be attacked as stated at all.

Discharged here, from the reviewer's own proof, so the statements below are well-formed. -/

theorem col_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    (WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0) : EuclideanSpace ℂ (Fin 2)) ≠ 0 := by
  intro h
  have hf : ∀ i, (U : Matrix (Fin 2) (Fin 2) ℂ) i 0 = 0 := by
    intro i
    have := congrFun (congrArg WithLp.ofLp h) i
    simpa using this
  have hU : star (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.2
  have h00 := congrFun (congrFun hU 0) 0
  rw [Matrix.mul_apply] at h00
  simp only [Matrix.star_apply, hf, star_zero, mul_zero, Finset.sum_const_zero,
    Matrix.one_apply_eq] at h00
  exact one_ne_zero h00.symm

/-! ### The load-bearing missing fact, isolated

If this is cheap, row 30 is mechanical; if it is hard, row 30 is hard.  Attack it first. -/

/-- ★★★ **THE FIRST VERSION OF THIS STATEMENT WAS SELF-DEFEATING, AND THAT IS A THIRD DEFECT KIND
FOR THIS DIRECTORY.  Refuted 2026-08-09 by the certificate-refutation review, on the same day it was
written.**

The first version's hypotheses were `a = Ad_U a` and `b = Ad_V b`.  But `Necessity.adU U a = U a Uᴴ`,
so `a = Ad_U a` says **`U` COMMUTES with `a`** — not that `U` diagonalizes it.  Consequences, both
compiled by the reviewer:
  * `a = b = 𝟙` is stabilized by *every* unitary (`adU_unital`) and is compatible with itself by
    `rfl`, so the hypotheses hold for **arbitrary** `U` and `V`;
  * therefore the statement implies `n2FrameTwist P hS2` is **globally constant, for every product**.

**Global constancy is exactly the negation of what rows 34 and 35 need** — a *nonconstant*
`ℝP² → ℝ` — and the tree itself proves nonconstant ones exist
(`RankTwo.tauModuliRP2_nonconstant`).  So the ingredient this certificate told the reader to "attack
FIRST" would, if true, refute `cor:qubit-classification`: **the very row this same certificate
covers.**

★★ **Name the three defect kinds together, because the tests that catch them are different.**
  * FALSE — row 22's `lem:orientation` statement: refutable by counterexample.
  * VACUOUS — row 36(i)'s `exists_peirce_exchange`: provable, moves nothing.  Caught by the
    inert-hypothesis test applied to the *gap*.
  * SELF-DEFEATING — this one: an ingredient whose truth kills its own conclusion.  Caught by
    neither of the above.  **The test is: assume the gap statement and check it does not contradict
    the row it feeds.**  One step, and it would have caught this immediately.

★ A second defect in the same statement, which the file's own prose asked for and the Lean did not
carry: `a` and `b` must be **non-scalar**.  For `a = t • 𝟙` every unitary diagonalizes it, so no frame
is determined — which is precisely why the article sets `t_a = 0` at scalars, as this file says at its
own lines 37–40.  A statement contradicting its own file's prose, in a file that had already retracted
one false statement.

**THE CORRECT IDIOM WAS ELEVEN LINES FROM A THEOREM THIS FILE CITES.**
`Necessity.n2_sp_eq_twistSeq_frame` takes `a = adU U (diagFamily r)` — "`a` is a `U`-conjugate of a
diagonal", which is what "`U` presents `a`'s frame" means — and this certificate's *own* row-30
statement uses that idiom correctly.  Two statements in one file disagreed about how a frame is
presented, and the load-bearing one had the wrong one.

**THE UNDERLYING MATHEMATICS IS TRUE AND CHEAP, so the pricing survives.**  A non-scalar Hermitian
`2×2` has two distinct eigenvalues, hence one-dimensional eigenspaces; a Hermitian `b` commuting with
it preserves each, so shares its frame.  The real remaining step, which the first version did not
isolate: **`P`-compatibility ⟹ matrix commutation** for an arbitrary `P`, transportable through
`n2_sp_eq_twistSeq_frame`.
★ **Do not price that as a build without checking Mathlib first**: simultaneous diagonalization of
commuting symmetric operators is there —
`Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean:110` `directSum_isInternal_of_commute` and
`:120` `iSup_iInf_eq_top_of_commute` (v4.28.0, read at source).  Flagged because "Mathlib lacks X" has
been wrong four times here.
★ **And do NOT reach for the tree's `HermitianMat.eq_diagonal_of_commute_hermitian`**: its hypothesis
is commuting with *every* Hermitian (the commutant of the whole algebra), strictly stronger than
commuting with one non-scalar `a`.  Related machinery, wrong shape.

Restated below with the diagonalizing idiom and non-scalar hypotheses.

★★★ **AND NOW PROVED, ARC-8 block 8.1(a) — this is no longer a gap.**  Kept in the file, with its
`sorry` replaced by the tree's theorem, because the retraction above is the content: the same
proposition that was self-defeating in one presentation is true and cheap in another, and a reader
checking that claim should be able to see both in one place.  The `sorry` count of this file drops
by one for a reason that is *not* new mathematics. -/
theorem frame_param_eq_of_compatible
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
    {r s : Fin 2 → ℝ} (hr : ∀ i, r i ≤ 0) (hs : ∀ i, s i ≤ 0)
    (hrne : r 0 ≠ r 1) (hsne : s 0 ≠ s 1)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (hcomm : P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r))
        (Necessity.adU (V : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily s))
      = P.sp (Necessity.adU (V : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily s))
        (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r))) :
    Necessity.n2FrameTwist P hS2 U = Necessity.n2FrameTwist P hS2 V :=
  Necessity.n2FrameTwist_eq_of_compatible P hS2 hr hs hrne hsne U V hcomm

/-! ### The row itself, stated at the article's generality

`prop:n2-sufficiency` asks for a `SequentialProductOn` structure built from an arbitrary continuous
`t : ℝP² → ℝ`.  The existence statement below is the article's assertion; the construction plus its
seven clauses is the gap. -/

/-- **NO LONGER A GAP — `prop:n2-sufficiency` is FORMALIZED** (ARC-8 block 8.1(b), both passes).
Every continuous `t : ℝP² → ℝ` is realized by an S1–S7 product with S2.

The `agrees` clause is what makes this the article's statement rather than a bare existence claim:
the product must be the twisted product with parameter read off the left argument's frame. -/
theorem exists_sequentialProduct_of_continuous_moduli (t : C(RankTwo.RP2, ℝ)) :
    ∃ P : SequentialProductOn (HermitianMat (Fin 2) ℂ), P.FirstArgContinuous ∧
      ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (r : Fin 2 → ℝ) (b : HermitianMat (Fin 2) ℂ),
        (∀ i, r i ≤ 0) → IsEffect b →
        P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b
          = HermitianMat.twistSeq (t (RankTwo.blochFrame (Projectivization.mk ℂ
              (WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0))
              (col_ne_zero U))))
            (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b :=
  ⟨RankTwo.n2SequentialProduct t, RankTwo.n2SequentialProduct_firstArgContinuous t,
    fun U r b _ _ => RankTwo.n2Sp_eq_twistSeq_at_frame t U r b⟩

/-! ### `cor:qubit-classification` (row 35): the bijection

Injectivity is the cheap half and is nearly in reach: two continuous `ℝP²` functions inducing the
same product agree, because `n2FrameTwist` recovers the parameter at every frame
(`Necessity.n2_sp_eq_twistSeq_frame`, in-tree).  Surjectivity is rows 32/33/34 assembled, of which
only 34's constructed quotient function is missing.  So the honest price of row 35 is
**row 30 plus row 34**, and it should be attempted only after both. -/

/-- **GAP — the classification map is a bijection.**  Stated as a two-sided correspondence rather
than as `Function.Bijective` of a named map, because the map itself cannot be written down until
row 34's `ℝP² → ℝ` object exists. -/
theorem qubit_classification
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous) :
    ∃! t : C(RankTwo.RP2, ℝ),
      ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ),
        t (RankTwo.blochFrame (Projectivization.mk ℂ
            (WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)) (col_ne_zero U)))
          = Necessity.n2FrameTwist P hS2 U :=
  RankTwo.exists_unique_qubitModuli P hS2

end WallCertificate
