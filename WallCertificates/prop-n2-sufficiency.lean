/-
WALL CERTIFICATE — `prop:n2-sufficiency`  (row 30)  and  `cor:qubit-classification`  (row 35)
Date: 2026-08-09, ARC-7 block 7.5.  Tag `paperA-arc7-cp1`.  Pin: main.tex blob 205fdf5a.
Row status on this date: 30 = ABSENT, 35 = ABSENT.

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
  * "'compatible effects share a spectral frame' is not stated":
      grep -rn 'Compatible.*frame\|frame.*compatible' RadicalRelativity/ -> no hits with that
      content; `compatible_ortho`/`compatible_add`/`compatible_sp` are the S4/S6/S7 axiom fields,
      not this lemma.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Necessity.FrameConstancy
import RadicalRelativity.RankTwo.Bloch

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

Restated below with the diagonalizing idiom and non-scalar hypotheses. -/
theorem frame_param_eq_of_compatible
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
    {r s : Fin 2 → ℝ} (hr : ∀ i, r i ≤ 0) (hs : ∀ i, s i ≤ 0)
    (hrne : r 0 ≠ r 1) (hsne : s 0 ≠ s 1)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (hcomm : P.sp (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r))
        (Necessity.adU (V : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily s))
      = P.sp (Necessity.adU (V : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily s))
        (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r))) :
    Necessity.n2FrameTwist P hS2 U = Necessity.n2FrameTwist P hS2 V := by
  sorry

/-! ### The row itself, stated at the article's generality

`prop:n2-sufficiency` asks for a `SequentialProductOn` structure built from an arbitrary continuous
`t : ℝP² → ℝ`.  The existence statement below is the article's assertion; the construction plus its
seven clauses is the gap. -/

/-- **GAP — `prop:n2-sufficiency`.**  Every continuous `t : ℝP² → ℝ` is realized by an S1–S7
product with S2.

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
            (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) b := by
  sorry

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
          = Necessity.n2FrameTwist P hS2 U := by
  sorry

end WallCertificate
