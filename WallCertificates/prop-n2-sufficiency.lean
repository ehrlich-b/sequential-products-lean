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
  directions.  Treat the S2-near-scalars claim as the part most likely to be mispriced, and attack
  the "compatible ==> same frame" lemma FIRST, since if that is cheap the rest is mechanical.

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

/-! ### The load-bearing missing fact, isolated

If this is cheap, row 30 is mechanical; if it is hard, row 30 is hard.  Attack it first. -/

/-- **GAP — the step row 30's S5 and S7 turn on.**  Two compatible effects of `H₂(ℂ)` have the same
spectral frame, hence are assigned the same parameter by any frame function.

Stated with `Necessity.n2FrameTwist`'s indexing (frames as unitaries) because that is the tree's
vocabulary; the article states it with frames as unordered atom sets. -/
theorem frameRay_eq_of_compatible
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
    {a b : HermitianMat (Fin 2) ℂ} (ha : IsEffect a) (hb : IsEffect b)
    (hcomm : P.sp a b = P.sp b a)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (hUa : a = Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) a)
    (hVb : b = Necessity.adU (V : Matrix (Fin 2) (Fin 2) ℂ) b) :
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
              (by sorry))))
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
            (WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)) (by sorry)))
          = Necessity.n2FrameTwist P hS2 U := by
  sorry

end WallCertificate
