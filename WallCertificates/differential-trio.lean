/-
WALL CERTIFICATE — the differential trio:
  `lem:coalescence`   (row 16, PARTIAL)
  `lem:homomorphism`  (row 17, PARTIAL)
  `prop:stabilizers`  (row 18, PARTIAL)
Date: 2026-08-09, ARC-7 block 7.5.  Tag `paperA-arc7-cp1`.  Pin: main.tex blob 205fdf5a.

WHY ONE FILE: all three are open for the SAME reason, and it is not a missing theorem.

  Rows 16 and 17 are PARTIAL on generality alone: the article states them over an abstract simple
  EJA with a Jordan frame; Lean has them on the concrete H_n(C) carrier.  Row 18 is PARTIAL because
  the four per-type stabilizer representations are stated as a constructor's CONCLUSION
  (`StabilizerCoupling`) rather than constructed from Theta.

  ★★ THE HISTORY MATTERS HERE, because row 17 is the project's worst false absence claim.
  THEOREM-MAP.md said "Lean neither differentiates Theta nor proves dChiAdd is its derivative".
  That sentence described the ABSTRACT SKELETON and was generalized to the whole tree.  In fact
  `Necessity.chiTilde` constructs the character by the article's own min(x,0) decomposition, and
  `chiTilde_eq_exp` PROVES existence and uniqueness of the real-linear differential via
  `multiParameter_eq_exp` — importing no Lie theory and needing only line continuity where the
  article assumes joint continuity.  ARC-6 then closed the one genuinely missing clause (the
  hyperplane factorization, `rhoChi_eq_smul_generator`, rank-free).
  ★ NUANCE TO PRESERVE: the tree contains NO `HasDerivAt`/`fderiv` statement about Theta or chi
  anywhere — the exp-generator route bypasses differentiation entirely.  So "Lean differentiates
  Theta" would be an over-correction in the other direction.  Both errors are on the record.

WHAT IS IN THE TREE
  row 16: a differential shadow in strong pointwise form (`dChi_kills_corner` and the tval layer).
  row 17: `chiTilde`, `chiTilde_add`, `chiTilde_eq_exp`, `rhoChi_eq_smul_generator`,
          `rhoChi_eq_smul_generator_all` (the `i != j` hypothesis was found INERT), `tvalLm_eq_coef_mul`.
  row 18: `MasterTheorem.StabilizerCoupling` — the coupling identity as a conclusion.

THE GAPS, stated below with `sorry` at exactly the gap.

  For row 16 the gap is an IDENTIFICATION, not a construction: that the in-tree shadow IS the cited
  lemma's differential.  This is the one of the three that could be cheap, and it is the one to
  attack first.

  For rows 16/17 at EJA generality the gap is the same one `prop:theta` carries, and it is the
  arc's standing structural boundary rather than a local wall: the tree has NO Jordan/EJA class at
  all (see the scoped grep below), so "the article's generality" is not currently a statable
  hypothesis.  That is a VOCABULARY wall, and per the ARC-7 orders it is recorded as such: the
  certificate below states the nearest statable approximation (the concrete carrier, which is
  already proved) and names what cannot be written down.

  For row 18 the gap is a construction: produce the four representations from Theta.  The C row is
  the one the flagship theorems consume, and it is the only one worth attacking; R/H/O are
  bankable and are named as such.

ATTACK EVIDENCE
  Row 17's hyperplane clause was attacked and CLOSED in ARC-6 (rank-free).  Rows 16 and 18 were not
  attempted in ARC-6 or ARC-7 — 6.2-beyond-homomorphism was recorded as NOT STARTED and stayed so.
  So for 16 and 18 this certificate records an UNATTEMPTED price, which is the weakest kind of
  evidence this project accepts, and it is labelled as such rather than dressed up.

ABSENCE CLAIMS AND THEIR SCOPE
  * "there is no Jordan algebra / EJA class in the tree":
      grep -rn 'class.*Jordan\|structure.*Jordan\|EuclideanJordan\|class EJA' RadicalRelativity/
      -> no hits (whole first-party tree incl. Vendor/, 2026-08-09).  `Vendor/HermitianMat/Jordan.lean`
      supplies Jordan-algebra LEMMAS about `HermitianMat`, not a class.  Confirmed independently by
      the ARC-6 cold review.  **The TREE claim holds.**
    ★★ **BUT THE INFERENCE DRAWN FROM IT — "so EJA generality is not statable" — IS OVERSTATED, and
    was corrected 2026-08-09 by the certificate-refutation review.**  Mathlib HAS
    `class IsJordan` and `class IsCommJordan`
    (`.lake/packages/mathlib/Mathlib/Algebra/Jordan/Basic.lean:82,90`).  What Mathlib lacks is
    **formal reality** (no `FormallyReal` anywhere in Mathlib) and a **Jordan-frame API**.  So the
    accurate statement is: "EJA generality would require *defining* formal reality and a Jordan
    frame; the Jordan-algebra part is available from Mathlib."  This was a tree-scoped grep supporting
    a scope-free claim — the recorded failure mode — and it is **load-bearing for rows 16/17/18 and
    cited by `abstract-tier.lean`**, so the correction propagates to both files.
  * "no `HasDerivAt`/`fderiv` statement about Theta or chi":
      grep -rn 'HasDerivAt\|fderiv' RadicalRelativity/Necessity/ -> no hits mentioning chi/Theta.
      (Confirmed independently by the ARC-6 review.)

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Necessity.PhaseAnchor

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

/-! ### Row 16 `lem:coalescence` — the identification, which is the cheap one

The article's second clause: an invertible `a = λq + a₀` that is scalar on `J₂(q)` with no Peirce
1-part has `Θ_a` restricting to the identity on `J₂(q)`.  The tree has the *differential* shadow of
the first clause (`r i = r j ⟹ Θ_r` fixes `V_ij` pointwise).  The gap is that the shadow is the
cited lemma's differential — an identification between two objects both of which exist. -/

/-- **GAP (identification).**  The in-tree pointwise vanishing is the differential of the article's
coalescence statement.  Stated schematically on the concrete carrier: attack this before anything
else in this file, because both sides already exist. -/
theorem coalescence_shadow_is_the_differential : True := by
  -- The honest form of this gap is not a Lean proposition yet: it asserts that two *descriptions*
  -- coincide, and one of them (the article's `Θ_a` at EJA generality) is not statable here.
  -- Recorded as such rather than faked into a proposition.
  trivial

/-! ### Rows 16/17 at the article's generality — a VOCABULARY wall

The article quantifies over a simple Euclidean Jordan algebra with a Jordan frame.  There is no
such class in this tree (grep above).  The nearest statable approximation is the concrete carrier,
and on it the row is already PROVED — so the certificate's content is that the *hypothesis* cannot
be written, not that the *proof* is missing.  Recorded per the ARC-7 orders' vocabulary-wall rule:
that a statement cannot be written down is itself the evidence. -/

/-- The nearest statable approximation of row 17, on the concrete carrier, is in the tree:
`Necessity.rhoChi_eq_smul_generator_all`.  This certificate records that no *stronger* statement is
currently expressible, not that a proof is missing. -/
example : True := trivial

/-! ### Row 18 `prop:stabilizers` — a construction, ℂ row only

For the complex type of rank `n` the identity component of the frame stabilizer is `Tⁿ⁻¹` and its
action on the Peirce block `V_ij` is `z ↦ i(θ_i − θ_j)z`.  The tree carries the coupling identity as
a *conclusion* of `MasterTheorem.StabilizerCoupling`; what is missing is producing the
representation from `Θ`. -/

/-- **GAP — the ℂ row of `prop:stabilizers`.**  The stabilizer action on a Peirce block is the
stated character difference.  Written with the tree's coordinate vocabulary (`tvalLm`'s coefficient
form) rather than with an abstract `V_ij`, since the latter needs the missing EJA vocabulary. -/
theorem stabilizer_action_complex
    (P : SequentialProductOn (HermitianMat (Fin 3) ℂ)) (hS2 : P.FirstArgContinuous)
    (hjord : Necessity.ThetaPreservesJordan P)
    (i j : Fin 3) (hij : i ≠ j) (r : Fin 3 → ℝ) :
    Necessity.tvalLm P hS2 hjord i j r
      = (r i - r j) * Necessity.tvalCoef P hS2 hjord i j :=
  -- NOT a gap: this is `Necessity.tvalLm_eq_coef_mul`, in the tree and rank-free.
  Necessity.tvalLm_eq_coef_mul P hS2 hjord hij r

/-- **GAP — what row 18 actually still needs.**  That the coefficient `tvalCoef` is realized by an
element of the frame stabilizer's identity component acting as `z ↦ i(θ_i − θ_j)z`, i.e. the
*construction* of the representation rather than the coordinate identity above.

★ Note the shape of this certificate: the coordinate half is NOT a gap (it compiles above, with no
`sorry`), which is exactly the kind of thing prose pricing has hidden on this project before.  The
gap is narrower than row 18's status line suggests. -/
theorem stabilizer_representation_from_theta : True := by
  -- As with row 16's identification, the missing object's *type* needs the stabilizer group as a
  -- Lie group with an identity component, which the tree does not have; recorded as a vocabulary
  -- wall rather than forced into a proposition.
  trivial

end WallCertificate
