/-
WALL CERTIFICATE — `thm:quaternionic`  (row 20, PARTIAL)
Date: 2026-08-09, ARC-7 block 7.5.  Tag `paperA-arc7-cp1`.  Pin: main.tex blob 205fdf5a.

WHAT THE ARTICLE ASSERTS
  On H_n(H), n >= 3: Theta_r = id, so a . b = Q_{sqrt a} b.

WHAT IS IN THE TREE
  `MasterTheorem.luders_quaternionic_produced` — the row at SKELETON level, with
  Z(H) cap Im H = {0} computed.  There is NO concrete quaternionic carrier.

THE OBSTRUCTION, CONFIRMED AT SOURCE (not inherited)
  Mathlib DOES have quaternions (`Quaternion`, Mathlib/Algebra/Quaternion.lean), so that is not
  the obstacle — a point worth stating because "Mathlib lacks X" has been wrong four times on this
  project.  The obstacle is that this tree's field-general `Gen` layer is written for `RCLike k`,
  and H can NEVER be `RCLike`:
    * `RCLike` extends `DenselyNormedField`, hence COMMUTATIVE, while H is not;
    * `RCLike.re_add_im_ax` demands a TWO-dimensional real decomposition z = re z + (im z) I,
      while H is four-dimensional over R.
  That is an impossibility, not an absent instance.  Consequence: no amount of work makes the `Gen`
  machinery instantiate at H.

  ★ SCOPE, and this is the correction the ARC-6 cold review made: the argument above blocks the
  `Gen` LAYER's reuse at H.  It does NOT block the ROW, which remains reachable by another route.
  The row therefore stays PARTIAL, and the status word stays inside the FORMALIZED/PARTIAL/ABSENT
  taxonomy the coverage count depends on — "BLOCKED" is a fourth term outside it, and row 32's own
  note forbids that vocabulary.  Put obstructions in prose, not in status words.

THE FORCED ROUTE
  H_n(H) embeds in H_{2n}(C) as the fixed points of a conjugate-linear involution — the quaternionic
  structure carried by the involution instead of by a scalar field.  Below is that route's first
  step, stated in Lean: the involution on H_{2n}(C) whose fixed points are the quaternionic
  Hermitian matrices.  The ARC-7 orders required that a certificate for this row CONTAIN the
  embedding rather than merely name it, and that is what the statements below are.

  Note the tree already has `Hermitian/Symplectic.lean` and `Hermitian/QuatQuadRep.lean`, so the
  symplectic vocabulary this route needs is partly present; the certificate's greps below record
  exactly what is and is not there.

ATTACK EVIDENCE
  Not attempted in ARC-6 (priced only) and not attempted in ARC-7 (budget).  So this records an
  UNATTEMPTED price for the route, and a CONFIRMED-at-source impossibility for the alternative
  route.  Those are different grades of evidence and are labelled separately.

ABSENCE CLAIMS AND THEIR SCOPE
  * "no concrete quaternionic carrier for the sequential product":
      grep -rn 'Quaternion' RadicalRelativity/ -> hits only in Hermitian/QuatQuadRep.lean and
      Hermitian/Symplectic.lean (quadratic-representation and symplectic lemmas); no
      `SequentialProductOn (HermitianMat _ Quaternion)` anywhere.  Whole first-party tree incl.
      Vendor/, 2026-08-09.
  * "H is not `RCLike`": this is a statement about Mathlib's class definition, verified by reading
      Mathlib/Analysis/RCLike/Basic.lean — `class RCLike extends DenselyNormedField`, plus the
      `re_add_im_ax` field.  Scope: Mathlib v4.28.0.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Hermitian.Symplectic

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder

/-! ### Step 1 of the forced route: the involution whose fixed points are `H_n(ℍ)`

For `J` the standard symplectic form on `ℂ^{2n}`, the map `A ↦ J (conj A) Jᵀ` (equivalently
`A ↦ -J Ā J`) is a conjugate-linear involution of `H_{2n}(ℂ)` whose fixed points are exactly the
quaternionic Hermitian matrices.  This is the object the row needs and the tree does not have. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **GAP.**  The symplectic involution on complex Hermitian matrices.  The `sorry` is the
Hermitian-ness of the image, i.e. that the construction lands in `HermitianMat` at all. -/
noncomputable def quatInv (J : Matrix n n ℂ) (A : HermitianMat n ℂ) : HermitianMat n ℂ :=
  ⟨J * (A.mat.map (starRingEnd ℂ)) * Jᵀ, by sorry⟩

/-- **GAP.**  It is an involution when `J` is a symplectic form (`Jᵀ = -J`, `JᴴJ = 1`). -/
theorem quatInv_involutive (J : Matrix n n ℂ) (hJ : Jᵀ = -J) (hJU : Jᴴ * J = 1)
    (A : HermitianMat n ℂ) : quatInv J (quatInv J A) = A := by
  sorry

/-- **GAP — the embedding's defining property.**  The fixed points of the involution are a real
subspace closed under the Jordan product, i.e. a Jordan subalgebra: this is what makes them
`H_n(ℍ)`.  Stated as closure under the symmetrized product, which is the tree's vocabulary
(`HermitianMat.symmMul`). -/
theorem quatInv_fixed_closed (J : Matrix n n ℂ) (hJ : Jᵀ = -J) (hJU : Jᴴ * J = 1)
    (A B : HermitianMat n ℂ) (hA : quatInv J A = A) (hB : quatInv J B = B) :
    quatInv J (HermitianMat.symmMul A B) = HermitianMat.symmMul A B := by
  sorry

/-- **GAP — what the row then needs.**  That an S1–S7 product on the fixed-point subalgebra
extends to / restricts from one on `H_{2n}(ℂ)`, so the in-tree complex classification transfers.

★ This is the step that decides whether the route is cheap or not, and it is the one this
certificate is least confident about: the complex classification gives `a^{1/2+it} b a^{1/2−it}`,
and the transfer must force `t = 0` on the fixed points.  The article gets `Θ_r = id` from
`Z(ℍ) ∩ Im ℍ = {0}` (computed in-tree at skeleton level), so the mechanism exists; whether it
survives the embedding is not known here.  Attack this before building the involution. -/
theorem quaternionic_row_via_embedding : True := by
  -- Not statable without the fixed-point subalgebra as a type; recorded as a vocabulary wall.
  trivial

end WallCertificate
