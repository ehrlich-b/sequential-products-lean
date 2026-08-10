/-
WALL CERTIFICATE — `thm:quaternionic`  (row 20, PARTIAL)
Date: 2026-08-09, ARC-7.  Pin: main.tex blob 205fdf5a.

★★★ THIS CERTIFICATE WAS REFUTED IN FULL ON THE DAY IT WAS WRITTEN, BY THE CERTIFICATE-REFUTATION
REVIEW, AND IT IS REWRITTEN RATHER THAN PATCHED.  What follows first is the retraction, because it
is the most useful thing in the file.

WHAT THE FIRST VERSION CLAIMED
  * "There is NO concrete quaternionic carrier."
  * Three `sorry`s presented as the forced route's first step: a symplectic involution `quatInv` on
    H_{2n}(C), its involutivity, and closure of its fixed points under the Jordan product.
  * A fourth entry, `quaternionic_row_via_embedding : True`, with the comment "Not statable without
    the fixed-point subalgebra as a type; recorded as a vocabulary wall."

EVERY ONE OF THOSE IS WRONG, AND ALL OF IT WAS IN `RadicalRelativity/Hermitian/Symplectic.lean` —
THE FILE THIS CERTIFICATE IMPORTED ON ITS OWN IMPORT LINE.
  * `HermitianMat.quatConj` (Symplectic.lean:70) is `symplecticJ * (A.map conj) * symplecticJᵀ` —
    character-for-character the `quatInv` body the certificate wrote as a gap.
  * `HermitianMat.quatConj_isHermitian` (:322) is the def-level `sorry`.
  * `HermitianMat.quatConjH` (:340) is the whole definition.
  * `HermitianMat.quatConj_involutive` (:130) is the second `sorry`.
  * `HermitianMat.IsQuaternionic.symmMul` (:196) is the third.
  * `HermitianMat.QuatCarrier n` (:455) IS the fixed-point subalgebra AS A TYPE, with
    `instance : OrderUnitSpace (QuatCarrier n)` (:462) whose own docstring reads "This is the carrier
    the `H_n(ℍ)` row's `SequentialProductOn` will live on."  There is no vocabulary wall.
  * `RadicalRelativity/Hermitian/QuatQuadRep.lean:105` already builds
    `quatQuadRep … : QuatCarrier n →ₗ[ℝ] QuatCarrier n`, and its line 100 says "This is the object
    the `H_n(ℍ)` row's `theta` would be built from."

  So the certificate's "first step of the forced route" was BEHIND where the tree already stood.

ROOT CAUSE, and the transferable rule is narrower than the one already on the record.  The standing
rule is "grep the tree before claiming absence", and I did grep — for `Quaternion`, the Mathlib type
name.  The tree's layer is named `quatConj` / `QuatCarrier` / `quatQuadRep`, so an accurate grep
supported a false claim.  THE NARROWER RULE:
    grep -n "^def \|^theorem \|^instance \|^abbrev " <the file you are importing>
  before writing a gap for anything in that file's subject area.  An import line is a declaration
  that the file is relevant; reading its declaration list costs one command.

  This is the SIXTH false absence claim on this project, and the second in which the grep was
  accurate and the inference was not.

A SECOND DEFECT, WORSE THAN VAGUENESS: THE FIRST VERSION'S `quatInv` `sorry` WAS FALSE.
  It quantified over an arbitrary `J : Matrix n n C` with NO hypotheses and asserted `J * conj A * Jᵀ`
  is Hermitian.  False at `n := Unit`, `J := !![1 + I]`, `A := 1`.  And — the reviewer's sharper
  point — even under the hypotheses the neighbouring theorems carried (`Jᵀ = -J`, `Jᴴ J = 1`) the
  obligation still fails, because both conditions are invariant under a unit phase: for `|c| = 1`
  and `J₀` the standard real form, `J := c • J₀` satisfies both, yet `quatInv J A = c² · quatConj A`,
  which at `c = e^{iπ/4}`, `A = 1` is `i · 1`, anti-Hermitian.  **`Jᵀ = -J` together with `JᴴJ = 1`
  does not pin down a symplectic form; the convention needed is `J` REAL** — which `symplecticJ` is,
  and which `quatConj_involutive`'s in-tree proof uses explicitly.

WHAT THE ROW ACTUALLY NEEDS, now that the embedding layer is known to exist
  Not the involution, not the carrier, not the Jordan closure, not `theta`'s raw material.  What is
  absent is the TRANSFER: that an S1–S7 product on `QuatCarrier n` forces `Theta_r = id`, i.e. that
  the complex classification's parameter `t` is pinned to `0` on the fixed points.  The article gets
  this from `Z(H) ∩ Im H = {0}`, which is computed in-tree at skeleton level
  (`MasterTheorem.luders_quaternionic_produced`).  Whether that mechanism survives the embedding is
  the open question, and it is the ONLY one this certificate can honestly name.

  Stated below.  Note it is now statable, precisely because `QuatCarrier` exists.

THE STANDING OBSTRUCTION IS UNCHANGED AND WAS ALWAYS CORRECT
  The `Gen` layer cannot reach H: `RCLike` extends `DenselyNormedField` (commutative) and its
  `re_add_im_ax` demands a two-dimensional real decomposition, while H is noncommutative and
  four-dimensional.  An impossibility, not a missing instance.  The reviewer confirmed this claim is
  both accurate and correctly scoped — it is the one thing the first version got right.  ★ Scope, as
  before: this blocks the `Gen` LAYER, not the row; status words stay inside the
  FORMALIZED/PARTIAL/ABSENT taxonomy and the obstruction goes in prose.

ABSENCE CLAIMS AND THEIR SCOPE (rewritten; the first version's were false)
  * "the transfer of the classification through the embedding is absent":
      grep -rn 'SequentialProductOn (HermitianMat.QuatCarrier\|SequentialProductOn (QuatCarrier' RadicalRelativity/
      -> no hits, whole first-party tree incl. Vendor/, 2026-08-09.  So the CARRIER exists and no
      product is defined on it.  That is the honest statement of where the row stands.
    ★★★ HALF-DISCHARGED 2026-08-09 (ARC-8 block 8.3): `HermitianMat.quatLuders` IS a
    `SequentialProductOn (QuatCarrier n)` — the Lüders product, with S1 and S3-S7 — and
    `HermitianMat.quatSp_eq_quatQuadRep` identifies it with the tree's own `quatQuadRep`, i.e. with
    the article's `a . b = Q_{sqrt a} b`.  So the grep above is now FALSE and the sentence after it
    is superseded: the carrier has a product.
    ★ NOTHING NEW WAS PROVED ABOUT S1-S7 to get it.  Every axiom is the ambient one at t = 0 read
    through the subtype coercion; the only content is closure of the quaternionic set under
    Q_{sqrt a}, and that was already in the tree (`IsQuaternionic.quadRep`, which is
    `IsQuaternionic.cfc_of_effect` plus `IsQuaternionic.conj`).  This is the SUFFICIENCY direction.
    ★★ THE ROW'S OWN STATEMENT IS UNTOUCHED.  `thm:quaternionic` says an ARBITRARY S1-S7 product on
    H_n(H), n >= 3, MUST be this one (Theta_r = id).  That is the transfer, it is still the only
    honest residue, and the gap below is still a gap.
  * "H is not `RCLike`": Mathlib v4.28.0, `Mathlib/Analysis/RCLike/Basic.lean` — read at source.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Hermitian.QuatQuadRep

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

/-! ### What the tree already has — compiled here so the retraction above is checkable

None of these is a gap.  They are stated to make the refutation self-evidencing: a reader who
suspects the retraction is over-generous can see the declarations discharge immediately. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The symplectic involution — **in the tree**, not a gap. -/
noncomputable example (A : HermitianMat (n ⊕ n) ℂ) : HermitianMat (n ⊕ n) ℂ :=
  HermitianMat.quatConjH A

/-- Its involutivity — **in the tree**, not a gap. -/
example (A : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    HermitianMat.quatConj (HermitianMat.quatConj A) = A :=
  HermitianMat.quatConj_involutive A

/-- The fixed-point subalgebra **as a type**, with its order-unit structure — so the "vocabulary
wall" the first version recorded does not exist. -/
noncomputable example : OrderUnitSpace (HermitianMat.QuatCarrier n) := inferInstance

/-! ### The one genuine gap

Now statable, because `QuatCarrier` is a type with an `OrderUnitSpace` instance. -/

/-- **GAP — the actual content of row 20.**

★★★ **RESTATED 2026-08-10 after the certificate-refutation review; the previous statement was
VACUOUS and the review compiled the proof.**  Its conclusion ended `… ∨ True`, discharged by
`Or.inr trivial`, and it stayed provable with **every hypothesis deleted** — `hS2` and `hrank` both
inert.  Worse, even the left disjunct was not the row's content: the Lüders product is not
commutative, so `P.sp a b = P.sp b a` is no approximation to `Θ_r = id`.
  ★★ **This is the file that was "REFUTED IN FULL and rewritten rather than patched" — and the rewrite
  reinstalled the directory's already-retracted `True`-placeholder defect in disguise, behind a
  disjunction instead of on its own.**  A `∨ True` is a `True`.
  ★ **And I refreshed this file's header earlier in this arc without reading its gap statement.**
  Updating a certificate's prose is not re-attacking its gap; the ARC-8 rule about attack evidence
  means the STATEMENT, not the header.
  ★ The restatement is now expressible because `HermitianMat.quatSp` / `quatLuders` landed this arc
  (block 8.3), and `quatSp_eq_quatQuadRep` identifies it with `Q_{√a}` — so the row's own conclusion
  `a · b = Q_{√a} b` can be written directly.  ★ CORRECTED 2026-08-10 (diff audit): I wrote that `hS2` and `hrank`
  are "now load-bearing rather than decorative: without rank ≥ 3 the article's conclusion is false (rank
  two is row 30's frame-dependent family)".  **That justification is an unbanked analogy across
  carriers.**  Row 30's family lives on `HermitianMat (Fin 2) ℂ`; the rank-two *quaternionic* carrier is
  `QuatCarrier` at `Nat.card n = 2`, and no twist family is constructed there in-tree.  Honest status:
  both hypotheses are carried **because the article carries them**, and neither is shown load-bearing.

Any S1–S7 product with S2 on the quaternionic carrier
is Lüders: the twist parameter is pinned to zero on the fixed points of the symplectic involution.

The article's mechanism is `Z(ℍ) ∩ Im ℍ = {0}`, computed in-tree at skeleton level; whether it
survives the embedding is the open question. -/
theorem quaternionic_luders
    (P : SequentialProductOn (HermitianMat.QuatCarrier n)) (hS2 : P.FirstArgContinuous)
    (hrank : 3 ≤ Nat.card n) :
    ∀ a b : HermitianMat.QuatCarrier n, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.quatSp a b := by
  sorry

end WallCertificate
