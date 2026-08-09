/-
WALL CERTIFICATE — the differential trio:
  `lem:coalescence`   (row 16, PARTIAL)
  `lem:homomorphism`  (row 17, PARTIAL)
  `prop:stabilizers`  (row 18, PARTIAL)
Date of this REWRITE: 2026-08-09, ARC-7.  Pin: main.tex blob 205fdf5a.

★★★ THIS CERTIFICATE'S FIRST VERSION WAS SUBSTANTIALLY REFUTED, ON THE DAY IT WAS WRITTEN, BY THE
COLD REVIEW SENT AT IT.  It is rewritten rather than patched, and the retraction is the content.

WHAT THE FIRST VERSION CLAIMED, AND WHY EACH CLAIM IS WRONG

  (1) "row 18: the four stabilizer representations are stated as a constructor's CONCLUSION
      (`StabilizerCoupling`) rather than constructed from Theta."  FALSE.
      `Necessity/StabilizerInstance.lean` builds every piece from `(P, hS2, hjord)`: `rhoField`
      (the block compression), `dChiStab` landing in the stabilizer via `dChi_mem_blockSkew`, the
      carrier `blockSkewSubmodule`, `diagonalHomSetup` with `rho_skew` and `coalescence_diff`
      PROVED, and `stabilizerCoupling` producing the whole structure.  Its own docstring says it
      "produces the coupling".  And `PhaseAnchor.lean`'s `complex_perFrame_concrete` proves
      `∃ tF, ∀ i j r, rho_ij(dchi r) = (tF·(r_i − r_j)) • rotJ` from an ARBITRARY product,
      rank-free above 3 — the article's `z ↦ i(theta_i − theta_j)z` in Lie-algebra form.

  (2) "row 18's remaining content needs the stabilizer group as a Lie group with an identity
      component, which the tree does not have" — parked behind `True`.  FALSE, AND THE STATEMENT
      IS NOW PROVED IN THE TREE: `Necessity.tvalCoef_realized_by_stabilizer` and
      `Necessity.stabilizer_group_action_complex`.  `torusU t r` is `diagonal (e^{i t r_k})`;
      `torusU_fixes_frameProj` says it fixes every frame projection, i.e. it IS in the frame
      stabilizer; `torusU_block` says it rotates the `(i,j)` block by the phase difference.  Four
      lines.  No Lie-group vocabulary was needed to say the thing I claimed could not be said.

  (3) "row 16: the tree has a differential shadow in strong pointwise form; the gap is that the
      shadow IS the cited lemma's differential."  FALSE, and understated by a whole level.
      `MasterTheorem/Coalescence.lean`'s `coalescence_J2q` is the article's SECOND clause, proved
      at the **Theta (group) level, at abstract generality**; `coalescence_block` is the FIRST
      clause, likewise.  Neither is a differential shadow, and no identification is needed.  It is
      instantiated too: `coalescenceSetup` builds the structure from an arbitrary product and PROVES
      the three Faraut–Korányi fields at the concrete carrier.

  (4) ★★★ "the tree has NO Jordan/EJA class at all, so 'the article's generality' is not currently a
      statable hypothesis.  That is a VOCABULARY wall."  FALSE — and this is the TENTH false absence
      claim on this project.  `MasterTheorem/Interface.lean`'s `structure ComparisonSetup` carries a
      Jordan product `jordan : J →ₗ[ℝ] J →ₗ[ℝ] J`, a unit `e`, `jordan_comm`, `jordan_unit`, a rank
      `n` with `rank_ge : 3 ≤ n`, **a Jordan frame `p : Fin n → J`** (its docstring: "a complete
      orthogonal system of primitive idempotents"), a cone `nonneg`, `Inv`, `aOf`, and
      `Theta : J → (J ≃ₗ[ℝ] J)` with `Theta_unital`/`Theta_orderIso`/`Theta_jordan`.  The article's
      generality is therefore **statable AND used** — row 16's two clauses are proved over it.
      My grep pattern (`class.*Jordan|structure.*Jordan|EuclideanJordan|class EJA`) structurally
      cannot see it: the structure is named `ComparisonSetup` and the Jordan product is a FIELD
      named `jordan`.  **Same failure mode as the quaternionic certificate's `Quaternion` grep, one
      file over in the same directory, on the same day.**

      ★ OVER-CORRECTION GUARD, from the reviewer and preserved deliberately: this is NOT an EJA
      class.  `Interface.lean` says outright that it "does not encode the JB-algebra premises (the
      Jordan identity, formal reality, the cone-of-squares reading of `nonneg`)".  Accurate wording:
      rows 16/17 at the article's generality ARE statable, and 16 is proved there; what is absent is
      an axiomatization that would make the cited vIR/FK fields derivable rather than carried.

  (5) "the exp-generator route bypasses differentiation entirely."  FALSE as written.
      `Necessity/CoalescenceDiff.lean` — the very file where `dChi_kills_corner` lives —
      differentiates the curve `t ↦ exp(t • A) x`, and that curve IS chi-tilde
      (`chiTilde_eq_exp_dChi`).  What the tree never does is *state* a `HasDerivAt` about Theta or
      chi.  Keep the nuance, drop the "bypasses differentiation" clause.
      ★ The first version also recorded its `HasDerivAt|fderiv` grep as scoped to `Necessity/` while
      writing "-> no hits"; tree-wide that pattern hits ten or more files.

  (6) A recorded grep misreported its own output: the Jordan grep was written as "-> no hits (whole
      first-party tree incl. Vendor/)" and in fact returns five or more hits, all docstring prose.
      The substantive reading (no Jordan *class declaration*) survives; the recorded result did not.
      This is the exact thing the README says trains readers to ignore verification recipes.

WHAT ACTUALLY REMAINS, after all of the above

  row 16.  A citation/axiomatization gap, not an identification gap: the abstract interface carries
    `Theta_jordan` (van Imhoff–Roelands) and the FK Peirce facts as FIELDS.  Closing it means
    encoding the JB-algebra premises so those become derivable.  That is real work and it is the same
    boundary `prop:theta` carries — i.e. it sits close to the pre-registered-external line.

  row 17.  Generality only, as before; the hyperplane clause closed in ARC-6.

  row 18.  ★ ONLY THE CONVERSE, for the C row: that a frame-fixing unitary MUST be such a torus
    element ("the stabilizer is exactly `T^n`, identity component `T^{n-1}`").  The reviewer checked
    the scope: grepping `fixes_frameProj|frameStabilizer|stabilizes.*frame|isDiag_of_adU|adU_frameProj`
    over `RadicalRelativity/`, every hit is Theta/chi-tilde *fixing* the frame and none is the
    converse.  It is **writable today** with `adU`/`frameProj`/`Matrix.unitaryGroup`, no new
    vocabulary, and looks like a short matrix argument.  Plus the R/H/O rows, still bankable.

ATTACK EVIDENCE
  Rows 16 and 18 were NOT attempted before this review; their prices above are the review's, verified
  at source, and the two theorems it wrote are now in the tree.  The `True` placeholders the first
  version used are gone: a `True` placeholder recorded awkwardness and got read as depth, which is
  the limiting case of the VACUOUS gap defect already on record for row 36(i).

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Necessity.FrameConstancy
import RadicalRelativity.MasterTheorem.Coalescence

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace Necessity MasterTheorem

/-! ### The refutation, made self-evidencing

None of these is a gap.  They compile, so a reader who suspects the retraction above is
over-generous can check it here rather than take it on trust. -/

/-- Row 18's former "unstatable" content — **in the tree**. -/
example {N : ℕ} (P : SequentialProductOn (HermitianMat (Fin N) ℂ)) (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (i j : Fin N) (hij : i ≠ j) (r : Fin N → ℝ) (z : ℂ) :
    adU (torusU (tvalCoef P hS2 hjord i j) r) (blockHerm i j z)
      = blockHerm i j (Complex.exp ((↑(tvalLm P hS2 hjord i j r) : ℂ) * Complex.I) * z) :=
  tvalCoef_realized_by_stabilizer P hS2 hjord i j hij r z

/-- Row 16's second clause at the article's own abstract generality — **in the tree**, and the
existence of this statement is what refutes the "vocabulary wall". -/
example {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    (C : CoalescenceSetup J) {a b : J} {i j : Fin C.n}
    (ha : C.Inv a) (hsc : C.ScalarOn i j a) (hb : C.J2 i j b) :
    C.Θ a b = b :=
  C.coalescence_J2q ha hsc hb

/-! ### The gap this file called its one genuine one — CLOSED, and the certificate went stale
inside the same arc

★★★ **RETRACTION 2026-08-09, ARC-8 block 8.0/8.2, and the interesting part is the timing.**  The
statement below was written here as row 18's single remaining stated gap, judged "writable today …
a short matrix argument".  The judgement was right and it was acted on **the same day**:
`Necessity.offdiag_eq_zero_of_fixes_frameProj` is this statement, with the same hypotheses and the
same conclusion, and it has been in the tree since ARC-7.  The `sorry` below survived only because
nobody re-read the file after the tree caught up with it.

★★★ **AND ARC-8's OWN ORDERS INHERITED THE STALENESS.**  `LEDGER.md`'s block 8.2 opens with "row
18's ℂ converse (`frame_stabilizer_is_torus`, stated ready in
`WallCertificates/differential-trio.lean`, priced a short matrix argument)" — a work order for
something already done, written from *this file* instead of from the tree.  The rule the arc adopted
("attack evidence must be from THIS ARC") was aimed at exactly this and was violated by the document
that states it.

★ **TRANSFERABLE RULE, and it is not the grep rule.**  The grep rule says an accurate grep is
evidence about a string.  This is one ring further out: **a certificate is evidence about the tree
at the moment it was written, and a work order derived from a certificate inherits that timestamp.**
The first move when opening a block is not to read the certificate — it is to check the certificate
against the tree, because the certificate is the thing most likely to be out of date.  A certificate
whose gap has closed is worse than a prose price: it is a prose price wearing a compiler's badge. -/

/-- **NO LONGER A GAP** — the frame stabilizer is exactly the diagonal subgroup.  Kept, with the
`sorry` replaced by the tree's theorem, so the retraction above is checkable here. -/
theorem frame_stabilizer_is_torus {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : Uᴴ * U = 1)
    (hfix : ∀ k, adU U (frameProj k) = frameProj k) :
    ∀ i j, i ≠ j → U i j = 0 :=
  Necessity.offdiag_eq_zero_of_fixes_frameProj hU hfix

end WallCertificate
