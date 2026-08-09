/-
WALL CERTIFICATE — the frame-geometry and necessity remainder:
  `lem:frame-fix`            (row 15, PARTIAL)
  `lem:orientation`          (row 22, ABSENT)
  `lem:frame-connectivity`   (row 26, PARTIAL)
  `prop:n2-necessity` gap(b) (row 29, PARTIAL)
  `thm:qubit-boundary`       (row 31, PARTIAL)
  `cor:selectors` clause (i) (row 36, PARTIAL — clauses (ii) and (iii) are PROVED)
Date: 2026-08-09, ARC-7 block 7.5.  Tag `paperA-arc7-cp1`.  Pin: main.tex blob 205fdf5a.

PER-ROW STATUS AND GAP

  row 15 `lem:frame-fix`.  A certificate for the produced setup exists
    (`MasterTheorem/Master.lean`); the general statement — Theta_r fixes each frame atom and the
    diagonal pointwise, preserves each Peirce block, and lies in Stab(F)^0, hence L_{a(r)} is
    Peirce-block-diagonal — is open.  The last clause ("lies in Stab(F)^0") needs the stabilizer as
    a group with an identity component, the same missing vocabulary as row 18.

  row 22 `lem:orientation`.  ABSENT: an explicit complex structure J_{q,k}(x) = iz - iz* on the
    cross-coherence space X, its independence of any splitting of q, its commutation with stabilizing
    inner automorphisms, and the formula Ad_{a^{it}}|_X = exp(t(log lam - log lam_k) J_{q,k}).
    ★★ RETRACTED SAME DAY, BY MY OWN AUDIT.  This entry first said the row is "the most
    self-contained genuinely-unbuilt row", needs "no missing vocabulary", and is "THE ROW TO ATTACK
    first".  All three are wrong.  The clauses are about J restricted to X, and X is a CARRIER the
    tree does not have — the same missing vocabulary as W_n (row 29) and the Peirce subalgebra
    (row 5).  Worse, the Lean statement this file first wrote down to sidestep the carrier — the
    unrestricted `forall x, J (J x) = -x` — is FALSE, with a compiled witness
    (`frameProj_mul_orthogonal_eq_zero` below).  See the retraction at
    `orientation_complex_structure`.

  row 26 `lem:frame-connectivity`.  ★ The pricing here has already been corrected once and the
    correction must not be lost: `AdjBlock` (the article's adjacency: all but two axes fixed) is
    STRICTLY FINER than `AdjAxis` (some axis fixed).  So connectivity for the article's graph does
    NOT follow from the in-tree `adjAxis_connected` — it is strictly STRONGER, and needs every
    unitary to factor into rank-two block rotations (Givens/Jacobi), not into the three axis-fixing
    Householder factors `exists_axisFixing_factor` provides.  ★★ And a SECOND correction: an earlier
    claim that "`AdjBlock` is a superset of the article's relation" is FALSE (article frames are
    unordered atom sets).  Never repeat the superset claim.

  row 29 gap (b).  The article's conclusion is about Theta_a restricted to W_n; Lean's is the
    product-level identity `n2_sp_eq_twistSeq_frame`.  Their equivalence is the route rather than a
    proved statement.  Gap (a) — the U(2) -> S^2 fibre gap — was CLOSED in ARC-6.

  row 31 `thm:qubit-boundary`.  Parts (i) and (iii) are proved, plus the cocycle and backward
    compatibility.  Open: the bundled S1-S7 verification of the tau family, and the unimodular
    cocycle subcases.  ★ The bundled S1-S7 clause is an INSTANTIATION of row 30
    (`prop:n2-sufficiency`) at t = tau, so it should not be attacked separately — see
    WallCertificates/prop-n2-sufficiency.lean, which prices the general case and identifies
    "compatible ==> same frame" as the load-bearing missing fact.

  row 36 clause (i).  Clauses (ii) (trace-form symmetry) and (iii) (transposition covariance) are
    PROVED — (iii) closed today, ARC-7 block 7.3.  Clause (i) is Peirce exchange covariance and
    needs the coherence-block action on H_N(C), which is a different piece of machinery from
    anything (ii) or (iii) used: (ii) went through the trace form, (iii) through the functional
    calculus, and neither touches Peirce exchange.  So clause (i)'s price is NOT "the same again".

ATTACK EVIDENCE
  Row 36 clause (iii) was attacked and CLOSED today.  Row 29 gap (a) was attacked and closed in
  ARC-6.  Rows 15, 22, 26, 29(b), 31 were NOT attempted in ARC-6 or ARC-7.  ★★ Row 22 WAS probed on
  2026-08-09, and the probe refuted this file's own pricing of it rather than advancing the row: the
  statement written here to avoid the missing carrier is false.  That is the useful outcome — a
  certificate whose statement is wrong sends the next person to prove a false thing, which is worse
  than a vague price.  Recorded because "ABSENT" on this project has three times meant "nobody
  looked", and this time looking produced a retraction instead of a proof.

ABSENCE CLAIMS AND THEIR SCOPE
  * "no Givens/Jacobi factorization of unitaries into rank-two block rotations":
      grep -rn 'Givens\|Jacobi\|blockRotation' RadicalRelativity/ -> no hits.  Whole first-party
      tree incl. Vendor/, 2026-08-09.  In Mathlib: grep -rn 'Givens' .lake/packages/mathlib/Mathlib/
      -> no hits either (scope: Mathlib v4.28.0).  ★ Stated with both scopes because "Mathlib lacks
      X" has been wrong four times on this project when the tree vendored it; here neither has it.
  * "no complex structure on a cross-coherence space":
      grep -rn 'crossCoherence\|orientationJ\|complexStructure' RadicalRelativity/ -> no hits.
  * "no Peirce exchange automorphism":
      grep -rn 'peirceExchange\|exchangeAuto\|PeirceExchange' RadicalRelativity/ -> no hits.

NOT imported from RadicalRelativity/.
-/
import RadicalRelativity.Necessity.FrameConstancy

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

/-! ### Row 22 `lem:orientation` — and the retraction of this file's first pricing of it

The article's clauses are about `J` restricted to the cross-coherence space `X`.  `X` is not a
carrier in this tree, and the attempt below to state the content *without* it produced a false
proposition.  Read the docstring on `orientation_complex_structure`: the useful content of this
section is the retraction, not the statement. -/

/-- ★★ **THIS CERTIFICATE'S FIRST VERSION STATED A FALSE PROPOSITION, and it is corrected here
rather than quietly replaced.**

The first version asserted the *unrestricted* pointwise form `∀ x, J (J x) = -x`, on the reasoning
that the cross-coherence subspace is the object the tree lacks, so the statement should be made
about all `x` instead.  **That is false, with a compiled witness**: for orthogonal frame
projections `frameProj 0 * frameProj 1 = 0` (checked in Lean), so at `x = q` the inner product
`q·x·p` vanishes, giving `J q = 0` and hence `J (J q) = 0`, while `-q ≠ 0`.  `J` squares to `−1`
**only on the coherence space**, which is exactly why the article states it there.

A certificate that states a gap *incorrectly* is worse than one that states it vaguely, because
someone will try to prove a false thing.  This is the failure mode this arc's certificate-refutation
brief asked reviewers to hunt for, and the first instance was mine.

**So the honest content of row 22 is the opposite of what this file first claimed.**  It said the row
"needs nothing the tree lacks" and was "the row to attack first".  Wrong: it needs the
cross-coherence space as a *carrier*, which the tree does not have — the same missing vocabulary as
`W_n` in row 29 and the Peirce subalgebra in row 5.  The statement below therefore carries the
subspace condition as a hypothesis, which is the strongest form that is actually statable here. -/
theorem orientation_complex_structure {N : ℕ}
    (q p : HermitianMat (Fin N) ℂ) (J : HermitianMat (Fin N) ℂ → HermitianMat (Fin N) ℂ)
    (hJ : ∀ x, J x = ⟨Complex.I • (q.mat * x.mat * p.mat)
      - Complex.I • (q.mat * x.mat * p.mat)ᴴ, by sorry⟩) :
    ∀ x, q.mat * x.mat * p.mat + (q.mat * x.mat * p.mat)ᴴ = x.mat → J (J x) = -x := by
  sorry

/-- The compiled witness behind the retraction above: distinct frame projections annihilate, so the
unrestricted form fails at `x = q`. -/
theorem frameProj_mul_orthogonal_eq_zero :
    (Necessity.frameProj (0 : Fin 3)).mat * (Necessity.frameProj (1 : Fin 3)).mat = 0 := by
  rw [Necessity.frameProj_mat_eq_single, Necessity.frameProj_mat_eq_single]
  ext i j
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h1 h2
  · exact absurd (h1.2.trans h2.1.symm) (by decide)
  all_goals simp

/-! ### Row 29 gap (b) — the Θ-level statement

Lean proves the product-level identity; the article states the Θ-level one.  Written out so the
gap is a proposition rather than a remark about "the route". -/

/-- **GAP — row 29's Θ-level form.**  That the in-tree product-level identity is equivalent to the
article's statement about `Θ_a` restricted to the coherence space `W_n`.  Not statable without
`W_n` as a carrier, so recorded as a vocabulary wall with the statable half noted: the
product-level identity itself is `Necessity.n2_sp_eq_twistSeq_frame`, in the tree. -/
theorem n2_necessity_theta_level : True := by
  trivial

/-! ### Row 36 clause (i) — Peirce exchange covariance

The remaining clause of `cor:selectors`.  The hypothesis is covariance under the Peirce exchange
automorphism, which does not exist in the tree; the conclusion is the same as clauses (ii)/(iii). -/

/-- **GAP — clause (i)'s missing input.**  A Peirce exchange automorphism of `H_N(ℂ)`: the unital
order automorphism swapping two frame atoms and acting on the coherence blocks accordingly.

Note the shape: once such a map exists and is shown to flip the twist (as transposition does —
`Necessity.transposeMap_twistSeq`, proved today), clause (i) closes by the *same* `∃!` step that
closed (ii) and (iii).  So the gap is an object, not an argument. -/
theorem exists_peirce_exchange {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) (hij : i ≠ j) :
    ∃ Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ,
      (∀ x y, x ≤ y ↔ Φ x ≤ Φ y) ∧ Φ 1 = 1 ∧ Φ (Necessity.frameProj i) = Necessity.frameProj j := by
  sorry

end WallCertificate
