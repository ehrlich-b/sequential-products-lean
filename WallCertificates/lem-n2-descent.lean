/-
WALL CERTIFICATE — `lem:n2-descent`  (row 34 of STATEMENT-MANIFEST.md)
Date: 2026-08-09, ARC-7 block 7.5.  Commit at issue: see `git log`; tag `paperA-arc7-cp1`.
Denominator pin: main.tex blob 205fdf5a.  Row status on this date: PARTIAL.

★★★ ROW 34 IS NOW FORMALIZED (2026-08-09, ARC-8 block 8.1(d)).  THIS FILE'S HEADER IS STALE FROM
HERE DOWN AND IS KEPT ONLY FOR THE RETRACTIONS INSIDE IT.  The descent object is
`RankTwo.n2QubitModuli P hS2 : C(RP2, R)`, and this file's own row conclusion `exists_rp2_moduli`
is discharged below rather than `sorry`-ed.  Two `sorry`s remain and BOTH ARE OFF-ROUTE: the
diagonal/monomial step and the ray-complementation identity were never used.
  ★ In particular the phrase below — "what is missing is the DESCENT ITSELF as a constructed
  object" — was true when written and is false now.

WHAT THE ARTICLE ASSERTS
  t~(-n) = t~(n) — the two sign changes cancel — so the frame parameter descends to a single
  continuous bounded  t : RP^2 -> R  with no residual line-bundle twist.

WHAT IS IN THE TREE (all for an ARBITRARY product, unless noted)
  * `Necessity.n2FrameTwist`            the frame parameter, on U(2)
  * `Necessity.n2FrameTwist_reverse`    the frame-reversal clause — t~(-n) = t~(n)
  * `Necessity.n2FrameTwist_mul_diagonal` and `_mul_diagonal_swap`  fibre-constancy
  * `Necessity.exists_n2FrameTwist_bound`   bounded            (ARC-7 7.1a, FORMALIZED)
  * `Necessity.continuous_n2FrameTwist`     continuous         (ARC-7 7.1b, FORMALIZED)
  * `RankTwo.blochFrame_eq_iff`         the Bloch map's fibres are exactly complementary pairs
                                        (ARC-7 7.1c — the descent's missing converse)
  So all three properties the article's conclusion names (invariant, bounded, continuous) are in
  hand.  What is missing is the DESCENT ITSELF as a constructed object.

THE THREE MISSING STEPS, stated below with `sorry` at exactly the gap:
  (1) `frameRay` — the map U(2) -> CP^1 sending a unitary to its first column's ray, and the
      transfer of `n2FrameTwist`'s invariances along it.  The mathematical content is
      "same first-column ray ==> the unitaries differ by a DIAGONAL unitary", which is elementary
      (W := U^H V has W e0 = lam e0, and unitarity then forces W 0 1 = 0) but is not in the tree.
  (2) the swap case: `orthoFrame (frameRay V) = frameRay (V * swapU)`, i.e. in C^2 a unit vector
      orthogonal to v0 is a phase times orthoVec v0.  Also elementary, also absent.
  (3) the quotient construction of `C(RP^2, R)`.  NOTE this step is CHEAPER than it looks and the
      certificate says so explicitly: `U(2)` is compact (in-tree, Vendor/Wigner/UnitaryCompact.lean)
      and `RP^2` is Hausdorff, so a continuous surjection between them is a closed map hence a
      quotient map, and continuity of the descended function is FREE.  The work is (1) and (2).

ATTACK EVIDENCE
  Attempted 2026-08-09.  Step (1)'s linear algebra was worked out on paper in full (see the row
  note) and is correct; it was not formalized only because of budget, not resistance.  The crux
  that WAS attacked and closed is `RankTwo.blochFrame_eq_iff`, which was the one step with real
  mathematical content (it needs `blochVec_normSq` to pin the scale of the proportionality before
  the coordinates determine the ray).  So this certificate records a wall of VOLUME, not of depth:
  roughly 200 lines of concrete C^2 linear algebra plus a quotient assembly.  It should be
  attacked before any row that needs new mathematics.

ABSENCE CLAIMS AND THEIR SCOPE
  * "no `U(2) -> CP^1` or `U(2) -> RP^2` map exists in the tree":
      grep -rn 'unitaryGroup.*QubitFrame\|QubitFrame.*unitaryGroup\|frameRay' RadicalRelativity/
      -> no hits, whole first-party tree including Vendor/, 2026-08-09.
  * "`RankTwo/` builds `tauModuliRP2 : C(RP2, R)` only for the CONCRETE tau family, not for an
    arbitrary product": `RankTwo/Bloch.lean:340` defines it from `tauRVec`, a formula on vectors;
      grep -c 'SequentialProductOn' RadicalRelativity/RankTwo/*.lean  -> 0 in every file.
    (This same grep was, in ARC-5, used to support a WRONGER claim — that the classification map
    did not exist at all — when in fact its input lives in `Necessity/`.  Directory-scoped absence
    claims have misfired here before; the scope is stated so this one can be checked.)

★★ REFUTED IN PART, 2026-08-09, SAME DAY, BY THE CHECKPOINT-1 COLD REVIEW.  Recorded here rather
than rewritten away, because the whole point of this directory is that certificates are falsifiable
and this one was falsified within the hour.

  STEP (1) BELOW IS UNNECESSARY.  It is priced above at ~200 lines of C^2 ray algebra ("same
  first-column ray ==> the unitaries differ by a diagonal unitary").  One never needs rays: the
  parameter descends along the FIRST SPECTRAL PROJECTION instead, because
  basePt x = 1 + (e^{-x} - 1) * frameProj 0, so equal first spectral projections force equal base
  points at every scale, and `n2FrameTwist_eq_of_base_eq` — already in the tree — then applies.
  That is `Necessity.n2FrameTwist_eq_of_frameMap_eq`, now landed, and it is GENUINE fibre-constancy
  rather than invariance at two group words.

  STEP (3) IS ALSO CHEAPER THAN PRICED and is now DONE: `Necessity.FrameSpace`,
  `Necessity.toFrameSpace`, `Necessity.isQuotientMap_toFrameSpace`, `Necessity.n2Moduli`,
  `Necessity.continuous_n2Moduli`, `Necessity.exists_n2Moduli_bound`.

  WHAT ACTUALLY REMAINS OF ROW 34, after all of the above: only that `FrameSpace` — the rank-one
  projections PRESENTED BY UNITARIES — is all of them, i.e. surjectivity onto rank-one projections,
  which needs `RankTwo.orthoVec` assembled into a unitary.  Plus the identification of that space
  with `RP^2` (the complementation quotient), for which `RankTwo.blochFrame_eq_iff` (ARC-7) supplies
  the fibre structure.

  WHY I MISSED IT, recorded because it is the transferable part: I reached for rays because
  `RankTwo/` is written in terms of `CP^1`, and never asked whether the parameter's own defining
  identity already descended along something cheaper.  A reviewer with no attachment to that
  vocabulary saw it immediately.

NOT imported from RadicalRelativity/.  `lake build` and AxiomAudit never see this file.
-/
import RadicalRelativity.Necessity.FrameConstancy
import RadicalRelativity.RankTwo.Bloch
import RadicalRelativity.RankTwo.Sufficiency

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

/-! ### Step (1): the frame ray of a unitary, and constancy of the parameter along it -/

/-- The first column of a unitary, as a vector of `EuclideanSpace`. -/
noncomputable def col₀ (U : Matrix.unitaryGroup (Fin 2) ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)

/-- **NO LONGER A GAP.**  `RankTwo.firstCol` is this definition and `RankTwo.firstCol_ne_zero` is
this theorem (ARC-8 block 8.1(b)). -/
theorem col₀_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ) : col₀ U ≠ 0 :=
  RankTwo.firstCol_ne_zero U

/-- The frame ray: the point of `ℂP¹` determined by a unitary's first column. -/
noncomputable def frameRay (U : Matrix.unitaryGroup (Fin 2) ℂ) : RankTwo.QubitFrame :=
  Projectivization.mk ℂ (col₀ U) (col₀_ne_zero U)

/-- **GAP — the mathematical content of step (1).**  Two unitaries with the same first-column ray
differ by a diagonal unitary.

This is elementary: with `W := Uᴴ V`, the hypothesis gives `W e₀ = λ e₀` with `λ ≠ 0`, and then
`WᴴW = 1` read at entry `(0,1)` gives `conj λ · W 0 1 = 0`, hence `W 0 1 = 0`, hence `W` diagonal.
Nothing in the tree performs this step. -/
theorem exists_diagonal_of_frameRay_eq (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (h : frameRay U = frameRay V) :
    ∃ (D : Matrix.unitaryGroup (Fin 2) ℂ) (d : Fin 2 → ℂ),
      (D : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal d ∧ V = U * D := by
  sorry

/-- ★★★ **NO LONGER A GAP, AND IT DID NOT GO THROUGH THE STEP ABOVE.**  Row 34 closed in ARC-8
block 8.1(d), and the diagonal/monomial step this file called "the mathematical content of step (1)"
was **never used**.  What the transfer actually needs is that equal rays give the same *first
spectral projection* — `RankTwo.frameMap_eq_of_colFrame_eq`, which follows from `rankOne`'s quadratic
homogeneity plus `RankTwo.nsq_firstCol` (a unitary's column is a unit vector).  No statement about
diagonal or monomial matrices appears anywhere in the assembly, so the `sorry` above is a gap in a
route nobody took.
  ★ THE TRANSFERABLE POINT, and this arc has now hit it three times: a residue read off the
  ARTICLE's proof is evidence about the article's route, not about the cheapest route through a formal
  library.  Reading the article to learn WHICH fact is needed has been reliable; reading it to learn
  HOW has been wrong three times out of three (this step, `lem:n2-descent`'s sibling in
  `prop-n2-sufficiency.lean`, and S2's predicted global-phase estimate). -/
theorem n2FrameTwist_eq_of_frameRay_eq
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ) (h : frameRay U = frameRay V) :
    Necessity.n2FrameTwist P hS2 V = Necessity.n2FrameTwist P hS2 U :=
  Necessity.n2FrameTwist_eq_of_frameMap_eq P U V hS2
    (RankTwo.frameMap_eq_of_colFrame_eq h).symm

/-! ### Step (2): the swap case -/

/-- **STILL A GAP, AND ALSO NOT NEEDED.**  The descent that closed row 34 split the fibre of
`blochFrame` with `RankTwo.blochFrame_eq_iff` and then worked with spectral *projections*
(`RankTwo.frameMap_eq_one_sub_of_colFrame_eq_ortho`), never with the ray identity below.  Kept as a
statement about `ℂ²` that remains unproved, and flagged so a reader does not mistake it for a
blocker. -/
theorem frameRay_mul_swap (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    frameRay (V * Necessity.swapU) = RankTwo.orthoFrame (frameRay V) := by
  sorry

/-! ### Step (3): the descent

Given (1) and (2), `n2FrameTwist` is constant on the fibres of
`blochFrame ∘ frameRay : U(2) → ℝP²` — by `RankTwo.blochFrame_eq_iff` (in-tree, ARC-7) the fibre
of `blochFrame` is exactly `{ray, complementary ray}`, and the two cases are handled by (1) and by
(2) together with the in-tree `n2FrameTwist_reverse`.

The remaining assembly is pure topology and is **cheap**: `U(2)` is compact
(`Vendor/Wigner/UnitaryCompact.lean`) and `ℝP²` is Hausdorff, so a continuous surjection is closed,
hence a quotient map, hence the descended function is automatically continuous.  Stated here so
the price is on the record as topology rather than analysis. -/

/-- **NO LONGER A GAP — this is row 34, and it is FORMALIZED** (ARC-8 block 8.1(d)):
`RankTwo.n2QubitModuli P hS2` is the function, with `RankTwo.n2QubitModuli_apply` the pullback
identity.  ★ The price recorded above — "pure topology and cheap: `U(2)` compact, `ℝP²` Hausdorff,
so a continuous surjection is closed, hence a quotient map" — **was exactly right**, which is worth
recording next to the two prices in this same file that were not. -/
theorem exists_rp2_moduli
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous) :
    ∃ f : C(RankTwo.RP2, ℝ), ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      f (RankTwo.blochFrame (frameRay U)) = Necessity.n2FrameTwist P hS2 U :=
  ⟨RankTwo.n2QubitModuli P hS2, fun U => RankTwo.n2QubitModuli_apply P hS2 U⟩

end WallCertificate
