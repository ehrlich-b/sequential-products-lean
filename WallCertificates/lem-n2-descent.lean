/-
WALL CERTIFICATE — `lem:n2-descent`  (row 34 of STATEMENT-MANIFEST.md)
Date: 2026-08-09, ARC-7 block 7.5.  Commit at issue: see `git log`; tag `paperA-arc7-cp1`.
Denominator pin: main.tex blob 205fdf5a.  Row status on this date: PARTIAL.

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

NOT imported from RadicalRelativity/.  `lake build` and AxiomAudit never see this file.
-/
import RadicalRelativity.Necessity.FrameConstancy
import RadicalRelativity.RankTwo.Bloch

set_option linter.style.longLine false

namespace WallCertificate

open scoped Matrix
open ComplexOrder OrderUnitSpace

/-! ### Step (1): the frame ray of a unitary, and constancy of the parameter along it -/

/-- The first column of a unitary, as a vector of `EuclideanSpace`. -/
noncomputable def col₀ (U : Matrix.unitaryGroup (Fin 2) ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun i => (U : Matrix (Fin 2) (Fin 2) ℂ) i 0)

/-- **GAP.** The first column of a unitary is nonzero.  Elementary (`UᴴU = 1` forces the column
to have norm one); not in the tree in this form. -/
theorem col₀_ne_zero (U : Matrix.unitaryGroup (Fin 2) ℂ) : col₀ U ≠ 0 := by
  sorry

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

/-- With the two steps above, constancy of the parameter along the frame ray is immediate from the
in-tree invariance `n2FrameTwist_mul_diagonal`. -/
theorem n2FrameTwist_eq_of_frameRay_eq
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ) (h : frameRay U = frameRay V) :
    Necessity.n2FrameTwist P hS2 V = Necessity.n2FrameTwist P hS2 U := by
  obtain ⟨D, d, hD, hUV⟩ := exists_diagonal_of_frameRay_eq U V h
  rw [hUV, Necessity.n2FrameTwist_mul_diagonal P hS2 U D hD]

/-! ### Step (2): the swap case -/

/-- **GAP.**  Reversing the frame is complementation of the ray.  In `ℂ²` a unit vector orthogonal
to `v₀` is a phase times `orthoVec v₀`; elementary, absent from the tree. -/
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

/-- **GAP (statement, not depth).**  The article's conclusion: a continuous function on `ℝP²`
pulling back to the frame parameter. -/
theorem exists_rp2_moduli
    (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous) :
    ∃ f : C(RankTwo.RP2, ℝ), ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      f (RankTwo.blochFrame (frameRay U)) = Necessity.n2FrameTwist P hS2 U := by
  sorry

end WallCertificate
