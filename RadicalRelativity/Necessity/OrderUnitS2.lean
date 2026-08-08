/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComplexRowUnconditional
import RadicalRelativity.Necessity.RealRowUnconditional

set_option linter.style.longLine false

/-!
# S2 in the ORDER-UNIT norm: the literal-fidelity bridge, and both rows restated over it

`SequentialProductOn.FirstArgContinuous` — the S2 hypothesis both flagship rows carry — is
`ContinuousOn` in the topology the carrier *has*, which on `HermitianMat n 𝕜` is the Frobenius
(Hilbert–Schmidt) norm inherited from the matrix algebra.  **The manuscript's S2 is continuity
in the order-unit norm** `‖a‖_e = inf {t ≥ 0 | −t·1 ≤ a ≤ t·1}`, the norm an order-unit space
carries intrinsically.  On a finite-dimensional carrier the two are equivalent, and
`Hermitian/OrderUnit.lean` proves the two-sided comparison
(`ouNorm_le_norm`, `norm_le_sqrt_card_mul_ouNorm`) — but a comparison of *norms* is not by
itself a statement about `ContinuousOn`, so until now the fidelity of the Lean S2 to the
paper's S2 was an argument in `THEOREM-MAP.md` rather than a theorem.  This file makes it a
theorem, and restates both rows so that their S2 hypothesis is the paper's verbatim.

Why the restatement is not vacuous bookkeeping: `ContinuousOn` cannot express "continuous in
the order-unit norm" directly, because the carrier has exactly one `TopologicalSpace` instance
and it is the Frobenius one.  So the order-unit hypothesis has to be written out in ε–δ form
against `ouNorm` on **both** sides of the map (`ContinuousOnOu`), which is precisely how the
manuscript states S2, and then proved equivalent.

* `HermitianMat.ContinuousOnOu` — ε–δ continuity on a set, both distances in `ouNorm`.
* `HermitianMat.continuousOnOu_iff_continuousOn` — **the bridge**: on a nonempty index type
  the two notions coincide.  The sandwich `ouNorm ≤ ‖·‖ ≤ √(card n)·ouNorm` supplies one
  rescaling of `ε` in each direction.
* `Necessity.FirstArgContinuousOu` — the paper's S2 for a pinned product, and
  `firstArgContinuousOu_iff` its equivalence with `FirstArgContinuous`.
* `Necessity.real_classification_ouNorm` and
  `Necessity.complex_classification_unconditional_ouNorm` — **both flagship rows with the
  paper's S2 as the literal hypothesis.**  Same conclusions, same closure (Lean core); the only
  change is that nothing is left to a prose argument about which norm S2 refers to.
-/

noncomputable section

open OrderUnitSpace

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

omit [DecidableEq n] in
/-- The comparison constant is positive as soon as the index type is nonempty. -/
theorem sqrt_card_pos [Nonempty n] : (0 : ℝ) < Real.sqrt (Fintype.card n) :=
  Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- **ε–δ continuity on a set, measured in the order-unit norm on both sides.**  This is the
manuscript's form of a continuity hypothesis on the order-unit space, written without reference
to the carrier's own norm. -/
def ContinuousOnOu (f : HermitianMat n 𝕜 → HermitianMat n 𝕜)
    (s : Set (HermitianMat n 𝕜)) : Prop :=
  ∀ a₀ ∈ s, ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, ouNorm (a - a₀) < δ → ouNorm (f a - f a₀) < ε

/-- **THE BRIDGE.**  Order-unit-norm continuity on a set and `ContinuousOn` (the carried
Frobenius topology) are the same property.

Both directions are the sandwich `ouNorm ≤ ‖·‖ ≤ √(card n)·ouNorm` used once on each side of
the map: going to `ContinuousOn` one shrinks the target `ε` by `√(card n)`, and coming back one
shrinks the source `δ` by the same factor.  Nonemptiness of the index type is what makes the
factor positive (on an empty index type the carrier is a single point and both sides hold
trivially, but the rescaling argument would divide by zero). -/
theorem continuousOnOu_iff_continuousOn [Nonempty n]
    (f : HermitianMat n 𝕜 → HermitianMat n 𝕜) (s : Set (HermitianMat n 𝕜)) :
    ContinuousOnOu f s ↔ ContinuousOn f s := by
  have hCpos : (0 : ℝ) < Real.sqrt (Fintype.card n) := sqrt_card_pos
  rw [Metric.continuousOn_iff]
  constructor
  · intro h a₀ ha₀ ε hε
    obtain ⟨δ, hδ, hmain⟩ := h a₀ ha₀ (ε / Real.sqrt (Fintype.card n)) (div_pos hε hCpos)
    refine ⟨δ, hδ, fun a ha hd => ?_⟩
    rw [dist_eq_norm] at hd
    have h2 := hmain a ha (lt_of_le_of_lt (ouNorm_le_norm _) hd)
    rw [dist_eq_norm]
    calc ‖f a - f a₀‖
        ≤ Real.sqrt (Fintype.card n) * ouNorm (f a - f a₀) :=
          norm_le_sqrt_card_mul_ouNorm _
      _ < Real.sqrt (Fintype.card n) * (ε / Real.sqrt (Fintype.card n)) :=
          mul_lt_mul_of_pos_left h2 hCpos
      _ = ε := by field_simp
  · intro h a₀ ha₀ ε hε
    obtain ⟨δ, hδ, hmain⟩ := h a₀ ha₀ ε hε
    refine ⟨δ / Real.sqrt (Fintype.card n), div_pos hδ hCpos, fun a ha hd => ?_⟩
    have h1 : ‖a - a₀‖ < δ := by
      calc ‖a - a₀‖
          ≤ Real.sqrt (Fintype.card n) * ouNorm (a - a₀) := norm_le_sqrt_card_mul_ouNorm _
        _ < Real.sqrt (Fintype.card n) * (δ / Real.sqrt (Fintype.card n)) :=
            mul_lt_mul_of_pos_left hd hCpos
        _ = δ := by field_simp
    have h2 := hmain a ha (by rw [dist_eq_norm]; exact h1)
    rw [dist_eq_norm] at h2
    exact lt_of_le_of_lt (ouNorm_le_norm _) h2

end HermitianMat

namespace Necessity

open HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The manuscript's S2, verbatim**: for each fixed effect `b`, the map `a ↦ a • b` is
continuous on the effects, with both distances measured in the ORDER-UNIT norm. -/
def FirstArgContinuousOu (P : SequentialProductOn (HermitianMat n 𝕜)) : Prop :=
  ∀ ⦃b : HermitianMat n 𝕜⦄, IsEffect b →
    ContinuousOnOu (fun a => P.sp a b) {a : HermitianMat n 𝕜 | IsEffect a}

/-- **The paper's S2 and the tree's S2 are the same hypothesis.** -/
theorem firstArgContinuousOu_iff [Nonempty n] (P : SequentialProductOn (HermitianMat n 𝕜)) :
    FirstArgContinuousOu P ↔ P.FirstArgContinuous := by
  constructor
  · intro h b hb
    exact (continuousOnOu_iff_continuousOn _ _).mp (h hb)
  · intro h b hb
    exact (continuousOnOu_iff_continuousOn _ _).mpr (h hb)

/-! ## Both flagship rows, with the paper's S2 as the literal hypothesis -/

/-- **`mthm:master`, THE REAL ROW, with S2 in the order-unit norm.**  Identical to
`real_classification` except that the continuity hypothesis is the manuscript's own:
`a ↦ a • b` continuous on effects in `‖·‖_e`.  The product is the Lüders product on all
effects, with no twist parameter. -/
theorem real_classification_ouNorm {N : ℕ} (hN : 0 < N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℝ))
    (hS2 : FirstArgContinuousOu P)
    {b : HermitianMat (Fin N) ℝ} (hb : IsEffect b)
    (a : HermitianMat (Fin N) ℝ) (ha : IsEffect a) :
    P.sp a b = b.conj (a.cfc Real.sqrt).mat := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact real_classification hN P ((firstArgContinuousOu_iff P).mp hS2) hb a ha

/-- **`mthm:master`, THE COMPLEX ROW, with S2 in the order-unit norm.**  Identical to
`complex_classification_unconditional` except that the continuity hypothesis is the
manuscript's own.  There is a unique real `t` with `a • b = a^{1/2+it} b a^{1/2−it}` on all
effects. -/
theorem complex_classification_unconditional_ouNorm {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : FirstArgContinuousOu P) :
    ∃! t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b := by
  haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  exact complex_classification_unconditional hN P ((firstArgContinuousOu_iff P).mp hS2)

end Necessity
