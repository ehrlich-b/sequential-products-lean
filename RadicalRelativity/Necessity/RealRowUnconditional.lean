/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealKadison
import RadicalRelativity.Necessity.RealRigidity

set_option linter.style.longLine false

/-!
# The real row, UNCONDITIONAL  (`prop:real` with every hypothesis discharged)

`RealRigidity.sp_eq_luders_of_effect` proves the real row conditional on one located
hypothesis: the Jordan property of the comparison map in each eigenframe, carried because
"real Kadison/Uhlhorn is available in no prover".  **It is now available in this one.**

* `thetaPreservesJordanR_of_S2` — the comparison map of any S1–S7 product with S2 on
  `H_N(ℝ)` is a unital surjective linear order-isomorphism, so real Kadison
  (`orderAutoR_preservesJordan`) applies.
* `real_classification` — **THE REAL ROW.** Every S1–S7 sequential product with S2 on
  `H_N(ℝ)` is the Lüders product on ALL effects.  No twist, no side condition.

The hypothesis list is now exactly the paper's: an S1–S7 product, S2, and a nonempty index.
Closure is Lean core alone (`propext`, `Classical.choice`, `Quot.sound`), as it already was for
the ℂ row — the real row's gap was a missing theorem, not a cited axiom, and the theorem is now
proved here.
-/

noncomputable section

open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {N : ℕ}

/-- **The eigenframe Jordan hypothesis, DISCHARGED at ℝ.**  The comparison map `theta` is a
unital surjective linear order-isomorphism of `H_N(ℝ)`, and every such map is a Jordan
automorphism by real Kadison rigidity. -/
theorem thetaPreservesJordanR_of_S2 (hN : 0 < N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℝ))
    (hS2 : P.FirstArgContinuous) :
    ThetaPreservesJordanG P := by
  intro a ha hbd
  refine orderAutoR_preservesJordan hN (theta P ha hbd) ?_ ?_ ?_
  · exact fun x y => (theta_le_iff P hS2 ha hbd x y).symm
  · exact theta_one P ha hbd
  · intro y
    obtain ⟨x, hx⟩ := (thetaEquiv P hS2 ha hbd).surjective y
    refine ⟨x, ?_⟩
    rw [← thetaEquiv_apply P hS2 ha hbd x]
    exact hx

/-- **`prop:real`, THE REAL ROW — UNCONDITIONAL.**

Every S1–S7 sequential product with S2 on `H_N(ℝ)` is the Lüders product
`a • b = √a · b · √a` on **all** effects, singular ones included.  The real type admits no
twist parameter whatsoever.

Conditional on nothing beyond the paper's own hypotheses: an S1–S7 product, S2, and `0 < N`.
The eigenframe Jordan property that `sp_eq_luders_of_effect` carried as a located hypothesis
is discharged here by `thetaPreservesJordanR_of_S2`, whose own Wigner input
(`exists_isometry_of_transProbPreservingR`) is proved in this development. -/
theorem real_classification (hN : 0 < N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℝ))
    (hS2 : P.FirstArgContinuous)
    {b : HermitianMat (Fin N) ℝ} (hb : IsEffect b)
    (a : HermitianMat (Fin N) ℝ) (ha : IsEffect a) :
    P.sp a b = b.conj (a.cfc Real.sqrt).mat :=
  sp_eq_luders_of_effect P hS2
    (fun _U hU hU' =>
      thetaPreservesJordanR_of_S2 hN _ (conjProduct_firstArgContinuousG P hU hU' hS2))
    hb a ha

end Necessity
