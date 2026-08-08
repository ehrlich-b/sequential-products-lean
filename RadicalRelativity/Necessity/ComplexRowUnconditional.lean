/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.UnitaryGeneration

set_option linter.style.longLine false

/-!
# The complex row, UNCONDITIONAL  (`mthm:master` at `H_N(ℂ)`, `N ≥ 3`, hypothesis-free)

`ComplexMaster.complex_classification` proves the complex row conditional on the manuscript's
two frame-graph facts, carried as located hypotheses: a caller-supplied adjacency relation, its
connectivity (`lem:frame-connectivity`), and the cross-coherence overlap of adjacent frames'
`U(1)` characters.  **Both are now theorems of this development.**

* `frameTwistConst` — `frameTwist` is constant: `FrameConstancy.frameTwist_eq_of_adjAxis`
  supplies coherence for one adjacency step, `UnitaryGeneration.adjAxis_connected` supplies the
  walk, and `Globalization.const_of_adjacent` chains them.
* `complex_classification_unconditional` — **THE COMPLEX ROW.**  Every S1–S7 sequential product
  with S2 on `H_N(ℂ)`, `N ≥ 3`, is `a • b = a^{1/2+it} b a^{1/2−it}` for a **unique** real `t`,
  on all effects.

The hypothesis list is now exactly the paper's: an S1–S7 product, S2, and `N ≥ 3`.  Closure is
Lean core alone (`propext`, `Classical.choice`, `Quot.sound`), as it already was for the
conditional form — what changed is not the axiom closure but the *carried hypotheses*.

Both flagship rows of `mthm:master` are now hypothesis-free: this one and
`RealRowUnconditional.real_classification`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {N : ℕ}

/-- **The per-frame twist parameter is constant** — the complex row's whole residue,
discharged.

One adjacency step is `frameTwist_eq_of_adjAxis`: axis-adjacent frames share a one-parameter
family of base points, and comparing the product's value along that family pins the two
parameters to each other exactly.  Any two frames are joined by a walk of three such steps
(`adjAxis_connected`, from the Householder factorization of `F⁻¹G`), and a real assignment
constant across adjacent pairs is constant along a walk. -/
theorem frameTwistConst (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) :
    FrameTwistConst hN P hS2 := by
  intro F G
  exact MasterTheorem.Globalization.const_of_adjacent
    (Adj := AdjAxis) (t := frameTwist hN P hS2)
    (fun _ _ hadj => frameTwist_eq_of_adjAxis hN P hS2 hadj)
    (adjAxis_connected hN F G)

/-- **`mthm:master`, THE COMPLEX ROW — UNCONDITIONAL.**

For every S1–S7 sequential product with S2 on `H_N(ℂ)`, `N ≥ 3`, there is a **unique** real `t`
with

`a • b = a^{1/2+it} · b · a^{1/2−it}`

for **all** effects `a, b`, singular ones included.

Conditional on nothing beyond the paper's own hypotheses.  The frame-graph facts that
`complex_classification` carried — connectivity of the unitary frame graph and cross-coherence
of adjacent frames' characters — are discharged by `frameTwistConst`. -/
theorem complex_classification_unconditional (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) :
    ∃! t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b :=
  complex_classification_of_frameTwistConst hN P hS2 (frameTwistConst hN P hS2)

/-! ## Non-vacuity, certified in-tree

A theorem quantified over a hypothesis class says nothing if the class is empty, and a theorem
producing a parameter says little if the parameter need not be the intended one.  Both are
checked here against a known member of the class.
-/

/-- **The hypothesis class is inhabited.**  M1's twist product with parameter `t` is an S1–S7
product with S2 on `H_N(ℂ)`, so the capstone applies to it: `3 ≤ N`, `SequentialProductOn`, and
`FirstArgContinuous` are simultaneously satisfiable, and the row is not vacuous. -/
theorem twistProductOn_classified (hN : 3 ≤ N) (t : ℝ) :
    ∃! t' : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      (twistProductOn t).sp a b = HermitianMat.twistSeq t' a b :=
  complex_classification_unconditional hN (twistProductOn t)
    (twistProductOn_firstArgContinuous t)

/-- **The recovered parameter is the intended one.**  Run the capstone on the twist product with
parameter `t` and the unique `t'` it returns is `t` itself.  So the classification is sharp: the
twist family is faithfully parameterized, and the `∃!` is not satisfied by some unrelated
value. -/
theorem complex_classification_sharp (hN : 3 ≤ N) (t t' : ℝ) :
    (∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
        (twistProductOn t).sp a b = HermitianMat.twistSeq t' a b)
      ↔ t' = t := by
  constructor
  · intro h
    refine (twist_param_unique (N := N) (by omega) (fun a b ha hb => ?_)).symm
    rw [← twistProductOn_sp t a b]
    exact h a b ha hb
  · intro h a b _ _
    rw [h, twistProductOn_sp]

end Necessity
