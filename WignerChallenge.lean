/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Wigner's theorem over the reals

Wigner's theorem says that a symmetry of a quantum system — a transformation of states
preserving all transition probabilities — must be induced by a unitary or antiunitary map.
This file states the **finite-dimensional real, non-bijective** case: only preservation of
transition probabilities is assumed, and bijectivity is not. That is the non-bijective Wigner
theorem. It is not the Uhlhorn form, which instead weakens the hypothesis to preservation of
orthogonality and traditionally retains bijectivity.

Everything the statement mentions is defined here from Mathlib: `ℙ ℝ E` is Mathlib's
projectivization, `E ≃ₗᵢ[ℝ] E` its linear isometry equivalences, and the two transition
probability functions are two lines each.
-/

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace WignerReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The transition probability of two vectors**, `|⟨ψ,φ⟩|² / (‖ψ‖²‖φ‖²)`.

This is the quantity a physicist calls the probability of observing the state `φ` given the
state `ψ`.  It depends only on the rays through `ψ` and `φ`, which is what makes the next
definition well posed.

★ At a zero argument the formula is `0/0`, which Lean evaluates to `0`. That value is junk: the
reading above, and the rescaling invariance the next definition relies on, are asserted for
**nonzero** vectors and nonzero scalars only. Nothing reaches it from `transProb`, since a point
of `ℙ ℝ E` has a nonzero representative. -/
def transProbVec (ψ φ : E) : ℝ :=
  ‖(inner ℝ ψ φ : ℝ)‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)

/-- **The transition probability of two rays.**  `ℙ ℝ E` is Mathlib's projectivization of `E`,
whose points are the one-dimensional subspaces, and `p.rep` is an arbitrary nonzero
representative of `p`.  `transProbVec` is invariant under rescaling either argument, so the
choice of representative does not matter. -/
def transProb (p q : ℙ ℝ E) : ℝ := transProbVec p.rep q.rep

/-- **The map on rays induced by a linear isometry.** -/
def projMap (e : E ≃ₗᵢ[ℝ] E) : ℙ ℝ E → ℙ ℝ E :=
  Projectivization.map e.toLinearEquiv.toLinearMap e.injective

/-- **A self-map of the rays preserves transition probabilities.**

Note what is *not* assumed: `f` is an arbitrary function on rays.  It is not assumed
bijective, continuous, or induced by anything. -/
def TransProbPreserving (f : ℙ ℝ E → ℙ ℝ E) : Prop :=
  ∀ p q, transProb (f p) (f q) = transProb p q

/-- **The finite-dimensional real, non-bijective Wigner theorem.**

Every transition-probability preserving self-map of the rays of a finite-dimensional real
inner product space is induced by a linear isometry of that space.

This is the rigidity statement underlying Wigner's theorem on symmetries of quantum systems:
a transformation of states that merely preserves the observable transition probabilities has
no freedom left, and must come from an isometry.

`TransProbPreserving f` is the single equation
`∀ p q, transProb (f p) (f q) = transProb p q`.  **Bijectivity is not assumed** — preservation
of transition probabilities alone forces `f` to be induced by an isometry, and hence forces it
to be bijective. -/
theorem exists_isometry_of_transProbPreserving [FiniteDimensional ℝ E] [Nontrivial E]
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreserving f) :
    ∃ e : E ≃ₗᵢ[ℝ] E, ∀ p : ℙ ℝ E, f p = projMap e p := sorry

end WignerReal

end
