/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComplexMaster

set_option linter.style.longLine false

/-!
# The complex row's residue, sharpened to one internal statement

`complex_classification` carries the manuscript's two frame-graph facts as located
hypotheses: a caller-supplied adjacency relation `Adj`, its connectivity, and the
cross-coherence overlap of adjacent frames' `U(1)` characters.  This file observes that
**`Adj` is chosen by the caller**, and collapses the whole apparatus.

Taking `Adj := fun _ _ => True`:

* `connected` becomes free — every pair is adjacent in one step;
* `overlap` becomes exactly "any two frames' characters agree on an interval", which by
  `real_character_unique` is exactly `frameTwist F = frameTwist G`.

So the row's entire residue is the single statement **`frameTwist` is constant**
(`FrameTwistConst`).  This is a strict improvement in the honesty ledger, for two reasons.
It removes a caller-supplied relation from the interface, so no choice of `Adj` can make
the theorem look stronger than it is.  And it states the residue purely in terms of objects
defined in this development, rather than as a citation to two lemmas of the manuscript.

Scope, stated exactly: this is a *sufficient* condition, packaged from the existing capstone.
The converse (that the row's conclusion forces `frameTwist` constant) is certainly true and
would make the reduction lossless, but it is **not proved here** — proving it needs the
per-frame parameter's uniqueness at each frame, which is a separate step.  Do not describe
`FrameTwistConst` as "equivalent to" the complex row until that is done; it is currently
"suffices for".
-/

noncomputable section

open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {N : ℕ}

/-- **The complex row's entire residue**: the per-frame twist parameter does not depend on
the frame. -/
def FrameTwistConst (hN : 3 ≤ N) (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) : Prop :=
  ∀ F G : Matrix.unitaryGroup (Fin N) ℂ, frameTwist hN P hS2 F = frameTwist hN P hS2 G

/-- **The complex row, with the frame-graph apparatus removed.**

Identical in strength to `complex_classification`, but carrying one hypothesis about this
development's own `frameTwist` instead of a caller-supplied adjacency relation together with
two citations.  The `Adj := True` instantiation makes connectivity free and turns
cross-coherence into constancy. -/
theorem complex_classification_of_frameTwistConst (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ)) (hS2 : P.FirstArgContinuous)
    (hconst : FrameTwistConst hN P hS2) :
    ∃! t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b :=
  complex_classification hN P hS2 (fun _ _ => True)
    (fun _ _ => Relation.ReflTransGen.single (Or.inl trivial))
    (fun F G _ => ⟨0, 1, zero_lt_one, fun x _ => by rw [hconst F G]⟩)

end Necessity
