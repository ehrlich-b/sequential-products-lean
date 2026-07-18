/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.PaperA.Statement

set_option linter.style.longLine false

/-!
# Paper A: persisted statement-fidelity pins

These four theorems pin, by definitional equality, the exact effect-level
shapes that `AxiomAudit.lean` advertises: the public S2 predicate, the
effect-level product, and the two product-level conclusion shapes.

Unlike anonymous `example` commands, these are **named, persisted
declarations** in a `RadicalRelativity.*` module.  They are therefore visited
by the project-wide axiom census in `AxiomAudit.lean`: replacing any pin's
direct proof (`rfl` or `s2_first_argument`) by `sorry` introduces `sorryAx`,
and replacing it by a stray/local axiom introduces that axiom name, either of
which the census rejects.  `AxiomAudit.lean` additionally exact-closure guards
all four so their closure stays exactly Lean's three core axioms.

Each pin's statement is itself the fidelity check: if the pinned definition
(`effectProduct`, `LudersConclusion`, `UniqueTwistConclusion`, or the public
S2 field) silently changes shape, the `rfl`/direct term stops elaborating and
the build fails.
-/

noncomputable section

open OrderUnitSpace SequentialProduct SequentialProductCore

namespace PaperA

/-- Pin: the public S2 field is first-variable continuity of `a ↦ a & b` on the
effect interval, in the carried norm. -/
theorem auditPin_s2 {V : Type*} [SequentialProduct V] {b : V}
    (hb : IsEffect b) :
    ContinuousOn
      (fun a : V => SequentialProductCore.sp a b)
      {a : V | IsEffect a} :=
  s2_first_argument hb

/-- Pin: the effect-level product is the core product on the underlying values. -/
theorem auditPin_effectProduct {V : Type*} [SequentialProduct V] (a b : Effect V) :
    (effectProduct V a b : V) = SequentialProductCore.sp a.1 b.1 :=
  rfl

/-- Pin: the Lüders conclusion is pointwise agreement of the product with the
supplied reference on every pair of effects. -/
theorem auditPin_luders {V : Type*} [SequentialProduct V] (luders : EffectProduct V) :
    LudersConclusion V luders
      = ∀ a b, effectProduct V a b = luders a b :=
  rfl

/-- Pin: the complex conclusion is existence of a unique real twist parameter
whose product agrees with the original on every pair of effects. -/
theorem auditPin_uniqueTwist {V : Type*} [SequentialProduct V]
    (twist : ℝ → EffectProduct V) :
    UniqueTwistConclusion V twist
      = ∃! t : ℝ, ∀ a b, effectProduct V a b = twist t a b :=
  rfl

end PaperA
