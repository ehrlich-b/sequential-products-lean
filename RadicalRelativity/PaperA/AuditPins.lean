/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.PaperA.Statement

set_option linter.style.longLine false

/-!
# Paper A: persisted statement-fidelity pins

These theorems pin, by definitional equality, the exact effect-level shapes and
*bodies* that `AxiomAudit.lean` advertises: the public S2 predicate, the
effect-level product, the two product-level conclusion shapes, and — added in
the round-eight boundary hardening — the literal bodies of the S2 predicate,
`IsEffect`, `Effect`, and `EffectProduct`.  The four `_body` pins close the
"outer type preserved, body silently swapped" hole: a mutation such as
`FirstArgContinuous := (…) ∧ False`, an empty `Effect` subtype, or a drifted
`IsEffect` body would keep the earlier printed-type freezes unchanged, but it
breaks the `Iff.rfl`/`rfl` here (or, if the pin's own statement is edited to
match, trips the pin's frozen printed type in `AxiomAudit.lean`).

The S2-body pin is stated over `SequentialProductCore`, not the full
`SequentialProduct` class, so it stays nonvacuous even if a hidden impossible
field were added to `SequentialProduct` (that separate escape is closed by the
class-constructor freezes in `AxiomAudit.lean`).

Unlike anonymous `example` commands, these are **named, persisted
declarations** in a `RadicalRelativity.*` module.  They are therefore visited
by the tracked-tree axiom census in `AxiomAudit.lean`: replacing any pin's
direct proof (`rfl`, `Iff.rfl`, or `s2_first_argument`) by `sorry` introduces
`sorryAx`, and replacing it by a stray/local axiom introduces that axiom name,
either of which the census rejects.  `AxiomAudit.lean` additionally exact-closure
guards them so their closure stays exactly Lean's three core axioms.

Each pin's statement is itself the fidelity check: if the pinned definition
(`effectProduct`, `LudersConclusion`, `UniqueTwistConclusion`, the public S2
field, `IsEffect`, `Effect`, or `EffectProduct`) silently changes shape, the
`rfl`/direct term stops elaborating and the build fails.
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

/-- Body pin: the public S2 predicate is *exactly* first-variable continuity of
`a ↦ a & b` on the effect interval, with nothing conjoined.  Stated over
`SequentialProductCore` (not the full class) so it cannot be made vacuous by an
impossible extra `SequentialProduct` field.  Blocks `FirstArgContinuous := (…) ∧ False`. -/
theorem auditPin_firstArgContinuous_body {V : Type*} [SequentialProductCore V] :
    SequentialProduct.FirstArgContinuous (V := V) ↔
      ∀ ⦃b : V⦄, IsEffect b →
        ContinuousOn (fun a : V => SequentialProductCore.sp a b) {a : V | IsEffect a} :=
  Iff.rfl

/-- Body pin: `IsEffect a` is *exactly* `0 ≤ a ∧ a ≤ 𝟙`.  Blocks a body drift of
`IsEffect` that preserves its outer `V → Prop` type. -/
theorem auditPin_isEffect_body {V : Type*} [OrderUnitSpace V] (a : V) :
    IsEffect a ↔ ((0 : V) ≤ a ∧ a ≤ ousUnit) :=
  Iff.rfl

/-- Body pin: the paper-facing effect space is *exactly* the `IsEffect` subtype;
it cannot be silently replaced by an empty subtype such as `{a // IsEffect a ∧ False}`. -/
theorem auditPin_effect_body (V : Type*) [OrderUnitSpace V] :
    Effect V = {a : V // IsEffect a} :=
  rfl

/-- Body pin: the paper-facing effect-product type is *exactly* the
effect → effect → effect function space. -/
theorem auditPin_effectProduct_body (V : Type*) [OrderUnitSpace V] :
    EffectProduct V = (Effect V → Effect V → Effect V) :=
  rfl

end PaperA
