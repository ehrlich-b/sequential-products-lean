/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SequentialProduct

set_option linter.style.longLine false

/-!
# Paper A: statement-fidelity boundary

This module freezes the effect-level meaning of the paper's S1--S7 assumption
and the two product-level conclusion shapes that a complete formalization must
eventually prove.

It intentionally proves **no classification theorem**.  In particular, merely
constructing a `LudersConclusion` or `UniqueTwistConclusion` proposition is not
evidence that the proposition holds.  The value of this module is narrower and
auditable: a future capstone cannot silently conclude only `T = 0`, or equality
of interface scalars, while being described as a theorem about the original
sequential product.

The exact S1--S7 data are the root typeclass `SequentialProduct`:

* `SequentialProductCore` contains S1, S3--S7 and effect codomain closure;
* `SequentialProduct.sp_continuous_left` is S2, continuity of
  `a ↦ a & b` on the effect interval in the norm topology.

The concrete EJA reference maps `Q_{√a}` and
`a^(1/2+it) b a^(1/2-it)` do not yet exist in this development.  Consequently
they are parameters below.  Replacing those parameters by concrete definitions
and proving the resulting propositions is future work beyond the scope of the
released conditional skeleton, which the paper's appendix discloses as such.
-/

noncomputable section

open OrderUnitSpace SequentialProduct SequentialProductCore

namespace PaperA

/-- The effect interval `[0, 𝟙]` as a subtype. -/
abbrev Effect (V : Type*) [OrderUnitSpace V] := {a : V // IsEffect a}

/-- A binary operation genuinely typed from effects to effects. -/
abbrev EffectProduct (V : Type*) [OrderUnitSpace V] := Effect V → Effect V → Effect V

/-- Restrict an exact S1--S7 sequential product to its honest effect domain and
codomain.  Values of the convenience operation outside the effect interval do
not occur in paper-facing statements. -/
def effectProduct (V : Type*) [SequentialProduct V] : EffectProduct V :=
  fun a b => ⟨a.1 & b.1, sp_effect a.2 b.2⟩

@[simp] theorem effectProduct_val {V : Type*} [SequentialProduct V]
    (a b : Effect V) : (effectProduct V a b : V) = a.1 & b.1 := rfl

/-- Signature-fidelity certificate for paper S2.  This theorem is intentionally
small: it makes Lean elaborate the exact first-variable continuity statement
from the public `SequentialProduct` interface. -/
theorem s2_first_argument {V : Type*} [SequentialProduct V] {b : V}
    (hb : IsEffect b) :
    ContinuousOn (fun a : V => a & b) {a : V | IsEffect a} :=
  SequentialProduct.sp_continuous_left hb

/-- Equality of the unknown effect-level product with a supplied reference
product. -/
def AgreesWith {V : Type*} [OrderUnitSpace V]
    (unknown reference : EffectProduct V) : Prop :=
  ∀ a b, unknown a b = reference a b

/-- The literal conclusion shape of the real, quaternionic and Albert branches:
the original product equals the supplied Lüders reference on every pair of
effects.  A completed formalization must instantiate `luders` concretely. -/
def LudersConclusion (V : Type*) [SequentialProduct V]
    (luders : EffectProduct V) : Prop :=
  AgreesWith (effectProduct V) luders

/-- The literal labelled complex conclusion shape: there is a unique real
parameter whose concrete twist product equals the original product on all
effects.  A completed formalization must instantiate `twist` by matrix powers
and prove this proposition, including singular effects. -/
def UniqueTwistConclusion (V : Type*) [SequentialProduct V]
    (twist : ℝ → EffectProduct V) : Prop :=
  ∃! t : ℝ, AgreesWith (effectProduct V) (twist t)

end PaperA
