/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.OrderUnitSpace
import Mathlib.Tactic.Abel
import Mathlib.Topology.Basic

set_option linter.style.longLine false

/-!
# Sequential Product Spaces: exact S1--S7 boundary

A **sequential product space** is an order unit space equipped with a binary
operation `&` on the effect space [0,1]_V satisfying axioms S1--S7 from
van de Wetering (arXiv:1803.11139, Definition 2).

This file separates the algebraic core (S1 and S3--S7) from the topological
axiom S2 without weakening the public definition. `SequentialProductCore`
carries the algebraic core and effect closure. `FirstArgContinuous` is the
literal S2 predicate in the norm topology supplied by `OrderUnitSpace`.
`SequentialProduct` extends the core with that S2 proof; on the paper's
finite-dimensional simple EJAs, where the carried norm is equivalent to the
order-unit norm, it is exactly the seven-axiom paper interface.

The sequential product `a & b` encodes: "first test a, then test b" with
intermediate model update. This is the foundational structure from which
quantum mechanics is derived.

## Main definitions

* `SequentialProductCore` — algebraic core: S1, S3--S7, and effect closure
* `FirstArgContinuous` — exact S2, continuity of `a ↦ a & b` on effects
* `SequentialProduct` — exact paper interface, S1--S7
* `SequentialProduct.Compatible` — two effects commute under &
* `SequentialProduct.jordanProd` — the Jordan product `a ∘ b = ½(a & b + b & a)`

## References

* van de Wetering, Sequential product spaces are Jordan algebras, arXiv:1803.11139
-/

noncomputable section

open OrderUnitSpace

/-- The **algebraic core** of a sequential product space: an order unit space
    `(V, 𝟙)` equipped with a binary operation `sp : V → V → V` whose
    restriction to effects satisfies S1 and S3--S7.

    We define `sp` on all of V for convenience; the axioms only constrain
    behavior on the effect space `[0,1]_V`.  `sp_effect` is not an eighth axiom:
    it records the codomain of the paper's effect-level operation.  Paper S2 is
    the separate predicate `FirstArgContinuous` below. -/
class SequentialProductCore (V : Type*) extends OrderUnitSpace V where
  /-- The sequential product operation `a & b`. -/
  sp : V → V → V
  -- S1: Additivity in second argument: a & (b + c) = a & b + a & c when b + c ≤ 𝟙
  sp_add_right : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit → sp a (b + c) = sp a b + sp a c
  -- S3: Unitality: 𝟙 & a = a
  sp_unit_left : ∀ {a : V}, IsEffect a → sp ousUnit a = a
  -- S4: Symmetry of orthogonality: a & b = 0 → b & a = 0
  sp_zero_symm : ∀ {a b : V}, IsEffect a → IsEffect b → sp a b = 0 → sp b a = 0
  -- S5: Associativity of compatible effects: a|b → a & (b & c) = (a & b) & c
  sp_assoc_of_compatible : ∀ {a b c : V},
    IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a (sp b c) = sp (sp a b) c
  -- S6a: Compatibility with orthocomplement: a|b → a|(𝟙 - b)
  compatible_ortho : ∀ {a b : V}, IsEffect a → IsEffect b →
    sp a b = sp b a → sp a (ousUnit - b) = sp (ousUnit - b) a
  -- S6b: Additivity of compatibility: a|b ∧ a|c → a|(b + c) when b + c ≤ 𝟙
  compatible_add : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit →
    sp a b = sp b a → sp a c = sp c a →
    sp a (b + c) = sp (b + c) a
  -- S7: Multiplicativity of compatibility: a|b ∧ a|c → a|(b & c)
  compatible_sp : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a c = sp c a →
    sp a (sp b c) = sp (sp b c) a
  -- Effect closure: sp maps effects to effects
  sp_effect : ∀ {a b : V}, IsEffect a → IsEffect b → IsEffect (sp a b)

namespace SequentialProduct

open SequentialProductCore

variable {V : Type*} [SequentialProductCore V]

/-- Notation for the sequential product. -/
scoped infixl:70 " & " => SequentialProductCore.sp

/-- **Paper axiom S2, exactly.** For every effect `b`, the map
`a ↦ a & b` is continuous on the effect interval in the ambient topology.

The ambient topology is the norm topology carried by `OrderUnitSpace`
(`NormedAddCommGroup`/`NormedSpace ℝ`); on the paper's finite-dimensional simple
EJAs this is the order-unit norm, all norms there being equivalent.  Naming the
predicate prevents the former variable-swap bug, where second-variable
monotonicity was labelled "S2" even though Definition 2 requires first-variable
norm continuity. -/
def FirstArgContinuous : Prop :=
  ∀ ⦃b : V⦄, IsEffect b →
    ContinuousOn (fun a : V => a & b) {a : V | IsEffect a}

/-- The exact S1--S7 sequential-product interface of van de Wetering,
Definition 2. S1 and S3--S7 come from the inherited algebraic core; the field
is precisely first-variable norm continuity S2. -/
class _root_.SequentialProduct (V : Type*) extends SequentialProductCore V where
  sp_continuous_left : FirstArgContinuous (V := V)

/-- Unbundled spelling of the paper's S2 (first-variable continuity), useful in
theorem signatures and statement-fidelity audits; S1 and S3--S7 remain
typeclass-side in `SequentialProductCore`. -/
def PaperS2 : Prop := FirstArgContinuous (V := V)

/-- Two effects are compatible if they commute under &. -/
def Compatible (a b : V) : Prop :=
  IsEffect a ∧ IsEffect b ∧ (a & b) = (b & a)

/-- The Jordan product: `a ∘ᴶ b = ½ (a & b + b & a)`. -/
def jordanProd (a b : V) : V := (1/2 : ℝ) • ((a & b) + (b & a))

scoped infixl:70 " ∘ᴶ " => jordanProd

/-- A sharp effect under the sequential product: p & p = p. -/
def IsIdempotent (p : V) : Prop := IsEffect p ∧ (p & p) = p

/-- The Jordan product is commutative by construction. -/
theorem jordanProd_comm (a b : V) : a ∘ᴶ b = b ∘ᴶ a := by
  unfold jordanProd
  congr 1
  exact add_comm _ _

/-- For compatible effects, the Jordan product equals the sequential product. -/
theorem jordanProd_eq_sp_of_compatible {a b : V}
    (h : Compatible a b) : a ∘ᴶ b = a & b := by
  unfold jordanProd
  rw [h.2.2]
  rw [← two_smul ℝ (b & a)]
  rw [smul_smul]
  norm_num

/-- Sharp effects are compatible with themselves. -/
theorem idempotent_self_compatible {p : V} (hp : IsIdempotent p) :
    Compatible p p :=
  ⟨hp.1, hp.1, rfl⟩

/-- Zero is a right annihilator. -/
theorem sp_zero_right {a : V} (ha : IsEffect a) : a & (0 : V) = 0 := by
  have h0 : (0 : V) + 0 ≤ 𝟙 := by rw [add_zero]; exact ousUnit_nonneg
  have h := sp_add_right ha isEffect_zero isEffect_zero h0
  rw [add_zero] at h
  have key : a & 0 + a & 0 = a & 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel key

/-- Zero is a left annihilator. -/
theorem sp_zero_left {a : V} (ha : IsEffect a) : (0 : V) & a = 0 := by
  exact sp_zero_symm ha isEffect_zero (sp_zero_right ha)

/-- 𝟙 is a right identity for effects. -/
theorem sp_unit_right {a : V} (ha : IsEffect a) : a & (𝟙 : V) = a := by
  have hcompat : a & (0 : V) = (0 : V) & a := by
    rw [sp_zero_right ha, sp_zero_left ha]
  have h := compatible_ortho ha isEffect_zero hcompat
  rw [sub_zero] at h
  rw [h, sp_unit_left ha]

/-- The unit is compatible with everything. -/
theorem unit_compatible {a : V} (ha : IsEffect a) :
    Compatible (ousUnit) a :=
  ⟨isEffect_unit, ha, by rw [sp_unit_left ha, sp_unit_right ha]⟩

/-- The sequential product is nonneg on effects. -/
theorem sp_nonneg {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    (0 : V) ≤ a & b :=
  (sp_effect ha hb).1

/-- Right monotonicity is derived from S1 and effect closure; it is not paper
S2 and therefore is not an independent structure field. -/
theorem sp_mono_right {a b₁ b₂ : V} (ha : IsEffect a)
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂) (hle : b₁ ≤ b₂) :
    a & b₁ ≤ a & b₂ := by
  have hdiff : IsEffect (b₂ - b₁) :=
    ⟨sub_nonneg_of_le hle,
      le_trans (sub_le_self_of_nonneg hb₁.1) hb₂.2⟩
  have hsum : b₁ + (b₂ - b₁) ≤ (𝟙 : V) := by
    have heq : b₁ + (b₂ - b₁) = b₂ := by abel
    rw [heq]
    exact hb₂.2
  have hadd := sp_add_right ha hb₁ hdiff hsum
  have heq : b₁ + (b₂ - b₁) = b₂ := by abel
  rw [heq] at hadd
  rw [hadd]
  exact le_add_of_nonneg_right (sp_effect ha hdiff).1

/-- The sequential product is bounded by the left argument: a & b ≤ a. -/
theorem sp_le_left {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    a & b ≤ a := by
  have h := sp_mono_right ha hb isEffect_unit hb.2
  rw [sp_unit_right ha] at h
  exact h

/-- **Subtractive form of S1**: if `c ≤ b` (both effects), then
    `a & (b - c) = a & b - a & c`.

    Proof: from S1, a & b = a & (c + (b - c)) = a & c + a & (b - c),
    so a & (b - c) = a & b - a & c. -/
theorem sp_sub_right {a b c : V} (ha : IsEffect a) (hb : IsEffect b)
    (hc : IsEffect c) (hle : c ≤ b) (hbc_eff : IsEffect (b - c)) :
    a & (b - c) = a & b - a & c := by
  have hsum : c + (b - c) ≤ 𝟙 := by
    have heq : c + (b - c) = b := by abel
    rw [heq]; exact hb.2
  have h := sp_add_right ha hc hbc_eff hsum
  have heq : c + (b - c) = b := by abel
  rw [heq] at h
  -- h : a & b = a & c + a & (b - c)
  -- goal : a & (b - c) = a & b - a & c
  have : a & b - a & c = a & (b - c) := by
    rw [h]; abel
  exact this.symm

end SequentialProduct

/-! ## Sequential products ON a fixed order-unit space

The necessity direction quantifies over the unknown product while the order-unit
structure stays THE structure of the concrete carrier (the paper fixes the EJA
and classifies operations on its effects).  An instance-quantified
`[SequentialProductCore V]` cannot express this: it carries its own
`toOrderUnitSpace` parent, which the elaborator treats as unrelated to the
carrier's canonical instance, so none of the carrier's order/norm/spectral
lemmas apply to the effects it speaks about.  `SequentialProductOn` is the
carrier-pinned formulation: the same eight fields, elaborated over the *ambient*
`[OrderUnitSpace V]`. -/

/-- An S1, S3–S7 sequential product structure **on** a fixed order-unit space:
the fields of `SequentialProductCore`, with the order-unit parent pinned to the
ambient instance rather than bundled.  Paper S2 for a `P : SequentialProductOn V`
is the unbundled `P.FirstArgContinuous` below. -/
structure SequentialProductOn (V : Type*) [OrderUnitSpace V] where
  /-- The sequential product operation `a & b`. -/
  sp : V → V → V
  sp_add_right : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit → sp a (b + c) = sp a b + sp a c
  sp_unit_left : ∀ {a : V}, IsEffect a → sp ousUnit a = a
  sp_zero_symm : ∀ {a b : V}, IsEffect a → IsEffect b → sp a b = 0 → sp b a = 0
  sp_assoc_of_compatible : ∀ {a b c : V},
    IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a (sp b c) = sp (sp a b) c
  compatible_ortho : ∀ {a b : V}, IsEffect a → IsEffect b →
    sp a b = sp b a → sp a (ousUnit - b) = sp (ousUnit - b) a
  compatible_add : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit →
    sp a b = sp b a → sp a c = sp c a →
    sp a (b + c) = sp (b + c) a
  compatible_sp : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a c = sp c a →
    sp a (sp b c) = sp (sp b c) a
  sp_effect : ∀ {a b : V}, IsEffect a → IsEffect b → IsEffect (sp a b)

namespace SequentialProductOn

variable {V : Type*} [OrderUnitSpace V]

/-- Repackage as a bundled `SequentialProductCore` whose parent is *definitionally*
the ambient instance — the bridge that lets the derived lemma layer of
`SequentialProduct` apply to a pinned product. -/
def toCore (P : SequentialProductOn V) : SequentialProductCore V :=
  { ‹OrderUnitSpace V› with
    sp := P.sp
    sp_add_right := P.sp_add_right
    sp_unit_left := P.sp_unit_left
    sp_zero_symm := P.sp_zero_symm
    sp_assoc_of_compatible := P.sp_assoc_of_compatible
    compatible_ortho := P.compatible_ortho
    compatible_add := P.compatible_add
    compatible_sp := P.compatible_sp
    sp_effect := P.sp_effect }

/-- Paper S2 for a pinned product: first-argument continuity on effects in the
carrier's norm topology. -/
def FirstArgContinuous (P : SequentialProductOn V) : Prop :=
  ∀ ⦃b : V⦄, IsEffect b → ContinuousOn (fun a : V => P.sp a b) {a : V | IsEffect a}

variable (P : SequentialProductOn V)

/-- A bundled `SequentialProductCore` on any type is a pinned product over its own
parent order-unit structure (the converse packaging). -/
def _root_.SequentialProductCore.toSequentialProductOn
    (W : Type*) [inst : SequentialProductCore W] :
    @SequentialProductOn W inst.toOrderUnitSpace :=
  { sp := SequentialProductCore.sp
    sp_add_right := SequentialProductCore.sp_add_right
    sp_unit_left := SequentialProductCore.sp_unit_left
    sp_zero_symm := SequentialProductCore.sp_zero_symm
    sp_assoc_of_compatible := SequentialProductCore.sp_assoc_of_compatible
    compatible_ortho := SequentialProductCore.compatible_ortho
    compatible_add := SequentialProductCore.compatible_add
    compatible_sp := SequentialProductCore.compatible_sp
    sp_effect := SequentialProductCore.sp_effect }

/- Derived lemmas, transported from the `SequentialProduct` layer through
`toCore` (whose parent is definitionally the ambient instance). -/

theorem sp_zero_right {a : V} (ha : IsEffect a) : P.sp a 0 = 0 :=
  letI := P.toCore
  SequentialProduct.sp_zero_right ha

theorem sp_zero_left {a : V} (ha : IsEffect a) : P.sp 0 a = 0 :=
  letI := P.toCore
  SequentialProduct.sp_zero_left ha

theorem sp_unit_right {a : V} (ha : IsEffect a) : P.sp a ousUnit = a :=
  letI := P.toCore
  SequentialProduct.sp_unit_right ha

theorem sp_nonneg {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    (0 : V) ≤ P.sp a b :=
  letI := P.toCore
  SequentialProduct.sp_nonneg ha hb

theorem sp_mono_right {a b₁ b₂ : V} (ha : IsEffect a)
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂) (hle : b₁ ≤ b₂) :
    P.sp a b₁ ≤ P.sp a b₂ :=
  letI := P.toCore
  SequentialProduct.sp_mono_right ha hb₁ hb₂ hle

theorem sp_le_left {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    P.sp a b ≤ a :=
  letI := P.toCore
  SequentialProduct.sp_le_left ha hb

theorem sp_sub_right {a b c : V} (ha : IsEffect a) (hb : IsEffect b)
    (hc : IsEffect c) (hle : c ≤ b) (hbc_eff : IsEffect (b - c)) :
    P.sp a (b - c) = P.sp a b - P.sp a c :=
  letI := P.toCore
  SequentialProduct.sp_sub_right ha hb hc hle hbc_eff

end SequentialProductOn
