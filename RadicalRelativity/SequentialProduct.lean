/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.OrderUnitSpace
import Mathlib.Tactic.Abel

set_option linter.style.longLine false

/-!
# Sequential Product Spaces

A **sequential product space** is an order unit space equipped with a binary
operation `&` on the effect space [0,1]_V satisfying axioms S1-S7 from
van de Wetering (arXiv:1803.11139, Definition 2).

The sequential product `a & b` encodes: "first test a, then test b" with
intermediate model update. This is the foundational structure from which
quantum mechanics is derived.

## Main definitions

* `SequentialProduct` — typeclass for the & operation satisfying S1-S7
* `SequentialProduct.Compatible` — two effects commute under &
* `SequentialProduct.jordanProd` — the Jordan product `a ∘ b = ½(a & b + b & a)`

## References

* van de Wetering, Sequential product spaces are Jordan algebras, arXiv:1803.11139
-/

noncomputable section

open OrderUnitSpace

/-- A **sequential product space** is an order unit space (V, 𝟙) equipped with
    a binary operation `sp : V → V → V` on effects satisfying axioms S1-S7.

    We define `sp` on all of V for convenience; the axioms only constrain
    behavior on the effect space [0,1]_V. -/
class SequentialProduct (V : Type*) extends OrderUnitSpace V where
  /-- The sequential product operation `a & b`. -/
  sp : V → V → V
  -- S1: Additivity in second argument: a & (b + c) = a & b + a & c when b + c ≤ 𝟙
  sp_add_right : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit → sp a (b + c) = sp a b + sp a c
  -- S2: Positivity in second argument (equivalent to right-monotonicity via S1)
  -- Van de Wetering S2: b ↦ a & b is positive, i.e. b₁ ≤ b₂ → a & b₁ ≤ a & b₂
  sp_mono_right : ∀ {a b₁ b₂ : V}, IsEffect a → IsEffect b₁ → IsEffect b₂ →
    b₁ ≤ b₂ → sp a b₁ ≤ sp a b₂
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
  -- Linearity of L_a on effect differences: a & (b - c) = a & b - a & c
  -- Follows from van de Wetering's S2 (continuity of b ↦ a & b).
  -- Strictly stronger than sp_sub_right (which requires c ≤ b).
  sp_sub_right_general : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    sp a (b - c) = sp a b - sp a c

namespace SequentialProduct

variable {V : Type*} [SequentialProduct V]

/-- Notation for the sequential product. -/
scoped infixl:70 " & " => SequentialProduct.sp

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
