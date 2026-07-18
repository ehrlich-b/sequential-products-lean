/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Tactic.Linarith

set_option linter.style.longLine false

/-!
# Order Unit Spaces

An **order unit space** (V, V⁺, 1) is a real ordered vector space with a distinguished
Archimedean order unit.

## Main definitions

* `OrderUnitSpace` — typeclass for ordered real vector spaces with Archimedean order unit
* `OrderUnitSpace.IsEffect` — predicate for the effect space [0, 1]_V

## References

* Alfsen-Shultz, Geometry of State Spaces of Operator Algebras
* van de Wetering, arXiv:1803.11139
-/

noncomputable section

/-- An order unit space is a real vector space with a partial order compatible
    with addition and a distinguished Archimedean order unit. -/
class OrderUnitSpace (V : Type*) extends
    AddCommGroup V,
    Module ℝ V,
    PartialOrder V where
  /-- Addition respects order on the left. -/
  add_le_add_left : ∀ (a b : V), a ≤ b → ∀ c, c + a ≤ c + b
  /-- The order unit. -/
  ousUnit : V
  /-- Nonneg scalar mult is monotone. -/
  smul_nonneg_mono : ∀ (r : ℝ), 0 ≤ r → ∀ {a b : V}, a ≤ b → r • a ≤ r • b
  /-- The order unit is positive. -/
  ousUnit_nonneg : (0 : V) ≤ ousUnit
  /-- Archimedean: every element bounded by a scalar multiple of the unit. -/
  archimedean : ∀ a : V, ∃ r : ℝ, 0 ≤ r ∧ a ≤ r • ousUnit

namespace OrderUnitSpace

variable {V : Type*} [OrderUnitSpace V]

scoped notation "𝟙" => OrderUnitSpace.ousUnit (V := _)

-- Ordered group lemmas derived from add_le_add_left

theorem add_le_add_right' {a b : V} (h : a ≤ b) (c : V) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]
  exact add_le_add_left a b h c

theorem neg_le_neg {a b : V} (h : a ≤ b) : -b ≤ -a := by
  have h1 := add_le_add_right' h (-b)
  rw [add_neg_cancel] at h1
  have h2 := add_le_add_right' h1 (-a)
  simp [add_assoc, add_neg_cancel, zero_add, add_zero] at h2
  exact h2

theorem neg_nonneg_of_nonpos {a : V} (h : a ≤ 0) : (0 : V) ≤ -a := by
  have := neg_le_neg h
  simp at this
  exact this

theorem neg_nonpos_of_nonneg {a : V} (h : (0 : V) ≤ a) : -a ≤ 0 := by
  have := neg_le_neg h
  simp at this
  exact this

theorem sub_nonneg_of_le {a b : V} (h : a ≤ b) : (0 : V) ≤ b - a := by
  have h1 := add_le_add_right' h (-a)
  rw [add_neg_cancel] at h1
  rwa [sub_eq_add_neg]

theorem sub_le_self_of_nonneg {b : V} {a : V} (h : (0 : V) ≤ a) : b - a ≤ b := by
  rw [sub_eq_add_neg]
  have h1 : -a ≤ 0 := neg_nonpos_of_nonneg h
  have h2 := add_le_add_left (-a) (0 : V) h1 b
  rwa [add_zero] at h2

theorem le_add_of_nonneg_right {a b : V} (h : (0 : V) ≤ b) : a ≤ a + b := by
  have h1 := add_le_add_left (0 : V) b h a
  rw [add_zero] at h1
  exact h1

-- Effect space

/-- An effect is an element `a` with `0 ≤ a ≤ 𝟙`. -/
def IsEffect (a : V) : Prop := (0 : V) ≤ a ∧ a ≤ 𝟙

theorem isEffect_zero : IsEffect (0 : V) :=
  ⟨le_refl 0, ousUnit_nonneg⟩

theorem isEffect_unit : IsEffect (𝟙 : V) :=
  ⟨ousUnit_nonneg, le_refl 𝟙⟩

/-- The orthocomplement `𝟙 - a` of an effect is an effect. -/
theorem IsEffect.ortho {a : V} (h : IsEffect a) :
    IsEffect (𝟙 - a) :=
  ⟨sub_nonneg_of_le h.2, sub_le_self_of_nonneg h.1⟩

/-- Two effects are orthogonal if `a + b ≤ 𝟙`. -/
def AreOrthogonal (a b : V) : Prop := a + b ≤ 𝟙

/-- A sharp effect (projective unit) is an effect `p` with no nonzero
    effect below both `p` and `𝟙 - p`. -/
def IsSharp (p : V) : Prop :=
  IsEffect p ∧ ∀ (a : V), IsEffect a → a ≤ p → a ≤ 𝟙 - p → a = 0

/-- Sum of nonneg elements is nonneg. -/
theorem add_nonneg {a b : V} (ha : (0 : V) ≤ a) (hb : (0 : V) ≤ b) :
    (0 : V) ≤ a + b :=
  le_trans ha (le_add_of_nonneg_right hb)

/-- Addition of effects whose sum is bounded. -/
theorem IsEffect.add_of_le_unit {a b : V} (ha : IsEffect a) (hb : IsEffect b)
    (hab : a + b ≤ 𝟙) : IsEffect (a + b) :=
  ⟨add_nonneg ha.1 hb.1, hab⟩

end OrderUnitSpace
