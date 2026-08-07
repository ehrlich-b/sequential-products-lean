/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.OrderUnitSpace

set_option linter.style.longLine false

/-!
# Direct sums of order-unit spaces  (M7 foundation)

`mthm:omnibus` classifies sequential products on a finite-dimensional formally real Jordan
algebra by decomposing it into simple factors and applying the per-type rows factorwise.
The assembly needs a carrier for that decomposition: the **direct sum** of order-unit
spaces.  Note the assembly theorem itself — "given the per-type rows, a product on a direct
sum is determined factorwise" — is provable independently of whether those rows are
finished, so this foundation is not gated on them.

* `instance : OrderUnitSpace (V × W)` — product order and norm, unit `(𝟙, 𝟙)`, with
  order-unit boundedness obtained by comparing both components against `max r₁ r₂`
  (which is what `smul_le_smul_of_le_of_nonneg` was added for).
* `isEffect_prod_iff` — an effect of a sum is exactly a pair of effects; this is the
  bookkeeping that makes "restrict a product to a summand" meaningful.

The parent `PartialOrder` is supplied explicitly: `OrderUnitSpace` extends it, and without
naming `Prod.instPartialOrder` the synthesized parent is anonymous and order hypotheses
become unprojectable.
-/

noncomputable section

namespace OrderUnitSpace

variable {V W : Type*} [OrderUnitSpace V] [OrderUnitSpace W]

/-- **The direct sum of two order-unit spaces is an order-unit space.** -/
instance instProd : OrderUnitSpace (V × W) where
  toPartialOrder := Prod.instPartialOrder _ _
  add_le_add_left := fun a b h c =>
    ⟨add_le_add_left a.1 b.1 h.1 c.1, add_le_add_left a.2 b.2 h.2 c.2⟩
  ousUnit := ((ousUnit : V), (ousUnit : W))
  smul_nonneg_mono := fun r hr {a b} h =>
    ⟨smul_nonneg_mono r hr h.1, smul_nonneg_mono r hr h.2⟩
  ousUnit_nonneg := ⟨ousUnit_nonneg, ousUnit_nonneg⟩
  archimedean := fun a => by
    obtain ⟨r₁, hr₁0, hr₁⟩ := archimedean a.1
    obtain ⟨r₂, hr₂0, hr₂⟩ := archimedean a.2
    refine ⟨max r₁ r₂, le_trans hr₁0 (le_max_left _ _), ?_⟩
    exact ⟨le_trans hr₁ (smul_le_smul_of_le_of_nonneg (le_max_left r₁ r₂) ousUnit_nonneg),
      le_trans hr₂ (smul_le_smul_of_le_of_nonneg (le_max_right r₁ r₂) ousUnit_nonneg)⟩

@[simp]
theorem prod_ousUnit : (ousUnit : V × W) = ((ousUnit : V), (ousUnit : W)) := rfl

/-- **An effect of a direct sum is exactly a pair of effects.**  This is what makes
"restrict a sequential product to a summand" meaningful, and it is the bookkeeping the
omnibus's factorwise assembly runs on. -/
theorem isEffect_prod_iff {a : V × W} :
    IsEffect a ↔ IsEffect a.1 ∧ IsEffect a.2 := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := h
    rw [Prod.le_def] at h0 h1
    exact ⟨⟨h0.1, h1.1⟩, ⟨h0.2, h1.2⟩⟩
  · intro h
    refine ⟨?_, ?_⟩ <;> rw [Prod.le_def]
    · exact ⟨h.1.1, h.2.1⟩
    · exact ⟨h.1.2, h.2.2⟩

end OrderUnitSpace
