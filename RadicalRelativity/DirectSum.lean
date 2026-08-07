/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SequentialProduct

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
namespace SequentialProductOn

variable {V W : Type*} [OrderUnitSpace V] [OrderUnitSpace W]

open OrderUnitSpace

/-- **The direct sum of two sequential products is a sequential product.**  This is the
*sufficiency* half of the omnibus's factorwise assembly: every S1-S7 axiom is a pointwise
identity or an implication between pointwise identities, so each one holds in `V × W`
exactly when it holds in both summands.  Compatibility is not a side condition here but
literally the equation `a & b = b & a`, which on a pair splits into its two components --
that is why no extra hypothesis is needed. -/
def prod (P : SequentialProductOn V) (Q : SequentialProductOn W) :
    SequentialProductOn (V × W) where
  sp a b := (P.sp a.1 b.1, Q.sp a.2 b.2)
  sp_add_right ha hb hc hbc := by
    rw [isEffect_prod_iff] at ha hb hc
    rw [Prod.le_def] at hbc
    exact Prod.ext_iff.mpr
      ⟨P.sp_add_right ha.1 hb.1 hc.1 hbc.1, Q.sp_add_right ha.2 hb.2 hc.2 hbc.2⟩
  sp_unit_left ha := by
    rw [isEffect_prod_iff] at ha
    exact Prod.ext_iff.mpr ⟨P.sp_unit_left ha.1, Q.sp_unit_left ha.2⟩
  sp_zero_symm ha hb h := by
    rw [isEffect_prod_iff] at ha hb
    simp only [Prod.mk_eq_zero] at h ⊢
    exact ⟨P.sp_zero_symm ha.1 hb.1 h.1, Q.sp_zero_symm ha.2 hb.2 h.2⟩
  sp_assoc_of_compatible ha hb hc h := by
    rw [isEffect_prod_iff] at ha hb hc
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨P.sp_assoc_of_compatible ha.1 hb.1 hc.1 h.1,
      Q.sp_assoc_of_compatible ha.2 hb.2 hc.2 h.2⟩
  compatible_ortho ha hb h := by
    rw [isEffect_prod_iff] at ha hb
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨P.compatible_ortho ha.1 hb.1 h.1, Q.compatible_ortho ha.2 hb.2 h.2⟩
  compatible_add ha hb hc hbc h h' := by
    rw [isEffect_prod_iff] at ha hb hc
    rw [Prod.le_def] at hbc
    simp only [Prod.mk.injEq] at h h' ⊢
    exact ⟨P.compatible_add ha.1 hb.1 hc.1 hbc.1 h.1 h'.1,
      Q.compatible_add ha.2 hb.2 hc.2 hbc.2 h.2 h'.2⟩
  compatible_sp ha hb hc h h' := by
    rw [isEffect_prod_iff] at ha hb hc
    simp only [Prod.mk.injEq] at h h' ⊢
    exact ⟨P.compatible_sp ha.1 hb.1 hc.1 h.1 h'.1,
      Q.compatible_sp ha.2 hb.2 hc.2 h.2 h'.2⟩
  sp_effect ha hb := by
    rw [isEffect_prod_iff] at ha hb
    exact isEffect_prod_iff.mpr ⟨P.sp_effect ha.1 hb.1, Q.sp_effect ha.2 hb.2⟩

@[simp]
theorem prod_sp (P : SequentialProductOn V) (Q : SequentialProductOn W) (a b : V × W) :
    (P.prod Q).sp a b = (P.sp a.1 b.1, Q.sp a.2 b.2) := rfl

end SequentialProductOn

namespace SequentialProductOn

variable {V W : Type*} [OrderUnitSpace V] [OrderUnitSpace W]

/-! ## The summand products are recoverable

The omnibus's assembly has two halves.  `prod` is sufficiency: summand products give a
product on the sum.  The lemmas below are *determination*: the summand products are read
back off the sum, so a split product carries exactly the data of its two restrictions and
the factorwise classification is not lossy.

What is **not** here is the third statement -- that *every* product on a direct sum is of
the form `P.prod Q`.  That is `prop:central`'s content (a product is compatible with each
central idempotent, hence preserves the summands), and it is the piece the manuscript
carries as a paper proof; `central_decomposition` machine-checks only its componentwise
identity.  So the assembly is certified conditional on the splitting, not unconditionally.
-/

/-- The left summand's product is the first component of the sum's, at any second
argument -- the restriction is literally a projection. -/
theorem prod_fst (P : SequentialProductOn V) (Q : SequentialProductOn W)
    (a b : V) (a' b' : W) : ((P.prod Q).sp (a, a') (b, b')).1 = P.sp a b := rfl

theorem prod_snd (P : SequentialProductOn V) (Q : SequentialProductOn W)
    (a b : V) (a' b' : W) : ((P.prod Q).sp (a, a') (b, b')).2 = Q.sp a' b' := rfl

/-- **A split product determines its factors.**  Hence the factorwise classification of
`mthm:omnibus` loses no information: distinct summand products give distinct sums. -/
theorem sp_eq_of_prod_eq {P P' : SequentialProductOn V} {Q Q' : SequentialProductOn W}
    (h : (P.prod Q).sp = (P'.prod Q').sp) : P.sp = P'.sp ∧ Q.sp = Q'.sp := by
  refine ⟨funext fun a => funext fun b => ?_, funext fun a' => funext fun b' => ?_⟩
  · have := congrFun (congrFun h (a, (0 : W))) (b, (0 : W))
    exact congrArg Prod.fst this
  · have := congrFun (congrFun h ((0 : V), a')) ((0 : V), b')
    exact congrArg Prod.snd this

end SequentialProductOn
