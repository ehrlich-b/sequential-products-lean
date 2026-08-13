/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.EJA.Pattern
import RadicalRelativity.MasterTheorem.Interface

set_option linter.style.longLine false

/-!
# The bridge: the EJA layer, usable from the bilinear-map interface

**ARC-9 block 9.21, 2026-08-13.**

Blocks 9.15 and 9.20 identified why the EJA layer could not be pointed at
`MasterTheorem/Interface.lean`: `ComparisonSetup` carries its product as a **bundled bilinear
map** `jordan : J →ₗ[ℝ] J →ₗ[ℝ] J` over `[NormedAddCommGroup J] [InnerProductSpace ℝ J]`,
while the EJA layer runs on the **typeclasses** `[NonUnitalNonAssocCommRing J] [Module ℝ J]`.
Assuming both gives two different `AddCommGroup J` instances, and `Module ℝ J` then fails to
synthesise at the EJA layer's use site — a textbook Mathlib diamond, with a failing example
recorded at 9.20.

**This file dodges it.** `ringOfBilinear` builds the multiplicative structure *on the ambient
additive group* — `{ (inferInstance : AddCommGroup J) with mul := fun x y => m x y, … }` —
so only one `AddCommGroup` is ever in play. Nothing is assumed twice.

## The payoff

`opCommute_scalarOn_interface` proves **`MasterTheorem.OpCommute m a b`** — the interface's own
predicate, the one `CoalescenceSetup.simDiag_opCommute` is stated in — from the Jordan
identity, for `a` scalar on `range c` and `b ∈ J₂(c)`. That is the load-bearing Faraut–Korányi
hypothesis under `lem:coalescence` (manifest row 16), no longer needing to be a citation.

## What this does NOT do

★ **It does not close row 16, and no manifest row moves.** Three things are still required:

1. `ComparisonSetup` does not *assert* the Jordan identity for its `jordan` field — it has
   `jordan_comm` but nothing else — so every theorem here takes `hjordan` as a hypothesis.
   That is the honest state of the interface, not a defect of this file.
2. The frame equations (`p i` idempotent, orthogonal, summing to `e`, and
   `aOf r = ∑ exp (r i) • p i`) are still not fields of `ComparisonSetup`; see
   `EJA/Frame.lean`.
3. Discharging the fields on an actual `CoalescenceSetup` means *constructing* one, which
   touches `AxiomAudit.lean`'s Layer-6 constructor freeze.

What has changed is that **the blocker is no longer structural.** Before this file the answer
to "can the EJA layer speak to the interface at all?" was *no, there is a diamond*. It is now
*yes, and here is the theorem in the interface's own vocabulary.*

★ `jpow` and anything else whose **statement** needs the ring instance cannot be bridged this
way — the instance would have to exist before the statement elaborates. Only results whose
statements are expressible with `m` alone cross over; `peirce_poly_bilinear` and
`opCommute_scalarOn_interface` are two, and Albert's theorem is not.
-/

namespace RadicalRelativity.EJA

section Bridge

variable {J : Type*} [NormedAddCommGroup J] [Module ℝ J]

/-- Build the multiplicative structure ON the ambient additive group, from a bilinear map. -/
def ringOfBilinear (m : J →ₗ[ℝ] J →ₗ[ℝ] J) (hcomm : ∀ x y, m x y = m y x) :
    NonUnitalNonAssocCommRing J :=
  { (inferInstance : AddCommGroup J) with
    mul := fun x y => m x y
    left_distrib := fun a b c => (m a).map_add b c
    right_distrib := fun a b c => by
      show m (a + b) c = m a c + m b c
      rw [map_add]; rfl
    zero_mul := fun a => by
      show m 0 a = 0
      rw [map_zero]; rfl
    mul_zero := fun a => (m a).map_zero
    mul_comm := hcomm }


variable (m : J →ₗ[ℝ] J →ₗ[ℝ] J)

/-- `m` is linear in its first argument — the scalar-tower law for the constructed ring. -/
theorem smul_bilinear (r : ℝ) (a b : J) : m (r • a) b = r • m a b := by
  rw [map_smul]; rfl

/-- **The Peirce polynomial identity, in bilinear-map vocabulary.** -/
theorem peirce_poly_bilinear (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    {c : J} (hc : m c c = c) (y : J) :
    (2 : ℕ) • m c (m c (m c y)) + m c y = (3 : ℕ) • m c (m c y) := by
  letI : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  letI : IsCommJordan J := ⟨hjordan⟩
  exact peirce_poly hc y

/-- **`CoalescenceSetup.simDiag_opCommute`, in bilinear-map vocabulary** — this is literally
`OpCommute m a b` evaluated at `w`. -/
theorem opCommute_scalarOn_bilinear (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    {c a a₀ b : J} {mu : ℝ} (hc : m c c = c) (ha : a = mu • c + a₀)
    (ha₀ : m c a₀ = 0) (hb : m c b = b) (w : J) :
    m a (m b w) = m b (m a w) := by
  letI : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  letI : IsCommJordan J := ⟨hjordan⟩
  letI : IsScalarTower ℝ J J := ⟨fun r x y => smul_bilinear m r x y⟩
  exact opCommute_scalarOn hc ha ha₀ hb w

/-- **The FK field exactly as `CoalescenceSetup` states it**: `OpCommute`, the interface's own
predicate, derived from the Jordan identity. -/
theorem opCommute_scalarOn_interface (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    {c a a₀ b : J} {mu : ℝ} (hc : m c c = c) (ha : a = mu • c + a₀)
    (ha₀ : m c a₀ = 0) (hb : m c b = b) :
    MasterTheorem.OpCommute m a b := by
  ext w
  exact opCommute_scalarOn_bilinear m hcomm hjordan hc ha ha₀ hb w

end Bridge

end RadicalRelativity.EJA
