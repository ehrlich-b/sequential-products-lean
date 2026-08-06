/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.TwistGeneral
import RadicalRelativity.Necessity.SingularExtension

set_option linter.style.longLine false

/-!
# The complex classification, assembled  (ℂ lane, the `∃!` capstone)

The last two moves of the complex case:

* `twistProductOn` / `twistProductOn_firstArgContinuous` — M1's twist product
  repackaged as a *pinned* `SequentialProductOn` over the carrier's ambient
  order-unit structure (its `SequentialProductCore` already takes
  `toOrderUnitSpace := inferInstance`, so this is definitional), with S2.
* `sp_eq_twistSeq_of_effect` — **the extension to singular effects**: agreement
  with the twist product on *invertible* effects extends to **all** effects, by
  2.9's `sp_eq_on_effects_of_eq_on_posDef` (density of the invertibles + S2).
* `exists_unique_twist` — **the `∃!` capstone**: if a product with S2 agrees
  with some twist product on the invertible effects, then there is a **unique**
  real `t` with `a • b = a^{1/2+it} b a^{1/2−it}` on *every* pair of effects.
  Existence is the extension; uniqueness is `twist_param_unique`.

This is the shape of `PaperA.UniqueTwistConclusion` stated over the pinned
`SequentialProductOn` interface, which is the spelling all M2–M5 necessity
statements use (an instance-quantified `SequentialProductCore` would bundle its
own order-unit structure and detach from the carrier's lemmas).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The twist product, pinned -/

/-- M1's twist product as a pinned product over the ambient order-unit
structure. -/
def twistProductOn (t : ℝ) : SequentialProductOn (HermitianMat n ℂ) :=
  (HermitianMat.twistSequentialProductCore t).toSequentialProductOn

@[simp]
theorem twistProductOn_sp (t : ℝ) (a b : HermitianMat n ℂ) :
    (twistProductOn t).sp a b = HermitianMat.twistSeq t a b := rfl

/-- S2 for the pinned twist product. -/
theorem twistProductOn_firstArgContinuous (t : ℝ) :
    (twistProductOn (n := n) t).FirstArgContinuous :=
  fun b _ => (HermitianMat.continuous_twistSeq_left t b).continuousOn

/-! ## Extension to the singular effects -/

/-- **`prop:singular` applied to the complex classification.**  A product with S2
that agrees with the twist product on the *invertible* effects agrees with it on
**all** effects. -/
theorem sp_eq_twistSeq_of_effect (P : SequentialProductOn (HermitianMat n ℂ))
    (hS2 : P.FirstArgContinuous) (t : ℝ)
    (hinv : ∀ a b : HermitianMat n ℂ, IsEffect a → a.mat.PosDef → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b)
    (a b : HermitianMat n ℂ) (ha : IsEffect a) (hb : IsEffect b) :
    P.sp a b = HermitianMat.twistSeq t a b := by
  have hext := sp_eq_on_effects_of_eq_on_posDef P (twistProductOn t) hS2
    (twistProductOn_firstArgContinuous t) hb
    (fun a' ha' hbd' => by
      rw [twistProductOn_sp]
      exact hinv a' b ha' hbd' hb)
  exact hext a ha

/-! ## The `∃!` capstone -/

/-- **The complex classification, `∃!` form.**  For a product with S2 on
`H_N(ℂ)` (`N ≥ 2`) that agrees with *some* twist product on the invertible
effects, there is a **unique** real `t` with
`a • b = a^{1/2+it} b a^{1/2−it}` for **all** effects `a, b`.

Existence extends the invertible-effect agreement by `prop:singular`
(`sp_eq_twistSeq_of_effect`); uniqueness is the phase-probe rigidity
(`twist_param_unique`).  This is `PaperA.UniqueTwistConclusion`'s shape over the
pinned interface. -/
theorem exists_unique_twist {N : ℕ} (hN : 2 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    (hsome : ∃ t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ,
      IsEffect a → a.mat.PosDef → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b) :
    ∃! t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b := by
  obtain ⟨t, ht⟩ := hsome
  refine ⟨t, fun a b ha hb => sp_eq_twistSeq_of_effect P hS2 t ht a b ha hb, ?_⟩
  intro t' ht'
  -- both parameters reproduce `P`, so the two twist products agree on effects
  apply twist_param_unique hN
  intro a b ha hb
  rw [← ht' a b ha hb]
  exact sp_eq_twistSeq_of_effect P hS2 t ht a b ha hb

end Necessity
