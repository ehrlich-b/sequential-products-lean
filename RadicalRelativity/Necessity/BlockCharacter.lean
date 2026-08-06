/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.TwistIdentification

set_option linter.style.longLine false

/-!
# The block character of `χ̃`  (closing the ℂ lane)

The last input of the twist identification is the *group-level* block action of
the comparison character.  This file packages it as a **character**:

* `chiEntry r i j : ℂ →ₗ[ℝ] ℂ` — the action of `χ̃(r)` read on the `(i,j)` block.
* `chiTilde_block_eq` — `χ̃(r) (blockHerm i j z) = blockHerm i j (chiEntry r i j z)`,
  i.e. `chiEntry` *is* the block action (upgrading the existence statement
  `chiTilde_block_exists` to a computed value).
* `chiEntry_normSq` — it is an isometry of `ℂ`.
* `chiEntry_zero`, `chiEntry_add` — it is a one-parameter family in `r`:
  `chiEntry 0 = id` and `chiEntry (r + r') = chiEntry r ∘ chiEntry r'`.

So `r ↦ chiEntry r i j` is a homomorphism from `ℝⁿ` into the isometries of `ℂ`.
Feeding it to `multiParameter_eq_exp` (or, once its values are known to be
`ℂ`-multiplications, to M5's `circleCharacter_linear_functional`) is what
identifies the block action with the rotation by `t_F(r_i − r_j)` and closes
`chiTilde_eq_adU_of_block`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The block entry map of the character -/

/-- The action of `χ̃(r)` read on the `(i,j)` block, as an `ℝ`-linear map of `ℂ`. -/
def chiEntry (hS2 : P.FirstArgContinuous) (r : n → ℝ) (i j : n) : ℂ →ₗ[ℝ] ℂ :=
  entryLm i j
    ∘ₗ (((chiTilde P hS2 r).val : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    ∘ₗ blockHermLm i j)

@[simp]
theorem chiEntry_apply (hS2 : P.FirstArgContinuous) (r : n → ℝ) (i j : n) (z : ℂ) :
    chiEntry P hS2 r i j z
      = ((chiTilde P hS2 r).val (blockHerm i j z)).mat i j := rfl

/-- **`chiEntry` is the block action**: the existence statement
`chiTilde_block_exists` is upgraded to a computed value, because the block's
`(i,j)` entry reads the parameter back (`blockHerm_entry`). -/
theorem chiTilde_block_eq (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    (chiTilde P hS2 r).val (blockHerm i j z)
      = blockHerm i j (chiEntry P hS2 r i j z) := by
  obtain ⟨w, hw, -⟩ := chiTilde_block_exists P hS2 hjord r hij z
  rw [hw]
  congr 1
  rw [chiEntry_apply, hw, blockHerm_entry hij]

/-- `chiEntry` is an isometry of `ℂ`. -/
theorem chiEntry_normSq (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    Complex.normSq (chiEntry P hS2 r i j z) = Complex.normSq z := by
  obtain ⟨w, hw, hn⟩ := chiTilde_block_exists P hS2 hjord r hij z
  rw [chiEntry_apply, hw, blockHerm_entry hij]
  exact hn

/-! ## The one-parameter family laws -/

/-- At `r = 0` the block action is the identity. -/
theorem chiEntry_zero (hS2 : P.FirstArgContinuous) {i j : n} (hij : i ≠ j) :
    chiEntry P hS2 0 i j = LinearMap.id := by
  apply LinearMap.ext
  intro z
  rw [chiEntry_apply, chiTilde_zero P hS2]
  show (blockHerm i j z).mat i j = z
  exact blockHerm_entry hij z

/-- **The block action is multiplicative in `r`**: `χ̃` is a character and the
block is invariant, so the entry maps compose. -/
theorem chiEntry_add (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r r' : n → ℝ) {i j : n} (hij : i ≠ j) :
    chiEntry P hS2 (r + r') i j
      = (chiEntry P hS2 r i j).comp (chiEntry P hS2 r' i j) := by
  apply LinearMap.ext
  intro z
  rw [chiEntry_apply, LinearMap.comp_apply, chiEntry_apply]
  have hmul : (chiTilde P hS2 (r + r')).val
      = ((chiTilde P hS2 r).val).comp ((chiTilde P hS2 r').val) := by
    rw [chiTilde_add P hS2 hjord r r', Units.val_mul]
    rfl
  rw [hmul]
  show ((chiTilde P hS2 r).val ((chiTilde P hS2 r').val (blockHerm i j z))).mat i j
    = _
  rw [chiTilde_block_eq P hS2 hjord r' hij z]

/-- The block action, as a homomorphism from `ℝⁿ` into the `ℝ`-linear
isometries of `ℂ` — the data `multiParameter_eq_exp` consumes. -/
theorem chiEntry_isCharacter (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) :
    chiEntry P hS2 0 i j = LinearMap.id
      ∧ (∀ r r' : n → ℝ, chiEntry P hS2 (r + r') i j
          = (chiEntry P hS2 r i j).comp (chiEntry P hS2 r' i j))
      ∧ (∀ (r : n → ℝ) (z : ℂ),
          Complex.normSq (chiEntry P hS2 r i j z) = Complex.normSq z) :=
  ⟨chiEntry_zero P hS2 hij,
    fun r r' => chiEntry_add P hS2 hjord r r' hij,
    fun r z => chiEntry_normSq P hS2 hjord r hij z⟩

end Necessity
