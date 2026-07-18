/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.longLine false

/-!
# Base-equality dichotomy for diachronic narrowness (`prop:diachronic`)

This file formalizes the arithmetic core of the manuscript's diachronic
narrowness proposition (`prop:diachronic` in `sections/type-exclusion.tex` of
"Self-Modeling Selects Complex Quantum Mechanics"): the base-equality
dichotomy and the zero-offset identity at the complex type.

## Manuscript statements

For the Hermitian matrix families over a real division algebra `𝕂` with
`d = dim_ℝ 𝕂 ∈ {1, 2, 4}`, the dimension is `dim h_n(𝕂) = n + d·n(n−1)/2`.
The proposition's single arithmetic source is:

> `n + d·n(n−1)/2 = n²  ⟺  (d − 2)(n − 1) = 0  ⟺  d = 2` (for `n ≥ 2`),
> and at `d = 2` the offset `C(k) − P(k)` vanishes identically:
> `C(k) = (n^k)² = (n²)^k = P(k)`.

## Main results

* `Selection.base_equality` — the base equality over `ℕ`, stated in the
  doubled convention (the `/2` cleared): `2n + d·n(n−1) = 2n² ↔ d = 2`
  for `n ≥ 2`.
* `Selection.complex_zero_offset` — the zero-offset identity at `d = 2`:
  `(n^k)² = (n²)^k` for all `n, k`.
* `Selection.dimH` — the dimension count `n + d·n(n−1)/2` over `ℚ`.
* `Selection.in_family_transparency_dichotomy` — the unconditional
  arithmetic dichotomy: `dimH` is multiplicative along the in-family
  self-composite tower (`dimH (n^k) d = (dimH n d)^k` for all `k ≥ 1`)
  iff `d = 0 ∨ d = 2`.
* `Selection.in_family_transparency_iff` — the paper's form: for `d ≥ 1`
  (every real division algebra has `dim_ℝ 𝕂 ≥ 1`), transparency at all
  tensor powers holds iff `d = 2`.

## Note on the `d = 0` degenerate case

Over the bare arithmetic (with `d` an unrestricted natural number), `d = 0`
also makes `dimH` multiplicative: `dimH m 0 = m`, and `n^k` is exactly
multiplicative.  This is the classical (diagonal) count, outside the
manuscript's range `d ∈ {1, 2, 4}`.  The dichotomy lemma records the
honest two-solution fact; the headline `iff` adds the hypothesis `1 ≤ d`
that the manuscript's setting supplies.
-/

namespace Selection

/-- **Base equality** (doubled convention).  For `n ≥ 2`, the Hermitian
dimension `n + d·n(n−1)/2` equals `n²` iff `d = 2`; here both sides are
doubled to stay in `ℕ` without division. -/
theorem base_equality (n d : ℕ) (hn : 2 ≤ n) :
    2 * n + d * (n * (n - 1)) = 2 * n ^ 2 ↔ d = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  have key : 2 * (m + 2) ^ 2 = 2 * (m + 2) + 2 * ((m + 2) * (m + 1)) := by ring
  constructor
  · intro h
    rw [key] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (Nat.add_left_cancel h)
  · rintro rfl
    ring

/-- **Zero offset at the complex type.**  At `d = 2` the composite dimension
equals the product dimension at every tensor power: `C(k) = (n^k)² = (n²)^k
= P(k)`. -/
theorem complex_zero_offset (n k : ℕ) : (n ^ k) ^ 2 = (n ^ 2) ^ k := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The Hermitian dimension count `dim h_n(𝕂) = n + d·n(n−1)/2` over `ℚ`,
with `d = dim_ℝ 𝕂`. -/
def dimH (n d : ℕ) : ℚ := (n : ℚ) + (d : ℚ) * (n : ℚ) * ((n : ℚ) - 1) / 2

/-- At the complex type the dimension count is exactly `n²`. -/
lemma dimH_two (m : ℕ) : dimH m 2 = (m : ℚ) ^ 2 := by
  simp only [dimH]
  push_cast
  ring

/-- At the degenerate classical count `d = 0` the dimension is `n` itself. -/
lemma dimH_zero (m : ℕ) : dimH m 0 = (m : ℚ) := by
  simp only [dimH]
  push_cast
  ring

/-- **In-family transparency dichotomy** (unconditional arithmetic form).
For `n ≥ 2`, the dimension count is multiplicative along the in-family
self-composite tower iff `d = 0` (the classical diagonal count) or `d = 2`
(the complex type).  The `k = 2` instance already forces the dichotomy. -/
theorem in_family_transparency_dichotomy (n d : ℕ) (hn : 2 ≤ n) :
    (∀ k : ℕ, 1 ≤ k → dimH (n ^ k) d = (dimH n d) ^ k) ↔ (d = 0 ∨ d = 2) := by
  constructor
  · intro h
    have h2 := h 2 (by norm_num)
    simp only [dimH] at h2
    push_cast at h2
    have hx : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    have hpos : (0 : ℚ) < (n : ℚ) * ((n : ℚ) - 1) :=
      mul_pos (by linarith) (by linarith)
    have key : (d : ℚ) * ((d : ℚ) - 2) * ((n : ℚ) * ((n : ℚ) - 1)) ^ 2 = 0 := by
      linear_combination (-4 : ℚ) * h2
    have hd0 : (d : ℚ) * ((d : ℚ) - 2) = 0 :=
      (mul_eq_zero.mp key).resolve_right (pow_ne_zero 2 (ne_of_gt hpos))
    rcases mul_eq_zero.mp hd0 with h' | h'
    · exact Or.inl (by exact_mod_cast h')
    · have : (d : ℚ) = 2 := by linarith
      exact Or.inr (by exact_mod_cast this)
  · rintro (rfl | rfl)
    · intro k _
      rw [dimH_zero, dimH_zero]
      push_cast
      ring
    · intro k _
      rw [dimH_two, dimH_two]
      exact_mod_cast complex_zero_offset n k

/-- **In-family transparency selects the complex type** (`prop:diachronic`,
arithmetic core).  For `n ≥ 2` and `d ≥ 1` (every real division algebra has
`dim_ℝ 𝕂 ≥ 1`), the composite dimension function agrees with the product
dimension function at every tensor power iff `d = 2`. -/
theorem in_family_transparency_iff (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    (∀ k : ℕ, 1 ≤ k → dimH (n ^ k) d = (dimH n d) ^ k) ↔ d = 2 := by
  rw [in_family_transparency_dichotomy n d hn]
  omega

end Selection
