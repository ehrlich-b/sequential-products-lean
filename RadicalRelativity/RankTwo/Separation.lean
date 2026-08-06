/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.Complementation
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.style.longLine false

/-!
# The rank-two family is genuinely frame-dependent  (LEDGER 5.3)

`MasterTheorem/RankTwo.lean` records the frame-dependence *pair* — on the
Hadamard frame the dial reads `τ = 0` and the product is Lüders
(`sp_tau_had_is_luders`), on the reference frame it reads `τ = 1` and the
product is the unit twist (`sp_tau_std_is_unit_twist`) — but never shows the two
products **differ**.  Without that the "rank two escapes the rigidity of
`mthm:master`" claim is carried by the dial alone, not by the operation.

This file closes that gap: at `λ = (1, 4)` the two members disagree on the
coherence matrix `E₀₁`, because the off-diagonal coefficient acquires the phase
`e^{-i log 4}` and `log 4 ∈ (0, 2π)`.

* `offCoeff_sep` — the two coefficients differ.
* `sp_luders_ne_unit_twist` — hence the products differ, so the rank-two family
  is not a single product: **frame dependence is real at the level of the
  operation**.
-/

noncomputable section

open scoped Matrix

namespace RankTwo

open MasterTheorem.RankTwo

/-- The coherence matrix `E₀₁`. -/
def Ecoh : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![0, 1], ![0, 0]]

@[simp] theorem Ecoh_01 : Ecoh 0 1 = 1 := rfl

/-! ## `log 4` is a genuine phase -/

theorem log_four_pos : 0 < Real.log 4 :=
  Real.log_pos (by norm_num)

theorem log_four_lt_two_pi : Real.log 4 < 2 * Real.pi := by
  have h1 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)
    linarith
  have h2 : (3 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

/-- `e^{-i log 4} ≠ 1`: the phase is nontrivial because `log 4` lies strictly
between `0` and `2π`. -/
theorem exp_neg_log_four_ne_one :
    Complex.exp ((↑(-(Real.log 4)) : ℂ) * Complex.I) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  -- `−log 4 = n · 2π`, with `0 < log 4 < 2π`
  have hreal : -(Real.log 4) = (n : ℝ) * 2 * Real.pi := by
    field_simp at hn
    exact_mod_cast hn
  have hpos := log_four_pos
  have hlt := log_four_lt_two_pi
  have hpi : 0 < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  -- `n·2π ∈ (−2π, 0)` forces `n ∈ (−1, 0)`, impossible
  have hn1 : (n : ℝ) * 2 * Real.pi < 0 := by linarith
  have hn2 : -(2 * Real.pi) < (n : ℝ) * 2 * Real.pi := by linarith
  have hnlt : (n : ℝ) < 0 := by nlinarith
  have hngt : (-1 : ℝ) < (n : ℝ) := by nlinarith
  have h1 : n < 0 := by exact_mod_cast hnlt
  have h2 : (-1 : ℤ) < n := by exact_mod_cast hngt
  omega

/-! ## The two members differ -/

/-- The off-diagonal coefficients of the Lüders member and the unit-twist member
differ at `λ = (1, 4)`. -/
theorem offCoeff_sep : offCoeff 1 4 0 ≠ offCoeff 1 4 1 := by
  intro h
  rw [offCoeff, offCoeff] at h
  have hsqrt : (Real.sqrt (1 * 4) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    rw [one_mul]
    positivity
  have hcancel := mul_left_cancel₀ hsqrt h
  rw [Real.log_one] at hcancel
  simp only [zero_mul, Complex.ofReal_zero, zero_sub, one_mul] at hcancel
  refine exp_neg_log_four_ne_one ?_
  rw [← hcancel, Complex.exp_zero]

/-- **Frame dependence is real at the level of the operation** (`thm:qubit-boundary`).
The Lüders member and the unit-twist member of the rank-two family are *different
maps*: they disagree on the coherence matrix at `λ = (1, 4)`.  Combined with
`sp_tau_had_is_luders` and `sp_tau_std_is_unit_twist` — which identify these two
as the values of the family on the Hadamard and reference frames — this is the
statement that the qubit escapes `mthm:master`'s rigidity, carried by the
operation rather than by the dial. -/
theorem sp_luders_ne_unit_twist : sp 1 4 0 Ecoh ≠ sp 1 4 1 Ecoh := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [sp_blockForm 1 4 0 (by norm_num) (by norm_num),
    sp_blockForm 1 4 1 (by norm_num) (by norm_num)] at h01
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one,
    Ecoh_01, mul_one, Matrix.of_apply] at h01
  exact offCoeff_sep h01

end RankTwo
