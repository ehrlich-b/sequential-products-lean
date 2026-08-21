/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.TwistPower
import RadicalRelativity.Necessity.ProjectionOrder
import RadicalRelativity.MasterTheorem.Globalization

set_option linter.style.longLine false

/-!
# The twist parameter is unique  (ℂ-lane, the `∃!` half)

`PaperA.UniqueTwistConclusion` asks for a **unique** real `t`.  Sufficiency is
M1's `twistSequentialProduct`; necessity is the ℂ lane.  This file supplies the
uniqueness: two twist products that agree on all effects have the same parameter.

* `twistFactor_diagFamily_diagonal` — the twist factor of the diagonal family
  is the diagonal matrix `diag(√(e^{r_k})·e^{i t r_k})` (`twistFactor_diagFamily`
  with the two diagonal factors merged).
* `twistSeq_diagFamily_entry` — hence its action on any `b` reads off entrywise:
  `(a^{1/2+it} b a^{1/2−it})_{kl} = g_k · b_{kl} · conj g_l`.
* `pairProj` — the rank-one projection `½(e_i + e_j)(e_i + e_j)*`, an effect
  whose `(i,j)` entry is `½ ≠ 0`: the probe that *sees* the phase.
* `twist_param_unique` — **uniqueness**: agreement of `twistSeq t₁` and
  `twistSeq t₂` on effects forces `e^{i t₁ x} = e^{i t₂ x}` on an interval of
  `x = log λ`, so `Globalization.real_character_unique` (no `2π` ambiguity)
  gives `t₁ = t₂`.  Needs only `2 ≤ N`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The twist factor of the diagonal family, merged -/

/-- The twist factor of `diagFamily r` is diagonal with entries
`√(e^{r_k})·e^{i t r_k}`. -/
theorem twistFactor_diagFamily_diagonal (r : n → ℝ) (t : ℝ) :
    HermitianMat.twistFactor (diagFamily r) t
      = Matrix.diagonal (fun k => ((Real.sqrt (Real.exp (r k)) : ℝ) : ℂ)
          * Complex.exp (((t * r k : ℝ) : ℂ) * Complex.I)) := by
  rw [twistFactor_diagFamily, diagFamily, HermitianMat.cfc_diagonal,
    HermitianMat.diagonal_mat, torusU, Matrix.diagonal_mul_diagonal]
  rfl

/-- The twist product reads off entrywise on the diagonal family. -/
theorem twistSeq_diagFamily_entry (r : n → ℝ) (t : ℝ)
    (b : HermitianMat n ℂ) (k l : n) :
    (HermitianMat.twistSeq t (diagFamily r) b).mat k l
      = (((Real.sqrt (Real.exp (r k)) : ℝ) : ℂ)
            * Complex.exp (((t * r k : ℝ) : ℂ) * Complex.I))
        * b.mat k l
        * star (((Real.sqrt (Real.exp (r l)) : ℝ) : ℂ)
            * Complex.exp (((t * r l : ℝ) : ℂ) * Complex.I)) := by
  rw [HermitianMat.twistSeq, HermitianMat.conj_apply_mat,
    twistFactor_diagFamily_diagonal]
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  rw [Pi.star_apply]
  ring

/-! ## The probe effect -/

/-- The rank-one projection onto `(e_i + e_j)/√2`: an effect whose `(i,j)` entry
is `½`, so it detects the twist phase. -/
def pairProj (i j : n) : HermitianMat n ℂ :=
  (1 / 2 : ℝ) • HermitianMat.rankOne (Pi.single i (1 : ℂ) + Pi.single j (1 : ℂ))

theorem pairVec_normSq {i j : n} (hij : i ≠ j) :
    star (Pi.single i (1 : ℂ) + Pi.single j (1 : ℂ)) ⬝ᵥ
        (Pi.single i (1 : ℂ) + Pi.single j (1 : ℂ)) = (2 : ℂ) := by
  rw [star_add, ← Pi.single_star, ← Pi.single_star, star_one]
  rw [add_dotProduct, single_dotProduct, single_dotProduct]
  norm_num [Pi.single_apply, hij, Ne.symm hij]

theorem pairProj_isProjection {i j : n} (hij : i ≠ j) :
    (pairProj i j).IsProjection := by
  set ψ : n → ℂ := Pi.single i (1 : ℂ) + Pi.single j (1 : ℂ) with hψ
  have hs : star ψ ⬝ᵥ ψ = 2 := pairVec_normSq hij
  rw [HermitianMat.isProjection_iff_mat_mul_self, pairProj]
  rw [HermitianMat.mat_smul, HermitianMat.rankOne_mat]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mulVec, hs, op_smul_eq_smul, Matrix.smul_vecMulVec]
  ext a b
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem pairProj_isEffect {i j : n} (hij : i ≠ j) : IsEffect (pairProj i j) :=
  (pairProj_isProjection hij).isEffect

omit [Fintype n] in
theorem pairProj_entry {i j : n} (hij : i ≠ j) :
    (pairProj i j).mat i j = (1 / 2 : ℝ) := by
  rw [pairProj, HermitianMat.mat_smul, HermitianMat.rankOne_mat,
    Matrix.smul_apply, Matrix.vecMulVec_apply]
  rw [star_add, ← Pi.single_star, ← Pi.single_star, star_one]
  norm_num [Pi.single_apply, hij, Ne.symm hij, Complex.real_smul]

/-! ## Uniqueness of the twist parameter -/

/-- **The twist parameter is unique.**  If the twist products with parameters
`t₁` and `t₂` agree on every pair of effects of `H_N(ℂ)` (`N ≥ 2`), then
`t₁ = t₂`.  Probing at `a = diag(e^x, 1, …)` and the pair projection reduces
this to equality of the characters `x ↦ e^{i t x}` on an interval, which
`Globalization.real_character_unique` settles with no `2π` ambiguity. -/
theorem twist_param_unique {N : ℕ} (hN : 2 ≤ N) {t₁ t₂ : ℝ}
    (h : ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      HermitianMat.twistSeq t₁ a b = HermitianMat.twistSeq t₂ a b) :
    t₁ = t₂ := by
  have h0 : (0 : ℕ) < N := by omega
  have h1 : (1 : ℕ) < N := by omega
  set i : Fin N := ⟨0, h0⟩ with hi
  set j : Fin N := ⟨1, h1⟩ with hj
  have hij : i ≠ j := by
    rw [hi, hj]
    exact Fin.ne_of_val_ne (by norm_num)
  refine MasterTheorem.Globalization.real_character_unique
    (a := -1) (b := 0) (by norm_num) ?_
  intro x hx
  have hxneg : x < 0 := hx.2
  -- the probe base point `diag(e^x, 1, …)`
  set r : Fin N → ℝ := Pi.single i x with hr
  have hrle : ∀ k, r k ≤ 0 := by
    intro k
    rw [hr]
    by_cases hk : k = i
    · rw [hk, Pi.single_eq_same]; exact le_of_lt hxneg
    · rw [Pi.single_eq_of_ne hk]
  have hri : r i = x := by rw [hr, Pi.single_eq_same]
  have hrj : r j = 0 := by rw [hr, Pi.single_eq_of_ne (Ne.symm hij)]
  -- read the `(i,j)` entry of both products on the pair projection
  have hentry := congrArg (fun M : HermitianMat (Fin N) ℂ => M.mat i j)
    (h (diagFamily r) (pairProj i j) (diagFamily_isEffect hrle)
      (pairProj_isEffect hij))
  rw [twistSeq_diagFamily_entry, twistSeq_diagFamily_entry,
    pairProj_entry hij, hri, hrj] at hentry
  -- the `j`-side factors are `1`, the common positive factor cancels
  simp only [Real.exp_zero, Real.sqrt_one, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one, star_one, Complex.ofReal_one] at hentry
  have hpos : ((Real.sqrt (Real.exp x) : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    have h1 : Real.sqrt (Real.exp x) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (Real.exp_pos x)
    simp only [ne_eq, mul_eq_zero, Complex.ofReal_eq_zero]
    push_neg
    exact ⟨h1, by norm_num⟩
  have hcancel : Complex.exp (((t₁ * x : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t₂ * x : ℝ) : ℂ) * Complex.I) := by
    have hrw : ∀ s : ℝ,
        ((Real.sqrt (Real.exp x) : ℝ) : ℂ) * Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
            * ((1 / 2 : ℝ) : ℂ)
          = (((Real.sqrt (Real.exp x) : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ))
            * Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
      intro s; ring
    rw [hrw t₁, hrw t₂] at hentry
    exact mul_left_cancel₀ hpos hentry
  rw [show ((t₁ : ℂ) * (x : ℂ)) = (((t₁ * x : ℝ)) : ℂ) by push_cast; ring,
    show ((t₂ : ℂ) * (x : ℂ)) = (((t₂ * x : ℝ)) : ℂ) by push_cast; ring]
  exact hcancel

end Necessity
