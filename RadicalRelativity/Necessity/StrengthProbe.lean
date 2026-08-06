/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.Strength

set_option linter.style.longLine false

/-!
# The probe family and the transition probability  (M3 bridge 2, part 2)

The order-definable strength, evaluated on the **probe**
`probe φ = ½(𝟙 + φφ*)`, returns the transition probability:

`Str(ψψ*, probe φ) = (2 − τ)⁻¹`,  `τ = |⟪φ,ψ⟫|²`.

Since `strength` is preserved by every linear order-isomorphism
(`strength_map`) and `τ ↦ (2−τ)⁻¹` is injective, a unital linear
order-automorphism preserves `τ` — the metric datum Wigner rigidity consumes.

This file proves the ingredients and the **forward** bound:

* `probe` and `probe_isEffect`.
* `rankOne_mulVec` — `(φφ*)ψ = ⟪φ,ψ⟫·φ`.
* `probe_mulVec_witness` — the collapse `probe φ · (2ψ − ⟪φ,ψ⟫·φ) = ψ`
  (i.e. the witness vector is `(probe φ)⁻¹ψ`, computed without any inverse).
* `tprob` and `tprob_le_one` — `τ ∈ [0,1]` by Cauchy–Schwarz.
* `strength_probe_le` — the forward bound `Str ≤ (2 − τ)⁻¹`, by feeding the
  witness vector to `rankOne_smul_le_iff`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The probe -/

/-- The **probe effect** `½(𝟙 + φφ*)`. -/
def probe (φ : n → ℂ) : HermitianMat n ℂ := (1 / 2 : ℝ) • (1 + rankOne φ)

/-- The transition probability `τ = |⟪φ,ψ⟫|²`. -/
def tprob (ψ φ : n → ℂ) : ℝ := Complex.normSq (star φ ⬝ᵥ ψ)

omit [DecidableEq n] in
theorem tprob_nonneg (ψ φ : n → ℂ) : 0 ≤ tprob ψ φ :=
  Complex.normSq_nonneg _

/-! ## The one `mulVec` identity -/

omit [DecidableEq n] in
/-- `(φφ*) ψ = ⟪φ,ψ⟫ · φ`. -/
theorem rankOne_mulVec (φ ψ : n → ℂ) :
    (rankOne φ).mat *ᵥ ψ = (star φ ⬝ᵥ ψ) • φ := by
  rw [rankOne_mat, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

/-! ## The witness vector -/

/-- **The witness collapse.** With `w := 2ψ − ⟪φ,ψ⟫·φ` (which is
`(probe φ)⁻¹ψ`), one has `probe φ · w = ψ` — proved by expanding, using
`(φφ*)φ = ⟪φ,φ⟫·φ = φ` for unit `φ`. -/
theorem probe_mulVec_witness {φ ψ : n → ℂ} (hφ : star φ ⬝ᵥ φ = 1) :
    (probe φ).mat *ᵥ ((2 : ℂ) • ψ - (star φ ⬝ᵥ ψ) • φ) = ψ := by
  set c := star φ ⬝ᵥ ψ with hc
  rw [probe, mat_smul, Matrix.smul_mulVec, mat_add, mat_one, Matrix.add_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_smul, Matrix.mulVec_smul, rankOne_mulVec, rankOne_mulVec, hφ]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, one_smul,
    RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

/-! ## `τ ≤ 1` by Cauchy–Schwarz -/

omit [DecidableEq n] in
/-- The probe's quadratic form at the witness equals `2 − τ` (both slots). -/
theorem dot_witness {φ ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ ((2 : ℂ) • ψ - (star φ ⬝ᵥ ψ) • φ)
      = ((2 - tprob ψ φ : ℝ) : ℂ) := by
  rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, hψ, mul_one]
  have hconj : star ψ ⬝ᵥ φ = star (star φ ⬝ᵥ ψ) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hconj, tprob]
  have hnn : ((Complex.normSq (star φ ⬝ᵥ ψ) : ℝ) : ℂ)
      = (star φ ⬝ᵥ ψ) * star (star φ ⬝ᵥ ψ) := by
    rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self]
  push_cast
  rw [hnn]

/-! ## `τ ≤ 1`: Cauchy–Schwarz through the probe's own positivity -/

/-- `τ ≤ 1` for unit vectors: `φφ* ≤ 𝟙` tested at `ψ`. -/
theorem tprob_le_one {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) : tprob ψ φ ≤ 1 := by
  have hle : rankOne φ ≤ 1 := (rankOne_isProjection hφ).le_one
  rw [le_iff_mulVec_le_mulVec] at hle
  have h := hle ψ
  rw [rankOne_quadratic, mat_one, Matrix.one_mulVec, hψ] at h
  have hconj : star ψ ⬝ᵥ φ = star (star φ ⬝ᵥ ψ) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hconj] at h
  have hnn : (star (star φ ⬝ᵥ ψ)) * (star φ ⬝ᵥ ψ)
      = ((tprob ψ φ : ℝ) : ℂ) := by
    rw [tprob, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [hnn] at h
  exact_mod_cast h

/-- Hence `1 ≤ 2 − τ`, so the strength formula never divides by zero. -/
theorem one_le_two_sub_tprob {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) : 1 ≤ 2 - tprob ψ φ := by
  have := tprob_le_one hψ hφ
  linarith

/-! ## The probe is an effect -/

theorem probe_nonneg (φ : n → ℂ) : 0 ≤ probe φ := by
  rw [probe]
  apply smul_nonneg (by norm_num)
  have h1 : (0 : HermitianMat n ℂ) ≤ 1 := zero_le_one
  have h2 : (0 : HermitianMat n ℂ) ≤ rankOne φ := by
    rw [zero_le_iff, rankOne_mat]
    have := Matrix.posSemidef_conjTranspose_mul_self
      (Matrix.replicateRow (Fin 1) (star φ))
    simpa [Matrix.vecMulVec_eq (Fin 1), Matrix.conjTranspose_replicateRow] using this
  exact _root_.add_nonneg h1 h2

theorem probe_le_one {φ : n → ℂ} (hφ : star φ ⬝ᵥ φ = 1) : probe φ ≤ 1 := by
  rw [probe]
  have hq : rankOne φ ≤ 1 := (rankOne_isProjection hφ).le_one
  have hsum : (1 : HermitianMat n ℂ) + rankOne φ ≤ 1 + 1 := by
    exact add_le_add_right hq 1 |>.trans_eq (by rw [add_comm]) |>.trans_eq rfl
  have hhalf : (1 / 2 : ℝ) • ((1 : HermitianMat n ℂ) + rankOne φ)
      ≤ (1 / 2 : ℝ) • ((1 : HermitianMat n ℂ) + 1) :=
    smul_le_smul_of_nonneg_left hsum (by norm_num)
  refine le_trans hhalf ?_
  have : (1 / 2 : ℝ) • ((1 : HermitianMat n ℂ) + 1) = 1 := by
    ext1
    rw [mat_smul, mat_add, mat_one]
    ext i j
    simp [Matrix.smul_apply, Matrix.add_apply, Complex.real_smul]
    ring
  rw [this]

/-! ## The forward bound -/

/-- **The forward bound**: `Str(ψψ*, probe φ) ≤ (2 − τ)⁻¹`, by feeding the
witness vector `w = (probe φ)⁻¹ψ` to the vectorwise criterion.  Both slots of
the criterion evaluate to `2 − τ` at `w`, so `t(2−τ)² ≤ (2−τ)`. -/
theorem strength_probe_le {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) :
    strength (rankOne ψ) (probe φ) ≤ (2 - tprob ψ φ)⁻¹ := by
  set τ := tprob ψ φ with hτ
  have hpos : (0 : ℝ) < 2 - τ :=
    lt_of_lt_of_le one_pos (one_le_two_sub_tprob hψ hφ)
  apply strength_le (probe_nonneg φ)
  intro t ht
  set w : n → ℂ := (2 : ℂ) • ψ - (star φ ⬝ᵥ ψ) • φ with hw
  have hcrit := (rankOne_smul_le_iff t ψ (probe φ)).mp ht w
  have hslot1 : star w ⬝ᵥ ψ = ((2 - τ : ℝ) : ℂ) := by
    have h := dot_witness (φ := φ) hψ
    rw [← hw] at h
    have hcomm : star w ⬝ᵥ ψ = star (star ψ ⬝ᵥ w) := by
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hcomm, h, Complex.star_def, Complex.conj_ofReal]
  have hslot2 : star w ⬝ᵥ (probe φ).mat *ᵥ w = ((2 - τ : ℝ) : ℂ) := by
    rw [probe_mulVec_witness (ψ := ψ) hφ, ← hw] at *
    exact hslot1
  have hslotψ : star w ⬝ᵥ ψ * (star ψ ⬝ᵥ w) = (((2 - τ) ^ 2 : ℝ) : ℂ) := by
    have h := dot_witness (φ := φ) hψ
    rw [← hw] at h
    rw [hslot1, h]
    push_cast
    ring
  rw [hslot2, hslotψ] at hcrit
  have hreal : t * (2 - τ) ^ 2 ≤ 2 - τ := by exact_mod_cast hcrit
  have h1 : t * (2 - τ) ≤ 1 := by nlinarith [hpos, hreal]
  have hinv : (0 : ℝ) < (2 - τ)⁻¹ := inv_pos.mpr hpos
  calc t = t * (2 - τ) * (2 - τ)⁻¹ := by field_simp
    _ ≤ 1 * (2 - τ)⁻¹ := mul_le_mul_of_nonneg_right h1 hinv.le
    _ = (2 - τ)⁻¹ := one_mul _

end HermitianMat
