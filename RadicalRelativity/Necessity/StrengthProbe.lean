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

/-! ## The backward bound: the sharp weighted Cauchy–Schwarz -/

/-- The scalar inequality at the heart of the backward bound, with the **sharp
weights `(2,1)`**: for `0 ≤ τ ≤ 1` and `x, y ≥ 0`,
`2(√τ x + √(1−τ) y)² ≤ (2−τ)(2x² + y²)`.  Plain unweighted Cauchy–Schwarz is
too lossy here (it would need `τ ≤ 0`); the weight `2` on the `x`-slot is what
makes this tight — the slack is exactly `(√τ·y − 2√(1−τ)·x)²`, so the
inequality holds for all real `x, y`. -/
theorem weighted_cs_sharp {τ x y : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    2 * (Real.sqrt τ * x + Real.sqrt (1 - τ) * y) ^ 2 ≤ (2 - τ) * (2 * x ^ 2 + y ^ 2) := by
  have hs : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ0
  have ht : Real.sqrt (1 - τ) ^ 2 = 1 - τ := Real.sq_sqrt (by linarith)
  -- expand: the difference is exactly `(√τ·y − 2√(1−τ)·x)²`
  nlinarith [_root_.sq_nonneg (Real.sqrt τ * y - 2 * Real.sqrt (1 - τ) * x), hs, ht]

/-! ## Real norm-squares and Cauchy–Schwarz on `n → ℂ` -/

omit [DecidableEq n] in
/-- The self inner product is the real norm-square. -/
theorem dot_self_eq (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]

/-- The real norm-square of a vector. -/
def nsq (v : n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

omit [DecidableEq n] in
theorem dot_self_eq_nsq (v : n → ℂ) : star v ⬝ᵥ v = ((nsq v : ℝ) : ℂ) :=
  dot_self_eq v

omit [DecidableEq n] in
theorem nsq_nonneg (v : n → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

omit [DecidableEq n] in
theorem nsq_smul (c : ℂ) (v : n → ℂ) :
    nsq (c • v) = Complex.normSq c * nsq v := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [Finset.mul_sum]

omit [Fintype n] [DecidableEq n] in
/-- `rankOne` is quadratically homogeneous. -/
theorem rankOne_smul (c : ℂ) (ψ : n → ℂ) :
    rankOne (c • ψ) = (Complex.normSq c) • rankOne ψ := by
  ext1
  rw [rankOne_mat, mat_smul, rankOne_mat]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, Pi.star_apply,
    smul_eq_mul, Complex.real_smul, star_mul']
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- `ψψ* ≤ ‖ψ‖²·𝟙`: the unit case plus quadratic homogeneity. -/
theorem rankOne_le_nsq_smul_one (ψ : n → ℂ) :
    rankOne ψ ≤ (nsq ψ) • (1 : HermitianMat n ℂ) := by
  by_cases hψ0 : nsq ψ = 0
  · have hz : ψ = 0 := by
      funext i
      have hall : ∀ k, Complex.normSq (ψ k) = 0 := by
        intro k
        clear i
        have hle : Complex.normSq (ψ k) ≤ nsq ψ :=
          Finset.single_le_sum (f := fun j => Complex.normSq (ψ j))
            (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ k)
        have := Complex.normSq_nonneg (ψ k)
        linarith [hψ0 ▸ hle]
      exact Complex.normSq_eq_zero.mp (hall i)
    have hr0 : rankOne (0 : n → ℂ) = 0 := by
      ext1
      rw [rankOne_mat]
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [hψ0, show (0:ℝ) • (1 : HermitianMat n ℂ) = 0 from zero_smul ℝ _, hz, hr0]
  · have hpos : 0 < nsq ψ := lt_of_le_of_ne (nsq_nonneg ψ) (Ne.symm hψ0)
    set r : ℝ := (Real.sqrt (nsq ψ))⁻¹ with hr
    have hrpos : 0 < r := by rw [hr]; positivity
    set u : n → ℂ := (r : ℂ) • ψ with hu
    have hunit : star u ⬝ᵥ u = 1 := by
      rw [hu, dot_self_eq_nsq, nsq_smul]
      have hnn : Complex.normSq (r : ℂ) = r ^ 2 := by
        rw [Complex.normSq_apply]
        simp only [Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hnn, hr]
      have : (Real.sqrt (nsq ψ))⁻¹ ^ 2 * nsq ψ = 1 := by
        rw [inv_pow, Real.sq_sqrt hpos.le]
        field_simp
      rw [this]
      norm_num
    have hle1 : rankOne u ≤ 1 := (rankOne_isProjection hunit).le_one
    have hexp : rankOne ψ = (nsq ψ) • rankOne u := by
      rw [hu, rankOne_smul]
      have hnn : Complex.normSq (r : ℂ) = r ^ 2 := by
        rw [Complex.normSq_apply]
        simp only [Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hnn, hr, smul_smul, inv_pow, Real.sq_sqrt hpos.le]
      rw [show nsq ψ * (nsq ψ)⁻¹ = 1 from mul_inv_cancel₀ hψ0, one_smul]
    rw [hexp]
    exact smul_le_smul_of_nonneg_left hle1 (nsq_nonneg ψ)

/-- **Cauchy–Schwarz** on `n → ℂ`, via `ψψ* ≤ ‖ψ‖²·𝟙` tested at the second
vector — no inner-product-space bridging needed. -/
theorem cs_dot (a b : n → ℂ) :
    Complex.normSq (star a ⬝ᵥ b) ≤ nsq a * nsq b := by
  have h := rankOne_le_nsq_smul_one a
  rw [le_iff_mulVec_le_mulVec] at h
  have hb := h b
  rw [rankOne_quadratic, mat_smul, Matrix.smul_mulVec, dotProduct_smul,
    RCLike.real_smul_eq_coe_mul, mat_one, Matrix.one_mulVec,
    dot_self_eq_nsq] at hb
  have hconj : star b ⬝ᵥ a = star (star a ⬝ᵥ b) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hconj] at hb
  have hnn : (star (star a ⬝ᵥ b)) * (star a ⬝ᵥ b)
      = ((Complex.normSq (star a ⬝ᵥ b) : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [hnn] at hb
  have hcast : ((Complex.normSq (star a ⬝ᵥ b) : ℝ) : ℂ)
      ≤ ((nsq a * nsq b : ℝ) : ℂ) := by
    push_cast
    exact hb
  exact Complex.real_le_real.mp hcast

/-! ## The backward bound and the strength formula -/

/-- The probe's quadratic form: `⟪v, probe φ · v⟫ = ½(‖v‖² + |⟪φ,v⟫|²)`. -/
theorem probe_quadratic (φ v : n → ℂ) :
    star v ⬝ᵥ (probe φ).mat *ᵥ v
      = ((1 / 2 * (nsq v + Complex.normSq (star φ ⬝ᵥ v)) : ℝ) : ℂ) := by
  rw [probe, mat_smul, Matrix.smul_mulVec, dotProduct_smul,
    RCLike.real_smul_eq_coe_mul, mat_add, mat_one, Matrix.add_mulVec,
    Matrix.one_mulVec, dotProduct_add, dot_self_eq_nsq, rankOne_quadratic]
  have hconj : star v ⬝ᵥ φ = star (star φ ⬝ᵥ v) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hconj]
  have hnn : (star (star φ ⬝ᵥ v)) * (star φ ⬝ᵥ v)
      = ((Complex.normSq (star φ ⬝ᵥ v) : ℝ) : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  rw [hnn]
  push_cast
  ring

/-- **The backward bound**: `(2−τ)⁻¹ · ψψ* ≤ probe φ`.  Decompose
`ψ = ⟪φ,ψ⟫φ + χ` and `v = ⟪φ,v⟫φ + w`; Cauchy–Schwarz on the `χ`-`w` pairing
then feeds `weighted_cs_sharp`, whose `(2,1)` weights match the probe's
quadratic form exactly. -/
theorem probe_ge_inv_smul_rankOne {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) :
    (2 - tprob ψ φ)⁻¹ • rankOne ψ ≤ probe φ := by
  set τ := tprob ψ φ with hτ
  have hτ0 : 0 ≤ τ := tprob_nonneg ψ φ
  have hτ1 : τ ≤ 1 := tprob_le_one hψ hφ
  have hpos : (0 : ℝ) < 2 - τ := by linarith
  rw [rankOne_smul_le_iff]
  intro v
  set c := star φ ⬝ᵥ ψ with hc
  set α := star φ ⬝ᵥ v with hα
  set χ : n → ℂ := ψ - c • φ with hχ
  set w : n → ℂ := v - α • φ with hw
  -- `χ ⊥ φ` and `w ⊥ φ`
  have hχφ : star χ ⬝ᵥ φ = 0 := by
    have hcj : star ψ ⬝ᵥ φ = star c := by
      rw [hc]
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hχ, star_sub, show star (c • φ) = star c • star φ from star_smul c φ,
      sub_dotProduct, smul_dotProduct, hφ, hcj, smul_eq_mul, mul_one, sub_self]
  -- norm-squares of the components
  have hnsqχ : nsq χ = 1 - τ := by
    have h1 : star χ ⬝ᵥ χ = ((1 - τ : ℝ) : ℂ) := by
      have hcj : star ψ ⬝ᵥ φ = star c := by
        rw [hc]
        simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hnn : star c * c = ((τ : ℝ) : ℂ) := by
        rw [hτ, tprob, ← hc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      rw [hχ, star_sub, show star (c • φ) = star c • star φ from star_smul c φ]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      rw [hψ, hφ, hcj, ← hc, mul_one]
      push_cast
      rw [hnn]
      ring
    rw [dot_self_eq_nsq] at h1
    exact_mod_cast h1
  have hnsqw : nsq w = nsq v - Complex.normSq α := by
    have h1 : star w ⬝ᵥ w
        = ((nsq v - Complex.normSq α : ℝ) : ℂ) := by
      have hcj : star v ⬝ᵥ φ = star α := by
        rw [hα]
        simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hnn : star α * α = ((Complex.normSq α : ℝ) : ℂ) := by
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      rw [hw, star_sub, show star (α • φ) = star α • star φ from star_smul α φ]
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      rw [dot_self_eq_nsq, hφ, hcj, ← hα, mul_one]
      push_cast
      rw [hnn]
      ring
    rw [dot_self_eq_nsq] at h1
    exact_mod_cast h1
  -- the pairing decomposition `⟪ψ,v⟫ = c̄α + ⟪χ,w⟫`
  have hsplit : star ψ ⬝ᵥ v = star c * α + star χ ⬝ᵥ w := by
    have hψeq : ψ = c • φ + χ := by rw [hχ]; abel
    have hveq : v = α • φ + w := by rw [hw]; abel
    have hφw : star φ ⬝ᵥ w = 0 := by
      rw [hw, dotProduct_sub, dotProduct_smul, hφ, smul_eq_mul, mul_one, ← hα,
        sub_self]
    conv_lhs => rw [hψeq, hveq]
    rw [star_add, show star (c • φ) = star c • star φ from star_smul c φ]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    rw [hφ, hχφ, hφw]
    ring
  -- the scalar estimate
  have hcnorm : Complex.normSq c = τ := by rw [hτ, tprob, hc]
  have hbound : Complex.normSq (star ψ ⬝ᵥ v)
      ≤ (Real.sqrt τ * Real.sqrt (Complex.normSq α)
          + Real.sqrt (1 - τ) * Real.sqrt (nsq w)) ^ 2 := by
    have hcs := cs_dot χ w
    rw [hnsqχ] at hcs
    have habs : ‖star ψ ⬝ᵥ v‖
        ≤ Real.sqrt τ * Real.sqrt (Complex.normSq α)
          + Real.sqrt (1 - τ) * Real.sqrt (nsq w) := by
      rw [hsplit]
      refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_mul]
        have h1 : ‖star c‖ = Real.sqrt τ := by
          rw [show ‖star c‖ = ‖c‖ from by rw [Complex.star_def, RCLike.norm_conj]]
          rw [← Real.sqrt_sq (norm_nonneg c), ← Complex.normSq_eq_norm_sq, hcnorm]
        have h2 : ‖α‖ = Real.sqrt (Complex.normSq α) := by
          rw [← Real.sqrt_sq (norm_nonneg α), ← Complex.normSq_eq_norm_sq]
        rw [h1, h2]
      · have h3 : ‖star χ ⬝ᵥ w‖ ≤ Real.sqrt (1 - τ) * Real.sqrt (nsq w) := by
          rw [← Real.sqrt_mul (by linarith)]
          rw [show ‖star χ ⬝ᵥ w‖
              = Real.sqrt (Complex.normSq (star χ ⬝ᵥ w)) from by
            rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq]]
          exact Real.sqrt_le_sqrt hcs
        exact h3
    have hsq : Complex.normSq (star ψ ⬝ᵥ v) = ‖star ψ ⬝ᵥ v‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [hsq]
    exact pow_le_pow_left₀ (norm_nonneg _) habs 2
  -- assemble through the sharp weighted Cauchy–Schwarz
  have hsharp := weighted_cs_sharp (τ := τ) (x := Real.sqrt (Complex.normSq α))
    (y := Real.sqrt (nsq w)) hτ0 hτ1
  rw [Real.sq_sqrt (Complex.normSq_nonneg α), Real.sq_sqrt (nsq_nonneg w)] at hsharp
  have hchain : 2 * Complex.normSq (star ψ ⬝ᵥ v)
      ≤ (2 - τ) * (nsq v + Complex.normSq α) := by
    have hstep : 2 * Complex.normSq (star ψ ⬝ᵥ v)
        ≤ 2 * (Real.sqrt τ * Real.sqrt (Complex.normSq α)
            + Real.sqrt (1 - τ) * Real.sqrt (nsq w)) ^ 2 := by linarith
    have hrhs : (2 - τ) * (2 * Complex.normSq α + nsq w)
        = (2 - τ) * (nsq v + Complex.normSq α) := by rw [hnsqw]; ring
    linarith [hstep, hsharp, hrhs]
  have hreal : (2 - τ)⁻¹ * Complex.normSq (star ψ ⬝ᵥ v)
      ≤ 1 / 2 * (nsq v + Complex.normSq α) := by
    rw [inv_mul_le_iff₀ hpos]
    nlinarith [hchain, hpos]
  -- transport to the ℂ-level goal
  rw [probe_quadratic]
  have hlhs : ((2 - τ : ℝ) : ℂ)⁻¹ * ((star v ⬝ᵥ ψ) * (star ψ ⬝ᵥ v))
      = (((2 - τ)⁻¹ * Complex.normSq (star ψ ⬝ᵥ v) : ℝ) : ℂ) := by
    have hcj : star v ⬝ᵥ ψ = star (star ψ ⬝ᵥ v) := by
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hcj, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  have hgoal : (((2 - τ)⁻¹ * Complex.normSq (star ψ ⬝ᵥ v) : ℝ) : ℂ)
      ≤ ((1 / 2 * (nsq v + Complex.normSq (star φ ⬝ᵥ v)) : ℝ) : ℂ) :=
    Complex.real_le_real.mpr (by rw [← hα]; exact hreal)
  refine le_trans (le_of_eq ?_) hgoal
  rw [← hlhs]
  push_cast
  ring

/-! ## The strength formula and `τ` as order data -/

/-- **The strength formula** (`Str(ψψ*, probe φ) = (2 − τ)⁻¹`): the forward
bound from the witness vector and the backward bound from the sharp weighted
Cauchy–Schwarz meet. -/
theorem strength_probe_eq {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) :
    strength (rankOne ψ) (probe φ) = (2 - tprob ψ φ)⁻¹ :=
  le_antisymm (strength_probe_le hψ hφ)
    (le_strength hψ (probe_le_one hφ) (probe_ge_inv_smul_rankOne hψ hφ))

/-- **`τ` is recovered from the strength**: `τ = 2 − Str⁻¹`.  Combined with
`strength_map`, this is the statement that the transition probability is
**order data**. -/
theorem tprob_eq_of_strength {ψ φ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hφ : star φ ⬝ᵥ φ = 1) :
    tprob ψ φ = 2 - (strength (rankOne ψ) (probe φ))⁻¹ := by
  rw [strength_probe_eq hψ hφ, inv_inv]
  ring

/-- **The payoff (M3 bridge 2, complete).**  A unital ℝ-linear order-automorphism
that carries the rank-one projection of `ψ` to that of `ψ'` and of `φ` to that of
`φ'` preserves the transition probability: `τ(ψ,φ) = τ(ψ',φ')`.

The proof is pure transport: `strength` is order data (`strength_map`), the probe
is built from the unit and a rank-one projection (both carried along by the
hypotheses), and `tprob_eq_of_strength` inverts the strength.  This is exactly
the `TransProbPreserving` input of `Projectivization.wigner_rigidity`. -/
theorem tprob_preserved (Φ : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    (hΦ : ∀ x y : HermitianMat n ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1)
    {ψ φ ψ' φ' : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (hφ : star φ ⬝ᵥ φ = 1)
    (hψ' : star ψ' ⬝ᵥ ψ' = 1) (hφ' : star φ' ⬝ᵥ φ' = 1)
    (hmapψ : Φ (rankOne ψ) = rankOne ψ') (hmapφ : Φ (rankOne φ) = rankOne φ') :
    tprob ψ φ = tprob ψ' φ' := by
  have hprobe : Φ (probe φ) = probe φ' := by
    rw [probe, map_smul, map_add, hunital, hmapφ, probe]
  rw [tprob_eq_of_strength hψ hφ, tprob_eq_of_strength hψ' hφ']
  rw [← hmapψ, ← hprobe, strength_map Φ hΦ]

end HermitianMat
