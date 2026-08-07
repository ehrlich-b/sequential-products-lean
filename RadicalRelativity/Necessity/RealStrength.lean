/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealJordanWitness

set_option linter.style.longLine false

/-!
# The Busch-Gudder strength at ℝ  (the ℝ bridge to real Kadison, part 4a)

The bridge's remaining step is to feed real Wigner with a
**transition-probability preserving** ray map.  That needs the transition probability to be
*order data*, and the device for that is the strength:

  `Str(p, a) = sup {t | t·p ≤ a}`

Nothing here mentions the scalar field except as a type parameter — the strength is defined
from the order and the real scalar action alone, which is precisely why it transports along
any order isomorphism (`strengthR_map`).  That transport is what will carry the transition
probability from `Φ`'s source to its image.

* `vecMulVec_mulVec` — `(ψψᵀ)v = (ψ ⬝ᵥ v)ψ`, the computation every quadratic form below runs on.
* `quadForm_smul_rankOneR` — the quadratic form of `t·ψψᵀ` at a unit `ψ` is `t`.  This is what
  bounds the defining set: `t·ψψᵀ ≤ a ≤ 𝟙` forces `t ≤ 1`.
* `strengthR_map` — **order isomorphisms preserve the strength.**
-/

noncomputable section

open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The rank-one matrix acting on a vector -/

omit [DecidableEq n] in
/-- `(ψψᵀ)v = (ψ ⬝ᵥ v)ψ`. -/
theorem vecMulVec_mulVec (ψ v : n → ℝ) :
    Matrix.vecMulVec ψ ψ *ᵥ v = (ψ ⬝ᵥ v) • ψ := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq n] in
/-- **The quadratic form of `t·ψψᵀ` at a unit vector is `t`.** -/
theorem quadForm_smul_rankOneR {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) (t : ℝ) :
    ψ ⬝ᵥ ((t • rankOneR ψ).mat *ᵥ ψ) = t := by
  rw [HermitianMat.mat_smul, rankOneR_mat, Matrix.smul_mulVec, vecMulVec_mulVec, hψ,
    one_smul, dotProduct_smul, smul_eq_mul, hψ, mul_one]

/-! ## The strength -/

/-- The **Busch-Gudder strength** of `p` in `a`: `Str(p, a) = sup {t | t·p ≤ a}`.  Defined
from the order and the real scalar action only, which is the whole point. -/
def strengthR (p a : HermitianMat n ℝ) : ℝ :=
  sSup {t : ℝ | t • p ≤ a}

omit [Fintype n] [DecidableEq n] in
/-- The defining set contains `0` whenever `a` is positive, so it is nonempty. -/
theorem strengthR_set_nonempty {p a : HermitianMat n ℝ} (ha : 0 ≤ a) :
    {t : ℝ | t • p ≤ a}.Nonempty := by
  refine ⟨0, ?_⟩
  show (0 : ℝ) • p ≤ a
  rw [zero_smul]
  exact ha

/-- The defining set is bounded above: `t·ψψᵀ ≤ a ≤ 𝟙` forces `t ≤ 1`, by testing the
quadratic form at `ψ` itself. -/
theorem strengthR_set_bddAbove {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1)
    {a : HermitianMat n ℝ} (ha : a ≤ 1) :
    BddAbove {t : ℝ | t • rankOneR ψ ≤ a} := by
  refine ⟨1, fun t ht => ?_⟩
  have hta : (t • rankOneR ψ) ≤ 1 := le_trans ht ha
  have h := (HermitianMat.le_iff_mulVec_le_mulVec _ _).mp hta ψ
  rw [star_trivial, quadForm_smul_rankOneR hψ, HermitianMat.mat_one, Matrix.one_mulVec,
    hψ] at h
  exact h

omit [DecidableEq n] in
/-- **Order-isomorphism invariance of the strength.**  Any ℝ-linear order isomorphism
transports the defining set exactly, so the strength is order data — and therefore so is
anything recovered from it. -/
theorem strengthR_map (Φ : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ)
    (hΦ : ∀ x y : HermitianMat n ℝ, x ≤ y ↔ Φ x ≤ Φ y)
    (p a : HermitianMat n ℝ) :
    strengthR (Φ p) (Φ a) = strengthR p a := by
  unfold strengthR
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  rw [← map_smul]
  exact (hΦ _ _).symm


/-! ## The probe, and the inequality at its heart

The transition probability is recovered from the strength via the **probe**
`Pr(φ) = ½(𝟙 + φφᵀ)`, for which `Str(ψψᵀ, Pr(φ)) = (2 − τ)⁻¹` with `τ = (ψ ⬝ᵥ φ)²`.  The `≥`
half of that is a tight inequality, and `probe_key_ineqR` below is its entire content,
isolated as pure arithmetic — the same tactic that worked for `sign_pair_of_abs`.

Decompose `v = αφ + w` and `ψ = sφ + χ` with `w, χ ⊥ φ`, `s = ψ ⬝ᵥ φ`, `d = χ ⬝ᵥ w`.  Then
`ψ ⬝ᵥ v = sα + d`, `v ⬝ᵥ v = α² + W` with `W = w ⬝ᵥ w`, and Cauchy-Schwarz gives
`d² ≤ (1 − τ)W`.  The required bound is then exactly two-term Cauchy-Schwarz with weights
`1` and `½`, and it is TIGHT — which is why the strength equals `(2 − τ)⁻¹` on the nose
rather than merely being bounded by it.

The certificate, found by hand and worth recording because `nlinarith` will not find it
unaided: after clearing `4(1−τ)`, the gap is exactly `2(2(1−τ)α − sd)²`, using `s² = τ` to
turn `2τd²` into `2s²d²`.
-/

/-- **The tight inequality behind the probe's strength.**  Pure arithmetic in the five
scalars the geometric decomposition produces. -/
theorem probe_key_ineqR {τ s α d W : ℝ} (hτ1 : τ ≤ 1) (hs : s ^ 2 = τ)
    (hW : 0 ≤ W) (hd : d ^ 2 ≤ (1 - τ) * W) :
    (s * α + d) ^ 2 ≤ (2 - τ) * (α ^ 2 + W / 2) := by
  -- `0 ≤ τ` is not a hypothesis: `s² = τ` already forces it
  have hτ0 : 0 ≤ τ := hs ▸ sq_nonneg s
  rcases eq_or_lt_of_le hτ1 with hτ | hτ
  · -- `τ = 1` forces `χ = 0`, i.e. `d = 0`
    have hd0 : d = 0 := by
      have : d ^ 2 ≤ 0 := by rw [← hτ] at hd; simpa using hd
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg d))
    rw [hd0, add_zero]
    have hs1 : s ^ 2 = 1 := by rw [hs, hτ]
    nlinarith [hs1, hW, hτ]
  · -- the generic case: clear `4(1 − τ)` and the gap is a square
    have h1 : 0 < 1 - τ := by linarith
    nlinarith [sq_nonneg (2 * (1 - τ) * α - s * d), hd, hs, hW, h1,
      mul_nonneg hτ0 (sub_nonneg.mpr hd), sq_nonneg (s * α + d), sq_nonneg d]

/-- The **probe** effect `Pr(φ) = ½(𝟙 + φφᵀ)`. -/
def probeR (φ : n → ℝ) : HermitianMat n ℝ := (1 / 2 : ℝ) • (1 + rankOneR φ)

/-! ## Quadratic forms, and Cauchy-Schwarz for the dot product -/

omit [DecidableEq n] in
/-- The quadratic form of `t·ψψᵀ` at an arbitrary vector. -/
theorem quadForm_smul_rankOneR_apply (t : ℝ) (ψ v : n → ℝ) :
    v ⬝ᵥ ((t • rankOneR ψ).mat *ᵥ v) = t * (ψ ⬝ᵥ v) ^ 2 := by
  rw [HermitianMat.mat_smul, rankOneR_mat, Matrix.smul_mulVec, vecMulVec_mulVec,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, dotProduct_comm v ψ]
  ring

omit [DecidableEq n] in
/-- `t·ψψᵀ ≤ a` is exactly a statement about quadratic forms. -/
theorem rankOneR_smul_le_iff (t : ℝ) (ψ : n → ℝ) (a : HermitianMat n ℝ) :
    t • rankOneR ψ ≤ a ↔ ∀ v : n → ℝ, t * (ψ ⬝ᵥ v) ^ 2 ≤ v ⬝ᵥ (a.mat *ᵥ v) := by
  rw [HermitianMat.le_iff_mulVec_le_mulVec]
  constructor
  · intro h v
    have hv := h v
    rw [star_trivial, quadForm_smul_rankOneR_apply] at hv
    exact hv
  · intro h v
    rw [star_trivial, quadForm_smul_rankOneR_apply]
    exact h v

/-- The quadratic form of the probe. -/
theorem quadForm_probeR (φ v : n → ℝ) :
    v ⬝ᵥ ((probeR φ).mat *ᵥ v) = (1 / 2 : ℝ) * (v ⬝ᵥ v + (φ ⬝ᵥ v) ^ 2) := by
  rw [probeR, HermitianMat.mat_smul, HermitianMat.mat_add, HermitianMat.mat_one, rankOneR_mat,
    Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
    dotProduct_smul, smul_eq_mul, dotProduct_add, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v φ]
  ring

omit [DecidableEq n] in
/-- **Cauchy-Schwarz for the real dot product**, division-free: expanding
`(‖y‖²x − ⟨x,y⟩y)·(same) = ‖y‖²(‖y‖²‖x‖² − ⟨x,y⟩²)` and dividing by `‖y‖² > 0`.  Proving it
here avoids transporting `n → ℝ` to `EuclideanSpace` just to quote the abstract version. -/
theorem dotProduct_sq_le (x y : n → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  by_cases hy : y ⬝ᵥ y = 0
  · simp [dotProduct_self_eq_zero.mp hy]
  · have hc : 0 < y ⬝ᵥ y := lt_of_le_of_ne (dotProduct_self_nonnegR y) (Ne.symm hy)
    have h := dotProduct_self_nonnegR ((y ⬝ᵥ y) • x - (x ⬝ᵥ y) • y)
    have hexp : ((y ⬝ᵥ y) • x - (x ⬝ᵥ y) • y) ⬝ᵥ ((y ⬝ᵥ y) • x - (x ⬝ᵥ y) • y)
        = (y ⬝ᵥ y) * ((y ⬝ᵥ y) * (x ⬝ᵥ x) - (x ⬝ᵥ y) ^ 2) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm y x]
      ring
    rw [hexp] at h
    nlinarith [h, hc]

/-! ## The probe dominates the scaled rank-one

The `≥` half of the strength computation, assembled: decompose `v` and `ψ` along `φ`, read off
the five scalars, and apply `probe_key_ineqR`.
-/

/-- **`(2 − τ)⁻¹·ψψᵀ ≤ Pr(φ)`** with `τ = (ψ ⬝ᵥ φ)²`.  This is the admissibility half of
`Str(ψψᵀ, Pr(φ)) = (2 − τ)⁻¹`. -/
theorem probe_ge_inv_smul_rankOneR {ψ φ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) (hφ : φ ⬝ᵥ φ = 1) :
    (2 - (ψ ⬝ᵥ φ) ^ 2)⁻¹ • rankOneR ψ ≤ probeR φ := by
  have hτ1 : (ψ ⬝ᵥ φ) ^ 2 ≤ 1 := by
    have := dotProduct_sq_le ψ φ
    rwa [hψ, hφ, mul_one] at this
  have hpos : (0 : ℝ) < 2 - (ψ ⬝ᵥ φ) ^ 2 := by linarith
  rw [rankOneR_smul_le_iff]
  intro v
  have hsymφψ : φ ⬝ᵥ ψ = ψ ⬝ᵥ φ := dotProduct_comm φ ψ
  have hsymφv : v ⬝ᵥ φ = φ ⬝ᵥ v := dotProduct_comm v φ
  -- the orthogonal parts.  NOTE: every expansion below rewrites `w` or `χ` — never `v` or
  -- `ψ` — because those appear inside the coefficients, and rewriting them there is the
  -- self-reference trap that has cost this campaign four rounds.
  obtain ⟨w, hw⟩ : ∃ w : n → ℝ, w = v - (φ ⬝ᵥ v) • φ := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : n → ℝ, χ = ψ - (ψ ⬝ᵥ φ) • φ := ⟨_, rfl⟩
  have hww : w ⬝ᵥ w = v ⬝ᵥ v - (φ ⬝ᵥ v) ^ 2 := by
    rw [hw]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hφ, hsymφv]
    ring
  have hχχ : χ ⬝ᵥ χ = 1 - (ψ ⬝ᵥ φ) ^ 2 := by
    rw [hχ]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hψ, hφ, hsymφψ]
    ring
  have hχw : χ ⬝ᵥ w = ψ ⬝ᵥ v - (ψ ⬝ᵥ φ) * (φ ⬝ᵥ v) := by
    rw [hχ, hw]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hφ, hsymφψ, hsymφv]
    ring
  have hW : (0 : ℝ) ≤ w ⬝ᵥ w := dotProduct_self_nonnegR w
  have hd : (χ ⬝ᵥ w) ^ 2 ≤ (1 - (ψ ⬝ᵥ φ) ^ 2) * (w ⬝ᵥ w) := by
    have := dotProduct_sq_le χ w
    rwa [hχχ] at this
  -- the arithmetic core
  have key := probe_key_ineqR (τ := (ψ ⬝ᵥ φ) ^ 2) (s := ψ ⬝ᵥ φ) (α := φ ⬝ᵥ v)
    (d := χ ⬝ᵥ w) (W := w ⬝ᵥ w) hτ1 rfl hW hd
  rw [show (ψ ⬝ᵥ φ) * (φ ⬝ᵥ v) + χ ⬝ᵥ w = ψ ⬝ᵥ v by rw [hχw]; ring, hww] at key
  have h2 := mul_le_mul_of_nonneg_left key (le_of_lt (inv_pos.mpr hpos))
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h2
  rw [quadForm_probeR]
  linarith [h2]

end Necessity
