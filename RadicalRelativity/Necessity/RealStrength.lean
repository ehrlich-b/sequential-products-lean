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

end Necessity
