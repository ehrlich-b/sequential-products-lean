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

end Necessity
