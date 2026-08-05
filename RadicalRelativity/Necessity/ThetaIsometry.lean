/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ChiExtension

set_option linter.style.longLine false

/-!
# Θ is an order-unit-norm isometry  (campaign LEDGER 2.6, u1)

A unital order isomorphism preserves the defining set of the order-unit norm
verbatim: `−t•1 ≤ x ≤ t•1 ⟺ −t•1 ≤ Θx ≤ t•1` (both bounds transported through
`theta_le_iff` and unitality), so `ouNorm (Θ x) = ouNorm x` — with no trace
preservation and no compactness anywhere. This is the engine of the skewness
step (u2): the one-parameter family `exp(t·dχ)` acts by ouNorm-isometries, and
on a single off-diagonal block the order-unit norm is the Euclidean norm.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- Order preservation for the totalized Θ (both directions). -/
theorem thetaNorm_le_iff (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) (x y : HermitianMat n ℂ) :
    x ≤ y ↔ thetaNorm P hS2 a x ≤ thetaNorm P hS2 a y := by
  rw [← sub_nonneg, ← sub_nonneg (b := thetaNorm P hS2 a x), ← map_sub]
  exact thetaNorm_nonneg_iff P hS2 h (y - x)

/-- Θ transports the unit interval bounds: `x ≤ t•1 ⟺ Θx ≤ t•1`. -/
theorem thetaNorm_le_smul_one_iff (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) (x : HermitianMat n ℂ) (t : ℝ) :
    x ≤ t • 1 ↔ thetaNorm P hS2 a x ≤ t • 1 := by
  rw [thetaNorm_le_iff P hS2 h x (t • 1), map_smul, thetaNorm_one P hS2 h]

theorem thetaNorm_neg_smul_one_le_iff (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) (x : HermitianMat n ℂ) (t : ℝ) :
    -(t • 1) ≤ x ↔ -(t • 1) ≤ thetaNorm P hS2 a x := by
  rw [thetaNorm_le_iff P hS2 h (-(t • 1)) x, map_neg, map_smul, thetaNorm_one P hS2 h]

/-- **Θ is an order-unit-norm isometry** (u1): the defining sets of the two
order-unit norms coincide, so the infima do. -/
theorem ouNorm_thetaNorm (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) (x : HermitianMat n ℂ) :
    HermitianMat.ouNorm (thetaNorm P hS2 a x) = HermitianMat.ouNorm x := by
  unfold HermitianMat.ouNorm
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨ht, h1, h2⟩
    exact ⟨ht, (thetaNorm_neg_smul_one_le_iff P hS2 h x t).mpr h1,
      (thetaNorm_le_smul_one_iff P hS2 h x t).mpr h2⟩
  · rintro ⟨ht, h1, h2⟩
    exact ⟨ht, (thetaNorm_neg_smul_one_le_iff P hS2 h x t).mp h1,
      (thetaNorm_le_smul_one_iff P hS2 h x t).mp h2⟩

/-- The units-valued character is an ouNorm-isometry at every parameter. -/
theorem ouNorm_thetaUnit (hS2 : P.FirstArgContinuous) (r : n → ℝ)
    (x : HermitianMat n ℂ) :
    HermitianMat.ouNorm ((thetaUnit P hS2 r).val x) = HermitianMat.ouNorm x := by
  rw [thetaUnit_val_apply]
  exact ouNorm_thetaNorm P hS2 (diagFamily_posDef r) x

/-- The inverse factor is an ouNorm-isometry too (apply the forward isometry at
the image point). -/
theorem ouNorm_thetaUnit_inv (hS2 : P.FirstArgContinuous) (r : n → ℝ)
    (x : HermitianMat n ℂ) :
    HermitianMat.ouNorm (((thetaUnit P hS2 r)⁻¹).val x) = HermitianMat.ouNorm x := by
  have h := ouNorm_thetaUnit P hS2 r (((thetaUnit P hS2 r)⁻¹).val x)
  have hcancel : (thetaUnit P hS2 r).val (((thetaUnit P hS2 r)⁻¹).val x) = x := by
    rw [← ContinuousLinearMap.mul_apply, Units.mul_inv]
    rfl
  rw [hcancel] at h
  exact h.symm

/-- **χ̃ is an ouNorm-isometry** at every parameter — the isometry input for the
skewness of `dχ` (u2). -/
theorem ouNorm_chiTilde (hS2 : P.FirstArgContinuous) (r : n → ℝ)
    (x : HermitianMat n ℂ) :
    HermitianMat.ouNorm ((chiTilde P hS2 r).val x) = HermitianMat.ouNorm x := by
  show HermitianMat.ouNorm
    (((thetaUnit P hS2 (r ⊓ 0)) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val x)
    = HermitianMat.ouNorm x
  rw [Units.val_mul, ContinuousLinearMap.mul_apply, ouNorm_thetaUnit,
    ouNorm_thetaUnit_inv]

end Necessity
