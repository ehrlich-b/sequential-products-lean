/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealProjectionOrder
import RadicalRelativity.Vendor.Wigner.RealWigner

set_option linter.style.longLine false

/-!
# The bridge to real Wigner rigidity  (the ℝ bridge to real Kadison, part 5e)

Real Wigner (`Vendor/Wigner/RealWigner.lean`) speaks about `EuclideanSpace ℝ (Fin N)` and its
inner product; the Kadison side speaks about `Fin N → ℝ` and `dotProduct`.  This file identifies
the two, so that `tprobR_preserved` becomes exactly the `TransProbPreservingR` hypothesis of
`exists_isometry_of_transProbPreservingR`.

Over ℝ this is markedly shorter than the ℂ analogue (`WignerBridge`): there is no `star` to
move across the dot product and no `Complex.normSq` to unfold, so the inner product IS the dot
product on the nose.

* `inner_eq_dotProductR` — the inner product is the dot product of the underlying functions.
* `norm_sq_eq_dotProduct_self` — the squared norm is the self dot product.
* `transProbVecR_eq_sq_dotProduct` — for unit vectors the vendored transition probability is
  `(ψ ⬝ᵥ φ)²`, which is exactly the quantity `tprobR_preserved` transports.
-/

noncomputable section

open scoped Matrix

namespace Necessity

variable {N : ℕ}

/-- On `EuclideanSpace ℝ (Fin N)` the inner product is the dot product of the underlying
functions.  No conjugation appears, which is the whole simplification over ℂ. -/
theorem inner_eq_dotProductR (ψ φ : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ ψ φ : ℝ) = (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp φ) := by
  rw [PiLp.inner_apply]
  simp only [dotProduct, RCLike.inner_apply, starRingEnd_apply, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The squared norm is the self dot product. -/
theorem norm_sq_eq_dotProduct_self (ψ : EuclideanSpace ℝ (Fin N)) :
    ‖ψ‖ ^ 2 = (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp ψ) := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_dotProductR]

/-- **The bridge**: on unit vectors the vendored transition probability is the squared dot
product — the quantity that `tprobR_preserved` carries along an order automorphism. -/
theorem transProbVecR_eq_sq_dotProduct {ψ φ : EuclideanSpace ℝ (Fin N)}
    (hψ : (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp ψ) = 1) (hφ : (WithLp.ofLp φ) ⬝ᵥ (WithLp.ofLp φ) = 1) :
    Projectivization.transProbVecR ψ φ = ((WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp φ)) ^ 2 := by
  have hφ1 : ‖φ‖ = 1 := by
    have h := norm_sq_eq_dotProduct_self φ
    rw [hφ] at h
    nlinarith [norm_nonneg φ, h]
  have hψ1 : ‖ψ‖ = 1 := by
    have h := norm_sq_eq_dotProduct_self ψ
    rw [hψ] at h
    nlinarith [norm_nonneg ψ, h]
  rw [Projectivization.transProbVecR_of_norm_one hφ1, hψ1, one_pow, div_one,
    inner_eq_dotProductR]

/-- A nonzero function has nonzero self dot product, so it normalizes. -/
theorem dotProduct_self_ne_zero_of_ne_zero {v : Fin N → ℝ} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 :=
  fun h => hv (dotProduct_self_eq_zero.mp h)

/-- The normalization of a nonzero function, and the fact that it is a unit vector. -/
def unitVecR {v : Fin N → ℝ} (_hv : v ≠ 0) : Fin N → ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v

theorem unitVecR_unit {v : Fin N → ℝ} (hv : v ≠ 0) : unitVecR hv ⬝ᵥ unitVecR hv = 1 := by
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dotProduct_self_nonnegR v) (Ne.symm (dotProduct_self_ne_zero_of_ne_zero hv))
  rw [unitVecR, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
    inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- Normalizing does not change the rank-one projection's ray: it scales it by a positive
factor, and on the nose it is the same projection for a unit vector. -/
theorem rankOneR_unitVecR {v : Fin N → ℝ} (hv : v ≠ 0) :
    rankOneR (unitVecR hv) = ((v ⬝ᵥ v)⁻¹) • rankOneR v := by
  have hpos : 0 < v ⬝ᵥ v :=
    lt_of_le_of_ne (dotProduct_self_nonnegR v) (Ne.symm (dotProduct_self_ne_zero_of_ne_zero hv))
  rw [unitVecR, rankOneR_smul, inv_pow, Real.sq_sqrt hpos.le]

end Necessity
