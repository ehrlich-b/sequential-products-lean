/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RankOneSpan
import RadicalRelativity.Vendor.Wigner.WignerRigidity

set_option linter.style.longLine false

/-!
# The bridge to Wigner rigidity  (M3, 3.2b)

Identifies the vendored projective transition probability with the
order-recovered `tprob`, so that `tprob_preserved` becomes exactly the
`TransProbPreserving` hypothesis of `Projectivization.wigner_rigidity`.

* `inner_eq_dotProduct` — on `EuclideanSpace ℂ (Fin N)` the inner product is
  the `star`-first dot product of the underlying functions.
* `transProbVec_eq_tprob` — for unit vectors,
  `transProbVec ψ φ = tprob (ofLp ψ) (ofLp φ)`.
* `unitVec` / `unitVec_unit` — normalization of a nonzero vector, and
  `rankOne_unitVec` : rescaling does not change the rank-one projection.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {N : ℕ}

/-! ## The inner product is the dot product -/

/-- On `EuclideanSpace ℂ (Fin N)` the inner product is the `star`-first dot
product of the underlying functions. -/
theorem inner_eq_dotProduct (ψ φ : EuclideanSpace ℂ (Fin N)) :
    (inner ℂ ψ φ : ℂ) = star (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp φ) := by
  rw [PiLp.inner_apply]
  simp only [dotProduct, Pi.star_apply, RCLike.inner_apply, starRingEnd_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The squared norm is the self dot product. -/
theorem norm_sq_eq_nsq (ψ : EuclideanSpace ℂ (Fin N)) :
    ‖ψ‖ ^ 2 = HermitianMat.nsq (WithLp.ofLp ψ) := by
  have h := inner_eq_dotProduct ψ ψ
  rw [HermitianMat.dot_self_eq_nsq] at h
  have h2 : ((‖ψ‖ ^ 2 : ℝ) : ℂ) = ((HermitianMat.nsq (WithLp.ofLp ψ) : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  exact_mod_cast h2

/-! ## The transition probabilities agree -/

/-- **The bridge**: on unit vectors the vendored `transProbVec` is the
order-recovered `tprob`. -/
theorem transProbVec_eq_tprob {ψ φ : EuclideanSpace ℂ (Fin N)}
    (hψ : HermitianMat.nsq (WithLp.ofLp ψ) = 1)
    (hφ : HermitianMat.nsq (WithLp.ofLp φ) = 1) :
    Projectivization.transProbVec ψ φ
      = HermitianMat.tprob (WithLp.ofLp ψ) (WithLp.ofLp φ) := by
  unfold Projectivization.transProbVec
  rw [norm_sq_eq_nsq, norm_sq_eq_nsq, hψ, hφ, mul_one, div_one]
  rw [inner_eq_dotProduct, HermitianMat.tprob]
  rw [Complex.normSq_eq_norm_sq]
  have hcj : star (WithLp.ofLp φ) ⬝ᵥ (WithLp.ofLp ψ)
      = star (star (WithLp.ofLp ψ) ⬝ᵥ (WithLp.ofLp φ)) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hcj, Complex.star_def, RCLike.norm_conj]

/-! ## Normalization -/

/-- The normalization of a nonzero vector. -/
def unitVec {v : Fin N → ℂ} (_hv : HermitianMat.nsq v ≠ 0) : Fin N → ℂ :=
  (((Real.sqrt (HermitianMat.nsq v))⁻¹ : ℝ) : ℂ) • v

theorem unitVec_unit {v : Fin N → ℂ} (hv : HermitianMat.nsq v ≠ 0) :
    star (unitVec hv) ⬝ᵥ (unitVec hv) = 1 := by
  have hpos : 0 < HermitianMat.nsq v :=
    lt_of_le_of_ne (HermitianMat.nsq_nonneg v) (Ne.symm hv)
  rw [unitVec, HermitianMat.dot_self_eq_nsq, HermitianMat.nsq_smul]
  have hnn : Complex.normSq (((Real.sqrt (HermitianMat.nsq v))⁻¹ : ℝ) : ℂ)
      = ((Real.sqrt (HermitianMat.nsq v))⁻¹) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hnn, inv_pow, Real.sq_sqrt hpos.le,
    show (HermitianMat.nsq v)⁻¹ * HermitianMat.nsq v = 1 from inv_mul_cancel₀ hv]
  norm_num

/-- **Rescaling does not change the rank-one projection** (up to the positive
scalar), so the rank-one of a normalized vector is determined by the ray. -/
theorem rankOne_smul_unit {c : ℂ} (hc : Complex.normSq c = 1) (v : Fin N → ℂ) :
    HermitianMat.rankOne (c • v) = HermitianMat.rankOne v := by
  rw [HermitianMat.rankOne_smul, hc, one_smul]

end Necessity
