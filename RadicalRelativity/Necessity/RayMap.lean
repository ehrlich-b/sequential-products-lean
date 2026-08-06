/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.WignerBridge

set_option linter.style.longLine false

/-!
# The ray map induced by an order-automorphism  (M3, 3.2c)

An order-automorphism `Φ` of `H_N(ℂ)` permutes rank-one projections
(`exists_rankOne_map`), so it induces a self-map of `ℂℙ^{N-1}`.  Rather than
constructing the map through a choice function on projective space (which would
force representative bookkeeping through `Quotient`), we work with the
*projection-level* statement and only pass to `ℙ` where the vendored theorem
needs it.

* `rankOneP` — the rank-one projection of a nonzero vector, normalized.
* `rankOneP_rep_eq` — `rankOneP` only depends on the ray: proportional vectors
  give the same projection.
* `tprob_rankOneP` — the transition probability of two rays computed from
  `rankOneP`'s data.
* `rayMap` and `rayMap_transProbPreserving` — the induced projective self-map
  and the fact that it preserves the transition probability, i.e. the exact
  hypothesis of `Projectivization.wigner_rigidity`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix LinearAlgebra.Projectivization

namespace Necessity

variable {N : ℕ}

/-! ## The normalized rank-one of a nonzero vector -/

theorem nsq_ne_zero_of_ne_zero {v : Fin N → ℂ} (hv : v ≠ 0) :
    HermitianMat.nsq v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hle : Complex.normSq (v i) ≤ HermitianMat.nsq v :=
    Finset.single_le_sum (f := fun j => Complex.normSq (v j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 := Complex.normSq_nonneg (v i)
  exact Complex.normSq_eq_zero.mp (by linarith [h ▸ hle])

/-- A unit vector is nonzero. -/
theorem ne_zero_of_unit {ψ : Fin N → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ψ ≠ 0 := by
  intro h
  rw [h] at hψ
  simp at hψ

/-- Normalizing a unit vector is the identity. -/
theorem unitVec_of_unit {ψ : Fin N → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (h : HermitianMat.nsq ψ ≠ 0) : unitVec h = ψ := by
  have hns : HermitianMat.nsq ψ = 1 := by
    have h1 : star ψ ⬝ᵥ ψ = ((HermitianMat.nsq ψ : ℝ) : ℂ) :=
      HermitianMat.dot_self_eq_nsq ψ
    rw [hψ] at h1
    exact_mod_cast h1.symm
  rw [unitVec, hns, Real.sqrt_one, inv_one]
  funext i
  simp

/-- The normalized canonical representative of a ray. -/
def repUnit (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : Fin N → ℂ :=
  unitVec (nsq_ne_zero_of_ne_zero (v := WithLp.ofLp p.rep) (by
    intro h
    exact p.rep_nonzero ((WithLp.ofLp_eq_zero (p := 2)).mp h)))

theorem repUnit_unit (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    star (repUnit p) ⬝ᵥ (repUnit p) = 1 := unitVec_unit _

/-- The rank-one projection attached to a point of `ℂℙ^{N-1}`. -/
def rankOneP (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : HermitianMat (Fin N) ℂ :=
  HermitianMat.rankOne (repUnit p)

/-- Normalizing a nonzero multiple of a **unit** vector recovers its rank-one
projection: the scalar becomes unit-modulus, which `rankOne` absorbs. -/
theorem rankOne_normalize_smul {ψ : Fin N → ℂ} (hns : HermitianMat.nsq ψ = 1)
    {a : ℂ} (ha : a ≠ 0) :
    HermitianMat.rankOne
        (((Real.sqrt (HermitianMat.nsq (a • ψ)))⁻¹ : ℝ) • (a • ψ))
      = HermitianMat.rankOne ψ := by
  have hnsa : HermitianMat.nsq (a • ψ) = Complex.normSq a := by
    rw [HermitianMat.nsq_smul, hns, mul_one]
  have hanorm : Real.sqrt (Complex.normSq a) = ‖a‖ := by
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg a)]
  have hne : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hcomb : (((Real.sqrt (HermitianMat.nsq (a • ψ)))⁻¹ : ℝ) : ℂ) • (a • ψ)
      = ((((‖a‖ : ℝ) : ℂ)⁻¹ * a) • ψ) := by
    rw [hnsa, hanorm, smul_smul]
    push_cast
    ring_nf
  have hcast : (((Real.sqrt (HermitianMat.nsq (a • ψ)))⁻¹ : ℝ) • (a • ψ))
      = (((Real.sqrt (HermitianMat.nsq (a • ψ)))⁻¹ : ℝ) : ℂ) • (a • ψ) := by
    funext i
    simp [Complex.real_smul]
  rw [hcast, hcomb, HermitianMat.rankOne_smul]
  have hmod : Complex.normSq ((((‖a‖ : ℝ) : ℂ)⁻¹ * a)) = 1 := by
    rw [Complex.normSq_mul, Complex.normSq_inv]
    have h1 : Complex.normSq (((‖a‖ : ℝ) : ℂ)) = ‖a‖ ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h1, Complex.normSq_eq_norm_sq]
    field_simp
  rw [hmod, one_smul]

/-- **`rankOneP` of a ray built from a unit vector recovers that vector's
projection**: the canonical representative differs by a nonzero scalar, which
normalization kills. -/
theorem rankOneP_mk {ψ : Fin N → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (hne : (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N)) ≠ 0) :
    rankOneP (Projectivization.mk ℂ (WithLp.toLp 2 ψ) hne)
      = HermitianMat.rankOne ψ := by
  have hns : HermitianMat.nsq ψ = 1 := by
    have h1 : star ψ ⬝ᵥ ψ = ((HermitianMat.nsq ψ : ℝ) : ℂ) :=
      HermitianMat.dot_self_eq_nsq ψ
    rw [hψ] at h1
    exact_mod_cast h1.symm
  obtain ⟨a, ha⟩ := Projectivization.rep_mk_eq_smul hne
  have hrep : (WithLp.ofLp (Projectivization.mk ℂ (WithLp.toLp 2 ψ) hne).rep)
      = (a : ℂ) • ψ := by
    rw [ha, Units.smul_def]
    rfl
  show HermitianMat.rankOne (repUnit _) = _
  unfold repUnit unitVec
  rw [hrep]
  exact rankOne_normalize_smul hns (by exact_mod_cast a.ne_zero)

/-- `rankOneP_mk` for an arbitrary Euclidean vector (no `toLp` wrapper needed):
`toLp (ofLp v) = v` holds by `rfl`, so this is the same statement. -/
theorem rankOneP_mk' {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0)
    (hu : star (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) = 1) :
    rankOneP (Projectivization.mk ℂ v hv)
      = HermitianMat.rankOne (WithLp.ofLp v) :=
  rankOneP_mk (ψ := WithLp.ofLp v) hu hv

/-! ## The induced projective map -/

/-- **The ray map** induced by an order-automorphism: send a ray to the ray of
the vector whose rank-one projection is the image of the ray's rank-one. -/
def rayMap (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) : ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
  Projectivization.mk ℂ
    (WithLp.toLp 2
      (exists_rankOne_map Φ hΦ hunital hsurj (repUnit_unit p)).choose)
    (by
      have hu := (exists_rankOne_map Φ hΦ hunital hsurj (repUnit_unit p)).choose_spec.1
      intro hz
      exact ne_zero_of_unit hu ((WithLp.toLp_eq_zero (p := 2)).mp hz))

/-- **The defining property of the ray map**: it implements `Φ` on rank-one
projections. -/
theorem rayMap_rankOne (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ)
    (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Φ (rankOneP p) = rankOneP (rayMap Φ hΦ hunital hsurj p) := by
  have hspec := (exists_rankOne_map Φ hΦ hunital hsurj (repUnit_unit p)).choose_spec
  rw [rayMap, rankOneP_mk hspec.1]
  exact hspec.2

/-! ## The ray map preserves transition probabilities -/

theorem nsq_repUnit (p : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    HermitianMat.nsq (repUnit p) = 1 := by
  have h1 : star (repUnit p) ⬝ᵥ (repUnit p)
      = ((HermitianMat.nsq (repUnit p) : ℝ) : ℂ) :=
    HermitianMat.dot_self_eq_nsq _
  rw [repUnit_unit p] at h1
  exact_mod_cast h1.symm

/-- `transProb` of two rays is the `tprob` of their normalized representatives. -/
theorem transProb_eq_tprob_repUnit (p q : ℙ ℂ (EuclideanSpace ℂ (Fin N))) :
    Projectivization.transProb p q
      = HermitianMat.tprob (repUnit p) (repUnit q) := by
  have hp : (WithLp.toLp 2 (repUnit p) : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro hz
    exact ne_zero_of_unit (repUnit_unit p) ((WithLp.toLp_eq_zero (p := 2)).mp hz)
  have hq : (WithLp.toLp 2 (repUnit q) : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro hz
    exact ne_zero_of_unit (repUnit_unit q) ((WithLp.toLp_eq_zero (p := 2)).mp hz)
  have hpp : Projectivization.mk ℂ (WithLp.toLp 2 (repUnit p)) hp = p := by
    have hnz := p.rep_nonzero
    conv_rhs => rw [← Projectivization.mk_rep p]
    unfold repUnit unitVec
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ hnz).mpr ?_
    refine ⟨((Real.sqrt (HermitianMat.nsq (WithLp.ofLp p.rep)))⁻¹ : ℝ), ?_⟩
    rfl
  have hqq : Projectivization.mk ℂ (WithLp.toLp 2 (repUnit q)) hq = q := by
    have hnz := q.rep_nonzero
    conv_rhs => rw [← Projectivization.mk_rep q]
    unfold repUnit unitVec
    refine (Projectivization.mk_eq_mk_iff' ℂ _ _ _ hnz).mpr ?_
    refine ⟨((Real.sqrt (HermitianMat.nsq (WithLp.ofLp q.rep)))⁻¹ : ℝ), ?_⟩
    rfl
  conv_lhs => rw [← hpp, ← hqq]
  rw [Projectivization.transProb_mk hp hq]
  exact transProbVec_eq_tprob (by simpa using nsq_repUnit p)
    (by simpa using nsq_repUnit q)

/-- **The ray map preserves the transition probability** — exactly the
hypothesis of `Projectivization.wigner_rigidity`.  Pure transport: the ray map
implements `Φ` on rank-ones (`rayMap_rankOne`), and `Φ` preserves `tprob`
(`tprob_preserved`). -/
theorem rayMap_transProbPreserving
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ) :
    Projectivization.TransProbPreserving (rayMap Φ hΦ hunital hsurj) := by
  intro p q
  rw [transProb_eq_tprob_repUnit, transProb_eq_tprob_repUnit]
  refine (HermitianMat.tprob_preserved Φ hΦ hunital (repUnit_unit p)
    (repUnit_unit q) (repUnit_unit _) (repUnit_unit _) ?_ ?_).symm
  · exact rayMap_rankOne Φ hΦ hunital hsurj p
  · exact rayMap_rankOne Φ hΦ hunital hsurj q

end Necessity
