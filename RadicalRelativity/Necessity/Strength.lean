/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ProjectionOrder

set_option linter.style.longLine false

/-!
# The Busch–Gudder strength function  (M3 bridge 2, part 1)

The **strength** of a rank-one projection in an effect,
`Str(p, a) = sup {t | t·p ≤ a}`, is built from the order and the real scalar
action alone, so every unital linear order-isomorphism preserves it
(`strength_map`) — this is the mechanism that turns purely order-theoretic
data into the metric datum Wigner rigidity consumes.

Contents:

* `rankOne_smul_le_iff` — the geometric core: `t·ψψ* ≤ a` iff for every `v`,
  `t·|⟪ψ,v⟫|² ≤ ⟪v, a v⟫` (Loewner order tested vectorwise through
  `le_iff_mulVec_le_mulVec`).
* `strength` — the definition, and `strength_map`: any additive, ℝ-homogeneous
  order-isomorphism preserves it (the defining set is literally transported).
* `strength_nonneg`, `strength_le_one_of_effect` — basic bounds via the
  `0 ∈ S` witness and the unit bound.

Part 2 (`Necessity/StrengthProbe.lean`) evaluates `Str` on the probe family
`a_ε = q + ε(𝟙 − q)`, recovering `tr(pq)` from order data.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The vectorwise reading of `t·ψψ* ≤ a` -/

omit [DecidableEq n] in
/-- The quadratic form of a rank-one projection: `⟪v, (ψψ*) v⟫ = ⟪v,ψ⟫⟪ψ,v⟫`. -/
theorem rankOne_quadratic (ψ v : n → ℂ) :
    star v ⬝ᵥ (rankOne ψ).mat *ᵥ v = (star v ⬝ᵥ ψ) * (star ψ ⬝ᵥ v) := by
  rw [rankOne_mat, Matrix.vecMulVec_mulVec, op_smul_eq_smul, dotProduct_smul,
    smul_eq_mul, mul_comm]

omit [DecidableEq n] in
/-- **The geometric core**: `t·ψψ* ≤ a` iff the rank-one quadratic form is
dominated by `a`'s, vectorwise. -/
theorem rankOne_smul_le_iff (t : ℝ) (ψ : n → ℂ) (a : HermitianMat n ℂ) :
    (t • rankOne ψ) ≤ a ↔
      ∀ v : n → ℂ, (t : ℂ) * ((star v ⬝ᵥ ψ) * (star ψ ⬝ᵥ v))
        ≤ star v ⬝ᵥ a.mat *ᵥ v := by
  rw [le_iff_mulVec_le_mulVec]
  constructor
  · intro h v
    have hv := h v
    rw [mat_smul, Matrix.smul_mulVec, dotProduct_smul,
      RCLike.real_smul_eq_coe_mul, rankOne_quadratic] at hv
    exact hv
  · intro h v
    have hv := h v
    rw [mat_smul, Matrix.smul_mulVec, dotProduct_smul,
      RCLike.real_smul_eq_coe_mul, rankOne_quadratic]
    exact hv

/-! ## The strength function -/

/-- The **Busch–Gudder strength** of the rank-one projection `ψψ*` in the
effect `a`: `Str(ψψ*, a) = sup {t | t·ψψ* ≤ a}`.  Defined from the order and
the real scalar action only. -/
def strength (p a : HermitianMat n ℂ) : ℝ :=
  sSup {t : ℝ | t • p ≤ a}

omit [Fintype n] [DecidableEq n] in
/-- The defining set contains `0` whenever `a` is positive, so it is nonempty. -/
theorem strength_set_nonempty {p a : HermitianMat n ℂ} (ha : 0 ≤ a) :
    {t : ℝ | t • p ≤ a}.Nonempty := by
  refine ⟨0, ?_⟩
  show (0 : ℝ) • p ≤ a
  rw [zero_smul]
  exact ha

/-- The defining set is bounded above when `p` is a nonzero projection and `a`
is an effect: `t·p ≤ a ≤ 𝟙` forces `t ≤ 1` by testing at a range vector. -/
theorem strength_set_bddAbove {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {a : HermitianMat n ℂ} (ha : a ≤ 1) :
    BddAbove {t : ℝ | t • rankOne ψ ≤ a} := by
  refine ⟨1, fun t ht => ?_⟩
  have hta : (t • rankOne ψ) ≤ 1 := le_trans ht ha
  have h := (rankOne_smul_le_iff t ψ 1).mp hta ψ
  rw [hψ, mul_one, mat_one, Matrix.one_mulVec, hψ, mul_one] at h
  exact_mod_cast h

omit [Fintype n] in
/-- **Order-isomorphism invariance of the strength.**  Any map that is additive,
ℝ-homogeneous, and an order isomorphism in both directions transports the
defining set exactly, hence preserves `strength`.  This is the whole point: the
strength is order data. -/
theorem strength_map (Φ : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    (hΦ : ∀ x y : HermitianMat n ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (p a : HermitianMat n ℂ) :
    strength (Φ p) (Φ a) = strength p a := by
  unfold strength
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  rw [← map_smul Φ t p]
  exact (hΦ (t • p) a).symm

/-! ## Basic bounds -/

theorem strength_nonneg {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {a : HermitianMat n ℂ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ strength (rankOne ψ) a :=
  le_csSup (strength_set_bddAbove hψ ha1) (by
    show (0 : ℝ) ∈ {t : ℝ | t • rankOne ψ ≤ a}
    simp only [Set.mem_setOf_eq]
    rw [show (0:ℝ) • rankOne ψ = 0 from zero_smul ℝ _]
    exact ha0)

theorem strength_le_one {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {a : HermitianMat n ℂ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    strength (rankOne ψ) a ≤ 1 :=
  csSup_le (strength_set_nonempty ha0) (fun t ht => by
    have hta : (t • rankOne ψ) ≤ 1 := le_trans ht ha1
    have h := (rankOne_smul_le_iff t ψ 1).mp hta ψ
    rw [hψ, mul_one, mat_one, Matrix.one_mulVec, hψ, mul_one] at h
    exact_mod_cast h)

/-- Membership certificate: any `t` with `t·p ≤ a` is at most the strength. -/
theorem le_strength {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {a : HermitianMat n ℂ} (ha1 : a ≤ 1) {t : ℝ} (ht : t • rankOne ψ ≤ a) :
    t ≤ strength (rankOne ψ) a :=
  le_csSup (strength_set_bddAbove hψ ha1) ht

omit [Fintype n] [DecidableEq n] in
/-- Upper certificate: a uniform bound on the defining set bounds the
strength. -/
theorem strength_le {p a : HermitianMat n ℂ} (ha0 : 0 ≤ a) {c : ℝ}
    (hc : ∀ t : ℝ, t • p ≤ a → t ≤ c) :
    strength p a ≤ c :=
  csSup_le (strength_set_nonempty ha0) hc

end HermitianMat
