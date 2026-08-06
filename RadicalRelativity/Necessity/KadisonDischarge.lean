/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RayMap
import RadicalRelativity.Necessity.JordanWitness
import RadicalRelativity.Necessity.ComparisonInstance
import RadicalRelativity.Necessity.PhaseAnchor

set_option linter.style.longLine false

/-!
# Kadison rigidity on `H_N(ℂ)`: the M3 discharge  (LEDGER M3)

**Every unital `ℝ`-linear order-automorphism of `H_N(ℂ)` is a Jordan
automorphism** (`orderAuto_preservesJordan`).  This is the paper's `prop:theta`
input (van Imhoff–Roelands / Kadison rigidity), the single hypothesis
`ThetaPreservesJordan` that every M2 result was conditional on.

The chain, all machine-checked in this development except the disclosed
vendored rigidity theorem:

1. `exists_rankOne_map` — `Φ` permutes rank-one projections, because
   atomicity of the projection order is order data (bridge 1).
2. `rayMap` / `rayMap_transProbPreserving` — hence `Φ` induces a self-map of
   `ℂℙ^{N-1}` preserving the transition probability.  The transition
   probability is *recovered from the order* by the Busch–Gudder strength
   function on the probe `½(𝟙 + φφ*)` (bridge 2).
3. `Projectivization.wigner_rigidity` (**the one disclosed import**) — such a
   map is induced by a unitary or an antiunitary.
4. `unitaryConj_preservesJordan` / `antiunitaryConj_preservesJordan` — both
   witnesses are Jordan automorphisms.
5. `linearMap_eq_of_eq_on_rankOne` — rank-ones span, so agreeing with a Jordan
   automorphism on them makes `Φ` equal to it.

Step 5 is what makes the conclusion about `Φ` itself rather than about its
action on rank-ones.
-/

noncomputable section

open ComplexOrder
open scoped Matrix LinearAlgebra.Projectivization

namespace Necessity

variable {N : ℕ}

/-- The Jordan property transfers along an equality of linear maps. -/
theorem preservesJordan_of_eq
    {S T : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ}
    (h : S = T) (hT : PreservesJordan T) : PreservesJordan S := by
  rw [h]
  exact hT

/-- **The M3 discharge, modulo identifying the Wigner witness on rank-ones.**

Given that `Φ` agrees on every rank-one projection with a map `Ψ` that is a
Jordan automorphism, `Φ = Ψ` (rank-ones span) and so `Φ` preserves the Jordan
product.  This isolates the only remaining Wigner-side computation: turning
`rayMap Φ = projMap e` into the rank-one agreement
`Φ (rankOne ψ) = Ψ (rankOne ψ)`. -/
theorem preservesJordan_of_agrees_on_rankOne
    (Φ Ψ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΨ : PreservesJordan Ψ)
    (hagree : ∀ ψ : Fin N → ℂ, star ψ ⬝ᵥ ψ = 1 →
      Φ (HermitianMat.rankOne ψ) = Ψ (HermitianMat.rankOne ψ)) :
    PreservesJordan Φ :=
  preservesJordan_of_eq
    (HermitianMat.linearMap_eq_of_eq_on_rankOne Φ Ψ hagree) hΨ

/-- **The unitary branch, assembled.**  If `Φ` acts on rank-one projections as
conjugation by `U` (with `Uᴴ U = 1`), then `Φ` *is* that conjugation and hence
a Jordan automorphism. -/
theorem preservesJordan_of_unitary_on_rankOne
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1)
    (hagree : ∀ ψ : Fin N → ℂ, star ψ ⬝ᵥ ψ = 1 →
      Φ (HermitianMat.rankOne ψ) = (HermitianMat.rankOne ψ).conj U) :
    PreservesJordan Φ :=
  preservesJordan_of_agrees_on_rankOne Φ (unitaryConj U)
    (unitaryConj_preservesJordan hU) hagree

/-- **The antiunitary branch, assembled.** -/
theorem preservesJordan_of_antiunitary_on_rankOne
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1)
    (hagree : ∀ ψ : Fin N → ℂ, star ψ ⬝ᵥ ψ = 1 →
      Φ (HermitianMat.rankOne ψ)
        = (transposeMap (HermitianMat.rankOne ψ)).conj U) :
    PreservesJordan Φ :=
  preservesJordan_of_agrees_on_rankOne Φ
    ((unitaryConj U).comp (transposeMap (n := Fin N)))
    (antiunitaryConj_preservesJordan hU) hagree

/-- **The Wigner dichotomy, applied to the induced ray map.**  Every unital
`ℝ`-linear order-automorphism of `H_N(ℂ)` induces a projective self-map that is
`projMap e` for a linear isometry equivalence `e`, or its composite with
conjugation.  This is the vendored theorem consumed at the exact interface the
order-theoretic bridges produce. -/
theorem rayMap_dichotomy
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ) :
    (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, rayMap Φ hΦ hunital hsurj p = Projectivization.projMap e p)
      ∨ (∃ e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N),
        ∀ p, rayMap Φ hΦ hunital hsurj p
          = Projectivization.projMap e (Projectivization.conjProj p)) :=
  Projectivization.wigner_rigidity (rayMap_transProbPreserving Φ hΦ hunital hsurj)

/-! ## The matrix identity closing the unitary branch -/

/-- `(Uψ)(Uψ)* = U(ψψ*)U*`: conjugation of a rank-one is the rank-one of the
image.  Entrywise `vecMulVec`/`mul` computation. -/
theorem rankOne_mulVec_eq_conj (U : Matrix (Fin N) (Fin N) ℂ) (ψ : Fin N → ℂ) :
    HermitianMat.rankOne (U *ᵥ ψ) = (HermitianMat.rankOne ψ).conj U := by
  ext1
  rw [HermitianMat.rankOne_mat, HermitianMat.conj_apply_mat,
    HermitianMat.rankOne_mat]
  ext a b
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Pi.star_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Finset.mul_sum, star_sum, star_mul']
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The matrix of an isometry equivalence is unitary in the `Uᴴ U = 1` form. -/
theorem unitaryOfIsometry_conjTranspose_mul
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N)) :
    (Projectivization.unitaryOfIsometry e)ᴴ
        * Projectivization.unitaryOfIsometry e = 1 := by
  have h := Projectivization.unitaryOfIsometry_mem e
  rw [Matrix.mem_unitaryGroup_iff'] at h
  exact h

/-- The isometry acts on coordinates as its matrix. -/
theorem isometry_apply_eq_mulVec
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (ψ : EuclideanSpace ℂ (Fin N)) :
    WithLp.ofLp (e ψ)
      = Projectivization.unitaryOfIsometry e *ᵥ (WithLp.ofLp ψ) := by
  have h := Projectivization.unitaryOfIsometry_toEuclideanLin e
  have h2 : Matrix.toEuclideanLin (Projectivization.unitaryOfIsometry e) ψ = e ψ := by
    rw [h]
    rfl
  rw [← h2]
  rfl

/-! ## The unitary branch, closed end to end -/

/-- **M3 on the unitary branch.**  If the induced ray map is `projMap e`, then
`Φ` preserves the Jordan product.

The chain: `rayMap_rankOne` says `Φ` acting on the ray's rank-one is the
rank-one of the image ray; substituting `projMap e` and computing through
`projMap_mk` / `rankOneP_mk` reduces to `(eψ)(eψ)* = U(ψψ*)U*`, which is
`rankOne_mulVec_eq_conj` with `U = unitaryOfIsometry e`. -/
theorem preservesJordan_of_rayMap_eq_projMap
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ)
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (he : ∀ p, rayMap Φ hΦ hunital hsurj p = Projectivization.projMap e p) :
    PreservesJordan Φ := by
  refine preservesJordan_of_unitary_on_rankOne Φ
    (unitaryOfIsometry_conjTranspose_mul e) ?_
  intro ψ hψ
  -- the ray of `ψ`
  have hne : (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro hz
    exact ne_zero_of_unit hψ ((WithLp.toLp_eq_zero (p := 2)).mp hz)
  set p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
    Projectivization.mk ℂ (WithLp.toLp 2 ψ) hne with hp
  -- `Φ` on the ray's rank-one, via the ray map
  have h1 := rayMap_rankOne Φ hΦ hunital hsurj p
  rw [rankOneP_mk hψ hne] at h1
  rw [he p, hp, Projectivization.projMap_mk e _ hne] at h1
  -- the image vector is `e ψ`, which has unit norm
  have hunit : star (WithLp.ofLp (e (WithLp.toLp 2 ψ)))
      ⬝ᵥ (WithLp.ofLp (e (WithLp.toLp 2 ψ))) = 1 := by
    have hnorm : HermitianMat.nsq
        (WithLp.ofLp (e (WithLp.toLp 2 ψ))) = 1 := by
      rw [← norm_sq_eq_nsq, e.norm_map, norm_sq_eq_nsq]
      have h2 : star ψ ⬝ᵥ ψ = ((HermitianMat.nsq ψ : ℝ) : ℂ) :=
        HermitianMat.dot_self_eq_nsq ψ
      rw [hψ] at h2
      have : HermitianMat.nsq ψ = 1 := by exact_mod_cast h2.symm
      simpa using this
    have h3 : star (WithLp.ofLp (e (WithLp.toLp 2 ψ)))
        ⬝ᵥ (WithLp.ofLp (e (WithLp.toLp 2 ψ)))
        = ((HermitianMat.nsq (WithLp.ofLp (e (WithLp.toLp 2 ψ))) : ℝ) : ℂ) :=
      HermitianMat.dot_self_eq_nsq _
    rw [h3, hnorm]
    norm_num
  rw [rankOneP_mk' _ hunit] at h1
  rw [h1, isometry_apply_eq_mulVec e, rankOne_mulVec_eq_conj]

/-! ## The antiunitary branch, closed end to end -/

/-- `(star ψ)(star ψ)* = (ψψ*)ᵗ`: the rank-one of the conjugate vector is the
transpose of the rank-one. -/
theorem rankOne_star_eq_transpose (ψ : Fin N → ℂ) :
    HermitianMat.rankOne (star ψ) = transposeMap (HermitianMat.rankOne ψ) := by
  ext1
  rw [HermitianMat.rankOne_mat, transposeMap_mat, HermitianMat.rankOne_mat]
  ext a b
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    star_star]
  ring

/-- Conjugation of a unit vector is a unit vector. -/
theorem star_unit {ψ : Fin N → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (star ψ) ⬝ᵥ (star ψ) = 1 := by
  rw [star_star]
  have h : ψ ⬝ᵥ star ψ = star ψ ⬝ᵥ ψ := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h, hψ]

/-- **M3 on the antiunitary branch.**  If the induced ray map is
`projMap e ∘ conjProj`, then `Φ` preserves the Jordan product. -/
theorem preservesJordan_of_rayMap_eq_projMap_conj
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ)
    (e : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (he : ∀ p, rayMap Φ hΦ hunital hsurj p
      = Projectivization.projMap e (Projectivization.conjProj p)) :
    PreservesJordan Φ := by
  refine preservesJordan_of_antiunitary_on_rankOne Φ
    (unitaryOfIsometry_conjTranspose_mul e) ?_
  intro ψ hψ
  have hne : (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro hz
    exact ne_zero_of_unit hψ ((WithLp.toLp_eq_zero (p := 2)).mp hz)
  set p : ℙ ℂ (EuclideanSpace ℂ (Fin N)) :=
    Projectivization.mk ℂ (WithLp.toLp 2 ψ) hne with hp
  have h1 := rayMap_rankOne Φ hΦ hunital hsurj p
  rw [rankOneP_mk hψ hne] at h1
  rw [he p] at h1
  -- the conjugated ray, then the isometry
  set w : EuclideanSpace ℂ (Fin N) :=
    Projectivization.conjVec (Projectivization.conjProj p).rep with hw
  have hcj : Projectivization.conjProj p
      = Projectivization.mk ℂ (Projectivization.conjVec p.rep)
        (Projectivization.conjVec_ne_zero p.rep_nonzero) := rfl
  -- `rankOneP` of the conjugated ray is the rank-one of `star ψ`
  have hconjrank : rankOneP (Projectivization.conjProj p)
      = HermitianMat.rankOne (star ψ) := by
    have hu : star (star ψ) ⬝ᵥ (star ψ) = 1 := star_unit hψ
    have hnez : (WithLp.toLp 2 (star ψ) : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
      intro hz
      exact ne_zero_of_unit hu ((WithLp.toLp_eq_zero (p := 2)).mp hz)
    have hmk : Projectivization.conjProj p
        = Projectivization.mk ℂ (WithLp.toLp 2 (star ψ)) hnez := by
      rw [hp, Projectivization.conjProj_mk hne]
      congr 1
    rw [hmk, rankOneP_mk hu hnez]
  -- the image of the conjugated ray under `projMap e`
  have hrep : star (WithLp.ofLp
        (e (WithLp.toLp 2 (star ψ)))) ⬝ᵥ
      (WithLp.ofLp (e (WithLp.toLp 2 (star ψ)))) = 1 := by
    have hu : star (star ψ) ⬝ᵥ (star ψ) = 1 := star_unit hψ
    have hn1 : HermitianMat.nsq (star ψ) = 1 := by
      have h2 : star (star ψ) ⬝ᵥ (star ψ)
          = ((HermitianMat.nsq (star ψ) : ℝ) : ℂ) :=
        HermitianMat.dot_self_eq_nsq _
      rw [hu] at h2
      exact_mod_cast h2.symm
    have hnorm : HermitianMat.nsq
        (WithLp.ofLp (e (WithLp.toLp 2 (star ψ)))) = 1 := by
      rw [← norm_sq_eq_nsq, e.norm_map, norm_sq_eq_nsq]
      simpa using hn1
    have h3 : star (WithLp.ofLp (e (WithLp.toLp 2 (star ψ))))
        ⬝ᵥ (WithLp.ofLp (e (WithLp.toLp 2 (star ψ))))
        = ((HermitianMat.nsq (WithLp.ofLp (e (WithLp.toLp 2 (star ψ)))) : ℝ) : ℂ) :=
      HermitianMat.dot_self_eq_nsq _
    rw [h3, hnorm]
    norm_num
  have hu : star (star ψ) ⬝ᵥ (star ψ) = 1 := star_unit hψ
  have hnez : (WithLp.toLp 2 (star ψ) : EuclideanSpace ℂ (Fin N)) ≠ 0 := by
    intro hz
    exact ne_zero_of_unit hu ((WithLp.toLp_eq_zero (p := 2)).mp hz)
  have hmk : Projectivization.conjProj p
      = Projectivization.mk ℂ (WithLp.toLp 2 (star ψ)) hnez := by
    rw [hp, Projectivization.conjProj_mk hne]
    congr 1
  rw [hmk, Projectivization.projMap_mk e _ hnez, rankOneP_mk' _ hrep] at h1
  rw [h1, isometry_apply_eq_mulVec e, rankOne_mulVec_eq_conj,
    rankOne_star_eq_transpose]

/-! ## The capstone: Kadison rigidity on `H_N(ℂ)` -/

/-- **KADISON RIGIDITY ON `H_N(ℂ)` (the M3 result).** Every unital `ℝ`-linear
order-automorphism of `H_N(ℂ)` is a Jordan automorphism.

This is the paper's `prop:theta` / van Imhoff–Roelands input, the single
hypothesis `ThetaPreservesJordan` on which every M2 result was conditional.
Both branches of the Wigner dichotomy are discharged: the unitary one by
conjugation, the antiunitary one by transpose-conjugation, and in each case the
spanning of rank-one projections upgrades agreement-on-rank-ones to equality of
maps. The only imported ingredient is the vendored, separately axiom-audited
`Projectivization.wigner_rigidity`. -/
theorem orderAuto_preservesJordan
    (Φ : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℂ, x ≤ y ↔ Φ x ≤ Φ y)
    (hunital : Φ 1 = 1) (hsurj : Function.Surjective Φ) :
    PreservesJordan Φ := by
  rcases rayMap_dichotomy Φ hΦ hunital hsurj with ⟨e, he⟩ | ⟨e, he⟩
  · exact preservesJordan_of_rayMap_eq_projMap Φ hΦ hunital hsurj e he
  · exact preservesJordan_of_rayMap_eq_projMap_conj Φ hΦ hunital hsurj e he

/-! ## Discharging `ThetaPreservesJordan` -/

/-- **`ThetaPreservesJordan` DISCHARGED (M3).**  Every comparison map of an
S1–S7 sequential product with S2 on `H_N(ℂ)` preserves the Jordan product,
because it is a unital surjective linear order-isomorphism and
`orderAuto_preservesJordan` applies.

This makes every M2 result — up to and including the per-frame parameter
`complex_perFrame_concrete` — **unconditional**, modulo only the vendored,
separately axiom-audited `Projectivization.wigner_rigidity`. -/
theorem thetaPreservesJordan_of_S2
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) :
    ThetaPreservesJordan P := by
  intro a ha hbd
  refine orderAuto_preservesJordan (theta P ha hbd) ?_ ?_ ?_
  · exact fun x y => (theta_le_iff P hS2 ha hbd x y).symm
  · exact theta_one P ha hbd
  · have hbij := (thetaEquiv P hS2 ha hbd).surjective
    intro y
    obtain ⟨x, hx⟩ := hbij y
    refine ⟨x, ?_⟩
    rw [← thetaEquiv_apply P hS2 ha hbd x]
    exact hx

/-! ## The unconditional per-frame theorem -/

/-- **`thm:complex`, per frame, on `H_N(ℂ)` — UNCONDITIONAL.**

For *any* S1–S7 sequential product on `H_N(ℂ)` with `N ≥ 3` satisfying the
paper's S2 (first-argument norm continuity), the produced stabilizer coupling
carries a **single per-frame parameter**: `ρ_{ij}(dχ(r)) = (t_F(r_i − r_j)) • J`
on every block.

This is `complex_perFrame_concrete` with its `ThetaPreservesJordan` hypothesis
discharged by M3.  The hypothesis list is now exactly the paper's: an S1–S7
product, S2, and `N ≥ 3`. -/
theorem complex_perFrame_unconditional {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) :
    ∃ tF : ℝ, ∀ (i j : Fin N) (r : Fin N → ℝ),
      (stabilizerCoupling hN P hS2 (thetaPreservesJordan_of_S2 P hS2)).ρ i j
          ((stabilizerCoupling hN P hS2 (thetaPreservesJordan_of_S2 P hS2)).dχ r)
        = (tF * (r i - r j)) • rotJ :=
  complex_perFrame_concrete hN P hS2 (thetaPreservesJordan_of_S2 P hS2)

/-! ## The product-level structural theorem -/

/-- **`a • b = Q_{√a}(Θ_a b)` — the paper's structural identity, at the level of
the PRODUCT.**  For an invertible effect `a` and any effect `b`, the unknown
sequential product is the Lüders conjugation applied to the comparison map's
value.  This is `quadRep_theta` (the defining equation of `Θ`) read through
`seqLeftMul_apply_effect` (which identifies the linear extension with the
product on effects), so it speaks about `P.sp` rather than about an extension. -/
theorem sp_eq_quadRep_theta (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    {a b : HermitianMat (Fin N) ℂ} (ha : OrderUnitSpace.IsEffect a)
    (hbd : a.mat.PosDef) (hb : OrderUnitSpace.IsEffect b) :
    P.sp a b = (theta P ha hbd b).conj (a.cfc Real.sqrt).mat := by
  rw [← quadRepEquiv_apply a hbd, quadRep_theta P ha hbd b,
    seqLeftMul_apply_effect P ha hb]

/-- **The structural theorem with the comparison map certified.**  Combining
`sp_eq_quadRep_theta` with M3: for any S1–S7 product with S2 on `H_N(ℂ)`, the
product is `Q_{√a}` applied to a **Jordan automorphism** of the algebra.  The
remaining paper step is the identification of that Jordan automorphism with
`Ad_{a^{it}}`, which is what turns this into the twist normal form. -/
theorem sp_eq_quadRep_jordanAuto (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    {a : HermitianMat (Fin N) ℂ} (ha : OrderUnitSpace.IsEffect a)
    (hbd : a.mat.PosDef) :
    PreservesJordan (theta P ha hbd) ∧
      ∀ b : HermitianMat (Fin N) ℂ, OrderUnitSpace.IsEffect b →
        P.sp a b = (theta P ha hbd b).conj (a.cfc Real.sqrt).mat :=
  ⟨thetaPreservesJordan_of_S2 P hS2 ha hbd,
    fun b hb => sp_eq_quadRep_theta P ha hbd hb⟩

end Necessity
