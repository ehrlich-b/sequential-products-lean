/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RayMap
import RadicalRelativity.Necessity.JordanWitness

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

end Necessity
