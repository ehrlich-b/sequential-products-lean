/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — the real branch (`prop:real`)

The real typewise branch of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`, `prop:real`).

**`prop:real`.** On `Hₙ(ℝ)` the off-diagonal Peirce block `V_{ij}` is
one-dimensional (`blockDim (.real n) = 1`), so `𝔰𝔬(V_{ij}) = 𝔰𝔬(1) = 0`: the
frame-stabilizer acts on each block by a *skew-adjoint operator on a
one-dimensional real inner product space*, and every such operator is zero.
Hence every block twist `T_{ij}` vanishes and the product is Lüders,
`a•b = Q_{√a}b`.

## Rank independence (the selling point)

Unlike the quaternionic and exceptional branches, this argument uses **no**
third index: it never touches the `rank_ge : 3 ≤ n` field. The paper states
`prop:real` for all `n ≥ 2` (the real qubit is rigid). We record the kill as
`real_kill`, a lemma about the `StabilizerCoupling` *data* (`ρ`, `dχ`, `T`,
`ρ_skew`, `coupling`) with **no rank hypothesis at all** — so it visibly holds
at every rank, including `n = 2`. The capstone `real_luders` specializes it to a
`StabilizerCoupling n Stab ℝ` (the block space `V := ℝ` modelling the
one-dimensional real Peirce block); its proof consumes `real_kill` and therefore
inherits the rank-independence.

This branch introduces **no axioms** and leaves **no `sorry`**.
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

/-- **`𝔰𝔬(1) = 0`, concretely.** A skew-adjoint operator on the one-dimensional
real inner product space `ℝ` is zero: if `⟪f x, x⟫ = 0` for all `x`, then `f = 0`.
Every endomorphism of `ℝ` is scalar (`f x = x • f 1`); the skew condition at
`x = 1` gives `f 1 · ‖1‖² = 0`, hence `f 1 = 0`, hence `f = 0`. This is the whole
content of the real branch: the block `V_{ij}` of `Hₙ(ℝ)` is one-dimensional, so
`T_{ij} ∈ 𝔰𝔬(V_{ij}) = 0`. -/
theorem skew_one_dim_eq_zero (f : ℝ →ₗ[ℝ] ℝ) (h : ∀ x : ℝ, ⟪f x, x⟫_ℝ = 0) :
    f = 0 := by
  have hc : f 1 = 0 := by
    have h1 := h 1
    rw [show f 1 = (f 1) • (1 : ℝ) by rw [smul_eq_mul, mul_one], real_inner_smul_left,
        real_inner_self_eq_norm_sq, norm_one] at h1
    simpa using h1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply, show x = x • (1 : ℝ) by rw [smul_eq_mul, mul_one], map_smul, hc,
      smul_zero]

variable {n : ℕ} {Stab : Type*} [AddCommGroup Stab] [Module ℝ Stab]

/-- **`prop:real`, rank-free core.** For a frame-stabilizer coupling whose block
space is the one-dimensional `V := ℝ`, every off-diagonal twist vanishes,
`T_{ij} = 0` (`i ≠ j`). The proof reads the coupling at `r = e_i` (so
`r_i − r_j = 1`), observes the left side `ρ_{ij}(dχ(r))` is skew (`ρ_skew`) hence
zero on the one-dimensional block (`skew_one_dim_eq_zero`), and reads off
`T_{ij} = 0`.

This lemma takes the `StabilizerCoupling` **fields directly** rather than the
packaged structure, so it carries **no `rank_ge` hypothesis** — the real kill
holds at every rank `n`, matching `prop:real`'s `n ≥ 2` (the rigid real qubit).
`n ≥ 3` is never used. **This field-level lemma is the sole carrier of the
`n = 2` claim**: the packaged `real_luders` below quantifies over
`StabilizerCoupling`, whose `rank_ge : 3 ≤ n` field makes it uninstantiable at
`n = 2` (adversarial-review precision, 2026-07-15). -/
theorem real_kill (ρ : Fin n → Fin n → Stab →ₗ[ℝ] (ℝ →ₗ[ℝ] ℝ))
    (dχ : (Fin n → ℝ) →ₗ[ℝ] Stab) (T : Fin n → Fin n → (ℝ →ₗ[ℝ] ℝ))
    (ρ_skew : ∀ i j (ξ : Stab) (x : ℝ), ⟪(ρ i j ξ) x, x⟫_ℝ = 0)
    (coupling : ∀ i j (r : Fin n → ℝ), ρ i j (dχ r) = (r i - r j) • T i j)
    {i j : Fin n} (hij : i ≠ j) : T i j = 0 := by
  have hskew : ρ i j (dχ (Pi.single i (1 : ℝ))) = 0 :=
    skew_one_dim_eq_zero _ (fun x => ρ_skew i j _ x)
  have hcoup := coupling i j (Pi.single i (1 : ℝ))
  rw [hskew] at hcoup
  have hr : (Pi.single i (1 : ℝ) : Fin n → ℝ) i - (Pi.single i (1 : ℝ) : Fin n → ℝ) j = 1 := by
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), sub_zero]
  rw [hr, one_smul] at hcoup
  exact hcoup.symm

/-- **`prop:real` (capstone).** On the real type — a `StabilizerCoupling` whose
block space is `V := ℝ`, the one-dimensional real Peirce block
(`blockDim (.real n) = 1`) — every off-diagonal block twist vanishes:
`T_{ij} = 0` for `i ≠ j`. In the paper's normal-form reading this is `Θ_r = id`
on every block, i.e. the L\"uders product `a•b = Q_{√a}b`; the Lean statement is
exactly `T i j = 0` (see the naming-convention note in `Interface.lean`).

The proof is `real_kill` applied to the coupling's fields and never touches
`S.rank_ge`; note however that `StabilizerCoupling` itself carries
`rank_ge : 3 ≤ n`, so this packaged form is uninstantiable at `n = 2` — the
paper's `n ≥ 2` claim (the rigid real qubit) is carried by the field-level
`real_kill` above, which has no rank hypothesis at all. -/
theorem real_luders (S : StabilizerCoupling n Stab ℝ) {i j : Fin n} (hij : i ≠ j) :
    S.T i j = 0 :=
  real_kill S.ρ S.dχ S.T S.ρ_skew S.coupling hij

end MasterTheorem
