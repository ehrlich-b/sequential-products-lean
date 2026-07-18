/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — the complex branch, per-frame half (`thm:complex`)

The per-frame half of the complex typewise branch of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`, `thm:complex`, "one parameter per
> frame").

**`thm:complex` (per frame).** On `Hₙ(ℂ)` the frame stabilizer is the diagonal
torus and its Lie algebra acts on the block `V_{ij} ≅ ℂ ≅ ℝ²` by the rotation
generator `J` scaled by the real character difference `θ_i(r) − θ_j(r)`, with
`θ_i(r) = Σ_l c_{il} r_l` real-linear (`lem:homomorphism`). The coupling
`ρ_{ij}(dχ(r)) = (r_i − r_j)T_{ij}` pins this difference to
`θ_i(r) − θ_j(r) = (r_i − r_j)t_{ij}`. Coefficient matching then collapses the
per-pair constants `t_{ij}` to **one** constant per frame: for `l ∉ {i,j}`
(available since `n ≥ 3`) one gets `c_{il} = c_{jl}`, so `c_{il}` is a common
`γ_l` for all `i ≠ l`, and `t_{ij} = c_{ii} − γ_i = c_{jj} − γ_j =: t_F`. Hence
`Θ_r` acts on every block by the rotation of angle `t_F(r_i − r_j)`.

## What is proved here, and how the globalization lane consumes it

* `complex_perFrame_tF` — the **core**, self-contained over the concrete character
  matrix `c : Fin n → Fin n → ℝ` and the per-pair constants `t : Fin n → Fin n → ℝ`,
  with the proportionality `θ_i(r) − θ_j(r) = t_{ij}(r_i − r_j)` (the torus reading
  of `lem:homomorphism`/`StabilizerCoupling.coupling`) as its hypothesis. It
  produces the **single** `t_F` with `θ_i(r) − θ_j(r) = t_F(r_i − r_j)` for every
  pair and every `r`. **This is the capstone the Globalization lane consumes**
  (one instance per frame, then it compares `t_F` across adjacent frames).

* `complex_perFrame_rho` — the **grounding bridge**: a genuine
  `StabilizerCoupling n Stab V` in the torus model (a nonzero rotation generator
  `J : V →ₗ[ℝ] V` and `S.ρ_{ij}(S.dχ r) = (θ_i(r) − θ_j(r)) • J`) satisfies the
  core's hypothesis, so it likewise carries one `t_F` with
  `S.ρ_{ij}(S.dχ r) = (t_F(r_i − r_j)) • J`. This consumes `StabilizerCoupling`'s
  `coupling` and `rank_ge` fields directly, demonstrating the Interface seam.

## Honest scope of the model binding

The block `V` is kept abstract with only `J ≠ 0` assumed (the complex block is
`ℂ ≅ ℝ²` and `J = i·` its complex-structure generator; the per-frame collapse
uses solely that the rotation generator does not vanish, so no `2`-dimensionality
is imposed). The `n ≥ 3` hypothesis is used to select the reference off-diagonal
pair pinning the single `t_F`; the bridge supplies it from `S.rank_ge`.

This branch introduces **no axioms** and leaves **no `sorry`**. It is the
**per-frame** statement only; the frame-overlap globalization to a single global
`t` is the separate Globalization lane (`thm:complex`, "global parameter").
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

/-- **`thm:complex`, per-frame collapse (core).** Given the torus-model character
matrix `c` (with `θ_i(r) = Σ_l c_{il} r_l`) and per-pair constants `t` satisfying
the coalescence-pinned proportionality
`θ_i(r) − θ_j(r) = t_{ij}(r_i − r_j)` (the torus reading of `lem:homomorphism`),
there is a **single** real `t_F` with `θ_i(r) − θ_j(r) = t_F(r_i − r_j)` for
every pair `(i,j)` and every `r`.

The proof matches coefficients on the standard basis: reading the proportionality
at `r = e_l` gives `c_{il} = c_{jl}` whenever `l ∉ {i,j}` (column constancy),
`t_{ij} = c_{ii} − c_{ji}`, and `t_{ij} = c_{jj} − c_{ij}`. Column constancy makes
`t_{ij}` independent of the second index, and the two `t`-formulas give
`t_{ij} = t_{ji}`; chaining these collapses every off-diagonal `t_{ij}` to the
value at a fixed reference pair (`⟨0,·⟩, ⟨1,·⟩`, available since `n ≥ 3`). -/
theorem complex_perFrame_tF {n : ℕ} (hn : 3 ≤ n) (c t : Fin n → Fin n → ℝ)
    (hprop : ∀ i j (r : Fin n → ℝ),
      (∑ l, c i l * r l) - (∑ l, c j l * r l) = t i j * (r i - r j)) :
    ∃ tF : ℝ, ∀ i j (r : Fin n → ℝ),
      (∑ l, c i l * r l) - (∑ l, c j l * r l) = tF * (r i - r j) := by
  -- `θ_a` evaluated on the standard basis vector `e_l = Pi.single l 1`.
  have hsingle : ∀ (a l : Fin n),
      (∑ m, c a m * (Pi.single l (1 : ℝ) : Fin n → ℝ) m) = c a l := by
    intro a l
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, mul_one]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  -- The proportionality read on `e_l`.
  have hval : ∀ (a b l : Fin n),
      c a l - c b l
        = t a b * ((Pi.single l (1 : ℝ) : Fin n → ℝ) a
            - (Pi.single l (1 : ℝ) : Fin n → ℝ) b) := by
    intro a b l
    have h := hprop a b (Pi.single l (1 : ℝ))
    rwa [hsingle a l, hsingle b l] at h
  -- Column constancy: `c_{al} = c_{bl}` whenever `l ∉ {a,b}`.
  have hCC : ∀ (a b l : Fin n), a ≠ l → b ≠ l → c a l = c b l := by
    intro a b l ha hb
    have h := hval a b l
    rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb, sub_zero, mul_zero] at h
    exact sub_eq_zero.mp h
  -- `t_{ij} = c_{ii} − c_{ji}`.
  have ht1 : ∀ (i j : Fin n), i ≠ j → t i j = c i i - c j i := by
    intro i j hij
    have h := hval i j i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), sub_zero, mul_one] at h
    exact h.symm
  -- `t_{ij} = c_{jj} − c_{ij}`.
  have ht2 : ∀ (i j : Fin n), i ≠ j → t i j = c j j - c i j := by
    intro i j hij
    have h := hval i j j
    rw [Pi.single_eq_of_ne hij, Pi.single_eq_same, zero_sub, mul_neg, mul_one] at h
    linarith
  -- `t` is symmetric on off-diagonal pairs.
  have hsymm : ∀ (i j : Fin n), i ≠ j → t i j = t j i := by
    intro i j hij; rw [ht2 i j hij, ht1 j i (Ne.symm hij)]
  -- `t_{ij}` is independent of the second index.
  have hindep : ∀ (i j j' : Fin n), i ≠ j → i ≠ j' → t i j = t i j' := by
    intro i j j' hij hij'
    rw [ht1 i j hij, ht1 i j' hij', hCC j j' i (Ne.symm hij) (Ne.symm hij')]
  -- `t` is constant on all off-diagonal pairs.
  have hmaster : ∀ (a b a' b' : Fin n), a ≠ b → a' ≠ b' → t a b = t a' b' := by
    intro a b a' b' hab ha'b'
    by_cases haa' : a = a'
    · subst haa'; exact hindep a b b' hab ha'b'
    · have e1 : t a b = t a a' := hindep a b a' hab haa'
      have e2 : t a a' = t a' a := hsymm a a' haa'
      have e3 : t a' a = t a' b' := hindep a' a b' (Ne.symm haa') ha'b'
      rw [e1, e2, e3]
  -- Reference off-diagonal pair `(⟨0,_⟩, ⟨1,_⟩)`, available since `n ≥ 3`.
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  refine ⟨t ⟨0, h0⟩ ⟨1, h1⟩, fun i j r => ?_⟩
  by_cases hij : i = j
  · subst hij; simp
  · rw [hprop i j r, hmaster i j ⟨0, h0⟩ ⟨1, h1⟩ hij (Fin.ne_of_val_ne (by norm_num))]

variable {n : ℕ} {Stab : Type*} [AddCommGroup Stab] [Module ℝ Stab]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **`thm:complex`, per-frame half over a `StabilizerCoupling` (grounding
bridge).** A frame-stabilizer coupling `S` in the torus model — a nonzero
rotation generator `J : V →ₗ[ℝ] V` (the complex-structure generator on
`V_{ij} ≅ ℂ`) and block action `S.ρ_{ij}(S.dχ r) = (θ_i(r) − θ_j(r)) • J` with
`θ_i(r) = Σ_l c_{il} r_l` — carries a **single** per-frame `t_F` with
`S.ρ_{ij}(S.dχ r) = (t_F(r_i − r_j)) • J` on every block.

The coupling field `S.coupling` (`ρ_{ij}(dχ r) = (r_i − r_j)T_{ij}`) together with
the model pins `T_{ij} = (c_{ii} − c_{ji}) • J`; cancelling the nonzero `J`
(`hJ`) turns the model into the core's proportionality hypothesis, and
`complex_perFrame_tF` (fed `S.rank_ge` for `n ≥ 3`) delivers `t_F`. This is the
per-frame statement; globalization to a single `t` is a separate lane. -/
theorem complex_perFrame_rho (S : StabilizerCoupling n Stab V)
    (J : V →ₗ[ℝ] V) (hJ : J ≠ 0) (c : Fin n → Fin n → ℝ)
    (hmodel : ∀ i j (r : Fin n → ℝ),
      S.ρ i j (S.dχ r) = ((∑ l, c i l * r l) - (∑ l, c j l * r l)) • J) :
    ∃ tF : ℝ, ∀ i j (r : Fin n → ℝ),
      S.ρ i j (S.dχ r) = (tF * (r i - r j)) • J := by
  -- Scalar cancellation against the nonzero rotation generator `J`.
  have hcancel : ∀ (α β : ℝ), α • J = β • J → α = β := by
    intro α β h
    have hz : (α - β) • J = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hz with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hJ
  -- `θ_a` on the standard basis vector `e_l`.
  have hsingle : ∀ (a l : Fin n),
      (∑ m, c a m * (Pi.single l (1 : ℝ) : Fin n → ℝ) m) = c a l := by
    intro a l
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, mul_one]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  -- The twist generator on block `(i,j)` is a scalar multiple of `J`.
  have hT : ∀ (i j : Fin n), i ≠ j → S.T i j = (c i i - c j i) • J := by
    intro i j hij
    have hr : (Pi.single i (1 : ℝ) : Fin n → ℝ) i - (Pi.single i (1 : ℝ) : Fin n → ℝ) j = 1 := by
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), sub_zero]
    have key := (S.coupling i j (Pi.single i (1 : ℝ))).symm.trans (hmodel i j (Pi.single i (1 : ℝ)))
    rw [hr, one_smul, hsingle i i, hsingle j i] at key
    exact key
  -- Feed the model into the core's proportionality hypothesis.
  set t : Fin n → Fin n → ℝ := fun i j => c i i - c j i with ht_def
  have hprop : ∀ i j (r : Fin n → ℝ),
      (∑ l, c i l * r l) - (∑ l, c j l * r l) = t i j * (r i - r j) := by
    intro i j r
    by_cases hij : i = j
    · subst hij; simp [ht_def]
    · have hmod := hmodel i j r
      rw [S.coupling i j r, hT i j hij, smul_smul] at hmod
      have hc := hcancel _ _ hmod
      simp only [ht_def]
      rw [← hc]; ring
  obtain ⟨tF, htF⟩ := complex_perFrame_tF S.rank_ge c t hprop
  exact ⟨tF, fun i j r => by rw [hmodel i j r, htF i j r]⟩

end MasterTheorem
