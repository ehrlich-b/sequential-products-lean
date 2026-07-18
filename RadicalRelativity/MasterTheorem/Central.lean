/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SequentialProduct
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

/-!
# Central decomposition of a sequential product (`prop:central`)

Machine-checked fragment of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`, `prop:central`).

**`prop:central` (central decomposition).** On a finite-dimensional Euclidean Jordan
algebra `J = ⊕_α J_α` with central summand units `e_α`, an S1–S7 sequential product is
componentwise: writing `a_α := e_α ∘ a` for the central component,
`a & b = Σ_α a_α & b_α`, and each `a_α & b_α` lands in `J_α`.

## Scope honesty — what is and is not checked here

Exactly as flagged in the formalization plan's adversarial section, `prop:central` is
**not** downstream of S1–S7 alone: its proof imports the compatibility bridge
(`prop:bridge`) and van de Wetering Prop 5.2 (the identities `a • e_α = Q_{√a} e_α = a_α`
and `a ⌣ e_α`). Those are the paper's *cited imports*, so — faithful to the
`ComparisonSetup`-style "interface field" contract of this tree — they are carried here
as **explicit hypotheses** (`hproj`, `hcompat`, `hunit`, the central decomposition
`hdecomp`), never derived from a bare `SequentialProduct`. A version that "proved"
`prop:central` over a bare `SequentialProduct` without those fields would be silently
assuming the Jordan reference structure the paper is agnostic about.

The two axioms the proof genuinely *consumes* are S5 (`sp_assoc_of_compatible`) and S1
(`sp_add_right`), both already fields of `SequentialProductCore`. What Lean checks:

* `central_component` — the load-bearing per-summand identity
  `a & (π α b) = (π α a) & (π α b)`, from S5 + the carried imports. Zero `sorry`.
* `central_decomposition` — the componentwise formula `a & b = Σ_α (π α a) & (π α b)`,
  by iterating S1 over the central decomposition `b = Σ_α π α b`. Zero `sorry`.

**Left as a paper-only follow-up (deliberately NOT `sorry`ed):** the proposition's last
clause, "each restriction is itself an S1–S7 product on `(J_α, ≤, e_α)`." As the
adversarial analysis noted, that inheritance clause is the bulk of the actual
formalization work — it requires `J_α` as its own order-unit space, the sub-effect-interval
closure `0 ≤ x ≤ e_α ⟹ x ∈ J_α`, and an axiom-by-axiom transfer of S1/S3/S4/S5/S6/S7 to
the restricted product. None of that infrastructure exists in this skeleton, so the
componentwise formula is checked while summand-inheritance stays a paper-proof-only
follow-up. This module makes no claim to formalize it.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*, `prop:central`.
* van de Wetering, arXiv:1803.08453, §5 (Prop 5.2) + EJA-appendix compatibility bridge.
-/

noncomputable section

open OrderUnitSpace SequentialProduct SequentialProductCore

namespace MasterTheorem.Central

variable {V : Type*} [SequentialProductCore V]

/-- **Right additivity of the sequential product over a finite sum** (iterated S1).
For an effect `a` and a family `c : ι → V` whose partial sums are all effects
(`hpartial` — this is the "each tail sum is an effect `≤ 𝟙`" hypothesis, carried rather
than reproved), `a & (∑ i ∈ s, c i) = ∑ i ∈ s, a & c i`. The single axiom consumed is
S1 (`sp_add_right`); the induction is over the Finset `s`. -/
theorem sp_sum_right {a : V} (ha : IsEffect a) {ι : Type*} [DecidableEq ι]
    (c : ι → V) (hc : ∀ i, IsEffect (c i))
    (hpartial : ∀ t : Finset ι, IsEffect (∑ i ∈ t, c i)) (s : Finset ι) :
    a & (∑ i ∈ s, c i) = ∑ i ∈ s, a & c i := by
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact sp_zero_right ha
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have hbound : c x + ∑ i ∈ s, c i ≤ (𝟙 : V) := by
      have h := (hpartial (insert x s)).2
      rwa [Finset.sum_insert hx] at h
    rw [sp_add_right ha (hc x) (hpartial s) hbound, ih]

/-- **`prop:central` (per-summand core, PROVED).** The load-bearing identity of the
central decomposition: for a central summand unit `e α` with associated projection
`π α` (`π α a = e α ∘ a`), an S1–S7 product satisfies
`a & (π α b) = (π α a) & (π α b)`.

The three imported facts are carried as hypotheses (audit by reading the signature):
* `hcompat : a & (e α) = (e α) & a` — bridge: `e α` central ⟹ operator-commutes with
  every effect ⟹ compatible for the unknown product;
* `hproj   : a & (e α) = π α a` — bridge + vdW Prop 5.2 (`a • e_α = Q_{√a} e_α = a_α`);
* `hunit   : (e α) & (π α b) = π α b` — vdW Prop 5.2 for `b_α ≤ e_α` (`e_α • b_α = b_α`).

The proof consumes exactly S5 (`sp_assoc_of_compatible`), with the compatibility
`hcompat` as its hypothesis:
`a & (π α b) = a & ((e α) & (π α b)) = (a & (e α)) & (π α b) = (π α a) & (π α b)`. -/
theorem central_component {m : ℕ} (e : Fin m → V) (π : Fin m → V → V)
    {a b : V} (ha : IsEffect a) (α : Fin m)
    (he : IsEffect (e α)) (hπb_eff : IsEffect (π α b))
    (hcompat : a & (e α) = (e α) & a)
    (hproj : a & (e α) = π α a)
    (hunit : (e α) & (π α b) = π α b) :
    a & (π α b) = (π α a) & (π α b) := by
  have hS5 := sp_assoc_of_compatible ha he hπb_eff hcompat
  rw [hunit] at hS5
  rw [hS5, hproj]

/-- **`prop:central` (central decomposition, main formula, PROVED).** For a finite family
of central summand units `e : Fin m → V` and their central projections `π : Fin m → V → V`
(`π α a = e α ∘ a`), an S1–S7 sequential product is componentwise:
`a & b = ∑ α, (π α a) & (π α b)`.

Imports carried as hypotheses (the cited bridge/vdW-Prop-5.2 surface, NOT derived):
* `he`       : each central unit `e α` is an effect;
* `hπb_eff`  : each component `π α b` is an effect;
* `hpartial` : every partial sum `∑ α ∈ t, π α b` is an effect (the "tail sum `≤ 𝟙`"
               hypothesis needed to iterate S1);
* `hcompat`  : `a & (e α) = (e α) & a` (bridge: `e α` central ⟹ compatible);
* `hproj`    : `a & (e α) = π α a` (bridge + vdW Prop 5.2);
* `hunit`    : `(e α) & (π α b) = π α b` (vdW Prop 5.2, `b_α ≤ e_α`);
* `hdecomp`  : `b = ∑ α, π α b` (central decomposition of the effect `b`).

Proof: `sp_sum_right` (iterated S1) pushes `a &` through `b = ∑ α, π α b`, then
`central_component` (S5 + imports) rewrites each term `a & (π α b)` to
`(π α a) & (π α b)`. The two axioms consumed are S1 and S5, both `SequentialProductCore`
fields; the summand-inheritance clause is a documented paper-only follow-up (see the
module docstring). -/
theorem central_decomposition {m : ℕ} (e : Fin m → V) (π : Fin m → V → V)
    {a b : V} (ha : IsEffect a)
    (he : ∀ α, IsEffect (e α))
    (hπb_eff : ∀ α, IsEffect (π α b))
    (hpartial : ∀ t : Finset (Fin m), IsEffect (∑ α ∈ t, π α b))
    (hcompat : ∀ α, a & (e α) = (e α) & a)
    (hproj : ∀ α, a & (e α) = π α a)
    (hunit : ∀ α, (e α) & (π α b) = π α b)
    (hdecomp : b = ∑ α, π α b) :
    a & b = ∑ α, (π α a) & (π α b) := by
  conv_lhs => rw [hdecomp]
  calc a & (∑ α, π α b)
      = ∑ α, a & (π α b) :=
        sp_sum_right ha (fun α => π α b) hπb_eff hpartial Finset.univ
    _ = ∑ α, (π α a) & (π α b) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        exact central_component e π ha α (he α) (hπb_eff α)
          (hcompat α) (hproj α) (hunit α)

end MasterTheorem.Central
