/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.TwistNormalForm
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.style.longLine false

/-!
# Existence half of the twist normal form

This file and its companion `RadicalRelativity/TwistNormalForm.lean` are the
**separate earlier Lean development** described in the shipped paper's appendix
(the pair-local ansatz route). They predate the shipped manuscript and use its
earlier internal labels (`thm:normal-form`, `lem:mult-rep`, `prop:coherence`,
`prop:closure`, `def:canonical-composite`, `def:paths`), which are *not* section
labels of the shipped paper.  The sole axiom of this development,
`aczel_continuous_multiplicative` (declared in this file), lies outside the
`master_chain` import tree and does not enter its axiom closure. (The former
companion axiom `bgw_canonical_composite` in `TwistNormalForm.lean` was
eliminated 2026-08-04 into the proved-table definition `bgwComposite`.)

This file formalizes the **existence** direction of the block twist normal form
(that development's `thm:normal-form`): on a non-classical Peirce `1`-space `W`,
continuity, unitality, and compatible associativity force the off-diagonal action
into the shape `E(x,y) = x^A y^B` with commuting `A, B ∈ End(W)` and `A + B = Id`
— i.e. they *produce* a `TwistNormalForm.NormalForm W`.  The companion file
carries the `NormalForm` interface itself and the *coherence* direction
(`coherence_forces_luders`); this file supplies the missing construction of that
interface from the sequential-product axioms.

## What is proved

`Selection.normalForm_existence` : from `AnsatzData W` — the off-diagonal action
`E` together with the three algebraic identities and the continuity that Steps 1–3
of the paper's proof feed on — there **exists** a `NormalForm W` whose action
`nf.E` reproduces `E` on all positive eigenvalue pairs.  Combined with
`TwistNormalForm.NormalForm.coherence_forces_luders`, this closes the loop:
the axioms produce the normal form, and reciprocity then pins the Lüders value.

`Selection.normalForm_unique` : the **uniqueness** clause — any two normal forms
reproducing the same block action `E` on all positive pairs have equal generators
`A`, `B` and equal twist `T`.  This is Paper A's uniqueness statement ("there is a
*unique* `T_{ij}`"), proved as the paper proves it: "`h(x) = E(x,1) = x^A`
determines `A` (differentiate at `x = 1`), hence `T`".  `normalForm_data_unique`
restates it relative to fixed ansatz data `D`: the twist is a function of `D.E`.

## Map to Paper A

* `AnsatzData` bundles the *output of Step 1* of the proof (not S1–S7 directly):
  - `mul`      = eq. (endo-compose), `E(α₁,α₂)∘E(β₁,β₂) = E(α₁β₁,α₂β₂)`, which the
                 paper derives from **S5** (compatible associativity) via the
                 Peirce-Preservation Lemma and the linear-extension Lemma;
  - `unit`     = the **S3** normalization `E(1,1) = Id`;
  - `coalesce` = eq. (coalescence), `E(λ,λ) = λ·Id`, the paper's Step 3 input from
                 **decomposition-independence** (condition (b)) and continuity;
  - `cont_*`   = the **S2** continuity of the two one-parameter marginals.
* `aczel_continuous_multiplicative` = the paper's Lemma "Multiplicative
  one-parameter representation" (`lem:mult-rep`): the single imported analytic
  fact, an **axiom** (see below).
* `NormalForm.E`, `NormalForm.sum_eq_one`, `NormalForm.commute` = the boxed
  conclusion eq. (normal-form): `E(x,y)=x^A y^B`, `A+B=Id`, `[A,B]=0`.

## Faithfulness deltas (honest)

1. **Interface boundary = Step 1.**  We take the multiplicative composition law
   eq. (endo-compose) and the coalescence identity eq. (coalescence) as *hypothesis
   fields* of `AnsatzData`, rather than deriving them from S5 / decomposition
   independence over an order unit space.  That derivation (Step 1 of the proof,
   run through the Peirce-Preservation Lemma) lives in the un-formalized order-unit
   layer; capturing its output as an interface mirrors how the surrounding Lean
   development treats the S1–S7 spine.  We therefore formalize **Steps 2–3** of the
   proof and the reduction to `lem:mult-rep`.
2. **Domain (0,∞) vs (0,1].**  The paper states the block identities on eigenvalue
   pairs in `(0,1]`; we quantify over all positive reals `(0,∞)`.  The extension is
   harmless — the off-diagonal action `x^A y^B` is defined for every positive scalar
   and the multiplicative / coalescence identities hold verbatim — and it lets the
   coalescence generator `A+B` be read off by a two-sided derivative at the unit.
3. **`lem:mult-rep` is axiomatized (the full lemma).**  The earlier *manuscript*
   argument establishes `lem:mult-rep` elementarily (an integration argument turning
   the continuous semigroup into a `C¹` one-parameter subgroup); this Lean file does
   not formalize that analytic argument and takes the lemma as an axiom instead.  The operator form is standard one-parameter-group
   theory (a continuous multiplicative map is `GL`-valued and `t ↦ h(e^{-t})` is
   a continuous, hence smooth, one-parameter group); the scalar functional
   equation is classical (Aczél 1966).  The axiom states the lemma verbatim —
   both the existence and the uniqueness of `A` (`∃!`).  The uniqueness half of
   `thm:normal-form` is nonetheless re-derived here by differentiation rather
   than by invoking the axiom's `∃!`, so it carries no axiom beyond the standard
   three.
4. **`W`** is the manuscript's "arbitrary real vector space" (the Peirce `1`-space),
   encoded — as in `TwistNormalForm.lean` — as a finite-dimensional real normed
   space with `End(W) = W →L[ℝ] W`.

## References

* Ehrlich 2026, Paper A, Theorem (block normal form), Lemma (multiplicative
  one-parameter representation), proof Steps 1–3.
* J. Aczél, *Lectures on Functional Equations and Their Applications*, 1966
  (scalar continuous multiplicative maps).
-/

noncomputable section

namespace Selection

open NormedSpace TwistNormalForm

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [CompleteSpace W]

/-! ## The Aczél leg (`lem:mult-rep`), axiomatized -/

/-- **Multiplicative one-parameter representation** (the analytic leg of the
earlier development's `thm:normal-form`; its `lem:mult-rep`).

A continuous multiplicative map `h : (0,∞) → End(W)` with `h(1) = Id` has the form
`h(x) = x^A := exp((log x)·A)` for a **unique** generator `A ∈ End(W)`; in
particular `h` is `GL(W)`-valued.  This is the sole imported analytic fact of both
halves of `thm:normal-form`.

This is the operator form of the classical multiplicative-continuity theorem:
`h` is automatically `GL`-valued and `g(t) = h(e^{-t})` is a continuous
one-parameter group, hence has a bounded generator (standard
one-parameter-semigroup theory; `A` is recovered by differentiating at the
identity, whence uniqueness).  The scalar functional equation is classical
(Aczél 1966).  We axiomatize the operator statement rather than formalize that
analytic argument.  The statement matches the earlier development's `lem:mult-rep`
verbatim (both the existence and the uniqueness clause of `A`), not a weakening:
the existence half of `thm:normal-form` consumes the existence clause, the
uniqueness half matches the uniqueness clause (and is here re-derived
independently by differentiation, so it does not lean on the axiom's `∃!`).
Faithfulness delta: stated on all of `(0,∞)` rather than the earlier `(0,1]`
form (a harmless strengthening of the hypotheses, i.e. a weakening of the
axiom; see the module docstring). -/
axiom aczel_continuous_multiplicative
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W]
    (h : ℝ → (W →L[ℝ] W))
    (hcont : ContinuousOn h (Set.Ioi 0))
    (hmul : ∀ x, 0 < x → ∀ y, 0 < y → h (x * y) = h x * h y)
    (hone : h 1 = 1) :
    ∃! A : W →L[ℝ] W, ∀ x, 0 < x → h x = exp (Real.log x • A)

/-! ## The ansatz data (output of Step 1) -/

/-- The pair-local off-diagonal data on a single Peirce `1`-space `W`, at the
interface boundary of Theorem `thm:normal-form`.  `E x y` is the block action
`E_{ij}(x,y) ∈ End(W)` of the corrected product for eigenvalue pair `(x,y)`; the
fields are the identities Steps 1–3 of the proof consume (see the module docstring
for the map to S2/S3/S5 and decomposition-independence). -/
structure AnsatzData (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W] where
  /-- The off-diagonal block action `E_{ij}(x,y) ∈ End(W)` (eq. (general-product)). -/
  E : ℝ → ℝ → (W →L[ℝ] W)
  /-- eq. (endo-compose): the multiplicative composition law that **S5** imposes
  (via the Peirce-Preservation Lemma), `E(α₁,α₂)∘E(β₁,β₂) = E(α₁β₁,α₂β₂)`. -/
  mul : ∀ a₁ a₂ b₁ b₂, 0 < a₁ → 0 < a₂ → 0 < b₁ → 0 < b₂ →
        E a₁ a₂ * E b₁ b₂ = E (a₁ * b₁) (a₂ * b₂)
  /-- **S3** normalization: the unit `id = p₁ + p₂` acts as the identity,
  `E(1,1) = Id`. -/
  unit : E 1 1 = 1
  /-- eq. (coalescence): under **decomposition-independence** the coalesced effect
  `λ(p₁+p₂)` acts by the compression scalar, `E(λ,λ) = λ·Id`. -/
  coalesce : ∀ l, 0 < l → E l l = l • (1 : W →L[ℝ] W)
  /-- **S2** continuity of the left marginal `x ↦ E(x,1)`. -/
  cont_left : ContinuousOn (fun x => E x 1) (Set.Ioi 0)
  /-- **S2** continuity of the right marginal `y ↦ E(1,y)`. -/
  cont_right : ContinuousOn (fun y => E 1 y) (Set.Ioi 0)

namespace AnsatzData

variable (D : AnsatzData W)

/-! ## Step 2 (scalar reduction): the marginals and factorization -/

/-- Left marginal multiplicativity (Step 2): `E(x·y, 1) = E(x,1)·E(y,1)`, from
eq. (endo-compose) with `α₂ = β₂ = 1`. -/
theorem E_left_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    D.E (x * y) 1 = D.E x 1 * D.E y 1 := by
  have h := D.mul x 1 y 1 hx one_pos hy one_pos
  simpa [mul_one] using h.symm

/-- Right marginal multiplicativity (Step 2): `E(1, x·y) = E(1,x)·E(1,y)`, from
eq. (endo-compose) with `α₁ = β₁ = 1`. -/
theorem E_right_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    D.E 1 (x * y) = D.E 1 x * D.E 1 y := by
  have h := D.mul 1 x 1 y one_pos hx one_pos hy
  simpa [mul_one] using h.symm

/-- Factorization (Step 2): `E(x,y) = E(x,1)·E(1,y)`, from eq. (endo-compose) with
`α₂ = β₁ = 1`.  This reduces the two-variable action to the two commuting
one-parameter marginals `h(x)=E(x,1)` and `k(y)=E(1,y)`. -/
theorem E_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    D.E x y = D.E x 1 * D.E 1 y := by
  have h := D.mul x 1 1 y hx one_pos one_pos hy
  simpa [mul_one, one_mul] using h.symm

/-! ## Step 2 (Aczél) + Step 3 (coalescence): the existence theorem -/

/-- **Existence half of `thm:normal-form`.**  Given the pair-local ansatz data on a
Peirce `1`-space `W` — the block action `E` with the multiplicative composition law
(eq. endo-compose, from S5), unitality (S3), coalescence (eq. coalescence, from
decomposition-independence), and continuity (S2) — there exists a
`TwistNormalForm.NormalForm W` (two commuting endomorphisms `A, B` with `A+B=Id`)
whose action `nf.E x y = x^A y^B` reproduces `E` on every positive eigenvalue pair.

Proof (Paper A, Steps 2–3): the marginals `h(x)=E(x,1)`, `k(y)=E(1,y)` are
continuous multiplicative maps, so `lem:mult-rep` gives `h(x)=x^A`, `k(y)=y^B`
(the Aczél leg); factorization gives `E(x,y)=x^A y^B`; and the coalescence identity,
differentiated at the unit, forces `A+B=Id` — whence `B=Id−A` commutes with `A`. -/
theorem normalForm_existence :
    ∃ nf : NormalForm W, ∀ x y : ℝ, 0 < x → 0 < y → D.E x y = nf.E x y := by
  -- Step 2 (Aczél leg): apply `lem:mult-rep` to each continuous multiplicative marginal.
  -- The existence half consumes only the `∃` part of the axiom's `∃!` (`.exists`).
  obtain ⟨A, hA⟩ := (aczel_continuous_multiplicative (fun x => D.E x 1) D.cont_left
    (fun x hx y hy => D.E_left_mul hx hy) D.unit).exists
  obtain ⟨B, hB⟩ := (aczel_continuous_multiplicative (fun y => D.E 1 y) D.cont_right
    (fun x hx y hy => D.E_right_mul hx hy) D.unit).exists
  -- `hA : ∀ x > 0, E(x,1) = exp(log x • A)`, `hB : ∀ y > 0, E(1,y) = exp(log y • B)`.
  -- Step 3 (coalescence): rewrite `E(λ,λ)=λ·Id` along the one-parameter group `λ=eˢ`.
  have hcoal : ∀ s : ℝ, exp (s • A) * exp (s • B) = Real.exp s • (1 : W →L[ℝ] W) := by
    intro s
    have hs : (0 : ℝ) < Real.exp s := Real.exp_pos s
    have e1 : D.E (Real.exp s) 1 = exp (Real.log (Real.exp s) • A) := hA _ hs
    have e2 : D.E 1 (Real.exp s) = exp (Real.log (Real.exp s) • B) := hB _ hs
    rw [Real.log_exp] at e1 e2
    have hc := D.coalesce (Real.exp s) hs
    rw [D.E_factor hs hs, e1, e2] at hc
    exact hc
  -- Read off `A + B = Id` by differentiating `hcoal` at `s = 0`.
  have hA0 : HasDerivAt (fun s : ℝ => exp (s • A)) A 0 := by
    simpa [exp_zero] using hasDerivAt_exp_smul_const A (0 : ℝ)
  have hB0 : HasDerivAt (fun s : ℝ => exp (s • B)) B 0 := by
    simpa [exp_zero] using hasDerivAt_exp_smul_const B (0 : ℝ)
  have hderivL : HasDerivAt (fun s : ℝ => exp (s • A) * exp (s • B)) (A + B) 0 := by
    simpa [exp_zero] using hA0.mul hB0
  have hderivR : HasDerivAt (fun s : ℝ => exp (s • A) * exp (s • B)) 1 0 := by
    have hexp : HasDerivAt (fun s : ℝ => Real.exp s • (1 : W →L[ℝ] W)) 1 0 := by
      simpa using (Real.hasDerivAt_exp 0).smul_const (1 : W →L[ℝ] W)
    have heq : (fun s : ℝ => exp (s • A) * exp (s • B))
        = fun s : ℝ => Real.exp s • (1 : W →L[ℝ] W) := funext hcoal
    rw [heq]; exact hexp
  have hsum : A + B = 1 := hderivL.unique hderivR
  -- `[A,B]=0` is then automatic: `B = Id − A` commutes with `A`.
  have hBeq : B = 1 - A := by rw [← hsum]; abel
  have hcomm : Commute A B := by
    rw [hBeq]; exact (Commute.one_right A).sub_right (Commute.refl A)
  -- Assemble the normal form and verify it reproduces `E`.
  refine ⟨⟨A, B, hsum, hcomm⟩, ?_⟩
  intro x y hx hy
  have hAx : D.E x 1 = exp (Real.log x • A) := hA x hx
  have hBy : D.E 1 y = exp (Real.log y • B) := hB y hy
  change D.E x y = exp (Real.log x • A) * exp (Real.log y • B)
  rw [D.E_factor hx hy, hAx, hBy]

end AnsatzData

/-! ## Uniqueness half of `thm:normal-form`

The generators `A, B` — hence the twist `T = A − ½Id` — are **determined** by the
block action `E`.  This is the paper's uniqueness clause ("there is a *unique*
`T_{ij}`"), proved as the paper proves it: "the map `h(x) = E(x,1) = x^A` determines
`A` (differentiate at `x = 1`), hence `T`."  We read each generator off its marginal
by differentiating the one-parameter subgroup at the identity — the same
`hasDerivAt_exp_smul_const` + `HasDerivAt.unique` device used in the existence
proof's coalescence step and in `coherence_forces_luders`.  These carry **no axiom**
beyond the standard three (the Aczél `∃!` is not invoked). -/

/-- Left-generator determinacy: normal forms with the same left marginal `E(·,1)`
share their `x`-generator `A`.  (Paper A, `thm:normal-form` uniqueness: `x^A`
determines `A` by differentiation at the identity.) -/
theorem A_unique {nf₁ nf₂ : NormalForm W}
    (h : ∀ x, 0 < x → nf₁.E x 1 = nf₂.E x 1) : nf₁.A = nf₂.A := by
  have hsub : ∀ s : ℝ, exp (s • nf₁.A) = exp (s • nf₂.A) := by
    intro s
    have hs := h (Real.exp s) (Real.exp_pos s)
    simpa only [NormalForm.E_right_one, Real.log_exp] using hs
  have h1 : HasDerivAt (fun s : ℝ => exp (s • nf₁.A)) nf₁.A 0 := by
    simpa [exp_zero] using hasDerivAt_exp_smul_const nf₁.A (0 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => exp (s • nf₁.A)) nf₂.A 0 := by
    rw [funext hsub]
    simpa [exp_zero] using hasDerivAt_exp_smul_const nf₂.A (0 : ℝ)
  exact h1.unique h2

/-- Right-generator determinacy: normal forms with the same right marginal `E(1,·)`
share their `y`-generator `B`. -/
theorem B_unique {nf₁ nf₂ : NormalForm W}
    (h : ∀ y, 0 < y → nf₁.E 1 y = nf₂.E 1 y) : nf₁.B = nf₂.B := by
  have hsub : ∀ s : ℝ, exp (s • nf₁.B) = exp (s • nf₂.B) := by
    intro s
    have hs := h (Real.exp s) (Real.exp_pos s)
    simpa only [NormalForm.E_left_one, Real.log_exp] using hs
  have h1 : HasDerivAt (fun s : ℝ => exp (s • nf₁.B)) nf₁.B 0 := by
    simpa [exp_zero] using hasDerivAt_exp_smul_const nf₁.B (0 : ℝ)
  have h2 : HasDerivAt (fun s : ℝ => exp (s • nf₁.B)) nf₂.B 0 := by
    rw [funext hsub]
    simpa [exp_zero] using hasDerivAt_exp_smul_const nf₂.B (0 : ℝ)
  exact h1.unique h2

/-- **Uniqueness half of `thm:normal-form`.**  Two normal forms that reproduce the
same block action `E` on every positive eigenvalue pair have equal generators and
equal twist: `A`, `B`, and `T = A − ½Id` are determined by `E`. -/
theorem normalForm_unique {nf₁ nf₂ : NormalForm W}
    (h : ∀ x y : ℝ, 0 < x → 0 < y → nf₁.E x y = nf₂.E x y) :
    nf₁.A = nf₂.A ∧ nf₁.B = nf₂.B ∧ nf₁.T = nf₂.T := by
  have hA : nf₁.A = nf₂.A := A_unique fun x hx => h x 1 hx one_pos
  have hB : nf₁.B = nf₂.B := B_unique fun y hy => h 1 y one_pos hy
  refine ⟨hA, hB, ?_⟩
  simp only [NormalForm.T, hA]

/-- The twist normal form's data is a **function of the ansatz data**: any two normal
forms both reproducing `D.E` on all positive pairs have identical `A`, `B`, `T`.
With `AnsatzData.normalForm_existence`, the twist is the unique invariant the ansatz
data determines. -/
theorem AnsatzData.normalForm_data_unique (D : AnsatzData W) {nf₁ nf₂ : NormalForm W}
    (h₁ : ∀ x y : ℝ, 0 < x → 0 < y → D.E x y = nf₁.E x y)
    (h₂ : ∀ x y : ℝ, 0 < x → 0 < y → D.E x y = nf₂.E x y) :
    nf₁.A = nf₂.A ∧ nf₁.B = nf₂.B ∧ nf₁.T = nf₂.T :=
  normalForm_unique fun x y hx hy => (h₁ x y hx hy).symm.trans (h₂ x y hx hy)

end Selection
