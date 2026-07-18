/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Selection.NormalFormExistence
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.longLine false

/-!
# Selector equivalence (`thm:selector`) — interface-level legs

This file formalizes, at the twist-normal-form interface level, the block-local
content of Theorem `thm:selector` of Paper A ("Twist Normal Forms and Global
Rigidity for Peirce-Respecting Sequential Products").  On a single Peirce `1`-space
`W`, working with the `TwistNormalForm.NormalForm` data (`A, B, T = A − ½·Id`) and
the block action `E`, the theorem's selectors are:

* **(i)** every twist vanishes: `T = 0`;
* **(ii)** the product is the Lüders product: `E(x,y) = √(xy)·Id` on the block;
* **(iii)** Peirce exchange covariance: `E(x,y) = E(y,x)` (`NormalForm.Reciprocity`);
* **(iv)** trace-inner-product symmetry: the block action is self-adjoint,
  `⟨E(x,y) w, w'⟩ = ⟨w, E(x,y) w'⟩`;
* **(v)** covariance under every unital order automorphism.

## What is proved (0 custom axioms throughout)

**Core equivalence `(i) ⇔ (ii) ⇔ (iii)`** — `selector_core_tfae`, with the three
headline iffs.  This is the paper's *own* contribution ("what is ours ... is the
equivalence of the selectors with the vanishing of the normal-form twist — in
particular `T ≡ 0 ⇔ Peirce exchange covariance (iii)`", `rem:selector-attribution`).
It is entirely block-local and needs no Jordan/trace structure: `(iii)⇒(i)` reuses
`TwistNormalForm.NormalForm.T_eq_zero` (the reciprocity elimination), and the cycle
closes via the normal form `E(x,y) = √(xy)·exp((log x − log y)·T)`.

**Trace leg (iv)** — over an abstract real inner product on `W` (the trace form
restricted to the block), `traceSymmetric_iff_selfAdjoint_T` proves
`(iv) ⇔ IsSelfAdjoint T`, and `T_eq_zero_of_traceSymmetric_of_skew` closes
`(iv) ⇒ (i)` once the twist is *also* skew-adjoint.  Skew-adjointness is exactly
twist isotropy `T ∈ 𝔰𝔬(W)` (`prop:isotropy`), which is imported here as the
hypothesis `IsSkewAdjoint T` — see the faithfulness delta.

**Automorphism leg (v), analytic core** — `commute_T_of_commute_flow`: an operator
`O` commuting with the whole twist flow `exp(s·T)` commutes with the generator `T`.
This is the differentiation step of the paper's `(v)⇒(i)` ("`O e^{sT} = e^{sT} O`
for all `s`; differentiating, `O T O⁻¹ = T`").

## Deltas / what is *not* formalized here (honest)

* **`(v)` as an equivalence is not closed.**  The paper's `(i)–(iv) ⇒ (v)` needs
  that a unital order automorphism of an EJA is a Jordan automorphism intertwining
  the Lüders product (Alfsen–Shultz), and `(v) ⇒ (i)` needs the fixed-point
  criterion on `O(W)`-conjugation of `𝔰𝔬(W)` plus the transpose realization on
  `Mₙ(ℂ)ˢᵃ`.  Both live at the EJA/automorphism level, above this interface; only
  the analytic core (`commute_T_of_commute_flow`) is formalized.  This matches the
  attribution remark: leg (v) is published in greater generality (van de Wetering).
* **Twist isotropy is imported.**  `(iv) ⇒ (i)` and the full role of `𝔰𝔬(W)` need
  `prop:isotropy` (`T` skew-adjoint / `T ∈ 𝔰𝔬(W)`), which is *not* proved here (it
  is the cone/Jordan argument, a separate `(c)`-class target).  We take it as the
  named hypothesis `IsSkewAdjoint T` at the exact point of use, so the reader sees
  precisely where it enters.
* **(iv) inner product.**  The manuscript uses the EJA trace inner product; we
  abstract it as an arbitrary real `InnerProductSpace` structure on `W` (the trace
  form's restriction to the block), so the leg is stated one level below the EJA.

## References

* Ehrlich 2026, Paper A, Theorem (selector equivalence) and its attribution remark.
* van de Wetering 2018 (legs iv, v in greater generality); Gudder–Latrémolière 2008.
-/

noncomputable section

namespace Selection

open NormedSpace TwistNormalForm

/-! ## Core equivalence `(i) ⇔ (ii) ⇔ (iii)` (block-local, no trace structure) -/

section Core

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [CompleteSpace W] (nf : NormalForm W)

/-- Selector **(ii)**: the block action is the Lüders value, `E(x,y) = √(xy)·Id` on
every positive eigenvalue pair (`thm:selector` (ii); eq. (corrected-product) on the
block). -/
def IsLuders : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → nf.E x y = Real.sqrt (x * y) • (1 : W →L[ℝ] W)

/-- `(i) ⇒ (ii)`: a vanishing twist gives the Lüders block action.  Immediate from
the normal form `E(x,y) = √(xy)·exp((log x − log y)·T)` at `T = 0`. -/
theorem isLuders_of_T_eq_zero (hT : nf.T = 0) : IsLuders nf := by
  intro x y hx hy
  rw [nf.E_normalForm hx hy, hT, smul_zero, exp_zero]

omit [CompleteSpace W] in
/-- `(ii) ⇒ (iii)`: the Lüders block action is exchange-symmetric, since `√(xy)`
is symmetric in `x, y`.  (`thm:selector`, trivial leg.) -/
theorem reciprocity_of_isLuders (h : IsLuders nf) : nf.Reciprocity := by
  intro x y hx hy
  rw [h x y hx hy, h y x hy hx, mul_comm x y]

/-- **Core selector equivalence** `(i) ⇔ (ii) ⇔ (iii)` (`thm:selector`): the twist
vanishes iff the product is Lüders iff Peirce exchange covariance holds.  The cycle
is `(i)⇒(ii)` (`isLuders_of_T_eq_zero`), `(ii)⇒(iii)` (`reciprocity_of_isLuders`),
`(iii)⇒(i)` (`NormalForm.T_eq_zero`, the reciprocity elimination of
`prop:coherence`).  This is the paper's claimed contribution to `thm:selector`. -/
theorem selector_core_tfae :
    [nf.T = 0, IsLuders nf, nf.Reciprocity].TFAE := by
  tfae_have 1 → 2 := isLuders_of_T_eq_zero nf
  tfae_have 2 → 3 := reciprocity_of_isLuders nf
  tfae_have 3 → 1 := nf.T_eq_zero
  tfae_finish

/-- `T = 0 ⇔` Lüders block action (`thm:selector` (i) ⇔ (ii)). -/
theorem T_eq_zero_iff_isLuders : nf.T = 0 ↔ IsLuders nf :=
  (selector_core_tfae nf).out 0 1

/-- `T = 0 ⇔` Peirce exchange covariance (`thm:selector` (i) ⇔ (iii)) — the paper's
headline `T ≡ 0 ⇔` exchange covariance. -/
theorem T_eq_zero_iff_reciprocity : nf.T = 0 ↔ nf.Reciprocity :=
  (selector_core_tfae nf).out 0 2

/-- Lüders block action `⇔` Peirce exchange covariance (`thm:selector` (ii) ⇔ (iii)). -/
theorem isLuders_iff_reciprocity : IsLuders nf ↔ nf.Reciprocity :=
  (selector_core_tfae nf).out 1 2

end Core

/-! ## Automorphism leg `(v)`, analytic core -/

section AutomorphismCovariance

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [CompleteSpace W] (nf : NormalForm W)

/-- **`thm:selector` (v)⇒(i), differentiation step.**  If an operator `O` commutes
with the entire twist flow `exp(s·T)` (as it does when `O` realizes a unital order
automorphism fixing the block's atoms and commuting with `E(a,·)`), then it commutes
with the generator `T`: the paper's "`O e^{sT} = e^{sT} O` for all `s`;
differentiating, `O T O⁻¹ = T`".  The remaining "no nonzero fixed point in `𝔰𝔬(W)`
⇒ `T = 0`" step, and the transpose realization, are above this interface (see the
module docstring). -/
theorem commute_T_of_commute_flow (O : W →L[ℝ] W)
    (hO : ∀ s : ℝ, O * exp (s • nf.T) = exp (s • nf.T) * O) :
    O * nf.T = nf.T * O := by
  have hExpT : HasDerivAt (fun s : ℝ => exp (s • nf.T)) nf.T 0 := by
    simpa [exp_zero] using hasDerivAt_exp_smul_const nf.T (0 : ℝ)
  have h1 : HasDerivAt (fun s : ℝ => O * exp (s • nf.T)) (O * nf.T) 0 := by
    simpa using hExpT.const_mul O
  have h2 : HasDerivAt (fun s : ℝ => O * exp (s • nf.T)) (nf.T * O) 0 := by
    rw [funext hO]
    simpa using hExpT.mul_const O
  exact h1.unique h2

/-- Conjugation form of `commute_T_of_commute_flow`: for invertible `O` commuting
with the twist flow, `O T O⁻¹ = T` (`thm:selector` (v)⇒(i)). -/
theorem conj_T_eq_of_commute_flow (O : (W →L[ℝ] W)ˣ)
    (hO : ∀ s : ℝ, (O : W →L[ℝ] W) * exp (s • nf.T) = exp (s • nf.T) * O) :
    (O : W →L[ℝ] W) * nf.T * (↑O⁻¹) = nf.T := by
  rw [commute_T_of_commute_flow nf O hO, mul_assoc, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, mul_one]

end AutomorphismCovariance

/-! ## Trace leg `(iv)`: symmetry for the trace inner product

Over an abstract real inner product on `W` — the EJA trace form restricted to the
block — the sequential product's trace symmetry `⟨a·b,c⟩ = ⟨b,a·c⟩` becomes, on the
block, self-adjointness of `E(x,y)`.  The `star` operation on `W →L[ℝ] W` is the
adjoint (`ContinuousLinearMap.star_eq_adjoint`), so `IsSelfAdjoint (E x y)` is
exactly `⟨E(x,y) w, w'⟩ = ⟨w, E(x,y) w'⟩`. -/

section TraceSymmetry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [CompleteSpace W] (nf : NormalForm W)

/-- Selector **(iv)**: the block action is self-adjoint for the trace inner product,
`⟨E(x,y) w, w'⟩ = ⟨w, E(x,y) w'⟩` (`thm:selector` (iv)). -/
def TraceSymmetric : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y → IsSelfAdjoint (nf.E x y)

/-- **`thm:selector` (iv) ⇔ `A` self-adjoint at the generator level.**  Trace
symmetry of the block action is equivalent to self-adjointness of the twist normal
form's `x`-generator `A`; via `T = A − ½·Id` this is self-adjointness of `T`.  Both
directions run through `star_exp` and differentiation at the identity, the
operator-level form of the paper's "each `e^{sT}` self-adjoint, hence `T` is". -/
theorem traceSymmetric_iff_selfAdjoint_T :
    TraceSymmetric nf ↔ IsSelfAdjoint nf.T := by
  constructor
  · -- (iv) ⇒ IsSelfAdjoint A ⇒ IsSelfAdjoint T
    intro hTS
    have hAsa : IsSelfAdjoint nf.A := by
      have hsub : ∀ s : ℝ, exp (s • star nf.A) = exp (s • nf.A) := by
        intro s
        have hE : IsSelfAdjoint (nf.E (Real.exp s) 1) :=
          hTS (Real.exp s) 1 (Real.exp_pos s) one_pos
        rw [NormalForm.E_right_one, Real.log_exp] at hE
        have hst : star (exp (s • nf.A)) = exp (s • nf.A) := hE
        rwa [star_exp, star_smul, star_trivial] at hst
      have h1 : HasDerivAt (fun s : ℝ => exp (s • star nf.A)) (star nf.A) 0 := by
        simpa [exp_zero] using hasDerivAt_exp_smul_const (star nf.A) (0 : ℝ)
      have h2 : HasDerivAt (fun s : ℝ => exp (s • star nf.A)) nf.A 0 := by
        rw [funext hsub]
        simpa [exp_zero] using hasDerivAt_exp_smul_const nf.A (0 : ℝ)
      exact h1.unique h2
    have hHalf : IsSelfAdjoint ((2⁻¹ : ℝ) • (1 : W →L[ℝ] W)) := by
      change star ((2⁻¹ : ℝ) • (1 : W →L[ℝ] W)) = (2⁻¹ : ℝ) • 1
      rw [star_smul, star_trivial, star_one]
    change IsSelfAdjoint (nf.A - (2⁻¹ : ℝ) • 1)
    exact hAsa.sub hHalf
  · -- IsSelfAdjoint T ⇒ (iv)
    intro hTsa x y hx hy
    rw [nf.E_normalForm hx hy]
    have hs : IsSelfAdjoint ((Real.log x - Real.log y) • nf.T) :=
      (IsSelfAdjoint.all _).smul hTsa
    exact (IsSelfAdjoint.all _).smul hs.exp

/-- `(i) ⇒ (iv)`: a vanishing twist gives a trace-symmetric block action. -/
theorem traceSymmetric_of_T_eq_zero (hT : nf.T = 0) : TraceSymmetric nf :=
  (traceSymmetric_iff_selfAdjoint_T nf).mpr (by rw [hT]; exact IsSelfAdjoint.zero _)

/-- **`thm:selector` (iv) ⇒ (i), under imported isotropy.**  Trace symmetry forces
the twist to vanish *once the twist is also skew-adjoint* — `T ∈ 𝔰𝔬(W)`, i.e. twist
isotropy `prop:isotropy`, taken here as the hypothesis `star T = -T` (membership in
`skewAdjoint`; Mathlib has no `IsSkewAdjoint` predicate).  A twist that is both
self-adjoint (from (iv)) and skew-adjoint is zero.  This is the paper's "`T`
self-adjoint; by twist isotropy `T` is also skew-adjoint; so `T = 0`." -/
theorem T_eq_zero_of_traceSymmetric_of_skew
    (hTS : TraceSymmetric nf) (hskew : star nf.T = -nf.T) : nf.T = 0 := by
  have hsa : star nf.T = nf.T := (traceSymmetric_iff_selfAdjoint_T nf).mp hTS
  have hTT : nf.T = - nf.T := hsa.symm.trans hskew
  have h2 : (2 : ℝ) • nf.T = 0 := by
    rw [two_smul]; nth_rewrite 2 [hTT]; exact add_neg_cancel nf.T
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end TraceSymmetry

end Selection
