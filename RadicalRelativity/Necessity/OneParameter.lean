/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option linter.style.longLine false

/-!
# Continuous one-parameter semigroups in a Banach algebra are exponentials
(campaign LEDGER 2.7, core lemma for the Aczél discharge)

`oneParameter_eq_exp`: a continuous `g : ℝ → 𝔸` into a real Banach algebra with
`g (s+t) = g s * g t` and `g 0 = 1` equals `t ↦ exp (t • A)` for a unique `A`.

Mathlib has no one-parameter-group theory (inventory-confirmed), so this is the
classical integral-regularization argument built from scratch:

1. Pick `d > 0` with `‖g s − 1‖ ≤ 1/2` on `[0, d]`; then `J := ∫ s in 0..d, g s`
   deviates from `d•1` by at most `d/2`, so `d⁻¹ • J` is a geometric-series unit
   (`Units.oneSub`).
2. The semigroup law gives `g t * J = ∫ s in t..t+d, g = F (t+d) − F t` for the
   primitive `F`; FTC-2 makes the right side differentiable in `t`, hence `g` is
   differentiable with the closed-form derivative `(g (t+d) − g t) * J⁻¹`.
3. Differentiating the semigroup law at `0` gives `g' t = g t * A` with
   `A := g' 0`.
4. `t ↦ g t * exp (t • (−A))` has vanishing derivative, hence is constantly
   `g 0 = 1`, so `g t = exp (t • A)`.
5. Uniqueness: differentiate at `0`.

The Aczél wrapper (LEDGER 2.7 proper) substitutes `g t := h (Real.exp t)` and
swaps the `Selection.aczel_continuous_multiplicative` axiom for a theorem.
-/

noncomputable section

open NormedSpace intervalIntegral MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

namespace Necessity

/-- Vanishing derivative on ℝ forces constancy (fderiv form specialized). -/
theorem const_of_hasDerivAt_zero {φ : ℝ → 𝔸} (hφ : ∀ t, HasDerivAt φ 0 t) (t : ℝ) :
    φ t = φ 0 := by
  apply is_const_of_fderiv_eq_zero (𝕜 := ℝ) (fun x => (hφ x).differentiableAt)
  intro x
  have h := (hφ x).hasFDerivAt.fderiv
  rw [h]
  exact ContinuousLinearMap.ext fun v => by simp

/-- **Continuous one-parameter semigroups are exponentials.** -/
theorem oneParameter_eq_exp (g : ℝ → 𝔸) (hcont : Continuous g)
    (hmul : ∀ s t : ℝ, g (s + t) = g s * g t) (hone : g 0 = 1) :
    ∃! A : 𝔸, ∀ t : ℝ, g t = exp (t • A) := by
  classical
  -- ## Step 1: the regularizing integral and its inverse
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ s : ℝ, |s| < δ → ‖g s - 1‖ < 1 / 2 := by
    have h0 : ContinuousAt g 0 := hcont.continuousAt
    rw [Metric.continuousAt_iff] at h0
    obtain ⟨δ, hδpos, hδ⟩ := h0 (1 / 2) (by norm_num)
    refine ⟨δ, hδpos, fun s hs => ?_⟩
    have := hδ (x := s) (by simpa [Real.dist_eq] using hs)
    simpa [dist_eq_norm, hone] using this
  set d : ℝ := δ / 2 with hd
  have hdpos : 0 < d := by positivity
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) d, ‖g s - 1‖ ≤ 1 / 2 := by
    intro s hs
    rw [Set.uIoc_of_le (le_of_lt hdpos)] at hs
    have habs : |s| < δ := by
      rw [abs_lt]
      refine ⟨by linarith [hs.1], ?_⟩
      have h2 := hs.2
      rw [hd] at h2
      linarith
    exact le_of_lt (hδ s habs)
  set J : 𝔸 := ∫ s in (0 : ℝ)..d, g s with hJ
  have hJdev : ‖J - d • 1‖ ≤ d / 2 := by
    have hgi : IntervalIntegrable g volume 0 d := hcont.intervalIntegrable _ _
    have hsub : J - d • 1 = ∫ s in (0 : ℝ)..d, (g s - 1) := by
      rw [hJ, intervalIntegral.integral_sub hgi intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp
    rw [hsub]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (C := 1 / 2) (f := fun s => g s - 1) (a := (0 : ℝ)) (b := d) hbound
    calc ‖∫ s in (0:ℝ)..d, (g s - 1)‖ ≤ 1 / 2 * |d - 0| := h
      _ = d / 2 := by rw [sub_zero, abs_of_pos hdpos]; ring
  have htnorm : ‖(1 : 𝔸) - d⁻¹ • J‖ < 1 := by
    have h1 : (1 : 𝔸) - d⁻¹ • J = d⁻¹ • (d • 1 - J) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hdpos), one_smul]
    rw [h1, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hdpos]
    have h2 : ‖d • (1 : 𝔸) - J‖ ≤ d / 2 := by
      rw [← norm_neg]
      simpa using hJdev
    calc d⁻¹ * ‖d • (1:𝔸) - J‖ ≤ d⁻¹ * (d / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  set u : 𝔸ˣ := Units.oneSub ((1 : 𝔸) - d⁻¹ • J) htnorm with hu
  have huval : (u : 𝔸) = d⁻¹ • J := by
    rw [hu, Units.val_oneSub, sub_sub_cancel]
  set Jinv : 𝔸 := d⁻¹ • (↑u⁻¹ : 𝔸) with hJinv
  have hJu : J = d • (u : 𝔸) := by
    rw [huval, smul_smul, mul_inv_cancel₀ (ne_of_gt hdpos), one_smul]
  have hJJinv : J * Jinv = 1 := by
    rw [hJu, hJinv, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hdpos), one_smul, u.mul_inv]
  -- ## Step 2: the translation identity and differentiability of g
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
    hcont.intervalIntegrable a b
  set F : ℝ → 𝔸 := fun t => ∫ s in (0 : ℝ)..t, g s with hF
  have htrans : ∀ t : ℝ, g t * J = F (t + d) - F t := by
    intro t
    have h1 : g t * J = ∫ s in (0 : ℝ)..d, g t * g s := by
      rw [hJ]
      exact ((ContinuousLinearMap.mul ℝ 𝔸 (g t)).intervalIntegral_comp_comm (hgi 0 d)).symm
    have h2 : (∫ s in (0 : ℝ)..d, g t * g s) = ∫ s in (0 : ℝ)..d, g (t + s) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact (hmul t s).symm
    have h3 : (∫ s in (0 : ℝ)..d, g (t + s)) = ∫ s in t..(t + d), g s := by
      have := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := d) (f := g) t
      simpa using this
    have h4 : F t + ∫ s in t..(t + d), g s = F (t + d) :=
      intervalIntegral.integral_add_adjacent_intervals (hgi 0 t) (hgi t (t + d))
    rw [h1, h2, h3]
    exact eq_sub_of_add_eq' h4
  -- the primitive is differentiable with derivative g (FTC-2)
  have hFd : ∀ t : ℝ, HasDerivAt F (g t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hgi 0 t)
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hgrep : ∀ t : ℝ, g t = (F (t + d) - F t) * Jinv := by
    intro t
    calc g t = g t * 1 := (mul_one _).symm
      _ = g t * (J * Jinv) := by rw [hJJinv]
      _ = (g t * J) * Jinv := (mul_assoc _ _ _).symm
      _ = (F (t + d) - F t) * Jinv := by rw [htrans t]
  have hg' : ∀ t : ℝ, HasDerivAt g ((g (t + d) - g t) * Jinv) t := by
    intro t
    have hshift : HasDerivAt (fun t : ℝ => F (t + d)) (g (t + d)) t := by
      have hinner : HasDerivAt (fun t : ℝ => t + d) 1 t := (hasDerivAt_id t).add_const d
      have := (hFd (t + d)).scomp t hinner
      simpa using this
    have hrepr : HasDerivAt (fun t => (F (t + d) - F t) * Jinv)
        ((g (t + d) - g t) * Jinv) t :=
      ((hshift.sub (hFd t)).mul_const Jinv)
    exact hrepr.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => (hgrep s))
  -- ## Step 3: the multiplicative derivative law
  have hA0' := hg' 0
  rw [zero_add, hone] at hA0'
  obtain ⟨A, hA0⟩ : ∃ A : 𝔸, HasDerivAt g A 0 := ⟨_, hA0'⟩
  have hmulderiv : ∀ t : ℝ, HasDerivAt g (g t * A) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => g t * g s) (g t * A) 0 := hA0.const_mul (g t)
    have h2 : (fun s : ℝ => g (t + s)) = fun s : ℝ => g t * g s :=
      funext fun s => hmul t s
    have h3 : HasDerivAt (fun s : ℝ => g (t + s)) (g t * A) 0 := h2 ▸ h1
    have h4 : HasDerivAt (fun s : ℝ => g (t + s)) ((g (t + d) - g t) * Jinv) 0 := by
      have hinner : HasDerivAt (fun s : ℝ => t + s) 1 0 := (hasDerivAt_id 0).const_add t
      have := (hg' (t + 0)).scomp 0 hinner
      simpa using this
    have heq : (g (t + d) - g t) * Jinv = g t * A := h4.unique h3
    exact heq ▸ hg' t
  -- ## Step 4: the ODE kill
  have hAcomm : ∀ t : ℝ, A * exp (t • (-A)) = exp (t • (-A)) * A := by
    intro t
    have h1 : Commute A (t • (-A)) := ((Commute.refl A).neg_right).smul_right t
    exact (h1.exp_right).eq
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => g t * exp (t • (-A))) 0 t := by
    intro t
    have hexp : HasDerivAt (fun t : ℝ => exp (t • (-A)))
        (exp (t • (-A)) * (-A)) t := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    have h := (hmulderiv t).mul hexp
    have hzero : g t * A * exp (t • (-A)) + g t * (exp (t • (-A)) * (-A)) = 0 := by
      rw [mul_assoc, mul_neg, mul_neg, ← hAcomm t]
      exact add_neg_cancel _
    rw [hzero] at h
    exact h
  have hconst : ∀ t : ℝ, g t * exp (t • (-A)) = 1 := by
    intro t
    have h := const_of_hasDerivAt_zero hφ t
    simpa [hone] using h
  have hgA : ∀ t : ℝ, g t = exp (t • A) := by
    intro t
    have hEE : exp (t • (-A)) * exp (t • A) = 1 := by
      have hc : Commute (t • (-A)) (t • A) :=
        (((Commute.refl A).neg_left).smul_left t).smul_right t
      have hadd : exp ((t • (-A)) + t • A) = exp (t • (-A)) * exp (t • A) :=
        exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
          ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
          ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
      rw [← hadd]
      simp
    calc g t = g t * 1 := (mul_one _).symm
      _ = g t * (exp (t • (-A)) * exp (t • A)) := by rw [hEE]
      _ = (g t * exp (t • (-A))) * exp (t • A) := (mul_assoc _ _ _).symm
      _ = exp (t • A) := by rw [hconst t, one_mul]
  -- ## Step 5: uniqueness
  refine ⟨A, hgA, ?_⟩
  intro B hB
  have hdB : HasDerivAt g B 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0
    have hfun : (fun u : ℝ => exp (u • B)) = g := (funext hB).symm
    rw [hfun] at h
    simpa using h
  exact hdB.unique hA0

/-- **The multiplicative Aczél classification** (paper Lemma "Multiplicative
representation"): a continuous multiplicative unital family on `(0, ∞)` of
operators on a finite-dimensional real space is `x ↦ exp (log x • A)` for a
unique generator.  This DISCHARGES the campaign's last custom axiom
(`Selection.aczel_continuous_multiplicative` aliases to this theorem). -/
theorem aczel_multiplicative_classification
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W]
    (h : ℝ → (W →L[ℝ] W))
    (hcont : ContinuousOn h (Set.Ioi 0))
    (hmul : ∀ x, 0 < x → ∀ y, 0 < y → h (x * y) = h x * h y)
    (hone : h 1 = 1) :
    ∃! A : W →L[ℝ] W, ∀ x, 0 < x → h x = exp (Real.log x • A) := by
  have hgcont : Continuous fun t : ℝ => h (Real.exp t) :=
    hcont.comp_continuous Real.continuous_exp fun t => Real.exp_pos t
  have hgmul : ∀ s t : ℝ, h (Real.exp (s + t)) = h (Real.exp s) * h (Real.exp t) := by
    intro s t
    rw [Real.exp_add]
    exact hmul _ (Real.exp_pos s) _ (Real.exp_pos t)
  have hgone : h (Real.exp 0) = 1 := by rw [Real.exp_zero]; exact hone
  obtain ⟨A, hA, hAuniq⟩ :=
    oneParameter_eq_exp (fun t => h (Real.exp t)) hgcont hgmul hgone
  refine ⟨A, ?_, ?_⟩
  · intro x hx
    have hlog := hA (Real.log x)
    rwa [Real.exp_log hx] at hlog
  · intro B hB
    apply hAuniq
    intro t
    have hexp := hB (Real.exp t) (Real.exp_pos t)
    rwa [Real.log_exp] at hexp

/-! ## Multi-parameter families: the differential of a character
(campaign LEDGER 2.6, the analytic core)

For a multiplicative family on `ℝⁿ` that is continuous along lines, the
line-generators from `oneParameter_eq_exp` are automatically ℝ-homogeneous and
additive BY UNIQUENESS, hence assemble into a linear differential — Cartan
smoothness costs nothing once the one-parameter theorem exists. -/

/-- Commuting exponential flows have commuting generators (differentiate twice). -/
theorem commute_of_commute_exp {A B : 𝔸}
    (h : ∀ s t : ℝ, Commute (exp (t • A)) (exp (s • B))) : Commute A B := by
  have h1 : ∀ s : ℝ, A * exp (s • B) = exp (s • B) * A := by
    intro s
    have hd1 : HasDerivAt (fun t : ℝ => exp (t • A) * exp (s • B))
        (A * exp (s • B)) 0 := by
      have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0).mul_const (exp (s • B))
      simpa using this
    have hd2 : HasDerivAt (fun t : ℝ => exp (t • A) * exp (s • B))
        (exp (s • B) * A) 0 := by
      have hfun : (fun t : ℝ => exp (s • B) * exp (t • A))
          = fun t : ℝ => exp (t • A) * exp (s • B) :=
        funext fun t => ((h s t).symm).eq
      have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0).const_mul (exp (s • B))
      rw [hfun] at this
      simpa using this
    exact hd1.unique hd2
  have hd1 : HasDerivAt (fun s : ℝ => A * exp (s • B)) (A * B) 0 := by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0).const_mul A
    simpa using this
  have hd2 : HasDerivAt (fun s : ℝ => A * exp (s • B)) (B * A) 0 := by
    have hfun : (fun s : ℝ => exp (s • B) * A) = fun s : ℝ => A * exp (s • B) :=
      funext fun s => (h1 s).symm
    have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) B 0).mul_const A
    rw [hfun] at this
    simpa using this
  exact hd1.unique hd2

/-- **The differential of a multiplicative family** (LEDGER 2.6 core): a family on
`ℝⁿ` (any real normed source works) with `χ (r + r') = χ r * χ r'`, `χ 0 = 1`, and
continuity along lines is `r ↦ exp (D r)` for a unique LINEAR `D` — additivity and
homogeneity of the generator map come from the uniqueness clause of
`oneParameter_eq_exp`, so no Cartan-smoothness input is needed. -/
theorem multiParameter_eq_exp {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : E → 𝔸)
    (hmul : ∀ r r' : E, χ (r + r') = χ r * χ r')
    (hone : χ 0 = 1)
    (hcont : ∀ v : E, Continuous fun t : ℝ => χ (t • v)) :
    ∃! D : E →ₗ[ℝ] 𝔸, ∀ r : E, χ r = exp (D r) := by
  classical
  -- the line semigroups and their unique generators
  have hline : ∀ v : E, ∃! A : 𝔸, ∀ t : ℝ, χ (t • v) = exp (t • A) := by
    intro v
    have hgmul : ∀ s t : ℝ, χ ((s + t) • v) = χ (s • v) * χ (t • v) := by
      intro s t
      rw [add_smul]
      exact hmul _ _
    have hgone : χ ((0 : ℝ) • v) = 1 := by rw [zero_smul]; exact hone
    exact oneParameter_eq_exp (fun t : ℝ => χ (t • v)) (hcont v) hgmul hgone
  choose A hA hAuniq using hline
  -- χ-values commute, hence the generators commute
  have hχcomm : ∀ r r' : E, Commute (χ r) (χ r') := by
    intro r r'
    have h1 := hmul r r'
    have h2 := hmul r' r
    rw [add_comm] at h2
    exact (h1.symm.trans h2)
  have hgen_comm : ∀ v w : E, Commute (A v) (A w) := by
    intro v w
    apply commute_of_commute_exp
    intro s t
    rw [← hA v t, ← hA w s]
    exact hχcomm _ _
  -- homogeneity by uniqueness
  have hsmul : ∀ (c : ℝ) (v : E), A (c • v) = c • A v := by
    intro c v
    refine (hAuniq (c • v) (c • A v) ?_).symm
    intro t
    rw [smul_smul, hA v (t * c), mul_smul]
  -- additivity by uniqueness (through commuting exponentials)
  have hadd : ∀ v w : E, A (v + w) = A v + A w := by
    intro v w
    refine (hAuniq (v + w) (A v + A w) ?_).symm
    intro t
    have hc : Commute (t • A v) (t • A w) := ((hgen_comm v w).smul_left t).smul_right t
    have hexp : exp ((t • A v) + (t • A w)) = exp (t • A v) * exp (t • A w) :=
      exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hc
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
        ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    rw [smul_add, hmul, hA v t, hA w t, ← hexp, ← smul_add]
  -- assemble the linear differential
  refine ⟨{ toFun := A, map_add' := hadd,
            map_smul' := by intro c v; simpa using hsmul c v }, ?_, ?_⟩
  · intro r
    have h1 := hA r 1
    rw [one_smul, one_smul] at h1
    exact h1
  · intro D' hD'
    apply LinearMap.ext
    intro v
    exact hAuniq v (D' v) fun t => by
      have h := hD' (t • v)
      rwa [map_smul] at h

end Necessity
