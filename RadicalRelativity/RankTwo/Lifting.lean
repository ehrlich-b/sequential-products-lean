/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.OneParameter
import RadicalRelativity.MasterTheorem.Globalization

set_option linter.style.longLine false

/-!
# The rank-two lifting step  (LEDGER 5.1, `prop:n2-necessity`)

The rank-two boundary needs: *a continuous character of `ℝⁿ` into the rotation
group lifts to a linear functional*.  In the paper this is the covering-space
lift `ℝ² → SO(2)`, `SO(2) ≅ ℝ/2πℤ`.

Here it is a **corollary of `multiParameter_eq_exp`** (LEDGER 2.7's engine,
proved from scratch for the Aczél discharge): a continuous homomorphism from a
real vector space into the units of a real Banach algebra is `r ↦ exp (D r)` for
a *unique* linear `D`.  No covering-space machinery, no `2π` bookkeeping — the
generator is linear on the nose, which is exactly the "lifts to a linear
functional" conclusion.

* `character_eq_exp_linear` — the general statement over a real Banach algebra.
* `circleCharacter_linear_functional` — the rank-two instance: a continuous
  character into the rotation group is `exp (i φ)` for a real-linear `φ`.
* `circleCharacter_functional_unique` — that `φ` is unique.
-/

noncomputable section

open NormedSpace

namespace RankTwo

/-! ## The general lift -/

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **The lifting step, general form.**  A continuous character of a real vector
space into a real Banach algebra is the exponential of a **unique linear**
generator.  This is the paper's "continuous hom lifts to a linear functional",
obtained from `multiParameter_eq_exp` rather than from covering spaces. -/
theorem character_eq_exp_linear {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : E → 𝔸) (hmul : ∀ r r' : E, χ (r + r') = χ r * χ r') (hone : χ 0 = 1)
    (hcont : ∀ v : E, Continuous fun t : ℝ => χ (t • v)) :
    ∃! D : E →ₗ[ℝ] 𝔸, ∀ r : E, χ r = exp (D r) :=
  Necessity.multiParameter_eq_exp χ hmul hone hcont

/-! ## The rank-two instance: characters into the rotation group -/

/-- **The rank-two lifting step** (`prop:n2-necessity`).  A continuous character
of a real vector space into the **rotation group** — realized as the unit circle
in `ℂ`, which is how `SO(2)` acts on a two-dimensional block — is
`r ↦ exp (i φ r)` for a **unique real-linear functional** `φ`.

This is the paper's "a continuous homomorphism `ℝ² → SO(2)` lifts to a linear
functional", with no covering-space machinery and no `2π` ambiguity: the
modulus-one condition forces the generator to be purely imaginary
(`‖exp z‖ = exp (re z)`), and its imaginary part is linear because the
generator is. -/
theorem circleCharacter_linear_functional {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : E → ℂ) (hmul : ∀ r r' : E, χ (r + r') = χ r * χ r') (hone : χ 0 = 1)
    (hcont : ∀ v : E, Continuous fun t : ℝ => χ (t • v))
    (hunit : ∀ r : E, ‖χ r‖ = 1) :
    ∃ φ : E →ₗ[ℝ] ℝ, ∀ r : E, χ r = Complex.exp (φ r * Complex.I) := by
  obtain ⟨D, hD, -⟩ := character_eq_exp_linear χ hmul hone hcont
  -- the modulus-one condition kills the real part of the generator
  have hre : ∀ r : E, (D r).re = 0 := by
    intro r
    have h1 : ‖Complex.exp (D r)‖ = 1 := by
      rw [Complex.exp_eq_exp_ℂ, ← hD r]
      exact hunit r
    rw [Complex.norm_exp] at h1
    have h2 : Real.exp ((D r).re) = Real.exp 0 := by rw [h1, Real.exp_zero]
    exact Real.exp_injective h2
  -- the imaginary part is a linear functional
  refine ⟨{ toFun := fun r => (D r).im
            map_add' := fun r r' => by rw [map_add]; exact Complex.add_im _ _
            map_smul' := fun c r => by
              rw [map_smul, RingHom.id_apply]
              exact Complex.smul_im _ _ }, ?_⟩
  intro r
  rw [hD r, Complex.exp_eq_exp_ℂ]
  congr 1
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hre r]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, LinearMap.coe_mk, AddHom.coe_mk]
    ring

/-- The functional of `circleCharacter_linear_functional` is unique: two
real-linear functionals whose imaginary exponentials agree are equal.  This is
the rigidity the rank-two assembly consumes. -/
theorem circleCharacter_functional_unique {E : Type*} [AddCommGroup E] [Module ℝ E]
    (χ : E → ℂ) (φ φ' : E →ₗ[ℝ] ℝ)
    (hφ : ∀ r : E, χ r = Complex.exp (φ r * Complex.I))
    (hφ' : ∀ r : E, χ r = Complex.exp (φ' r * Complex.I)) :
    φ = φ' := by
  apply LinearMap.ext
  intro r
  -- restrict to the line through `r` and use the character-uniqueness theorem
  have hline : ∀ x : ℝ, Complex.exp ((φ r : ℂ) * x * Complex.I)
      = Complex.exp ((φ' r : ℂ) * x * Complex.I) := by
    intro x
    have h1 := hφ (x • r)
    have h2 := hφ' (x • r)
    rw [map_smul] at h1 h2
    have heq : Complex.exp (((x • φ r : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((x • φ' r : ℝ) : ℂ) * Complex.I) := by
      rw [← h1, ← h2]
    have hcast : ∀ ψ : E →ₗ[ℝ] ℝ, ((x • ψ r : ℝ) : ℂ) * Complex.I
        = (ψ r : ℂ) * (x : ℂ) * Complex.I := by
      intro ψ
      rw [smul_eq_mul]
      push_cast
      ring
    rw [hcast φ, hcast φ'] at heq
    exact heq
  exact MasterTheorem.Globalization.real_character_unique
    (a := -1) (b := 1) (by norm_num) (fun x _ => hline x)

end RankTwo
