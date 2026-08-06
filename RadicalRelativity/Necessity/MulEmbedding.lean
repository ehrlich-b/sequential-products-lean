/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockCharacter

set_option linter.style.longLine false

/-!
# `ℂ` inside its own `ℝ`-linear endomorphisms, and `exp`  (closing the ℂ lane)

The last step of the complex lane needs: **the exponential of "multiplication by
`w`" is "multiplication by `exp w`"**.  That is `NormedSpace.map_exp` along the
ring embedding of `ℂ` into `ℂ →L[ℝ] ℂ` sending `w` to multiplication by `w`.

* `mulBy : ℂ →+* (ℂ →L[ℝ] ℂ)` — the embedding, with `mulBy_apply`.
* `mulBy_continuous` — it is continuous (it is `ℝ`-linear between finite
  -dimensional spaces).
* `exp_mulBy` — **`exp (mulBy w) = mulBy (exp w)`**.
* `exp_mulBy_I` — the case the identification uses: `exp (mulBy (c·i))` is
  multiplication by `e^{ic}`, i.e. rotation by `c`.

With `skew_linear_eq_I_smul` (a skew `ℝ`-linear map of `ℂ` is `mulBy (i·t)`)
this converts the *generator* statement of `complex_perFrame_unconditional` into
the *group-level* block action that `chiTilde_eq_adU_of_block` consumes.
-/

noncomputable section

open NormedSpace

namespace Necessity

/-! ## The embedding -/

/-- Multiplication by a complex number, as an `ℝ`-linear continuous map. -/
def mulByCLM (w : ℂ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => w * z
      map_add' := fun z z' => by ring
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, Complex.real_smul]
        ring }

@[simp]
theorem mulByCLM_apply (w z : ℂ) : mulByCLM w z = w * z := rfl

/-- The embedding `ℂ →+* (ℂ →L[ℝ] ℂ)`. -/
def mulBy : ℂ →+* (ℂ →L[ℝ] ℂ) where
  toFun := mulByCLM
  map_one' := by
    ext z
    simp only [mulByCLM_apply, one_mul]
    rfl
  map_mul' w w' := by
    ext z
    simp only [mulByCLM_apply]
    show w * w' * z = w * (w' * z)
    ring
  map_zero' := by
    ext z
    simp only [mulByCLM_apply, zero_mul]
    rfl
  map_add' w w' := by
    ext z
    simp only [mulByCLM_apply]
    show (w + w') * z = w * z + w' * z
    ring

@[simp]
theorem mulBy_apply (w z : ℂ) : mulBy w z = w * z := rfl

/-- The embedding is continuous (an `ℝ`-linear map between finite-dimensional
spaces). -/
theorem mulBy_continuous : Continuous (mulBy : ℂ → (ℂ →L[ℝ] ℂ)) := by
  have hlin : IsLinearMap ℝ (mulBy : ℂ → (ℂ →L[ℝ] ℂ)) := by
    constructor
    · intro w w'
      exact map_add mulBy w w'
    · intro c w
      ext z
      simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, mulBy_apply,
        Complex.real_smul]
      ring
  exact (hlin.mk' _).continuous_of_finiteDimensional

/-! ## `exp` transfers -/

/-- **`exp` of a multiplication is the multiplication by `exp`.** -/
theorem exp_mulBy (w : ℂ) : exp (mulBy w) = mulBy (Complex.exp w) := by
  have h := NormedSpace.map_exp mulBy mulBy_continuous w
  rw [Complex.exp_eq_exp_ℂ]
  exact h.symm

/-- The case the twist identification uses: the exponential of the skew map
`z ↦ (c i) z` is the rotation `z ↦ e^{ic} z`. -/
theorem exp_mulBy_I (c : ℝ) (z : ℂ) :
    exp (mulBy ((c : ℂ) * Complex.I)) z
      = Complex.exp ((c : ℂ) * Complex.I) * z := by
  rw [exp_mulBy]
  rfl

/-- Packaged for the block action: if a one-parameter family's generator is the
skew map `mulBy (i·θ)`, the family member is the rotation by `θ`. -/
theorem exp_generator_is_rotation (θ : ℝ) :
    exp (mulBy ((θ : ℂ) * Complex.I)) = mulByCLM (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [exp_mulBy]
  rfl

end Necessity
