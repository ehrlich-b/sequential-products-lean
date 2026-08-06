/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockRotation

set_option linter.style.longLine false

/-!
# The block angle is the phase rate  (closing the ℂ lane's identification)

`chiEntry_is_rotation` gives the block action as `z ↦ e^{i c(r)} z` with
`c(r) = (gen r 1).im` for the abstract generator `gen`.  This file identifies
`c` with the phase rate `t_{ij}` of `PhaseAnchor`, closing the loop.

The identification needs **no new analysis**: both generators are the derivative
at `0` of the *same* real function `t ↦ chiEntry (t • r) i j z`, one via
`chiEntry = exp ∘ gen` and one via `χ̃ = exp ∘ dχ` read entrywise, so
`HasDerivAt.unique` equates them.

* `chiEntryGen_eq_dChiEntry` — the two generators agree.
* `chiEntry_rotation_tval` — **the block action in closed form**:
  `chiEntry r i j z = e^{i t_{ij}(r)} z`.
* `chiTilde_block_rotation` — the same at the `HermitianMat` level, i.e. exactly
  the hypothesis shape of `chiTilde_eq_adU_of_block`.
-/

noncomputable section

open ComplexOrder NormedSpace
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The two generators agree -/

/-- **The abstract generator is the entry map of `dχ`.**  Both are the derivative
at `0` of `t ↦ chiEntry (t • r) i j z`: the first because
`chiEntry (t • r) = exp (t • gen r)`, the second because
`χ̃(t • r) = exp (t • dχ r)` and the block entry is continuous linear. -/
theorem chiEntryGen_eq_dChiEntry (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) (z : ℂ) :
    (chiEntryGen P hS2 hjord hij r) z = dChiEntry P hS2 hjord r i j z := by
  -- the curve, and its two derivative computations at `0`
  have hcurve : ∀ t : ℝ, chiEntry P hS2 (t • r) i j z
      = exp (t • (chiEntryGen P hS2 hjord hij r)) z := by
    intro t
    have h := chiEntry_eq_exp_gen P hS2 hjord hij (t • r)
    rw [map_smul] at h
    have h2 := congrFun (congrArg (fun L : ℂ →L[ℝ] ℂ => (L : ℂ → ℂ)) h) z
    simp only at h2
    rw [← chiEntryCLM_apply P hS2 (t • r) i j z]
    exact h2
  have h1 : HasDerivAt (fun t : ℝ => chiEntry P hS2 (t • r) i j z)
      ((chiEntryGen P hS2 hjord hij r) z) 0 := by
    rw [show (fun t : ℝ => chiEntry P hS2 (t • r) i j z)
        = fun t : ℝ => exp (t • (chiEntryGen P hS2 hjord hij r)) z from funext hcurve]
    exact exp_apply_hasDerivAt_gen _ z
  have h2 : HasDerivAt (fun t : ℝ => chiEntry P hS2 (t • r) i j z)
      (dChiEntry P hS2 hjord r i j z) 0 := by
    have hexp : ∀ t : ℝ, chiEntry P hS2 (t • r) i j z
        = (exp (t • dChi P hS2 hjord r) (blockHerm i j z)).mat i j := by
      intro t
      rw [chiEntry_apply]
      congr 1
      rw [chiTilde_eq_exp_dChi P hS2 hjord (t • r), map_smul]
    rw [show (fun t : ℝ => chiEntry P hS2 (t • r) i j z)
        = fun t : ℝ => (exp (t • dChi P hS2 hjord r) (blockHerm i j z)).mat i j from
      funext hexp]
    have h := exp_entry_hasDerivAt (dChi P hS2 hjord r) (blockHerm i j z) i j
    rw [dChiEntry_apply]
    exact h
  exact h1.unique h2

/-! ## The block action in closed form -/

/-- **The block action of `χ̃` is the rotation by the phase rate**:
`chiEntry r i j z = e^{i t_{ij}(r)} z`.  Combines `chiEntry_is_rotation` with
`chiEntryGen_eq_dChiEntry` and the skew classification `dChiEntry_eq`. -/
theorem chiEntry_rotation_tval (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) (z : ℂ) :
    chiEntry P hS2 r i j z
      = Complex.exp (((tvalLm P hS2 hjord i j r : ℝ) : ℂ) * Complex.I) * z := by
  have hgen : ((chiEntryGen P hS2 hjord hij r) 1).im
      = tvalLm P hS2 hjord i j r := by
    rw [chiEntryGen_eq_dChiEntry P hS2 hjord hij r 1]
    rw [dChiEntry_eq P hS2 hjord r hij 1]
    simp only [mul_one, Complex.smul_im, Complex.I_im, smul_eq_mul, mul_one]
  rw [chiEntry_is_rotation P hS2 hjord hij r z, hgen]

/-- The same statement at the `HermitianMat` level — exactly the hypothesis shape
of `chiTilde_eq_adU_of_block`. -/
theorem chiTilde_block_rotation (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) (z : ℂ) :
    (chiTilde P hS2 r).val (blockHerm i j z)
      = blockHerm i j
        (Complex.exp (((tvalLm P hS2 hjord i j r : ℝ) : ℂ) * Complex.I) * z) := by
  rw [chiTilde_block_eq P hS2 hjord r hij z, chiEntry_rotation_tval P hS2 hjord hij r z]

/-! ## The identification fires -/

/-- **`Θ = Ad` on `H_N(ℂ)`, given the per-frame collapse of the phase rates.**
If the phase rates take the collapsed form `t_{ij}(r) = t (r_i − r_j)` — which is
what `complex_perFrame_unconditional` supplies — then the comparison character
**is** conjugation by the torus unitary:
`χ̃(r) = Ad_{U_t(r)}`.

This closes the complex lane's identification: everything else in the hypothesis
list of `chiTilde_eq_adU_of_block` is now discharged. -/
theorem chiTilde_eq_adU (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (t : ℝ) (r : n → ℝ)
    (hcollapse : ∀ i j : n, i ≠ j → tvalLm P hS2 hjord i j r = t * (r i - r j)) :
    ((chiTilde P hS2 r).val : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
      = HermitianMat.conjLinear ℝ (torusU t r) := by
  refine chiTilde_eq_adU_of_block P hS2 t r ?_
  intro i j hij z
  rw [chiTilde_block_rotation P hS2 hjord hij r z, hcollapse i j hij]

/-- **The product-level form.**  With the phase rates collapsed, the sequential
product on invertible effects is the twist conjugation through `Q_{√a}`.  This is
`mthm:master`'s complex shape, with the comparison map now *identified* rather
than merely certified as a Jordan automorphism. -/
theorem sp_eq_quadRep_torus {N : ℕ}
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {a : HermitianMat (Fin N) ℂ} (ha : OrderUnitSpace.IsEffect a)
    (hbd : a.mat.PosDef) (t : ℝ) (r : Fin N → ℝ)
    (hθ : ((theta P ha hbd : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ))
      = ((chiTilde P hS2 r).val : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ))
    (hcollapse : ∀ i j : Fin N, i ≠ j →
      tvalLm P hS2 hjord i j r = t * (r i - r j))
    {b : HermitianMat (Fin N) ℂ} (hb : OrderUnitSpace.IsEffect b) :
    P.sp a b = (adU (torusU t r) b).conj (a.cfc Real.sqrt).mat :=
  sp_eq_quadRep_adU P ha hbd t r
    (hθ.trans (chiTilde_eq_adU P hS2 hjord t r hcollapse)) hb

end Necessity
