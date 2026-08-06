/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.PhaseAnchor

set_option linter.style.longLine false

/-!
# Reading the phase rate off the coupling  (ℂ lane, the last bookkeeping link)

`complex_perFrame_unconditional` (and hence `frameTwist_spec`) states the
per-frame result in the *abstract* interface currency: the block representation
of the differential is a multiple of the rotation generator,
`ρ_{ij}(dχ(r)) = (c(r_i − r_j)) • J`.  The identification lane
(`chiTilde_eq_adU`, `sp_eq_twistSeq_diagFamily`) consumes the *concrete* phase
rate `tvalLm`.  This file is the one-line-of-linear-algebra bridge between them:

* `tvalLm_of_coupling` — evaluate the coupling equation at the block vector
  `z = 1` and read the second coordinate.  The left side is
  `(0, t_{ij}(r))` (the entry of `dχ(r)` on `blockHerm i j 1` is
  `t_{ij}(r) · i` by `dChiEntry_eq`), the right side is `(0, c(r_i − r_j))`
  (because `J(1,0) = (0,1)`), so `t_{ij}(r) = c(r_i − r_j)`.

With this, the per-frame parameter produced by the abstract branch lane *is* the
rate the concrete identification needs, and the `hcollapse` hypothesis of
`sp_eq_twistSeq_diagFamily` is discharged from `frameTwist_spec`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace MasterTheorem

namespace Necessity

/-- **The abstract per-frame parameter is the concrete phase rate.**  If the
produced coupling of `P` has the torus form with constant `c`, then `P`'s block
phase rates are `t_{ij}(r) = c(r_i − r_j)`. -/
theorem tvalLm_of_coupling {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) (c : ℝ)
    (hcoup : ∀ (i j : Fin N) (r : Fin N → ℝ),
      (stabilizerCoupling hN P hS2 hjord).ρ i j
          ((stabilizerCoupling hN P hS2 hjord).dχ r)
        = (c * (r i - r j)) • rotJ)
    {i j : Fin N} (hij : i ≠ j) (r : Fin N → ℝ) :
    tvalLm P hS2 hjord i j r = c * (r i - r j) := by
  have h := hcoup i j r
  rw [stabilizerCoupling_rho_dChi hN P hS2 hjord i j r] at h
  -- evaluate at the block vector `z = 1`
  set x : BlockV := (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm (1, 0) with hx
  have hxe : (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)) x = ((1 : ℝ), (0 : ℝ)) := by
    rw [hx, LinearEquiv.apply_symm_apply]
  have hval := congrArg
    (fun L : BlockV →ₗ[ℝ] BlockV => (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)) (L x)) h
  simp only at hval
  -- the left side: block coordinates of `dχ(r)` on `blockHerm i j 1`
  rw [rhoFieldL2_apply, LinearEquiv.apply_symm_apply,
    rhoField_apply_of_ne (n := Fin N) hij, hxe] at hval
  rw [blockEmbedLm_apply, blockCoordLm_apply] at hval
  have hentry : ((dChiStab P hS2 hjord r).val
        (blockHerm i j (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))).mat i j
      = (tvalLm P hS2 hjord i j r) • (Complex.I * (1 : ℂ)) := by
    have h1 : (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = (1 : ℂ) := by
      push_cast; ring
    rw [h1]
    have h2 := dChiEntry_eq P hS2 hjord r hij (1 : ℂ)
    rw [dChiEntry_apply] at h2
    exact h2
  rw [hentry] at hval
  -- the right side: `J(1,0) = (0,1)`, scaled
  rw [LinearMap.smul_apply, rotJ_apply, hxe] at hval
  simp only [map_smul, LinearEquiv.apply_symm_apply, Complex.smul_re,
    Complex.smul_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, neg_zero, Prod.smul_mk, smul_eq_mul] at hval
  have hsnd := congrArg Prod.snd hval
  simp only at hsnd
  linarith [hsnd]

end Necessity
