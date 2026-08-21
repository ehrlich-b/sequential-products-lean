/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockChi
import RadicalRelativity.Hermitian.OperatorInstances

set_option linter.style.longLine false

/-!
# The block generator is skew  (LEDGER 2.6, u5b — `prop:isotropy` on `H_n(ℂ)`)

Differentiate the isometric flow: `t ↦ |entry of χ̃(t·r)(blockHerm z₀)|²` is
constant (`chiTilde_block_exists`), its derivative at `t = 0` is
`2(z₀.re·w.re + z₀.im·w.im)` for `w := entry of dχ(r)(blockHerm z₀)` — so the
block action of the differential is skew for the Euclidean structure:
`dChi_block_skew : v₁·w.re + v₂·w.im = 0`.

This is the paper's `prop:isotropy` on the concrete carrier, obtained with no
compactness and no invariant-measure argument — only the square law and
one-variable calculus.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace Topology NormedSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- The `(i,j)` matrix entry as an ℝ-linear map. -/
def entryLm (i j : n) : HermitianMat n ℂ →ₗ[ℝ] ℂ where
  toFun x := x.mat i j
  map_add' x y := by
    rw [HermitianMat.mat_add]
    simp [Matrix.add_apply]
  map_smul' r x := by
    rw [HermitianMat.mat_smul]
    simp [Matrix.smul_apply]

/-- The entry map as a continuous linear map (finite dimensions). -/
def entryCLM (i j : n) : HermitianMat n ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (entryLm i j)

@[simp]
theorem entryCLM_apply (i j : n) (x : HermitianMat n ℂ) :
    entryCLM i j x = x.mat i j := by
  show LinearMap.toContinuousLinearMap (entryLm i j) x = x.mat i j
  rw [LinearMap.coe_toContinuousLinearMap']
  rfl

/-- **The block generator is skew** (`prop:isotropy`, machine-checked): for
`z₀ = v₁ + v₂ i` and `w` the block coordinate of `dχ(r)` applied to the block
element of `z₀`, the Euclidean dot product `v₁·w.re + v₂·w.im` vanishes. -/
theorem dChi_block_skew (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) {i j : n} (hij : i ≠ j) (v1 v2 : ℝ) :
    v1 * ((dChi P hS2 hjord r
        (blockHerm i j ((v1 : ℂ) + v2 * Complex.I))).mat i j).re
      + v2 * ((dChi P hS2 hjord r
        (blockHerm i j ((v1 : ℂ) + v2 * Complex.I))).mat i j).im = 0 := by
  set z₀ : ℂ := (v1 : ℂ) + v2 * Complex.I with hz
  set A := dChi P hS2 hjord r with hA
  set x := blockHerm i j z₀ with hx
  -- the entry curve and its derivative at 0
  have hcurve : HasDerivAt (fun t : ℝ => entryCLM i j (exp (t • A) x))
      (entryCLM i j (A x)) 0 := by
    have hd := exp_apply_hasDerivAt A x
    -- Compose with the constant map directly. The `hasDerivAt_const .clm_apply` route needs a
    -- normed structure on `HermitianMat n ℂ →L[ℝ] ℂ`, which the topology diamond blocks.
    exact (entryCLM i j).hasFDerivAt.comp_hasDerivAt 0 hd
  -- the value at 0 is z₀
  have hval0 : entryCLM i j (exp ((0 : ℝ) • A) x) = z₀ := by
    rw [show (0 : ℝ) • A = 0 from zero_smul ℝ A, exp_zero]
    show entryCLM i j ((1 : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) x) = z₀
    rw [ContinuousLinearMap.one_apply, entryCLM_apply, hx, blockHerm_entry hij]
  -- real and imaginary components of the curve
  have hre : HasDerivAt (fun t : ℝ => (entryCLM i j (exp (t • A) x)).re)
      ((entryCLM i j (A x)).re) 0 := by
    have hcC := hasDerivAt_const (0 : ℝ) Complex.reCLM
    have hcomb := hcC.clm_apply hcurve
    simpa using hcomb
  have him : HasDerivAt (fun t : ℝ => (entryCLM i j (exp (t • A) x)).im)
      ((entryCLM i j (A x)).im) 0 := by
    have hcC := hasDerivAt_const (0 : ℝ) Complex.imCLM
    have hcomb := hcC.clm_apply hcurve
    simpa using hcomb
  -- F := re² + im² has derivative 2(z₀.re·w.re + z₀.im·w.im) at 0
  have hFd : HasDerivAt
      (fun t : ℝ => (entryCLM i j (exp (t • A) x)).re
          * (entryCLM i j (exp (t • A) x)).re
        + (entryCLM i j (exp (t • A) x)).im
          * (entryCLM i j (exp (t • A) x)).im)
      ((entryCLM i j (A x)).re * (entryCLM i j (exp ((0:ℝ) • A) x)).re
        + (entryCLM i j (exp ((0:ℝ) • A) x)).re * (entryCLM i j (A x)).re
        + ((entryCLM i j (A x)).im * (entryCLM i j (exp ((0:ℝ) • A) x)).im
          + (entryCLM i j (exp ((0:ℝ) • A) x)).im * (entryCLM i j (A x)).im)) 0 :=
    (hre.mul hre).add (him.mul him)
  -- F is constant, equal to normSq z₀
  have hFconst : (fun t : ℝ => (entryCLM i j (exp (t • A) x)).re
          * (entryCLM i j (exp (t • A) x)).re
        + (entryCLM i j (exp (t • A) x)).im
          * (entryCLM i j (exp (t • A) x)).im)
      = fun _ : ℝ => Complex.normSq z₀ := by
    funext t
    have hexp : exp (t • A) = ((chiTilde P hS2 (t • r)).val) := by
      rw [hA, ← map_smul (dChi P hS2 hjord) t r]
      exact (chiTilde_eq_exp_dChi P hS2 hjord (t • r)).symm
    rw [hexp]
    obtain ⟨wt, hwt, hnt⟩ := chiTilde_block_exists P hS2 hjord (t • r) hij z₀
    rw [hx, hwt, entryCLM_apply, blockHerm_entry hij]
    rw [← hnt, Complex.normSq_apply]
  have hzero : HasDerivAt (fun _ : ℝ => Complex.normSq z₀) 0 0 :=
    hasDerivAt_const _ _
  rw [hFconst] at hFd
  have hkill := hFd.unique hzero
  rw [hval0] at hkill
  -- unpack: z₀.re = v₁, z₀.im = v₂
  have hzre : z₀.re = v1 := by simp [hz]
  have hzim : z₀.im = v2 := by simp [hz]
  rw [hzre, hzim] at hkill
  have hw : entryCLM i j (A x) = (A x).mat i j := entryCLM_apply i j (A x)
  rw [hw] at hkill
  linarith

end Necessity
