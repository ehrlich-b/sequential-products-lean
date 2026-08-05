/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockModel

set_option linter.style.longLine false

/-!
# The phase cocycle, part 1: skew classification and cross-block products  (LEDGER 2.6, u6a)

Two ingredients for the torus normalization of the derivative `dχ`:

* `skew_linear_eq_I_smul` — **the 2×2 skew classification**: an ℝ-linear map
  `T : ℂ → ℂ` with `Re(z̄ · Tz) = 0` for all `z` is multiplication by `it`
  for the real number `t = (T 1).im`.  Applied to the block entry maps of
  `dχ(r)` (skew by `dChi_block_skew`), this turns each block action into a
  single real phase rate `t_{ij}(r)`.
* `blockHerm_symmMul_blockHerm` — **the cross-block product formula**:
  `(z E_ij + z̄ E_ji) ∘ (v E_jk + v̄ E_kj) = ½ (zv E_ik + z̄v̄ E_ki)` for
  pairwise distinct `i,j,k`.  Feeding this into the Jordan-derivation
  property of `dχ(r)` (u6c) yields the Leibniz rule for the entry maps and
  hence the **cocycle identity** `t_{ik} = t_{ij} + t_{jk}` (u6d) — the
  content that collapses the per-pair rates to a per-index anchor, which is
  exactly the `hmodel` hypothesis of `complex_perFrame_rho`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The skew classification -/

/-- **Skew classification on ℂ**: an ℝ-linear `T : ℂ → ℂ` whose value is
Euclidean-orthogonal to its argument everywhere is multiplication by `it`
with `t = (T 1).im`. -/
theorem skew_linear_eq_I_smul (T : ℂ →ₗ[ℝ] ℂ)
    (hskew : ∀ z : ℂ, z.re * (T z).re + z.im * (T z).im = 0) (z : ℂ) :
    T z = (T 1).im • (Complex.I * z) := by
  have h1 : (T 1).re = 0 := by simpa using hskew 1
  have hI : (T Complex.I).im = 0 := by simpa using hskew Complex.I
  have hIre : (T Complex.I).re = -(T 1).im := by
    have h := hskew (1 + Complex.I)
    rw [map_add] at h
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, h1, hI] at h
    linarith
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have hTz : T z = z.re • T 1 + z.im • T Complex.I := by
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
  rw [hTz]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, h1, hI, hIre]
    ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_re, h1, hI, hIre]
    ring

/-! ## The cross-block product -/

/-- **The cross-block product formula**: for pairwise distinct `i, j, k`,
`blockHerm i j z ∘ blockHerm j k v = ½ • blockHerm i k (zv)`. -/
theorem blockHerm_symmMul_blockHerm {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (z v : ℂ) :
    (blockHerm i j z).symmMul (blockHerm j k v)
      = (1 / 2 : ℝ) • blockHerm i k (z * v) := by
  have f1 : Matrix.single i j (1:ℂ) * Matrix.single j k 1 = Matrix.single i k 1 := by
    simp
  have f2 : Matrix.single i j (1:ℂ) * Matrix.single k j 1 = 0 := by
    simp [hjk]
  have f3 : Matrix.single j i (1:ℂ) * Matrix.single j k 1 = 0 := by
    simp [hij]
  have f4 : Matrix.single j i (1:ℂ) * Matrix.single k j 1 = 0 := by
    simp [hik]
  have g1 : Matrix.single j k (1:ℂ) * Matrix.single i j 1 = 0 := by
    simp [Ne.symm hik]
  have g2 : Matrix.single j k (1:ℂ) * Matrix.single j i 1 = 0 := by
    simp [Ne.symm hjk]
  have g3 : Matrix.single k j (1:ℂ) * Matrix.single i j 1 = 0 := by
    simp [Ne.symm hij]
  have g4 : Matrix.single k j (1:ℂ) * Matrix.single j i 1 = Matrix.single k i 1 := by
    simp
  ext1
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul, blockHerm_mat, blockHerm_mat,
    blockHerm_mat]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    f1, f2, f3, f4, g1, g2, g3, g4, smul_zero, add_zero, zero_add]
  rw [star_mul]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

end Necessity
