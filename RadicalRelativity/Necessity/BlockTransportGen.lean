/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockModelGen

set_option linter.style.longLine false

/-!
# Θ transports blocks isometrically  (LEDGER 2.6, u2 part 2)

* `blockHermG` satisfies the Peirce eigenrelations (`frameProjG_symmMul_blockHerm_*`).
* Θ fixes the frame and preserves `∘` (M3), so it preserves the relations —
  `thetaNorm_blockG`: the image of a block element is a block element.
* **`normSq_thetaNorm_blockG` (the u2 capstone)**: comparing the square law on
  both sides of `Θ(x∘x) = Θx ∘ Θx` — with `Θ` fixing `p_i + p_j` — gives
  `|w|² = |z|²`: **Θ acts on each block by a Euclidean isometry**, with no norm
  or compactness imports anywhere.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
variable (P : SequentialProductOn (HermitianMat n 𝕜))

theorem thetaNorm_fixes_frameProjG (hS2 : P.FirstArgContinuous) (s : n → ℝ) (k : n) :
    thetaNormG P hS2 (diagFamilyG 𝕜 s) (frameProjG 𝕜 k) = frameProjG 𝕜 k :=
  thetaNorm_fix_of_commuteG P hS2 (diagFamilyG_posDef s) (diagFamilyG_commute_frameProj s k)

/-! ## The block satisfies the Peirce eigenrelations -/

theorem frameProjG_symmMul_blockHerm_left {i j : n} (hij : i ≠ j) (z : 𝕜) :
    (frameProjG 𝕜 i).symmMul (blockHermG i j z) = (1 / 2 : ℝ) • blockHermG i j z := by
  have e1 : Matrix.single i i (1:𝕜) * Matrix.single i j 1 = Matrix.single i j 1 := by
    simp
  have e2 : Matrix.single i i (1:𝕜) * Matrix.single j i 1 = 0 := by
    simp [hij]
  have e3 : Matrix.single i j (1:𝕜) * Matrix.single i i 1 = 0 := by
    simp [Ne.symm hij]
  have e4 : Matrix.single j i (1:𝕜) * Matrix.single i i 1 = Matrix.single j i 1 := by
    simp
  ext1
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul, frameProj_mat_eq_singleG,
    blockHerm_matG]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e1, e2, e3, e4, smul_zero,
    add_zero, zero_add]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

theorem frameProjG_symmMul_blockHerm_right {i j : n} (hij : i ≠ j) (z : 𝕜) :
    (frameProjG 𝕜 j).symmMul (blockHermG i j z) = (1 / 2 : ℝ) • blockHermG i j z := by
  have e1 : Matrix.single j j (1:𝕜) * Matrix.single i j 1 = 0 := by
    simp [Ne.symm hij]
  have e2 : Matrix.single j j (1:𝕜) * Matrix.single j i 1 = Matrix.single j i 1 := by
    simp
  have e3 : Matrix.single i j (1:𝕜) * Matrix.single j j 1 = Matrix.single i j 1 := by
    simp
  have e4 : Matrix.single j i (1:𝕜) * Matrix.single j j 1 = 0 := by
    simp [hij]
  ext1
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul, frameProj_mat_eq_singleG,
    blockHerm_matG]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e1, e2, e3, e4, smul_zero,
    add_zero, zero_add]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

theorem frameProjG_symmMul_blockHerm_other {i j k : n} (hki : k ≠ i) (hkj : k ≠ j)
    (z : 𝕜) : (frameProjG 𝕜 k).symmMul (blockHermG i j z) = 0 := by
  have e1 : Matrix.single k k (1:𝕜) * Matrix.single i j 1 = 0 := by
    simp [hki]
  have e2 : Matrix.single k k (1:𝕜) * Matrix.single j i 1 = 0 := by
    simp [hkj]
  have e3 : Matrix.single i j (1:𝕜) * Matrix.single k k 1 = 0 := by
    simp [Ne.symm hkj]
  have e4 : Matrix.single j i (1:𝕜) * Matrix.single k k 1 = 0 := by
    simp [Ne.symm hki]
  ext1
  rw [HermitianMat.symmMul_toMat, frameProj_mat_eq_singleG, blockHerm_matG]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e1, e2, e3, e4, smul_zero,
    add_zero, zero_add, HermitianMat.mat_zero]

/-! ## Θ transports blocks to blocks -/

/-- **Θ maps block elements to block elements** (the Peirce relations transport
through the M3 Jordan hypothesis and frame-fixing). -/
theorem thetaNorm_blockG (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : 𝕜) :
    thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j z)
      = blockHermG i j
          ((thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j z)).mat i j) := by
  apply eq_blockHerm_of_peirceG hij
  · have hj' := thetaNorm_jordanG P hS2 hjord (diagFamilyG_posDef s)
      (frameProjG 𝕜 i) (blockHermG i j z)
    simp only [jordanBilin_applyG] at hj'
    rw [thetaNorm_fixes_frameProjG P hS2 s i] at hj'
    rw [← hj', frameProjG_symmMul_blockHerm_left hij z, map_smul]
  · have hj' := thetaNorm_jordanG P hS2 hjord (diagFamilyG_posDef s)
      (frameProjG 𝕜 j) (blockHermG i j z)
    simp only [jordanBilin_applyG] at hj'
    rw [thetaNorm_fixes_frameProjG P hS2 s j] at hj'
    rw [← hj', frameProjG_symmMul_blockHerm_right hij z, map_smul]
  · intro k hki hkj
    have hj' := thetaNorm_jordanG P hS2 hjord (diagFamilyG_posDef s)
      (frameProjG 𝕜 k) (blockHermG i j z)
    simp only [jordanBilin_applyG] at hj'
    rw [thetaNorm_fixes_frameProjG P hS2 s k] at hj'
    rw [← hj', frameProjG_symmMul_blockHerm_other hki hkj z, map_zero]

/-! ## The capstone: Θ is a Euclidean isometry on each block -/

/-- **Θ acts on each off-diagonal block by a Euclidean isometry** — `|w| = |z|`
for `Θ(blockHermG z) = blockHermG w` — from the square law alone. -/
theorem normSq_thetaNorm_blockG (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : 𝕜) :
    RCLike.normSq ((thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j z)).mat i j)
      = RCLike.normSq z := by
  set y := thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j z) with hy
  have hyb : y = blockHermG i j (y.mat i j) := thetaNorm_blockG P hS2 hjord s hij z
  have h1 : y.symmMul y
      = (RCLike.normSq (y.mat i j) : ℝ) • (frameProjG 𝕜 i + frameProjG 𝕜 j) := by
    conv_lhs => rw [hyb]
    exact blockHerm_symmMul_selfG hij _
  have h2 : y.symmMul y
      = (RCLike.normSq z : ℝ) • (frameProjG 𝕜 i + frameProjG 𝕜 j) := by
    have hjrd := thetaNorm_jordanG P hS2 hjord (diagFamilyG_posDef s)
      (blockHermG i j z) (blockHermG i j z)
    simp only [jordanBilin_applyG] at hjrd
    rw [hy, ← hjrd, blockHerm_symmMul_selfG hij z, map_smul, map_add,
      thetaNorm_fixes_frameProjG, thetaNorm_fixes_frameProjG]
  have hcomp := h1.symm.trans h2
  have hentry := congrArg (fun M => M.mat i i) hcomp
  simp only [HermitianMat.mat_smul, HermitianMat.mat_add, Matrix.smul_apply,
    Matrix.add_apply, frameProjG_mat] at hentry
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at hentry
  simp only [if_true, if_neg hij, add_zero, RCLike.real_smul_eq_coe_mul,
    Complex.ofReal_one, mul_one] at hentry
  exact_mod_cast hentry

end Necessity
