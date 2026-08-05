/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockModel

set_option linter.style.longLine false

/-!
# Θ transports blocks isometrically  (LEDGER 2.6, u2 part 2)

* `blockHerm` satisfies the Peirce eigenrelations (`frameProj_symmMul_blockHerm_*`).
* Θ fixes the frame and preserves `∘` (M3), so it preserves the relations —
  `thetaNorm_block`: the image of a block element is a block element.
* **`normSq_thetaNorm_block` (the u2 capstone)**: comparing the square law on
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
variable (P : SequentialProductOn (HermitianMat n ℂ))

theorem thetaNorm_fixes_frameProj (hS2 : P.FirstArgContinuous) (s : n → ℝ) (k : n) :
    thetaNorm P hS2 (diagFamily s) (frameProj k) = frameProj k :=
  thetaNorm_fix_of_commute P hS2 (diagFamily_posDef s) (diagFamily_commute_frameProj s k)

/-! ## The block satisfies the Peirce eigenrelations -/

theorem frameProj_symmMul_blockHerm_left {i j : n} (hij : i ≠ j) (z : ℂ) :
    (frameProj i).symmMul (blockHerm i j z) = (1 / 2 : ℝ) • blockHerm i j z := by
  have e1 : Matrix.single i i (1:ℂ) * Matrix.single i j 1 = Matrix.single i j 1 := by
    simp
  have e2 : Matrix.single i i (1:ℂ) * Matrix.single j i 1 = 0 := by
    simp [hij]
  have e3 : Matrix.single i j (1:ℂ) * Matrix.single i i 1 = 0 := by
    simp [Ne.symm hij]
  have e4 : Matrix.single j i (1:ℂ) * Matrix.single i i 1 = Matrix.single j i 1 := by
    simp
  ext1
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul, frameProj_mat_eq_single,
    blockHerm_mat]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e1, e2, e3, e4, smul_zero,
    add_zero, zero_add]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem frameProj_symmMul_blockHerm_right {i j : n} (hij : i ≠ j) (z : ℂ) :
    (frameProj j).symmMul (blockHerm i j z) = (1 / 2 : ℝ) • blockHerm i j z := by
  have e1 : Matrix.single j j (1:ℂ) * Matrix.single i j 1 = 0 := by
    simp [Ne.symm hij]
  have e2 : Matrix.single j j (1:ℂ) * Matrix.single j i 1 = Matrix.single j i 1 := by
    simp
  have e3 : Matrix.single i j (1:ℂ) * Matrix.single j j 1 = Matrix.single i j 1 := by
    simp
  have e4 : Matrix.single j i (1:ℂ) * Matrix.single j j 1 = 0 := by
    simp [hij]
  ext1
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul, frameProj_mat_eq_single,
    blockHerm_mat]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e1, e2, e3, e4, smul_zero,
    add_zero, zero_add]
  ext a b
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem frameProj_symmMul_blockHerm_other {i j k : n} (hki : k ≠ i) (hkj : k ≠ j)
    (z : ℂ) : (frameProj k).symmMul (blockHerm i j z) = 0 := by
  have e1 : Matrix.single k k (1:ℂ) * Matrix.single i j 1 = 0 := by
    simp [hki]
  have e2 : Matrix.single k k (1:ℂ) * Matrix.single j i 1 = 0 := by
    simp [hkj]
  have e3 : Matrix.single i j (1:ℂ) * Matrix.single k k 1 = 0 := by
    simp [Ne.symm hkj]
  have e4 : Matrix.single j i (1:ℂ) * Matrix.single k k 1 = 0 := by
    simp [Ne.symm hki]
  ext1
  rw [HermitianMat.symmMul_toMat, frameProj_mat_eq_single, blockHerm_mat]
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, e1, e2, e3, e4, smul_zero,
    add_zero, zero_add, HermitianMat.mat_zero]

/-! ## Θ transports blocks to blocks -/

/-- **Θ maps block elements to block elements** (the Peirce relations transport
through the M3 Jordan hypothesis and frame-fixing). -/
theorem thetaNorm_block (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    thetaNorm P hS2 (diagFamily s) (blockHerm i j z)
      = blockHerm i j
          ((thetaNorm P hS2 (diagFamily s) (blockHerm i j z)).mat i j) := by
  apply eq_blockHerm_of_peirce hij
  · have hj' := thetaNorm_jordan P hS2 hjord (diagFamily_posDef s)
      (frameProj i) (blockHerm i j z)
    simp only [jordanBilin_apply] at hj'
    rw [thetaNorm_fixes_frameProj P hS2 s i] at hj'
    rw [← hj', frameProj_symmMul_blockHerm_left hij z, map_smul]
  · have hj' := thetaNorm_jordan P hS2 hjord (diagFamily_posDef s)
      (frameProj j) (blockHerm i j z)
    simp only [jordanBilin_apply] at hj'
    rw [thetaNorm_fixes_frameProj P hS2 s j] at hj'
    rw [← hj', frameProj_symmMul_blockHerm_right hij z, map_smul]
  · intro k hki hkj
    have hj' := thetaNorm_jordan P hS2 hjord (diagFamily_posDef s)
      (frameProj k) (blockHerm i j z)
    simp only [jordanBilin_apply] at hj'
    rw [thetaNorm_fixes_frameProj P hS2 s k] at hj'
    rw [← hj', frameProj_symmMul_blockHerm_other hki hkj z, map_zero]

/-! ## The capstone: Θ is a Euclidean isometry on each block -/

/-- **Θ acts on each off-diagonal block by a Euclidean isometry** — `|w| = |z|`
for `Θ(blockHerm z) = blockHerm w` — from the square law alone. -/
theorem normSq_thetaNorm_block (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    Complex.normSq ((thetaNorm P hS2 (diagFamily s) (blockHerm i j z)).mat i j)
      = Complex.normSq z := by
  set y := thetaNorm P hS2 (diagFamily s) (blockHerm i j z) with hy
  have hyb : y = blockHerm i j (y.mat i j) := thetaNorm_block P hS2 hjord s hij z
  have h1 : y.symmMul y
      = (Complex.normSq (y.mat i j) : ℝ) • (frameProj i + frameProj j) := by
    conv_lhs => rw [hyb]
    exact blockHerm_symmMul_self hij _
  have h2 : y.symmMul y
      = (Complex.normSq z : ℝ) • (frameProj i + frameProj j) := by
    have hjrd := thetaNorm_jordan P hS2 hjord (diagFamily_posDef s)
      (blockHerm i j z) (blockHerm i j z)
    simp only [jordanBilin_apply] at hjrd
    rw [hy, ← hjrd, blockHerm_symmMul_self hij z, map_smul, map_add,
      thetaNorm_fixes_frameProj, thetaNorm_fixes_frameProj]
  have hcomp := h1.symm.trans h2
  have hentry := congrArg (fun M => M.mat i i) hcomp
  simp only [HermitianMat.mat_smul, HermitianMat.mat_add, Matrix.smul_apply,
    Matrix.add_apply, frameProj_mat] at hentry
  rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at hentry
  simp only [if_true, if_neg hij, add_zero, Complex.real_smul,
    Complex.ofReal_one, mul_one] at hentry
  exact_mod_cast hentry

end Necessity
