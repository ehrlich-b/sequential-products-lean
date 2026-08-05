/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockTransport

set_option linter.style.longLine false

/-!
# χ̃ transports blocks isometrically  (LEDGER 2.6, u5a)

Extends the u2 capstone from Θ to the whole character: the inverse factor
`Θ⁻¹` maps blocks to blocks isometrically (relations transport through the
inverse-Jordan property; the norm identity by applying the forward isometry at
the image), hence so does `χ̃(r) = Θ_{r⊓0} Θ_{(r⊓0)−r}⁻¹`:

* `blockHerm_entry` — the coordinate readback `(blockHerm z)_{ij} = z`.
* `thetaNorm_block_exists` / `thetaNorm_symm_block_exists` — Θ±1 send
  `blockHerm z` to some `blockHerm w` with `|w|² = |z|²`.
* `chiTilde_block_exists` — the composite: **χ̃ acts on every block by a
  Euclidean isometry**, for every parameter `r`. The skew generator (u5b)
  differentiates this.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- Coordinate readback: the `(i,j)` entry of `blockHerm i j z` is `z`. -/
theorem blockHerm_entry {i j : n} (hij : i ≠ j) (z : ℂ) :
    (blockHerm i j z).mat i j = z := by
  rw [blockHerm_mat]
  have c1 : (i = i ∧ j = j) = True := eq_true ⟨rfl, rfl⟩
  have c2 : (j = i ∧ i = j) = False := eq_false fun ⟨h', _⟩ => hij h'.symm
  simp [Matrix.single, c1, c2]

/-- Θ sends blocks to blocks isometrically (existential form of u2). -/
theorem thetaNorm_block_exists (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    ∃ w : ℂ, thetaNorm P hS2 (diagFamily s) (blockHerm i j z) = blockHerm i j w
      ∧ Complex.normSq w = Complex.normSq z :=
  ⟨(thetaNorm P hS2 (diagFamily s) (blockHerm i j z)).mat i j,
    thetaNorm_block P hS2 hjord s hij z,
    normSq_thetaNorm_block P hS2 hjord s hij z⟩

/-- Θ⁻¹ sends blocks to blocks isometrically: apply the forward statement at the
inverse image and cancel. -/
theorem thetaNorm_symm_block_exists (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    ∃ w : ℂ, (thetaNorm P hS2 (diagFamily s)).symm (blockHerm i j z)
        = blockHerm i j w
      ∧ Complex.normSq w = Complex.normSq z := by
  -- the inverse image satisfies the Peirce relations (inverse-Jordan transport)
  set y := (thetaNorm P hS2 (diagFamily s)).symm (blockHerm i j z) with hy
  have hsymfix : ∀ k, (thetaNorm P hS2 (diagFamily s)).symm (frameProj k)
      = frameProj k := by
    intro k
    calc (thetaNorm P hS2 (diagFamily s)).symm (frameProj k)
        = (thetaNorm P hS2 (diagFamily s)).symm
            (thetaNorm P hS2 (diagFamily s) (frameProj k)) := by
          rw [thetaNorm_fixes_frameProj P hS2 s k]
      _ = frameProj k := LinearEquiv.symm_apply_apply _ _
  have hrel : ∀ k : n, (frameProj k).symmMul y
      = (thetaNorm P hS2 (diagFamily s)).symm
          ((frameProj k).symmMul (blockHerm i j z)) := by
    intro k
    calc (frameProj k).symmMul y
        = ((thetaNorm P hS2 (diagFamily s)).symm (frameProj k)).symmMul y := by
          rw [hsymfix k]
      _ = (thetaNorm P hS2 (diagFamily s)).symm
            ((frameProj k).symmMul (blockHerm i j z)) := by
          rw [hy]
          exact (thetaNorm_symm_jordan P hS2 hjord s _ _).symm
  have hyb : y = blockHerm i j (y.mat i j) := by
    apply eq_blockHerm_of_peirce hij
    · rw [hrel i, frameProj_symmMul_blockHerm_left hij z, map_smul]
    · rw [hrel j, frameProj_symmMul_blockHerm_right hij z, map_smul]
    · intro k hki hkj
      rw [hrel k, frameProj_symmMul_blockHerm_other hki hkj z, map_zero]
  refine ⟨y.mat i j, hyb, ?_⟩
  -- isometry: apply the forward isometry at `y` and cancel `Θ Θ⁻¹ = id`
  have hfwd := normSq_thetaNorm_block P hS2 hjord s hij (y.mat i j)
  have hcancel : thetaNorm P hS2 (diagFamily s) (blockHerm i j (y.mat i j))
      = blockHerm i j z := by
    rw [← hyb, hy, LinearEquiv.apply_symm_apply]
  rw [hcancel, blockHerm_entry hij z] at hfwd
  exact hfwd.symm

/-- **χ̃ acts on every off-diagonal block by a Euclidean isometry**, for every
parameter `r` — the composite of the two Θ-factor statements. -/
theorem chiTilde_block_exists (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    ∃ w : ℂ, (chiTilde P hS2 r).val (blockHerm i j z) = blockHerm i j w
      ∧ Complex.normSq w = Complex.normSq z := by
  obtain ⟨w1, hw1, hn1⟩ := thetaNorm_symm_block_exists P hS2 hjord ((r ⊓ 0) - r) hij z
  obtain ⟨w2, hw2, hn2⟩ := thetaNorm_block_exists P hS2 hjord (r ⊓ 0) hij w1
  refine ⟨w2, ?_, hn2.trans hn1⟩
  show ((thetaUnit P hS2 (r ⊓ 0)) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val
    (blockHerm i j z) = blockHerm i j w2
  rw [Units.val_mul, ContinuousLinearMap.mul_apply]
  have hinv : ((thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val (blockHerm i j z)
      = blockHerm i j w1 := by
    show LinearMap.toContinuousLinearMap
      (thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm.toLinearMap
        (blockHerm i j z) = blockHerm i j w1
    rw [LinearMap.coe_toContinuousLinearMap']
    exact hw1
  rw [hinv]
  show LinearMap.toContinuousLinearMap
    (thetaNorm P hS2 (diagFamily (r ⊓ 0))).toLinearMap (blockHerm i j w1)
      = blockHerm i j w2
  rw [LinearMap.coe_toContinuousLinearMap']
  exact hw2

end Necessity
