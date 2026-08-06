/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockTransportGen

set_option linter.style.longLine false

/-!
# χ̃ transports blocks isometrically  (LEDGER 2.6, u5a)

Extends the u2 capstone from Θ to the whole character: the inverse factor
`Θ⁻¹` maps blocks to blocks isometrically (relations transport through the
inverse-Jordan property; the norm identity by applying the forward isometry at
the image), hence so does `χ̃(r) = Θ_{r⊓0} Θ_{(r⊓0)−r}⁻¹`:

* `blockHerm_entryG` — the coordinate readback `(blockHermG z)_{ij} = z`.
* `thetaNorm_blockG_existsG` / `thetaNorm_symm_block_existsG` — Θ±1 send
  `blockHermG z` to some `blockHermG w` with `|w|² = |z|²`.
* `chiTilde_block_existsG` — the composite: **χ̃ acts on every block by a
  Euclidean isometry**, for every parameter `r`. The skew generator (u5b)
  differentiates this.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
variable (P : SequentialProductOn (HermitianMat n 𝕜))

/-- Coordinate readback: the `(i,j)` entry of `blockHermG i j z` is `z`. -/
theorem blockHerm_entryG {i j : n} (hij : i ≠ j) (z : 𝕜) :
    (blockHermG i j z).mat i j = z := by
  rw [blockHerm_matG]
  have c1 : (i = i ∧ j = j) = True := eq_true ⟨rfl, rfl⟩
  have c2 : (j = i ∧ i = j) = False := eq_false fun ⟨h', _⟩ => hij h'.symm
  simp [Matrix.single, c1, c2]

/-- Θ sends blocks to blocks isometrically (existential form of u2). -/
theorem thetaNorm_blockG_existsG (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : 𝕜) :
    ∃ w : 𝕜, thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j z) = blockHermG i j w
      ∧ RCLike.normSq w = RCLike.normSq z :=
  ⟨(thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j z)).mat i j,
    thetaNorm_blockG P hS2 hjord s hij z,
    normSq_thetaNorm_blockG P hS2 hjord s hij z⟩

/-- Θ⁻¹ sends blocks to blocks isometrically: apply the forward statement at the
inverse image and cancel. -/
theorem thetaNorm_symm_block_existsG (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (s : n → ℝ) {i j : n} (hij : i ≠ j) (z : 𝕜) :
    ∃ w : 𝕜, (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (blockHermG i j z)
        = blockHermG i j w
      ∧ RCLike.normSq w = RCLike.normSq z := by
  -- the inverse image satisfies the Peirce relations (inverse-Jordan transport)
  set y := (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (blockHermG i j z) with hy
  have hsymfix : ∀ k, (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (frameProjG 𝕜 k)
      = frameProjG 𝕜 k := by
    intro k
    calc (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (frameProjG 𝕜 k)
        = (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm
            (thetaNormG P hS2 (diagFamilyG 𝕜 s) (frameProjG 𝕜 k)) := by
          rw [thetaNorm_fixes_frameProjG P hS2 s k]
      _ = frameProjG 𝕜 k := LinearEquiv.symm_apply_apply _ _
  have hrel : ∀ k : n, (frameProjG 𝕜 k).symmMul y
      = (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm
          ((frameProjG 𝕜 k).symmMul (blockHermG i j z)) := by
    intro k
    calc (frameProjG 𝕜 k).symmMul y
        = ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (frameProjG 𝕜 k)).symmMul y := by
          rw [hsymfix k]
      _ = (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm
            ((frameProjG 𝕜 k).symmMul (blockHermG i j z)) := by
          rw [hy]
          exact (thetaNorm_symm_jordanG P hS2 hjord s _ _).symm
  have hyb : y = blockHermG i j (y.mat i j) := by
    apply eq_blockHerm_of_peirceG hij
    · rw [hrel i, frameProjG_symmMul_blockHerm_left hij z, map_smul]
    · rw [hrel j, frameProjG_symmMul_blockHerm_right hij z, map_smul]
    · intro k hki hkj
      rw [hrel k, frameProjG_symmMul_blockHerm_other hki hkj z, map_zero]
  refine ⟨y.mat i j, hyb, ?_⟩
  -- isometry: apply the forward isometry at `y` and cancel `Θ Θ⁻¹ = id`
  have hfwd := normSq_thetaNorm_blockG P hS2 hjord s hij (y.mat i j)
  have hcancel : thetaNormG P hS2 (diagFamilyG 𝕜 s) (blockHermG i j (y.mat i j))
      = blockHermG i j z := by
    rw [← hyb, hy, LinearEquiv.apply_symm_apply]
  rw [hcancel, blockHerm_entryG hij z] at hfwd
  exact hfwd.symm

/-- **χ̃ acts on every off-diagonal block by a Euclidean isometry**, for every
parameter `r` — the composite of the two Θ-factor statements. -/
theorem chiTilde_block_existsG (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) (z : 𝕜) :
    ∃ w : 𝕜, (chiTildeG P hS2 r).val (blockHermG i j z) = blockHermG i j w
      ∧ RCLike.normSq w = RCLike.normSq z := by
  obtain ⟨w1, hw1, hn1⟩ := thetaNorm_symm_block_existsG P hS2 hjord ((r ⊓ 0) - r) hij z
  obtain ⟨w2, hw2, hn2⟩ := thetaNorm_blockG_existsG P hS2 hjord (r ⊓ 0) hij w1
  refine ⟨w2, ?_, hn2.trans hn1⟩
  show ((thetaUnitG P hS2 (r ⊓ 0)) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val
    (blockHermG i j z) = blockHermG i j w2
  rw [Units.val_mul, ContinuousLinearMap.mul_apply]
  have hinv : ((thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val (blockHermG i j z)
      = blockHermG i j w1 := by
    show LinearMap.toContinuousLinearMap
      (thetaNormG P hS2 (diagFamilyG 𝕜 ((r ⊓ 0) - r))).symm.toLinearMap
        (blockHermG i j z) = blockHermG i j w1
    rw [LinearMap.coe_toContinuousLinearMap']
    exact hw1
  rw [hinv]
  show LinearMap.toContinuousLinearMap
    (thetaNormG P hS2 (diagFamilyG 𝕜 (r ⊓ 0))).toLinearMap (blockHermG i j w1)
      = blockHermG i j w2
  rw [LinearMap.coe_toContinuousLinearMap']
  exact hw2

end Necessity
