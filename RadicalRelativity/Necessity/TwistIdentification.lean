/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.FrameBlockSpan

set_option linter.style.longLine false

/-!
# The twist identification: `χ̃(r) = Ad_{U_t(r)}`  (closing the ℂ lane)

Assembles the two sides computed earlier:

* the **comparison side** — `χ̃(r)` fixes every frame projection
  (`chiTilde_fixes_frameProj`, proved here unconditionally) and maps each block
  to itself isometrically (`chiTilde_block_exists`);
* the **torus side** — `Ad_{U_t(r)}` fixes every frame projection
  (`torusU_fixes_frameProj`) and rotates the `(i,j)` block by `t(r_i − r_j)`
  (`torusU_block`);
* the **agreement principle** — `linearMap_eq_of_frame_block`.

The result (`chiTilde_eq_adU_of_block`) is that the identification reduces to a
single input: the *group-level* block action of `χ̃`.  The frame half is
discharged here; the block half is the exponentiation of
`complex_perFrame_unconditional`'s generator statement, which is the last
assembly step of the complex lane.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The comparison character fixes the frame -/

/-- `Θ⁻¹` fixes every frame projection. -/
theorem thetaNorm_symm_fixes_frameProj (hS2 : P.FirstArgContinuous)
    (s : n → ℝ) (k : n) :
    (thetaNorm P hS2 (diagFamily s)).symm (frameProj k) = frameProj k := by
  have h := thetaNorm_fixes_frameProj P hS2 s k
  calc (thetaNorm P hS2 (diagFamily s)).symm (frameProj k)
      = (thetaNorm P hS2 (diagFamily s)).symm
          (thetaNorm P hS2 (diagFamily s) (frameProj k)) := by rw [h]
    _ = frameProj k := LinearEquiv.symm_apply_apply _ _

/-- **The comparison character fixes every frame projection**, unconditionally
(both factors of `χ̃` do). -/
theorem chiTilde_fixes_frameProj (hS2 : P.FirstArgContinuous) (r : n → ℝ) (k : n) :
    (chiTilde P hS2 r).val (frameProj k) = frameProj k := by
  show (((thetaUnit P hS2 (r ⊓ 0)) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val)
    (frameProj k) = _
  rw [Units.val_mul, ContinuousLinearMap.mul_apply]
  have hinv : ((thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val (frameProj k)
      = frameProj k := by
    show LinearMap.toContinuousLinearMap
      (thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm.toLinearMap (frameProj k)
      = frameProj k
    rw [LinearMap.coe_toContinuousLinearMap']
    exact thetaNorm_symm_fixes_frameProj P hS2 _ k
  rw [hinv]
  show LinearMap.toContinuousLinearMap
    (thetaNorm P hS2 (diagFamily (r ⊓ 0))).toLinearMap (frameProj k) = _
  rw [LinearMap.coe_toContinuousLinearMap']
  exact thetaNorm_fixes_frameProj P hS2 _ k

/-! ## The identification -/

/-- **The twist identification, assembled.**  If the comparison character's
group-level block action is the rotation by `t(r_i − r_j)` — the exponentiated
form of `complex_perFrame_unconditional`'s generator statement — then `χ̃(r)` **is**
conjugation by the torus unitary `U_t(r)`, i.e. the paper's `Θ_a = Ad_{a^{it}}`.

The frame half of the hypothesis list is discharged (`chiTilde_fixes_frameProj`,
`torusU_fixes_frameProj`), so this is the identification modulo exactly one
input. -/
theorem chiTilde_eq_adU_of_block (hS2 : P.FirstArgContinuous) (t : ℝ) (r : n → ℝ)
    (hblock : ∀ (i j : n), i ≠ j → ∀ z : ℂ,
      (chiTilde P hS2 r).val (blockHerm i j z)
        = blockHerm i j (Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z)) :
    ((chiTilde P hS2 r).val : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
      = HermitianMat.conjLinear ℝ (torusU t r) := by
  refine linearMap_eq_of_frame_block _ _ ?_ ?_
  · intro k
    show (chiTilde P hS2 r).val (frameProj k) = _
    rw [chiTilde_fixes_frameProj P hS2 r k]
    show _ = adU (torusU t r) (frameProj k)
    rw [torusU_fixes_frameProj]
  · intro i j hij z
    show (chiTilde P hS2 r).val (blockHerm i j z) = _
    rw [hblock i j hij z]
    show _ = adU (torusU t r) (blockHerm i j z)
    rw [torusU_block t r hij z]

/-- **The product-level consequence.**  With the identification in hand, the
sequential product on invertible effects is the twist conjugation applied through
`Q_{√a}`: `a • b = Q_{√a}(Ad_{U_t(r)} b)`.  This is the shape of
`mthm:master`'s complex case; the remaining work is bookkeeping between the
character parameter `r` and the spectrum of `a`. -/
theorem sp_eq_quadRep_adU {N : ℕ}
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    {a : HermitianMat (Fin N) ℂ} (ha : OrderUnitSpace.IsEffect a)
    (hbd : a.mat.PosDef) (t : ℝ) (r : Fin N → ℝ)
    (hid : ((theta P ha hbd : HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ))
      = HermitianMat.conjLinear ℝ (torusU t r))
    {b : HermitianMat (Fin N) ℂ} (hb : OrderUnitSpace.IsEffect b) :
    P.sp a b = (adU (torusU t r) b).conj (a.cfc Real.sqrt).mat := by
  rw [sp_eq_quadRep_theta P ha hbd hb]
  congr 1
  have h := congrFun (congrArg (fun L : HermitianMat (Fin N) ℂ →ₗ[ℝ]
    HermitianMat (Fin N) ℂ => (L : HermitianMat (Fin N) ℂ → HermitianMat (Fin N) ℂ)) hid) b
  exact h

end Necessity
