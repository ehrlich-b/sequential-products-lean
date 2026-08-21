/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.CoalescenceDiff

set_option linter.style.longLine false

/-!
# Block invariance of the character and its differential  (LEDGER 2.6, u3)

The corner `J₂(q)` is invariant under the whole lane:

* `cornerJ2_iff_symmMul` — corner membership is the Jordan eigenrelation
  `q ∘ x = x` (forward by absorption, backward by `cornerJ2_of_double`).
* `thetaNorm_preserves_cornerJ2` / inverse / `chiTilde_preserves_cornerJ2` —
  Θ fixes `q` (diagonal commutation) and preserves `∘` (the M3 hypothesis), so
  it preserves the eigenrelation; the inverse inherits both properties.
* `dChi_preserves_corner` — differentiate: `L(exp(t·dχ)x) ≡ exp(t·dχ)x` for the
  corner-conjugation `L`, so the derivatives at `0` agree, i.e.
  `L(dχ(r)x) = dχ(r)x`.

With u4 (`dChi_kills_corner`) this completes the differential-face geometry:
`dχ(r)` preserves every corner and kills the coalesced ones.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace Topology NormedSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The corner as a Hermitian element and the Jordan eigenrelation -/

theorem cornerQ_isHermitian (i j : n) : (cornerQ i j).IsHermitian := by
  show _ᴴ = _
  unfold cornerQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  by_cases h : k = i ∨ k = j <;> simp [h]

/-- The corner projection as a Hermitian matrix. -/
def cornerHerm (i j : n) : HermitianMat n ℂ := ⟨cornerQ i j, cornerQ_isHermitian i j⟩

@[simp]
theorem cornerHerm_mat (i j : n) : (cornerHerm i j).mat = cornerQ i j := rfl

/-- Forward: corner membership gives the Jordan eigenrelation `q ∘ x = x`. -/
theorem cornerHerm_symmMul_of_J2 {i j : n} {x : HermitianMat n ℂ}
    (hx : cornerJ2 i j x) : (cornerHerm i j).symmMul x = x := by
  ext1
  rw [HermitianMat.symmMul_toMat, cornerHerm_mat,
    (cornerJ2_absorb hx).1, (cornerJ2_absorb hx).2]
  rw [← two_smul ℂ x.mat, smul_smul]
  norm_num

/-- Backward: the Jordan eigenrelation gives corner membership. -/
theorem cornerJ2_of_symmMul {i j : n} {x : HermitianMat n ℂ}
    (h : (cornerHerm i j).symmMul x = x) : cornerJ2 i j x := by
  apply cornerJ2_of_double
  have hmat := congrArg HermitianMat.mat h
  rw [HermitianMat.symmMul_toMat] at hmat
  have h2 := congrArg (fun M => (2 : ℂ) • M) hmat
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_smul] at h2
  exact h2

/-- The diagonal family commutes with every corner projection. -/
theorem diagFamily_commute_cornerQ (s : n → ℝ) (i j : n) :
    Commute (diagFamily s).mat (cornerQ i j) := by
  show _ * _ = _ * _
  rw [diagFamily_mat]
  unfold cornerQ
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  ring

/-! ## Θ, its inverse, and χ̃ preserve corners -/

theorem thetaNorm_fixes_cornerHerm (hS2 : P.FirstArgContinuous) (s : n → ℝ) (i j : n) :
    thetaNorm P hS2 (diagFamily s) (cornerHerm i j) = cornerHerm i j :=
  thetaNorm_fix_of_commute P hS2 (diagFamily_posDef s) (diagFamily_commute_cornerQ s i j)

theorem thetaNorm_preserves_cornerJ2 (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (s : n → ℝ) {i j : n} {x : HermitianMat n ℂ}
    (hx : cornerJ2 i j x) :
    cornerJ2 i j (thetaNorm P hS2 (diagFamily s) x) := by
  apply cornerJ2_of_symmMul
  have hj := thetaNorm_jordan P hS2 hjord (diagFamily_posDef s) (cornerHerm i j) x
  simp only [jordanBilin_apply] at hj
  calc (cornerHerm i j).symmMul (thetaNorm P hS2 (diagFamily s) x)
      = (thetaNorm P hS2 (diagFamily s) (cornerHerm i j)).symmMul
          (thetaNorm P hS2 (diagFamily s) x) := by
        rw [thetaNorm_fixes_cornerHerm P hS2 s i j]
    _ = thetaNorm P hS2 (diagFamily s) ((cornerHerm i j).symmMul x) := hj.symm
    _ = thetaNorm P hS2 (diagFamily s) x := by
        rw [cornerHerm_symmMul_of_J2 hx]

/-- The inverse of a Jordan-preserving linear equivalence is Jordan-preserving. -/
theorem thetaNorm_symm_jordan (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (s : n → ℝ) (u v : HermitianMat n ℂ) :
    (thetaNorm P hS2 (diagFamily s)).symm (u.symmMul v)
      = ((thetaNorm P hS2 (diagFamily s)).symm u).symmMul
        ((thetaNorm P hS2 (diagFamily s)).symm v) := by
  apply (thetaNorm P hS2 (diagFamily s)).injective
  have hj := thetaNorm_jordan P hS2 hjord (diagFamily_posDef s)
    ((thetaNorm P hS2 (diagFamily s)).symm u)
    ((thetaNorm P hS2 (diagFamily s)).symm v)
  simp only [jordanBilin_apply] at hj
  rw [LinearEquiv.apply_symm_apply, hj,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem thetaNorm_symm_preserves_cornerJ2 (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (s : n → ℝ) {i j : n} {x : HermitianMat n ℂ}
    (hx : cornerJ2 i j x) :
    cornerJ2 i j ((thetaNorm P hS2 (diagFamily s)).symm x) := by
  apply cornerJ2_of_symmMul
  have hfixsym : (thetaNorm P hS2 (diagFamily s)).symm (cornerHerm i j)
      = cornerHerm i j := by
    calc (thetaNorm P hS2 (diagFamily s)).symm (cornerHerm i j)
        = (thetaNorm P hS2 (diagFamily s)).symm
            (thetaNorm P hS2 (diagFamily s) (cornerHerm i j)) := by
          rw [thetaNorm_fixes_cornerHerm P hS2 s i j]
      _ = cornerHerm i j := LinearEquiv.symm_apply_apply _ _
  calc (cornerHerm i j).symmMul ((thetaNorm P hS2 (diagFamily s)).symm x)
      = ((thetaNorm P hS2 (diagFamily s)).symm (cornerHerm i j)).symmMul
          ((thetaNorm P hS2 (diagFamily s)).symm x) := by rw [hfixsym]
    _ = (thetaNorm P hS2 (diagFamily s)).symm ((cornerHerm i j).symmMul x) :=
        (thetaNorm_symm_jordan P hS2 hjord s _ _).symm
    _ = (thetaNorm P hS2 (diagFamily s)).symm x := by
        rw [cornerHerm_symmMul_of_J2 hx]

/-- χ̃ preserves every corner. -/
theorem chiTilde_preserves_cornerJ2 (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) {i j : n} {x : HermitianMat n ℂ}
    (hx : cornerJ2 i j x) :
    cornerJ2 i j ((chiTilde P hS2 r).val x) := by
  show cornerJ2 i j
    (((thetaUnit P hS2 (r ⊓ 0)) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val x)
  rw [Units.val_mul, ContinuousLinearMap.mul_apply]
  have hinv : cornerJ2 i j (((thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val x) := by
    show cornerJ2 i j (LinearMap.toContinuousLinearMap
      (thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm.toLinearMap x)
    rw [LinearMap.coe_toContinuousLinearMap']
    exact thetaNorm_symm_preserves_cornerJ2 P hS2 hjord _ hx
  show cornerJ2 i j (LinearMap.toContinuousLinearMap
    (thetaNorm P hS2 (diagFamily (r ⊓ 0))).toLinearMap _)
  rw [LinearMap.coe_toContinuousLinearMap']
  exact thetaNorm_preserves_cornerJ2 P hS2 hjord _ hinv

/-! ## The differential preserves corners -/

/-- The corner conjugation `x ↦ q x q` as a continuous linear map. -/
def cornerConjCLM (i j : n) : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ :=
  LinearMap.toContinuousLinearMap (HermitianMat.conjLinear ℝ (cornerQ i j))

theorem cornerConjCLM_eq_iff {i j : n} {x : HermitianMat n ℂ} :
    cornerConjCLM i j x = x ↔ cornerJ2 i j x := by
  have happ : cornerConjCLM i j x = HermitianMat.conjLinear ℝ (cornerQ i j) x := by
    unfold cornerConjCLM
    rw [LinearMap.coe_toContinuousLinearMap']
  rw [happ, HermitianMat.conjLinear_apply]
  constructor
  · intro h
    have hm := congrArg HermitianMat.mat h
    rw [HermitianMat.conj_apply_mat, cornerQ_isHermitian i j] at hm
    exact hm
  · intro h
    ext1
    rw [HermitianMat.conj_apply_mat, cornerQ_isHermitian i j]
    exact h

/-- The derivative of `t ↦ exp (t • A) x` at `0` is `A x`. -/
theorem exp_apply_hasDerivAt (A : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)
    (x : HermitianMat n ℂ) :
    HasDerivAt (fun t : ℝ => exp (t • A) x) (A x) 0 := by
  have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
  have hu : HasDerivAt (fun _ : ℝ => x) 0 (0 : ℝ) := hasDerivAt_const 0 x
  have hcomb := hc.clm_apply hu
  -- At v4.33 neither `rw` nor `simp only` matches the pre-formed `exp (0 • A)` slots in
  -- `hcomb`, so discharge the derivative value as an explicit equation instead.
  have hval : (exp ((0 : ℝ) • A) * A) x + (exp ((0 : ℝ) • A)) 0 = A x := by
    simp [show ((0 : ℝ) • A) = 0 from zero_smul ℝ A]
  exact hval ▸ hcomb

/-- **The differential preserves every corner** (u3): differentiate the invariance
of the corner under the character flow. With `dChi_kills_corner` (u4), the
differential-face geometry of `dχ` is complete. -/
theorem dChi_preserves_corner (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) {i j : n} {x : HermitianMat n ℂ}
    (hx : cornerJ2 i j x) :
    cornerJ2 i j (dChi P hS2 hjord r x) := by
  rw [← cornerConjCLM_eq_iff]
  have hcurve : ∀ t : ℝ, cornerConjCLM i j (exp (t • dChi P hS2 hjord r) x)
      = exp (t • dChi P hS2 hjord r) x := by
    intro t
    rw [cornerConjCLM_eq_iff]
    have hexp : exp (t • dChi P hS2 hjord r) = ((chiTilde P hS2 (t • r)).val) := by
      rw [← map_smul (dChi P hS2 hjord) t r]
      exact (chiTilde_eq_exp_dChi P hS2 hjord (t • r)).symm
    rw [hexp]
    exact chiTilde_preserves_cornerJ2 P hS2 hjord _ hx
  have hd := exp_apply_hasDerivAt (dChi P hS2 hjord r) x
  have hdL : HasDerivAt
      (fun t : ℝ => cornerConjCLM i j (exp (t • dChi P hS2 hjord r) x))
      (cornerConjCLM i j (dChi P hS2 hjord r x)) 0 := by
    -- Compose with the constant map directly; the `hasDerivAt_const .clm_apply` route leaves a
    -- `0 (…)` summand whose zero sits at a different instance path.
    exact (cornerConjCLM i j).hasFDerivAt.comp_hasDerivAt 0 hd
  rw [show (fun t : ℝ => cornerConjCLM i j (exp (t • dChi P hS2 hjord r) x))
      = fun t : ℝ => exp (t • dChi P hS2 hjord r) x from funext hcurve] at hdL
  exact hdL.unique hd

end Necessity
