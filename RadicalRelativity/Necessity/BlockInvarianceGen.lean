/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.CoalescenceDiffGen

set_option linter.style.longLine false

/-!
# Block invariance of the character and its differential  (LEDGER 2.6, u3)

The corner `J₂(q)` is invariant under the whole lane:

* `cornerJ2_iff_symmMul` — corner membership is the Jordan eigenrelation
  `q ∘ x = x` (forward by absorption, backward by `cornerJ2_of_doubleG`).
* `thetaNorm_preserves_cornerJ2G` / inverse / `chiTilde_preserves_cornerJ2G` —
  Θ fixes `q` (diagonal commutation) and preserves `∘` (the M3 hypothesis), so
  it preserves the eigenrelation; the inverse inherits both properties.
* `dChi_preserves_cornerG` — differentiate: `L(exp(t·dχ)x) ≡ exp(t·dχ)x` for the
  corner-conjugation `L`, so the derivatives at `0` agree, i.e.
  `L(dχ(r)x) = dχ(r)x`.

With u4 (`dChi_kills_cornerG`) this completes the differential-face geometry:
`dχ(r)` preserves every corner and kills the coalesced ones.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace Topology NormedSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
variable (P : SequentialProductOn (HermitianMat n 𝕜))

/-! ## The corner as a Hermitian element and the Jordan eigenrelation -/

theorem cornerQ_isHermitianG (i j : n) : (cornerQG 𝕜 i j).IsHermitian := by
  show _ᴴ = _
  unfold cornerQG
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  by_cases h : k = i ∨ k = j <;> simp [h]

/-- The corner projection as a Hermitian matrix. -/
def cornerHermG (i j : n) : HermitianMat n 𝕜 := ⟨cornerQG 𝕜 i j, cornerQ_isHermitianG i j⟩

@[simp]
theorem cornerHerm_matG (i j : n) : (cornerHermG i j).mat = cornerQG 𝕜 i j := rfl

/-- Forward: corner membership gives the Jordan eigenrelation `q ∘ x = x`. -/
theorem cornerHerm_symmMul_of_J2G {i j : n} {x : HermitianMat n 𝕜}
    (hx : cornerJ2G i j x) : (cornerHermG i j).symmMul x = x := by
  ext1
  rw [HermitianMat.symmMul_toMat, cornerHerm_matG,
    (cornerJ2_absorbG hx).1, (cornerJ2_absorbG hx).2]
  rw [← two_smul 𝕜 x.mat, smul_smul]
  norm_num

/-- Backward: the Jordan eigenrelation gives corner membership. -/
theorem cornerJ2_of_symmMulG {i j : n} {x : HermitianMat n 𝕜}
    (h : (cornerHermG i j).symmMul x = x) : cornerJ2G i j x := by
  apply cornerJ2_of_doubleG
  have hmat := congrArg HermitianMat.mat h
  rw [HermitianMat.symmMul_toMat] at hmat
  have h2 := congrArg (fun M => (2 : 𝕜) • M) hmat
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:𝕜) ≠ 0), one_smul] at h2
  exact h2

/-- The diagonal family commutes with every corner projection. -/
theorem diagFamilyG_commute_cornerQ (s : n → ℝ) (i j : n) :
    Commute (diagFamilyG 𝕜 s).mat (cornerQG 𝕜 i j) := by
  show _ * _ = _ * _
  rw [diagFamilyG_mat]
  unfold cornerQG
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  ring

/-! ## Θ, its inverse, and χ̃ preserve corners -/

theorem thetaNorm_fixes_cornerHermG (hS2 : P.FirstArgContinuous) (s : n → ℝ) (i j : n) :
    thetaNormG P hS2 (diagFamilyG 𝕜 s) (cornerHermG i j) = cornerHermG i j :=
  thetaNorm_fix_of_commuteG P hS2 (diagFamilyG_posDef s) (diagFamilyG_commute_cornerQ s i j)

theorem thetaNorm_preserves_cornerJ2G (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (s : n → ℝ) {i j : n} {x : HermitianMat n 𝕜}
    (hx : cornerJ2G i j x) :
    cornerJ2G i j (thetaNormG P hS2 (diagFamilyG 𝕜 s) x) := by
  apply cornerJ2_of_symmMulG
  have hj := thetaNorm_jordanG P hS2 hjord (diagFamilyG_posDef s) (cornerHermG i j) x
  simp only [jordanBilin_applyG] at hj
  calc (cornerHermG i j).symmMul (thetaNormG P hS2 (diagFamilyG 𝕜 s) x)
      = (thetaNormG P hS2 (diagFamilyG 𝕜 s) (cornerHermG i j)).symmMul
          (thetaNormG P hS2 (diagFamilyG 𝕜 s) x) := by
        rw [thetaNorm_fixes_cornerHermG P hS2 s i j]
    _ = thetaNormG P hS2 (diagFamilyG 𝕜 s) ((cornerHermG i j).symmMul x) := hj.symm
    _ = thetaNormG P hS2 (diagFamilyG 𝕜 s) x := by
        rw [cornerHerm_symmMul_of_J2G hx]

/-- The inverse of a Jordan-preserving linear equivalence is Jordan-preserving. -/
theorem thetaNorm_symm_jordanG (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (s : n → ℝ) (u v : HermitianMat n 𝕜) :
    (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (u.symmMul v)
      = ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm u).symmMul
        ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm v) := by
  apply (thetaNormG P hS2 (diagFamilyG 𝕜 s)).injective
  have hj := thetaNorm_jordanG P hS2 hjord (diagFamilyG_posDef s)
    ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm u)
    ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm v)
  simp only [jordanBilin_applyG] at hj
  rw [LinearEquiv.apply_symm_apply, hj,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem thetaNorm_symm_preserves_cornerJ2G (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (s : n → ℝ) {i j : n} {x : HermitianMat n 𝕜}
    (hx : cornerJ2G i j x) :
    cornerJ2G i j ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm x) := by
  apply cornerJ2_of_symmMulG
  have hfixsym : (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (cornerHermG i j)
      = cornerHermG i j := by
    calc (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (cornerHermG i j)
        = (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm
            (thetaNormG P hS2 (diagFamilyG 𝕜 s) (cornerHermG i j)) := by
          rw [thetaNorm_fixes_cornerHermG P hS2 s i j]
      _ = cornerHermG i j := LinearEquiv.symm_apply_apply _ _
  calc (cornerHermG i j).symmMul ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm x)
      = ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm (cornerHermG i j)).symmMul
          ((thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm x) := by rw [hfixsym]
    _ = (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm ((cornerHermG i j).symmMul x) :=
        (thetaNorm_symm_jordanG P hS2 hjord s _ _).symm
    _ = (thetaNormG P hS2 (diagFamilyG 𝕜 s)).symm x := by
        rw [cornerHerm_symmMul_of_J2G hx]

/-- χ̃ preserves every corner. -/
theorem chiTilde_preserves_cornerJ2G (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} {x : HermitianMat n 𝕜}
    (hx : cornerJ2G i j x) :
    cornerJ2G i j ((chiTildeG P hS2 r).val x) := by
  show cornerJ2G i j
    (((thetaUnitG P hS2 (r ⊓ 0)) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val x)
  rw [Units.val_mul, ContinuousLinearMap.mul_apply]
  have hinv : cornerJ2G i j (((thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val x) := by
    show cornerJ2G i j (LinearMap.toContinuousLinearMap
      (thetaNormG P hS2 (diagFamilyG 𝕜 ((r ⊓ 0) - r))).symm.toLinearMap x)
    rw [LinearMap.coe_toContinuousLinearMap']
    exact thetaNorm_symm_preserves_cornerJ2G P hS2 hjord _ hx
  show cornerJ2G i j (LinearMap.toContinuousLinearMap
    (thetaNormG P hS2 (diagFamilyG 𝕜 (r ⊓ 0))).toLinearMap _)
  rw [LinearMap.coe_toContinuousLinearMap']
  exact thetaNorm_preserves_cornerJ2G P hS2 hjord _ hinv

/-! ## The differential preserves corners -/

/-- The corner conjugation `x ↦ q x q` as a continuous linear map. -/
def cornerConjCLMG (𝕜 : Type*) [RCLike 𝕜] (i j : n) :
    HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜 :=
  LinearMap.toContinuousLinearMap (HermitianMat.conjLinear ℝ (cornerQG 𝕜 i j))

theorem cornerConjCLM_eq_iffG {i j : n} {x : HermitianMat n 𝕜} :
    cornerConjCLMG 𝕜 i j x = x ↔ cornerJ2G i j x := by
  have happ : cornerConjCLMG 𝕜 i j x = HermitianMat.conjLinear ℝ (cornerQG 𝕜 i j) x := by
    unfold cornerConjCLMG
    rw [LinearMap.coe_toContinuousLinearMap']
  rw [happ, HermitianMat.conjLinear_apply]
  constructor
  · intro h
    have hm := congrArg HermitianMat.mat h
    rw [HermitianMat.conj_apply_mat, cornerQ_isHermitianG i j] at hm
    exact hm
  · intro h
    ext1
    rw [HermitianMat.conj_apply_mat, cornerQ_isHermitianG i j]
    exact h

/-- The derivative of `t ↦ exp (t • A) x` at `0` is `A x`. -/
theorem exp_apply_hasDerivAtG (A : HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜)
    (x : HermitianMat n 𝕜) :
    HasDerivAt (fun t : ℝ => exp (t • A) x) (A x) 0 := by
  have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
  have hu : HasDerivAt (fun _ : ℝ => x) 0 (0 : ℝ) := hasDerivAt_const 0 x
  have hcomb := hc.clm_apply hu
  -- At v4.33 neither `rw` nor `simp only` matches the pre-formed `exp (0 • A)` slots in
  -- `hcomb`, so discharge the derivative value as an explicit equation instead.
  have hval : (exp ((0 : ℝ) • A) * A) x + (exp ((0 : ℝ) • A)) 0 = A x := by
    rw [zero_smul, exp_zero]
    simp
  exact hval ▸ hcomb

/-- **The differential preserves every corner** (u3): differentiate the invariance
of the corner under the character flow. With `dChi_kills_cornerG` (u4), the
differential-face geometry of `dχ` is complete. -/
theorem dChi_preserves_cornerG (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} {x : HermitianMat n 𝕜}
    (hx : cornerJ2G i j x) :
    cornerJ2G i j (dChiG P hS2 hjord r x) := by
  rw [← cornerConjCLM_eq_iffG]
  have hcurve : ∀ t : ℝ, cornerConjCLMG 𝕜 i j (exp (t • dChiG P hS2 hjord r) x)
      = exp (t • dChiG P hS2 hjord r) x := by
    intro t
    rw [cornerConjCLM_eq_iffG]
    have hexp : exp (t • dChiG P hS2 hjord r) = ((chiTildeG P hS2 (t • r)).val) := by
      rw [← map_smul (dChiG P hS2 hjord) t r]
      exact (chiTilde_eq_exp_dChiG P hS2 hjord (t • r)).symm
    rw [hexp]
    exact chiTilde_preserves_cornerJ2G P hS2 hjord _ hx
  have hd := exp_apply_hasDerivAtG (dChiG P hS2 hjord r) x
  have hdL : HasDerivAt
      (fun t : ℝ => cornerConjCLMG 𝕜 i j (exp (t • dChiG P hS2 hjord r) x))
      (cornerConjCLMG 𝕜 i j (dChiG P hS2 hjord r x)) 0 := by
    -- Compose with the constant map directly. Going via `hasDerivAt_const .clm_apply` leaves a
    -- `0 (…)` summand whose zero sits at a different instance path, which at v4.33 neither
    -- `rw` nor `simp` can reduce.
    exact (cornerConjCLMG 𝕜 i j).hasFDerivAt.comp_hasDerivAt 0 hd
  rw [show (fun t : ℝ => cornerConjCLMG 𝕜 i j (exp (t • dChiG P hS2 hjord r) x))
      = fun t : ℝ => exp (t • dChiG P hS2 hjord r) x from funext hcurve] at hdL
  exact hdL.unique hd

end Necessity
