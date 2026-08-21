/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockSkew

set_option linter.style.longLine false

/-!
# The differential is a Jordan derivation  (LEDGER 2.6, u6c)

`dχ(r)` satisfies the Leibniz rule for the Jordan product:

* `chiTilde_jordan` — **χ̃(r) preserves `∘`** at every parameter: compose the
  forward `thetaNorm_jordan` with the inverse `thetaNorm_symm_jordan` through
  the two-factor definition of χ̃.
* `exp_entry_hasDerivAt` — entry functions of a flow are differentiable with
  derivative the entry of the generator.
* `dChi_jordan_derivation` — **the Leibniz rule**: differentiate
  `χ̃(t•r)(x∘y) = χ̃(t•r)x ∘ χ̃(t•r)y` at `t = 0`.  The differentiation is
  done *entrywise in ℂ* (products and finite sums of scalar functions), which
  sidesteps the operator-topology diamond on nested `→L` spaces that blocks
  the curried-bilinear-CLM route.

This is the engine for the entry-map Leibniz rule (u6d): applied to
cross-block elements via `blockHerm_symmMul_blockHerm` it yields
`T_{ik}(zv) = T_{ij}(z)·v + z·T_{jk}(v)` and hence the phase cocycle
`t_{ik} = t_{ij} + t_{jk}`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace Topology NormedSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## χ̃ preserves the Jordan product -/

/-- **χ̃(r) is a Jordan automorphism** at every parameter `r`: the forward
factor by `thetaNorm_jordan`, the inverse factor by `thetaNorm_symm_jordan`. -/
theorem chiTilde_jordan (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) (x y : HermitianMat n ℂ) :
    (chiTilde P hS2 r).val (x.symmMul y)
      = ((chiTilde P hS2 r).val x).symmMul ((chiTilde P hS2 r).val y) := by
  have hval : ∀ w, (chiTilde P hS2 r).val w
      = thetaNorm P hS2 (diagFamily (r ⊓ 0))
          ((thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm w) := by
    intro w
    show (((thetaUnit P hS2 (r ⊓ 0)) * (thetaUnit P hS2 ((r ⊓ 0) - r))⁻¹).val) w = _
    rw [Units.val_mul, ContinuousLinearMap.mul_apply]
    show LinearMap.toContinuousLinearMap
      (thetaNorm P hS2 (diagFamily (r ⊓ 0))).toLinearMap
        (LinearMap.toContinuousLinearMap
          (thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm.toLinearMap w) = _
    rw [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_toContinuousLinearMap']
    rfl
  rw [hval, hval, hval, thetaNorm_symm_jordan P hS2 hjord _ x y]
  have hj := thetaNorm_jordan P hS2 hjord (diagFamily_posDef (r ⊓ 0))
    ((thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm x)
    ((thetaNorm P hS2 (diagFamily ((r ⊓ 0) - r))).symm y)
  simp only [jordanBilin_apply] at hj
  exact hj

/-- The exponential of the scaled differential preserves the Jordan product:
`exp(t•dχ(r)) = χ̃(t•r)` and χ̃ is a Jordan automorphism. -/
theorem exp_smul_dChi_symmMul (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) (t : ℝ) (u v : HermitianMat n ℂ) :
    exp (t • dChi P hS2 hjord r) (u.symmMul v)
      = (exp (t • dChi P hS2 hjord r) u).symmMul (exp (t • dChi P hS2 hjord r) v) := by
  have h1 : (chiTilde P hS2 (t • r)).val = exp (t • dChi P hS2 hjord r) := by
    rw [chiTilde_eq_exp_dChi P hS2 hjord (t • r), map_smul]
  rw [← h1]
  exact chiTilde_jordan P hS2 hjord (t • r) u v

/-! ## Entrywise differentiation of the flow -/

/-- Entry functions of a flow are differentiable, with derivative the entry of
the generator. -/
theorem exp_entry_hasDerivAt (A : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)
    (w : HermitianMat n ℂ) (a b : n) :
    HasDerivAt (fun t : ℝ => (exp (t • A) w).mat a b) ((A w).mat a b) 0 := by
  have h := (entryCLM (n := n) a b).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (exp_apply_hasDerivAt A w)
  have h2 : HasDerivAt (fun t : ℝ => entryCLM a b (exp (t • A) w))
      (entryCLM a b (A w)) 0 := h
  simpa only [entryCLM_apply] using h2

/-! ## The Leibniz rule -/

/-- **`dχ(r)` is a Jordan derivation** (u6c): differentiate the Jordan
automorphism property of `χ̃(t•r)` at `t = 0`, entrywise. -/
theorem dChi_jordan_derivation (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) (x y : HermitianMat n ℂ) :
    dChi P hS2 hjord r (x.symmMul y)
      = (dChi P hS2 hjord r x).symmMul y + x.symmMul (dChi P hS2 hjord r y) := by
  have h0 : exp ((0 : ℝ) • dChi P hS2 hjord r)
      = (1 : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) := by
    rw [show (0 : ℝ) • dChi P hS2 hjord r = 0 from zero_smul ℝ (dChi P hS2 hjord r)]
    exact exp_zero
  ext1
  ext a b
  -- the flow of x∘y, entrywise
  have hF : HasDerivAt
      (fun t : ℝ => (exp (t • dChi P hS2 hjord r) (x.symmMul y)).mat a b)
      ((dChi P hS2 hjord r (x.symmMul y)).mat a b) 0 :=
    exp_entry_hasDerivAt _ (x.symmMul y) a b
  -- the product form, entrywise: each summand by the scalar product rule
  have hprod : ∀ m : n, HasDerivAt
      (fun t : ℝ => (exp (t • dChi P hS2 hjord r) x).mat a m
        * (exp (t • dChi P hS2 hjord r) y).mat m b)
      ((dChi P hS2 hjord r x).mat a m * y.mat m b
        + x.mat a m * (dChi P hS2 hjord r y).mat m b) 0 := by
    intro m
    have h := (exp_entry_hasDerivAt (dChi P hS2 hjord r) x a m).mul
      (exp_entry_hasDerivAt (dChi P hS2 hjord r) y m b)
    simpa only [h0, ContinuousLinearMap.one_apply] using! h
  have hprod' : ∀ m : n, HasDerivAt
      (fun t : ℝ => (exp (t • dChi P hS2 hjord r) y).mat a m
        * (exp (t • dChi P hS2 hjord r) x).mat m b)
      ((dChi P hS2 hjord r y).mat a m * x.mat m b
        + y.mat a m * (dChi P hS2 hjord r x).mat m b) 0 := by
    intro m
    have h := (exp_entry_hasDerivAt (dChi P hS2 hjord r) y a m).mul
      (exp_entry_hasDerivAt (dChi P hS2 hjord r) x m b)
    simpa only [h0, ContinuousLinearMap.one_apply] using! h
  have hsum : HasDerivAt
      (fun t : ℝ =>
        (∑ m, (exp (t • dChi P hS2 hjord r) x).mat a m
          * (exp (t • dChi P hS2 hjord r) y).mat m b)
        + ∑ m, (exp (t • dChi P hS2 hjord r) y).mat a m
          * (exp (t • dChi P hS2 hjord r) x).mat m b)
      ((∑ m, ((dChi P hS2 hjord r x).mat a m * y.mat m b
          + x.mat a m * (dChi P hS2 hjord r y).mat m b))
        + ∑ m, ((dChi P hS2 hjord r y).mat a m * x.mat m b
          + y.mat a m * (dChi P hS2 hjord r x).mat m b)) 0 :=
    (HasDerivAt.fun_sum fun m _ => hprod m).add
      (HasDerivAt.fun_sum fun m _ => hprod' m)
  have hG := hsum.const_mul ((2 : ℂ)⁻¹)
  -- the two functions agree: χ̃ is a Jordan automorphism
  have hFG : (fun t : ℝ => (exp (t • dChi P hS2 hjord r) (x.symmMul y)).mat a b)
      = (fun t : ℝ => (2 : ℂ)⁻¹
        * ((∑ m, (exp (t • dChi P hS2 hjord r) x).mat a m
            * (exp (t • dChi P hS2 hjord r) y).mat m b)
          + ∑ m, (exp (t • dChi P hS2 hjord r) y).mat a m
            * (exp (t • dChi P hS2 hjord r) x).mat m b)) := by
    funext t
    rw [exp_smul_dChi_symmMul P hS2 hjord r t x y, HermitianMat.symmMul_toMat]
    simp [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, smul_eq_mul, mul_add]
  rw [hFG] at hF
  have huniq := hF.unique hG
  rw [huniq, HermitianMat.mat_add]
  simp only [Matrix.add_apply, HermitianMat.symmMul_toMat, Matrix.smul_apply,
    Matrix.mul_apply, smul_eq_mul, Finset.sum_add_distrib]
  ring

end Necessity
