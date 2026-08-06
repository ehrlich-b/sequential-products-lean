/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockAngle
import RadicalRelativity.Hermitian.Twist

set_option linter.style.longLine false

/-!
# The torus factor IS `a^{it}`: the literal twist form  (ℂ-lane closure)

Sequel to `Necessity/TwistIdentification.lean` (which produced
`χ̃(r) = Ad_{U_t(r)}`) and `Necessity/BlockAngle.lean` (which fired it).

The identification chain ends at `sp_eq_quadRep_torus`:
`a • b = Q_{√a}(Ad_{U_t(r)} b)` with `U_t(r) = diag(e^{i t r_k})`.  The paper's
conclusion is stated with the *matrix power* `a^{1/2+it}` (M1's `twistFactor`).
This file closes the gap, which is pure spectral bookkeeping because the
character parameter is already the log-spectrum: `diagFamily r = diag(e^{r_k})`.

* `twistFactor_diagFamily` — **`√a · U_t(r) = a^{1/2+it}`** entrywise on the
  diagonal family: `√(e^{r_k})·(cos(t r_k) + i sin(t r_k)) = √(e^{r_k})e^{i t r_k}`
  (`Real.log_exp` supplies `log(e^{r_k}) = r_k`, `Complex.exp_mul_I` the polar
  form).  No `cfc` multiplicativity and no spectral theorem.
* `sp_eq_twistSeq_diagFamily` — **the paper's conclusion shape on the diagonal
  family**: for any S1–S7 product with S2 whose phase rates collapse to a single
  `t`, `a • b = a^{1/2+it} b a^{1/2−it}` = M1's `twistSeq t a b`, for every
  effect `b`.  The comparison-map hypothesis is discharged internally
  (`chiTilde_of_nonpos` + `thetaNorm_apply_eq_theta`), so the only inputs are
  S2, the M3 Jordan property, and the rate collapse.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The torus factor is the matrix power -/

/-- The scalar polar identity behind the diagonal computation, stated with the
`Complex.ofReal` coercion; the carrier's `RCLike.ofReal` coercion is defeq to it,
so `exact` bridges the two spellings where `rw`/`ring` cannot. -/
theorem ofReal_polar (s x : ℝ) :
    ((s * Real.cos x : ℝ) : ℂ) + Complex.I * ((s * Real.sin x : ℝ) : ℂ)
      = ((s : ℝ) : ℂ) * Complex.exp (((x : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- **`√a · U_t(r) = a^{1/2+it}` on the diagonal family.**  Both sides are
diagonal; entry `k` is `√(e^{r_k})·e^{i t r_k}` because the character parameter
`r` is the log-spectrum of `diagFamily r`. -/
theorem twistFactor_diagFamily (r : n → ℝ) (t : ℝ) :
    HermitianMat.twistFactor (diagFamily r) t
      = ((diagFamily r).cfc Real.sqrt).mat * torusU t r := by
  rw [HermitianMat.twistFactor, HermitianMat.twistRe, HermitianMat.twistIm,
    diagFamily]
  rw [HermitianMat.cfc_diagonal, HermitianMat.cfc_diagonal,
    HermitianMat.cfc_diagonal]
  rw [HermitianMat.diagonal_mat, HermitianMat.diagonal_mat,
    HermitianMat.diagonal_mat]
  rw [torusU, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    simp only [Function.comp_apply, Real.log_exp, smul_eq_mul]
    exact ofReal_polar _ _
  · rw [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab,
      Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab]
    simp

/-! ## The paper's conclusion shape on the diagonal family -/

/-- **The complex conclusion, literally.**  For an S1–S7 sequential product with
S2 on `H_N(ℂ)` (`N ≥ 3`) whose block phase rates collapse to a single `t`, the
product on the diagonal family is the Liu–Wu twist
`a • b = a^{1/2+it} b a^{1/2−it}` — M1's `twistSeq t`. -/
theorem sp_eq_twistSeq_diagFamily {N : ℕ}
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (t : ℝ) {r : Fin N → ℝ} (hr : ∀ i, r i ≤ 0)
    (hcollapse : ∀ i j : Fin N, i ≠ j →
      tvalLm P hS2 hjord i j r = t * (r i - r j))
    {b : HermitianMat (Fin N) ℂ} (hb : IsEffect b) :
    P.sp (diagFamily r) b = HermitianMat.twistSeq t (diagFamily r) b := by
  have ha : IsEffect (diagFamily r) := diagFamily_isEffect hr
  have hbd : (diagFamily r).mat.PosDef := diagFamily_posDef r
  -- the comparison map at this base point IS the character at `r`
  have hθ : ((theta P ha hbd :
        HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ))
      = ((chiTilde P hS2 r).val :
        HermitianMat (Fin N) ℂ →ₗ[ℝ] HermitianMat (Fin N) ℂ) := by
    rw [chiTilde_of_nonpos P hS2 hr]
    apply LinearMap.ext
    intro x
    show theta P ha hbd x = _
    rw [← thetaNorm_apply_eq_theta P hS2 ha hbd x]
    rfl
  rw [sp_eq_quadRep_torus P hS2 hjord ha hbd t r hθ hcollapse hb]
  show (b.conj (torusU t r)).conj ((diagFamily r).cfc Real.sqrt).mat = b.conj _
  rw [HermitianMat.conj_conj, ← twistFactor_diagFamily r t]

end Necessity
