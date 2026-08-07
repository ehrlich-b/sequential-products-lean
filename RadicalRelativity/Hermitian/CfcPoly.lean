/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit

set_option linter.style.longLine false

/-!
# The functional calculus at polynomials, over any `RCLike` field

`A.cfc p` for a polynomial `p` is just the matrix polynomial `p(A)`, so it is
**manifestly continuous in `A`** — no C⋆-algebra machinery involved.

This is the field-general replacement for the ℂ-only `HermitianMat.cfc_continuous`,
whose proof routes through `ContinuousOn.cfc` at `CStarMatrix d d ℂ` and therefore
cannot generalize: Mathlib's `CStarAlgebra` class is *complex by definition*
(`extends … NormedAlgebra ℂ A`), so real matrices are simply not an instance.

Together with the (already `𝕜`-general) bound `norm_cfc_sub_le_of_sup_le` and
Stone–Weierstrass on a compact spectrum window, these give continuity of
`A ↦ A.cfc f` for continuous `f` over any `RCLike 𝕜` — which is what the real
branch needs for its singular-effect extension.

* `mat_cfc_pow` — `(A.cfc (·^k)).mat = A.mat ^ k`.
* `continuous_cfc_pow` — hence `A ↦ A.cfc (·^k)` is continuous.
* `continuous_cfc_polynomial` — and so is `A ↦ A.cfc (p.eval ·)` for any `p`.
-/

noncomputable section

open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The functional calculus at a monomial is a matrix power. -/
theorem mat_cfc_pow (A : HermitianMat n 𝕜) (k : ℕ) :
    (A.cfc (fun x => x ^ k)).mat = A.mat ^ k := by
  induction k with
  | zero =>
    have h : (fun x : ℝ => x ^ 0) = (fun _ : ℝ => (1 : ℝ)) := by
      funext x; simp
    rw [h, HermitianMat.cfc_const, HermitianMat.mat_smul, HermitianMat.mat_one,
      one_smul]
    symm
    simp
  | succ k ih =>
    have hsplit : (fun x : ℝ => x ^ (k + 1)) = (fun x : ℝ => x ^ k * x) := by
      funext x; rw [pow_succ]
    rw [hsplit, HermitianMat.mat_cfc_mul_apply, ih, HermitianMat.cfc_id', pow_succ]

/-- Matrix powers are continuous in the matrix, so the functional calculus at a
monomial is continuous — with no appeal to the C⋆ structure. -/
theorem continuous_cfc_pow (k : ℕ) :
    Continuous (fun A : HermitianMat n 𝕜 => A.cfc (fun x => x ^ k)) := by
  apply Continuous.subtype_mk
  have h : (fun A : HermitianMat n 𝕜 => ((A.cfc (fun x => x ^ k)).mat))
      = fun A : HermitianMat n 𝕜 => (A.mat) ^ k := by
    funext A
    exact mat_cfc_pow A k
  show Continuous fun A : HermitianMat n 𝕜 => ((A.cfc (fun x => x ^ k)).mat)
  rw [h]
  exact (continuous_subtype_val).pow k

/-- **The functional calculus at any polynomial is continuous in the matrix.**  This
is the manifestly-continuous approximating family the real branch uses in place of
the complex-only `cfc_continuous`. -/
theorem continuous_cfc_polynomial (p : Polynomial ℝ) :
    Continuous (fun A : HermitianMat n 𝕜 => A.cfc (fun x => p.eval x)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h : (fun A : HermitianMat n 𝕜 => A.cfc (fun x => (p + q).eval x))
        = fun A : HermitianMat n 𝕜 =>
          A.cfc (fun x => p.eval x) + A.cfc (fun x => q.eval x) := by
      funext A
      rw [← HermitianMat.cfc_add_apply]
      congr 1
      funext x
      rw [Polynomial.eval_add]
    rw [h]
    exact hp.add hq
  | monomial k c =>
    apply Continuous.subtype_mk
    have h : (fun A : HermitianMat n 𝕜 =>
          (A.cfc (fun x => (Polynomial.monomial k c).eval x)).mat)
        = fun A : HermitianMat n 𝕜 => c • (A.mat ^ k) := by
      funext A
      have hfun : (fun x : ℝ => (Polynomial.monomial k c).eval x)
          = fun x : ℝ => c * x ^ k := by
        funext x
        rw [Polynomial.eval_monomial]
      rw [hfun, HermitianMat.mat_cfc_mul_apply, HermitianMat.cfc_const,
        HermitianMat.mat_smul, HermitianMat.mat_one, mat_cfc_pow, Matrix.smul_mul,
        one_mul]
    show Continuous fun A : HermitianMat n 𝕜 =>
      (A.cfc (fun x => (Polynomial.monomial k c).eval x)).mat
    rw [h]
    exact ((continuous_subtype_val).pow k).const_smul c

/-! ## `cfc` at a polynomial IS the matrix polynomial -/

/-- **`(A.cfc p).mat = p(A)`** — the functional calculus at a polynomial is literally the
matrix polynomial, `Polynomial.aeval` of the matrix.  This is the bridge any argument
needs that transfers a property from matrix polynomials to the functional calculus
(e.g. invariance under an algebra involution). -/
theorem mat_cfc_polynomial (A : HermitianMat n 𝕜) (p : Polynomial ℝ) :
    (A.cfc (fun x => p.eval x)).mat
      = Polynomial.aeval A.mat (p.map (algebraMap ℝ 𝕜)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hfun : (fun x : ℝ => (p + q).eval x)
        = (fun x : ℝ => p.eval x + q.eval x) := by
      funext x
      rw [Polynomial.eval_add]
    rw [hfun, HermitianMat.cfc_add_apply, HermitianMat.mat_add, hp, hq,
      Polynomial.map_add, map_add]
  | monomial k c =>
    have hfun : (fun x : ℝ => (Polynomial.monomial k c).eval x)
        = (fun x : ℝ => c * x ^ k) := by
      funext x
      rw [Polynomial.eval_monomial]
    rw [hfun, HermitianMat.mat_cfc_mul_apply, HermitianMat.cfc_const,
      HermitianMat.mat_smul, HermitianMat.mat_one, mat_cfc_pow]
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial]
    rw [Matrix.smul_mul, one_mul]
    rw [Algebra.smul_def]
    congr 1

end HermitianMat
