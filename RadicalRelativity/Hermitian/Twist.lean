/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit
import Mathlib.Data.Matrix.Mul

set_option linter.style.longLine false

/-!
# The twist sequential product on H_n(ℂ)  (campaign LEDGER 1.2)

Route decision (LEDGER 1.2, 2026-08-04): **pair-of-real-cfc**.  Mathlib has no
complex-power functional calculus for positive elements, so `a^{1/2+it}` is built
from two applications of the vendored real functional calculus:

  `twistFactor a t := cfc(√x · cos(t·log x)) + i · cfc(√x · sin(t·log x))`,

a plain (non-Hermitian) matrix.  At an eigenvalue `0` every component is
`√0 · (…) = 0`, so the paper's spectral convention `0^{1/2±it} = 0` holds
*definitionally* — the junk value `Real.log 0 = 0` is multiplied away.

The twist sequential product is then

  `twistSeq t a b := a^{1/2+it} · b · a^{1/2-it} = b.conj (twistFactor a t)`

through the vendored `HermitianMat.conj`, which is an `AddMonoidHom` in the
conjugated argument — so S1-additivity (`twistSeq_add_right`), monotonicity
(`twistSeq_mono_right`), positivity (`twistSeq_nonneg`), and effect closure
(`twistSeq_isEffect`) ride the vendored `conj` lemmas directly.

## Main results

* `twistFactor_conjTranspose` — `(a^{1/2+it})ᴴ = a^{1/2-it}`.
* `twistFactor_mul_conjTranspose` / `conjTranspose_mul_twistFactor` — for
  `0 ≤ a`, `X·Xᴴ = Xᴴ·X = a` (the Pythagorean cancellation, via
  `cfc_self_commute` and `cfc_congr_of_nonneg`).
* `twistFactor_one` — `1^{1/2+it} = 1`.
* Unit laws `twistSeq_one_right` (`a &ₜ 1 = a`, S3-dual) and
  `twistSeq_one_left` (`1 &ₜ b = b`, the paper's S3).
* `twistSeq_zero` — `t = 0` recovers the Lüders product `√a · b · √a`.

The S1–S7 verification proper is LEDGER 1.3, building on these.
-/

noncomputable section

open ComplexOrder
-- NB: opened before `namespace HermitianMat` — see LEDGER H6 (the vendored island
-- declares names under `HermitianMat.Matrix`, which would shadow this scope).
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real component of `a^{1/2+it}`: `cfc(√x · cos(t · log x))`. -/
def twistRe (a : HermitianMat n ℂ) (t : ℝ) : HermitianMat n ℂ :=
  a.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)

/-- Imaginary component of `a^{1/2+it}`: `cfc(√x · sin(t · log x))`. -/
def twistIm (a : HermitianMat n ℂ) (t : ℝ) : HermitianMat n ℂ :=
  a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)

/-- The twist factor `a^{1/2+it}`, a plain (non-Hermitian) matrix. -/
def twistFactor (a : HermitianMat n ℂ) (t : ℝ) : Matrix n n ℂ :=
  (twistRe a t).mat + Complex.I • (twistIm a t).mat

/-- **The twist sequential product** `a &ₜ b := a^{1/2+it} · b · a^{1/2-it}`,
Hermitian by construction (a `conj`). -/
def twistSeq (t : ℝ) (a b : HermitianMat n ℂ) : HermitianMat n ℂ :=
  b.conj (twistFactor a t)

theorem twistRe_neg (a : HermitianMat n ℂ) (t : ℝ) : twistRe a (-t) = twistRe a t := by
  unfold twistRe
  congr 1
  funext x
  rw [neg_mul, Real.cos_neg]

theorem twistIm_neg (a : HermitianMat n ℂ) (t : ℝ) : twistIm a (-t) = -(twistIm a t) := by
  unfold twistIm
  rw [← cfc_neg_apply]
  congr 1
  funext x
  rw [neg_mul, Real.sin_neg, mul_neg]

/-- `(a^{1/2+it})ᴴ = a^{1/2-it}`. -/
theorem twistFactor_conjTranspose (a : HermitianMat n ℂ) (t : ℝ) :
    (twistFactor a t)ᴴ = twistFactor a (-t) := by
  unfold twistFactor
  rw [twistRe_neg, twistIm_neg, mat_neg, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, (twistRe a t).H, (twistIm a t).H]
  simp [Complex.star_def, Complex.conj_I]

/-- The twist components commute (same functional-calculus family). -/
theorem twistRe_mul_twistIm_comm (a : HermitianMat n ℂ) (t : ℝ) :
    (twistIm a t).mat * (twistRe a t).mat = (twistRe a t).mat * (twistIm a t).mat :=
  (cfc_self_commute a _ _).eq.symm

/-- Pythagorean recomposition: `C² + S² = a` for `0 ≤ a`. -/
theorem twistRe_sq_add_twistIm_sq (a : HermitianMat n ℂ) (ha : 0 ≤ a) (t : ℝ) :
    (twistRe a t).mat * (twistRe a t).mat + (twistIm a t).mat * (twistIm a t).mat
      = a.mat := by
  unfold twistRe twistIm
  rw [← mat_cfc_mul_apply, ← mat_cfc_mul_apply, ← mat_add, ← cfc_add_apply]
  have key : a.cfc (fun x =>
      Real.sqrt x * Real.cos (t * Real.log x) * (Real.sqrt x * Real.cos (t * Real.log x)) +
      Real.sqrt x * Real.sin (t * Real.log x) * (Real.sqrt x * Real.sin (t * Real.log x))) = a := by
    have heq : Set.EqOn (fun x =>
        Real.sqrt x * Real.cos (t * Real.log x) * (Real.sqrt x * Real.cos (t * Real.log x)) +
        Real.sqrt x * Real.sin (t * Real.log x) * (Real.sqrt x * Real.sin (t * Real.log x)))
        (fun x => x) (Set.Ici 0) := by
      intro x hx
      have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
      calc Real.sqrt x * Real.cos (t * Real.log x) * (Real.sqrt x * Real.cos (t * Real.log x)) +
            Real.sqrt x * Real.sin (t * Real.log x) * (Real.sqrt x * Real.sin (t * Real.log x))
          = Real.sqrt x * Real.sqrt x *
              (Real.cos (t * Real.log x) ^ 2 + Real.sin (t * Real.log x) ^ 2) := by ring
        _ = x := by rw [hs, Real.cos_sq_add_sin_sq, mul_one]
    calc a.cfc _ = a.cfc (fun x => x) := cfc_congr_of_nonneg ha heq
      _ = a := cfc_id' a
  rw [key]

/-- For `0 ≤ a`: `a^{1/2+it} · a^{1/2-it} = a`. -/
theorem twistFactor_mul_conjTranspose {a : HermitianMat n ℂ} (ha : 0 ≤ a) (t : ℝ) :
    twistFactor a t * (twistFactor a t)ᴴ = a.mat := by
  rw [twistFactor_conjTranspose]
  unfold twistFactor
  rw [twistRe_neg, twistIm_neg, mat_neg]
  have hCS := twistRe_mul_twistIm_comm a t
  set C := (twistRe a t).mat with hC
  set S := (twistIm a t).mat with hS
  have hIS : (Complex.I • S) * C = C * (Complex.I • S) := by
    rw [Matrix.smul_mul, hCS, Matrix.mul_smul]
  have hVV : (Complex.I • S) * (Complex.I • S) = -(S * S) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]
  calc (C + Complex.I • S) * (C + Complex.I • -S)
      = (C + Complex.I • S) * (C - Complex.I • S) := by
        rw [smul_neg, ← sub_eq_add_neg]
    _ = C * C - C * (Complex.I • S) + ((Complex.I • S) * C -
          (Complex.I • S) * (Complex.I • S)) := by
        rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    _ = C * C + S * S := by rw [hIS, hVV]; abel
    _ = a.mat := twistRe_sq_add_twistIm_sq a ha t

/-- For `0 ≤ a`: `a^{1/2-it} · a^{1/2+it} = a`. -/
theorem conjTranspose_mul_twistFactor {a : HermitianMat n ℂ} (ha : 0 ≤ a) (t : ℝ) :
    (twistFactor a t)ᴴ * twistFactor a t = a.mat := by
  calc (twistFactor a t)ᴴ * twistFactor a t
      = twistFactor a (-t) * (twistFactor a (-t))ᴴ := by
        rw [twistFactor_conjTranspose, twistFactor_conjTranspose, neg_neg]
    _ = a.mat := twistFactor_mul_conjTranspose ha (-t)

/-- `1^{1/2+it} = 1`. -/
theorem twistFactor_one (t : ℝ) : twistFactor (1 : HermitianMat n ℂ) t = 1 := by
  unfold twistFactor twistRe twistIm
  rw [cfc_apply_one, cfc_apply_one]
  simp [Real.log_one, Real.sqrt_one]

@[simp]
theorem twistSeq_mat (t : ℝ) (a b : HermitianMat n ℂ) :
    (twistSeq t a b).mat = twistFactor a t * b.mat * (twistFactor a t)ᴴ :=
  conj_apply_mat _ _

/-- The twist product of positive arguments is positive (in `b`). -/
theorem twistSeq_nonneg (t : ℝ) (a : HermitianMat n ℂ) {b : HermitianMat n ℂ}
    (hb : 0 ≤ b) : 0 ≤ twistSeq t a b :=
  conj_nonneg _ hb

/-- S1 (additivity in the second argument) holds on all of `H_n(ℂ)`. -/
theorem twistSeq_add_right (t : ℝ) (a b c : HermitianMat n ℂ) :
    twistSeq t a (b + c) = twistSeq t a b + twistSeq t a c :=
  map_add (conj (twistFactor a t)) b c

/-- The twist product is monotone in the second argument. -/
theorem twistSeq_mono_right (t : ℝ) (a : HermitianMat n ℂ) {b c : HermitianMat n ℂ}
    (h : b ≤ c) : twistSeq t a b ≤ twistSeq t a c :=
  conj_mono h

/-- `a &ₜ 𝟙 = a` for `0 ≤ a` (the dual unit law). -/
theorem twistSeq_one_right {a : HermitianMat n ℂ} (ha : 0 ≤ a) (t : ℝ) :
    twistSeq t a 1 = a := by
  ext1
  rw [twistSeq_mat, mat_one, Matrix.mul_one, twistFactor_mul_conjTranspose ha]

/-- `𝟙 &ₜ b = b` (the paper's S3). -/
theorem twistSeq_one_left (t : ℝ) (b : HermitianMat n ℂ) :
    twistSeq t 1 b = b := by
  ext1
  rw [twistSeq_mat, twistFactor_one]
  simp

/-- Effect closure: the twist product of effects is an effect. -/
theorem twistSeq_isEffect (t : ℝ) {a b : HermitianMat n ℂ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ twistSeq t a b ∧ twistSeq t a b ≤ 1 := by
  refine ⟨twistSeq_nonneg t a hb0, ?_⟩
  calc twistSeq t a b ≤ twistSeq t a 1 := twistSeq_mono_right t a hb1
    _ = a := twistSeq_one_right ha0 t
    _ ≤ 1 := ha1

/-- At `t = 0` the twist factor is `√a` — no positivity hypothesis needed: the
component functions agree everywhere. -/
theorem twistFactor_zero (a : HermitianMat n ℂ) :
    twistFactor a 0 = (a.cfc Real.sqrt).mat := by
  unfold twistFactor twistRe twistIm
  have hcos : a.cfc (fun x => Real.sqrt x * Real.cos (0 * Real.log x)) = a.cfc Real.sqrt := by
    congr 1
    funext x
    rw [zero_mul, Real.cos_zero, mul_one]
  have hsin : a.cfc (fun x => Real.sqrt x * Real.sin (0 * Real.log x)) = a.cfc fun _ => 0 := by
    congr 1
    funext x
    rw [zero_mul, Real.sin_zero, mul_zero]
  rw [hcos, hsin, cfc_const]
  simp

/-- **`t = 0` is the Lüders product**: `twistSeq 0 a b = √a · b · √a`. -/
theorem twistSeq_zero (a b : HermitianMat n ℂ) :
    twistSeq 0 a b = b.conj (a.cfc Real.sqrt).mat := by
  unfold twistSeq
  rw [twistFactor_zero]

end HermitianMat
