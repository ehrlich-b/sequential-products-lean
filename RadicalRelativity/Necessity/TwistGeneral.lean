/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.TwistUniqueness
import RadicalRelativity.Necessity.ConjTransport

set_option linter.style.longLine false

/-!
# From the diagonal family to every invertible effect  (ℂ lane, item (i))

`sp_eq_twistSeq_diagFamily` gives the twist form at *diagonal* base points.
Every positive-definite effect is unitarily conjugate to one, so the general
case is transport:

* `diagFamily_log_eigenvalues` — the two diagonal spellings agree:
  `diagFamily (log ∘ eigenvalues) = diagonal ℂ eigenvalues` for a positive
  definite matrix (`Real.exp_log` on `Matrix.PosDef.eigenvalues_pos`).
* `eq_adU_diagFamily` — hence `a = Ad_U (diagFamily r)` with `U` the
  eigenvector unitary and `r = log ∘ eigenvalues`, by the vendored spectral
  theorem `eq_conj_diagonal`.
* `log_eigenvalues_nonpos` — for an *effect* the eigenvalues are `≤ 1`
  (`le_smul_one_imp_eigenvalues_le`), so `r ≤ 0` and the diagonal base point is
  itself an effect.
* `twistFactor_adU` — **unitary covariance of the twist factor**:
  `a^{1/2+it}` conjugates along `U` (`cfc_conj_unitary` on both real cfc legs).
* `sp_eq_twistSeq_of_posDef` — **the twist form at every invertible effect**,
  given the per-frame rate collapse in the conjugated frame.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The two diagonal spellings -/

/-- For a positive-definite matrix the log-spectrum reproduces the spectrum:
`diagFamily (log ∘ eigenvalues) = diagonal ℂ eigenvalues`. -/
theorem diagFamily_log_eigenvalues {a : HermitianMat n ℂ} (hbd : a.mat.PosDef) :
    diagFamily (fun i => Real.log (a.H.eigenvalues i))
      = HermitianMat.diagonal ℂ a.H.eigenvalues := by
  rw [diagFamily]
  congr 1
  funext i
  exact Real.exp_log (hbd.eigenvalues_pos i)

/-- **The spectral theorem, in the shape the ℂ lane consumes**: every Hermitian
matrix is `Ad_U` of a diagonal family with `r` its log-spectrum (positive
definiteness makes the log legitimate). -/
theorem eq_adU_diagFamily {a : HermitianMat n ℂ} (hbd : a.mat.PosDef) :
    a = adU (a.H.eigenvectorUnitary : Matrix n n ℂ)
        (diagFamily (fun i => Real.log (a.H.eigenvalues i))) := by
  rw [diagFamily_log_eigenvalues hbd]
  exact a.eq_conj_diagonal

/-- For an effect the eigenvalues are at most `1`, so the log-spectrum is
nonpositive and the diagonal base point is itself an effect. -/
theorem log_eigenvalues_nonpos {a : HermitianMat n ℂ} (ha : IsEffect a)
    (hbd : a.mat.PosDef) (i : n) :
    Real.log (a.H.eigenvalues i) ≤ 0 := by
  have hle : a ≤ (1 : ℝ) • (1 : HermitianMat n ℂ) := by
    rw [one_smul]
    exact le_of_le_of_eq ha.2 HermitianMat.ousUnit_eq_one
  have h1 : a.H.eigenvalues i ≤ 1 :=
    HermitianMat.le_smul_one_imp_eigenvalues_le a 1 hle i
  exact Real.log_nonpos (le_of_lt (hbd.eigenvalues_pos i)) h1

/-! ## Unitary covariance of the twist factor -/

/-- **The twist factor conjugates along a unitary**:
`(Ad_U a)^{1/2+it} = U · a^{1/2+it} · Uᴴ`.  Both real functional-calculus legs
transport by `cfc_conj_unitary`. -/
theorem twistFactor_adU (a : HermitianMat n ℂ)
    (U : Matrix.unitaryGroup n ℂ) (t : ℝ) :
    HermitianMat.twistFactor (adU (U : Matrix n n ℂ) a) t
      = (U : Matrix n n ℂ) * HermitianMat.twistFactor a t
        * ((U : Matrix n n ℂ))ᴴ := by
  have hUa : adU (U : Matrix n n ℂ) a = a.conj (U : Matrix n n ℂ) := rfl
  have hre : HermitianMat.twistRe (adU (U : Matrix n n ℂ) a) t
      = (HermitianMat.twistRe a t).conj (U : Matrix n n ℂ) := by
    rw [hUa, HermitianMat.twistRe, HermitianMat.twistRe]
    exact HermitianMat.cfc_conj_unitary a _ U
  have him : HermitianMat.twistIm (adU (U : Matrix n n ℂ) a) t
      = (HermitianMat.twistIm a t).conj (U : Matrix n n ℂ) := by
    rw [hUa, HermitianMat.twistIm, HermitianMat.twistIm]
    exact HermitianMat.cfc_conj_unitary a _ U
  rw [HermitianMat.twistFactor, hre, him, HermitianMat.conj_apply_mat,
    HermitianMat.conj_apply_mat, HermitianMat.twistFactor]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- Matrix-form restatement of `twistFactor_adU` (no `unitaryGroup` coercion in
the statement, so callers never need to rewrite `U` by a term containing `U`). -/
theorem twistFactor_adU_mat (a : HermitianMat n ℂ) {U : Matrix n n ℂ}
    (hU' : U * Uᴴ = 1) (t : ℝ) :
    HermitianMat.twistFactor (adU U a) t
      = U * HermitianMat.twistFactor a t * Uᴴ := by
  have hmem : U ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hU'
  have hco : ((⟨U, hmem⟩ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) = U := rfl
  have h := twistFactor_adU a ⟨U, hmem⟩ t
  rw [hco] at h
  exact h

/-! ## Transport to a general invertible effect -/

/-- **Transport.**  If a product conjugated by `U` has the twist form at the
diagonal family `diagFamily r`, then the original product has it at
`a = Ad_U (diagFamily r)`: the conjugations cancel and the twist factor is
carried back by unitary covariance (`twistFactor_adU`).

The unitary is a parameter, so the statement stays cheap to elaborate; the
caller instantiates it at the eigenvector unitary via `eq_adU_diagFamily`. -/
theorem sp_eq_twistSeq_transport {N : ℕ}
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {r : Fin N → ℝ} {a : HermitianMat (Fin N) ℂ}
    (hadiag : a = adU U (diagFamily r)) (t : ℝ)
    (hform : ∀ b' : HermitianMat (Fin N) ℂ, IsEffect b' →
      (conjProduct P hU hU').sp (diagFamily r) b'
        = HermitianMat.twistSeq t (diagFamily r) b')
    {b : HermitianMat (Fin N) ℂ} (hb : IsEffect b) :
    P.sp a b = HermitianMat.twistSeq t a b := by
  have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hU'
  have hUU' : Uᴴ * (Uᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hU
  have hcancelU : ∀ x : HermitianMat (Fin N) ℂ, adU U (adU Uᴴ x) = x := by
    intro x
    rw [adU, adU, HermitianMat.conj_conj, hU']
    exact HermitianMat.conj_one x
  have hdiag := hform _ (adU_isEffect hUU hUU' hb)
  rw [conjProduct_sp, hcancelU b, ← hadiag] at hdiag
  have hgoal := congrArg (adU U) hdiag
  rw [hcancelU (P.sp a b)] at hgoal
  rw [hgoal, HermitianMat.twistSeq, HermitianMat.twistSeq, adU, adU,
    HermitianMat.conj_conj, HermitianMat.conj_conj]
  congr 1
  rw [hadiag, twistFactor_adU_mat (diagFamily r) hU' t, Matrix.mul_assoc]

end Necessity
