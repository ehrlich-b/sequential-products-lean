/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.ExtremeEffects

set_option linter.style.longLine false

/-!
# Real rank-one projections  (the ℝ bridge to real Kadison, part 1)

`prop:real` carries one hypothesis: the **Jordan property** of the comparison map, i.e. real
Kadison.  Real Wigner rigidity (`Wigner/RealWigner.lean`) is the classical input to
that, and this file starts the bridge between them.

**Route decision, recorded because the alternative looks cheaper and is not.**  The ℂ lane
bridges Wigner to Kadison across five files (`RayMap` → `WignerBridge` → `RankOneSpan` →
`JordanWitness` → `KadisonDischarge`).  Those are written at ℂ and use `rankOne` / `tprob` /
`nsq`, which are defined at ℂ in `ProjectionOrder` and `StrengthProbe` with **60 uses of
`Complex.normSq` in one file** and eleven downstream consumers, several of them finished and
banked (`RankTwo/*`, `TwistUniqueness`).  Generalizing those primitives in place would
destabilize completed rows for no gain, so the ℝ bridge is written **natively at ℝ** instead.
Two things make the native route genuinely cheaper, not merely safer:

* over ℝ, `star = id`, so all the conjugation bookkeeping disappears;
* over ℝ there is **no antiunitary branch** — real Wigner produces an orthogonal map, and
  conjugation by an orthogonal matrix is already a Jordan automorphism, so the ℂ lane's
  `transposeMap` half of `JordanWitness` has no ℝ counterpart.

This file supplies the object everything else is phrased in terms of:

* `rankOneR ψ` — the projection `ψψᵀ`, with `rankOneR_isProjection` for unit `ψ`.
* `trace_rankOneR_mul` — the trace pairing against `ψψᵀ` is the quadratic form `ψᵀ y ψ`.
  This is what makes rank-one projections a *separating* family, hence the span argument.
* `trace_rankOneR_mul_rankOneR` — the overlap of two rank-ones is `(ψ ⬝ᵥ φ)²`, i.e. exactly
  the real transition probability.  Over ℝ there is no modulus to take.
-/

noncomputable section

open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rank-one matrix `ψψᵀ` as a Hermitian (here: symmetric) matrix. -/
def rankOneR (ψ : n → ℝ) : HermitianMat n ℝ :=
  ⟨Matrix.vecMulVec ψ ψ, by
    show _ᴴ = _
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]⟩

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem rankOneR_mat (ψ : n → ℝ) :
    (rankOneR ψ).mat = Matrix.vecMulVec ψ ψ := rfl

omit [DecidableEq n] in
/-- The matrix product of two rank-ones factors through the overlap. -/
theorem vecMulVec_mul_vecMulVec (ψ φ : n → ℝ) :
    Matrix.vecMulVec ψ ψ * Matrix.vecMulVec φ φ
      = (ψ ⬝ᵥ φ) • Matrix.vecMulVec ψ φ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `ψψᵀ` is idempotent for a unit vector. -/
theorem rankOneR_isProjection {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) :
    (rankOneR ψ).IsProjection := by
  rw [HermitianMat.isProjection_iff_mat_mul_self, rankOneR_mat,
    vecMulVec_mul_vecMulVec, hψ, one_smul]

omit [DecidableEq n] in
/-- **The trace pairing against `ψψᵀ` is the quadratic form.**  Hence a matrix is determined
by its quadratic form on all vectors, which is the separation the span argument runs on. -/
theorem trace_rankOneR_mul (ψ : n → ℝ) (y : Matrix n n ℝ) :
    Matrix.trace ((rankOneR ψ).mat * y) = ψ ⬝ᵥ (y *ᵥ ψ) := by
  simp only [rankOneR_mat, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq n] in
/-- **The overlap of two rank-one projections is the real transition probability.**  Over ℝ
the numerator is literally a square — no modulus — which is the same reason the real
rigidity's residual freedom is a sign rather than a phase. -/
theorem trace_rankOneR_mul_rankOneR (ψ φ : n → ℝ) :
    Matrix.trace ((rankOneR ψ).mat * (rankOneR φ).mat) = (ψ ⬝ᵥ φ) ^ 2 := by
  rw [rankOneR_mat, rankOneR_mat, vecMulVec_mul_vecMulVec, Matrix.trace_smul,
    Matrix.trace_vecMulVec, smul_eq_mul, sq]

omit [Fintype n] [DecidableEq n] in
/-- Rescaling scales the rank-one quadratically, so the RAY determines the projection up to
a positive factor. -/
theorem rankOneR_smul (c : ℝ) (ψ : n → ℝ) :
    rankOneR (c • ψ) = (c ^ 2) • rankOneR ψ := by
  apply HermitianMat.ext
  ext i j
  show (c • ψ) i * (c • ψ) j = c ^ 2 * (ψ i * ψ j)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Necessity
