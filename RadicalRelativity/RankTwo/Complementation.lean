/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.FrameFunction

set_option linter.style.longLine false

/-!
# Complementation invariance of the frame function  (LEDGER 5.3)

A rank-two Jordan frame is an *unordered* complementary pair `{P, 𝟙 − P}` of
rank-one projections, so the frame function must not distinguish a ray from its
orthogonal complement.  `MasterTheorem/RankTwo.lean` already proves
`tau_swap_invariant` (`τ(𝟙 − P, R) = τ(P, R)` when `tr R = 1`); this file
supplies the geometric half — that passing to the orthogonal complement ray *is*
the complementation `P ↦ 𝟙 − P` — and concludes that `τ` is a function of the
frame, not of the ray.

* `orthoVec` — the orthogonal complement vector in two dimensions,
  `(a, b) ↦ (−b̄, ā)`, with `orthoVec_orthogonal` and `nsq_orthoVec`.
* `rankOne_orthoVec` — **the geometric identity**: for a unit vector,
  `(orthoVec ψ)(orthoVec ψ)* = 𝟙 − ψψ*`.
* `tauVec_orthoVec` — hence `τ` is complementation invariant, so it descends to
  the space of unordered complementary pairs: the actual frame space.
-/

noncomputable section

open scoped Matrix

namespace RankTwo

/-! ## The complement vector in two dimensions -/

/-- The orthogonal complement vector of `(a, b)` in `ℂ²`, namely `(−b̄, ā)`. -/
def orthoVec (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![-(star (v 1)), star (v 0)]

@[simp] theorem orthoVec_zero (v : Fin 2 → ℂ) : orthoVec v 0 = -(star (v 1)) := rfl
@[simp] theorem orthoVec_one (v : Fin 2 → ℂ) : orthoVec v 1 = star (v 0) := rfl

/-- `orthoVec v` is orthogonal to `v`. -/
theorem orthoVec_orthogonal (v : Fin 2 → ℂ) : star v ⬝ᵥ orthoVec v = 0 := by
  rw [dotProduct, Fin.sum_univ_two]
  simp only [Pi.star_apply, orthoVec_zero, orthoVec_one]
  ring

/-- `orthoVec` is norm preserving. -/
theorem nsq_orthoVec (v : Fin 2 → ℂ) :
    HermitianMat.nsq (orthoVec v) = HermitianMat.nsq v := by
  unfold HermitianMat.nsq
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [orthoVec_zero, orthoVec_one, Complex.normSq_neg, Complex.star_def,
    Complex.normSq_conj]
  ring

/-- `orthoVec` commutes with real rescaling. -/
theorem orthoVec_real_smul (r : ℝ) (v : Fin 2 → ℂ) :
    orthoVec ((r : ℂ) • v) = (r : ℂ) • orthoVec v := by
  refine funext ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;>
    simp only [orthoVec_zero, orthoVec_one, Pi.smul_apply, smul_eq_mul,
      Complex.star_def, map_mul, Complex.conj_ofReal, mul_neg]

/-! ## The geometric identity -/

/-- **The complement ray is the complementary projection**: for a unit vector
`ψ` in `ℂ²`, `(orthoVec ψ)(orthoVec ψ)* = 𝟙 − ψψ*`.  Entrywise: the diagonal
entries swap (`|b|², |a|²` against `1 − |a|², 1 − |b|²`, equal since
`|a|² + |b|² = 1`) and the off-diagonal entries pick up the sign. -/
theorem rankOne_orthoVec {ψ : Fin 2 → ℂ} (hψ : HermitianMat.nsq ψ = 1) :
    HermitianMat.rankOne (orthoVec ψ) = 1 - HermitianMat.rankOne ψ := by
  have hsum : Complex.normSq (ψ 0) + Complex.normSq (ψ 1) = 1 := by
    unfold HermitianMat.nsq at hψ
    rwa [Fin.sum_univ_two] at hψ
  ext1
  rw [HermitianMat.rankOne_mat, HermitianMat.mat_sub, HermitianMat.mat_one,
    HermitianMat.rankOne_mat]
  have hsum' : (ψ 0).re * (ψ 0).re + (ψ 0).im * (ψ 0).im
      + ((ψ 1).re * (ψ 1).re + (ψ 1).im * (ψ 1).im) = 1 := by
    rw [← Complex.normSq_apply, ← Complex.normSq_apply]
    exact hsum
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply,
      Pi.star_apply, orthoVec_zero, orthoVec_one, Complex.star_def,
      map_neg, Complex.conj_conj, if_true, if_false, one_ne_zero, zero_ne_one] <;>
    apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im] <;>
    linarith [hsum']

/-! ## `τ` is a function of the frame -/

/-- **Complementation invariance of the frame function.**  Passing to the
orthogonal complement ray replaces the rank-one projection by its complement
(`rankOne_orthoVec`), and `τ` is invariant under that (`tau_swap_invariant`,
since `tr Rref = 1`).  So `τ` does not distinguish a ray from its complement —
it is a function of the unordered pair, i.e. of the **frame**. -/
theorem tau_orthoVec_eq {ψ : Fin 2 → ℂ} (hψ : HermitianMat.nsq ψ = 1) :
    MasterTheorem.RankTwo.tau (HermitianMat.rankOne (orthoVec ψ)).mat
        MasterTheorem.RankTwo.Rref
      = MasterTheorem.RankTwo.tau (HermitianMat.rankOne ψ).mat
        MasterTheorem.RankTwo.Rref := by
  have hR : (MasterTheorem.RankTwo.Rref.trace).re = 1 := by
    rw [MasterTheorem.RankTwo.Rref, Matrix.trace_fin_two]
    simp
  rw [rankOne_orthoVec hψ, HermitianMat.mat_sub, HermitianMat.mat_one]
  exact MasterTheorem.RankTwo.tau_swap_invariant _ _ hR

end RankTwo
