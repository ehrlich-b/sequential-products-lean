/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.CfcPoly
import RadicalRelativity.Hermitian.RCLikeGeneral

set_option linter.style.longLine false

/-!
# The square root is continuous on effects, over any `RCLike` field

`A ↦ A.cfc Real.sqrt` is continuous on the effect interval of `H_n(𝕜)`.

This is the last piece the real branch needs for its singular-effect extension, and
it is assembled entirely from field-general parts — **no C⋆-algebra machinery**,
which matters because Mathlib's `CStarAlgebra` class is complex by definition, so
the ℂ-only `HermitianMat.cfc_continuous` cannot be generalized (it routes through
`CStarMatrix d d ℂ`):

* an effect's spectrum lies in the compact `[0,1]`
  (`spectrum_subset_Icc_of_isEffect`, from the `𝕜`-general
  `eigenvalues_mem_Icc_of_effect`);
* Weierstrass gives polynomials uniformly near `√` on `[0,1]`;
* `A ↦ A.cfc p` is continuous for polynomials (`continuous_cfc_polynomial` — the
  functional calculus at a polynomial is a matrix polynomial);
* `norm_cfc_sub_le_of_sup_le'` turns the uniform scalar bound into a uniform matrix
  bound on the effect set;
* uniform approximation by continuous functions gives continuity.
-/

noncomputable section

open scoped Matrix
open OrderUnitSpace

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- An effect's spectrum lies in `[0,1]`. -/
theorem spectrum_subset_Icc_of_isEffect {A : HermitianMat n 𝕜} (hA : IsEffect A) :
    spectrum ℝ A.mat ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues A.H] at hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  exact eigenvalues_mem_Icc_of_effect hA.1 hA.2 i

/-- **The square root is continuous on the effect interval**, over any `RCLike`
field.  Assembled from Weierstrass, polynomial continuity of the functional
calculus, and the eigenvalue-norm bound — no C⋆ structure. -/
theorem continuousOn_cfc_sqrt_effects :
    ContinuousOn (fun A : HermitianMat n 𝕜 => A.cfc Real.sqrt)
      {A : HermitianMat n 𝕜 | IsEffect A} := by
  refine Metric.continuousOn_iff.mpr ?_
  intro A hA ε εpos
  -- pick a polynomial uniformly near `√` on `[0,1]`
  set c : ℝ := Real.sqrt (Fintype.card n) with hc
  have hcnn : 0 ≤ c := Real.sqrt_nonneg _
  set δ : ℝ := ε / (3 * (c + 1)) with hδ
  have hδpos : 0 < δ := by
    apply div_pos εpos
    have : (0 : ℝ) < c + 1 := by linarith
    linarith
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 Real.sqrt
    (Real.continuous_sqrt.continuousOn) δ hδpos
  -- the polynomial approximant is uniformly close to `√` in the matrix norm, on effects
  have hclose : ∀ B : HermitianMat n 𝕜, IsEffect B →
      ‖B.cfc (fun x => p.eval x) - B.cfc Real.sqrt‖ ≤ c * δ := by
    intro B hB
    exact norm_cfc_sub_le_of_sup_le' (spectrum_subset_Icc_of_isEffect hB)
      (le_of_lt hδpos) (fun x hx => le_of_lt (by simpa using hp x hx))
  -- and it is continuous in the matrix
  have hpc : Continuous (fun B : HermitianMat n 𝕜 => B.cfc (fun x => p.eval x)) :=
    continuous_cfc_polynomial p
  -- assemble the three-ε estimate
  have hcδ : c * δ ≤ ε / 3 := by
    have h1 : c * δ ≤ (c + 1) * δ := by nlinarith
    have h2 : (c + 1) * δ = ε / 3 := by
      rw [hδ]
      field_simp
    linarith
  obtain ⟨η, ηpos, hη⟩ := Metric.continuous_iff.mp hpc A (ε / 3) (by linarith)
  refine ⟨η, ηpos, ?_⟩
  intro B hB hdist
  calc dist (B.cfc Real.sqrt) (A.cfc Real.sqrt)
      ≤ dist (B.cfc Real.sqrt) (B.cfc (fun x => p.eval x))
        + dist (B.cfc (fun x => p.eval x)) (A.cfc (fun x => p.eval x))
        + dist (A.cfc (fun x => p.eval x)) (A.cfc Real.sqrt) := dist_triangle4 _ _ _ _
    _ < ε := by
        have e1 : dist (B.cfc Real.sqrt) (B.cfc (fun x => p.eval x)) ≤ c * δ := by
          rw [dist_eq_norm, ← norm_neg, neg_sub]
          exact hclose B hB
        have e2 : dist (B.cfc (fun x => p.eval x)) (A.cfc (fun x => p.eval x)) < ε / 3 :=
          hη B hdist
        have e3 : dist (A.cfc (fun x => p.eval x)) (A.cfc Real.sqrt) ≤ c * δ := by
          rw [dist_eq_norm]
          exact hclose A hA
        linarith

end HermitianMat
