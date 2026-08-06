/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.Resolution

set_option linter.style.longLine false

/-!
# Square roots multiply on commuting positives, over any `RCLike` field

`√(ab) = √a · √b` for commuting positive semidefinite `a, b`, stated over an
arbitrary `RCLike 𝕜`.

The ℂ development gets this as the `t = 0` case of
`HermitianMat.twistFactor_mul_of_commute` (`Hermitian/Sequential.lean`), but
`twistFactor` is *intrinsically* complex (`twistRe + Complex.I • twistIm`), so the
real branch cannot reuse it. What the twist proof actually uses is the joint
spectral family of two commuting Hermitian matrices, and that scaffolding is
field-generic — it rides `Hermitian/Resolution.lean`. This file keeps the
scaffolding, drops the complex structure, and needs only the scalar identity
`√(μν) = √μ·√ν`.

Mathlib has no square-root multiplicativity for commuting positive matrices
(checked 2026-08-06), so this is from scratch.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Square roots multiply on commuting positives**: if `a, b ≥ 0` commute and
`m = ab`, then `√m = √a · √b`. Proved through the joint spectral family of `a`
and `b`; the only scalar input is `Real.sqrt_mul`. -/
theorem sqrt_mul_of_commute {a b m : HermitianMat n 𝕜} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hab : Commute a.mat b.mat) (hm : m.mat = a.mat * b.mat) :
    (m.cfc Real.sqrt).mat = (a.cfc Real.sqrt).mat * (b.cfc Real.sqrt).mat := by
  classical
  have hPQ : ∀ μ ν : ℝ, Commute (a.specProj μ).mat (b.specProj ν).mat :=
    fun μ ν => cfc_commute _ _ hab
  -- the joint family over pairs of eigenvalues is a resolution
  have hidem : ∀ q ∈ a.eigFinset ×ˢ b.eigFinset,
      ((a.specProj q.1).mat * (b.specProj q.2).mat) *
        ((a.specProj q.1).mat * (b.specProj q.2).mat)
      = (a.specProj q.1).mat * (b.specProj q.2).mat := by
    rintro ⟨μ, ν⟩ -
    rw [(hPQ μ ν).symm.mul_mul_mul_comm, specProj_mul_self, specProj_mul_self]
  have horth : ∀ q ∈ a.eigFinset ×ˢ b.eigFinset, ∀ q' ∈ a.eigFinset ×ˢ b.eigFinset, q ≠ q' →
      ((a.specProj q.1).mat * (b.specProj q.2).mat) *
        ((a.specProj q'.1).mat * (b.specProj q'.2).mat) = 0 := by
    rintro ⟨μ, ν⟩ - ⟨μ', ν'⟩ - hne
    rw [(hPQ μ' ν).symm.mul_mul_mul_comm]
    by_cases hμ : μ = μ'
    · subst hμ
      have hν : ν ≠ ν' := fun h => hne (by rw [h])
      rw [specProj_mul_orth b hν, mul_zero]
    · rw [specProj_mul_orth a hμ, zero_mul]
  have hsum : ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
      (a.specProj q.1).mat * (b.specProj q.2).mat = 1 := by
    rw [Finset.sum_product]
    calc ∑ μ ∈ a.eigFinset, ∑ ν ∈ b.eigFinset, (a.specProj μ).mat * (b.specProj ν).mat
        = ∑ μ ∈ a.eigFinset, (a.specProj μ).mat * ∑ ν ∈ b.eigFinset, (b.specProj ν).mat :=
          Finset.sum_congr rfl fun μ _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [sum_specProj_mat b]; simp only [mul_one]; exact sum_specProj_mat a
  -- products of component expansions land on the joint family
  have hmix : ∀ x y : ℝ → ℝ,
      (∑ μ ∈ a.eigFinset, x μ • (a.specProj μ).mat) *
        (∑ ν ∈ b.eigFinset, y ν • (b.specProj ν).mat)
      = ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
          (x q.1 * y q.2) • ((a.specProj q.1).mat * (b.specProj q.2).mat) := by
    intro x y
    rw [Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hM : m.mat = ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
      (q.1 * q.2) • ((a.specProj q.1).mat * (b.specProj q.2).mat) := by
    rw [hm, ← sum_smul_specProj_mat a, ← sum_smul_specProj_mat b]
    exact hmix _ _
  -- NB: left unannotated deliberately (see `twistFactor_mul_of_commute`) — ascribing
  -- the beta-reduced type makes the unifier grind through `specProj` bodies.
  have hres := fun (f : ℝ → ℝ) => mat_cfc_of_resolution hidem horth hsum hM f
  -- the single scalar identity: `√(μν) = √μ · √ν` on the joint spectrum
  rw [hres Real.sqrt, mat_cfc_eq_sum_specProj a, mat_cfc_eq_sum_specProj b, hmix _ _]
  apply Finset.sum_congr rfl
  rintro ⟨μ, ν⟩ hq
  obtain ⟨hμ, hν⟩ := Finset.mem_product.mp hq
  rw [Real.sqrt_mul (eigFinset_nonneg ha μ hμ)]

end HermitianMat
