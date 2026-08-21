/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Vendor.HermitianMat.Order
import RadicalRelativity.Vendor.HermitianMat.CFC

set_option linter.style.longLine false

/-!
# `RCLike`-general restatements of five `ℂ`-only vendored lemmas

Upstream physlib states five results about `HermitianMat` at the complex field only.
First-party code in this repo is uniform in `RCLike 𝕜` — and in one case
(`RadicalRelativity/Necessity/RealRigidity.lean`) the carrier is genuinely `ℝ`, which
no `ℂ`-only statement can serve at all. This file restates those five at `RCLike 𝕜`
generality, under primed names.

Nothing about the mathematics forces the narrowing. Both enabling results are already
`𝕜`-general upstream:

* `Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff` (`Vendor/Matrix.lean:425`) for the
  two order/eigenvalue bounds — so those proofs are the same one-liners;
* `HermitianMat.norm_eq_sum_eigenvalues_sq` (`Vendor/HermitianMat/CFC.lean:283`) for the
  three functional-calculus norm bounds, which go through the eigenvalue sum and never
  touch the C⋆-algebra structure (Mathlib's `CStarAlgebra` is complex by definition, so
  routing through it is exactly what would have forced `ℂ`).

## Why this file exists rather than a patch to the vendor

The same generalization was previously applied **in place**, inside the vendored files
(commits 8ac68ca for the order pair, 084412e for the functional-calculus trio). The
2026-08-21 re-vendor of the physlib island pulled upstream verbatim and silently wiped
both — 084412e carrying no annotation of any kind, so only a declaration-signature diff
against the previous pin recovered it. See `RadicalRelativity/Vendor/VENDOR.md`.

Keeping these restatements here, in first-party code that imports the island rather than
edits it, lets `RadicalRelativity/Vendor/` stay byte-verbatim upstream across future
bumps: a re-vendor becomes a pure re-pull with no patch-reapplication step, and a
generalization can no longer disappear without a compile error pointing at it.

## Naming

The primed names (`…'`) deliberately differ from the vendored `ℂ`-only originals, which
still exist and are still used inside the island. `Necessity/TwistGeneral.lean` and
`Hermitian/Symplectic.lean` are genuinely complex and keep calling the unprimed vendored
versions.
-/

noncomputable section

open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Order-unit eigenvalue bounds, uniform in `𝕜` -/

/-- If a Hermitian matrix is bounded by `M • 1`, all its eigenvalues are at most `M`.

`RCLike 𝕜`-general form of the vendored `ℂ`-only `le_smul_one_imp_eigenvalues_le`. -/
theorem le_smul_one_imp_eigenvalues_le' (A : HermitianMat n 𝕜) (M : ℝ)
    (h : A ≤ M • (1 : HermitianMat n 𝕜)) (i : n) :
    A.H.eigenvalues i ≤ M :=
  (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff A.H M).mpr h i

open MatrixOrder in
/-- If all eigenvalues of a Hermitian matrix are at most `M`, it is bounded by `M • 1`.

`RCLike 𝕜`-general form of the vendored `ℂ`-only `eigenvalues_le_imp_le_smul_one`. -/
theorem eigenvalues_le_imp_le_smul_one' (A : HermitianMat n 𝕜) (M : ℝ)
    (h : ∀ i, A.H.eigenvalues i ≤ M) :
    A ≤ M • (1 : HermitianMat n 𝕜) :=
  (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff A.H M).mp h

/-! ### Functional-calculus norm bounds, uniform in `𝕜`

Proofs lifted from the pre-re-vendor tree (commit 084412e), where they were already
written at `RCLike 𝕜`. -/

section CFC

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Bound the Frobenius norm of a functional calculus application.

`RCLike 𝕜`-general form of the vendored `ℂ`-only `norm_cfc_le_sqrt_card_mul_bound`. -/
lemma norm_cfc_le_sqrt_card_mul_bound' {A : HermitianMat d 𝕜} {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x ∈ spectrum ℝ A.mat, ‖f x‖ ≤ C) :
    ‖A.cfc f‖ ≤ Real.sqrt (Fintype.card d) * C := by
  rw [ ← Real.sqrt_sq ( norm_nonneg _ ) ];
  -- Recall that the Frobenius norm of a Hermitian matrix is the square root of the sum of the squares of its eigenvalues.
  have h_frobenius_eigenvalues : ∀ (M : HermitianMat d 𝕜), ‖M‖ ^ 2 = ∑ i ∈ Finset.univ, (M.H.eigenvalues i) ^ 2 := by
    exact fun M => norm_eq_sum_eigenvalues_sq M;
  -- Applying the bound on the eigenvalues to the Frobenius norm.
  have h_bound : ∑ i ∈ Finset.univ, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ (Fintype.card d) * C ^ 2 := by
    have h_bound : ∀ i, ((A.cfc f).H.eigenvalues i) ^ 2 ≤ C ^ 2 := by
      intro i
      have h_eigenvalue_bound : |(A.cfc f).H.eigenvalues i| ≤ C := by
        obtain ⟨ x, hx, hx' ⟩ : (A.cfc f).H.eigenvalues i ∈ f '' spectrum ℝ A.mat := by
          have h_bound := (A.cfc f).H.eigenvalues_mem_spectrum_real i
          rwa [spectrum_cfc_eq_image A f] at h_bound
        specialize hf x hx
        aesop;
      nlinarith only [ abs_le.mp h_eigenvalue_bound ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => h_bound _ ) ( by simp );
  rw [ h_frobenius_eigenvalues, Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg ( Fintype.card d : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg ( Fintype.card d ) ) ]

/-- The norm of the difference of two functional calculus applications is bounded by
`sqrt(d)` times the sup norm of the difference of the functions.

`RCLike 𝕜`-general form of the vendored `ℂ`-only `norm_cfc_sub_cfc_le_sqrt_card`. -/
lemma norm_cfc_sub_cfc_le_sqrt_card' {A : HermitianMat d 𝕜} {f g : ℝ → ℝ} :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖ := by
  rw [ ← HermitianMat.cfc_sub ];
  refine' le_trans ( norm_cfc_le_sqrt_card_mul_bound' _ _ ) _;
  exact ⨆ x ∈ spectrum ℝ A.mat, ‖f x - g x‖;
  · exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _;
  · intro x hx
    apply le_csSup;
    · -- The supremum of a finite set of real numbers is finite.
      have h_finite : Set.Finite (spectrum ℝ A.mat) := by
        exact Set.toFinite _;
      obtain ⟨ M, hM ⟩ := h_finite.exists_finset_coe;
      refine' ⟨ ∑ x ∈ M, ‖f x - g x‖, Set.forall_mem_range.2 fun x => _ ⟩;
      rw [ ← hM ];
      rw [ @ciSup_eq_ite ];
      split_ifs <;> [ exact Finset.single_le_sum ( fun x _ => norm_nonneg ( f x - g x ) ) ( by assumption ) ; exact le_trans ( by norm_num ) ( Finset.sum_nonneg fun x _ => norm_nonneg ( f x - g x ) ) ];
    · exact ⟨ x, by aesop ⟩;
  · rfl

/-- If `f` and `g` are close on `T`, and the spectrum of `A` is in `T`, then `A.cfc f` and
`A.cfc g` are close.

`RCLike 𝕜`-general form of the vendored `ℂ`-only `norm_cfc_sub_le_of_sup_le`. -/
lemma norm_cfc_sub_le_of_sup_le' {A : HermitianMat d 𝕜} {f g : ℝ → ℝ} {T : Set ℝ} {ε : ℝ}
    (hT : spectrum ℝ A.mat ⊆ T) (hε : 0 ≤ ε) (h_sup : ∀ x ∈ T, ‖f x - g x‖ ≤ ε) :
    ‖A.cfc f - A.cfc g‖ ≤ Real.sqrt (Fintype.card d) * ε := by
  refine' le_trans ( norm_cfc_sub_cfc_le_sqrt_card' ) _;
  gcongr;
  refine' ciSup_le fun x => _;
  exact Real.iSup_le (fun i => h_sup x (hT i)) hε

end CFC

end HermitianMat
