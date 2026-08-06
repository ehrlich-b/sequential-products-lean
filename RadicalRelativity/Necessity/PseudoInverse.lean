/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.SharpEffects

set_option linter.style.longLine false

/-!
# Pseudo-inverses and order reflection  (campaign LEDGER 2.1e, vdW Prop 4.19–4.20)

For a positive-definite effect `b` on `H_n(𝕜)` and an arbitrary S1–S7+S2 product:

* `pseudoInv b` — the normalized spectral pseudo-inverse
  `ν := ∑_μ (c/μ) • specProj b μ` over `b`'s eigenvalue family, with the
  normalization `c := ∏_μ μ` chosen so that `ν` is an effect with NO nonemptiness
  case split (`c ≤ μ` because the remaining factors lie in `(0,1]`).
* `sp_pseudoInv_eq_smul_one` — `ν ◦' b = b ◦' ν = c•1`: both are diagonal in one
  orthogonal family, so the 2.1d value law computes them.
* `sp_pseudoInv_cancel` — `ν ◦' (b ◦' x) = c•x` on effects, by S5 through the
  family compatibility, then first-argument homogeneity and S3.
* `seqLeftMul_pseudoInv_comp` — the same at the linear-map level:
  `L'_ν ∘ L'_b = c·id`, extended from effects by `span_isEffect_eq_top`.
* `seqLeftMul_reflectsNonneg` / `seqLeftMul_injective` — **the payoff** (vdW 4.19,
  matrix-concrete): for positive-definite `b`, the left multiplication of the
  unknown product is order-REFLECTING and injective.  This is the hard half of
  `Θ_orderIso` in the Θ assembly (2.1f).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Spectral data of an effect, at the HermitianMat level -/

theorem specProj_isProjection (b : HermitianMat n 𝕜) (μ : ℝ) :
    (b.specProj μ).IsProjection :=
  HermitianMat.isProjection_iff_mat_mul_self.mpr (HermitianMat.specProj_mul_self b μ)

theorem sum_smul_specProj (b : HermitianMat n 𝕜) :
    ∑ μ ∈ b.eigFinset, μ • b.specProj μ = b := by
  ext1
  rw [mat_finsetSum]
  simpa using HermitianMat.sum_smul_specProj_mat b

theorem sum_specProj (b : HermitianMat n 𝕜) :
    ∑ μ ∈ b.eigFinset, b.specProj μ = 1 := by
  ext1
  rw [mat_finsetSum]
  simpa using HermitianMat.sum_specProj_mat b

theorem eigFinset_le_one {b : HermitianMat n 𝕜} (hb : b ≤ 1) :
    ∀ μ ∈ b.eigFinset, μ ≤ 1 := by
  intro μ hμ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hμ
  exact HermitianMat.le_smul_one_imp_eigenvalues_le b 1 (by simpa using hb) i

theorem eigFinset_pos {b : HermitianMat n 𝕜} (hbd : b.mat.PosDef) :
    ∀ μ ∈ b.eigFinset, 0 < μ := by
  intro μ hμ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hμ
  exact hbd.eigenvalues_pos i

/-! ## The normalized pseudo-inverse -/

/-- The normalization constant: the product of the eigenvalues.  For an effect it
lies in `(0, μ]` for every eigenvalue `μ`, with no nonemptiness hypothesis. -/
def pseudoInvCoef (b : HermitianMat n 𝕜) : ℝ := ∏ μ ∈ b.eigFinset, μ

/-- The normalized spectral pseudo-inverse `∑_μ (c/μ) • P_μ`. -/
def pseudoInv (b : HermitianMat n 𝕜) : HermitianMat n 𝕜 :=
  ∑ μ ∈ b.eigFinset, (pseudoInvCoef b / μ) • b.specProj μ

variable {b : HermitianMat n 𝕜}

theorem pseudoInvCoef_pos (hbd : b.mat.PosDef) : 0 < pseudoInvCoef b :=
  Finset.prod_pos (eigFinset_pos hbd)

theorem pseudoInvCoef_le (hb : IsEffect b) (hbd : b.mat.PosDef) :
    ∀ μ ∈ b.eigFinset, pseudoInvCoef b ≤ μ := by
  intro μ hμ
  have h := Finset.prod_le_one (s := b.eigFinset.erase μ)
    (fun i hi => le_of_lt (eigFinset_pos hbd i (Finset.mem_of_mem_erase hi)))
    (fun i hi => eigFinset_le_one hb.2 i (Finset.mem_of_mem_erase hi))
  have hsplit : pseudoInvCoef b = μ * ∏ i ∈ b.eigFinset.erase μ, i :=
    (Finset.mul_prod_erase b.eigFinset id hμ).symm
  rw [hsplit]
  calc μ * ∏ i ∈ b.eigFinset.erase μ, i ≤ μ * 1 := by
        apply mul_le_mul_of_nonneg_left h (le_of_lt (eigFinset_pos hbd μ hμ))
    _ = μ := mul_one μ

theorem pseudoInvCoef_le_one (hb : IsEffect b) : pseudoInvCoef b ≤ 1 :=
  Finset.prod_le_one (fun i hi => HermitianMat.eigFinset_nonneg hb.1 i hi)
    (fun i hi => eigFinset_le_one hb.2 i hi)

theorem pseudoInvCoef_div_nonneg (hbd : b.mat.PosDef) :
    ∀ μ ∈ b.eigFinset, 0 ≤ pseudoInvCoef b / μ := fun μ hμ =>
  div_nonneg (le_of_lt (pseudoInvCoef_pos hbd)) (le_of_lt (eigFinset_pos hbd μ hμ))

theorem pseudoInvCoef_div_le_one (hb : IsEffect b) (hbd : b.mat.PosDef) :
    ∀ μ ∈ b.eigFinset, pseudoInvCoef b / μ ≤ 1 := fun μ hμ =>
  (div_le_one (eigFinset_pos hbd μ hμ)).mpr (pseudoInvCoef_le hb hbd μ hμ)

theorem pseudoInv_isEffect (hb : IsEffect b) (hbd : b.mat.PosDef) :
    IsEffect (pseudoInv b) := by
  rw [pseudoInv]
  exact sum_smul_proj_isEffect (p := fun μ => b.specProj μ)
    (fun μ _ => specProj_isProjection b μ)
    (fun _ _ _ _ hμν => HermitianMat.specProj_mul_orth b hμν)
    (pseudoInvCoef_div_nonneg hbd) (pseudoInvCoef_div_le_one hb hbd)

/-! ## The pseudo-inverse identity `ν ◦' b = c•1` -/

variable (P : SequentialProductOn (HermitianMat n 𝕜))

/-- The 2.1d value law computes `ν ◦' b`: it is the scalar `c = pseudoInvCoef b`. -/
theorem sp_pseudoInv_eq_smul_one (hS2 : P.FirstArgContinuous) (hb : IsEffect b)
    (hbd : b.mat.PosDef) :
    P.sp (pseudoInv b) b = pseudoInvCoef b • 1 := by
  have hval := sp_orthFamily_value P hS2 (p := fun μ => b.specProj μ)
    (fun μ _ => specProj_isProjection b μ)
    (fun _ _ _ _ hμν => HermitianMat.specProj_mul_orth b hμν)
    (pseudoInvCoef_div_nonneg hbd) (pseudoInvCoef_div_le_one hb hbd)
    (fun μ hμ => HermitianMat.eigFinset_nonneg hb.1 μ hμ) (eigFinset_le_one hb.2)
  rw [sum_smul_specProj b] at hval
  rw [pseudoInv, hval]
  rw [show (∑ μ ∈ b.eigFinset, (pseudoInvCoef b / μ * μ) • b.specProj μ)
      = ∑ μ ∈ b.eigFinset, pseudoInvCoef b • b.specProj μ from
    Finset.sum_congr rfl fun μ hμ => by
      rw [div_mul_cancel₀ _ (ne_of_gt (eigFinset_pos hbd μ hμ))]]
  rw [← Finset.smul_sum, sum_specProj]

/-- The reverse order, by the 2.1d compatibility transfer. -/
theorem sp_pseudoInv_comm (hS2 : P.FirstArgContinuous) (hb : IsEffect b)
    (hbd : b.mat.PosDef) :
    P.sp (pseudoInv b) b = P.sp b (pseudoInv b) := by
  have hcomm := sp_orthFamily_comm P hS2 (p := fun μ => b.specProj μ)
    (fun μ _ => specProj_isProjection b μ)
    (fun _ _ _ _ hμν => HermitianMat.specProj_mul_orth b hμν)
    (pseudoInvCoef_div_nonneg hbd) (pseudoInvCoef_div_le_one hb hbd)
    (fun μ hμ => HermitianMat.eigFinset_nonneg hb.1 μ hμ) (eigFinset_le_one hb.2)
  rw [sum_smul_specProj b] at hcomm
  rw [pseudoInv]
  exact hcomm

/-- **The cancellation identity** `ν ◦' (b ◦' x) = c•x` on effects, by S5 through
the family compatibility, first-argument homogeneity, and S3. -/
theorem sp_pseudoInv_cancel (hS2 : P.FirstArgContinuous) (hb : IsEffect b)
    (hbd : b.mat.PosDef) {x : HermitianMat n 𝕜} (hx : IsEffect x) :
    P.sp (pseudoInv b) (P.sp b x) = pseudoInvCoef b • x := by
  have hν : IsEffect (pseudoInv b) := pseudoInv_isEffect hb hbd
  have hassoc := P.sp_assoc_of_compatible hν hb hx (sp_pseudoInv_comm P hS2 hb hbd)
  rw [hassoc, sp_pseudoInv_eq_smul_one P hS2 hb hbd]
  have h1eff : IsEffect (1 : HermitianMat n 𝕜) := isEffect_unit
  rw [sp_smul_left P hS2 h1eff hx (le_of_lt (pseudoInvCoef_pos hbd))
    (pseudoInvCoef_le_one hb)]
  have hu : P.sp (1 : HermitianMat n 𝕜) x = x := P.sp_unit_left hx
  rw [hu]

/-! ## Order reflection and injectivity of `seqLeftMul` (vdW 4.19) -/

/-- The effects span the carrier. -/
theorem span_isEffect_eq_top :
    Submodule.span ℝ {a : HermitianMat n 𝕜 | IsEffect a} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hmem : ∀ y : HermitianMat n 𝕜, 0 ≤ y →
      y ∈ Submodule.span ℝ {a : HermitianMat n 𝕜 | IsEffect a} := by
    intro y hy
    have heff : IsEffect ((‖y‖ + 1)⁻¹ • y) :=
      norm_smul_inv_effect hy (by positivity) (le_norm_add_one_smul_one y)
    have hrepr : y = (‖y‖ + 1) • ((‖y‖ + 1)⁻¹ • y) := by
      rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    rw [hrepr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span heff)
  have hx := HermitianMat.posPart_add_negPart x
  rw [← hx]
  exact Submodule.sub_mem _ (hmem _ (HermitianMat.posPart_nonneg x))
    (hmem _ (HermitianMat.negPart_nonneg x))

/-- **The linear-map cancellation**: `L'_ν ∘ L'_b = c·id`. -/
theorem seqLeftMul_pseudoInv_comp (hS2 : P.FirstArgContinuous) (hb : IsEffect b)
    (hbd : b.mat.PosDef) :
    (seqLeftMul P (pseudoInv b) (pseudoInv_isEffect hb hbd)).comp (seqLeftMul P b hb)
      = pseudoInvCoef b • LinearMap.id := by
  apply LinearMap.ext_on (s := {a : HermitianMat n 𝕜 | IsEffect a}) span_isEffect_eq_top
  intro e he
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [seqLeftMul_apply_effect P hb he,
    seqLeftMul_apply_effect P (pseudoInv_isEffect hb hbd) (P.sp_effect hb he)]
  exact sp_pseudoInv_cancel P hS2 hb hbd he

/-- **Order reflection** (vdW 4.19 on matrices): for positive-definite `b`, the
left multiplication of the unknown product reflects positivity. -/
theorem seqLeftMul_reflectsNonneg (hS2 : P.FirstArgContinuous) (hb : IsEffect b)
    (hbd : b.mat.PosDef) {x : HermitianMat n 𝕜}
    (hx : 0 ≤ seqLeftMul P b hb x) : 0 ≤ x := by
  have h1 : 0 ≤ seqLeftMul P (pseudoInv b) (pseudoInv_isEffect hb hbd)
      (seqLeftMul P b hb x) :=
    seqLeftMul_nonneg P (pseudoInv_isEffect hb hbd) hx
  have h2 : seqLeftMul P (pseudoInv b) (pseudoInv_isEffect hb hbd)
      (seqLeftMul P b hb x) = pseudoInvCoef b • x := by
    have h := congrArg (fun f : HermitianMat n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜 => f x)
      (seqLeftMul_pseudoInv_comp P hS2 hb hbd)
    simpa using h
  rw [h2] at h1
  have hrepr : x = (pseudoInvCoef b)⁻¹ • (pseudoInvCoef b • x) := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (pseudoInvCoef_pos hbd)), one_smul]
  rw [hrepr]
  exact smul_nonneg (inv_nonneg.mpr (le_of_lt (pseudoInvCoef_pos hbd))) h1

/-- **Injectivity** of the left multiplication for positive-definite `b`. -/
theorem seqLeftMul_injective (hS2 : P.FirstArgContinuous) (hb : IsEffect b)
    (hbd : b.mat.PosDef) : Function.Injective (seqLeftMul P b hb) := by
  intro x y hxy
  have h : ∀ z : HermitianMat n 𝕜, seqLeftMul P (pseudoInv b) (pseudoInv_isEffect hb hbd)
      (seqLeftMul P b hb z) = pseudoInvCoef b • z := by
    intro z
    have h := congrArg (fun f : HermitianMat n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜 => f z)
      (seqLeftMul_pseudoInv_comp P hS2 hb hbd)
    simpa using h
  have hc := congrArg (seqLeftMul P (pseudoInv b) (pseudoInv_isEffect hb hbd)) hxy
  rw [h x, h y] at hc
  exact smul_right_injective _ (ne_of_gt (pseudoInvCoef_pos hbd)) hc

end Necessity
