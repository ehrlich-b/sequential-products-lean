/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.PseudoInverse

set_option linter.style.longLine false

/-!
# The comparison map Θ  (campaign LEDGER 2.1f: vdW Props 5.2/5.3, construction)

For a positive-definite effect `a` and an arbitrary S1–S7+S2 product `P`, this file
constructs the paper's comparison map and proves it a unital linear order
isomorphism — the concluding unit of LEDGER 2.1:

* `quadRepEquiv a` — the standard quadratic representation `Q_{√a} : x ↦ √a·x·√a`
  as a linear equivalence (inverse `Q` at `(√·)⁻¹`, through the functional
  calculus on the positive spectrum).
* `theta P a := Q_{√a}⁻¹ ∘ L'_a` — the comparison map, with `L'_a = seqLeftMul P a`
  the unknown product's left multiplication (2.1a).
* `thetaEquiv` — Θ as a `LinearEquiv`: injectivity comes from the pseudo-inverse
  cancellation (2.1e), surjectivity from finite dimension.
* `theta_one` — **unitality** `Θ_a 1 = 1` (vdW 5.3).
* `theta_nonneg_iff` — **the order isomorphism property** `0 ≤ Θ_a x ↔ 0 ≤ x`:
  forward by conjugation positivity, backward by 2.1e's order reflection.

By construction `L'_a = Q_{√a} ∘ Θ_a` (`quadRep_theta`), the paper's defining
equation for Θ.  `Θ_fix` (vdW 5.5) is LEDGER 2.2; the cocycle law is 2.4.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The quadratic representation `Q_{√a}` as a linear equivalence -/

/-- `Q_{√a} : x ↦ √a·x·√a`. -/
def quadRep (a : HermitianMat n ℂ) : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ :=
  HermitianMat.conjLinear ℝ (a.cfc Real.sqrt).mat

/-- The inverse branch `x ↦ (√a)⁻¹·x·(√a)⁻¹`, through the functional calculus. -/
def quadRepInv (a : HermitianMat n ℂ) : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ :=
  HermitianMat.conjLinear ℝ (a.cfc fun x => (Real.sqrt x)⁻¹).mat

theorem sqrt_mul_invSqrt {a : HermitianMat n ℂ} (hbd : a.mat.PosDef) :
    (a.cfc Real.sqrt).mat * (a.cfc fun x => (Real.sqrt x)⁻¹).mat = 1 := by
  rw [← HermitianMat.mat_cfc_mul_apply]
  have hcongr : a.cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) = a.cfc (fun _ => (1 : ℝ)) :=
    HermitianMat.cfc_congr_of_posDef hbd fun x hx =>
      mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hx))
  rw [hcongr, HermitianMat.cfc_const]
  simp

theorem invSqrt_mul_sqrt {a : HermitianMat n ℂ} (hbd : a.mat.PosDef) :
    (a.cfc fun x => (Real.sqrt x)⁻¹).mat * (a.cfc Real.sqrt).mat = 1 := by
  rw [← HermitianMat.mat_cfc_mul_apply]
  have hcongr : a.cfc (fun x => (Real.sqrt x)⁻¹ * Real.sqrt x) = a.cfc (fun _ => (1 : ℝ)) :=
    HermitianMat.cfc_congr_of_posDef hbd fun x hx =>
      inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hx))
  rw [hcongr, HermitianMat.cfc_const]
  simp

/-- Composition of conjugations: `(x.conj S).conj T = x.conj (T·S)`. -/
theorem conj_conj_mat (x : HermitianMat n ℂ) (S T : Matrix n n ℂ) :
    (x.conj S).conj T = x.conj (T * S) := by
  ext1
  rw [HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
    Matrix.conjTranspose_mul]
  noncomm_ring

theorem conj_one_mat (x : HermitianMat n ℂ) : x.conj (1 : Matrix n n ℂ) = x := by
  ext1
  rw [HermitianMat.conj_apply_mat]
  simp

/-- **`Q_{√a}` as a linear equivalence**, for positive-definite `a`. -/
def quadRepEquiv (a : HermitianMat n ℂ) (hbd : a.mat.PosDef) :
    HermitianMat n ℂ ≃ₗ[ℝ] HermitianMat n ℂ :=
  LinearEquiv.ofLinear (quadRep a) (quadRepInv a)
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, quadRep, quadRepInv,
        HermitianMat.conjLinear_apply]
      rw [conj_conj_mat, sqrt_mul_invSqrt hbd, conj_one_mat])
    (by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, quadRep, quadRepInv,
        HermitianMat.conjLinear_apply]
      rw [conj_conj_mat, invSqrt_mul_sqrt hbd, conj_one_mat])

theorem quadRepEquiv_apply (a : HermitianMat n ℂ) (hbd : a.mat.PosDef)
    (x : HermitianMat n ℂ) :
    quadRepEquiv a hbd x = x.conj (a.cfc Real.sqrt).mat := rfl

theorem quadRepEquiv_symm_apply (a : HermitianMat n ℂ) (hbd : a.mat.PosDef)
    (x : HermitianMat n ℂ) :
    (quadRepEquiv a hbd).symm x = x.conj (a.cfc fun t => (Real.sqrt t)⁻¹).mat := rfl

/-- `Q_{√a} 1 = a`. -/
theorem quadRepEquiv_one {a : HermitianMat n ℂ} (ha0 : 0 ≤ a) (hbd : a.mat.PosDef) :
    quadRepEquiv a hbd 1 = a := by
  ext1
  rw [quadRepEquiv_apply, HermitianMat.conj_apply_mat, HermitianMat.mat_one, Matrix.mul_one,
    (a.cfc Real.sqrt).H, ← HermitianMat.mat_cfc_mul_apply]
  have hcongr : a.cfc (fun x => Real.sqrt x * Real.sqrt x) = a.cfc (fun x => x) :=
    HermitianMat.cfc_congr_of_nonneg ha0 fun x hx => Real.mul_self_sqrt hx
  rw [hcongr, HermitianMat.cfc_id']

/-! ## The comparison map Θ -/

variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- **The comparison map** `Θ_a := Q_{√a}⁻¹ ∘ L'_a` (vdW 5.3, matrix-concrete). -/
def theta {a : HermitianMat n ℂ} (ha : IsEffect a) (hbd : a.mat.PosDef) :
    HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ :=
  ((quadRepEquiv a hbd).symm.toLinearMap).comp (seqLeftMul P a ha)

/-- The paper's defining equation: `L'_a = Q_{√a} ∘ Θ_a`. -/
theorem quadRep_theta {a : HermitianMat n ℂ} (ha : IsEffect a) (hbd : a.mat.PosDef)
    (x : HermitianMat n ℂ) :
    quadRepEquiv a hbd (theta P ha hbd x) = seqLeftMul P a ha x := by
  rw [theta]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact (quadRepEquiv a hbd).apply_symm_apply _

/-- **Θ is injective** (from the 2.1e pseudo-inverse cancellation). -/
theorem theta_injective (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) :
    Function.Injective (theta P ha hbd) := by
  rw [theta]
  exact ((quadRepEquiv a hbd).symm.injective).comp (seqLeftMul_injective P hS2 ha hbd)

/-- **Θ as a linear equivalence** (surjectivity from finite dimension). -/
def thetaEquiv (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) :
    HermitianMat n ℂ ≃ₗ[ℝ] HermitianMat n ℂ :=
  LinearEquiv.ofBijective (theta P ha hbd)
    ⟨theta_injective P hS2 ha hbd,
      LinearMap.injective_iff_surjective.mp (theta_injective P hS2 ha hbd)⟩

theorem thetaEquiv_apply (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) (x : HermitianMat n ℂ) :
    thetaEquiv P hS2 ha hbd x = theta P ha hbd x := rfl

/-! ## Unitality and the order isomorphism property -/

/-- **Θ is unital** (vdW 5.3): `Θ_a 1 = 1`. -/
theorem theta_one {a : HermitianMat n ℂ} (ha : IsEffect a) (hbd : a.mat.PosDef) :
    theta P ha hbd 1 = 1 := by
  rw [theta]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [seqLeftMul_one P ha]
  rw [LinearEquiv.symm_apply_eq, quadRepEquiv_one ha.1 hbd]

/-- **Θ is an order isomorphism** (vdW 5.3): `0 ≤ Θ_a x ↔ 0 ≤ x`.  Forward by
2.1e's order reflection, backward by conjugation positivity. -/
theorem theta_nonneg_iff (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) (x : HermitianMat n ℂ) :
    0 ≤ theta P ha hbd x ↔ 0 ≤ x := by
  constructor
  · intro h
    have hQ : 0 ≤ quadRepEquiv a hbd (theta P ha hbd x) := by
      rw [quadRepEquiv_apply]
      exact HermitianMat.conj_nonneg _ h
    rw [quadRep_theta P ha hbd] at hQ
    exact seqLeftMul_reflectsNonneg P hS2 ha hbd hQ
  · intro h
    have hL : 0 ≤ seqLeftMul P a ha x := seqLeftMul_nonneg P ha h
    rw [theta]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [quadRepEquiv_symm_apply]
    exact HermitianMat.conj_nonneg _ hL

/-- The monotone form: `Θ_a x ≤ Θ_a y ↔ x ≤ y`. -/
theorem theta_le_iff (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) (x y : HermitianMat n ℂ) :
    theta P ha hbd x ≤ theta P ha hbd y ↔ x ≤ y := by
  rw [← sub_nonneg, ← map_sub, theta_nonneg_iff P hS2 ha hbd, sub_nonneg]

/-! ## The normalization law `Θ_{t·a} = Θ_a`  (campaign LEDGER 2.3, vdW 5.4) -/

/-- `√(t•a) = √t • √a`, through the matrix-argument scaling law. -/
theorem sqrt_smul {t : ℝ} (ht : 0 ≤ t) (a : HermitianMat n ℂ) :
    (t • a).cfc Real.sqrt = Real.sqrt t • a.cfc Real.sqrt := by
  rw [HermitianMat.cfc_smul_arg]
  rw [show (fun x => Real.sqrt (t * x)) = fun x => Real.sqrt t * Real.sqrt x from
    funext fun x => Real.sqrt_mul ht x]
  exact HermitianMat.cfc_const_mul a _ _

/-- First-argument homogeneity at the linear-map level. -/
theorem seqLeftMul_smul (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hta : IsEffect (t • a)) :
    seqLeftMul P (t • a) hta = t • seqLeftMul P a ha := by
  apply LinearMap.ext_on (s := {x : HermitianMat n ℂ | IsEffect x}) span_isEffect_eq_top
  intro e he
  simp only [LinearMap.smul_apply]
  rw [seqLeftMul_apply_effect P hta he, seqLeftMul_apply_effect P ha he]
  exact sp_smul_left P hS2 ha he ht0 ht1

/-- The quadratic representation scales linearly with the base point. -/
theorem quadRepEquiv_smul {a : HermitianMat n ℂ} (hbd : a.mat.PosDef) {t : ℝ}
    (ht : 0 < t) (htbd : (t • a).mat.PosDef) (x : HermitianMat n ℂ) :
    quadRepEquiv (t • a) htbd x = t • quadRepEquiv a hbd x := by
  ext1
  rw [quadRepEquiv_apply, quadRepEquiv_apply, HermitianMat.mat_smul,
    HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat]
  rw [show ((t • a).cfc Real.sqrt).mat = (Real.sqrt t • a.cfc Real.sqrt).mat from
    congrArg _ (sqrt_smul (le_of_lt ht) a)]
  rw [HermitianMat.mat_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [show star (Real.sqrt t) = Real.sqrt t from star_trivial _]
  rw [show Real.sqrt t * Real.sqrt t = t from Real.mul_self_sqrt (le_of_lt ht)]

/-- **The normalization law** (vdW 5.4, paper cone-ext): Θ is scale-invariant in
its base point, `Θ_{t·a} = Θ_a` for `t ∈ (0,1]`. -/
theorem theta_smul (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hta : IsEffect (t • a)) (htbd : (t • a).mat.PosDef) :
    theta P hta htbd = theta P ha hbd := by
  apply LinearMap.ext
  intro x
  apply (quadRepEquiv (t • a) htbd).injective
  rw [quadRep_theta P hta htbd,
    quadRepEquiv_smul hbd ht0 htbd (theta P ha hbd x),
    quadRep_theta P ha hbd,
    seqLeftMul_smul P hS2 ha (le_of_lt ht0) ht1 hta]
  simp

end Necessity
