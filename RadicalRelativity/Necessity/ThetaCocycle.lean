/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ThetaFix
import RadicalRelativity.Hermitian.Sequential
import RadicalRelativity.Vendor.HermitianMat.Jordan
import Mathlib.Tactic.Module

set_option linter.style.longLine false

/-!
# The Θ cocycle law  (campaign LEDGER 2.4: vdW Prop 5.7)

For commuting positive-definite effects, `Θ_{a◦b} = Θ_a ∘ Θ_b`.  vdW's proof of
the exchange step 5.7(1) consumes invariance of the standard product under unital
order isomorphisms — Kadison-grade input the campaign carries as the `Θ_jordan`
interface field (M3).  Accordingly this file proves everything concrete
unconditionally and states the assembly CONDITIONALLY on `PreservesJordan Θ_a`,
which the instantiation discharges from the same `Θ_jordan` field:

* `conj_eq_jordan` — the fundamental identity: Lüders conjugation is a Jordan
  polynomial, `s·y·s = s∘(s∘y) + s∘(s∘y) − (s∘s)∘y`.
* `sqrt_isEffect` — square roots of effects are effects.
* `sp_comm_of_commute` — commuting effects are ◦'-compatible.
* `seqLeftMul_mul_of_commute` — the S5 splitting `L'_{a◦'b} = L'_a ∘ L'_b`.
* `quadRepEquiv_mul_of_commute` — `Q_{√(ab)} = Q_{√a} ∘ Q_{√b}` (riding M1's
  `twistFactor_mul_of_commute` at `t = 0`).
* `theta_conj_exchange` — GIVEN `PreservesJordan Θ_b`: `Θ_b` commutes with Lüders
  conjugation at any commuting base point (the 5.7(1) exchange), via `theta_fix`
  on the square root and the fundamental identity.
* `theta_cocycle_of_preservesJordan` — **the cocycle**, conditional only on
  `PreservesJordan Θ_a`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Lüders conjugation is a Jordan polynomial -/

/-- **The fundamental identity**: `s·y·s = s∘(s∘y) + s∘(s∘y) − (s∘s)∘y`, with
`∘` the vendored symmetrized product.  Matrix-concrete; closed by `module` after
normalizing the associations. -/
theorem conj_eq_jordan (s y : HermitianMat n ℂ) :
    y.conj s.mat
      = s.symmMul (s.symmMul y) + s.symmMul (s.symmMul y) - (s.symmMul s).symmMul y := by
  ext1
  rw [HermitianMat.mat_sub, HermitianMat.mat_add, HermitianMat.conj_apply_mat, s.H,
    HermitianMat.symmMul_toMat, HermitianMat.symmMul_toMat, HermitianMat.symmMul_toMat,
    HermitianMat.symmMul_self]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, Matrix.mul_add, Matrix.add_mul,
    smul_smul, Matrix.mul_assoc]
  module

/-! ## Square roots of effects are effects -/

theorem sqrt_isEffect {a : HermitianMat n ℂ} (ha : IsEffect a) :
    IsEffect (a.cfc Real.sqrt) := by
  constructor
  · rw [show (0 : HermitianMat n ℂ) ≤ a.cfc Real.sqrt ↔
        ∀ i, 0 ≤ Real.sqrt (a.H.eigenvalues i) from HermitianMat.cfc_nonneg_iff a Real.sqrt]
    exact fun i => Real.sqrt_nonneg _
  · have hev : ∀ i, (a.cfc Real.sqrt).H.eigenvalues i ≤ 1 := by
      obtain ⟨e, he⟩ := HermitianMat.cfc_eigenvalues Real.sqrt a
      intro i
      rw [he]
      simp only [Function.comp_apply]
      have h1 : a.H.eigenvalues (e i) ≤ 1 :=
        HermitianMat.le_smul_one_imp_eigenvalues_le a 1 (by simpa using ha.2) (e i)
      calc Real.sqrt (a.H.eigenvalues (e i)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
        _ = 1 := Real.sqrt_one
    have := HermitianMat.eigenvalues_le_imp_le_smul_one (a.cfc Real.sqrt) 1 hev
    simpa using this

/-! ## Commuting effects are compatible; the S5 splitting -/

/-- Commuting effects are ◦'-compatible (through the joint family; no positive
definiteness needed). -/
theorem sp_comm_of_commute (P : SequentialProductOn (HermitianMat n ℂ))
    (hS2 : P.FirstArgContinuous) {a b : HermitianMat n ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hab : Commute a.mat b.mat) :
    P.sp a b = P.sp b a := by
  have hcomm := sp_orthFamily_comm P hS2 (fun q (_ : q ∈ a.eigFinset ×ˢ b.eigFinset) =>
      jointProj_isProjection hab q)
    (fun q _ q' _ hne => jointProj_orth hab hne)
    (lam := fun q => q.1) (mu := fun q => q.2)
    (fun q hq => HermitianMat.eigFinset_nonneg ha.1 q.1 (Finset.mem_product.mp hq).1)
    (fun q hq => eigFinset_le_one ha.2 q.1 (Finset.mem_product.mp hq).1)
    (fun q hq => HermitianMat.eigFinset_nonneg hb.1 q.2 (Finset.mem_product.mp hq).2)
    (fun q hq => eigFinset_le_one hb.2 q.2 (Finset.mem_product.mp hq).2)
  rw [← a_eq_sum_jointProj hab, ← b_eq_sum_jointProj hab] at hcomm
  exact hcomm

/-- **The S5 splitting at the linear-map level**: `L'_{a◦'b} = L'_a ∘ L'_b` for
◦'-compatible pairs. -/
theorem seqLeftMul_mul_of_commute (P : SequentialProductOn (HermitianMat n ℂ))
    (hS2 : P.FirstArgContinuous) {a b m : HermitianMat n ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hab : Commute a.mat b.mat)
    (hm : m = P.sp a b) (hme : IsEffect m) :
    seqLeftMul P m hme = (seqLeftMul P a ha).comp (seqLeftMul P b hb) := by
  apply LinearMap.ext_on (s := {x : HermitianMat n ℂ | IsEffect x}) span_isEffect_eq_top
  intro e he
  simp only [LinearMap.comp_apply]
  rw [seqLeftMul_apply_effect P hme he, seqLeftMul_apply_effect P hb he,
    seqLeftMul_apply_effect P ha (P.sp_effect hb he), hm]
  exact (P.sp_assoc_of_compatible ha hb he (sp_comm_of_commute P hS2 ha hb hab)).symm

/-- `Q_{√(ab)} = Q_{√a} ∘ Q_{√b}` on commuting nonnegatives, riding M1's twist-factor
multiplicativity at `t = 0`. -/
theorem quadRepEquiv_mul_of_commute {a b m : HermitianMat n ℂ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hab : Commute a.mat b.mat)
    (hmm : m.mat = a.mat * b.mat)
    (hbda : a.mat.PosDef) (hbdb : b.mat.PosDef) (hbdm : m.mat.PosDef)
    (x : HermitianMat n ℂ) :
    quadRepEquiv m hbdm x = quadRepEquiv a hbda (quadRepEquiv b hbdb x) := by
  have h := HermitianMat.twistFactor_mul_of_commute ha0 hb0 hab hmm 0
  rw [HermitianMat.twistFactor_zero, HermitianMat.twistFactor_zero,
    HermitianMat.twistFactor_zero] at h
  rw [quadRepEquiv_apply, quadRepEquiv_apply, quadRepEquiv_apply, conj_conj_mat, ← h]

/-! ## The exchange and the cocycle, conditional on Jordan preservation -/

/-- The Jordan-preservation predicate for a comparison map — discharged at
instantiation time by the `Θ_jordan` interface field (M3, Kadison/vIR). -/
def PreservesJordan (T : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ) : Prop :=
  ∀ x y : HermitianMat n ℂ, T (x.symmMul y) = (T x).symmMul (T y)

/-- **The vdW 5.7(1) exchange**: given `PreservesJordan Θ_b`, the comparison map at
`b` commutes with Lüders conjugation at any commuting base point `a`. -/
theorem theta_conj_exchange (P : SequentialProductOn (HermitianMat n ℂ))
    (hS2 : P.FirstArgContinuous) {a b : HermitianMat n ℂ}
    (ha : IsEffect a) (hb : IsEffect b) (hbdb : b.mat.PosDef)
    (hab : Commute a.mat b.mat)
    (hjord : PreservesJordan (theta P hb hbdb)) (y : HermitianMat n ℂ) :
    theta P hb hbdb (y.conj (a.cfc Real.sqrt).mat)
      = (theta P hb hbdb y).conj (a.cfc Real.sqrt).mat := by
  have hsqrt_comm : Commute b.mat (a.cfc Real.sqrt).mat :=
    Commute.cfc_right _ hab.symm
  have hfix : theta P hb hbdb (a.cfc Real.sqrt) = a.cfc Real.sqrt :=
    theta_fix P hS2 hb hbdb (sqrt_isEffect ha) hsqrt_comm
  rw [conj_eq_jordan (a.cfc Real.sqrt) y, map_sub, map_add, hjord, hjord, hjord, hjord, hfix,
    conj_eq_jordan (a.cfc Real.sqrt) (theta P hb hbdb y)]

/-- **The Θ cocycle** (vdW 5.7(2)), conditional only on `PreservesJordan Θ_a`:
for commuting positive-definite effects with `m = a ◦' b`,
`Θ_m = Θ_a ∘ Θ_b`. -/
theorem theta_cocycle_of_preservesJordan (P : SequentialProductOn (HermitianMat n ℂ))
    (hS2 : P.FirstArgContinuous) {a b m : HermitianMat n ℂ}
    (ha : IsEffect a) (hb : IsEffect b)
    (hbda : a.mat.PosDef) (hbdb : b.mat.PosDef)
    (hab : Commute a.mat b.mat)
    (hm : m = P.sp a b) (hme : IsEffect m) (hbdm : m.mat.PosDef)
    (hmm : m.mat = a.mat * b.mat)
    (hjord : PreservesJordan (theta P ha hbda)) (x : HermitianMat n ℂ) :
    theta P hme hbdm x = theta P ha hbda (theta P hb hbdb x) := by
  -- reduce to an identity under Q_{√m} = Q_{√a} ∘ Q_{√b}
  apply (quadRepEquiv m hbdm).injective
  rw [quadRep_theta P hme hbdm,
    seqLeftMul_mul_of_commute P hS2 ha hb hab hm hme]
  -- LHS is now L'_a (L'_b x); rewrite the RHS through the multiplicative splitting
  rw [quadRepEquiv_mul_of_commute ha.1 hb.1 hab hmm hbda hbdb hbdm]
  -- Q_a (Q_b (Θ_a (Θ_b x))) = Q_a (Θ_a (Q_b (Θ_b x)))  by the exchange
  have hexch : quadRepEquiv b hbdb (theta P ha hbda (theta P hb hbdb x))
      = theta P ha hbda (quadRepEquiv b hbdb (theta P hb hbdb x)) := by
    rw [quadRepEquiv_apply, quadRepEquiv_apply]
    exact (theta_conj_exchange P hS2 hb ha hbda hab.symm hjord (theta P hb hbdb x)).symm
  rw [hexch, quadRep_theta P ha hbda, quadRep_theta P hb hbdb]
  simp only [LinearMap.comp_apply]

/-! ## Jordan operator commutation and Peirce compression  (campaign LEDGER 2.5)

The concrete discharge kit for the `frame_opCommute` and `simDiag_opCommute`
interface fields: matrix commutation implies commutation of the Jordan
multiplication operators, and a Peirce-2 element is fixed by compression. -/

omit [DecidableEq n] in
/-- **Matrix commutation implies Jordan operator commutation**:
`a∘(b∘x) = b∘(a∘x)` for the symmetrized product. -/
theorem symmMul_opCommute_of_commute {a b : HermitianMat n ℂ}
    (hab : Commute a.mat b.mat) (x : HermitianMat n ℂ) :
    a.symmMul (b.symmMul x) = b.symmMul (a.symmMul x) := by
  ext1
  rw [HermitianMat.symmMul_toMat, HermitianMat.symmMul_toMat,
    HermitianMat.symmMul_toMat, HermitianMat.symmMul_toMat]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, Matrix.mul_add, Matrix.add_mul,
    smul_smul, Matrix.mul_assoc]
  rw [show a.mat * (b.mat * x.mat) = b.mat * (a.mat * x.mat) from by
    rw [← Matrix.mul_assoc, hab.eq, Matrix.mul_assoc]]
  rw [show x.mat * (b.mat * a.mat) = x.mat * (a.mat * b.mat) from by rw [hab.eq]]
  module

/-- **Peirce compression**: an element with `e∘x = x` for a projection `e`
satisfies `e·x·e = x` (the concrete `J₂(e)`-membership normal form). -/
theorem conj_eq_self_of_symmMul_eq_self {e x : HermitianMat n ℂ}
    (he : e.IsProjection) (hx : e.symmMul x = x) : x.conj e.mat = x := by
  have hee : e.mat * e.mat = e.mat := HermitianMat.isProjection_iff_mat_mul_self.mp he
  have hmat : e.mat * x.mat + x.mat * e.mat = (2 : ℂ) • x.mat := by
    have h := congrArg HermitianMat.mat hx
    rw [HermitianMat.symmMul_toMat] at h
    calc e.mat * x.mat + x.mat * e.mat
        = (2 : ℂ) • ((2 : ℂ)⁻¹ • (e.mat * x.mat + x.mat * e.mat)) := by
          rw [smul_smul]
          norm_num
      _ = (2 : ℂ) • x.mat := by rw [h]
  -- multiply the relation by e on the left and on the right
  have hleft : e.mat * x.mat * e.mat = e.mat * x.mat := by
    have h := congrArg (fun M => e.mat * M) hmat
    simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, hee] at h
    -- h : e x + e x e = 2 • (e x)
    have h2 : e.mat * x.mat + e.mat * x.mat * e.mat
        = e.mat * x.mat + e.mat * x.mat := by
      calc e.mat * x.mat + e.mat * x.mat * e.mat
          = (2 : ℂ) • (e.mat * x.mat) := h
        _ = e.mat * x.mat + e.mat * x.mat := two_smul ℂ _
    exact add_left_cancel h2
  have hright : e.mat * (x.mat * e.mat) = x.mat * e.mat := by
    have h := congrArg (fun M => M * e.mat) hmat
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hee] at h
    -- h : e (x e) + x e = 2 • (x e)
    have h2 : e.mat * (x.mat * e.mat) + x.mat * e.mat
        = x.mat * e.mat + x.mat * e.mat := by
      calc e.mat * (x.mat * e.mat) + x.mat * e.mat
          = (2 : ℂ) • (x.mat * e.mat) := h
        _ = x.mat * e.mat + x.mat * e.mat := two_smul ℂ _
    exact add_right_cancel h2
  -- combine: e x e = e x and e x e = x e, so e x = x e and both equal e x e
  ext1
  rw [HermitianMat.conj_apply_mat, e.H]
  -- goal: e x e = x
  have hcomm : e.mat * x.mat = x.mat * e.mat := by
    calc e.mat * x.mat = e.mat * x.mat * e.mat := hleft.symm
      _ = e.mat * (x.mat * e.mat) := by rw [Matrix.mul_assoc]
      _ = x.mat * e.mat := hright
  have h2x : e.mat * x.mat + e.mat * x.mat = (2 : ℂ) • x.mat := by
    rw [← hmat, hcomm]
  calc e.mat * x.mat * e.mat
      = e.mat * x.mat := hleft
    _ = x.mat := by
      have h3 := h2x
      rw [← two_smul ℂ (e.mat * x.mat)] at h3
      exact smul_right_injective _ (two_ne_zero) h3

end Necessity
