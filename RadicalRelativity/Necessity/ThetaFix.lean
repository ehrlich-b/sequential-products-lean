/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.Theta

set_option linter.style.longLine false

/-!
# Θ fixes commuting effects  (campaign LEDGER 2.2: vdW Prop 5.5)

For a positive-definite effect `a`, an effect `b` operator-commuting with `a`, and
an arbitrary S1–S7+S2 product:

* `jointProj` — the joint spectral family `P_μ·Q_ν` of the commuting pair: a
  pairwise-orthogonal projection family in which BOTH `a` and `b` (and `√a`) are
  diagonal (`a_eq_sum_jointProj`, `b_eq_sum_jointProj`, `sqrt_eq_sum_jointProj`,
  via the padding lemmas `sum_smul_specProj_pad`/`_pad_left`).
* `sp_eq_quadRep_of_commute` — `a ◦' b = Q_{√a} b`: the unknown side is the 2.1d
  value law over the joint family; the standard side is two applications of the
  resolution multiplication rule and `√μ·ν·√μ = μν`.
* `theta_fix` — **vdW 5.5**: `Θ_a b = b` for every effect `b` commuting with `a`,
  by cancelling `Q_{√a}` through the defining equation `L'_a = Q_{√a}·Θ_a`.

This is the same joint-family construction that certified the twist-factor
multiplicativity in M1 (`Hermitian/Sequential.lean`), now deployed on the
necessity side.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a b : HermitianMat n ℂ}

/-! ## The joint spectral family of a commuting pair -/

/-- The joint spectral projection `P_μ·Q_ν` at the eigenvalue pair `q = (μ, ν)`,
Hermitian because the factors commute. -/
def jointProj (hab : Commute a.mat b.mat) (q : ℝ × ℝ) : HermitianMat n ℂ :=
  ⟨(a.specProj q.1).mat * (b.specProj q.2).mat, by
    have hc : Commute (a.specProj q.1).mat (b.specProj q.2).mat :=
      HermitianMat.cfc_commute _ _ hab
    show ((a.specProj q.1).mat * (b.specProj q.2).mat)ᴴ = _
    rw [Matrix.conjTranspose_mul, (a.specProj q.1).H, (b.specProj q.2).H]
    exact hc.symm.eq⟩

theorem jointProj_mat (hab : Commute a.mat b.mat) (q : ℝ × ℝ) :
    (jointProj hab q).mat = (a.specProj q.1).mat * (b.specProj q.2).mat := rfl

theorem jointProj_isProjection (hab : Commute a.mat b.mat) (q : ℝ × ℝ) :
    (jointProj hab q).IsProjection := by
  rw [HermitianMat.isProjection_iff_mat_mul_self, jointProj_mat]
  have hc : Commute (b.specProj q.2).mat (a.specProj q.1).mat :=
    (HermitianMat.cfc_commute _ _ hab).symm
  rw [hc.mul_mul_mul_comm, HermitianMat.specProj_mul_self, HermitianMat.specProj_mul_self]

theorem jointProj_orth (hab : Commute a.mat b.mat) {q q' : ℝ × ℝ} (hne : q ≠ q') :
    (jointProj hab q).mat * (jointProj hab q').mat = 0 := by
  rw [jointProj_mat, jointProj_mat]
  have hc : Commute (b.specProj q.2).mat (a.specProj q'.1).mat :=
    (HermitianMat.cfc_commute _ _ hab).symm
  rw [hc.mul_mul_mul_comm]
  rcases eq_or_ne q.1 q'.1 with h1 | h1
  · have h2 : q.2 ≠ q'.2 := fun h2 => hne (Prod.ext h1 h2)
    rw [HermitianMat.specProj_mul_orth b h2, mul_zero]
  · rw [HermitianMat.specProj_mul_orth a h1, zero_mul]

/-! ## Padding: single-family diagonals are joint-family diagonals -/

theorem sum_smul_specProj_pad (f : ℝ → ℝ) :
    ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
        f q.1 • ((a.specProj q.1).mat * (b.specProj q.2).mat)
      = (a.cfc f).mat := by
  rw [Finset.sum_product]
  calc ∑ μ ∈ a.eigFinset, ∑ ν ∈ b.eigFinset,
        f μ • ((a.specProj μ).mat * (b.specProj ν).mat)
      = ∑ μ ∈ a.eigFinset, f μ • ((a.specProj μ).mat * ∑ ν ∈ b.eigFinset, (b.specProj ν).mat) := by
        apply Finset.sum_congr rfl
        intro μ _
        rw [Finset.mul_sum, Finset.smul_sum]
    _ = ∑ μ ∈ a.eigFinset, f μ • (a.specProj μ).mat := by
        rw [HermitianMat.sum_specProj_mat b]
        simp only [Matrix.mul_one]
    _ = (a.cfc f).mat := (HermitianMat.mat_cfc_eq_sum_specProj a f).symm

theorem sum_smul_specProj_pad_left (g : ℝ → ℝ) :
    ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
        g q.2 • ((a.specProj q.1).mat * (b.specProj q.2).mat)
      = (b.cfc g).mat := by
  rw [Finset.sum_product, Finset.sum_comm]
  calc ∑ ν ∈ b.eigFinset, ∑ μ ∈ a.eigFinset,
        g ν • ((a.specProj μ).mat * (b.specProj ν).mat)
      = ∑ ν ∈ b.eigFinset, g ν • ((∑ μ ∈ a.eigFinset, (a.specProj μ).mat) * (b.specProj ν).mat) := by
        apply Finset.sum_congr rfl
        intro ν _
        rw [Finset.sum_mul, Finset.smul_sum]
    _ = ∑ ν ∈ b.eigFinset, g ν • (b.specProj ν).mat := by
        rw [HermitianMat.sum_specProj_mat a]
        simp only [Matrix.one_mul]
    _ = (b.cfc g).mat := (HermitianMat.mat_cfc_eq_sum_specProj b g).symm

/-- `a` is diagonal in the joint family. -/
theorem a_eq_sum_jointProj (hab : Commute a.mat b.mat) :
    a = ∑ q ∈ a.eigFinset ×ˢ b.eigFinset, q.1 • jointProj hab q := by
  ext1
  rw [mat_finsetSum]
  simp only [HermitianMat.mat_smul, jointProj_mat]
  rw [show (∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
      q.1 • ((a.specProj q.1).mat * (b.specProj q.2).mat))
    = (a.cfc fun x => x).mat from sum_smul_specProj_pad (fun x => x)]
  rw [HermitianMat.cfc_id']

/-- `b` is diagonal in the joint family. -/
theorem b_eq_sum_jointProj (hab : Commute a.mat b.mat) :
    b = ∑ q ∈ a.eigFinset ×ˢ b.eigFinset, q.2 • jointProj hab q := by
  ext1
  rw [mat_finsetSum]
  simp only [HermitianMat.mat_smul, jointProj_mat]
  rw [show (∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
      q.2 • ((a.specProj q.1).mat * (b.specProj q.2).mat))
    = (b.cfc fun x => x).mat from sum_smul_specProj_pad_left (fun x => x)]
  rw [HermitianMat.cfc_id']

/-! ## The value identity `a ◦' b = Q_{√a} b` -/

variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- For a commuting pair of effects (with `a` positive definite), the unknown
product takes the standard Lüders value. -/
theorem sp_eq_quadRep_of_commute (hS2 : P.FirstArgContinuous)
    (ha : IsEffect a) (hbd : a.mat.PosDef) (hb : IsEffect b)
    (hab : Commute a.mat b.mat) :
    P.sp a b = quadRepEquiv a hbd b := by
  classical
  set s : Finset (ℝ × ℝ) := a.eigFinset ×ˢ b.eigFinset with hs
  have hproj : ∀ q ∈ s, (jointProj hab q).IsProjection :=
    fun q _ => jointProj_isProjection hab q
  have horthH : ∀ q ∈ s, ∀ q' ∈ s, q ≠ q' →
      (jointProj hab q).mat * (jointProj hab q').mat = 0 :=
    fun q _ q' _ hne => jointProj_orth hab hne
  have hmem1 : ∀ q ∈ s, 0 ≤ q.1 ∧ q.1 ≤ 1 := by
    intro q hq
    obtain ⟨h1, _⟩ := Finset.mem_product.mp hq
    exact ⟨HermitianMat.eigFinset_nonneg ha.1 q.1 h1, eigFinset_le_one ha.2 q.1 h1⟩
  have hmem2 : ∀ q ∈ s, 0 ≤ q.2 ∧ q.2 ≤ 1 := by
    intro q hq
    obtain ⟨_, h2⟩ := Finset.mem_product.mp hq
    exact ⟨HermitianMat.eigFinset_nonneg hb.1 q.2 h2, eigFinset_le_one hb.2 q.2 h2⟩
  -- the unknown side, via the 2.1d value law
  have hval : P.sp a b = ∑ q ∈ s, (q.1 * q.2) • jointProj hab q := by
    have h := sp_orthFamily_value P hS2 hproj horthH
      (fun q hq => (hmem1 q hq).1) (fun q hq => (hmem1 q hq).2)
      (fun q hq => (hmem2 q hq).1) (fun q hq => (hmem2 q hq).2)
    rw [← a_eq_sum_jointProj hab, ← b_eq_sum_jointProj hab] at h
    exact h
  -- the standard side, via the resolution multiplication rule
  have hstd : (quadRepEquiv a hbd b).mat = ∑ q ∈ s, (q.1 * q.2) • (jointProj hab q).mat := by
    rw [quadRepEquiv_apply, HermitianMat.conj_apply_mat, (a.cfc Real.sqrt).H]
    have hsqrt : (a.cfc Real.sqrt).mat
        = ∑ q ∈ s, Real.sqrt q.1 • (jointProj hab q).mat := by
      simp only [jointProj_mat]
      exact (sum_smul_specProj_pad Real.sqrt).symm
    have hbmat : b.mat = ∑ q ∈ s, q.2 • (jointProj hab q).mat := by
      simp only [jointProj_mat]
      rw [show (∑ q ∈ s, q.2 • ((a.specProj q.1).mat * (b.specProj q.2).mat))
        = (b.cfc fun x => x).mat from sum_smul_specProj_pad_left (fun x => x)]
      rw [HermitianMat.cfc_id']
    have hidemM : ∀ q ∈ s, (jointProj hab q).mat * (jointProj hab q).mat = (jointProj hab q).mat :=
      fun q hq => HermitianMat.isProjection_iff_mat_mul_self.mp (hproj q hq)
    rw [hsqrt, hbmat,
      HermitianMat.resolution_mul hidemM horthH (fun q => Real.sqrt q.1) (fun q => q.2),
      HermitianMat.resolution_mul hidemM horthH (fun q => Real.sqrt q.1 * q.2) (fun q => Real.sqrt q.1)]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    have h0 := (hmem1 q hq).1
    calc Real.sqrt q.1 * q.2 * Real.sqrt q.1
        = Real.sqrt q.1 * Real.sqrt q.1 * q.2 := by ring
      _ = q.1 * q.2 := by rw [Real.mul_self_sqrt h0]
  rw [hval]
  ext1
  rw [hstd, mat_finsetSum]
  exact Finset.sum_congr rfl fun q _ => rfl

/-- **vdW Proposition 5.5, matrix-concrete** (LEDGER 2.2): Θ fixes every effect
that operator-commutes with its base point. -/
theorem theta_fix (hS2 : P.FirstArgContinuous)
    (ha : IsEffect a) (hbd : a.mat.PosDef) (hb : IsEffect b)
    (hab : Commute a.mat b.mat) :
    theta P ha hbd b = b := by
  apply (quadRepEquiv a hbd).injective
  rw [quadRep_theta P ha hbd, seqLeftMul_apply_effect P ha hb,
    sp_eq_quadRep_of_commute P hS2 ha hbd hb hab]

end Necessity
