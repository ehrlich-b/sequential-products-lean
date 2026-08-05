/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.LeftMultiplication
import RadicalRelativity.Hermitian.ExtremeEffects

set_option linter.style.longLine false

/-!
# Sharp effects under an unknown sequential product
(campaign LEDGER 2.1c: the Gudder–Greechie sharp-effect base layer, matrix-concrete)

For an arbitrary `P : SequentialProductOn (HermitianMat n ℂ)`:

* `proj_pinch` — the product-independent sharpness of projections: an effect below
  both `p` and `1 - p` is zero (the matrix form of `p ∧ p⊥ = 0`), by two
  conjugation pinches through the vendored `conj` and the square-root trick.
* `sp_proj_compl` / `sp_proj_self` — `p ◦' (1-p) = 0` and `p ◦' p = p` for every
  projection `p`.  The compatibility `p ◦' (1-p) = (1-p) ◦' p` comes from S6a
  applied to the TRIVIAL self-compatibility `p |' p`; then `p ◦' (1-p) ≤ p` and
  `(1-p) ◦' p ≤ 1-p` (both from the S1 splitting of `x ◦' 1 = x`) pinch it to
  zero.
* `orth_compl_isProjection` / `proj_orth_le_one_sub` — for orthogonal projections
  (`p·q = 0`), `1 - p - q` is a projection, hence `q ≤ 1 - p`.
* `sp_proj_orth` / `sp_proj_orth'` — orthogonal projections ◦'-annihilate, in
  both orders (the second by S4).
* `sp_comm_proj_orth` — orthogonal projections are ◦'-compatible.

These are the matrix instances of the Gudder–Greechie sequential-effect-algebra
facts cited through vdW's Proposition 3.15; everything is proved from S1, S4, S6a
and the derived layer — no S2.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The product-independent pinch: `p ∧ (1-p) = 0` for projections -/

/-- If a PSD `e` is killed by conjugation with a Hermitian `m` (`m·e·m = 0`),
then `m·e = 0` — via the square root of `e` and the Frobenius trace argument. -/
theorem mul_eq_zero_of_conj_eq_zero {e m : HermitianMat n ℂ} (he : 0 ≤ e)
    (hme : e.conj m.mat = 0) : m.mat * e.mat = 0 := by
  have hsq : (e.cfc Real.sqrt).mat * (e.cfc Real.sqrt).mat = e.mat := by
    rw [← HermitianMat.mat_cfc_mul_apply]
    have hcongr : e.cfc (fun x => Real.sqrt x * Real.sqrt x) = e.cfc (fun x => x) :=
      HermitianMat.cfc_congr_of_nonneg he fun x hx => Real.mul_self_sqrt hx
    rw [hcongr, HermitianMat.cfc_id']
  have hmat : m.mat * e.mat * m.mat = 0 := by
    have h := congrArg HermitianMat.mat hme
    rw [HermitianMat.conj_apply_mat, m.H] at h
    simpa using h
  have hzero : (m.mat * (e.cfc Real.sqrt).mat) *
      (m.mat * (e.cfc Real.sqrt).mat)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, (e.cfc Real.sqrt).H, m.H]
    calc m.mat * (e.cfc Real.sqrt).mat * ((e.cfc Real.sqrt).mat * m.mat)
        = m.mat * ((e.cfc Real.sqrt).mat * (e.cfc Real.sqrt).mat) * m.mat := by
          noncomm_ring
      _ = m.mat * e.mat * m.mat := by rw [hsq]
      _ = 0 := hmat
  have hms : m.mat * (e.cfc Real.sqrt).mat = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (by rw [hzero, Matrix.trace_zero])
  calc m.mat * e.mat = m.mat * ((e.cfc Real.sqrt).mat * (e.cfc Real.sqrt).mat) := by rw [hsq]
    _ = (m.mat * (e.cfc Real.sqrt).mat) * (e.cfc Real.sqrt).mat := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hms, Matrix.zero_mul]

/-- **Projections are sharp, product-independently**: an effect below both `p` and
`1 - p` is zero. -/
theorem proj_pinch {p e : HermitianMat n ℂ} (hp : p.IsProjection) (he : 0 ≤ e)
    (h1 : e ≤ p) (h2 : e ≤ 1 - p) : e = 0 := by
  have hpp : p.mat * p.mat = p.mat := HermitianMat.isProjection_iff_mat_mul_self.mp hp
  -- pinch by (1 - p): (1-p)·p·(1-p) = 0
  have hp1 : p.conj (1 - p).mat = 0 := by
    ext1
    rw [HermitianMat.conj_apply_mat, (1 - p).H, HermitianMat.mat_sub, HermitianMat.mat_one,
      HermitianMat.mat_zero]
    calc (1 - p.mat) * p.mat * (1 - p.mat)
        = (p.mat - p.mat * p.mat) * (1 - p.mat) := by noncomm_ring
      _ = 0 := by rw [hpp, sub_self, Matrix.zero_mul]
  have h1' : e.conj (1 - p).mat = 0 :=
    le_antisymm (le_of_le_of_eq (HermitianMat.conj_mono h1) hp1) (HermitianMat.conj_nonneg _ he)
  have k1 : (1 - p).mat * e.mat = 0 := mul_eq_zero_of_conj_eq_zero he h1'
  -- pinch by p: p·(1-p)·p = 0
  have hp2 : (1 - p).conj p.mat = 0 := by
    ext1
    rw [HermitianMat.conj_apply_mat, p.H, HermitianMat.mat_sub, HermitianMat.mat_one,
      HermitianMat.mat_zero]
    calc p.mat * (1 - p.mat) * p.mat
        = (p.mat - p.mat * p.mat) * p.mat := by noncomm_ring
      _ = 0 := by rw [hpp, sub_self, Matrix.zero_mul]
  have h2' : e.conj p.mat = 0 :=
    le_antisymm (le_of_le_of_eq (HermitianMat.conj_mono h2) hp2) (HermitianMat.conj_nonneg _ he)
  have k2 : p.mat * e.mat = 0 := mul_eq_zero_of_conj_eq_zero he h2'
  ext1
  rw [HermitianMat.mat_zero]
  calc e.mat = (1 - p).mat * e.mat + p.mat * e.mat := by
        rw [HermitianMat.mat_sub, HermitianMat.mat_one, Matrix.sub_mul, Matrix.one_mul]
        abel
    _ = 0 := by rw [k1, k2, add_zero]

/-! ## Projections under the unknown product -/

variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- The S1 splitting `p ◦' p + p ◦' (1-p) = p` for a projection (indeed any
effect) `p`. -/
theorem sp_self_add_compl {p : HermitianMat n ℂ} (hpe : IsEffect p) :
    P.sp p p + P.sp p (1 - p) = p := by
  have hpc : IsEffect (1 - p) := ⟨sub_nonneg.mpr hpe.2, by simpa using sub_le_self 1 hpe.1⟩
  have hps : p + (1 - p) = (1 : HermitianMat n ℂ) := by abel
  have hle : p + (1 - p) ≤ ousUnit :=
    le_of_eq (hps.trans (HermitianMat.ousUnit_eq_one).symm)
  have hsplit := P.sp_add_right hpe hpe hpc hle
  rw [hps] at hsplit
  have hu : P.sp p (1 : HermitianMat n ℂ) = p := P.sp_unit_right hpe
  rw [hu] at hsplit
  exact hsplit.symm

/-- **A projection annihilates its complement under any sequential product**:
`p ◦' (1-p) = 0`. -/
theorem sp_proj_compl {p : HermitianMat n ℂ} (hp : p.IsProjection) :
    P.sp p (1 - p) = 0 := by
  have hpe : IsEffect p := ⟨hp.nonneg, hp.le_one⟩
  have hpc : IsEffect (1 - p) := ⟨sub_nonneg.mpr hpe.2, by simpa using sub_le_self 1 hpe.1⟩
  -- S6a on the trivial self-compatibility
  have hcompat := P.compatible_ortho hpe hpe rfl
  rw [HermitianMat.ousUnit_eq_one] at hcompat
  -- p ◦' (1-p) ≤ p
  have hz_le_p : P.sp p (1 - p) ≤ p := by
    have h := eq_sub_of_add_eq' (sp_self_add_compl P hpe)
    rw [h]
    exact sub_le_self p (P.sp_nonneg hpe hpe)
  -- (1-p) ◦' p ≤ 1-p, transported through the compatibility
  have hz_le_pc : P.sp p (1 - p) ≤ 1 - p := by
    rw [hcompat]
    have hsplit := sp_self_add_compl P hpc
    rw [sub_sub_cancel] at hsplit
    have h := eq_sub_of_add_eq' hsplit
    rw [h]
    exact sub_le_self (1 - p) (P.sp_nonneg hpc hpc)
  exact proj_pinch hp (P.sp_nonneg hpe hpc) hz_le_p hz_le_pc

/-- **Projections are ◦'-idempotent**: `p ◦' p = p` (the Gudder–Greechie
sharpness theorem, matrix-concrete). -/
theorem sp_proj_self {p : HermitianMat n ℂ} (hp : p.IsProjection) :
    P.sp p p = p := by
  have h := sp_self_add_compl P ⟨hp.nonneg, hp.le_one⟩
  rw [sp_proj_compl P hp, add_zero] at h
  exact h

/-! ## Orthogonal projections -/

theorem orth_compl_isProjection {p q : HermitianMat n ℂ} (hp : p.IsProjection)
    (hq : q.IsProjection) (hpq : p.mat * q.mat = 0) :
    (1 - p - q).IsProjection := by
  have hqp : q.mat * p.mat = 0 := by
    have h := congrArg Matrix.conjTranspose hpq
    rw [Matrix.conjTranspose_mul, p.H, q.H] at h
    simpa using h
  have hpp := HermitianMat.isProjection_iff_mat_mul_self.mp hp
  have hqq := HermitianMat.isProjection_iff_mat_mul_self.mp hq
  rw [HermitianMat.isProjection_iff_mat_mul_self, HermitianMat.mat_sub, HermitianMat.mat_sub,
    HermitianMat.mat_one]
  calc (1 - p.mat - q.mat) * (1 - p.mat - q.mat)
      = 1 - p.mat - q.mat - (p.mat - p.mat * p.mat - p.mat * q.mat)
        - (q.mat - q.mat * p.mat - q.mat * q.mat) := by noncomm_ring
    _ = 1 - p.mat - q.mat := by rw [hpp, hpq, hqp, hqq]; abel

theorem proj_orth_le_one_sub {p q : HermitianMat n ℂ} (hp : p.IsProjection)
    (hq : q.IsProjection) (hpq : p.mat * q.mat = 0) : q ≤ 1 - p :=
  sub_nonneg.mp (orth_compl_isProjection hp hq hpq).nonneg

/-- **Orthogonal projections annihilate** under any sequential product. -/
theorem sp_proj_orth {p q : HermitianMat n ℂ} (hp : p.IsProjection)
    (hq : q.IsProjection) (hpq : p.mat * q.mat = 0) : P.sp p q = 0 := by
  have hpe : IsEffect p := ⟨hp.nonneg, hp.le_one⟩
  have hqe : IsEffect q := ⟨hq.nonneg, hq.le_one⟩
  have hpc : IsEffect (1 - p) := ⟨sub_nonneg.mpr hpe.2, by simpa using sub_le_self 1 hpe.1⟩
  have hle : P.sp p q ≤ P.sp p (1 - p) :=
    P.sp_mono_right hpe hqe hpc (proj_orth_le_one_sub hp hq hpq)
  rw [sp_proj_compl P hp] at hle
  exact le_antisymm hle (P.sp_nonneg hpe hqe)

/-- The reversed order, by S4. -/
theorem sp_proj_orth' {p q : HermitianMat n ℂ} (hp : p.IsProjection)
    (hq : q.IsProjection) (hpq : p.mat * q.mat = 0) : P.sp q p = 0 :=
  P.sp_zero_symm ⟨hp.nonneg, hp.le_one⟩ ⟨hq.nonneg, hq.le_one⟩ (sp_proj_orth P hp hq hpq)

/-- Orthogonal projections are ◦'-compatible (both products vanish). -/
theorem sp_comm_proj_orth {p q : HermitianMat n ℂ} (hp : p.IsProjection)
    (hq : q.IsProjection) (hpq : p.mat * q.mat = 0) : P.sp p q = P.sp q p := by
  rw [sp_proj_orth P hp hq hpq, sp_proj_orth' P hp hq hpq]

end Necessity
