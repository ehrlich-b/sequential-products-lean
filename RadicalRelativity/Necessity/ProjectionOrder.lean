/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.ExtremeEffects

set_option linter.style.longLine false

/-!
# The projection order and its atoms  (M3 bridge layer, part 1)

Order-theoretic structure of projections in `H_n(ℂ)`, feeding the Kadison
step (M3):

* `IsProjection.le_iff_mul_eq` — **absorption order**: for projections,
  `q ≤ p ↔ q·p = q` (forward: conjugate by `1−p` and kill with `XᴴX = 0 ⟹
  X = 0`; backward: `p − q` is then itself a projection, hence `≥ 0`).
* `rankOne ψ` — the rank-one projection `ψψ*` of a unit vector.
* `rankOne_isAtom` — rank-one projections are **atoms** of the projection
  order (outer-product algebra only: a subprojection of `ψψ*` is `wψ*` by
  absorption, idempotence pins the scalar, Hermiticity forces `w ∥ ψ`).
* `IsAtomProjection.exists_rankOne` — conversely every atom is a `rankOne`
  (normalize a vector in the range and squeeze with atomicity).

Atomicity is a purely order-theoretic property, so a unital order-automorphism
transports rank-one projections to rank-one projections (part 2).
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The absorption order on projections -/

/-- For projections, domination is absorption: `q ≤ p ↔ q·p = q`. -/
theorem IsProjection.le_iff_mul_eq {p q : HermitianMat n ℂ}
    (hp : p.IsProjection) (hq : q.IsProjection) :
    q ≤ p ↔ q.mat * p.mat = q.mat := by
  have hpp := isProjection_iff_mat_mul_self.mp hp
  have hqq := isProjection_iff_mat_mul_self.mp hq
  constructor
  · intro hle
    -- conjugating by `1 − p` kills `p`, hence kills `q` below it
    have hmono : q.conj (1 - p).mat ≤ p.conj (1 - p).mat := by
      have h := conj_nonneg (M := (1 - p).mat) (sub_nonneg.mpr hle)
      rw [map_sub] at h
      exact sub_nonneg.mp h
    have hpz : p.conj (1 - p).mat = 0 := by
      ext1
      rw [conj_apply_mat]
      have hH : ((1 - p).mat)ᴴ = (1 - p).mat := (1 - p).H
      rw [hH]
      have hzero : (1 - p).mat * p.mat = 0 := by
        rw [mat_sub, mat_one, sub_mul, one_mul, hpp, sub_self]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc, hzero, Matrix.zero_mul]
      rfl
    have hqz : q.conj (1 - p).mat = 0 :=
      le_antisymm (hpz ▸ hmono) (conj_nonneg (M := (1 - p).mat) hq.nonneg)
    have hmat : (1 - p).mat * q.mat * ((1 - p).mat)ᴴ = 0 := by
      have h := congrArg HermitianMat.mat hqz
      rwa [conj_apply_mat] at h
    -- `X := q(1−p)` has `XᴴX = (1−p)q(1−p) = 0`
    have hX : q.mat * (1 - p).mat = 0 := by
      rw [← Matrix.conjTranspose_mul_self_eq_zero (A := q.mat * (1 - p).mat)]
      have hqH : (q.mat)ᴴ = q.mat := q.H
      have hpH : ((1 - p).mat)ᴴ = (1 - p).mat := (1 - p).H
      calc (q.mat * (1 - p).mat)ᴴ * (q.mat * (1 - p).mat)
          = (1 - p).mat * (q.mat * q.mat) * (1 - p).mat := by
            rw [Matrix.conjTranspose_mul, hqH, hpH]
            noncomm_ring
        _ = (1 - p).mat * q.mat * ((1 - p).mat)ᴴ := by
            rw [hqq, hpH, Matrix.mul_assoc]
        _ = 0 := hmat
    -- expand `q(1−p) = q − qp = 0`
    have hexp : q.mat - q.mat * p.mat = 0 := by
      rw [mat_sub, mat_one, mul_sub, mul_one] at hX
      exact hX
    exact (sub_eq_zero.mp hexp).symm
  · intro hmul
    have hqp : p.mat * q.mat = q.mat := by
      have h := congrArg Matrix.conjTranspose hmul
      rwa [Matrix.conjTranspose_mul, q.H, p.H] at h
    have hproj : (p - q).IsProjection := by
      rw [isProjection_iff_mat_mul_self]
      simp only [mat_sub, sub_mul, mul_sub, hpp, hqq, hmul, hqp]
      abel
    exact sub_nonneg.mp hproj.nonneg

/-! ## Rank-one projections -/

/-- The rank-one matrix `ψψ*` as a Hermitian matrix. -/
def rankOne (ψ : n → ℂ) : HermitianMat n ℂ :=
  ⟨Matrix.vecMulVec ψ (star ψ), by
    show _ᴴ = _
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]⟩

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem rankOne_mat (ψ : n → ℂ) :
    (rankOne ψ).mat = Matrix.vecMulVec ψ (star ψ) := rfl

/-- `ψψ*` is idempotent for a unit vector. -/
theorem rankOne_isProjection {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    (rankOne ψ).IsProjection := by
  rw [isProjection_iff_mat_mul_self, rankOne_mat,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec, hψ, MulOpposite.op_one, one_smul]

omit [DecidableEq n] in
theorem rankOne_ne_zero {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    rankOne ψ ≠ 0 := by
  intro h
  have h2 := congrArg (fun A : HermitianMat n ℂ => A.mat *ᵥ ψ) h
  simp only [rankOne_mat, Matrix.vecMulVec_mulVec, hψ, MulOpposite.op_one,
    one_smul] at h2
  have h3 : star ψ ⬝ᵥ ψ = 0 := by
    rw [show ψ = (0 : HermitianMat n ℂ).mat *ᵥ ψ from h2]
    simp
  rw [hψ] at h3
  exact one_ne_zero h3

/-! ## Atoms of the projection order -/

/-- An **atom** of the projection order: a nonzero projection with no proper
nonzero subprojection. -/
def IsAtomProjection (p : HermitianMat n ℂ) : Prop :=
  p.IsProjection ∧ p ≠ 0 ∧
    ∀ q : HermitianMat n ℂ, q.IsProjection → q ≤ p → q = 0 ∨ q = p

/-- **Rank-one projections are atoms.** -/
theorem rankOne_isAtom {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    IsAtomProjection (rankOne ψ) := by
  refine ⟨rankOne_isProjection hψ, rankOne_ne_zero hψ, ?_⟩
  intro q hq hle
  have habs := (IsProjection.le_iff_mul_eq (rankOne_isProjection hψ) hq).mp hle
  -- `q = w ψ*` with `w := q ψ`
  have hqmat : q.mat = Matrix.vecMulVec (q.mat *ᵥ ψ) (star ψ) := by
    rw [← Matrix.mul_vecMulVec, ← rankOne_mat, habs]
  set w := q.mat *ᵥ ψ with hw
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · right
    have hψ0 : ψ ≠ 0 := by
      intro h
      rw [h] at hψ
      simp at hψ
    have hw0 : w ≠ 0 := by
      intro h
      apply hq0
      ext1
      rw [hqmat, h]
      ext i j
      simp [Matrix.vecMulVec_apply]
    -- idempotence pins the scalar `c := ψ* ⬝ᵥ w` to `1`
    have hsq := isProjection_iff_mat_mul_self.mp hq
    rw [hqmat, Matrix.mul_vecMulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul] at hsq
    obtain ⟨j, hj⟩ : ∃ j, ψ j ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hψ0 (funext hall)
    have hfac : (star ψ ⬝ᵥ w) • w = w := by
      funext i
      have hij := congrFun (congrFun (congrArg (fun M : Matrix n n ℂ => M) hsq) i) j
      simp only [Matrix.vecMulVec_apply] at hij
      have hsj : (star ψ) j ≠ 0 := by
        simp only [Pi.star_apply]
        exact star_ne_zero.mpr hj
      exact mul_right_cancel₀ hsj hij
    have hc1 : star ψ ⬝ᵥ w = 1 := by
      have h2 : ((star ψ ⬝ᵥ w) - 1) • w = 0 := by
        rw [sub_smul, one_smul, hfac, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · linear_combination h3
      · exact absurd h3 hw0
    -- Hermiticity gives `wψ* = ψw*`, hence `w = (w* ⬝ᵥ ψ) • ψ`
    have hherm : Matrix.vecMulVec w (star ψ) = Matrix.vecMulVec ψ (star w) := by
      have hH : (q.mat)ᴴ = q.mat := q.H
      have h2 : (Matrix.vecMulVec w (star ψ))ᴴ = Matrix.vecMulVec ψ (star w) := by
        ext i j
        simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
      calc Matrix.vecMulVec w (star ψ) = q.mat := hqmat.symm
        _ = (q.mat)ᴴ := hH.symm
        _ = (Matrix.vecMulVec w (star ψ))ᴴ := by rw [← hqmat]
        _ = Matrix.vecMulVec ψ (star w) := h2
    have hwpar : w = (star w ⬝ᵥ ψ) • ψ := by
      have h := congrArg (fun M : Matrix n n ℂ => M *ᵥ ψ) hherm
      simpa [Matrix.vecMulVec_mulVec, hψ, op_smul_eq_smul] using h
    -- the two scalars agree, so `w = ψ`
    have hd1 : star w ⬝ᵥ ψ = 1 := by
      have h : star ψ ⬝ᵥ w = (star w ⬝ᵥ ψ) * (star ψ ⬝ᵥ ψ) := by
        conv_lhs => rw [hwpar]
        rw [dotProduct_smul, smul_eq_mul]
      rw [hψ, mul_one] at h
      rw [← h, hc1]
    have hwψ : w = ψ := by rw [hwpar, hd1, one_smul]
    ext1
    rw [hqmat, hwψ, rankOne_mat]

/-- **Every atom is a rank-one projection**: normalize a nonzero vector of the
range and squeeze with atomicity. -/
theorem IsAtomProjection.exists_rankOne {p : HermitianMat n ℂ}
    (hp : IsAtomProjection p) :
    ∃ ψ : n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ p = rankOne ψ := by
  obtain ⟨hproj, hne, hatom⟩ := hp
  -- a nonzero vector in the range
  have hex : ∃ v : n → ℂ, p.mat *ᵥ v ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hne
    ext1
    ext i j
    have h := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using h
  obtain ⟨v, hv⟩ := hex
  set ψ₀ : n → ℂ := p.mat *ᵥ v with hψ₀
  have hfix : p.mat *ᵥ ψ₀ = ψ₀ := by
    rw [hψ₀, Matrix.mulVec_mulVec, isProjection_iff_mat_mul_self.mp hproj]
  -- normalization
  set R : ℝ := ∑ i, Complex.normSq (ψ₀ i) with hR
  have hRpos : 0 < R := by
    obtain ⟨i, hi⟩ : ∃ i, ψ₀ i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hv (funext hall)
    have hterm : 0 < Complex.normSq (ψ₀ i) := Complex.normSq_pos.mpr hi
    exact Finset.sum_pos' (fun m _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, hterm⟩
  have hdot : star ψ₀ ⬝ᵥ ψ₀ = (R : ℂ) := by
    rw [hR]
    push_cast
    simp only [dotProduct, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  set c : ℝ := (Real.sqrt R)⁻¹ with hc
  set ψ : n → ℂ := (c : ℂ) • ψ₀ with hψdef
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hreal : c * (c * R) = 1 := by
    rw [hc, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hRpos.le]
    field_simp
  have hunit : star ψ ⬝ᵥ ψ = 1 := by
    rw [hψdef, star_smul, smul_dotProduct, dotProduct_smul, hdot]
    rw [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_eq_mul]
    exact_mod_cast hreal
  -- `rankOne ψ ≤ p` by absorption
  have hfixψ : p.mat *ᵥ ψ = ψ := by
    rw [hψdef, Matrix.mulVec_smul, hfix]
  have hle : rankOne ψ ≤ p := by
    rw [IsProjection.le_iff_mul_eq hproj (rankOne_isProjection hunit)]
    rw [rankOne_mat, Matrix.vecMulVec_mul]
    congr 1
    have h := congrArg star hfixψ
    rw [Matrix.star_mulVec, p.H] at h
    exact h
  rcases hatom (rankOne ψ) (rankOne_isProjection hunit) hle with h0 | hp'
  · exact absurd h0 (rankOne_ne_zero hunit)
  · exact ⟨ψ, hunit, hp'.symm⟩

end HermitianMat
