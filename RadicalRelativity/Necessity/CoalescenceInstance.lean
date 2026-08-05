/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComparisonInstance
import RadicalRelativity.MasterTheorem.Coalescence

set_option linter.style.longLine false

/-!
# The concrete `CoalescenceSetup` on `H_N(ℂ)`  (campaign LEDGER 2.6 wiring, part 2)

The three Faraut–Korányi fields of `MasterTheorem.CoalescenceSetup`, discharged as
matrix algebra on the concrete carrier:

* `cornerQ i j` — the diagonal indicator of `{i, j}` (equal to `p_i + p_j` for
  `i ≠ j`, to `p_i` for `i = j`; idempotent in every case).
* `cornerJ2 i j b := q b q = b` — the Peirce-2 corner.
* `cornerScalarOn i j a := a = λ q + a₀`, `q a₀ = a₀ q = 0`.
* `corner_commute` — **the FK simultaneous-diagonalization import, replaced by
  matrix algebra**: `q` absorbs corner elements, so `a b = λ b = b a`.
* `diagFamily_scalarOn` — `a(r)` splits as `e^{r_i} q + (rest)` when `r_i = r_j`.
* `blockElt_cornerJ2` — **pure ring algebra**: the Peirce eigenrelations give
  `q x + x q = 2x` (for `i ≠ j`; for `i = j` the relations force `x = 0`), and
  idempotence turns that into `q x q = x`. No entry computations.

`coalescenceSetup` extends `comparisonSetup`; the only cited field in the combined
structure remains `Θ_jordan = ThetaPreservesJordan` (M3).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace
open MasterTheorem

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The corner projection -/

/-- The corner projection: the diagonal indicator of `{i, j}`. Idempotent for every
`i, j` (including `i = j`, where it is `p_i`). -/
def cornerQ (i j : n) : Matrix n n ℂ :=
  Matrix.diagonal (fun k => if k = i ∨ k = j then 1 else 0)

theorem cornerQ_idem (i j : n) : cornerQ i j * cornerQ i j = cornerQ i j := by
  unfold cornerQ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i ∨ k = j <;> simp [h]

theorem cornerQ_eq_add {i j : n} (hij : i ≠ j) :
    cornerQ i j = (frameProj i).mat + (frameProj j).mat := by
  unfold cornerQ
  rw [frameProj_mat, frameProj_mat, Matrix.diagonal_add]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j <;> simp [hki, hkj, Ne.symm hij]

theorem cornerQ_eq_self (i : n) : cornerQ i i = (frameProj i).mat := by
  unfold cornerQ
  rw [frameProj_mat]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

/-! ## The FK predicates, concretely -/

/-- Membership in the Peirce-2 corner `J₂(q)`: `q b q = b`. -/
def cornerJ2 (i j : n) (b : HermitianMat n ℂ) : Prop :=
  cornerQ i j * b.mat * cornerQ i j = b.mat

/-- `a` is scalar on `range q`: `a = λ q + a₀` with `a₀` annihilated by `q` on
both sides. -/
def cornerScalarOn (i j : n) (a : HermitianMat n ℂ) : Prop :=
  ∃ (lam : ℝ) (a₀ : Matrix n n ℂ),
    a.mat = (lam : ℂ) • cornerQ i j + a₀ ∧
      cornerQ i j * a₀ = 0 ∧ a₀ * cornerQ i j = 0

/-- From `q b q = b` and `q² = q`: `q` absorbs `b` on both sides. -/
theorem cornerJ2_absorb {i j : n} {b : HermitianMat n ℂ} (hb : cornerJ2 i j b) :
    cornerQ i j * b.mat = b.mat ∧ b.mat * cornerQ i j = b.mat := by
  constructor
  · calc cornerQ i j * b.mat
        = cornerQ i j * (cornerQ i j * b.mat * cornerQ i j) := by rw [hb]
      _ = (cornerQ i j * cornerQ i j) * b.mat * cornerQ i j := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = cornerQ i j * b.mat * cornerQ i j := by rw [cornerQ_idem]
      _ = b.mat := hb
  · calc b.mat * cornerQ i j
        = (cornerQ i j * b.mat * cornerQ i j) * cornerQ i j := by rw [hb]
      _ = cornerQ i j * b.mat * (cornerQ i j * cornerQ i j) := by
          rw [Matrix.mul_assoc (cornerQ i j * b.mat)]
      _ = cornerQ i j * b.mat * cornerQ i j := by rw [cornerQ_idem]
      _ = b.mat := hb

/-- **The FK simultaneous-diagonalization import, replaced by matrix algebra**:
scalar-on-the-corner and corner-supported elements commute. -/
theorem corner_commute {i j : n} {a b : HermitianMat n ℂ}
    (ha : cornerScalarOn i j a) (hb : cornerJ2 i j b) :
    Commute a.mat b.mat := by
  obtain ⟨lam, a₀, hsum, hqa, haq⟩ := ha
  obtain ⟨habs1, habs2⟩ := cornerJ2_absorb hb
  show a.mat * b.mat = b.mat * a.mat
  rw [hsum, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [habs1, habs2]
  congr 1
  calc a₀ * b.mat
      = a₀ * (cornerQ i j * b.mat) := by rw [habs1]
    _ = (a₀ * cornerQ i j) * b.mat := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [haq, Matrix.zero_mul]
    _ = b.mat * (cornerQ i j * a₀) := by rw [hqa, Matrix.mul_zero]
    _ = (b.mat * cornerQ i j) * a₀ := by rw [Matrix.mul_assoc]
    _ = b.mat * a₀ := by rw [habs2]

/-! ## The diagonal family is scalar on coalesced corners -/

theorem diagFamily_scalarOn {r : n → ℝ} {i j : n} (h : r i = r j) :
    cornerScalarOn i j (diagFamily r) := by
  refine ⟨Real.exp (r i),
    Matrix.diagonal (fun k => if k = i ∨ k = j then 0 else (Real.exp (r k) : ℂ)),
    ?_, ?_, ?_⟩
  · rw [diagFamily_mat]
    unfold cornerQ
    rw [← Matrix.diagonal_smul, Matrix.diagonal_add]
    congr 1
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hki : k = i
    · subst hki
      simp
    · by_cases hkj : k = j
      · subst hkj
        simp [h]
      · simp [hki, hkj]
  · unfold cornerQ
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (if k = i ∨ k = j then (1:ℂ) else 0)
        * (if k = i ∨ k = j then 0 else (Real.exp (r k) : ℂ))) = fun _ => (0:ℂ) from ?_]
    · exact Matrix.diagonal_zero
    · funext k
      by_cases hk : k = i ∨ k = j <;> simp [hk]
  · unfold cornerQ
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (if k = i ∨ k = j then (0:ℂ) else (Real.exp (r k) : ℂ))
        * (if k = i ∨ k = j then 1 else 0)) = fun _ => (0:ℂ) from ?_]
    · exact Matrix.diagonal_zero
    · funext k
      by_cases hk : k = i ∨ k = j <;> simp [hk]

/-! ## Peirce block relations imply corner support (pure ring algebra) -/

/-- The mat-level content of a Peirce eigenrelation `p ∘ x = ½ x`:
`p x + x p = x`. -/
theorem peirce_half_mat {p x : HermitianMat n ℂ}
    (h : p.symmMul x = (1 / 2 : ℝ) • x) :
    p.mat * x.mat + x.mat * p.mat = x.mat := by
  have hmat := congrArg HermitianMat.mat h
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul] at hmat
  have hhalf : ((1/2 : ℝ) • x.mat : Matrix n n ℂ) = (2:ℂ)⁻¹ • x.mat := by
    ext a b
    simp only [Matrix.smul_apply]
    rw [Complex.real_smul]
    norm_num
  rw [hhalf] at hmat
  have h2 := congrArg (fun M => (2 : ℂ) • M) hmat
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_smul] at h2
  exact h2

/-- The mat-level content of a Peirce annihilation `p ∘ x = 0`:
`p x + x p = 0`. -/
theorem peirce_zero_mat {p x : HermitianMat n ℂ}
    (h : p.symmMul x = 0) :
    p.mat * x.mat + x.mat * p.mat = 0 := by
  have hmat := congrArg HermitianMat.mat h
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_zero] at hmat
  have h2 := congrArg (fun M => (2 : ℂ) • M) hmat
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:ℂ) ≠ 0), one_smul,
    smul_zero] at h2
  exact h2

/-- **`block_mem_J2`, proved by ring algebra.** The Peirce relations for
`x ∈ V_{ij}` give `q x q = x`: summing the annihilation relations over
`k ∉ {i,j}` yields `(1−q) x + x (1−q) = 0`, i.e. `q x + x q = 2x`, and
multiplying by the idempotent `q` on each side gives `q x q = q x = x q`,
whence `2 q x q = 2 x`. -/
theorem blockElt_cornerJ2 {i j : n} {x : HermitianMat n ℂ}
    (hk : ∀ k, k ≠ i → k ≠ j → jordanBilin (frameProj k) x = 0) :
    cornerJ2 i j x := by
  set q : Matrix n n ℂ := cornerQ i j with hq
  -- the complement sum: Σ_{k ∉ {i,j}} p_k = 1 − q
  have hcompl : (∑ k ∈ Finset.univ.filter (fun k => ¬(k = i ∨ k = j)),
      (frameProj k).mat) = 1 - q := by
    have hall : (∑ k : n, (frameProj k).mat) = (1 : Matrix n n ℂ) := by
      have hsum : ((∑ k : n, frameProj k : HermitianMat n ℂ)).mat
          = (1 : HermitianMat n ℂ).mat := by rw [sum_frameProj]
      rw [mat_finsetSum, HermitianMat.mat_one] at hsum
      exact hsum
    have hsplit : (∑ k : n, (frameProj k).mat)
        = (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j), (frameProj k).mat)
          + (∑ k ∈ Finset.univ.filter (fun k => ¬(k = i ∨ k = j)), (frameProj k).mat) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hin : (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
        (frameProj k).mat) = q := by
      rw [hq]
      unfold cornerQ
      rw [show (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j), (frameProj k).mat)
          = ∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
            Matrix.diagonal (fun m => if m = k then (1:ℂ) else 0) from
        Finset.sum_congr rfl fun k _ => frameProj_mat k]
      rw [show (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
            Matrix.diagonal (fun m => if m = k then (1:ℂ) else 0))
          = Matrix.diagonal (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
            (fun m => if m = k then (1:ℂ) else 0)) from
        (map_sum (Matrix.diagonalAddMonoidHom n ℂ) _ _).symm]
      congr 1
      funext m
      rw [Finset.sum_apply]
      by_cases hm : m = i ∨ m = j
      · rw [Finset.sum_eq_single m]
        · simp [hm]
        · intro k hkmem hkm
          simp [Ne.symm hkm]
        · intro hmem
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩) hmem
      · rw [Finset.sum_eq_zero, if_neg hm]
        intro k hkmem
        have hkij := (Finset.mem_filter.mp hkmem).2
        have hmk : m ≠ k := by
          intro hcon
          subst hcon
          exact hm hkij
        simp [hmk]
    rw [hall, hin] at hsplit
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsplit.symm
  -- (1 − q) x + x (1 − q) = 0
  have hzero : (1 - q) * x.mat + x.mat * (1 - q) = 0 := by
    rw [← hcompl, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro k hkmem
    have hkij := (Finset.mem_filter.mp hkmem).2
    push_neg at hkij
    exact peirce_zero_mat (by simpa using hk k hkij.1 hkij.2)
  -- hence q x + x q = 2 x
  have h2x : q * x.mat + x.mat * q = (2 : ℂ) • x.mat := by
    have h' : x.mat - q * x.mat + (x.mat - x.mat * q) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at hzero
      exact hzero
    calc q * x.mat + x.mat * q
        = (x.mat + x.mat) - ((x.mat - q * x.mat) + (x.mat - x.mat * q)) := by abel
      _ = (x.mat + x.mat) - 0 := by rw [h']
      _ = (2 : ℂ) • x.mat := by rw [sub_zero, two_smul]
  -- multiply by the idempotent q on each side
  have hqx : q * x.mat * q = q * x.mat := by
    have hL := congrArg (fun M => q * M) h2x
    simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc] at hL
    rw [show q * q = q from cornerQ_idem i j] at hL
    rw [two_smul] at hL
    exact add_left_cancel hL
  have hxq : q * x.mat * q = x.mat * q := by
    have hR := congrArg (fun M => M * q) h2x
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] at hR
    rw [show q * q = q from cornerQ_idem i j] at hR
    rw [two_smul, ← Matrix.mul_assoc] at hR
    exact add_right_cancel hR
  -- combine: 2 (q x q) = q x + x q = 2 x
  show q * x.mat * q = x.mat
  have hcomb : (2 : ℂ) • (q * x.mat * q) = (2 : ℂ) • x.mat := by
    rw [two_smul]
    calc q * x.mat * q + q * x.mat * q
        = q * x.mat + q * x.mat * q := by nth_rewrite 1 [hqx]; rfl
      _ = q * x.mat + x.mat * q := by rw [hxq]
      _ = (2 : ℂ) • x.mat := h2x
  exact smul_right_injective (Matrix n n ℂ) (by norm_num : (2:ℂ) ≠ 0) hcomb

/-! ## The instance -/

/-- **The concrete `CoalescenceSetup` on `H_N(ℂ)`**, extending `comparisonSetup`.
All three FK fields (`simDiag_opCommute`, `aOf_scalarOn`, `block_mem_J2`) are
discharged by the matrix-algebra theorems above; the only cited hypothesis in the
combined structure remains `Θ_jordan = ThetaPreservesJordan` (M3). The abstract
`coalescence_J2q` / `coalescence_block` / `block_preserved` now hold concretely. -/
def coalescenceSetup {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    CoalescenceSetup (HermitianMat (Fin N) ℂ) :=
  { comparisonSetup hN P hS2 hjord with
    J2 := cornerJ2
    ScalarOn := cornerScalarOn
    simDiag_opCommute := fun _ _ _ _ hsc hb =>
      opCommute_of_commute (corner_commute hsc hb)
    aOf_scalarOn := fun _ i j h => diagFamily_scalarOn h
    block_mem_J2 := fun _ _ x hx => blockElt_cornerJ2 hx.2.2 }

end Necessity
