/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComparisonInstanceGen
import RadicalRelativity.MasterTheorem.Coalescence

set_option linter.style.longLine false

/-!
# The concrete `CoalescenceSetup` on `H_N(𝕜)`  (campaign LEDGER 2.6 wiring, part 2)

The three Faraut–Korányi fields of `MasterTheorem.CoalescenceSetup`, discharged as
matrix algebra on the concrete carrier:

* `cornerQG 𝕜 i j` — the diagonal indicator of `{i, j}` (equal to `p_i + p_j` for
  `i ≠ j`, to `p_i` for `i = j`; idempotent in every case).
* `cornerJ2G i j b := q b q = b` — the Peirce-2 corner.
* `cornerScalarOnG i j a := a = λ q + a₀`, `q a₀ = a₀ q = 0`.
* `corner_commuteG` — **the FK simultaneous-diagonalization import, replaced by
  matrix algebra**: `q` absorbs corner elements, so `a b = λ b = b a`.
* `diagFamilyG_scalarOn` — `a(r)` splits as `e^{r_i} q + (rest)` when `r_i = r_j`.
* `blockElt_cornerJ2G` — **pure ring algebra**: the Peirce eigenrelations give
  `q x + x q = 2x` (for `i ≠ j`; for `i = j` the relations force `x = 0`), and
  idempotence turns that into `q x q = x`. No entry computations.

`coalescenceSetupG` extends `comparisonSetupG`; the only cited field in the combined
structure remains `Θ_jordan = ThetaPreservesJordanG` (M3).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace
open MasterTheorem

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The corner projection -/

/-- The corner projection: the diagonal indicator of `{i, j}`. Idempotent for every
`i, j` (including `i = j`, where it is `p_i`). -/
def cornerQG (𝕜 : Type*) [RCLike 𝕜] (i j : n) : Matrix n n 𝕜 :=
  Matrix.diagonal (fun k => if k = i ∨ k = j then 1 else 0)

theorem cornerQ_idemG (i j : n) : cornerQG 𝕜 i j * cornerQG 𝕜 i j = cornerQG 𝕜 i j := by
  unfold cornerQG
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  by_cases h : k = i ∨ k = j <;> simp [h]

theorem cornerQ_eq_addG {i j : n} (hij : i ≠ j) :
    cornerQG 𝕜 i j = (frameProjG 𝕜 i).mat + (frameProjG 𝕜 j).mat := by
  unfold cornerQG
  rw [frameProjG_mat, frameProjG_mat, Matrix.diagonal_add]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j <;> simp [hki, hkj, Ne.symm hij]

theorem cornerQ_eq_selfG (i : n) : cornerQG 𝕜 i i = (frameProjG 𝕜 i).mat := by
  unfold cornerQG
  rw [frameProjG_mat]
  congr 1
  funext k
  by_cases h : k = i <;> simp [h]

/-! ## The FK predicates, concretely -/

/-- Membership in the Peirce-2 corner `J₂(q)`: `q b q = b`. -/
def cornerJ2G (i j : n) (b : HermitianMat n 𝕜) : Prop :=
  cornerQG 𝕜 i j * b.mat * cornerQG 𝕜 i j = b.mat

/-- `a` is scalar on `range q`: `a = λ q + a₀` with `a₀` annihilated by `q` on
both sides. -/
def cornerScalarOnG (i j : n) (a : HermitianMat n 𝕜) : Prop :=
  ∃ (lam : ℝ) (a₀ : Matrix n n 𝕜),
    a.mat = (lam : 𝕜) • cornerQG 𝕜 i j + a₀ ∧
      cornerQG 𝕜 i j * a₀ = 0 ∧ a₀ * cornerQG 𝕜 i j = 0

/-- From `q b q = b` and `q² = q`: `q` absorbs `b` on both sides. -/
theorem cornerJ2_absorbG {i j : n} {b : HermitianMat n 𝕜} (hb : cornerJ2G i j b) :
    cornerQG 𝕜 i j * b.mat = b.mat ∧ b.mat * cornerQG 𝕜 i j = b.mat := by
  constructor
  · calc cornerQG 𝕜 i j * b.mat
        = cornerQG 𝕜 i j * (cornerQG 𝕜 i j * b.mat * cornerQG 𝕜 i j) := by rw [hb]
      _ = (cornerQG 𝕜 i j * cornerQG 𝕜 i j) * b.mat * cornerQG 𝕜 i j := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
      _ = cornerQG 𝕜 i j * b.mat * cornerQG 𝕜 i j := by rw [cornerQ_idemG]
      _ = b.mat := hb
  · calc b.mat * cornerQG 𝕜 i j
        = (cornerQG 𝕜 i j * b.mat * cornerQG 𝕜 i j) * cornerQG 𝕜 i j := by rw [hb]
      _ = cornerQG 𝕜 i j * b.mat * (cornerQG 𝕜 i j * cornerQG 𝕜 i j) := by
          rw [Matrix.mul_assoc (cornerQG 𝕜 i j * b.mat)]
      _ = cornerQG 𝕜 i j * b.mat * cornerQG 𝕜 i j := by rw [cornerQ_idemG]
      _ = b.mat := hb

/-- **The FK simultaneous-diagonalization import, replaced by matrix algebra**:
scalar-on-the-corner and corner-supported elements commute. -/
theorem corner_commuteG {i j : n} {a b : HermitianMat n 𝕜}
    (ha : cornerScalarOnG i j a) (hb : cornerJ2G i j b) :
    Commute a.mat b.mat := by
  obtain ⟨lam, a₀, hsum, hqa, haq⟩ := ha
  obtain ⟨habs1, habs2⟩ := cornerJ2_absorbG hb
  show a.mat * b.mat = b.mat * a.mat
  rw [hsum, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  rw [habs1, habs2]
  congr 1
  calc a₀ * b.mat
      = a₀ * (cornerQG 𝕜 i j * b.mat) := by rw [habs1]
    _ = (a₀ * cornerQG 𝕜 i j) * b.mat := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [haq, Matrix.zero_mul]
    _ = b.mat * (cornerQG 𝕜 i j * a₀) := by rw [hqa, Matrix.mul_zero]
    _ = (b.mat * cornerQG 𝕜 i j) * a₀ := by rw [Matrix.mul_assoc]
    _ = b.mat * a₀ := by rw [habs2]

/-! ## The diagonal family is scalar on coalesced corners -/

theorem diagFamilyG_scalarOn {r : n → ℝ} {i j : n} (h : r i = r j) :
    cornerScalarOnG i j (diagFamilyG 𝕜 r) := by
  refine ⟨Real.exp (r i),
    Matrix.diagonal (fun k => if k = i ∨ k = j then 0 else (Real.exp (r k) : 𝕜)),
    ?_, ?_, ?_⟩
  · rw [diagFamilyG_mat]
    unfold cornerQG
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
  · unfold cornerQG
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (if k = i ∨ k = j then (1:𝕜) else 0)
        * (if k = i ∨ k = j then 0 else (Real.exp (r k) : 𝕜))) = fun _ => (0:𝕜) from ?_]
    · exact Matrix.diagonal_zero
    · funext k
      by_cases hk : k = i ∨ k = j <;> simp [hk]
  · unfold cornerQG
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (if k = i ∨ k = j then (0:𝕜) else (Real.exp (r k) : 𝕜))
        * (if k = i ∨ k = j then 1 else 0)) = fun _ => (0:𝕜) from ?_]
    · exact Matrix.diagonal_zero
    · funext k
      by_cases hk : k = i ∨ k = j <;> simp [hk]

/-! ## Peirce block relations imply corner support (pure ring algebra) -/

/-- The mat-level content of a Peirce eigenrelation `p ∘ x = ½ x`:
`p x + x p = x`. -/
theorem peirce_half_matG {p x : HermitianMat n 𝕜}
    (h : p.symmMul x = (1 / 2 : ℝ) • x) :
    p.mat * x.mat + x.mat * p.mat = x.mat := by
  have hmat := congrArg HermitianMat.mat h
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_smul] at hmat
  have hhalf : ((1/2 : ℝ) • x.mat : Matrix n n 𝕜) = (2:𝕜)⁻¹ • x.mat := by
    have hc : ((2 : 𝕜))⁻¹ = ((1/2 : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_div, RCLike.ofReal_one, RCLike.ofReal_ofNat, one_div]
    rw [hc]
    ext a b
    simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  rw [hhalf] at hmat
  have h2 := congrArg (fun M => (2 : 𝕜) • M) hmat
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:𝕜) ≠ 0), one_smul] at h2
  exact h2

/-- The mat-level content of a Peirce annihilation `p ∘ x = 0`:
`p x + x p = 0`. -/
theorem peirce_zero_matG {p x : HermitianMat n 𝕜}
    (h : p.symmMul x = 0) :
    p.mat * x.mat + x.mat * p.mat = 0 := by
  have hmat := congrArg HermitianMat.mat h
  rw [HermitianMat.symmMul_toMat, HermitianMat.mat_zero] at hmat
  have h2 := congrArg (fun M => (2 : 𝕜) • M) hmat
  simp only [smul_smul, mul_inv_cancel₀ (by norm_num : (2:𝕜) ≠ 0), one_smul,
    smul_zero] at h2
  exact h2

/-- The double-relation closes the corner: `q x + x q = 2x` with `q` idempotent
gives `q x q = x` (multiply by `q` on each side, then add). -/
theorem cornerJ2_of_doubleG {i j : n} {x : HermitianMat n 𝕜}
    (h2x : cornerQG 𝕜 i j * x.mat + x.mat * cornerQG 𝕜 i j = (2 : 𝕜) • x.mat) :
    cornerJ2G i j x := by
  set q : Matrix n n 𝕜 := cornerQG 𝕜 i j with hq
  have hqx : q * x.mat * q = q * x.mat := by
    have hL := congrArg (fun M => q * M) h2x
    simp only [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc] at hL
    rw [show q * q = q from cornerQ_idemG i j] at hL
    rw [two_smul] at hL
    exact add_left_cancel hL
  have hxq : q * x.mat * q = x.mat * q := by
    have hR := congrArg (fun M => M * q) h2x
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc] at hR
    rw [show q * q = q from cornerQ_idemG i j] at hR
    rw [two_smul, ← Matrix.mul_assoc] at hR
    exact add_right_cancel hR
  show q * x.mat * q = x.mat
  have hcomb : (2 : 𝕜) • (q * x.mat * q) = (2 : 𝕜) • x.mat := by
    rw [two_smul]
    calc q * x.mat * q + q * x.mat * q
        = q * x.mat + q * x.mat * q := by nth_rewrite 1 [hqx]; rfl
      _ = q * x.mat + x.mat * q := by rw [hxq]
      _ = (2 : 𝕜) • x.mat := h2x
  exact smul_right_injective (Matrix n n 𝕜) (by norm_num : (2:𝕜) ≠ 0) hcomb

/-- **`block_mem_J2`, proved by ring algebra.** The Peirce annihilation
relations for `x ∈ V_{ij}` give `q x q = x`: summing over `k ∉ {i,j}` yields
`(1−q) x + x (1−q) = 0`, i.e. `q x + x q = 2x`, and `cornerJ2_of_doubleG`
closes. -/
theorem blockElt_cornerJ2G {i j : n} {x : HermitianMat n 𝕜}
    (hk : ∀ k, k ≠ i → k ≠ j → jordanBilinG 𝕜 (frameProjG 𝕜 k) x = 0) :
    cornerJ2G i j x := by
  set q : Matrix n n 𝕜 := cornerQG 𝕜 i j with hq
  -- the complement sum: Σ_{k ∉ {i,j}} p_k = 1 − q
  have hcompl : (∑ k ∈ Finset.univ.filter (fun k => ¬(k = i ∨ k = j)),
      (frameProjG 𝕜 k).mat) = 1 - q := by
    have hall : (∑ k : n, (frameProjG 𝕜 k).mat) = (1 : Matrix n n 𝕜) := by
      have hsum : ((∑ k : n, frameProjG 𝕜 k : HermitianMat n 𝕜)).mat
          = (1 : HermitianMat n 𝕜).mat := by rw [sum_frameProjG]
      rw [mat_finsetSum, HermitianMat.mat_one] at hsum
      exact hsum
    have hsplit : (∑ k : n, (frameProjG 𝕜 k).mat)
        = (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j), (frameProjG 𝕜 k).mat)
          + (∑ k ∈ Finset.univ.filter (fun k => ¬(k = i ∨ k = j)), (frameProjG 𝕜 k).mat) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hin : (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
        (frameProjG 𝕜 k).mat) = q := by
      rw [hq]
      unfold cornerQG
      rw [show (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j), (frameProjG 𝕜 k).mat)
          = ∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
            Matrix.diagonal (fun m => if m = k then (1:𝕜) else 0) from
        Finset.sum_congr rfl fun k _ => frameProjG_mat k]
      rw [show (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
            Matrix.diagonal (fun m => if m = k then (1:𝕜) else 0))
          = Matrix.diagonal (∑ k ∈ Finset.univ.filter (fun k => k = i ∨ k = j),
            (fun m => if m = k then (1:𝕜) else 0)) from
        (map_sum (Matrix.diagonalAddMonoidHom n 𝕜) _ _).symm]
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
    exact peirce_zero_matG (by simpa using hk k hkij.1 hkij.2)
  -- hence q x + x q = 2 x
  have h2x : q * x.mat + x.mat * q = (2 : 𝕜) • x.mat := by
    have h' : x.mat - q * x.mat + (x.mat - x.mat * q) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one] at hzero
      exact hzero
    calc q * x.mat + x.mat * q
        = (x.mat + x.mat) - ((x.mat - q * x.mat) + (x.mat - x.mat * q)) := by abel
      _ = (x.mat + x.mat) - 0 := by rw [h']
      _ = (2 : 𝕜) • x.mat := by rw [sub_zero, two_smul]
  exact cornerJ2_of_doubleG h2x

/-! ## The instance -/

/-- **The concrete `CoalescenceSetup` on `H_N(𝕜)`**, extending `comparisonSetupG`.
All three FK fields (`simDiag_opCommute`, `aOf_scalarOn`, `block_mem_J2`) are
discharged by the matrix-algebra theorems above; the only cited hypothesis in the
combined structure remains `Θ_jordan = ThetaPreservesJordanG` (M3). The abstract
`coalescence_J2q` / `coalescence_block` / `block_preserved` now hold concretely. -/
def coalescenceSetupG {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) 𝕜))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P) :
    CoalescenceSetup (HermitianMat (Fin N) 𝕜) :=
  { comparisonSetupG hN P hS2 hjord with
    J2 := cornerJ2G
    ScalarOn := cornerScalarOnG
    simDiag_opCommute := fun _ _ _ _ hsc hb =>
      opCommute_of_commuteG (corner_commuteG hsc hb)
    aOf_scalarOn := fun _ i j h => diagFamilyG_scalarOn h
    block_mem_J2 := fun _ _ x hx => blockElt_cornerJ2G hx.2.2 }

end Necessity
