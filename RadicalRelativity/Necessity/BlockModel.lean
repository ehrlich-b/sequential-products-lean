/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockInvariance

set_option linter.style.longLine false

/-!
# The off-diagonal block model and the square law  (LEDGER 2.6, u2)

The Peirce-½ block `V_{ij} ≅ ℂ` concretely:

* `blockHerm i j z = z E_ij + z̄ E_ji` — the block parametrization.
* `blockHerm_sq` — the **square law**: `x² = |z|² (p_i + p_j)` for block `x`.
* `blockHerm_peirce_*` — the block satisfies the Peirce eigenrelations.
* `eq_blockHerm_of_peirce` — conversely, the eigenrelations force the support:
  any Hermitian `x` with `p_i ∘ x = ½x`, `p_j ∘ x = ½x`, `p_k ∘ x = 0` is
  `blockHerm i j (x_{ij})`.
* `normSq_thetaNorm_block` — **Euclidean norm preservation on blocks with no
  norm imports**: Θ is a Jordan map fixing the frame, so
  `|w|²(p_i+p_j) = (Θx)² = Θ(x²) = |z|²(p_i+p_j)`, and comparing the `(i,i)`
  entry gives `|w| = |z|`. This is the isometry input for the skewness of the
  block restriction of `dχ` (u5).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The block parametrization -/

theorem blockE_isHermitian (i j : n) (z : ℂ) :
    (z • Matrix.single i j (1 : ℂ) + star z • Matrix.single j i (1 : ℂ)).IsHermitian := by
  show _ᴴ = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    single_conjTranspose, single_conjTranspose, star_star]
  exact add_comm _ _

/-- The block element `z E_ij + z̄ E_ji`. -/
def blockHerm (i j : n) (z : ℂ) : HermitianMat n ℂ :=
  ⟨z • Matrix.single i j (1 : ℂ) + star z • Matrix.single j i (1 : ℂ),
    blockE_isHermitian i j z⟩

@[simp]
theorem blockHerm_mat (i j : n) (z : ℂ) :
    (blockHerm i j z).mat
      = z • Matrix.single i j (1 : ℂ) + star z • Matrix.single j i (1 : ℂ) := rfl

theorem frameProj_mat_eq_single (i : n) :
    (frameProj i).mat = Matrix.single i i (1 : ℂ) := by
  rw [frameProj_mat]
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    by_cases hai : a = i
    · subst hai
      simp [Matrix.single]
    · have hia : (i = a) = False := eq_false fun h => hai h.symm
      simp [Matrix.single, hia, hai]
  · rw [Matrix.diagonal_apply_ne _ hab]
    have : ¬(i = a ∧ i = b) := fun ⟨h1, h2⟩ => hab (h1 ▸ h2)
    simp [Matrix.single, this]

/-! ## The square law -/

theorem blockHerm_sq_mat {i j : n} (hij : i ≠ j) (z : ℂ) :
    (blockHerm i j z).mat * (blockHerm i j z).mat
      = (Complex.normSq z : ℂ) • ((frameProj i).mat + (frameProj j).mat) := by
  have e1 : Matrix.single i j (1:ℂ) * Matrix.single i j 1 = 0 := by
    simp [Ne.symm hij]
  have e2 : Matrix.single i j (1:ℂ) * Matrix.single j i 1 = Matrix.single i i 1 := by
    simp
  have e3 : Matrix.single j i (1:ℂ) * Matrix.single i j 1 = Matrix.single j j 1 := by
    simp
  have e4 : Matrix.single j i (1:ℂ) * Matrix.single j i 1 = 0 := by
    simp [hij]
  rw [blockHerm_mat, frameProj_mat_eq_single, frameProj_mat_eq_single]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e1, e2, e3, e4,
    smul_zero, add_zero, zero_add]
  rw [smul_add, Complex.star_def, mul_comm ((starRingEnd ℂ) z) z, Complex.mul_conj]

/-- The square law at the `HermitianMat` level: `x ∘ x = |z|² • (p_i + p_j)`. -/
theorem blockHerm_symmMul_self {i j : n} (hij : i ≠ j) (z : ℂ) :
    (blockHerm i j z).symmMul (blockHerm i j z)
      = (Complex.normSq z : ℝ) • (frameProj i + frameProj j) := by
  ext1
  rw [HermitianMat.symmMul_self, blockHerm_sq_mat hij z, HermitianMat.mat_smul,
    HermitianMat.mat_add]
  ext a b
  simp [Complex.real_smul, mul_add]

/-! ## Entry helpers -/

theorem single_one_mul_apply (i a b : n) (X : Matrix n n ℂ) :
    (Matrix.single i i (1 : ℂ) * X) a b = if a = i then X i b else 0 := by
  by_cases hai : a = i
  · subst hai
    rw [if_pos rfl, Matrix.mul_apply, Finset.sum_eq_single a]
    · simp [Matrix.single]
    · intro k _ hk
      have hak : (a = k) = False := eq_false fun h => hk h.symm
      simp [Matrix.single, hak]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [if_neg hai, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have : ¬(i = a ∧ i = k) := fun ⟨h1, _⟩ => hai h1.symm
    simp [Matrix.single, this]

theorem mul_single_one_apply (i a b : n) (X : Matrix n n ℂ) :
    (X * Matrix.single i i (1 : ℂ)) a b = if b = i then X a i else 0 := by
  by_cases hbi : b = i
  · subst hbi
    rw [if_pos rfl, Matrix.mul_apply, Finset.sum_eq_single b]
    · simp [Matrix.single]
    · intro k _ hk
      have hbk : (b = k) = False := eq_false fun h => hk h.symm
      simp [Matrix.single, hbk]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · rw [if_neg hbi, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    have : ¬(i = k ∧ i = b) := fun ⟨_, h2⟩ => hbi h2.symm
    simp [Matrix.single, this]

/-! ## The support characterization -/

/-- **The Peirce eigenrelations force the block support**: a Hermitian matrix with
`p_i ∘ x = ½x`, `p_j ∘ x = ½x`, and `p_k ∘ x = 0` for `k ∉ {i,j}` equals
`blockHerm i j (x_{ij})`. -/
theorem eq_blockHerm_of_peirce {i j : n} (hij : i ≠ j) {x : HermitianMat n ℂ}
    (hi : (frameProj i).symmMul x = (1 / 2 : ℝ) • x)
    (hj : (frameProj j).symmMul x = (1 / 2 : ℝ) • x)
    (hk : ∀ k, k ≠ i → k ≠ j → (frameProj k).symmMul x = 0) :
    x = blockHerm i j (x.mat i j) := by
  have hi' := peirce_half_mat hi
  have hj' := peirce_half_mat hj
  have hk' : ∀ k, k ≠ i → k ≠ j →
      (frameProj k).mat * x.mat + x.mat * (frameProj k).mat = 0 :=
    fun k h1 h2 => peirce_zero_mat (hk k h1 h2)
  rw [frameProj_mat_eq_single] at hi' hj'
  have hk'' : ∀ k, k ≠ i → k ≠ j →
      Matrix.single k k (1:ℂ) * x.mat + x.mat * Matrix.single k k 1 = 0 := by
    intro k h1 h2
    have := hk' k h1 h2
    rwa [frameProj_mat_eq_single] at this
  -- rows outside {i,j} vanish
  have hrow : ∀ a b : n, a ≠ i → a ≠ j → x.mat a b = 0 := by
    intro a b hai haj
    have h := congrArg (fun M => M a b) (hk'' a hai haj)
    simp only [Matrix.add_apply, Matrix.zero_apply] at h
    rw [single_one_mul_apply, mul_single_one_apply, if_pos rfl] at h
    by_cases hba : b = a
    · subst hba
      rw [if_pos rfl] at h
      have h2 : (2 : ℂ) * x.mat b b = 0 := by rw [two_mul]; exact h
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    · rw [if_neg hba, add_zero] at h
      exact h
  -- columns outside {i,j} vanish (Hermitian symmetry)
  have hcol : ∀ a b : n, b ≠ i → b ≠ j → x.mat a b = 0 := by
    intro a b hbi hbj
    have h := hrow b a hbi hbj
    have hherm : x.mat a b = star (x.mat b a) := by
      have := congrArg (fun M => M a b) x.H
      simpa [Matrix.conjTranspose_apply] using this.symm
    rw [hherm, h, star_zero]
  -- diagonal entries at i and j vanish
  have hii : x.mat i i = 0 := by
    have h := congrArg (fun M => M i i) hi'
    simp only [Matrix.add_apply] at h
    rw [single_one_mul_apply, mul_single_one_apply] at h
    simp only [if_true] at h
    linear_combination h
  have hjj : x.mat j j = 0 := by
    have h := congrArg (fun M => M j j) hj'
    simp only [Matrix.add_apply] at h
    rw [single_one_mul_apply, mul_single_one_apply] at h
    simp only [if_true] at h
    linear_combination h
  ext1
  rw [blockHerm_mat]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  -- case bash
  by_cases hai : a = i
  · by_cases hbj : b = j
    · have c1 : (i = a ∧ j = b) = True := eq_true ⟨hai.symm, hbj.symm⟩
      have c2 : (j = a ∧ i = b) = False :=
        eq_false fun ⟨h', _⟩ => hij ((h'.trans hai).symm)
      conv_lhs => rw [hai, hbj]
      simp [Matrix.single, c1, c2]
    · by_cases hbi : b = i
      · have c1 : (i = a ∧ j = b) = False := eq_false fun ⟨_, h'⟩ => hbj h'.symm
        have c2 : (j = a ∧ i = b) = False :=
          eq_false fun ⟨h', _⟩ => hij ((h'.trans hai).symm)
        conv_lhs => rw [hai, hbi, hii]
        simp [Matrix.single, c1, c2]
      · have c1 : (i = a ∧ j = b) = False := eq_false fun ⟨_, h'⟩ => hbj h'.symm
        have c2 : (j = a ∧ i = b) = False := eq_false fun ⟨_, h'⟩ => hbi h'.symm
        rw [hcol a b hbi hbj]
        simp [Matrix.single, c1, c2]
  · by_cases haj : a = j
    · by_cases hbi : b = i
      · have c1 : (i = a ∧ j = b) = False := eq_false fun ⟨h', _⟩ => hai h'.symm
        have c2 : (j = a ∧ i = b) = True := eq_true ⟨haj.symm, hbi.symm⟩
        have hherm : x.mat j i = (starRingEnd ℂ) (x.mat i j) := by
          have hH := congrArg (fun M => M j i) x.H
          simp only [Matrix.conjTranspose_apply] at hH
          rw [← hH, Complex.star_def]
        conv_lhs => rw [haj, hbi, hherm]
        simp [Matrix.single, c1, c2]
      · by_cases hbj : b = j
        · have c1 : (i = a ∧ j = b) = False := eq_false fun ⟨h', _⟩ => hai h'.symm
          have c2 : (j = a ∧ i = b) = False :=
            eq_false fun ⟨_, h'⟩ => hij (h'.trans hbj)
          conv_lhs => rw [haj, hbj, hjj]
          simp [Matrix.single, c1, c2]
        · have c1 : (i = a ∧ j = b) = False := eq_false fun ⟨h', _⟩ => hai h'.symm
          have c2 : (j = a ∧ i = b) = False := eq_false fun ⟨_, h'⟩ => hbi h'.symm
          rw [hcol a b hbi hbj]
          simp [Matrix.single, c1, c2]
    · have c1 : (i = a ∧ j = b) = False := eq_false fun ⟨h', _⟩ => hai h'.symm
      have c2 : (j = a ∧ i = b) = False := eq_false fun ⟨h', _⟩ => haj h'.symm
      rw [hrow a b hai haj]
      simp [Matrix.single, c1, c2]

end Necessity
