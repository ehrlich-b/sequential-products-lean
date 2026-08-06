/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockModelGen

set_option linter.style.longLine false

/-!
# The frame projections and the blocks span, over any `RCLike` field (M4.1 twin)

Every Hermitian matrix is the sum of its diagonal part, spread over the frame
projections, and its off-diagonal part, spread over the Peirce blocks:

`x = Σ_i (x_ii) • p_i + ½ Σ_{i ≠ j} blockHermG i j (x_ij)`.

The `½` is because each unordered pair `{i,j}` is visited twice by the ordered
`offDiag` sum, and `blockHermG i j (x_ij)` and `blockHermG j i (x_ji)` are the
same matrix.

This is the spanning statement the `Ad_{a^{it}}` identification needs: two
`ℝ`-linear maps agreeing on the frame projections and on every block are equal
(`linearMap_eq_of_frame_blockG`).  The rank-one spanning lemma of M3 does not
substitute — that is a different spanning set.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Two auxiliary lemmas -/

/-- A sum whose summand vanishes off a two-element support. -/
theorem sum_eq_two_of_supportG {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    {s : Finset α} {f : α → M} {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (h : ∀ c ∈ s, c ≠ a → c ≠ b → f c = 0) :
    ∑ c ∈ s, f c = f a + f b := by
  rw [← Finset.sum_pair hab]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  · intro y hy hny
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hny
    exact h y hy hny.1 hny.2

/-- The underlying matrix of a finite sum is the sum of the matrices. -/
theorem mat_sumG {ι : Type*} (s : Finset ι) (f : ι → HermitianMat n 𝕜) :
    (∑ i ∈ s, f i).mat = ∑ i ∈ s, (f i).mat := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianMat.mat_add, ih]

/-- The diagonal entries of a Hermitian matrix are real. -/
theorem diag_eq_ofRealG (x : HermitianMat n 𝕜) (a : n) :
    x.mat a a = (RCLike.re (x.mat a a) : 𝕜) := by
  have hH := congrArg (fun M : Matrix n n 𝕜 => M a a) x.H
  simp only [Matrix.conjTranspose_apply] at hH
  exact (RCLike.conj_eq_iff_re.mp (by
    rw [RCLike.star_def] at hH
    exact hH)).symm

/-! ## The spanning identity -/

/-- **The frame-and-block decomposition.** -/
theorem eq_frame_add_blocksG (x : HermitianMat n 𝕜) :
    x = (∑ i, (RCLike.re (x.mat i i) : ℝ) • frameProjG 𝕜 i)
      + (1 / 2 : ℝ) • (∑ p ∈ Finset.univ.offDiag,
          blockHermG p.1 p.2 (x.mat p.1 p.2)) := by
  ext1
  rw [HermitianMat.mat_add, HermitianMat.mat_smul, mat_sumG, mat_sumG]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply]
  -- the frame part
  have hframe : (∑ i, ((RCLike.re (x.mat i i) : ℝ) • frameProjG 𝕜 i).mat a b)
      = if a = b then x.mat a b else 0 := by
    have hterm : ∀ i : n, ((RCLike.re (x.mat i i) : ℝ) • frameProjG 𝕜 i).mat a b
        = if i = a ∧ i = b then (RCLike.re (x.mat i i) : 𝕜) else 0 := by
      intro i
      rw [HermitianMat.mat_smul, frameProj_mat_eq_singleG]
      simp only [Matrix.smul_apply, Matrix.single, Matrix.of_apply,
        RCLike.real_smul_eq_coe_mul]
      by_cases hc : i = a ∧ i = b
      · rw [if_pos hc, if_pos hc, mul_one]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, Finset.sum_eq_single a]
      · rw [if_pos ⟨rfl, rfl⟩]
        exact (diag_eq_ofRealG x a).symm
      · intro i _ hi
        rw [if_neg (fun hc => hi hc.1)]
      · intro h; exact absurd (Finset.mem_univ a) h
    · rw [if_neg hab]
      apply Finset.sum_eq_zero
      intro i _
      refine if_neg ?_
      intro hc
      exact hab (hc.1 ▸ hc.2)
  -- the block part
  have hblock : (∑ p ∈ Finset.univ.offDiag,
        (blockHermG p.1 p.2 (x.mat p.1 p.2)).mat a b)
      = if a = b then 0 else 2 * x.mat a b := by
    have hterm : ∀ p : n × n, (blockHermG p.1 p.2 (x.mat p.1 p.2)).mat a b
        = (if p.1 = a ∧ p.2 = b then x.mat p.1 p.2 else 0)
          + (if p.2 = a ∧ p.1 = b then star (x.mat p.1 p.2) else 0) := by
      intro p
      rw [blockHerm_matG]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single, Matrix.of_apply,
        smul_eq_mul]
      by_cases h1 : p.1 = a ∧ p.2 = b
      · by_cases h2 : p.2 = a ∧ p.1 = b
        · rw [if_pos h1, if_pos h1, if_pos h2, if_pos h2, mul_one, mul_one]
        · rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2, mul_one, mul_zero]
      · by_cases h2 : p.2 = a ∧ p.1 = b
        · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, mul_zero, mul_one]
        · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl fun p _ => hterm p]
    by_cases hab : a = b
    · rw [if_pos hab]
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_offDiag] at hp
      have h1 : ¬(p.1 = a ∧ p.2 = b) := by
        intro ⟨h1', h2'⟩
        exact hp.2.2 (h1'.trans (hab.trans h2'.symm))
      have h2 : ¬(p.2 = a ∧ p.1 = b) := by
        intro ⟨h1', h2'⟩
        exact hp.2.2 (h2'.trans (hab.symm.trans h1'.symm))
      rw [if_neg h1, if_neg h2, add_zero]
    · rw [if_neg hab]
      have hmemab : (a, b) ∈ Finset.univ.offDiag := by
        rw [Finset.mem_offDiag]
        exact ⟨Finset.mem_univ a, Finset.mem_univ b, hab⟩
      have hmemba : (b, a) ∈ Finset.univ.offDiag := by
        rw [Finset.mem_offDiag]
        exact ⟨Finset.mem_univ b, Finset.mem_univ a, Ne.symm hab⟩
      have hne : ((a, b) : n × n) ≠ (b, a) := by
        intro h
        exact hab (congrArg Prod.fst h)
      rw [sum_eq_two_of_supportG hmemab hmemba hne ?_]
      · -- the two surviving terms
        have e1 : (if ((a, b) : n × n).1 = a ∧ ((a, b) : n × n).2 = b
              then x.mat (a, b).1 (a, b).2 else 0)
            + (if ((a, b) : n × n).2 = a ∧ ((a, b) : n × n).1 = b
              then star (x.mat (a, b).1 (a, b).2) else 0)
            = x.mat a b := by
          have hno : ¬(((a, b) : n × n).2 = a ∧ ((a, b) : n × n).1 = b) := by
            intro ⟨h1', _⟩
            exact hab h1'.symm
          rw [if_pos ⟨rfl, rfl⟩, if_neg hno, add_zero]
        have hherm : star (x.mat b a) = x.mat a b := by
          have hH := congrArg (fun M : Matrix n n 𝕜 => M a b) x.H
          simpa only [Matrix.conjTranspose_apply] using hH
        have e2 : (if ((b, a) : n × n).1 = a ∧ ((b, a) : n × n).2 = b
              then x.mat (b, a).1 (b, a).2 else 0)
            + (if ((b, a) : n × n).2 = a ∧ ((b, a) : n × n).1 = b
              then star (x.mat (b, a).1 (b, a).2) else 0)
            = x.mat a b := by
          have hno : ¬(((b, a) : n × n).1 = a ∧ ((b, a) : n × n).2 = b) := by
            intro ⟨h1', _⟩
            exact hab h1'.symm
          rw [if_neg hno, if_pos ⟨rfl, rfl⟩, zero_add]
          exact hherm
        rw [e1, e2]
        ring
      · intro p hp hpab hpba
        have h1 : ¬(p.1 = a ∧ p.2 = b) := by
          intro ⟨h1', h2'⟩
          exact hpab (Prod.ext h1' h2')
        have h2 : ¬(p.2 = a ∧ p.1 = b) := by
          intro ⟨h1', h2'⟩
          exact hpba (Prod.ext h2' h1')
        rw [if_neg h1, if_neg h2, add_zero]
  rw [hframe, hblock]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, smul_zero, add_zero]
  · rw [if_neg hab, if_neg hab, zero_add]
    rw [RCLike.real_smul_eq_coe_mul]
    push_cast
    ring

/-! ## The agreement principle -/

/-- **Agreement on the frame and the blocks is agreement everywhere.**  Two
`ℝ`-linear maps out of `H_n(𝕜)` that agree on every frame projection and on every
block are equal.  This is the tool the `Ad_{a^{it}}` identification needs. -/
theorem linearMap_eq_of_frame_blockG {W : Type*} [AddCommGroup W] [Module ℝ W]
    (S T : HermitianMat n 𝕜 →ₗ[ℝ] W)
    (hframe : ∀ i : n, S (frameProjG 𝕜 i) = T (frameProjG 𝕜 i))
    (hblock : ∀ (i j : n), i ≠ j → ∀ z : 𝕜,
      S (blockHermG i j z) = T (blockHermG i j z)) :
    S = T := by
  apply LinearMap.ext
  intro x
  have hA : S (∑ i, (RCLike.re (x.mat i i) : ℝ) • frameProjG 𝕜 i)
      = T (∑ i, (RCLike.re (x.mat i i) : ℝ) • frameProjG 𝕜 i) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hframe i]
  have hB : S (∑ p ∈ Finset.univ.offDiag, blockHermG p.1 p.2 (x.mat p.1 p.2))
      = T (∑ p ∈ Finset.univ.offDiag, blockHermG p.1 p.2 (x.mat p.1 p.2)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_offDiag] at hp
    exact hblock p.1 p.2 hp.2.2 (x.mat p.1 p.2)
  rw [eq_frame_add_blocksG x, map_add, map_add, map_smul, map_smul, hA, hB]

end Necessity
