/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit
import Mathlib.LinearAlgebra.Lagrange

set_option linter.style.longLine false

/-!
# Spectral resolutions and the functional calculus  (campaign LEDGER 1.3 infrastructure)

Two layers.

1. **Value-indexed spectral projections.**  `specProj a μ := a.cfc 1_{x = μ}` and
   `eigFinset a` (the eigenvalues of `a` as a `Finset ℝ`).  The vendored matrix
   functional calculus carries no continuity hypothesis, so indicator functions are
   legitimate arguments.  `mat_cfc_eq_sum_specProj` expands *every* `a.cfc f` over
   this family; the projection algebra (`specProj_mul_self`, `specProj_mul_orth`,
   `sum_specProj_mat`, `sum_smul_specProj_mat`) makes it a resolution of the identity.

2. **The resolution lemma** (`mat_cfc_of_resolution`).  If `M.mat = ∑ i, c i • R i`
   for ANY finite family of pairwise-orthogonal idempotents summing to `1` — not
   necessarily `M`'s own eigenprojections — then `(M.cfc f).mat = ∑ i, f (c i) • R i`.
   Proof: Lagrange-interpolate `f` at the nodes `{c i} ∪ σ(M)`; on those nodes `f`
   agrees with a polynomial, `cfc` of a polynomial is the matrix polynomial
   (`polyeval_of_resolution`), and matrix polynomials act on a resolution
   coefficientwise (`pow_of_resolution` — pure ring algebra).

Layer 2 is the two-variable engine behind `twistFactor_mul_of_commute` (the S5
verification in `Hermitian/Sequential.lean`): the joint family `P_μ · Q_ν` of two
commuting effects is a resolution for their product, which certifies
`(ab)^{1/2+it} = a^{1/2+it} · b^{1/2+it}` with no simultaneous-diagonalization
machinery at all.
-/

noncomputable section

open ComplexOrder
-- NB: opened before `namespace HermitianMat` — see LEDGER H6.
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Value-indexed spectral projections -/

/-- The spectral projection of `a` at the value `μ`, as `cfc` of the indicator
function of `{μ}`.  For `μ` outside the spectrum this is `0`. -/
def specProj (a : HermitianMat n ℂ) (μ : ℝ) : HermitianMat n ℂ :=
  a.cfc fun x => if x = μ then 1 else 0

/-- The eigenvalues of `a` as a finite set of reals. -/
def eigFinset (a : HermitianMat n ℂ) : Finset ℝ :=
  Finset.univ.image a.H.eigenvalues

theorem spectrum_subset_eigFinset (a : HermitianMat n ℂ) :
    spectrum ℝ a.mat ⊆ ↑a.eigFinset := by
  rw [a.H.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem eigFinset_nonneg {a : HermitianMat n ℂ} (ha : 0 ≤ a) :
    ∀ μ ∈ a.eigFinset, 0 ≤ μ := by
  intro μ hμ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hμ
  exact eigenvalues_nonneg ha i

theorem specProj_mul_self (a : HermitianMat n ℂ) (μ : ℝ) :
    (a.specProj μ).mat * (a.specProj μ).mat = (a.specProj μ).mat := by
  have h : (fun x : ℝ => (if x = μ then (1 : ℝ) else 0) * (if x = μ then 1 else 0))
      = fun x : ℝ => if x = μ then (1 : ℝ) else 0 := by
    funext x; by_cases hx : x = μ <;> simp [hx]
  calc (a.specProj μ).mat * (a.specProj μ).mat
      = (a.cfc fun x => (if x = μ then (1 : ℝ) else 0) * (if x = μ then 1 else 0)).mat :=
        (mat_cfc_mul_apply a _ _).symm
    _ = (a.specProj μ).mat := by rw [h]; rfl

theorem specProj_mul_orth (a : HermitianMat n ℂ) {μ ν : ℝ} (h : μ ≠ ν) :
    (a.specProj μ).mat * (a.specProj ν).mat = 0 := by
  have hfun : (fun x : ℝ => (if x = μ then (1 : ℝ) else 0) * (if x = ν then 1 else 0))
      = fun _ : ℝ => (0 : ℝ) := by
    funext x
    by_cases hxμ : x = μ
    · subst hxμ
      simp [h]
    · simp [hxμ]
  calc (a.specProj μ).mat * (a.specProj ν).mat
      = (a.cfc fun x => (if x = μ then (1 : ℝ) else 0) * (if x = ν then 1 else 0)).mat :=
        (mat_cfc_mul_apply a _ _).symm
    _ = 0 := by rw [hfun, cfc_const]; simp

/-- `cfc` distributes over finite sums in the function argument. -/
theorem cfc_finsetSum {ι : Type*} (s : Finset ι) (a : HermitianMat n ℂ) (F : ι → ℝ → ℝ) :
    a.cfc (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, a.cfc (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rw [cfc_const]; simp
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    rw [cfc_add_apply, ih]

/-- **Every `cfc` expands over the value-indexed spectral projections.** -/
theorem mat_cfc_eq_sum_specProj (a : HermitianMat n ℂ) (f : ℝ → ℝ) :
    (a.cfc f).mat = ∑ μ ∈ a.eigFinset, f μ • (a.specProj μ).mat := by
  have key : a.cfc f = a.cfc (fun x => ∑ μ ∈ a.eigFinset, f μ * (if x = μ then 1 else 0)) := by
    apply cfc_congr
    intro x hx
    have hmem : x ∈ a.eigFinset := spectrum_subset_eigFinset a hx
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq a.eigFinset x f, if_pos hmem]
  rw [key, cfc_finsetSum]
  have hterm : ∀ μ ∈ a.eigFinset,
      a.cfc (fun x => f μ * (if x = μ then 1 else 0)) = f μ • a.specProj μ :=
    fun μ _ => cfc_const_mul a _ _
  rw [Finset.sum_congr rfl hterm]
  rw [show ((∑ μ ∈ a.eigFinset, f μ • a.specProj μ).mat)
      = ∑ μ ∈ a.eigFinset, (f μ • a.specProj μ).mat from map_sum
        (AddSubmonoidClass.subtype _) _ _]
  exact Finset.sum_congr rfl fun μ _ => rfl

/-- The spectral projections sum to the identity. -/
theorem sum_specProj_mat (a : HermitianMat n ℂ) :
    ∑ μ ∈ a.eigFinset, (a.specProj μ).mat = 1 := by
  have h := mat_cfc_eq_sum_specProj a (fun _ => 1)
  simp only [one_smul] at h
  rw [← h, cfc_const]
  simp

/-- The spectral resolution of `a` itself. -/
theorem sum_smul_specProj_mat (a : HermitianMat n ℂ) :
    ∑ μ ∈ a.eigFinset, μ • (a.specProj μ).mat = a.mat := by
  have h := mat_cfc_eq_sum_specProj a id
  rw [cfc_id] at h
  exact h.symm

/-! ## The resolution lemma -/

section resolution

variable {ι : Type*} {R : ι → Matrix n n ℂ} {s : Finset ι}

omit [DecidableEq n] in
/-- Linear combinations over a pairwise-orthogonal idempotent family multiply
coefficientwise. -/
theorem resolution_mul
    (hidem : ∀ i ∈ s, R i * R i = R i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → R i * R j = 0)
    (x y : ι → ℝ) :
    (∑ i ∈ s, x i • R i) * (∑ j ∈ s, y j • R j) = ∑ i ∈ s, (x i * y i) • R i := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single_of_mem i hi]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hidem i hi]
  · intro j hj hne
    rw [Matrix.smul_mul, Matrix.mul_smul, horth i hi j hj hne.symm, smul_zero, smul_zero]

variable {M : HermitianMat n ℂ} {c : ι → ℝ}

/-- Powers of a matrix presented by a resolution. -/
theorem pow_of_resolution
    (hidem : ∀ i ∈ s, R i * R i = R i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → R i * R j = 0)
    (hsum : ∑ i ∈ s, R i = 1)
    (hM : M.mat = ∑ i ∈ s, c i • R i) (k : ℕ) :
    M.mat ^ k = ∑ i ∈ s, (c i ^ k) • R i := by
  induction k with
  -- `_root_`: the vendor declares `HermitianMat.pow_zero`, which shadows the root
  -- lemma inside this namespace (LEDGER H6 family).
  | zero => simp only [_root_.pow_zero, one_smul]; exact hsum.symm
  | succ k ih =>
    rw [pow_succ, ih, hM, resolution_mul hidem horth]
    exact Finset.sum_congr rfl fun i _ => by rw [← pow_succ]

/-- Real polynomials of a matrix presented by a resolution, through the
functional calculus. -/
theorem polyeval_of_resolution
    (hidem : ∀ i ∈ s, R i * R i = R i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → R i * R j = 0)
    (hsum : ∑ i ∈ s, R i = 1)
    (hM : M.mat = ∑ i ∈ s, c i • R i) (p : Polynomial ℝ) :
    (M.cfc fun x => p.eval x).mat = ∑ i ∈ s, (p.eval (c i)) • R i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [cfc_add_apply, mat_add, hp, hq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
  | monomial k r =>
    simp only [Polynomial.eval_monomial]
    rw [cfc_const_mul, cfc_pow, mat_smul, mat_pow,
      pow_of_resolution hidem horth hsum hM k, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul r _ _

/-- **The resolution lemma.**  The functional calculus respects any presentation of
`M` by a pairwise-orthogonal idempotent family summing to `1` — not just `M`'s own
eigendecomposition. -/
theorem mat_cfc_of_resolution
    (hidem : ∀ i ∈ s, R i * R i = R i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → R i * R j = 0)
    (hsum : ∑ i ∈ s, R i = 1)
    (hM : M.mat = ∑ i ∈ s, c i • R i) (f : ℝ → ℝ) :
    (M.cfc f).mat = ∑ i ∈ s, f (c i) • R i := by
  classical
  set nodes : Finset ℝ := M.eigFinset ∪ s.image c with hnodes
  set p : Polynomial ℝ := Lagrange.interpolate nodes id f with hp
  have hnode_eval : ∀ z ∈ nodes, p.eval z = f z := by
    intro z hz
    simpa using Lagrange.eval_interpolate_at_node (r := f) (Set.injOn_id _) hz
  have hcongr : M.cfc f = M.cfc (fun x => p.eval x) := by
    apply cfc_congr
    intro x hx
    exact (hnode_eval x (Finset.mem_union_left _ (spectrum_subset_eigFinset M hx))).symm
  rw [hcongr, polyeval_of_resolution hidem horth hsum hM p]
  exact Finset.sum_congr rfl fun i hi => by
    rw [hnode_eval (c i) (Finset.mem_union_right _ (Finset.mem_image_of_mem c hi))]

/-- **Matrix-argument scaling law**: `cfc` of `r • a` is `cfc` of `a` at the
rescaled function — an immediate payoff of the resolution lemma (present `r • a`
by `a`'s own spectral family with scaled coefficients).  No sign hypothesis. -/
theorem cfc_smul_arg (r : ℝ) (a : HermitianMat n ℂ) (f : ℝ → ℝ) :
    (r • a).cfc f = a.cfc (fun x => f (r * x)) := by
  classical
  ext1
  have hidem : ∀ μ ∈ a.eigFinset, (a.specProj μ).mat * (a.specProj μ).mat = (a.specProj μ).mat :=
    fun μ _ => specProj_mul_self a μ
  have horth : ∀ μ ∈ a.eigFinset, ∀ ν ∈ a.eigFinset, μ ≠ ν →
      (a.specProj μ).mat * (a.specProj ν).mat = 0 :=
    fun μ _ ν _ h => specProj_mul_orth a h
  have hM : (r • a).mat = ∑ μ ∈ a.eigFinset, (r * μ) • (a.specProj μ).mat := by
    rw [mat_smul, ← sum_smul_specProj_mat a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun μ _ => by rw [smul_smul]
  rw [mat_cfc_of_resolution hidem horth (sum_specProj_mat a) hM f,
    mat_cfc_eq_sum_specProj a]

end resolution

end HermitianMat
