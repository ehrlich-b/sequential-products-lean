/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.PhaseCocycle
import RadicalRelativity.Necessity.JordanDerivation
import RadicalRelativity.Necessity.StabilizerInstance
import RadicalRelativity.MasterTheorem.Branches.Complex

set_option linter.style.longLine false

/-!
# The phase anchor: cocycle → character matrix → per-frame collapse  (LEDGER 2.6, u6d)

The final ℂ-lane wiring of `lem:homomorphism`:

* `dChiEntry` — the block entry map `z ↦ (dχ(r)(z E_ij + z̄ E_ji))_{ij}` as an
  ℝ-linear map `ℂ → ℂ`; it is skew (`dChi_block_skew`), hence multiplication
  by `i·t_{ij}(r)` (`skew_linear_eq_I_smul`).
* `tvalLm` — the phase rate `t_{ij} : ℝⁿ →ₗ ℝ`.
* `tval_cocycle` — **the phase cocycle** `t_{ik} = t_{ij} + t_{jk}`: apply the
  Jordan-derivation Leibniz rule to cross-block elements and read the `(i,k)`
  entry through the cross-block product formula.
* `tval_antisymm` — `t_{ji} = −t_{ij}` from Hermiticity.
* `thetaAnchor`/`cMatrix` — anchoring at a reference index `i₀` collapses the
  per-pair rates to per-index characters `θ_i(r) = Σ_l c_{il} r_l`.
* `complex_perFrame_concrete` — the concrete `hmodel` for the produced
  `stabilizerCoupling`, fed to `complex_perFrame_rho`: **a single `t_F` per
  frame with `ρ_{ij}(dχ(r)) = (t_F(r_i − r_j)) • J` on `H_N(ℂ)`.**
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace MasterTheorem

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## Cross-block entry extraction -/

/-- The `(i,k)` entry of `w ∘ blockHerm j k v` for pairwise distinct `i,j,k`:
only the `E_jk` leg of the block and the `(i,j)` entry of `w` survive. -/
theorem symmMul_blockHerm_entry {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (w : HermitianMat n ℂ) (v : ℂ) :
    (w.symmMul (blockHerm j k v)).mat i k = (2 : ℂ)⁻¹ * (w.mat i j * v) := by
  rw [HermitianMat.symmMul_toMat, Matrix.smul_apply, Matrix.add_apply]
  have h1 : (w.mat * (blockHerm j k v).mat) i k = w.mat i j * v := by
    rw [blockHerm_mat, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    have e1 : (w.mat * Matrix.single j k (1 : ℂ)) i k = w.mat i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · simp [Matrix.single]
      · intro m _ hm
        simp [Matrix.single, Ne.symm hm]
      · intro h; exact absurd (Finset.mem_univ j) h
    have e2 : (w.mat * Matrix.single k j (1 : ℂ)) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      have hc : (k = m ∧ j = k) = False := eq_false (fun ⟨_, h'⟩ => hjk h')
      simp [Matrix.single, hc]
    rw [e1, e2, smul_zero, add_zero, smul_eq_mul, mul_comm]
  have h2 : ((blockHerm j k v).mat * w.mat) i k = 0 := by
    rw [blockHerm_mat, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    have e3 : (Matrix.single j k (1 : ℂ) * w.mat) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      have hc : (j = i ∧ k = m) = False := eq_false (fun ⟨h', _⟩ => hij h'.symm)
      simp [Matrix.single, hc]
    have e4 : (Matrix.single k j (1 : ℂ) * w.mat) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      have hc : (k = i ∧ j = m) = False := eq_false (fun ⟨h', _⟩ => hik h'.symm)
      simp [Matrix.single, hc]
    rw [e3, e4, smul_zero, smul_zero, add_zero]
  rw [h1, h2, add_zero, smul_eq_mul]

/-- The `(i,k)` entry of `blockHerm i j z ∘ w` for pairwise distinct `i,j,k`:
only the `E_ij` leg of the block and the `(j,k)` entry of `w` survive. -/
theorem blockHerm_symmMul_entry {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (z : ℂ) (w : HermitianMat n ℂ) :
    ((blockHerm i j z).symmMul w).mat i k = (2 : ℂ)⁻¹ * (z * w.mat j k) := by
  rw [HermitianMat.symmMul_toMat, Matrix.smul_apply, Matrix.add_apply]
  have h1 : ((blockHerm i j z).mat * w.mat) i k = z * w.mat j k := by
    rw [blockHerm_mat, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    have e1 : (Matrix.single i j (1 : ℂ) * w.mat) i k = w.mat j k := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · simp [Matrix.single]
      · intro m _ hm
        simp [Matrix.single, Ne.symm hm]
      · intro h; exact absurd (Finset.mem_univ j) h
    have e2 : (Matrix.single j i (1 : ℂ) * w.mat) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      have hc : (j = i ∧ i = m) = False := eq_false (fun ⟨h', _⟩ => hij h'.symm)
      simp [Matrix.single, hc]
    rw [e1, e2, smul_zero, add_zero, smul_eq_mul]
  have h2 : (w.mat * (blockHerm i j z).mat) i k = 0 := by
    rw [blockHerm_mat, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    have e3 : (w.mat * Matrix.single i j (1 : ℂ)) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      have hc : (i = m ∧ j = k) = False := eq_false (fun ⟨_, h'⟩ => hjk h')
      simp [Matrix.single, hc]
    have e4 : (w.mat * Matrix.single j i (1 : ℂ)) i k = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro m _
      have hc : (j = m ∧ i = k) = False := eq_false (fun ⟨_, h'⟩ => hik h')
      simp [Matrix.single, hc]
    rw [e3, e4, smul_zero, smul_zero, add_zero]
  rw [h1, h2, add_zero, smul_eq_mul]

/-! ## The block parametrization as a linear map -/

/-- `z ↦ blockHerm i j z` is ℝ-linear. -/
def blockHermLm (i j : n) : ℂ →ₗ[ℝ] HermitianMat n ℂ where
  toFun z := blockHerm i j z
  map_add' z w := by
    ext1
    simp only [blockHerm_mat, HermitianMat.mat_add, star_add, add_smul]
    abel
  map_smul' c z := by
    ext1
    simp only [blockHerm_mat, HermitianMat.mat_smul, RingHom.id_apply,
      star_smul, star_trivial, smul_add, smul_assoc]

@[simp]
theorem blockHermLm_apply (i j : n) (z : ℂ) :
    blockHermLm i j z = blockHerm i j z := rfl

/-! ## The entry map of the differential and its classification -/

/-- The block entry map of `dχ(r)`: `z ↦ (dχ(r)(blockHerm i j z))_{ij}`. -/
def dChiEntry (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) (i j : n) : ℂ →ₗ[ℝ] ℂ :=
  entryLm i j
    ∘ₗ ((dChi P hS2 hjord r : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    ∘ₗ blockHermLm i j)

@[simp]
theorem dChiEntry_apply (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) (i j : n) (z : ℂ) :
    dChiEntry P hS2 hjord r i j z
      = (dChi P hS2 hjord r (blockHerm i j z)).mat i j := rfl

/-- The phase rate `t_{ij}` as a linear functional of `r`. -/
def tvalLm (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i j : n) : (n → ℝ) →ₗ[ℝ] ℝ where
  toFun r := (dChiEntry P hS2 hjord r i j 1).im
  map_add' r r' := by
    simp only [dChiEntry_apply]
    rw [map_add (dChi P hS2 hjord), ContinuousLinearMap.add_apply]
    exact Complex.add_im _ _
  map_smul' c r := by
    simp only [dChiEntry_apply, RingHom.id_apply]
    rw [map_smul (dChi P hS2 hjord), ContinuousLinearMap.smul_apply]
    exact Complex.smul_im _ _

@[simp]
theorem tvalLm_apply (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i j : n) (r : n → ℝ) :
    tvalLm P hS2 hjord i j r
      = ((dChi P hS2 hjord r (blockHerm i j 1)).mat i j).im := rfl

/-- **The skew classification applied to `dχ`**: the block entry map is
multiplication by `i·t_{ij}(r)`. -/
theorem dChiEntry_eq (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    dChiEntry P hS2 hjord r i j z
      = (tvalLm P hS2 hjord i j r) • (Complex.I * z) := by
  have hskew : ∀ w : ℂ, w.re * ((dChiEntry P hS2 hjord r i j) w).re
      + w.im * ((dChiEntry P hS2 hjord r i j) w).im = 0 := by
    intro w
    have h := dChi_block_skew P hS2 hjord r hij w.re w.im
    rw [show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w from Complex.re_add_im w] at h
    exact h
  have h := skew_linear_eq_I_smul (dChiEntry P hS2 hjord r i j) hskew z
  rw [h]
  rfl

/-! ## The hyperplane factorization (`lem:homomorphism`, final clause)

The article's `lem:homomorphism` asserts `ρ_ij(dχ(r)) = (r_i − r_j) T_ij` for a
*single* `T_ij ∈ 𝔰𝔬(V_ij)`.  Everything upstream of this identity is already in
the tree: `chiTilde` is the article's own canonical-representative extension of
`Θ` from the negative orthant to all of `ℝⁿ` (`chiTilde_of_nonpos`,
`chiTilde_add`), `chiTilde_eq_exp` *proves* — via `multiParameter_eq_exp`, from
the homomorphism law plus line continuity, with no Lie-theoretic import — that
it is `exp ∘ dχ` for a unique real-linear `dχ`, and `dChi_mem_blockSkew` puts
`dχ(r)` in the block-skew algebra, which is what makes `T_ij` skew.

What was missing is only the factorization itself.  The article gets it by
showing that differences of coalesced orthant vectors span the hyperplane
`{r_i = r_j}`; the tree gets the vanishing directly from the differentiated
coalescence (`dChi_kills_corner`, `rhoField_dChi_coalesced`) and then factors a
linear functional that kills a hyperplane, which is exact and needs no
`2π` bookkeeping.  Rank-free, so it also covers the rank-two lane. -/

/-- A block element lies in the Peirce 2-space of `q = p_i + p_j`. -/
theorem blockHerm_cornerJ2 {i j : n} (z : ℂ) : cornerJ2 i j (blockHerm i j z) := by
  apply blockElt_cornerJ2
  intro k hki hkj
  rw [jordanBilin_apply]
  exact frameProj_symmMul_blockHerm_other hki hkj _

/-- **The phase rate kills the coalesced diagonal**, at every rank. -/
theorem tvalLm_of_diag_eq (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i j : n) {r : n → ℝ} (h : r i = r j) :
    tvalLm P hS2 hjord i j r = 0 := by
  rw [tvalLm_apply, dChi_kills_corner P hS2 hjord h (blockHerm_cornerJ2 (1 : ℂ))]
  simp

/-- The single generator's coefficient, independent of `r`. -/
noncomputable def tvalCoef (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (i j : n) : ℝ :=
  tvalLm P hS2 hjord i j (fun k => if k = i then 1 else 0)

/-- **The hyperplane factorization in coordinates**: the phase rate is
`(r_i − r_j)` times a single constant. -/
theorem tvalLm_eq_coef_mul (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) :
    tvalLm P hS2 hjord i j r = (r i - r j) * tvalCoef P hS2 hjord i j := by
  set e : n → ℝ := fun k => if k = i then (1 : ℝ) else 0 with he
  set c : ℝ := r i - r j with hc
  have hei : e i = 1 := by simp [he]
  have hej : e j = 0 := by simp [he, hij.symm]
  have hsij : (r - c • e) i = (r - c • e) j := by
    show r i - c * e i = r j - c * e j
    rw [hei, hej, hc]; ring
  have hsplit : r = c • e + (r - c • e) := by abel
  rw [hsplit, map_add, tvalLm_of_diag_eq P hS2 hjord i j hsij, add_zero,
    map_smul, smul_eq_mul]
  rfl

/-- The block entry map of `dχ(r)` is `(r_i − r_j)` times the single generator
`z ↦ i·z` scaled by `tvalCoef`. -/
theorem dChiEntry_eq_mul_generator (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) (z : ℂ) :
    dChiEntry P hS2 hjord r i j z
      = ((r i - r j) * tvalCoef P hS2 hjord i j) • (Complex.I * z) := by
  rw [dChiEntry_eq P hS2 hjord r hij z, tvalLm_eq_coef_mul P hS2 hjord hij r]

/-- The article's `ρ_ij(dχ(·))`, as a linear map of `r`. -/
noncomputable def rhoChi (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (i j : n) :
    (n → ℝ) →ₗ[ℝ] ((ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) where
  toFun r := rhoField i j (dChiStab P hS2 hjord r)
  map_add' r r' := by
    rw [map_add (dChiStab P hS2 hjord), map_add]
  map_smul' c r := by
    have h : dChiStab P hS2 hjord (c • r) = c • dChiStab P hS2 hjord r :=
      Subtype.ext (by
        show dChi P hS2 hjord (c • r) = c • dChi P hS2 hjord r
        exact map_smul _ _ _)
    rw [h, map_smul]
    rfl

/-- **`lem:homomorphism`, the article's block-representation identity, at every
rank**: `ρ_ij(dχ(r)) = (r_i − r_j) • T_ij` for the single generator
`T_ij = ρ_ij(dχ(e_i))`, which lies in `𝔰𝔬(V_ij)` because `dχ` lands in
`blockSkewSubmodule` by construction (`dChi_mem_blockSkew`). -/
theorem rhoChi_eq_smul_generator (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) :
    rhoChi P hS2 hjord i j r
      = (r i - r j) • rhoChi P hS2 hjord i j (fun k => if k = i then 1 else 0) := by
  set e : n → ℝ := fun k => if k = i then (1 : ℝ) else 0 with he
  set c : ℝ := r i - r j with hc
  have hei : e i = 1 := by simp [he]
  have hej : e j = 0 := by simp [he, hij.symm]
  have hsij : (r - c • e) i = (r - c • e) j := by
    show r i - c * e i = r j - c * e j
    rw [hei, hej, hc]; ring
  have hvanish : rhoChi P hS2 hjord i j (r - c • e) = 0 :=
    rhoField_dChi_coalesced P hS2 hjord i j (r - c • e) hsij
  have hsplit : r = c • e + (r - c • e) := by abel
  rw [hsplit, map_add, hvanish, add_zero, map_smul]

/-- **The same identity, unconditionally.**

Self-audit finding (2026-08-08): the `i ≠ j` hypothesis of `rhoChi_eq_smul_generator` is
**inert** — `rhoField` is defined to be `0` on the diagonal, so at `i = j` both sides are `0`
and the identity holds for free. Recorded and the stronger version stated, rather than leaving
a hypothesis that looks like it is doing work; this is the defect the arc-5 cold review found
in `lem:adjacent`, applied here to my own diff before a reviewer had to.

The article states its version for `i ≠ j` (there is no `V_ii`), so the hypothesised form
remains the one that matches the paper; this is a bonus, not a fidelity change. -/
theorem rhoChi_eq_smul_generator_all (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (i j : n) (r : n → ℝ) :
    rhoChi P hS2 hjord i j r
      = (r i - r j) • rhoChi P hS2 hjord i j (fun k => if k = i then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    have h0 : ∀ s : n → ℝ, rhoChi P hS2 hjord i i s = 0 := by
      intro s
      show rhoField i i (dChiStab P hS2 hjord s) = 0
      rw [rhoField_diag]
      rfl
    rw [h0, h0, sub_self, zero_smul]
  · exact rhoChi_eq_smul_generator P hS2 hjord hij r

/-! ## The phase cocycle -/

/-- **The phase cocycle** `t_{ik}(r) = t_{ij}(r) + t_{jk}(r)`: the Leibniz rule
for `dχ(r)` applied to cross-block elements, read at the `(i,k)` entry. -/
theorem tval_cocycle (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    tvalLm P hS2 hjord i k r
      = tvalLm P hS2 hjord i j r + tvalLm P hS2 hjord j k r := by
  have hL := dChi_jordan_derivation P hS2 hjord r (blockHerm i j 1) (blockHerm j k 1)
  rw [blockHerm_symmMul_blockHerm hij hjk hik 1 1, mul_one, map_smul] at hL
  have h2 := congrArg (fun X : HermitianMat n ℂ => (X.mat i k).im) hL
  simp only [HermitianMat.mat_smul, Matrix.smul_apply, HermitianMat.mat_add,
    Matrix.add_apply] at h2
  rw [symmMul_blockHerm_entry hij hjk hik _ 1,
    blockHerm_symmMul_entry hij hjk hik 1 _] at h2
  rw [mul_one, one_mul] at h2
  have hhalf : ∀ w : ℂ, ((2 : ℂ)⁻¹ * w).im = 2⁻¹ * w.im := by
    intro w
    rw [Complex.mul_im]
    norm_num
  rw [Complex.add_im, hhalf, hhalf, Complex.smul_im] at h2
  simp only [tvalLm_apply]
  simp only [smul_eq_mul] at h2
  linarith

/-- **Antisymmetry** `t_{ji}(r) = −t_{ij}(r)`: `blockHerm j i 1 = blockHerm i j 1`
and Hermiticity of the image flips the imaginary part across the diagonal. -/
theorem tval_antisymm (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (r : n → ℝ) (i j : n) :
    tvalLm P hS2 hjord j i r = -(tvalLm P hS2 hjord i j r) := by
  have hb : blockHerm j i (1 : ℂ) = blockHerm i j 1 := by
    ext1
    rw [blockHerm_mat, blockHerm_mat, star_one]
    exact add_comm _ _
  have hherm : ∀ W : HermitianMat n ℂ, W.mat j i = star (W.mat i j) := by
    intro W
    have h := congrArg (fun M => M j i) W.H
    simpa [Matrix.conjTranspose_apply] using h.symm
  simp only [tvalLm_apply]
  rw [hb, hherm]
  simp

/-! ## The anchored characters and the character matrix -/

/-- The anchored character `θ_i(r)`: zero at the anchor `i₀`, else `t_{i,i₀}(r)`. -/
def thetaAnchor (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i₀ : n) (r : n → ℝ) (i : n) : ℝ :=
  if i = i₀ then 0 else tvalLm P hS2 hjord i i₀ r

/-- **The per-pair rate is an anchored character difference**: the cocycle
through the anchor plus antisymmetry. -/
theorem tval_eq_theta_sub (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i₀ : n) {i j : n} (hij : i ≠ j) (r : n → ℝ) :
    tvalLm P hS2 hjord i j r
      = thetaAnchor P hS2 hjord i₀ r i - thetaAnchor P hS2 hjord i₀ r j := by
  unfold thetaAnchor
  by_cases hi : i = i₀
  · subst hi
    rw [if_pos rfl, if_neg (Ne.symm hij), tval_antisymm P hS2 hjord r j i]
    ring
  · rw [if_neg hi]
    by_cases hj : j = i₀
    · subst hj
      rw [if_pos rfl, sub_zero]
    · rw [if_neg hj, tval_cocycle P hS2 hjord r hi (Ne.symm hj) hij,
        tval_antisymm P hS2 hjord r j i₀]
      ring

/-- The character matrix `c_{il} = θ_i(e_l)`. -/
def cMatrix (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i₀ : n) (i l : n) : ℝ :=
  thetaAnchor P hS2 hjord i₀ (Pi.single l 1) i

/-- **The characters are linear**: `θ_i(r) = Σ_l c_{il} r_l`. -/
theorem thetaAnchor_expand (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i₀ : n) (i : n) (r : n → ℝ) :
    thetaAnchor P hS2 hjord i₀ r i = ∑ l, cMatrix P hS2 hjord i₀ i l * r l := by
  unfold cMatrix thetaAnchor
  by_cases hi : i = i₀
  · simp [hi]
  · simp only [if_neg hi]
    have hr : r = ∑ l, Pi.single l (r l) := (Finset.univ_sum_single r).symm
    conv_lhs => rw [hr]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro l _
    have hs : Pi.single l (r l) = (r l) • (Pi.single l (1 : ℝ) : n → ℝ) := by
      funext m
      by_cases hm : m = l
      · subst hm; simp
      · simp [Pi.single_eq_of_ne hm]
    rw [hs, map_smul, smul_eq_mul, mul_comm]

/-! ## The rotation generator on the L² block -/

/-- The rotation generator `J(v₁,v₂) = (−v₂, v₁)` on the L² block — the
complex-structure generator of `V_{ij} ≅ ℂ`. -/
def rotJ : BlockV →ₗ[ℝ] BlockV :=
  (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm.toLinearMap
    ∘ₗ (LinearMap.prod (-(LinearMap.snd ℝ ℝ ℝ)) (LinearMap.fst ℝ ℝ ℝ))
    ∘ₗ (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).toLinearMap

theorem rotJ_apply (x : BlockV) :
    rotJ x = (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm
      (-(WithLp.linearEquiv 2 ℝ (ℝ × ℝ) x).2,
        (WithLp.linearEquiv 2 ℝ (ℝ × ℝ) x).1) := rfl

theorem rotJ_ne_zero : rotJ ≠ 0 := by
  intro h
  have h2 := LinearMap.congr_fun h
    ((WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm ((0 : ℝ), (1 : ℝ)))
  rw [rotJ_apply] at h2
  simp only [LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at h2
  have h3 := congrArg (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)) h2
  simp only [LinearEquiv.apply_symm_apply, map_zero] at h3
  have h4 := congrArg Prod.fst h3
  norm_num at h4

/-! ## The concrete per-frame collapse on `H_N(ℂ)` -/

/-- The produced coupling's data unfolds to the concrete compression of `dχ`. -/
theorem stabilizerCoupling_rho_dChi {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    (i j : Fin N) (r : Fin N → ℝ) :
    (stabilizerCoupling hN P hS2 hjord).ρ i j ((stabilizerCoupling hN P hS2 hjord).dχ r)
      = rhoFieldL2 i j (dChiStab P hS2 hjord r) := by
  show rhoFieldL2 i j ((diagonalHomSetup hN P hS2 hjord).dChiLinear r)
    = rhoFieldL2 i j (dChiStab P hS2 hjord r)
  rw [DiagonalHomSetup.dChiLinear_apply]
  rfl

/-- **`thm:complex`, per frame, on `H_N(ℂ)` — PRODUCED.**  For any S1–S7
sequential product on `H_N(ℂ)` (`N ≥ 3`) with S2 and the M3 Jordan property,
the produced stabilizer coupling carries a **single per-frame parameter**:
`ρ_{ij}(dχ(r)) = (t_F(r_i − r_j)) • J` on every block, with `J` the rotation
generator. -/
theorem complex_perFrame_concrete {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    ∃ tF : ℝ, ∀ (i j : Fin N) (r : Fin N → ℝ),
      (stabilizerCoupling hN P hS2 hjord).ρ i j
          ((stabilizerCoupling hN P hS2 hjord).dχ r)
        = (tF * (r i - r j)) • rotJ := by
  have h0 : (0 : ℕ) < N := by omega
  set i₀ : Fin N := ⟨0, h0⟩ with hi₀
  apply complex_perFrame_rho (stabilizerCoupling hN P hS2 hjord) rotJ rotJ_ne_zero
    (cMatrix P hS2 hjord i₀)
  intro i j r
  rw [stabilizerCoupling_rho_dChi hN P hS2 hjord i j r,
    ← thetaAnchor_expand P hS2 hjord i₀ i r, ← thetaAnchor_expand P hS2 hjord i₀ j r]
  by_cases hij : i = j
  · subst hij
    rw [sub_self, zero_smul]
    apply LinearMap.ext
    intro v
    rw [rhoFieldL2_apply, rhoField_diag]
    simp
  · rw [← tval_eq_theta_sub P hS2 hjord i₀ hij r]
    apply LinearMap.ext
    intro v
    rw [rhoFieldL2_apply, rhoField_apply_of_ne hij]
    rw [show (dChiStab P hS2 hjord r).val = dChi P hS2 hjord r from rfl]
    set u := WithLp.linearEquiv 2 ℝ (ℝ × ℝ) v with hu
    have hentry : (dChi P hS2 hjord r
          (blockHerm i j ((u.1 : ℂ) + u.2 * Complex.I))).mat i j
        = (tvalLm P hS2 hjord i j r)
            • (Complex.I * ((u.1 : ℂ) + u.2 * Complex.I)) := by
      have h := dChiEntry_eq P hS2 hjord r hij ((u.1 : ℂ) + u.2 * Complex.I)
      rwa [dChiEntry_apply] at h
    rw [blockEmbedLm_apply, blockCoordLm_apply, hentry]
    rw [LinearMap.smul_apply, rotJ_apply]
    have hsm : ∀ (t : ℝ) (w : ℝ × ℝ),
        (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm (t • w)
          = t • (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm w :=
      fun t w => map_smul _ t w
    rw [← hsm]
    congr 1
    rw [Prod.smul_mk]
    refine Prod.ext ?_ ?_ <;>
      simp [hu, Complex.mul_re, Complex.mul_im, smul_eq_mul]

end Necessity
