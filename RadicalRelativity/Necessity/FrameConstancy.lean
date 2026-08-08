/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComplexResidue

set_option linter.style.longLine false

/-!
# Cross-frame coherence: the per-frame twist agrees across adjacent frames

`ComplexResidue` reduced the complex row to one statement, `FrameTwistConst`.  This file
proves half of it: **`frameTwist` takes the same value at any two frames that share a
coordinate axis.**

The mechanism is a base point that lies in *both* frames.  If `F⁻¹G` fixes the axis `m`,
then `F` and `G` diagonalize the same one-parameter family
`a_x = Ad_F (diagFamily (x • s))`, `s = −1` at `m` and `0` elsewhere: the family commutes
with `F⁻¹G` because its spectrum is constant on each of the two blocks the adjacency
provides.  The per-frame theorem then computes `P.sp a_x b` twice, once with `frameTwist F`
and once with `frameTwist G`, so the two twist products agree at `a_x` for every effect `b`.
Reading the `(m, m')` entry against the pair projection turns that into agreement of the
characters `x ↦ e^{i t x}` on an interval, and `real_character_unique` finishes with no
`2π` ambiguity.

Why the family and not a single base point: **one phase equation cannot pin `t`.** The probe
used here reads a single entry, giving `e^{i t₁ Δ} = e^{i t₂ Δ}` with `Δ` the spectral gap,
which determines `t₁ − t₂` only modulo `2π/Δ`; running `x` over an interval removes the
ambiguity.  This is a statement about *this* probe, not a mathematical necessity — for
`N ≥ 3` a single base point with incommensurable gaps, read at two index pairs, would also
force exactness.  The scaled family is chosen because it is cheap and because the two-level
spectrum is exactly what an axis adjacency preserves.

* `sp_eq_twistSeq_frame` — **the workhorse.**  At any frame `U` and any nonpositive
  diagonal family, the product is the twist with parameter `frameTwist U`.  This is
  `ComplexMaster`'s chain with the frame left free instead of specialized to
  `a.H.eigenvectorUnitary`.
* `twistSeq_eq_of_adU` — conjugation cancels: agreement at `Ad_U a` is agreement at `a`.
* `twist_param_unique_of_scaled` — uniqueness against a *given* scaled family.
* `AdjAxis`, `frameTwist_eq_of_adjAxis` — the adjacency and the coherence theorem.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace MasterTheorem

namespace Necessity

variable {N : ℕ}

/-! ## The workhorse: the twist form at an arbitrary frame -/

/-- **The per-frame twist form, with the frame free.**

For any unitary `U` and any nonpositive `r`, the product at the base point
`a = Ad_U (diagFamily r)` is the twist product with parameter `frameTwist U`.

`ComplexMaster.sp_eq_twistSeq_of_frameGraph` is the special case `U = a.H.eigenvectorUnitary`
followed by the global collapse; the point of stating it this way is that `U` is now a
*parameter*, so two different frames diagonalizing the same base point can be compared. -/
theorem sp_eq_twistSeq_frame (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    {r : Fin N → ℝ} (hr : ∀ i, r i ≤ 0)
    {a : HermitianMat (Fin N) ℂ}
    (hadiag : a = adU (U : Matrix (Fin N) (Fin N) ℂ) (diagFamily r))
    {b : HermitianMat (Fin N) ℂ} (hb : IsEffect b) :
    P.sp a b = HermitianMat.twistSeq (frameTwist hN P hS2 U) a b := by
  have hU := unitaryGroup_conjTranspose_mul U
  have hU' := unitaryGroup_mul_conjTranspose U
  have hQS2 : (conjProduct P hU hU').FirstArgContinuous :=
    conjProduct_firstArgContinuous P hU hU' hS2
  have hcollapse : ∀ i j : Fin N, i ≠ j →
      tvalLm (conjProduct P hU hU') hQS2
          (thetaPreservesJordan_of_S2 _ hQS2) i j r
        = frameTwist hN P hS2 U * (r i - r j) := fun i j hij =>
    tvalLm_of_coupling hN (conjProduct P hU hU') hQS2
      (thetaPreservesJordan_of_S2 _ hQS2) (frameTwist hN P hS2 U)
      (frameTwist_spec hN P hS2 U) hij r
  exact sp_eq_twistSeq_transport P hU hU' hadiag (frameTwist hN P hS2 U)
    (fun b' hb' => sp_eq_twistSeq_diagFamily (conjProduct P hU hU') hQS2
      (thetaPreservesJordan_of_S2 _ hQS2) (frameTwist hN P hS2 U) hr hcollapse hb') hb

/-! ## Conjugation cancels

The workhorse compares two frames at the base point `Ad_F (diagFamily r)`, but the
uniqueness machinery reads entries of `diagFamily r` itself.  The twist product is
unitarily covariant, so the conjugation can be stripped.
-/

/-- **Unitary covariance of the twist product**: `Ad_U` intertwines `twistSeq t`. -/
theorem twistSeq_adU_mat (t : ℝ) {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1)
    (hU' : U * Uᴴ = 1) (a b : HermitianMat (Fin N) ℂ) :
    HermitianMat.twistSeq t (adU U a) (adU U b) = adU U (HermitianMat.twistSeq t a b) := by
  rw [HermitianMat.twistSeq, HermitianMat.twistSeq, twistFactor_adU_mat a hU' t]
  simp only [adU_apply]
  rw [HermitianMat.conj_conj, HermitianMat.conj_conj]
  congr 1
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

/-- **Stripping the conjugation.**  Agreement of two twist products at `Ad_U a` on all
effects is agreement at `a` on all effects: push the probe through `Ad_U` (a bijection of
the effects) and cancel with `Ad_{U*}`. -/
theorem twistSeq_eq_of_adU {t₁ t₂ : ℝ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) {a : HermitianMat (Fin N) ℂ}
    (h : ∀ c : HermitianMat (Fin N) ℂ, IsEffect c →
      HermitianMat.twistSeq t₁ (adU U a) c = HermitianMat.twistSeq t₂ (adU U a) c)
    {b : HermitianMat (Fin N) ℂ} (hb : IsEffect b) :
    HermitianMat.twistSeq t₁ a b = HermitianMat.twistSeq t₂ a b := by
  have hc := h (adU U b) (adU_isEffect hU hU' hb)
  rw [twistSeq_adU_mat t₁ hU hU' a b, twistSeq_adU_mat t₂ hU hU' a b] at hc
  have hcc := congrArg (adU Uᴴ) hc
  rwa [adU_cancel hU, adU_cancel hU] at hcc

/-! ## The character behind a diagonal base point -/

/-- `star` of a polar factor reflects the phase. -/
theorem star_phase_factor (c α : ℝ) :
    star (((c : ℝ) : ℂ) * Complex.exp (((α : ℝ) : ℂ) * Complex.I))
      = ((c : ℝ) : ℂ) * Complex.exp ((((-α : ℝ)) : ℂ) * Complex.I) := by
  have h1 : (((-α : ℝ)) : ℂ) * Complex.I
      = (starRingEnd ℂ) (((α : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
    ring
  rw [h1, Complex.exp_conj, star_mul']
  congr 1
  exact Complex.conj_ofReal c

/-- **The character equation behind a diagonal base point.**  If the twist products with
parameters `t₁` and `t₂` agree at `diagFamily r` on the pair projection, their phases agree
at the spectral gap `r i − r j`: the `(i,j)` entry is a nonzero positive multiple of
`e^{i t (r i − r j)}`. -/
theorem exp_eq_of_twistSeq_diagFamily_eq {t₁ t₂ : ℝ} {i j : Fin N} (hij : i ≠ j)
    (r : Fin N → ℝ)
    (h : HermitianMat.twistSeq t₁ (diagFamily r) (pairProj i j)
      = HermitianMat.twistSeq t₂ (diagFamily r) (pairProj i j)) :
    Complex.exp (((t₁ * (r i - r j) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((t₂ * (r i - r j) : ℝ) : ℂ) * Complex.I) := by
  have hentry := congrArg (fun M : HermitianMat (Fin N) ℂ => M.mat i j) h
  simp only at hentry
  rw [twistSeq_diagFamily_entry, twistSeq_diagFamily_entry, pairProj_entry hij,
    star_phase_factor, star_phase_factor] at hentry
  have hs : ∀ k : Fin N, ((Real.sqrt (Real.exp (r k)) : ℝ) : ℂ) ≠ 0 := by
    intro k
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact Real.sqrt_ne_zero'.mpr (Real.exp_pos _)
  have hA : ((Real.sqrt (Real.exp (r i)) : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)
      * ((Real.sqrt (Real.exp (r j)) : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (hs i) ?_) (hs j)
    norm_num
  have hform : ∀ t : ℝ,
      (((Real.sqrt (Real.exp (r i)) : ℝ) : ℂ)
              * Complex.exp (((t * r i : ℝ) : ℂ) * Complex.I))
            * ((1 / 2 : ℝ) : ℂ)
            * (((Real.sqrt (Real.exp (r j)) : ℝ) : ℂ)
              * Complex.exp (((-(t * r j) : ℝ) : ℂ) * Complex.I))
        = (((Real.sqrt (Real.exp (r i)) : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)
            * ((Real.sqrt (Real.exp (r j)) : ℝ) : ℂ))
          * Complex.exp (((t * (r i - r j) : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [show ((t * (r i - r j) : ℝ) : ℂ) * Complex.I
        = (((t * r i : ℝ) : ℂ) * Complex.I) + (((-(t * r j) : ℝ) : ℂ) * Complex.I) by
      push_cast; ring]
    rw [Complex.exp_add]
    ring
  rw [hform t₁, hform t₂] at hentry
  exact mul_left_cancel₀ hA hentry

/-- **Uniqueness of the twist parameter against a prescribed scaled family.**

If the two twist products agree at the base points `diagFamily (x • s)` for every `x` in an
interval, and `s` separates two indices, then `t₁ = t₂`.

The *interval* is what makes this exact.  At a single base point the phases only pin
`t₁ − t₂` modulo `2π/(r i − r j)`; running the whole scaled family and appealing to
`real_character_unique` removes the ambiguity. -/
theorem twist_param_unique_of_scaled {t₁ t₂ : ℝ} {i j : Fin N} (hij : i ≠ j)
    {u v : ℝ} (huv : u < v) {s : Fin N → ℝ} (hs : s i ≠ s j)
    (h : ∀ x ∈ Set.Ioo u v, HermitianMat.twistSeq t₁ (diagFamily (x • s)) (pairProj i j)
      = HermitianMat.twistSeq t₂ (diagFamily (x • s)) (pairProj i j)) :
    t₁ = t₂ := by
  have hδ : s i - s j ≠ 0 := sub_ne_zero_of_ne hs
  refine mul_right_cancel₀ hδ ?_
  refine MasterTheorem.Globalization.real_character_unique huv ?_
  intro x hx
  have hx' := exp_eq_of_twistSeq_diagFamily_eq hij (x • s) (h x hx)
  rw [show ((t₁ * (s i - s j) : ℝ) : ℂ) * (x : ℂ) * Complex.I
      = ((t₁ * ((x • s) i - (x • s) j) : ℝ) : ℂ) * Complex.I by
        simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring,
    show ((t₂ * (s i - s j) : ℝ) : ℂ) * (x : ℂ) * Complex.I
      = ((t₂ * ((x • s) i - (x • s) j) : ℝ) : ℂ) * Complex.I by
        simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring]
  exact hx'

/-! ## Axis adjacency

Two frames are adjacent when the unitary carrying one to the other fixes a coordinate axis.
Such a pair shares a whole one-parameter family of base points: the family whose spectrum is
one value on the axis and another off it commutes with the connecting unitary, so it is
diagonal in *both* frames.
-/

/-- The two-level spectrum an axis adjacency preserves: `−1` on the axis `m`, `0` off it. -/
def axisSplit (m : Fin N) : Fin N → ℝ := fun k => if k = m then -1 else 0

/-- **Axis adjacency.**  `F` and `G` are adjacent when `F⁻¹G = F* G` fixes some coordinate
axis `m`, i.e. its row `m` and column `m` vanish off the diagonal.  Equivalently the two
frames share their `m`-th vector up to phase. -/
def AdjAxis (F G : Matrix.unitaryGroup (Fin N) ℂ) : Prop :=
  ∃ m : Fin N, ∀ i j : Fin N, i ≠ j → (i = m ∨ j = m) →
    ((F : Matrix (Fin N) (Fin N) ℂ)ᴴ * (G : Matrix (Fin N) (Fin N) ℂ)) i j = 0

/-- **The shared family commutes with the connecting unitary.**  Off the axis the spectrum is
constant, so those entries commute for free; the entries that straddle the axis vanish by
adjacency. -/
theorem diag_commute_of_axis {m : Fin N} {W : Matrix (Fin N) (Fin N) ℂ}
    (hW : ∀ i j : Fin N, i ≠ j → (i = m ∨ j = m) → W i j = 0) (x : ℝ) :
    W * (diagFamily (x • axisSplit m)).mat = (diagFamily (x • axisSplit m)).mat * W := by
  ext i j
  rw [diagFamily_mat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · rw [hij]; ring
  · by_cases hi : i = m
    · rw [hW i j hij (Or.inl hi), zero_mul, mul_zero]
    · by_cases hj : j = m
      · rw [hW i j hij (Or.inr hj), zero_mul, mul_zero]
      · have hei : (x • axisSplit m) i = 0 := by simp [axisSplit, hi]
        have hej : (x • axisSplit m) j = 0 := by simp [axisSplit, hj]
        rw [hei, hej]
        ring

/-- **A commuting base point is diagonal in both frames.**  If `F* G` commutes with `D`, then
`F D F* = G D G*`. -/
theorem adU_eq_of_commute {F G : Matrix (Fin N) (Fin N) ℂ}
    (hF' : F * Fᴴ = 1) (hG' : G * Gᴴ = 1) {D : HermitianMat (Fin N) ℂ}
    (hcomm : (Fᴴ * G) * D.mat = D.mat * (Fᴴ * G)) :
    adU F D = adU G D := by
  ext1
  simp only [adU_apply, HermitianMat.conj_apply_mat]
  have h1 : F * D.mat * Fᴴ = F * D.mat * Fᴴ * (G * Gᴴ) := by
    rw [hG', Matrix.mul_one]
  have h2 : F * D.mat * Fᴴ * (G * Gᴴ) = F * (D.mat * (Fᴴ * G)) * Gᴴ := by
    simp only [Matrix.mul_assoc]
  have h3 : F * ((Fᴴ * G) * D.mat) * Gᴴ = (F * Fᴴ) * (G * D.mat * Gᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [h1, h2, ← hcomm, h3, hF', Matrix.one_mul]

/-- **Cross-frame coherence.**  The per-frame twist parameter takes the same value at any two
axis-adjacent frames.

The base point `a_x = Ad_F (diagFamily (x • axisSplit m))` is diagonal in both frames, so the
workhorse computes `P.sp a_x b` twice — once with `frameTwist F`, once with `frameTwist G` —
and the two twist products therefore agree at `a_x` for every effect `b`.  Stripping the
conjugation and running `x` over an interval, `twist_param_unique_of_scaled` forces the two
parameters to be equal, with no `2π` ambiguity. -/
theorem frameTwist_eq_of_adjAxis (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) {F G : Matrix.unitaryGroup (Fin N) ℂ}
    (hadj : AdjAxis F G) :
    frameTwist hN P hS2 F = frameTwist hN P hS2 G := by
  obtain ⟨m, hm⟩ := hadj
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨m', hm'⟩ := exists_ne m
  have hsne : axisSplit m m ≠ axisSplit m m' := by
    simp only [axisSplit, if_neg hm']
    norm_num
  refine twist_param_unique_of_scaled (Ne.symm hm') zero_lt_one hsne ?_
  intro x hx
  have hxpos : (0 : ℝ) < x := hx.1
  have hr : ∀ k, (x • axisSplit m) k ≤ 0 := by
    intro k
    simp only [Pi.smul_apply, smul_eq_mul, axisSplit]
    by_cases hk : k = m
    · rw [if_pos hk]; linarith
    · rw [if_neg hk, mul_zero]
  have hFU := unitaryGroup_conjTranspose_mul F
  have hFU' := unitaryGroup_mul_conjTranspose F
  have hGU' := unitaryGroup_mul_conjTranspose G
  have hGdiag : adU (F : Matrix (Fin N) (Fin N) ℂ) (diagFamily (x • axisSplit m))
      = adU (G : Matrix (Fin N) (Fin N) ℂ) (diagFamily (x • axisSplit m)) :=
    adU_eq_of_commute hFU' hGU' (diag_commute_of_axis hm x)
  refine twistSeq_eq_of_adU hFU hFU' ?_ (pairProj_isEffect (Ne.symm hm'))
  intro c hc
  rw [← sp_eq_twistSeq_frame hN P hS2 F hr rfl hc,
    sp_eq_twistSeq_frame hN P hS2 G hr hGdiag hc]

/-! ## The article's own frame adjacency

`AdjAxis` is not the relation `lem:adjacent` and `lem:frame-connectivity` are stated with.
The article's frames are adjacent when they **differ by a rotation inside a single rank-two
block** `q = p₁ + p₂ = p'₁ + p'₂` and **share the remaining atoms** `p₃, …, p_n`
(`main.tex`, `lem:adjacent`).  In the unitary coordinates used here that says the connecting
unitary `F*G` is diagonal outside one pair of indices: every off-diagonal entry `(k,l)`
vanishes unless *both* `k` and `l` lie in the distinguished pair.

`AdjBlock` below is that relation, and `adjAxis_of_adjBlock` is the observation that closes
`lem:adjacent` at the article's own generality: at rank `n ≥ 3` a two-element pair cannot
exhaust the indices, so an article-adjacent pair of frames shares at least one whole
coordinate axis, which is exactly `AdjAxis`.  Hence `frameTwist_eq_of_adjBlock`.

**`AdjBlock` is strictly finer than `AdjAxis`, and this direction is the only free one.**
`AdjAxis` asks that *some* axis be fixed; `AdjBlock` asks that *all but two* be.  So
connectivity for the article's graph (`lem:frame-connectivity`) does **not** follow from
`adjAxis_connected` — it is a strictly stronger statement, needing every unitary to
factor into rank-two block rotations (a Givens/Jacobi decomposition) rather than into the
three axis-fixing Householder factors `exists_axisFixing_factor` provides.  That row stays
open; see `THEOREM-MAP.md`. -/

/-- **The article's frame adjacency.**  `F` and `G` differ by a rotation inside the rank-two
block on indices `i ≠ j` and agree on every other atom: `F*G` is diagonal outside `{i, j}`,
i.e. an off-diagonal entry `(k,l)` can be nonzero only when `k` and `l` both lie in
`{i, j}`. -/
def AdjBlock (F G : Matrix.unitaryGroup (Fin N) ℂ) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧ ∀ k l : Fin N, k ≠ l →
    ((k ≠ i ∧ k ≠ j) ∨ (l ≠ i ∧ l ≠ j)) →
    ((F : Matrix (Fin N) (Fin N) ℂ)ᴴ * (G : Matrix (Fin N) (Fin N) ℂ)) k l = 0

/-- At rank `n ≥ 3` a pair of indices cannot exhaust `Fin N`, so some axis lies outside the
distinguished block. -/
theorem exists_notMem_pair (hN : 3 ≤ N) {i j : Fin N} :
    ∃ m : Fin N, m ≠ i ∧ m ≠ j := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset (Fin N)) ⊆ {i, j} := by
    intro x _
    rcases eq_or_ne x i with h | h
    · exact h ▸ Finset.mem_insert_self i {j}
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hcon x h))
  have h1 : (Finset.univ : Finset (Fin N)).card ≤ ({i, j} : Finset (Fin N)).card :=
    Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin N)).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- **The article's adjacency implies axis adjacency** (`n ≥ 3`).  Article-adjacent frames
share all but two atoms, hence at least one; that shared axis witnesses `AdjAxis`. -/
theorem adjAxis_of_adjBlock (hN : 3 ≤ N) {F G : Matrix.unitaryGroup (Fin N) ℂ}
    (h : AdjBlock F G) : AdjAxis F G := by
  obtain ⟨i, j, _, hFG⟩ := h
  obtain ⟨m, hmi, hmj⟩ := exists_notMem_pair (i := i) (j := j) hN
  refine ⟨m, fun k l hkl hm => ?_⟩
  rcases hm with hk | hl
  · exact hFG k l hkl (Or.inl ⟨hk ▸ hmi, hk ▸ hmj⟩)
  · exact hFG k l hkl (Or.inr ⟨hl ▸ hmi, hl ▸ hmj⟩)

/-- **`lem:adjacent` at the article's own adjacency relation.**  Frames differing by a
rotation inside one rank-two block, and sharing the remaining atoms, carry the same twist
parameter. -/
theorem frameTwist_eq_of_adjBlock (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) {F G : Matrix.unitaryGroup (Fin N) ℂ}
    (hadj : AdjBlock F G) :
    frameTwist hN P hS2 F = frameTwist hN P hS2 G :=
  frameTwist_eq_of_adjAxis hN P hS2 (adjAxis_of_adjBlock hN hadj)

end Necessity
