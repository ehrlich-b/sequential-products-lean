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

/-! ## Rank two: the per-frame parameter, extracted from an ARBITRARY product

Everything above is the `N ≥ 3` story, where cross-frame constancy collapses the family of
per-frame parameters to a single `t`.  At rank two that collapse is exactly what fails, and
the article's `prop:n2-necessity` is the surviving statement: *one real parameter per ordered
frame*, with no cross-frame constancy.

`THEOREM-MAP.md` recorded that the classification map `product ↦ moduli` "does not exist in
Lean at all", and that the `N ≥ 3` machinery could not be reused because `StabilizerCoupling`
carries `rank_ge : 3 ≤ n`.  The first half is what this section changes; the second half was
true but misleading about *which* machinery is rank-gated.  Auditing the chain: only 15 of the
76 `Necessity/` modules carry a rank-3 hypothesis at all, and the pieces this extraction needs
are all outside them —

* `Necessity.theta` and `thetaPreservesJordan_of_S2` — `prop:theta` on the concrete carrier,
  **no rank hypothesis**.  (This is not an oversight: unital order automorphisms of `H_2(ℂ)`
  are `O(3)` acting on the Bloch ball, which is still exactly `{Ad_U} ∪ {Ad_U ∘ ᵗ}`.  The
  dimension-3 requirement that does exist in this area belongs to *Uhlhorn's* theorem, whose
  hypothesis — preserving transition probabilities between rays — is weaker than being an
  order automorphism.)
* `tvalLm` — the phase rate as an **ℝ-linear functional** of `r`, built from `dChi`, no rank
  hypothesis.  So the "universal-cover lift ⟹ linear functional" step is *already discharged
  in the tree*; `MasterTheorem.RankTwo.n2_necessity` takes a linear `angle` as a parameter,
  and `tvalLm` is exactly the argument it was waiting for.
* `dChi_kills_corner` — the coalescence vanishing, no rank hypothesis.  At `N = 2` it is
  especially cheap: the Peirce 2-corner of `p₀ + p₁ = 1` is the whole algebra
  (`cornerJ2_all`), so `r 0 = r 1` forces `dχ(r) = 0` outright.
* `conjProduct`, `sp_eq_twistSeq_transport`, `sp_eq_twistSeq_diagFamily`, `tval_antisymm` —
  all rank-free.

What remains genuinely rank-3-gated is the *coupling* step `tvalLm_of_coupling`, which uses
`prop:stabilizers` to pin the rate across index pairs.  That is the cross-frame constancy, and
at rank two it is false — which is why the rank-two moduli space is `C(ℝP², ℝ)` and not `ℝ`.

The linearity argument replacing it here is elementary and exact, with no `2π` ambiguity: a
linear functional on `ℝ²` that vanishes on the diagonal `⟨(1,1)⟩` factors through
`r ↦ r 0 - r 1`, so `tvalLm ... 0 1 r = t · (r 0 - r 1)` with `t` its value at `(1,0)`.

**What this section does NOT do.** It produces the frame function
`n2FrameTwist : U(2) → ℝ` and proves the product is the twist with that parameter at every
ordered frame.  It does *not* yet prove that function bounded (`lem:n2-bounded`), continuous
(`lem:n2-continuity`), or invariant under reversing the frame so as to descend to `ℝP²`
(`lem:n2-descent`), and so does not assemble `cor:qubit-classification`.  Those are the next
steps and they now have an input to act on.
-/

/-- Conjugation by a diagonal unitary fixes every diagonal family: each phase cancels
against its own conjugate, entrywise. -/
theorem diagonal_conj_diagFamily {d : Fin N → ℂ}
    (hd : ∀ k, d k * star (d k) = 1) (r : Fin N → ℝ) :
    Matrix.diagonal d * (diagFamily r).mat * (Matrix.diagonal d)ᴴ = (diagFamily r).mat := by
  rw [diagFamily_mat, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  show d k * (Real.exp (r k) : ℂ) * star (d k) = _
  rw [mul_comm (d k) _, mul_assoc, hd k, mul_one]

/-- Transporting a twisted product back along `Ad_{U*}` moves the conjugation onto the
second argument. -/
theorem adU_conj_twistSeq (t : ℝ) {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1)
    (a b : HermitianMat (Fin N) ℂ) :
    adU Uᴴ (HermitianMat.twistSeq t (adU U a) b)
      = HermitianMat.twistSeq t a (adU Uᴴ b) := by
  -- ★ `U * Uᴴ = 1` was a second hypothesis here until a cold reviewer pointed out it is
  -- *redundant* for a square matrix: it follows from `hU` by `mul_eq_one_comm`.  One
  -- assumption stated twice, not two.  (`hU` itself IS load-bearing — certified by a compiled
  -- counterexample at `U = 2·1`, `a = b = 1`, `t = 0`, where the two sides differ 16 vs 4.)
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hb : adU U (adU Uᴴ b) = b := adU_cancel' hU' b
  conv_lhs => rw [← hb]
  rw [twistSeq_adU_mat t hU hU', adU_cancel hU]

/-! ## Phase arithmetic for the frame parameter

Two elementary facts, used to turn "the phase stays near `1` for every small scale" into a
numerical bound on the parameter. -/

/-- `|e^{iθ} − 1|² = 2 − 2 cos θ`. -/
theorem normSq_exp_I_sub_one (θ : ℝ) :
    Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I) - 1) = 2 - 2 * Real.cos θ := by
  rw [Complex.exp_mul_I]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hc : (Complex.cos (θ : ℂ)).im = 0 := by rw [← Complex.ofReal_cos]; simp
  have hs : (Complex.sin (θ : ℂ)).im = 0 := by rw [← Complex.ofReal_sin]; simp
  rw [hc, hs]
  have hpy := Real.sin_sq_add_cos_sq θ
  ring_nf
  nlinarith [hpy]

/-- **The quantitative step.**  If the phase `e^{-i t x}` stays strictly inside the unit
circle about `1` for every scale `x ∈ [0,δ]`, then `|t| ≤ π/(3δ)`.

The witness is explicit: `x = π/(3|t|)` sends the phase to `e^{∓iπ/3}`, which sits at
distance exactly `1` from `1`.  So no intermediate-value argument is needed, and — as
everywhere else in this file — no branch of a logarithm is chosen.

`hδ` is **necessary**, and that is a theorem here rather than a remark:
`not_abs_le_of_phase_near_one_without_pos` below. (It was a remark until a cold reviewer noted
the claim "checked by disproving" had nothing banked behind it.) -/
theorem abs_lt_of_phase_near_one {t δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ δ →
      Complex.normSq (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) - 1) < 1) :
    |t| < Real.pi / (3 * δ) := by
  by_contra hcon
  push_neg at hcon
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnum : 0 < Real.pi / (3 * δ) := by positivity
  have habs : 0 < |t| := lt_of_lt_of_le hnum hcon
  set x : ℝ := Real.pi / (3 * |t|) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hxle : x ≤ δ := by
    rw [hx, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hcon
    nlinarith
  have hcos : Real.cos (-(t * x)) = 1 / 2 := by
    rw [Real.cos_neg]
    have habsne : |t| ≠ 0 := ne_of_gt habs
    have habsx : |t * x| = Real.pi / 3 := by
      rw [abs_mul, abs_of_pos hxpos, hx]
      field_simp
    calc Real.cos (t * x) = Real.cos |t * x| := (Real.cos_abs (t * x)).symm
      _ = Real.cos (Real.pi / 3) := by rw [habsx]
      _ = 1 / 2 := Real.cos_pi_div_three
  have hval := h x hxpos.le hxle
  rw [normSq_exp_I_sub_one, hcos] at hval
  norm_num at hval

/-- **`hδ` in `abs_lt_of_phase_near_one` is necessary** — the hypothesis-free statement is
false, not merely unproved.  At `δ = 0` the premise ranges over `0 ≤ x ≤ 0`, so only `x = 0`,
where the distance is `0 < 1`; it therefore holds for *every* `t`, while Lean's
`π / (3 * 0) = 0` would force `|t| ≤ 0`.  `t = 1` refutes it.

This is the *strong* form of the inert-hypothesis test — disprove the hypothesis-free statement
rather than fail to prove it — and it is banked as a theorem so the claim is checkable. -/
theorem not_abs_le_of_phase_near_one_without_pos :
    ¬ (∀ (t δ : ℝ),
        (∀ x : ℝ, 0 ≤ x → x ≤ δ →
          Complex.normSq (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) - 1) < 1) →
        |t| ≤ Real.pi / (3 * δ)) := by
  intro h
  have hpre : ∀ x : ℝ, 0 ≤ x → x ≤ (0 : ℝ) →
      Complex.normSq (Complex.exp (((-((1 : ℝ) * x) : ℝ) : ℂ) * Complex.I) - 1) < 1 := by
    intro x hx0 hx1
    have hx : x = 0 := le_antisymm hx1 hx0
    subst hx
    norm_num
  have hbad := h 1 0 hpre
  norm_num at hbad

/-- The non-strict form, kept for callers.  ★ Sharpness note (2026-08-08): the strict version
above is the correct statement — the premise `normSq(e^{-itx} − 1) < 1` says `cos(tx) > 1/2`,
which as `x` sweeps `[0,δ]` in the principal branch forces `|t|δ < π/3`.  So the constant `π/3`
is right and the inequality is strict; the earlier `≤` form was correct but weaker.  Found by
doing the sharpness analysis a cold reviewer was asked for. -/
theorem abs_le_of_phase_near_one {t δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ δ →
      Complex.normSq (Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) - 1) < 1) :
    |t| ≤ Real.pi / (3 * δ) :=
  le_of_lt (abs_lt_of_phase_near_one hδ h)

section RankTwoExtraction

variable (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))

/-- Every element of `H_2(ℂ)` lies in the Peirce 2-corner of `p₀ + p₁ = 1`. -/
theorem cornerJ2_all (x : HermitianMat (Fin 2) ℂ) : cornerJ2 (0 : Fin 2) 1 x := by
  refine blockElt_cornerJ2 (fun k hk0 hk1 => ?_)
  revert hk0 hk1
  fin_cases k <;> simp

/-- The generator of the rank-two coherence rotation. -/
def n2Twist (hS2 : P.FirstArgContinuous) : ℝ :=
  tvalLm P hS2 (thetaPreservesJordan_of_S2 P hS2) 0 1 (fun k => if k = 0 then 1 else 0)

theorem n2_tval_diag_zero (hS2 : P.FirstArgContinuous) {r : Fin 2 → ℝ} (h : r 0 = r 1) :
    tvalLm P hS2 (thetaPreservesJordan_of_S2 P hS2) 0 1 r = 0 := by
  rw [tvalLm_apply,
    dChi_kills_corner P hS2 (thetaPreservesJordan_of_S2 P hS2) h (cornerJ2_all _)]
  simp

theorem n2_tval_eq (hS2 : P.FirstArgContinuous) (r : Fin 2 → ℝ) :
    tvalLm P hS2 (thetaPreservesJordan_of_S2 P hS2) 0 1 r
      = n2Twist P hS2 * (r 0 - r 1) := by
  have hdecomp : r = (r 0 - r 1) • (fun k : Fin 2 => if k = 0 then (1 : ℝ) else 0)
      + r 1 • (fun _ : Fin 2 => (1 : ℝ)) := by
    funext k
    fin_cases k <;> simp
  have honesz : tvalLm P hS2 (thetaPreservesJordan_of_S2 P hS2) 0 1
      (fun _ : Fin 2 => (1 : ℝ)) = 0 := n2_tval_diag_zero P hS2 rfl
  conv_lhs => rw [hdecomp]
  rw [map_add, map_smul, map_smul, honesz, smul_zero, add_zero, smul_eq_mul, mul_comm]
  rfl

/-- **The rank-two per-frame parameter, extracted from an arbitrary product.** -/
theorem n2_sp_eq_twistSeq (hS2 : P.FirstArgContinuous) {r : Fin 2 → ℝ}
    (hr : ∀ i, r i ≤ 0) {b : HermitianMat (Fin 2) ℂ} (hb : IsEffect b) :
    P.sp (diagFamily r) b = HermitianMat.twistSeq (n2Twist P hS2) (diagFamily r) b := by
  refine sp_eq_twistSeq_diagFamily P hS2 (thetaPreservesJordan_of_S2 P hS2)
    (n2Twist P hS2) hr (fun i j hij => ?_) hb
  have hcase : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide
  rcases hcase i j hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hi, hj]; exact n2_tval_eq P hS2 r
  · rw [hi, hj, tval_antisymm P hS2 (thetaPreservesJordan_of_S2 P hS2) r 0 1,
      n2_tval_eq P hS2 r]
    ring

/-- **The rank-two frame function.**  The twist parameter of `P` at the ordered frame given
by the columns of `U`, obtained by transporting `P` along `Ad_U` and reading the
standard-frame generator of the transported product. -/
def n2FrameTwist (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  n2Twist (conjProduct P (unitaryGroup_conjTranspose_mul U)
      (unitaryGroup_mul_conjTranspose U))
    (conjProduct_firstArgContinuous P _ _ hS2)

/-- **`prop:n2-necessity`, per ordered frame, from an arbitrary product.** -/
theorem n2_sp_eq_twistSeq_frame (hS2 : P.FirstArgContinuous)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) {r : Fin 2 → ℝ} (hr : ∀ i, r i ≤ 0)
    {a : HermitianMat (Fin 2) ℂ}
    (ha : a = adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily r))
    {b : HermitianMat (Fin 2) ℂ} (hb : IsEffect b) :
    P.sp a b = HermitianMat.twistSeq (n2FrameTwist P hS2 U) a b :=
  sp_eq_twistSeq_transport P (unitaryGroup_conjTranspose_mul U)
    (unitaryGroup_mul_conjTranspose U) ha (n2FrameTwist P hS2 U)
    (fun _b' hb' => n2_sp_eq_twistSeq _ (conjProduct_firstArgContinuous P _ _ hS2) hr hb') hb

/-- **The `(U, r)` form covers every invertible effect**, which is how the article states
`prop:n2-necessity`.  The spectral theorem (`eq_adU_diagFamily`) writes a positive-definite
effect as `Ad_U (diagFamily r)` with `r` the logarithms of its eigenvalues, and those are
nonpositive because the eigenvalues of an effect are at most one — so the restriction to
nonpositive `r` is not a restriction at all.

Added after the arc-5 cold review pointed out that the section proved this but never said
it, so a reader could not see that the `(U, r)` parametrization is exhaustive. -/
theorem n2_every_posDef_effect (hS2 : P.FirstArgContinuous)
    {a b : HermitianMat (Fin 2) ℂ} (ha : IsEffect a) (hbd : (a.mat).PosDef)
    (hb : IsEffect b) :
    P.sp a b = HermitianMat.twistSeq (n2FrameTwist P hS2 a.H.eigenvectorUnitary) a b :=
  n2_sp_eq_twistSeq_frame P hS2 _
    (fun i => log_eigenvalues_nonpos ha hbd i) (eq_adU_diagFamily hbd) hb

/-! ### The frame-reversal clause of `lem:n2-descent`, for an arbitrary product

Reversing an ordered frame means swapping the two columns of `U`.  The frame function is
invariant under that.  ★ **Corrected by a cold reviewer: swap-invariance ALONE does not make it a
function of the unordered frame** — that also needs constancy on the diagonal-phase fibres, which
is `n2FrameTwist_mul_diagonal`, proved further down this file.  This sentence predated that
clause and asserted the conclusion from half the input.

This was banked as remaining boulder work and it should not have been: the arc-5 cold review
produced it in ~35 lines from `n2_sp_eq_twistSeq_frame` plus pre-existing machinery, and it is
adopted here with that provenance. The mechanism is that the swap carries the two-level
spectrum `axisSplit 1` to `axisSplit 0`, so a single base point is diagonal in both the frame
of `U` and the frame of `U * swap`; `twist_param_unique_of_scaled` then pins the two
parameters to each other exactly, over an interval, with no `2π` ambiguity. -/

/-- The swap of the two coordinates. -/
def swapMat : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun k l => if k = l then 0 else 1

theorem swapMat_unitary : swapMat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply]

/-- Frame reversal, as an element of `U(2)`. -/
def swapU : Matrix.unitaryGroup (Fin 2) ℂ := ⟨swapMat, swapMat_unitary⟩

/-- Conjugating a two-level diagonal family by the swap exchanges the two exponents. -/
theorem adU_swap_diagFamily (x : ℝ) :
    adU swapMat (diagFamily (x • axisSplit (1 : Fin 2)))
      = diagFamily (x • axisSplit (0 : Fin 2)) := by
  ext1
  rw [adU_apply, HermitianMat.conj_apply_mat, diagFamily_mat, diagFamily_mat]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, axisSplit,
      Matrix.conjTranspose_apply]

theorem axisSplit_smul_nonpos (m : Fin 2) {x : ℝ} (hx : 0 < x) :
    ∀ k, (x • axisSplit m) k ≤ 0 := by
  intro k
  simp only [Pi.smul_apply, smul_eq_mul, axisSplit]
  by_cases hk : k = m
  · rw [if_pos hk]; linarith
  · rw [if_neg hk, mul_zero]

/-- **`lem:n2-descent`, frame-reversal clause, for an ARBITRARY product**: the rank-two frame
function does not see the order of the frame. -/
theorem n2FrameTwist_reverse (hS2 : P.FirstArgContinuous)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2FrameTwist P hS2 (U * swapU) = n2FrameTwist P hS2 U := by
  refine twist_param_unique_of_scaled (N := 2) (i := 0) (j := 1) (by decide)
    (u := 0) (v := 1) zero_lt_one (s := axisSplit (0 : Fin 2)) (by simp [axisSplit]) ?_
  intro x hx
  have hxpos : (0 : ℝ) < x := hx.1
  have hbase : adU ((U * swapU : Matrix.unitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit (1 : Fin 2)))
      = adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit (0 : Fin 2))) := by
    rw [← adU_swap_diagFamily x]
    ext1
    simp only [adU_apply, HermitianMat.conj_apply_mat, Submonoid.coe_mul]
    show ((U : Matrix (Fin 2) (Fin 2) ℂ) * swapMat) * _
        * ((U : Matrix (Fin 2) (Fin 2) ℂ) * swapMat)ᴴ
      = (U : Matrix (Fin 2) (Fin 2) ℂ) * (swapMat * _ * swapMatᴴ)
        * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine twistSeq_eq_of_adU (U := (U : Matrix (Fin 2) (Fin 2) ℂ))
    (unitaryGroup_conjTranspose_mul U) (unitaryGroup_mul_conjTranspose U) ?_
    (pairProj_isEffect (i := (0 : Fin 2)) (j := 1) (by decide))
  intro c hc
  have h1 := n2_sp_eq_twistSeq_frame P hS2 (U * swapU) (axisSplit_smul_nonpos 1 hxpos)
    (a := adU ((U * swapU : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      (diagFamily (x • axisSplit (1 : Fin 2)))) rfl hc
  have h2 := n2_sp_eq_twistSeq_frame P hS2 U (axisSplit_smul_nonpos 0 hxpos)
    (a := adU (U : Matrix (Fin 2) (Fin 2) ℂ)
      (diagFamily (x • axisSplit (0 : Fin 2)))) rfl hc
  rw [hbase] at h1
  rw [← h1, h2]

/-! ### The diagonal-phase fibre, and why the frame function is a function of the frame

`n2FrameTwist` takes a *unitary*, but `prop:n2-necessity` is about the ordered frame it
presents.  Two unitaries present the same ordered frame exactly when they differ by a
diagonal unitary on the right — each column is rescaled by a phase, which changes no
spectral projection.  `n2FrameTwist_mul_diagonal` says the frame function does not see
that, closing the `U(2) → S²` gap the arc-5 cold review identified; with
`n2FrameTwist_reverse` (order-blindness) the function descends to the *unordered* frame,
i.e. to a point of `ℝP²`.

Both come from one engine, `n2FrameTwist_eq_of_base_eq`: the parameter is pinned by the
products it represents, so any two unitaries presenting the same base points are
indistinguishable to it.  No `2π` bookkeeping enters, because
`twist_param_unique_of_scaled` pins the two parameters over a whole interval of scales. -/

/-- **The frame function only sees the base points.**  If `V` and `U` send a one-parameter
family of two-level spectra to the *same* base point, they carry the same twist parameter. -/
theorem n2FrameTwist_eq_of_base_eq (hS2 : P.FirstArgContinuous)
    (U V : Matrix.unitaryGroup (Fin 2) ℂ) (m m' : Fin 2)
    (hbase : ∀ x : ℝ, 0 < x →
      adU (V : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit m'))
        = adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit m))) :
    n2FrameTwist P hS2 V = n2FrameTwist P hS2 U := by
  -- the spectral-separation side condition is automatic at rank two, for either axis, so it is
  -- discharged here rather than imposed on callers (self-audit, 2026-08-08)
  have hs : (axisSplit m) (0 : Fin 2) ≠ (axisSplit m) 1 := by
    fin_cases m <;> simp [axisSplit]
  refine twist_param_unique_of_scaled (N := 2) (i := 0) (j := 1) (by decide)
    (u := 0) (v := 1) zero_lt_one (s := axisSplit m) hs ?_
  intro x hx
  have hxpos : (0 : ℝ) < x := hx.1
  refine twistSeq_eq_of_adU (U := (U : Matrix (Fin 2) (Fin 2) ℂ))
    (unitaryGroup_conjTranspose_mul U) (unitaryGroup_mul_conjTranspose U) ?_
    (pairProj_isEffect (i := (0 : Fin 2)) (j := 1) (by decide))
  intro c hc
  have h1 := n2_sp_eq_twistSeq_frame P hS2 V (axisSplit_smul_nonpos m' hxpos)
    (a := adU (V : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit m'))) rfl hc
  have h2 := n2_sp_eq_twistSeq_frame P hS2 U (axisSplit_smul_nonpos m hxpos)
    (a := adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit m))) rfl hc
  rw [hbase x hxpos] at h1
  rw [← h1, h2]

/-- **The `U(2) → S²` fibre gap, closed.**  Right multiplication by a diagonal unitary
rescales each frame vector by a phase, leaving every spectral projection — hence the frame —
unchanged, and the frame function does not see it. -/
theorem n2FrameTwist_mul_diagonal (hS2 : P.FirstArgContinuous)
    (U D : Matrix.unitaryGroup (Fin 2) ℂ) {d : Fin 2 → ℂ}
    (hD : (D : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal d) :
    n2FrameTwist P hS2 (U * D) = n2FrameTwist P hS2 U := by
  have hdu : ∀ k, d k * star (d k) = 1 := by
    have h := unitaryGroup_mul_conjTranspose D
    rw [hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at h
    intro k
    have hk := congrFun (congrFun h k) k
    simpa using hk
  refine n2FrameTwist_eq_of_base_eq P hS2 U (U * D) 0 0 ?_
  intro x _
  ext1
  simp only [adU_apply, HermitianMat.conj_apply_mat, Submonoid.coe_mul, hD]
  rw [Matrix.conjTranspose_mul]
  calc (U : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.diagonal d
        * (diagFamily (x • axisSplit (0 : Fin 2))).mat
        * ((Matrix.diagonal d)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
      = (U : Matrix (Fin 2) (Fin 2) ℂ)
        * (Matrix.diagonal d * (diagFamily (x • axisSplit (0 : Fin 2))).mat
          * (Matrix.diagonal d)ᴴ)
        * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by simp only [Matrix.mul_assoc]
    _ = (U : Matrix (Fin 2) (Fin 2) ℂ) * (diagFamily (x • axisSplit (0 : Fin 2))).mat
        * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [diagonal_conj_diagFamily hdu]

/-- **Invariance under the FULL stabilizer of the unordered frame** — the inference that
`n2FrameTwist` descends to `ℝP²`, made machine-checked rather than left as prose.

A unitary presents the ordered frame given by the projections onto its columns, so two
unitaries present the same *unordered* frame exactly when they differ on the right by a diagonal
unitary (rephasing each column) possibly composed with the swap (exchanging them): for `Fin 2`
the monomial group is generated by the diagonal torus together with the single transposition,
and `swap * D = D' * swap` with `D'` the permuted diagonal, so every such element is `D` or
`D * swap`.  Invariance under both generators — `n2FrameTwist_mul_diagonal` and
`n2FrameTwist_reverse` — is therefore invariance under the whole stabilizer.

★ **Precisely what is and is not checked here (narrowed after review).**  What Lean proves is
invariance at the two group *words* `U·D` and `U·D·swap`.  That those words exhaust the
right-stabilizer of the unordered frame — i.e. that a unitary presenting the same unordered pair
of column lines must be monomial — is the paragraph above, and it is **mathematics in prose, not
a Lean statement**.

★ **Second correction, narrowing my own first one:** an earlier version of this note said "nor is
any `S² → ℝ` or `ℝP² → ℝ` object constructed", which overshot.  `RP2`, `QubitFrame` and
`tauModuli : C(QubitFrame, ℝ)` **do** exist, in `RankTwo/`.  What does not exist is such an object
for an *arbitrary* product's `n2FrameTwist` — `tauModuli` is built for the concrete `τ` family.
So: say "invariant under the diagonal torus and the swap"; the descent to `ℝP²` for an arbitrary
product is justified-but-unformalized, while for `τ` it is formalized elsewhere. -/
theorem n2FrameTwist_mul_diagonal_swap (hS2 : P.FirstArgContinuous)
    (U D : Matrix.unitaryGroup (Fin 2) ℂ) {d : Fin 2 → ℂ}
    (hD : (D : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal d) :
    n2FrameTwist P hS2 (U * D * swapU) = n2FrameTwist P hS2 U := by
  rw [n2FrameTwist_reverse P hS2 (U * D), n2FrameTwist_mul_diagonal P hS2 U D hD]

/-! ### Making the frame parameter analytically visible (`lem:n2-bounded`, partial)

`lem:n2-bounded` asserts `sup_n |t̃(n)| < ∞`.  The article proves it by a contradiction that
needs operator-norm continuity of `a ↦ Θ_a` in the *matrix* argument.  The route taken here
avoids `Θ` entirely: it reads the parameter off the product itself as a pure phase, so that
a compactness argument on `U(2)` can bound it.  `n2Readout_eq` is that readout, and
`abs_lt_of_phase_near_one` is the numerical step that converts "phase near `1` at every small
scale" into a bound (strict; `abs_le_of_phase_near_one` is its `≤` corollary).

★★ **This paragraph used to state the remaining work and was WRONG TWICE; both errors were
caught by the ARC-6 cold reviewers and are corrected here rather than appended to.**

It said the route needs "continuity of the product in its *second* argument". **It does not** —
`b` is held fixed, so `U` and `x` enter only the first argument, and S2 alone suffices
(`continuousOn_n2Readout`, below). The `seqLeftMul` justification offered for it solved a
problem that does not arise.

It also said the route needs "a fixed test effect whose frame coefficient never vanishes".
**No such effect exists**, and three reviewers proved it independently: `n2Coef b U` is the
`(0,1)` entry of `Uᴴ b U`, so for *any* Hermitian `b`, taking `U` to be an eigenbasis of `b`
makes that conjugate diagonal and the coefficient zero. Every fixed probe is blind at its own
eigenframe. That is exactly why the construction below uses **two** test effects with no common
eigenbasis, and it is why `n2Weight_pos` is a theorem about a *pair*. The old sentence also
contradicted the very plan it was describing.

★★ **Status, 2026-08-09: nothing remains — `lem:n2-bounded` is PROVED**
(`exists_n2FrameTwist_bound`, at the end of this section, where the four steps and what each
cost are itemized).  The wording that used to close this paragraph — "what actually remains is
one uniform-continuity step" — was the *second* mispricing of this row and is retracted: the
review that refuted it counted four steps, and it was right. Notably, none of the four turned out
to be a uniform-continuity step. -/

/-- The base-point family: spectrum `{e^{-x}, 1}`, hence ordered log-ratio `-x`, tending to
the unit effect as `x → 0`. -/
noncomputable def basePt (x : ℝ) : HermitianMat (Fin 2) ℂ :=
  diagFamily (x • axisSplit (0 : Fin 2))

theorem basePt_exponent_nonpos {x : ℝ} (hx : 0 ≤ x) :
    ∀ i, (x • axisSplit (0 : Fin 2)) i ≤ 0 := by
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, axisSplit]
  by_cases h : i = 0
  · rw [if_pos h]; nlinarith
  · rw [if_neg h, mul_zero]

/-! The two halves of the joint continuity the `lem:n2-bounded` route needs.

★ **Correction (caught by a cold reviewer): this note previously said "the assembly into
`ContinuousOn` of the readout is NOT [proved]" and described four heartbeat timeouts. That is
stale — `continuousOn_n2Readout` below proves exactly it.** The timeouts were real but the fix
was to stop asking `whnf` to unify a composite against `n2Readout`'s unfolding; see that
theorem's docstring. A reader coming top-down was being told the theorem beneath them did not
exist.

The mathematical point these two settle: because the test effect `b` is *fixed*, S2's
first-argument-only continuity is enough, and no continuity of `P.sp` in its second argument is
required anywhere on this route. -/

theorem continuous_basePt : Continuous (basePt) := by
  show Continuous fun x : ℝ => diagFamily (x • axisSplit (0 : Fin 2))
  refine Continuous.subtype_mk ?_ _
  show Continuous fun x : ℝ => (HermitianMat.diagonal ℂ
    (fun i => Real.exp ((x • axisSplit (0 : Fin 2)) i))).mat
  simp only [HermitianMat.diagonal_mat]
  refine continuous_matrix ?_
  intro i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
  · simp only [Matrix.diagonal_apply_ne _ h]
    exact continuous_const

/-- `Ad` is jointly continuous in the unitary and its argument. -/
theorem continuous_adU_pair :
    Continuous fun p : Matrix.unitaryGroup (Fin 2) ℂ × HermitianMat (Fin 2) ℂ =>
      adU ((p.1 : Matrix (Fin 2) (Fin 2) ℂ)) p.2 := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun p : Matrix.unitaryGroup (Fin 2) ℂ × HermitianMat (Fin 2) ℂ =>
    (p.1 : Matrix (Fin 2) (Fin 2) ℂ) * (p.2).mat * (p.1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
  have hU : Continuous fun p : Matrix.unitaryGroup (Fin 2) ℂ × HermitianMat (Fin 2) ℂ =>
      (p.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val.comp continuous_fst
  have hy : Continuous fun p : Matrix.unitaryGroup (Fin 2) ℂ × HermitianMat (Fin 2) ℂ =>
      (p.2).mat := HermitianMat.continuous_mat.comp continuous_snd
  have hstar : Continuous fun p : Matrix.unitaryGroup (Fin 2) ℂ × HermitianMat (Fin 2) ℂ =>
      (p.1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    simp only [← Matrix.star_eq_conjTranspose]; exact continuous_star.comp hU
  exact (hU.mul hy).mul hstar

/-- The frame coefficient of a test effect: its `(0,1)` entry pulled back to the standard
frame. -/
noncomputable def n2Coef (b : HermitianMat (Fin 2) ℂ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) : ℂ :=
  (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) b).mat 0 1

/-- **The two test effects share no eigenbasis** — so the banked boundedness route's combined
weight never vanishes.

`n2Coef b U = (Uᴴ b U) 0 1 = ⟪u, b v⟫` for `u, v` the columns of `U`, and it vanishes for a
given `b` exactly when `v` is an eigenvector of `b`.  So a *single* test effect is not enough:
every non-scalar `b` is blind at the frames that diagonalize it.  Two effects suffice provided
they have no common eigenvector — equivalently, for rank-one projections in dimension two, that
they do not commute.  That is this lemma, and it is why `frameProj 0` together with
`pairProj 0 1` is the right pair.

★ **Scope, corrected by a cold reviewer:** this theorem states only that the two matrices do not
commute.  The chain "non-commuting ⟹ no common eigenvector ⟹ the combined weight never
vanishes" was prose here when it should not have been; it is now the theorem `n2Weight_pos`
below, which is what may be cited for the conclusion.  Note also that non-vanishing here is
*pointwise*; the uniform lower bound the boundedness argument needs is
`exists_n2Weight_lower_bound`. -/
theorem frameProj_pairProj_not_commute :
    (frameProj (0 : Fin 2)).mat * (pairProj (0 : Fin 2) 1).mat
      ≠ (pairProj (0 : Fin 2) 1).mat * (frameProj (0 : Fin 2)).mat := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  simp [frameProj_mat_eq_single, pairProj, HermitianMat.rankOne, Matrix.mul_apply,
    Matrix.single, Pi.single_apply, Matrix.vecMulVec_apply] at h01 h10

/-- The readout: the `(0,1)` entry of `P.sp (base point in the frame of `U`) b`, pulled back
to the standard frame. -/
noncomputable def n2Readout (b : HermitianMat (Fin 2) ℂ) (x : ℝ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) : ℂ :=
  (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
    (P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b)).mat 0 1

/-- **The readout identity.**  The readout is the frame coefficient, times an explicit
positive scalar, times the pure phase `e^{-i t(U) x}`.  Everything except the phase is
explicit.  ★ **Not "nonvanishing" — corrected by a cold reviewer:** `n2Coef b U` *does* vanish,
at exactly the frames that diagonalize `b` (`U = 1`, `b = frameProj 0` is a witness), which is
why the boundedness route below uses two test effects with no common eigenbasis rather than one.
What the identity gives is that the phase is the *only* non-explicit factor. -/
theorem n2Readout_eq (hS2 : P.FirstArgContinuous) {b : HermitianMat (Fin 2) ℂ}
    (hb : IsEffect b) {x : ℝ} (hx : 0 ≤ x) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2Readout P b x U
      = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
        * Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I)
        * n2Coef b U := by
  have hcls := n2_sp_eq_twistSeq_frame P hS2 U (basePt_exponent_nonpos hx)
    (a := adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) rfl hb
  unfold n2Readout
  rw [hcls, adU_conj_twistSeq _ (unitaryGroup_conjTranspose_mul U)]
  rw [show basePt x = diagFamily (x • axisSplit (0 : Fin 2)) from rfl,
    twistSeq_diagFamily_entry]
  have h0 : (x • axisSplit (0 : Fin 2)) 0 = -x := by
    simp only [Pi.smul_apply, smul_eq_mul, axisSplit, if_pos]
    ring
  have h1 : (x • axisSplit (0 : Fin 2)) 1 = 0 := by simp [axisSplit]
  rw [h0, h1]
  simp only [Real.exp_zero, Real.sqrt_one, Complex.ofReal_one, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, star_one]
  rw [n2Coef]
  congr 2
  push_cast
  ring

/-- Pointwise unfolding of the readout, so continuity can be proved about an explicit lambda
and transferred, instead of asking `whnf` to unify a composite against the definition. -/
theorem n2Readout_apply (b : HermitianMat (Fin 2) ℂ) (x : ℝ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2Readout P b x U
      = (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
          (P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b)).mat 0 1 := rfl

/-- **The readout is jointly continuous on `[0,∞) × U(2)`** — the plumbing the banked
`lem:n2-bounded` route needs, and the point where that route could have failed.

S2 gives continuity in the FIRST argument only. Had the test effect `b` needed to vary with `U`,
the composite would not obviously be continuous and the route would be worthless. **Keeping `b`
fixed is exactly what makes it go through**: no continuity of `P.sp` in its *second* argument is
used. (Continuity of `adU` in both of its arguments *is* used — `continuous_adU_pair` — but that
is a property of conjugation, not of the unknown product.)

Note the shape of the proof, because a naive version does not compile: proving continuity of an
*explicit lambda* and transferring with `ContinuousOn.congr` avoids asking `whnf` to unify the
composite against `n2Readout`'s unfolding. Four formulations that did ask for that all hit a
heartbeat timeout even at `maxHeartbeats 1000000`; `n2Readout_apply` plus `congr` costs nothing. -/
theorem continuousOn_n2Readout (hS2 : P.FirstArgContinuous) {b : HermitianMat (Fin 2) ℂ}
    (hb : IsEffect b) :
    ContinuousOn (fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ => n2Readout P b p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ) := by
  have hinner : Continuous fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ =>
      adU ((p.2 : Matrix (Fin 2) (Fin 2) ℂ)) (basePt p.1) := by
    refine Continuous.subtype_mk ?_ _
    show Continuous fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ =>
      (p.2 : Matrix (Fin 2) (Fin 2) ℂ) * (basePt p.1).mat
        * (p.2 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
    have hU : Continuous fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ =>
        (p.2 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val.comp continuous_snd
    have hy : Continuous fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ => (basePt p.1).mat :=
      HermitianMat.continuous_mat.comp (continuous_basePt.comp continuous_fst)
    have hstar : Continuous fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ =>
        (p.2 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
      simp only [← Matrix.star_eq_conjTranspose]; exact continuous_star.comp hU
    exact (hU.mul hy).mul hstar
  have hmem : ∀ p ∈ Set.Ici (0:ℝ) ×ˢ (Set.univ : Set (Matrix.unitaryGroup (Fin 2) ℂ)),
      adU ((p.2 : Matrix (Fin 2) (Fin 2) ℂ)) (basePt p.1)
        ∈ {a : HermitianMat (Fin 2) ℂ | IsEffect a} := fun p hp =>
    adU_isEffect (unitaryGroup_conjTranspose_mul p.2) (unitaryGroup_mul_conjTranspose p.2)
      (diagFamily_isEffect (basePt_exponent_nonpos hp.1))
  have hsp : ContinuousOn (fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ =>
      P.sp (adU ((p.2 : Matrix (Fin 2) (Fin 2) ℂ)) (basePt p.1)) b)
      (Set.Ici 0 ×ˢ Set.univ) := (hS2 hb).comp hinner.continuousOn hmem
  have hpair : ContinuousOn (fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ =>
      ((P.sp (adU ((p.2 : Matrix (Fin 2) (Fin 2) ℂ)) (basePt p.1)) b), p.2))
      (Set.Ici 0 ×ˢ Set.univ) := hsp.prodMk continuousOn_snd
  have houter : Continuous fun q : HermitianMat (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ =>
      ((q.2 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (q.1).mat
        * (q.2 : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 := by
    have hc : Continuous fun q : HermitianMat (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ =>
        (q.2 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val.comp continuous_snd
    have h1 : Continuous fun q : HermitianMat (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ =>
        (q.2 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
      simp only [← Matrix.star_eq_conjTranspose]; exact continuous_star.comp hc
    have hy : Continuous fun q : HermitianMat (Fin 2) ℂ × Matrix.unitaryGroup (Fin 2) ℂ =>
        (q.1).mat := HermitianMat.continuous_mat.comp continuous_fst
    exact (continuous_apply (1 : Fin 2)).comp
      ((continuous_apply (0 : Fin 2)).comp ((h1.mul hy).mul hc))
  refine ((houter.comp_continuousOn hpair).congr ?_)
  intro p hp
  simp only [Function.comp_apply]
  rw [n2Readout_apply, adU_apply, HermitianMat.conj_apply_mat,
    Matrix.conjTranspose_conjTranspose]

/-- The two-effect weighted readout: each readout is paired with the conjugate of its own frame
coefficient, so the coefficients enter as squared moduli and cannot cancel. -/
noncomputable def n2Comb (b₁ b₂ : HermitianMat (Fin 2) ℂ) (x : ℝ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) : ℂ :=
  n2Readout P b₁ x U * star (n2Coef b₁ U) + n2Readout P b₂ x U * star (n2Coef b₂ U)

/-- The total weight. -/
noncomputable def n2Weight (b₁ b₂ : HermitianMat (Fin 2) ℂ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) : ℝ :=
  Complex.normSq (n2Coef b₁ U) + Complex.normSq (n2Coef b₂ U)

/-- **The combined readout is the weight times the pure phase.**

Scope, stated carefully because the tempting phrasing overclaims: this is an *algebraic
identity only*.  It does **not** by itself exhibit `exp(-i t(U) x)` as a continuous function of
`(x, U)` — that additionally needs the weight bounded away from zero, which is
`frameProj_pairProj_not_commute` upgraded to `0 < n2Weight` plus compactness of `U(2)`.

★ **Correction (2026-08-09, ARC-7 cold review): that upgrade IS assembled**, and has been since
ARC-6 — `n2Weight_pos` and `exists_n2Weight_lower_bound`, both below in this file.  The sentence
that used to end this docstring said it "is not yet assembled", which is the **second** instance
in this file of telling a top-down reader that a theorem sixty lines beneath them does not exist
(the first is corrected at the `basePt` section head).  When a claim of absence is written into a
docstring, it has to be re-read every time the file grows. -/
theorem n2Comb_eq (hS2 : P.FirstArgContinuous) {b₁ b₂ : HermitianMat (Fin 2) ℂ}
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂) {x : ℝ} (hx : 0 ≤ x)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2Comb P b₁ b₂ x U
      = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
        * Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I)
        * ((n2Weight b₁ b₂ U : ℝ) : ℂ) := by
  unfold n2Comb n2Weight
  rw [n2Readout_eq P hS2 hb₁ hx U, n2Readout_eq P hS2 hb₂ hx U]
  have hsq : ∀ z : ℂ, z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def]; exact Complex.mul_conj z
  push_cast
  rw [show (∀ A z w : ℂ, A * z * star z + A * w * star w = A * (z * star z + w * star w)) from
    fun A z w => by ring]
  rw [hsq, hsq]

/-! ### Weight positivity: the last ingredient of `lem:n2-bounded`

`n2Coef b U` is the `(0,1)` entry of `Uᴴ b U`, so it vanishes exactly when that conjugate is
diagonal.  If BOTH test effects had vanishing coefficient at the same `U`, both conjugates would
be diagonal, hence commuting; transporting back by `U` would make the two test effects themselves
commute, contradicting `frameProj_pairProj_not_commute`.  Entirely matrix-level — no eigenvector
argument needed. -/

theorem fin2_ne_cases : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide

/-- A `2×2` Hermitian matrix whose `(0,1)` entry vanishes is diagonal. -/
theorem isDiag_of_herm_offdiag_zero {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : B.IsHermitian)
    (h01 : B 0 1 = 0) : ∀ i j, i ≠ j → B i j = 0 := by
  have h10 : B 1 0 = 0 := by
    have hh := congrFun (congrFun hB 1) 0
    simp only [Matrix.conjTranspose_apply] at hh
    rw [← hh, h01]; simp
  intro i j hij
  rcases fin2_ne_cases i j hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hi, hj]; exact h01
  · rw [hi, hj]; exact h10

/-- Two `2×2` matrices that are both diagonal commute. -/
theorem commute_of_isDiag {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : ∀ i j, i ≠ j → A i j = 0) (hB : ∀ i j, i ≠ j → B i j = 0) :
    A * B = B * A := by
  have hA01 : A 0 1 = 0 := hA 0 1 (by decide)
  have hA10 : A 1 0 = 0 := hA 1 0 (by decide)
  have hB01 : B 0 1 = 0 := hB 0 1 (by decide)
  have hB10 : B 1 0 = 0 := hB 1 0 (by decide)
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp [hA01, hA10, hB01, hB10] <;> ring
  · rcases fin2_ne_cases i j hij with ⟨hi, hj⟩ | ⟨hi, hj⟩ <;> subst hi <;> subst hj <;>
      simp [hA01, hA10, hB01, hB10]

/-- **The weight of *this* pair never vanishes, at every frame.**  Scope, narrowed after the
ARC-7 cold review read the old one-line version ("the two-effect weight never vanishes") as a
claim about an arbitrary pair: it is not.  `U` is arbitrary; the pair is *fixed* to
`(frameProj 0, pairProj 0 1)`, and that is essential — the statement is false for a pair with a
common eigenvector, which is what `frameProj_pairProj_not_commute` rules out here. -/
theorem n2Weight_pos (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    0 < n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U := by
  have hw : n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U
      = Complex.normSq (n2Coef (frameProj (0 : Fin 2)) U)
        + Complex.normSq (n2Coef (pairProj (0 : Fin 2) 1) U) := rfl
  have hnn1 := Complex.normSq_nonneg (n2Coef (frameProj (0 : Fin 2)) U)
  have hnn2 := Complex.normSq_nonneg (n2Coef (pairProj (0 : Fin 2) 1) U)
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U
      by rw [hw]; linarith) with h | h
  swap
  · exact h
  exfalso
  rw [hw] at h
  have hz1 : n2Coef (frameProj (0 : Fin 2)) U = 0 :=
    Complex.normSq_eq_zero.mp (by linarith)
  have hz2 : n2Coef (pairProj (0 : Fin 2) 1) U = 0 :=
    Complex.normSq_eq_zero.mp (by linarith)
  have hdiag : ∀ b : HermitianMat (Fin 2) ℂ, n2Coef b U = 0 →
      ∀ i j, i ≠ j → (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) b).mat i j = 0 := by
    intro b hb
    exact isDiag_of_herm_offdiag_zero (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) b).H hb
  have hcomm := commute_of_isDiag (hdiag _ hz1) (hdiag _ hz2)
  -- transport back: Uᴴ b₁ U · Uᴴ b₂ U = Uᴴ (b₁ b₂) U
  have hUU : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 :=
    unitaryGroup_mul_conjTranspose U
  have hexp : ∀ b c : HermitianMat (Fin 2) ℂ,
      (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) b).mat * (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) c).mat
        = (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (b.mat * c.mat)
            * (U : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro b c
    simp only [adU_apply, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose]
    calc (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * b.mat * (U : Matrix (Fin 2) (Fin 2) ℂ)
          * ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * c.mat * (U : Matrix (Fin 2) (Fin 2) ℂ))
        = (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * b.mat
            * ((U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
            * c.mat * (U : Matrix (Fin 2) (Fin 2) ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (b.mat * c.mat)
            * (U : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hexp, hexp] at hcomm
  -- strip the conjugation
  have hstrip : (frameProj (0 : Fin 2)).mat * (pairProj (0 : Fin 2) 1).mat
      = (pairProj (0 : Fin 2) 1).mat * (frameProj (0 : Fin 2)).mat := by
    have h1 := congrArg (fun M => (U : Matrix (Fin 2) (Fin 2) ℂ) * M
      * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) hcomm
    simp only at h1
    have hUUL : (U : Matrix (Fin 2) (Fin 2) ℂ) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := hUU
    calc (frameProj (0 : Fin 2)).mat * (pairProj (0 : Fin 2) 1).mat
        = (U : Matrix (Fin 2) (Fin 2) ℂ) * ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            * ((frameProj (0 : Fin 2)).mat * (pairProj (0 : Fin 2) 1).mat)
            * (U : Matrix (Fin 2) (Fin 2) ℂ)) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
          simp only [← Matrix.mul_assoc, hUUL, Matrix.one_mul]
          simp only [Matrix.mul_assoc, hUUL, Matrix.mul_one]
      _ = (U : Matrix (Fin 2) (Fin 2) ℂ) * ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            * ((pairProj (0 : Fin 2) 1).mat * (frameProj (0 : Fin 2)).mat)
            * (U : Matrix (Fin 2) (Fin 2) ℂ)) * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
          rw [hcomm]
      _ = (pairProj (0 : Fin 2) 1).mat * (frameProj (0 : Fin 2)).mat := by
          simp only [← Matrix.mul_assoc, hUUL, Matrix.one_mul]
          simp only [Matrix.mul_assoc, hUUL, Matrix.mul_one]
  exact frameProj_pairProj_not_commute hstrip

/-! ### From positivity to a uniform lower bound, by compactness of `U(2)` -/

/-- `n2Coef b` is continuous in the unitary. -/
theorem continuous_n2Coef (b : HermitianMat (Fin 2) ℂ) :
    Continuous (n2Coef b) := by
  show Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ => n2Coef b U
  have hrw : (fun U : Matrix.unitaryGroup (Fin 2) ℂ => n2Coef b U)
      = fun U : Matrix.unitaryGroup (Fin 2) ℂ => ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * b.mat
          * (U : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 := by
    funext U
    rw [n2Coef, adU_apply, HermitianMat.conj_apply_mat, Matrix.conjTranspose_conjTranspose]
  rw [hrw]
  have hc : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have h1 : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    simp only [← Matrix.star_eq_conjTranspose]; exact continuous_star.comp hc
  exact (continuous_apply (1 : Fin 2)).comp
    ((continuous_apply (0 : Fin 2)).comp ((h1.mul continuous_const).mul hc))

/-- The weight is continuous. -/
theorem continuous_n2Weight (b₁ b₂ : HermitianMat (Fin 2) ℂ) :
    Continuous (n2Weight b₁ b₂) := by
  show Continuous fun U => Complex.normSq (n2Coef b₁ U) + Complex.normSq (n2Coef b₂ U)
  exact (Complex.continuous_normSq.comp (continuous_n2Coef b₁)).add
    (Complex.continuous_normSq.comp (continuous_n2Coef b₂))

/-- **The weight has a positive lower bound**, by compactness of `U(2)`. -/
theorem exists_n2Weight_lower_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ε ≤ n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U := by
  obtain ⟨U₀, -, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
    (continuous_n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1)).continuousOn
  refine ⟨n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U₀, n2Weight_pos U₀, ?_⟩
  intro U
  exact hmin (Set.mem_univ U)

/-- **An independent derivation of the readout formula, as a standing cross-check on the sign.**

`n2Readout_eq` reaches the formula through `n2_sp_eq_twistSeq_frame` and `adU_conj_twistSeq`.
This states the same formula for the twist product at the standard frame, derived directly from
`twistSeq_diagFamily_entry`.

★ **Scope, corrected by a cold reviewer: this is NOT a fully independent check.** Both chains
bottom out in `twistSeq_diagFamily_entry`, so a sign error *there* would flip both and they would
still agree.  What it does guard is the classification chain — `n2_sp_eq_twistSeq_frame` and
`adU_conj_twistSeq` — which is where a transport or conjugation slip would live.  Call it a
cross-check on the chain, never on the entry lemma.

Kept because the sign here is load-bearing for the banked route to `lem:n2-bounded`, and it was
the one claim in that route argued rather than computed. -/
theorem readout_direct (t x : ℝ) (b : HermitianMat (Fin 2) ℂ) :
    (HermitianMat.twistSeq t (basePt x) b).mat 0 1
      = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
        * Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I)
        * b.mat 0 1 := by
  show (HermitianMat.twistSeq t (diagFamily (x • axisSplit (0 : Fin 2))) b).mat 0 1 = _
  rw [twistSeq_diagFamily_entry]
  have h0 : (x • axisSplit (0 : Fin 2)) 0 = -x := by
    simp only [Pi.smul_apply, smul_eq_mul, axisSplit, if_pos]; ring
  have h1 : (x • axisSplit (0 : Fin 2)) 1 = 0 := by simp [axisSplit]
  rw [h0, h1]
  simp only [Real.exp_zero, Real.sqrt_one, Complex.ofReal_one, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, star_one]
  congr 2
  push_cast; ring

/-! ### `lem:n2-bounded`, assembled

The four steps the ARC-6 cold review itemized, in order.  Recorded because the *pricing* was
wrong twice: this was first banked as "one uniform-continuity step, nothing but plumbing", then
retracted to four steps with one of them genuinely analytic.  The four steps, as executed:

* **(i) the uniform scale.** `exists_uniform_sp_close`. S2 is continuity at *each* effect; what
  the bound needs is one scale good at *every* frame. The bridge is that conjugation is a
  Frobenius isometry (`norm_adU`), so `‖Ad_U(basePt x) − 𝟙‖ = ‖basePt x − 𝟙‖` with the frame
  gone. S2 is then used at the single point `a = 𝟙` and nowhere else. **No compactness.**
* **(ii) stripping the modulus** — the step that had been missed. `n2Comb_eq`'s scalar factor is
  `√(e^{−x})·e^{−itx}`, while `abs_lt_of_phase_near_one` needs `|e^{−itx} − 1|`.
  `norm_phase_sub_one_le` bridges them for the cost of the modulus defect `|1 − √(e^{−x})|`,
  which `exists_sqrtExp_close` makes small on a right interval.
* **(iii) the weight.** `exists_n2Weight_lower_bound` (already in the tree) keeps the divisor off
  zero uniformly. This is the *one* place compactness of `U(2)` enters the route.
* **(iv) the budget, spent in the right order.** `ε` is chosen *after* the weight bound
  `ε₀`, as `ε₀/(4(C+1))` with `C = ‖b₁‖ + ‖b₂‖`; each of the two defects then eats a quarter and
  the total stays under the `< 1` that `abs_lt_of_phase_near_one` demands.

★ Two things the earlier plan got wrong are worth keeping visible. There is no "product metric"
argument available — `PseudoMetricSpace` does not synthesize on `Matrix.unitaryGroup`, only
`UniformSpace` does — and none is needed: the scale is uniform because of an *algebraic* identity
(isometry), not a compactness or uniform-continuity argument. And `Ici 0 ×ˢ univ` is not compact,
which is why nothing here integrates or extremizes over it. -/

/-- A continuous function vanishing at `0` is small on a right interval `[0,δ]`. -/
theorem exists_small_of_continuousAt_zero {f : ℝ → ℝ} (hf : ContinuousAt f 0) (h0 : f 0 = 0)
    {η : ℝ} (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ → |f x| < η := by
  rw [Metric.continuousAt_iff] at hf
  obtain ⟨δ, hδpos, hδ⟩ := hf η hη
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx0 hxle
  have hdx : dist x (0:ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0]; linarith
  have hres := hδ hdx
  rwa [Real.dist_eq, h0, sub_zero] at hres

@[simp]
theorem basePt_zero : basePt 0 = 1 := by
  rw [basePt, show (0 : ℝ) • axisSplit (0 : Fin 2) = 0 from zero_smul _ _, diagFamily_zero]

/-- The base point approaches the unit effect. -/
theorem exists_basePt_close {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ → ‖basePt x - 1‖ < η := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_small_of_continuousAt_zero
    (f := fun x : ℝ => ‖basePt x - 1‖)
    (continuous_norm.comp (continuous_basePt.sub continuous_const)).continuousAt
    (by simp) hη
  exact ⟨δ, hδpos, fun x hx0 hxle => by
    have h := hδ x hx0 hxle; rwa [abs_of_nonneg (norm_nonneg _)] at h⟩

/-- The modulus defect of the base point's square root is small on a right interval — step (ii)'s
numerical input. -/
theorem exists_sqrtExp_close {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ →
      |1 - Real.sqrt (Real.exp (-x))| < η :=
  exists_small_of_continuousAt_zero
    (f := fun x : ℝ => 1 - Real.sqrt (Real.exp (-x)))
    (by fun_prop) (by simp) hη

/-- **Step (ii): stripping the modulus.**  `n2Comb_eq` controls `‖s·E − 1‖` where `s` is a
positive real modulus; the numerical step needs `‖E − 1‖`.  A triangle inequality bridges them
at the cost of the modulus defect `|1 − s|`, and costs nothing else — in particular the phase `E`
is never written as an exponential of a chosen logarithm. -/
theorem norm_phase_sub_one_le {s : ℝ} {E : ℂ} (hE : ‖E‖ = 1) :
    ‖E - 1‖ ≤ |1 - s| + ‖(s : ℂ) * E - 1‖ := by
  calc ‖E - 1‖ = ‖(1 - (s:ℂ)) * E + ((s:ℂ) * E - 1)‖ := by ring_nf
    _ ≤ ‖(1 - (s:ℂ)) * E‖ + ‖(s:ℂ) * E - 1‖ := norm_add_le _ _
    _ = |1 - s| + ‖(s:ℂ) * E - 1‖ := by
        rw [norm_mul, hE, mul_one]
        congr 1
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Step (i): one scale for every frame.**  S2 is applied at the single effect `a = 𝟙`; the
scale it returns is uniform in `U` because conjugation is a Frobenius isometry, so the frame
drops out of `‖Ad_U(basePt x) − 𝟙‖` entirely.

This is the leg the ARC-6 review banked as cheap, and it is: no compactness of `U(2)`, and not
even the explicit value of `‖basePt x − 𝟙‖` (which is `|e^{−x} − 1|`) — continuity of `basePt` at
`0` together with `basePt 0 = 𝟙` is enough. -/
theorem exists_uniform_sp_close (hS2 : P.FirstArgContinuous) {b : HermitianMat (Fin 2) ℂ}
    (hb : IsEffect b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → x ≤ δ →
      ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
        ‖P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b - b‖ < ε := by
  have hcont := (hS2 hb).continuousWithinAt
    (show (1 : HermitianMat (Fin 2) ℂ) ∈ {a : HermitianMat (Fin 2) ℂ | IsEffect a} from
      isEffect_unit)
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨η, hηpos, hη⟩ := hcont ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_basePt_close hηpos
  refine ⟨δ, hδpos, ?_⟩
  intro x hx0 hxle U
  have heff : IsEffect (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) :=
    adU_isEffect (unitaryGroup_conjTranspose_mul U) (unitaryGroup_mul_conjTranspose U)
      (diagFamily_isEffect (basePt_exponent_nonpos hx0))
  have hdist : dist (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x))
      (1 : HermitianMat (Fin 2) ℂ) < η := by
    rw [dist_eq_norm,
      show (1 : HermitianMat (Fin 2) ℂ) = adU (U : Matrix (Fin 2) (Fin 2) ℂ) 1 from
        (adU_unital (unitaryGroup_mul_conjTranspose U)).symm,
      ← adU_sub, norm_adU _ (unitaryGroup_conjTranspose_mul U)]
    exact hδ x hx0 hxle
  have hres := hη heff hdist
  rw [dist_eq_norm, show (1 : HermitianMat (Fin 2) ℂ) = OrderUnitSpace.ousUnit from rfl,
    P.sp_unit_left hb] at hres
  exact hres

/-- The frame coefficient is bounded by its test effect's norm, uniformly in the frame. -/
theorem n2Coef_norm_le (b : HermitianMat (Fin 2) ℂ) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖n2Coef b U‖ ≤ ‖b‖ := by
  have hUh : ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact unitaryGroup_mul_conjTranspose U
  calc ‖n2Coef b U‖ ≤ ‖adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) b‖ :=
        norm_entry_le_norm (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) b) 0 1
    _ = ‖b‖ := norm_adU _ hUh b

/-- The readout deviates from the frame coefficient by at most the product's own deviation from
the unital value. -/
theorem norm_n2Readout_sub_n2Coef (b : HermitianMat (Fin 2) ℂ) (x : ℝ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ‖n2Readout P b x U - n2Coef b U‖
      ≤ ‖P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b - b‖ := by
  have hUh : ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)ᴴ * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact unitaryGroup_mul_conjTranspose U
  have hsub : n2Readout P b x U - n2Coef b U
      = (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
          (P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b - b)).mat 0 1 := by
    rw [adU_sub]; rfl
  rw [hsub]
  calc ‖(adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
          (P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b - b)).mat 0 1‖
      ≤ ‖adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
          (P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b - b)‖ :=
        norm_entry_le_norm _ 0 1
    _ = ‖P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b - b‖ := norm_adU _ hUh _

/-- The combined readout's deviation from the weight, resolved into the two per-effect
deviations.  Each readout is paired with the conjugate of its *own* coefficient, so the
coefficients enter as squared moduli and cannot cancel. -/
theorem n2Comb_sub_weight (b₁ b₂ : HermitianMat (Fin 2) ℂ) (x : ℝ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2Comb P b₁ b₂ x U - ((n2Weight b₁ b₂ U : ℝ) : ℂ)
      = (n2Readout P b₁ x U - n2Coef b₁ U) * star (n2Coef b₁ U)
        + (n2Readout P b₂ x U - n2Coef b₂ U) * star (n2Coef b₂ U) := by
  unfold n2Comb n2Weight
  have hsq : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = z * star z := fun z => by
    rw [Complex.star_def]; exact (Complex.mul_conj z).symm
  push_cast
  rw [hsq, hsq]
  ring

/-- **The core estimate: one scale `δ` at which the phase is near `1` for every frame.**

The budget is spent in the order step (iv) requires: the weight bound `ε₀` comes first, then
`ε := ε₀/(4(C+1))` is chosen against it, then the two scales S2 returns, then the modulus
scale.  Each defect eats a quarter, so the total is at most `1/2 < 1`. -/
theorem exists_uniform_phase_near_one
    (hS2 : P.FirstArgContinuous) {b₁ b₂ : HermitianMat (Fin 2) ℂ}
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂)
    {ε₀ : ℝ} (hε₀pos : 0 < ε₀)
    (hε₀ : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, ε₀ ≤ n2Weight b₁ b₂ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : Matrix.unitaryGroup (Fin 2) ℂ) (x : ℝ), 0 ≤ x → x ≤ δ →
      Complex.normSq
        (Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I) - 1) < 1 := by
  have hC0 : (0:ℝ) ≤ ‖b₁‖ + ‖b₂‖ := by positivity
  have hden : (0:ℝ) < 4 * ((‖b₁‖ + ‖b₂‖) + 1) := by linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := exists_uniform_sp_close P hS2 hb₁ (div_pos hε₀pos hden)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_uniform_sp_close P hS2 hb₂ (div_pos hε₀pos hden)
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := exists_sqrtExp_close (η := 1/4) (by norm_num)
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁pos (lt_min hδ₂pos hδ₃pos), ?_⟩
  intro U x hx0 hxδ
  have hx1 : x ≤ δ₁ := le_trans hxδ (min_le_left _ _)
  have hx2 : x ≤ δ₂ := le_trans hxδ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hx3 : x ≤ δ₃ := le_trans hxδ (le_trans (min_le_right _ _) (min_le_right _ _))
  set ε : ℝ := ε₀ / (4 * ((‖b₁‖ + ‖b₂‖) + 1)) with hεdef
  set E : ℂ := Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I) with hEdef
  set s : ℝ := Real.sqrt (Real.exp (-x)) with hsdef
  set W : ℝ := n2Weight b₁ b₂ U with hWdef
  have hE : ‖E‖ = 1 := by rw [hEdef]; exact Complex.norm_exp_ofReal_mul_I _
  have hWge : ε₀ ≤ W := hε₀ U
  have hWpos : 0 < W := lt_of_lt_of_le hε₀pos hWge
  have hfac : n2Comb P b₁ b₂ x U - ((W : ℝ) : ℂ) = ((s : ℂ) * E - 1) * ((W : ℝ) : ℂ) := by
    rw [n2Comb_eq P hS2 hb₁ hb₂ hx0 U]; ring
  have hd1 : ‖n2Readout P b₁ x U - n2Coef b₁ U‖ < ε :=
    lt_of_le_of_lt (norm_n2Readout_sub_n2Coef P b₁ x U) (hδ₁ x hx0 hx1 U)
  have hd2 : ‖n2Readout P b₂ x U - n2Coef b₂ U‖ < ε :=
    lt_of_le_of_lt (norm_n2Readout_sub_n2Coef P b₂ x U) (hδ₂ x hx0 hx2 U)
  have hnum : ‖n2Comb P b₁ b₂ x U - ((W : ℝ) : ℂ)‖ ≤ ε * (‖b₁‖ + ‖b₂‖) := by
    rw [n2Comb_sub_weight]
    have hbd1 : ‖(n2Readout P b₁ x U - n2Coef b₁ U) * star (n2Coef b₁ U)‖ ≤ ε * ‖b₁‖ := by
      rw [norm_mul, norm_star]
      exact mul_le_mul hd1.le (n2Coef_norm_le b₁ U) (norm_nonneg _) (div_pos hε₀pos hden).le
    have hbd2 : ‖(n2Readout P b₂ x U - n2Coef b₂ U) * star (n2Coef b₂ U)‖ ≤ ε * ‖b₂‖ := by
      rw [norm_mul, norm_star]
      exact mul_le_mul hd2.le (n2Coef_norm_le b₂ U) (norm_nonneg _) (div_pos hε₀pos hden).le
    calc ‖(n2Readout P b₁ x U - n2Coef b₁ U) * star (n2Coef b₁ U)
            + (n2Readout P b₂ x U - n2Coef b₂ U) * star (n2Coef b₂ U)‖
        ≤ ‖(n2Readout P b₁ x U - n2Coef b₁ U) * star (n2Coef b₁ U)‖
            + ‖(n2Readout P b₂ x U - n2Coef b₂ U) * star (n2Coef b₂ U)‖ := norm_add_le _ _
      _ ≤ ε * ‖b₁‖ + ε * ‖b₂‖ := add_le_add hbd1 hbd2
      _ = ε * (‖b₁‖ + ‖b₂‖) := by ring
  have hprod : ‖(s : ℂ) * E - 1‖ * W ≤ ε * (‖b₁‖ + ‖b₂‖) := by
    have h := hnum
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hWpos] at h
    exact h
  have hphase : ‖(s : ℂ) * E - 1‖ ≤ 1/4 := by
    have hstep : ‖(s : ℂ) * E - 1‖ * ε₀ ≤ ε * (‖b₁‖ + ‖b₂‖) :=
      le_trans (mul_le_mul_of_nonneg_left hWge (norm_nonneg _)) hprod
    have hεC : ε * (‖b₁‖ + ‖b₂‖) ≤ ε₀ / 4 := by
      rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
      nlinarith [hε₀pos.le, hC0]
    nlinarith [norm_nonneg ((s : ℂ) * E - 1), hε₀pos]
  have hmod : |1 - s| < 1/4 := hδ₃ x hx0 hx3
  have hEsub : ‖E - 1‖ < 1/2 := by
    have h := norm_phase_sub_one_le (s := s) hE
    linarith
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (E - 1), hEsub]

/-- **`lem:n2-bounded`.**  For any S1–S7 product with S2 on `H₂(ℂ)`, the ordered-frame parameter
is bounded over *all* frames: `sup_U |t̃(U)| < ∞`.

The article proves this by a contradiction argument needing operator-norm continuity of
`a ↦ Θ_a` in the matrix argument.  This route never mentions `Θ`, never chooses a branch of a
logarithm, and needs compactness of `U(2)` at exactly one point (the weight bound). -/
theorem exists_n2FrameTwist_bound (hS2 : P.FirstArgContinuous) :
    ∃ M : ℝ, 0 < M ∧ ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      |n2FrameTwist P hS2 U| ≤ M := by
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := exists_n2Weight_lower_bound
  obtain ⟨δ, hδpos, hδ⟩ := exists_uniform_phase_near_one P hS2
    (frameProj_isProjection (0 : Fin 2)).isEffect
    (pairProj_isEffect (i := (0 : Fin 2)) (j := 1) (by decide)) hε₀pos hε₀
  refine ⟨Real.pi / (3 * δ), by positivity, ?_⟩
  intro U
  exact abs_le_of_phase_near_one hδpos (fun x hx0 hxδ => hδ U x hx0 hxδ)

/-! ### `lem:n2-continuity`, via `arg` rather than the article's `SO(3)` logarithm

With boundedness in hand this row is cheap, and its recorded blocker is exactly what lifted.
Row 33 had priced it as unreachable before `lem:n2-bounded` and had refuted three routes that
tried to bypass boundedness — correctly. The route here is the article's *order* (bound, then
continuity) but not the article's *argument*: no principal branch of a logarithm on `SO(3)` and no
trace formula.

The shape: fix one scale `δ` with `M·δ = π/4`. The readout at that fixed scale exhibits
`U ↦ exp(-i·t̃(U)·δ)` as an explicit *quotient* of continuous functions — numerator the combined
readout, denominator the weight, which never vanishes — hence continuous. The a priori bound then
confines the exponent to `[-π/4, π/4]`, where `Complex.arg` is continuous and inverts the
exponential, so `t̃ = -arg(phase)/δ`.

★ **Why this is not the lifting problem row 33 refuted.** That refutation was of recovering `t̃`
from its phase *without* a bound: a discontinuous section of a covering need not agree with a
continuous lift, and two incommensurable scales pin the value but not continuity. The bound
removes the covering entirely — with `|t̃·δ| ≤ π/4` the phase never leaves one sheet, so `arg` is
an honest inverse rather than a choice of branch. The moral is that the bound was not merely
*prior* to continuity, it was the whole difficulty.

★ Note also that `continuousOn_n2Readout` **is** load-bearing here, though the ARC-7 review
correctly found it is *not* on the critical path of the bound. Same theorem, two rungs, opposite
verdicts — which is why "is X needed?" has to be asked per rung and not per file. -/

theorem arg_exp_ofReal_mul_I {θ : ℝ} (h1 : -Real.pi < θ) (h2 : θ ≤ Real.pi) :
    Complex.arg (Complex.exp ((θ : ℂ) * Complex.I)) = θ := by
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨h1, h2⟩

theorem exp_ofReal_mul_I_mem_slitPlane {θ : ℝ} (h1 : -(Real.pi / 2) < θ)
    (h2 : θ < Real.pi / 2) :
    Complex.exp ((θ : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  refine Or.inl ?_
  rw [Complex.exp_ofReal_mul_I_re]
  exact Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩

/-- **The lifting step, with no covering-space argument.**  A real parameter whose phase at one
fixed scale is continuous, and which is a priori small enough to keep that phase inside the
principal branch, is itself continuous — because there `arg` inverts the exponential outright. -/
theorem continuous_of_continuous_phase {X : Type*} [TopologicalSpace X] {f : X → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hbd : ∀ x, |f x * δ| ≤ Real.pi / 4)
    (hcont : Continuous fun x => Complex.exp (((-(f x * δ) : ℝ) : ℂ) * Complex.I)) :
    Continuous f := by
  have hpi := Real.pi_pos
  have hslit : ∀ x, Complex.exp (((-(f x * δ) : ℝ) : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro x
    have h := hbd x
    rw [abs_le] at h
    exact exp_ofReal_mul_I_mem_slitPlane (by linarith [h.2]) (by linarith [h.1])
  have harg : ∀ x, Complex.arg (Complex.exp (((-(f x * δ) : ℝ) : ℂ) * Complex.I))
      = -(f x * δ) := by
    intro x
    have h := hbd x
    rw [abs_le] at h
    exact arg_exp_ofReal_mul_I (by linarith [h.2]) (by linarith [h.1])
  have hargcont : Continuous fun x =>
      Complex.arg (Complex.exp (((-(f x * δ) : ℝ) : ℂ) * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hcomp : ContinuousAt (Complex.arg ∘ fun y =>
        Complex.exp (((-(f y * δ) : ℝ) : ℂ) * Complex.I)) x :=
      ContinuousAt.comp (Complex.continuousAt_arg (hslit x)) hcont.continuousAt
    exact hcomp
  refine ((hargcont.neg).div_const δ).congr ?_
  intro x
  rw [harg x]
  field_simp

/-- The readout at a *fixed* scale is continuous in the frame.

Note the proof shape, which is the file's standing anti-`whnf` discipline: prove continuity of the
explicit composite and transfer with `Continuous.congr`.  Writing this as a direct term
`(continuousOn_n2Readout …).comp_continuous …` asks the unifier to match a composite against
`n2Readout`'s unfolding and **times out at a million heartbeats**, exactly as four earlier
formulations of `continuousOn_n2Readout` itself did. -/
theorem continuous_n2Readout_fixed (hS2 : P.FirstArgContinuous) {b : HermitianMat (Fin 2) ℂ}
    (hb : IsEffect b) {x : ℝ} (hx : 0 ≤ x) :
    Continuous (fun U : Matrix.unitaryGroup (Fin 2) ℂ => n2Readout P b x U) := by
  have hpair : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ => ((x : ℝ), U) := by fun_prop
  have h : Continuous ((fun p : ℝ × Matrix.unitaryGroup (Fin 2) ℂ => n2Readout P b p.1 p.2)
      ∘ fun U : Matrix.unitaryGroup (Fin 2) ℂ => ((x : ℝ), U)) :=
    (continuousOn_n2Readout P hS2 hb).comp_continuous hpair (fun U => ⟨hx, Set.mem_univ U⟩)
  refine h.congr ?_
  intro U
  simp only [Function.comp_apply]

/-- The combined readout at a fixed scale is continuous in the frame. -/
theorem continuous_n2Comb_fixed (hS2 : P.FirstArgContinuous) {b₁ b₂ : HermitianMat (Fin 2) ℂ}
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂) {x : ℝ} (hx : 0 ≤ x) :
    Continuous (fun U : Matrix.unitaryGroup (Fin 2) ℂ => n2Comb P b₁ b₂ x U) := by
  change Continuous fun U => n2Readout P b₁ x U * star (n2Coef b₁ U)
      + n2Readout P b₂ x U * star (n2Coef b₂ U)
  exact ((continuous_n2Readout_fixed P hS2 hb₁ hx).mul
      (continuous_star.comp (continuous_n2Coef b₁))).add
    ((continuous_n2Readout_fixed P hS2 hb₂ hx).mul
      (continuous_star.comp (continuous_n2Coef b₂)))

/-- **`lem:n2-continuity`.**  For any S1–S7 product with S2 on `H₂(ℂ)` the ordered-frame
parameter is continuous.

Carries S1–S7 + S2 and nothing else.  As with `lem:n2-bounded`, Lean indexes frames by
`U ∈ U(2)` where the article uses `n ∈ S²`; continuity here is continuity of the pullback, which
with fibre-constancy (`n2FrameTwist_mul_diagonal`, `n2FrameTwist_reverse`) is continuity for the
quotient topology. -/
theorem continuous_n2FrameTwist (hS2 : P.FirstArgContinuous) :
    Continuous (n2FrameTwist P hS2) := by
  obtain ⟨M, hMpos, hM⟩ := exists_n2FrameTwist_bound P hS2
  have hb₁ : IsEffect (frameProj (0 : Fin 2)) := (frameProj_isProjection (0 : Fin 2)).isEffect
  have hb₂ : IsEffect (pairProj (0 : Fin 2) 1) :=
    pairProj_isEffect (by decide : (0 : Fin 2) ≠ 1)
  obtain ⟨δ, hδpos, hMδ⟩ : ∃ δ : ℝ, 0 < δ ∧ M * δ = Real.pi / 4 :=
    ⟨Real.pi / (4 * M), by positivity, by field_simp⟩
  have hspos : 0 < Real.sqrt (Real.exp (-δ)) := Real.sqrt_pos.mpr (Real.exp_pos _)
  have hsne : ((Real.sqrt (Real.exp (-δ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hspos)
  have hWne : ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
      ((n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U : ℝ) : ℂ) ≠ 0 :=
    fun U => Complex.ofReal_ne_zero.mpr (ne_of_gt (n2Weight_pos U))
  have hquot : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
      n2Comb P (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) δ U
        / (((Real.sqrt (Real.exp (-δ)) : ℝ) : ℂ)
            * ((n2Weight (frameProj (0 : Fin 2)) (pairProj (0 : Fin 2) 1) U : ℝ) : ℂ)) := by
    refine (continuous_n2Comb_fixed P hS2 hb₁ hb₂ hδpos.le).div
      (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_n2Weight _ _))) ?_
    intro U
    exact mul_ne_zero hsne (hWne U)
  have hphase : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
      Complex.exp (((-(n2FrameTwist P hS2 U * δ) : ℝ) : ℂ) * Complex.I) := by
    refine hquot.congr ?_
    intro U
    have hw := hWne U
    rw [n2Comb_eq P hS2 hb₁ hb₂ hδpos.le U]
    field_simp
  refine continuous_of_continuous_phase hδpos ?_ hphase
  intro U
  rw [abs_mul, abs_of_pos hδpos]
  calc |n2FrameTwist P hS2 U| * δ ≤ M * δ := mul_le_mul_of_nonneg_right (hM U) hδpos.le
    _ = Real.pi / 4 := hMδ

/-! ### The descent onto the frame space — the article's own indexing

★★ **New 2026-08-09 (ARC-7 checkpoint 1 review), and it exists because a cold reviewer refuted the
caveat I had written on rows 32 and 33.**

Those two rows were landed about `n2FrameTwist : U(2) → ℝ`, with a manifest caveat saying that
fibre-constancy plus surjectivity of "the frame map" made this the article's frame-indexed
statement.  The reviewer found two things.  **(a)** No map from `U(2)` to any frame space existed
anywhere in the tree, so the caveat's surjectivity clause was prose about an undefined object.
**(b)** Worse, for CONTINUITY the inference is not merely unproved but *invalid*: continuity of a
pullback along a bare surjection does not give continuity downstairs — that needs a quotient map.
Row 33's caveat was therefore load-bearing and wrong, and the reviewer recommended downgrading.

★★ **It then found the tree already contained something strictly stronger than what I had used, and
that it deletes the expensive step of my own wall certificate.**  `n2FrameTwist_eq_of_base_eq` at
`m = m' = 0` gives constancy on the fibres of `U ↦ Ad_U(frameProj 0)` — genuine fibre-constancy,
not invariance at two group words — because `basePt x = 𝟙 + (e^{−x} − 1)·frameProj 0`, so equal
first spectral projections force equal base points at every scale.  `WallCertificates/lem-n2-descent.lean`
had priced the descent's first step at ~200 lines of `ℂ²` linear algebra ("same first-column ray ⟹
the unitaries differ by a diagonal unitary").  **That step is unnecessary: one never needs rays if
one descends along the projection.**  The whole descent below is ~50 lines.

The lesson, recorded because it is the transferable one: I reached for the *rays* because
`RankTwo/` is written in terms of `ℂP¹`, and never asked whether the parameter's own defining
identity already descended along something cheaper.  A reviewer with no attachment to that
vocabulary saw it immediately.

**What this buys.**  `n2Moduli` below is a function of the FRAME, and rows 32/33 hold for it
outright — so the indexing caveat shrinks to one honest residue: `FrameSpace` is the set of rank-one
projections *presented by unitaries*, and identifying it with `S²`/`ℝP²` needs surjectivity onto all
rank-one projections, which is still absent. -/

section Descent

/-- `basePt` as a rank-one perturbation of the unit — the identity that makes the descent work. -/
theorem basePt_mat_eq (x : ℝ) :
    (basePt x).mat
      = (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + ((Real.exp (-x) : ℂ) - 1) • (frameProj (0 : Fin 2)).mat := by
  rw [basePt, diagFamily_mat, frameProj_mat_eq_single]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Matrix.diagonal, Matrix.single, axisSplit]

/-- **The frame map**: a unitary to its first spectral projection.  This is the article's "frame",
presented concretely; contrast `RankTwo.QubitFrame`, which is the same geometry via rays. -/
noncomputable def frameMap (U : Matrix.unitaryGroup (Fin 2) ℂ) : HermitianMat (Fin 2) ℂ :=
  adU (U : Matrix (Fin 2) (Fin 2) ℂ) (frameProj (0 : Fin 2))

theorem continuous_frameMap : Continuous frameMap := by
  refine Continuous.subtype_mk ?_ _
  change Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
    (U : Matrix (Fin 2) (Fin 2) ℂ) * (frameProj (0 : Fin 2)).mat
      * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
  have hU : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have hstar : Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    simp only [← Matrix.star_eq_conjTranspose]; exact continuous_star.comp hU
  exact (hU.mul continuous_const).mul hstar

/-- **Genuine fibre-constancy.**  Two unitaries with the same first spectral projection carry the
same twist parameter.  Strictly stronger than `n2FrameTwist_mul_diagonal` together with
`n2FrameTwist_reverse`, which are invariance at two group words; this is constancy on the actual
fibres, and it makes the monomial-exhaustion argument those two needed unnecessary. -/
theorem n2FrameTwist_eq_of_frameMap_eq (U V : Matrix.unitaryGroup (Fin 2) ℂ)
    (hS2 : P.FirstArgContinuous) (h : frameMap V = frameMap U) :
    n2FrameTwist P hS2 V = n2FrameTwist P hS2 U := by
  refine n2FrameTwist_eq_of_base_eq P hS2 U V 0 0 ?_
  intro x _
  have hmat : (V : Matrix (Fin 2) (Fin 2) ℂ) * (frameProj (0 : Fin 2)).mat
        * (V : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      = (U : Matrix (Fin 2) (Fin 2) ℂ) * (frameProj (0 : Fin 2)).mat
        * (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
    have hc := congrArg HermitianMat.mat h
    simpa [frameMap, adU_apply, HermitianMat.conj_apply_mat] using hc
  have key : ∀ W : Matrix.unitaryGroup (Fin 2) ℂ,
      (W : Matrix (Fin 2) (Fin 2) ℂ) * (basePt x).mat * (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        = (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + ((Real.exp (-x) : ℂ) - 1) • ((W : Matrix (Fin 2) (Fin 2) ℂ)
              * (frameProj (0 : Fin 2)).mat * (W : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) := by
    intro W
    rw [basePt_mat_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      unitaryGroup_mul_conjTranspose W, Matrix.mul_smul, Matrix.smul_mul]
  change adU (V : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)
      = adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)
  ext1
  rw [adU_apply, adU_apply, HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat,
    key U, key V, hmat]

/-! ### Toward "compatible ⟹ same frame": the two elementary steps

★★ New 2026-08-09.  `WallCertificates/prop-n2-sufficiency.lean` identifies "compatible effects share
a spectral frame" as the load-bearing missing fact for rows 30/35, and its own absence claim about it
was refuted twice over: the hard half (**compatibility ⟹ matrix commutation**) was already in the tree
as `HermitianMat.commute_of_twistSeq_comm`, and the two-parameter form the rank-two application needs
is now `commute_of_twistSeq_comm_param`.  These are the next two steps, and they are the elementary
ones.

**The full chain, so the remainder is a stated size rather than a vague price.**  With
`a = Ad_U(diagFamily r)`, `b = Ad_V(diagFamily s)`, both non-scalar, and `W = UᴴV`:
  1. `P.sp a b = P.sp b a` ⟹ `Commute a b` — `n2_sp_eq_twistSeq_frame` then
     `commute_of_twistSeq_comm_param` (the two parameters differ, which is why the one-parameter form
     did not suffice).  **In the tree.**
  2. conjugating by `Uᴴ`, `Commute (diagFamily r) (Ad_W (diagFamily s))`; since `diagFamily r` is
     diagonal with distinct entries, `M := Ad_W (diagFamily s)` is **diagonal** —
     `offdiag_zero_of_commute_diagonal` below.  **In the tree now.**
  3. `M` is not a scalar (else conjugating back forces `s 0 = s 1`), so its diagonal entries are
     distinct; and `M (W e₀) = e^{s₀}(W e₀)`, so `W e₀` is a multiple of a basis vector —
     `eigen_diagonal_fin2` below.  **The eigenvector step is in the tree now; the "M is not a
     scalar" step is not.**
  4. hence `Ad_W (frameProj 0) ∈ {frameProj 0, frameProj 1}`, so `frameMap V = frameMap U` or
     `= 𝟙 − frameMap U`, and `n2FrameTwist_eq_of_frameMap_eq` / `frameMap_mul_swap` +
     `n2FrameTwist_reverse` finish.  **Not assembled.**
So the honest remainder is steps 3(b) and 4: matrix plumbing over `Fin 2`, no new mathematics, and no
missing vocabulary.  That is a much narrower claim than the certificate's original "nothing in the
tree states it". -/

/-- A matrix commuting with a diagonal matrix of distinct entries is diagonal. -/
theorem offdiag_zero_of_commute_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {d : n → ℂ} (hd : ∀ i j, i ≠ j → d i ≠ d j)
    (h : M * Matrix.diagonal d = Matrix.diagonal d * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  have he := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hz : M i j * (d j - d i) = 0 := by linear_combination he
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact h1
  · exact absurd (sub_eq_zero.mp h2) (Ne.symm (hd i j hij))

/-- An eigenvector of a `2×2` diagonal matrix with distinct entries is supported on a single
coordinate. -/
theorem eigen_diagonal_fin2 {d : Fin 2 → ℂ} (hd : d 0 ≠ d 1)
    {v : Fin 2 → ℂ} {lam : ℂ} (h : Matrix.diagonal d *ᵥ v = lam • v) :
    v 1 = 0 ∨ v 0 = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [Matrix.mulVec_diagonal] at h0 h1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  by_cases hv0 : v 0 = 0
  · exact Or.inr hv0
  · refine Or.inl ?_
    have hlam : lam = d 0 := by
      rcases mul_eq_zero.mp (by linear_combination h0 : (d 0 - lam) * v 0 = 0) with hh | hh
      · exact (sub_eq_zero.mp hh).symm
      · exact absurd hh hv0
    rw [hlam] at h1
    rcases mul_eq_zero.mp (by linear_combination h1 : (d 1 - d 0) * v 1 = 0) with hh | hh
    · exact absurd (sub_eq_zero.mp hh) hd.symm
    · exact hh

/-! ### Residual item (c): reversing the frame complements the frame map

★★ New 2026-08-09.  The rows 32/33 caveat lists three residual items for identifying `FrameSpace`
with `S²`/`ℝP²`; this is the third, and it is the one that carries **row 34** rather than 32/33 — the
`p ↦ 𝟙 − p` quotient that turns the sphere into the projective plane.  The reviewer who enumerated the
three noted the needed identity was absent and elementary; both were right. -/

theorem adU_swap_frameProj_zero :
    adU swapMat (frameProj (0 : Fin 2)) = frameProj (1 : Fin 2) := by
  ext1
  rw [adU_apply, HermitianMat.conj_apply_mat, frameProj_mat_eq_single, frameProj_mat_eq_single]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single,
      Matrix.conjTranspose_apply]

/-- **Reversing the frame complements the frame map.**  With `n2FrameTwist_reverse` this is the
`ℝP²`-side of the descent: the frame function is blind to the complementation that distinguishes
`S²` from `ℝP²`. -/
theorem frameMap_mul_swap (V : Matrix.unitaryGroup (Fin 2) ℂ) :
    frameMap (V * swapU) = 1 - frameMap V := by
  have hVsw : ((V * swapU : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      = (V : Matrix (Fin 2) (Fin 2) ℂ) * swapMat := rfl
  have hstep : frameMap (V * swapU)
      = adU (V : Matrix (Fin 2) (Fin 2) ℂ) (frameProj (1 : Fin 2)) := by
    rw [frameMap, hVsw, ← adU_swap_frameProj_zero]
    ext1
    rw [adU_apply, adU_apply, adU_apply, HermitianMat.conj_apply_mat,
      HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat]
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hsum : frameProj (1 : Fin 2) = 1 - frameProj (0 : Fin 2) := by
    have h := sum_frameProj (n := Fin 2)
    rw [Fin.sum_univ_two] at h
    linear_combination (norm := module) h
  rw [hstep, hsum, adU_sub, adU_unital (unitaryGroup_mul_conjTranspose V), frameMap]

/-! ### Surjectivity of the frame map onto the unit-vector rank-one projections

★★ New 2026-08-09, from the independent review of residual item (a).  This closes the first of the
three items the rows 32/33 caveat lists: every rank-one projection of a unit vector is `frameMap U`
for an explicit `U`.  `RankTwo.orthoVec` is **not** needed — the unitary is written down directly.

★★★ **A RETRACTION ABOUT EVIDENCE, not about content, and it is the more useful half.**  The
reviewer's first report said the substantive half of this "COMPILES", I recorded that in the manifest
on its word, and **it was false at the time**: the proof had an unsolved goal, Lean's error recovery
inserted a `sorry`, and the top-level theorem was carrying `sorryAx`.  The cause was reading
`lake env lean` output through a `head` window that the earlier failures had already filled — the
truncating-pipe failure this project has a rule about, committed by the reviewer and then propagated
by me.  The conclusion survived (it was cheap, and it is genuinely compiled now); the evidence did
not exist when it was claimed.
★ **The check that would have caught it, now standing protocol for scratch work:** count errors over
the FULL output (`grep -cE error`, never a `head` window) and run `#print axioms` on the final
theorem looking for **`sorryAx`**.  For the library itself this is already automatic and stronger —
`AxiomAudit.lean` requires every tracked declaration's closure to lie in
`[propext, Classical.choice, Quot.sound]`, and `sorryAx` is not in that list — which is why the tree
was never at risk even while the claim about it was wrong.

Two pieces of friction cost both of us several attempts, recorded because they are one-word fixes:
`frameMap_frameU` needs **`Matrix.vecMul_diagonal`** in the simp set (with `Matrix.diagonal_apply`
the goals stall at a `ᵥ*` residue), and the `frameProj` *diagonal* form rather than
`frameProj_mat_eq_single` (which leaves `vecHead`/`vecTail` residue).  And `frameU_unitary`'s
`all_goals` must be its own line rather than chained off the multi-line `simp`, or the alternatives
are never reached. -/

/-- The unitary whose first column is `ψ` and whose second is the complement. -/
def frameU (ψ : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ψ 0, -(star (ψ 1)); ψ 1, star (ψ 0)]

theorem frameU_unitary {ψ : Fin 2 → ℂ} (hψ : HermitianMat.nsq ψ = 1) :
    frameU ψ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hn : Complex.normSq (ψ 0) + Complex.normSq (ψ 1) = 1 := by
    unfold HermitianMat.nsq at hψ; rwa [Fin.sum_univ_two] at hψ
  have e0 : (starRingEnd ℂ) (ψ 0) * ψ 0 + (starRingEnd ℂ) (ψ 1) * ψ 1 = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self,
      ← Complex.ofReal_add, hn, Complex.ofReal_one]
  have e1 : ψ 1 * (starRingEnd ℂ) (ψ 1) + ψ 0 * (starRingEnd ℂ) (ψ 0) = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add,
      show Complex.normSq (ψ 1) + Complex.normSq (ψ 0)
        = Complex.normSq (ψ 0) + Complex.normSq (ψ 1) from by ring, hn, Complex.ofReal_one]
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.conjTranspose_apply, star_star]
  all_goals first | exact e0 | exact e1 | ring

theorem frameMap_frameU {ψ : Fin 2 → ℂ} (hψ : HermitianMat.nsq ψ = 1) :
    frameMap ⟨frameU ψ, frameU_unitary hψ⟩ = HermitianMat.rankOne ψ := by
  ext1
  rw [frameMap, adU_apply, HermitianMat.conj_apply_mat, HermitianMat.rankOne_mat,
    frameProj, HermitianMat.diagonal_mat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul_diagonal,
      Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Pi.star_apply]

/-- **Residual item (a): the frame map hits every unit-vector rank-one projection.** -/
theorem exists_frameMap_eq_rankOne (ψ : Fin 2 → ℂ) (hψ : HermitianMat.nsq ψ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, frameMap U = HermitianMat.rankOne ψ :=
  ⟨⟨frameU ψ, frameU_unitary hψ⟩, frameMap_frameU hψ⟩

/-- The space of rank-two frames **presented by unitaries**.

The residual honesty point about rows 32/33: this is the range of `frameMap`, not the full space of
rank-one projections.  The two coincide (every rank-one projection of `ℂ²` is `Ad_U(frameProj 0)`
for some `U`), but that surjectivity is not proved here — it needs assembling `RankTwo.orthoVec`
into a unitary, which the tree never does. -/
def FrameSpace : Type := Set.range frameMap

noncomputable instance : TopologicalSpace FrameSpace := by
  unfold FrameSpace; infer_instance

instance : T2Space FrameSpace := by
  unfold FrameSpace; infer_instance

noncomputable def toFrameSpace : Matrix.unitaryGroup (Fin 2) ℂ → FrameSpace :=
  Set.rangeFactorization frameMap

theorem continuous_toFrameSpace : Continuous toFrameSpace :=
  Continuous.subtype_mk continuous_frameMap _

theorem surjective_toFrameSpace : Function.Surjective toFrameSpace :=
  Set.rangeFactorization_surjective

/-- **The frame map is a QUOTIENT map**, which is the property continuity actually needs (a bare
continuous surjection is not enough).  Free here: `U(2)` is compact — vendored in-tree at
`Vendor/Wigner/UnitaryCompact.lean` — and the frame space is Hausdorff, so a continuous surjection
between them is closed. -/
theorem isQuotientMap_toFrameSpace : Topology.IsQuotientMap toFrameSpace :=
  (continuous_toFrameSpace.isClosedMap).isQuotientMap continuous_toFrameSpace
    surjective_toFrameSpace

open Classical in
/-- **The article's `t̃`, as a function of the frame.** -/
noncomputable def n2Moduli (hS2 : P.FirstArgContinuous) : FrameSpace → ℝ :=
  fun p => n2FrameTwist P hS2 (Classical.choose (show ∃ U, frameMap U = p.1 from p.2))

theorem n2Moduli_toFrameSpace (hS2 : P.FirstArgContinuous)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2Moduli P hS2 (toFrameSpace U) = n2FrameTwist P hS2 U := by
  -- ★★ NB the argument order, and read this together with the anti-`whnf` note on
  -- `continuousOn_n2Readout` above — they are ONE lesson reached from opposite directions, and a
  -- reader who files them as two will learn it a third time.  The lesson: never ask the unifier to
  -- match a composite against a `def`'s unfolding.  There it happened because a term was written in
  -- composite form; here because the metavariable was in the wrong SLOT.  The metavariable must land
  -- in `V`, since the goal's left side is the parameter at the CHOSEN preimage; putting it in `U`
  -- asks Lean to match `n2Moduli …` against `n2FrameTwist …` and times out at `isDefEq`.
  -- ★ What makes this worth a comment rather than a fix-and-forget: I "fixed" that timeout three
  -- times before finding the cause — twice by reformulating (`abbrev` for `def`, `surjInv` for
  -- `Classical.choose`) and once by raising `maxHeartbeats` with a comment blaming the range
  -- subtype.  Raising the budget would have banked a FALSE explanation.  It compiles at the
  -- file's default budget.
  refine n2FrameTwist_eq_of_frameMap_eq P U _ hS2 ?_
  exact Classical.choose_spec (show ∃ W, frameMap W = frameMap U from ⟨U, rfl⟩)

/-- **`lem:n2-continuity` for the frame-indexed parameter** — no longer a statement about a
pullback.  This is what the checkpoint-1 review asked for. -/
theorem continuous_n2Moduli (hS2 : P.FirstArgContinuous) :
    Continuous (n2Moduli P hS2) := by
  rw [isQuotientMap_toFrameSpace.continuous_iff]
  exact (continuous_n2FrameTwist P hS2).congr
    (fun U => (n2Moduli_toFrameSpace P hS2 U).symm)

/-- **`lem:n2-bounded` for the frame-indexed parameter.** -/
theorem exists_n2Moduli_bound (hS2 : P.FirstArgContinuous) :
    ∃ M : ℝ, 0 < M ∧ ∀ p : FrameSpace, |n2Moduli P hS2 p| ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := exists_n2FrameTwist_bound P hS2
  refine ⟨M, hMpos, ?_⟩
  intro p
  obtain ⟨U, hU⟩ := surjective_toFrameSpace p
  rw [← hU, n2Moduli_toFrameSpace]
  exact hM U

/-- **`n2Moduli` is the product's own twist parameter at that frame** — the link that makes the two
labels self-evidencing rather than a reader's exercise.

Contributed by the checkpoint-1 verification pass, which observed that nothing in this section tied
`n2Moduli` back to `P`, so a reader had to chain two theorems to see that it is the twist parameter
and not merely some continuous function that happens to exist. -/
theorem n2_sp_eq_twistSeq_n2Moduli (hS2 : P.FirstArgContinuous)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) {r : Fin 2 → ℝ} (hr : ∀ i, r i ≤ 0)
    {a b : HermitianMat (Fin 2) ℂ}
    (ha : a = adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily r)) (hb : IsEffect b) :
    P.sp a b = HermitianMat.twistSeq (n2Moduli P hS2 (toFrameSpace U)) a b := by
  rw [n2Moduli_toFrameSpace]
  exact n2_sp_eq_twistSeq_frame P hS2 U hr ha hb

/-- **The descent is not vacuous**: the frame space has at least two points, so continuity on it has
content.  Also from the checkpoint-1 verification — it was the one way this whole section could have
been true and empty. -/
theorem frameMap_swap_ne_one :
    frameMap swapU ≠ frameMap (1 : Matrix.unitaryGroup (Fin 2) ℂ) := by
  intro h
  have hc := congrArg (fun a : HermitianMat (Fin 2) ℂ => a.mat 0 0) h
  simp only [frameMap, adU_apply, HermitianMat.conj_apply_mat] at hc
  simp [swapU, swapMat, frameProj, HermitianMat.diagonal, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.diagonal] at hc

end Descent

end RankTwoExtraction

/-! ## A product that is garbage off the effect set — certifying effect hypotheses

★★ **Contributed by the ARC-7 cold review (2026-08-09), and it discharges a standing debt.**

The project's *strong* inert-hypothesis test is: to certify a hypothesis load-bearing, **disprove
the hypothesis-free statement**.  Failing to find a proof certifies nothing.  Four hypotheses in
this file were stuck at the weak form — reasoned load-bearing, not certified — and the recorded
obstacle was real: for the twist product `sp = twistSeq` *everywhere*, and
`twistSeq_diagFamily_entry` holds for every `r` with no sign condition, so the twist product
cannot witness any failure.  What was needed was a **bespoke** product agreeing with the twist
product on effects and differing off them.

`badP` is that product, and it exists for a structural reason worth stating: **every** field of
`SequentialProductOn` guards all of its arguments with `IsEffect`, and `FirstArgContinuous` is a
`ContinuousOn` over `{a | IsEffect a}`.  So the axioms say *nothing* about off-effect values, and
setting them to `0` costs nothing.  The only field needing a thought is `compatible_ortho`, where
`IsEffect (𝟙 - b)` may fail — and then both sides are `0` anyway.

Consequence, stated generally because it is the reusable part: **one construction certifies any
hypothesis whose only job is to place an argument inside the effect set.** The two theorems below
do it for `n2Readout_eq`'s `hb` and `hx`; nothing further is needed for hypotheses of that shape. -/

section EffectHypothesisWitness

open Classical in
/-- The twist product on effects, `0` anywhere else. -/
noncomputable def badSp (t : ℝ) (a b : HermitianMat (Fin 2) ℂ) : HermitianMat (Fin 2) ℂ :=
  if IsEffect a ∧ IsEffect b then (twistProductOn t).sp a b else 0

theorem badSp_eq {t : ℝ} {a b : HermitianMat (Fin 2) ℂ} (ha : IsEffect a) (hb : IsEffect b) :
    badSp t a b = (twistProductOn t).sp a b := if_pos ⟨ha, hb⟩

theorem badSp_eq_zero {t : ℝ} {a b : HermitianMat (Fin 2) ℂ}
    (h : ¬ (IsEffect a ∧ IsEffect b)) : badSp t a b = 0 := if_neg h

/-- **A genuine S1–S7 sequential product that agrees with the twist product on effects and is
`0` off them.**  Every clause reduces to the twist product's, because every clause is guarded by
`IsEffect` on all of its arguments. -/
noncomputable def badP (t : ℝ) : SequentialProductOn (HermitianMat (Fin 2) ℂ) where
  sp := badSp t
  sp_add_right := by
    intro a b c ha hb hc hbc
    have hbc' : IsEffect (b + c) := ⟨_root_.add_nonneg hb.1 hc.1, hbc⟩
    rw [badSp_eq ha hbc', badSp_eq ha hb, badSp_eq ha hc]
    exact (twistProductOn t).sp_add_right ha hb hc hbc
  sp_unit_left := by
    intro a ha
    rw [badSp_eq isEffect_unit ha]
    exact (twistProductOn t).sp_unit_left ha
  sp_zero_symm := by
    intro a b ha hb h
    rw [badSp_eq ha hb] at h
    rw [badSp_eq hb ha]
    exact (twistProductOn t).sp_zero_symm ha hb h
  sp_assoc_of_compatible := by
    intro a b c ha hb hc hcomm
    rw [badSp_eq ha hb, badSp_eq hb ha] at hcomm
    rw [badSp_eq hb hc, badSp_eq ha hb,
      badSp_eq ha ((twistProductOn t).sp_effect hb hc),
      badSp_eq ((twistProductOn t).sp_effect ha hb) hc]
    exact (twistProductOn t).sp_assoc_of_compatible ha hb hc hcomm
  compatible_ortho := by
    intro a b ha hb hcomm
    rw [badSp_eq ha hb, badSp_eq hb ha] at hcomm
    by_cases hob : IsEffect (OrderUnitSpace.ousUnit - b)
    · rw [badSp_eq ha hob, badSp_eq hob ha]
      exact (twistProductOn t).compatible_ortho ha hb hcomm
    · rw [badSp_eq_zero (fun h => hob h.2), badSp_eq_zero (fun h => hob h.1)]
  compatible_add := by
    intro a b c ha hb hc hbc hab hac
    have hbc' : IsEffect (b + c) := ⟨_root_.add_nonneg hb.1 hc.1, hbc⟩
    rw [badSp_eq ha hb, badSp_eq hb ha] at hab
    rw [badSp_eq ha hc, badSp_eq hc ha] at hac
    rw [badSp_eq ha hbc', badSp_eq hbc' ha]
    exact (twistProductOn t).compatible_add ha hb hc hbc hab hac
  compatible_sp := by
    intro a b c ha hb hc hab hac
    rw [badSp_eq ha hb, badSp_eq hb ha] at hab
    rw [badSp_eq ha hc, badSp_eq hc ha] at hac
    rw [badSp_eq hb hc, badSp_eq ha ((twistProductOn t).sp_effect hb hc),
      badSp_eq ((twistProductOn t).sp_effect hb hc) ha]
    exact (twistProductOn t).compatible_sp ha hb hc hab hac
  sp_effect := by
    intro a b ha hb
    rw [badSp_eq ha hb]
    exact (twistProductOn t).sp_effect ha hb

theorem badP_sp (t : ℝ) (a b : HermitianMat (Fin 2) ℂ) :
    (badP t).sp a b = badSp t a b := rfl

/-- `badP` satisfies S2 as well, so it is a witness against the *full* hypothesis set. -/
theorem badP_S2 (t : ℝ) : (badP t).FirstArgContinuous := by
  intro b hb
  refine ContinuousOn.congr (twistProductOn_firstArgContinuous t hb) ?_
  intro a ha
  exact badSp_eq ha hb

theorem n2Coef_one (b : HermitianMat (Fin 2) ℂ) : n2Coef b 1 = b.mat 0 1 := by
  simp [n2Coef, adU_apply]

theorem adU_zero_entry (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (adU M (0 : HermitianMat (Fin 2) ℂ)).mat 0 1 = 0 := by
  rw [adU_apply, HermitianMat.conj_apply_mat]
  simp

theorem negPair_not_effect : ¬ IsEffect ((-1 : ℝ) • pairProj (0 : Fin 2) 1) := by
  intro h
  have h0 : (0 : HermitianMat (Fin 2) ℂ) ≤ (-1 : ℝ) • pairProj (0 : Fin 2) 1 := h.1
  rw [show ((-1 : ℝ) • pairProj (0 : Fin 2) 1) = -(pairProj (0 : Fin 2) 1) by simp] at h0
  have hzero : pairProj (0 : Fin 2) 1 = 0 :=
    le_antisymm (neg_nonneg.mp h0) (pairProj_isEffect (by decide : (0 : Fin 2) ≠ 1)).1
  have hentry : (pairProj (0 : Fin 2) 1).mat 0 1 = (0 : HermitianMat (Fin 2) ℂ).mat 0 1 := by
    rw [hzero]
  rw [pairProj_entry (by decide : (0 : Fin 2) ≠ 1)] at hentry
  simp at hentry

/-- **`n2Readout_eq`'s `hb` is load-bearing — the hypothesis-free statement is FALSE.**  Witness:
`badP 0`, second argument `-pairProj 0 1` (not an effect), `x = 1`, `U = 1`.  The left side is `0`
because the product is garbage there; the right side is a product of three nonzero factors — and
note the value of `n2FrameTwist` is never needed, since `Complex.exp` never vanishes. -/
theorem hb_is_load_bearing :
    ¬ (∀ (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
        (b : HermitianMat (Fin 2) ℂ) (x : ℝ), 0 ≤ x →
        ∀ U : Matrix.unitaryGroup (Fin 2) ℂ,
        n2Readout P b x U
          = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
            * Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I)
            * n2Coef b U) := by
  intro hall
  have hbad := hall (badP 0) (badP_S2 0) ((-1 : ℝ) • pairProj (0 : Fin 2) 1) 1 zero_le_one 1
  have hlhs : n2Readout (badP 0) ((-1 : ℝ) • pairProj (0 : Fin 2) 1) 1 1 = 0 := by
    unfold n2Readout
    rw [badP_sp, badSp_eq_zero (fun h => negPair_not_effect h.2), adU_zero_entry]
  have hcoef : n2Coef ((-1 : ℝ) • pairProj (0 : Fin 2) 1) 1 ≠ 0 := by
    rw [n2Coef_one, HermitianMat.mat_smul, Matrix.smul_apply,
      pairProj_entry (by decide : (0 : Fin 2) ≠ 1)]
    norm_num
  have hsq : ((Real.sqrt (Real.exp (-(1:ℝ))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Real.exp_pos _)))
  rw [hlhs] at hbad
  exact (mul_ne_zero (mul_ne_zero hsq (Complex.exp_ne_zero _)) hcoef) hbad.symm

theorem basePt_neg_not_effect_core : ¬ IsEffect (basePt (-1)) := by
  intro h
  have hpos : (0 : HermitianMat (Fin 2) ℂ) ≤ 1 - basePt (-1) := sub_nonneg.mpr h.2
  rw [show basePt (-1 : ℝ) = diagFamily ((-1 : ℝ) • axisSplit (0 : Fin 2)) from rfl] at hpos
  have hsub : (1 : HermitianMat (Fin 2) ℂ) - diagFamily ((-1 : ℝ) • axisSplit (0 : Fin 2))
      = HermitianMat.diagonal ℂ
        (fun i => 1 - Real.exp (((-1 : ℝ) • axisSplit (0 : Fin 2)) i)) := by
    rw [show (fun i : Fin 2 => 1 - Real.exp (((-1 : ℝ) • axisSplit (0 : Fin 2)) i))
        = (1 : Fin 2 → ℝ) - fun i => Real.exp (((-1 : ℝ) • axisSplit (0 : Fin 2)) i) from rfl,
      HermitianMat.diagonal_sub, HermitianMat.diagonal_one]
    rfl
  rw [hsub, HermitianMat.zero_le_iff, HermitianMat.diagonal_mat] at hpos
  have hd := hpos.diag_nonneg (i := (0 : Fin 2))
  rw [Matrix.diagonal_apply_eq,
    show ((-1 : ℝ) • axisSplit (0 : Fin 2)) 0 = 1 by
      simp only [Pi.smul_apply, smul_eq_mul, axisSplit, if_pos]; ring] at hd
  have hreal : (0 : ℝ) ≤ 1 - Real.exp 1 := (Complex.le_def.mp hd).1
  nlinarith [Real.add_one_le_exp (1 : ℝ)]

theorem adU_one_eq (y : HermitianMat (Fin 2) ℂ) :
    adU ((1 : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) y = y := by
  apply HermitianMat.ext
  simp [adU_apply]

theorem basePt_neg_not_effect :
    ¬ IsEffect (adU ((1 : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
      (basePt (-1))) := by
  rw [adU_one_eq]
  exact basePt_neg_not_effect_core

/-- **`n2Readout_eq`'s `hx` is load-bearing — the hypothesis-free statement is FALSE.**  Witness:
`badP 0`, `b = pairProj 0 1` (an effect this time), `x = -1`, `U = 1`.  At a negative scale the
base point `diag(e, 1)` is not an effect, so the *first* argument leaves the guarded region. -/
theorem hx_is_load_bearing :
    ¬ (∀ (P : SequentialProductOn (HermitianMat (Fin 2) ℂ)) (hS2 : P.FirstArgContinuous)
        {b : HermitianMat (Fin 2) ℂ}, IsEffect b → ∀ (x : ℝ)
        (U : Matrix.unitaryGroup (Fin 2) ℂ),
        n2Readout P b x U
          = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
            * Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I)
            * n2Coef b U) := by
  intro hall
  have hbad := hall (badP 0) (badP_S2 0)
    (pairProj_isEffect (by decide : (0 : Fin 2) ≠ 1)) (-1) 1
  have hlhs : n2Readout (badP 0) (pairProj (0 : Fin 2) 1) (-1) 1 = 0 := by
    unfold n2Readout
    rw [badP_sp, badSp_eq_zero (fun h => basePt_neg_not_effect (by simpa using h.1)),
      adU_zero_entry]
  have hcoef : n2Coef (pairProj (0 : Fin 2) 1) 1 ≠ 0 := by
    rw [n2Coef_one, pairProj_entry (by decide : (0 : Fin 2) ≠ 1)]
    norm_num
  have hsq : ((Real.sqrt (Real.exp (-(-1 : ℝ))) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Real.exp_pos _)))
  rw [hlhs] at hbad
  exact (mul_ne_zero (mul_ne_zero hsq (Complex.exp_ne_zero _)) hcoef) hbad.symm

/-! ### `prop:stabilizers`' ℂ row: the coefficient IS realized by a frame-stabilizer element

★★★ **New 2026-08-09, and it discharges a gap a wall certificate had called unstatable.**

`WallCertificates/differential-trio.lean` recorded row 18's remaining content as "that the
coefficient `tvalCoef` is realized by an element of the frame stabilizer's identity component acting
as `z ↦ i(θ_i − θ_j)z`", and parked it behind a `True` placeholder justified by "the missing object's
*type* needs the stabilizer group as a Lie group with an identity component, which the tree does not
have."

**No Lie-group vocabulary is needed to say it.**  The reviewer who was sent at that certificate wrote
the statement and proved it in four lines from `torusU_block` and `tvalLm_eq_coef_mul`, both already
in the tree.  `torusU t r` (`Necessity/TorusAction.lean`) is the diagonal unitary `diag(e^{i t r_k})`;
`torusU_fixes_frameProj` says it fixes every frame projection — i.e. it *is* in the frame stabilizer —
and `torusU_block` says it rotates the `(i,j)` Peirce block by the phase difference.  That is the
article's `z ↦ i(θ_i − θ_j)z`, in group form.

★ **This is the same failure mode as the quaternionic certificate, one directory over**: the
placeholder's justification was about a *type* I assumed would be needed, not about anything I had
looked for.  A `True` placeholder recorded awkwardness and got read as depth. -/

/-- The torus element fixes the whole Jordan frame **and** rotates each Peirce block by the phase
difference — the frame-stabilizer action of `prop:stabilizers`' ℂ row, in group form. -/
theorem stabilizer_group_action_complex {n : Type*} [Fintype n] [DecidableEq n]
    (t : ℝ) (r : n → ℝ) :
    (∀ k, adU (torusU t r) (frameProj k) = frameProj k)
      ∧ ∀ (i j : n), i ≠ j → ∀ z : ℂ,
          adU (torusU t r) (blockHerm i j z)
            = blockHerm i j (Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z) :=
  ⟨fun k => torusU_fixes_frameProj t r k, fun _ _ hij z => torusU_block t r hij z⟩

/-- **The converse: the frame stabilizer is exactly the diagonal subgroup.**

★★ New 2026-08-09.  After the cold review discharged row 18's forward direction, the rewritten
`WallCertificates/differential-trio.lean` recorded this converse as the row's **single** remaining
stated gap, judged "writable today with `adU`/`frameProj`/`Matrix.unitaryGroup`, no new vocabulary,
and looks like a short matrix argument".  That judgement was right, and this is it — so that
certificate's one gap closed within the hour of being written, which is now the fourth time a
certificate in that directory has been falsified by an attempt.

The argument: fixing `frameProj k` under conjugation is, after multiplying through by `U`, plain
commutation with the matrix unit `E_kk`.  Reading the `(i,k)` entry of `U·E_kk = E_kk·U` gives
`U i k = 0` whenever `i ≠ k`. -/
theorem offdiag_eq_zero_of_fixes_frameProj {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1)
    (hfix : ∀ k, adU U (frameProj k) = frameProj k) :
    ∀ i k, i ≠ k → U i k = 0 := by
  intro i k hik
  have hmat : U * (frameProj k).mat = (frameProj k).mat * U := by
    have h := congrArg HermitianMat.mat (hfix k)
    rw [adU_apply, HermitianMat.conj_apply_mat] at h
    calc U * (frameProj k).mat
        = (U * (frameProj k).mat * Uᴴ) * U := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
      _ = (frameProj k).mat * U := by rw [h]
  have hentry := congrFun (congrFun hmat i) k
  rw [frameProj_mat_eq_single] at hentry
  simpa [Matrix.mul_apply, Matrix.single, Ne.symm hik] using hentry

/-- **The certificate's stated gap, verbatim and proved**: an arbitrary product's coefficient
`tvalCoef` is realized by the frame-stabilizer element `torusU (tvalCoef …) r`, acting on the `(i,j)`
block by the phase the article predicts. -/
theorem tvalCoef_realized_by_stabilizer {N : ℕ}
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ)) (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (i j : Fin N) (hij : i ≠ j) (r : Fin N → ℝ) (z : ℂ) :
    adU (torusU (tvalCoef P hS2 hjord i j) r) (blockHerm i j z)
      = blockHerm i j
          (Complex.exp ((↑(tvalLm P hS2 hjord i j r) : ℂ) * Complex.I) * z) := by
  rw [torusU_block _ r hij z, tvalLm_eq_coef_mul P hS2 hjord hij r]
  congr 3
  push_cast
  ring

/-! ### The parameter is PINNED by the product — so its construction cannot make it wrong

★★★ **New 2026-08-09, and it closes what was the arc's largest unexamined risk by removing the
question rather than answering it.**

A cold reviewer had flagged `tvalLm` and `twist_param_unique_of_scaled` as the top remaining risk:
they carry the *identification* of the parameter — that the number `n2FrameTwist` reads off is the
product's own twist parameter — and unlike a sign error that is invariant under nothing rows 32/33
conclude.  Instead of auditing how `n2FrameTwist` is built, it proved the construction irrelevant.

`n2FrameTwist_unique_param` says `n2FrameTwist P hS2 U` is **the unique real number** at which the
product acts as the twist product at `U`'s frame.  That is the article's *definition* of `t̃(n)`.  So
whatever `tvalLm` computes internally, it cannot produce a wrong number: a defect there could only
surface as `n2_sp_eq_twistSeq_frame` failing to compile, and it compiles.  Non-vacuity is automatic,
because the `∃!` carries its own witness.

★★ **The methodological lesson, which the reviewer stated against its own two previous reports and
which I had accepted uncritically — twice, once by promoting it to "the top item".**  "I have not read
the proof of X" does not belong on a risk list for a kernel-checked theorem with a clean
`#print axioms`: the kernel read it, and it is stricter than any reviewer.  What a reviewer must read
is **statements**, **definitions** (a `def` can silently be the wrong object with no error anywhere),
and **`Prop`-valued hypotheses** (a located stand-in typechecks fine).  This item was closable two
passes earlier by reading three *statements*; what finally closed it was proving a new one. -/

/-- **The frame parameter is pinned by the product.**  Any `t'` at which the product acts as the
twist product at `U`'s frame equals `n2FrameTwist P hS2 U`. -/
theorem n2FrameTwist_pinned (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) (t' : ℝ)
    (h : ∀ r : Fin 2 → ℝ, (∀ i, r i ≤ 0) → ∀ b : HermitianMat (Fin 2) ℂ, IsEffect b →
      P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily r)) b
        = HermitianMat.twistSeq t' (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily r)) b) :
    t' = n2FrameTwist P hS2 U := by
  have hs : (axisSplit (0 : Fin 2)) 0 ≠ (axisSplit (0 : Fin 2)) 1 := by simp [axisSplit]
  refine twist_param_unique_of_scaled (N := 2) (i := 0) (j := 1) (by decide)
    (u := 0) (v := 1) zero_lt_one (s := axisSplit 0) hs ?_
  intro x hx
  have hxpos : (0:ℝ) < x := hx.1
  refine twistSeq_eq_of_adU (U := (U : Matrix (Fin 2) (Fin 2) ℂ))
    (unitaryGroup_conjTranspose_mul U) (unitaryGroup_mul_conjTranspose U) ?_
    (pairProj_isEffect (i := (0 : Fin 2)) (j := 1) (by decide))
  intro c hc
  have h1 := h (x • axisSplit (0 : Fin 2)) (axisSplit_smul_nonpos 0 hxpos) c hc
  have h2 := n2_sp_eq_twistSeq_frame P hS2 U (axisSplit_smul_nonpos 0 hxpos)
    (a := adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily (x • axisSplit (0 : Fin 2)))) rfl hc
  rw [← h1, h2]

/-- **The article's `t̃(n)`, characterised with no reference to `tvalLm` at all.**  This is what makes
rows 32/33 provably about the article's object rather than about a number the tree happens to
compute. -/
theorem n2FrameTwist_unique_param (P : SequentialProductOn (HermitianMat (Fin 2) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃! t : ℝ, ∀ r : Fin 2 → ℝ, (∀ i, r i ≤ 0) → ∀ b : HermitianMat (Fin 2) ℂ, IsEffect b →
      P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily r)) b
        = HermitianMat.twistSeq t (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (diagFamily r)) b :=
  ⟨n2FrameTwist P hS2 U, fun r hr b hb => n2_sp_eq_twistSeq_frame P hS2 U hr rfl hb,
    fun t' ht' => n2FrameTwist_pinned P hS2 U t' ht'⟩

/-! ### The sensitivity guard — what the sign audit found actually matters

★★ **New 2026-08-09, and it replaces a risk this arc had mispriced — including by the reviewer who
raised it.**  A cold reviewer flagged twice that a sign slip in `twistSeq_diagFamily_entry` "would
flip both rows [32 and 33] and `readout_direct` could not catch it", and called it the largest
unexamined risk under those labels.  It then audited the sign — confirmed correct, by an independent
re-derivation from the definitions of `twistRe`/`twistIm`/`twistFactor` that bypasses both lemmas the
tree's route goes through — **and retracted its own pricing.**

The retraction is the useful part.  Row 32 concludes `|t̃(U)| ≤ M` and row 33 concludes
`Continuous t̃`, and **both are invariant under `t̃ ↦ −t̃`** (row 33 under `t̃ ↦ c·t̃` for any
`c ≠ 0`).  So a global sign error could not have falsified either row; it would only have meant the
bounded, continuous object is `−t̃`.  What a sign error costs is the **dictionary** between Lean's `t`
and the manuscript's — a fidelity question about `twistSeq`'s definition, not a soundness question
about any row.  The error mode: treating a shared dependency as load-bearing for every consumer
without asking what each consumer's *statement* is sensitive to.  Same shape as "is X needed?" having
opposite answers on two rungs, which this file already records once.

**What IS load-bearing, and had no theorem guarding it:** the phase must see `t` through a factor
that does not vanish at the probe point.  Here that factor is `r₀ − r₁ = −x`, nonzero for `x > 0`.
Had the phase come out proportional to `r_k + r_l`, or to anything vanishing at `basePt`, the readout
would be **blind to `t`** and the entire boundedness route would collapse silently.  That is what the
`x > 0` side conditions are protecting, and this is the theorem that would fail loudly if a refactor
broke it.

★ Deliberately NOT landed: the reviewer's independent re-derivation of the factor lemma.  It shares
`cfc_diagonal` and `ofReal_polar` with the tree's route, so as a guard it is worth what
`readout_direct` was worth before its scope was corrected — two chains bottoming out in the same
lemma are not independent, and a second "independent check" that is not one is worse than none. -/

/-- `e^{−iπ} = −1`. -/
theorem exp_neg_pi_mul_I : Complex.exp (((-Real.pi : ℝ) : ℂ) * Complex.I) = -1 := by
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- **The readout genuinely sees the parameter.**  At any positive scale, and any test effect with a
nonvanishing frame coefficient, changing `t` changes the readout.

This is the sensitivity the boundedness route depends on and the one thing in the chain that no other
theorem guards: if the phase were ever refactored into a factor vanishing at `basePt`, every
statement above would still typecheck and the route would be silently vacuous. -/
theorem readout_nonconstant_in_param {x : ℝ} (hx : 0 < x) {b : HermitianMat (Fin 2) ℂ}
    (hb : b.mat 0 1 ≠ 0) :
    (HermitianMat.twistSeq (Real.pi / x) (basePt x) b).mat 0 1
      ≠ (HermitianMat.twistSeq 0 (basePt x) b).mat 0 1 := by
  rw [readout_direct, readout_direct]
  have hxne : x ≠ 0 := ne_of_gt hx
  have hph : ((-(Real.pi / x * x) : ℝ) : ℂ) = ((-Real.pi : ℝ) : ℂ) := by
    congr 1
    field_simp
  rw [hph, exp_neg_pi_mul_I]
  have hs : ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (Real.exp_pos _)))
  simp only [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  intro hcon
  refine hb ?_
  have h3 : ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ) * (-(b.mat 0 1))
      = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ) * (b.mat 0 1) := by
    linear_combination hcon
  have h4 := mul_left_cancel₀ hs h3
  linear_combination (-(1:ℂ)/2) * h4

/-- **A sign check that bypasses `twistSeq_diagFamily_entry`.**  Also from the ARC-7 review.

`readout_direct` was kept as a cross-check on the sign, and a reviewer correctly observed it is
*not* independent: it and `n2Readout_eq` both rewrite with `twistSeq_diagFamily_entry`, so an
error there would flip both and they would still agree.  This one goes through
`twistFactor_diagFamily_diagonal` instead, never touching the entry lemma, and localizes the sign
to the twist factor's own `(0,0)` entry — where it is forced by the `+ Complex.I •` in
`twistFactor` and by `Real.log_exp`. -/
theorem sign_check (t x : ℝ) :
    HermitianMat.twistFactor (basePt x) t 0 0
      = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
        * Complex.exp (((-(t * x) : ℝ) : ℂ) * Complex.I) := by
  rw [basePt, twistFactor_diagFamily_diagonal, Matrix.diagonal_apply_eq,
    show (x • axisSplit (0 : Fin 2)) 0 = -x by
      simp only [Pi.smul_apply, smul_eq_mul, axisSplit, if_pos]; ring]
  congr 2
  push_cast
  ring

end EffectHypothesisWitness

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
