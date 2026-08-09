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
    (hU' : U * Uᴴ = 1) (a b : HermitianMat (Fin N) ℂ) :
    adU Uᴴ (HermitianMat.twistSeq t (adU U a) b)
      = HermitianMat.twistSeq t a (adU Uᴴ b) := by
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

`hδ` is **necessary, and provably so** (checked 2026-08-08 by disproving the hypothesis-free
version, not merely by failing to prove it): at `δ = 0` the premise quantifies over `0 ≤ x ≤ 0`,
so only `x = 0`, where the distance is `0 < 1` — the premise then holds for *every* `t`, while
`π / (3 * 0) = 0` in Lean would force `|t| ≤ 0`.  `t = 1` refutes it. -/
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
invariant under that, so it is a function of the *unordered* frame — which is the first of the
three things `lem:n2-descent` needs (the others, boundedness and continuity, remain open).

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

Added 2026-08-08 after a cold reviewer was asked whether the two generators really suffice.
They do, and the composition is now checked rather than argued. -/
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
`abs_le_of_phase_near_one` is the numerical step that converts "phase near `1` at every small
scale" into a bound.

**What remains, precisely** (see `LEDGER.md`): joint continuity of the readout in `(x, U)`,
which needs continuity of the product in its *second* argument as well as its first — and
that is available, because `Necessity.seqLeftMul` realizes `b ↦ P.sp a b` as an honest
`→ₗ[ℝ]` linear map (`seqLeftMul_apply_effect`), so on a finite-dimensional carrier
continuity in `b` is automatic; plus a fixed test effect whose frame coefficient never
vanishes, plus assembly.  None of that is a missing theorem; it is plumbing. -/

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

/-! The two halves of the joint continuity the banked `lem:n2-bounded` route needs.

Both are proved; **the assembly into `ContinuousOn` of the readout is NOT**, and the obstruction
is elaboration cost rather than mathematics — four distinct formulations all hit a `whnf`
heartbeat timeout while unifying the composite against `n2Readout`'s unfolding, even at
`maxHeartbeats 1000000`. Recorded in `LEDGER.md`. The mathematical point that mattered is
settled by these two: because the test effect `b` is *fixed*, S2's first-argument-only
continuity is enough, and no continuity in the second argument is required. -/

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

/-- The readout: the `(0,1)` entry of `P.sp (base point in the frame of `U`) b`, pulled back
to the standard frame. -/
noncomputable def n2Readout (b : HermitianMat (Fin 2) ℂ) (x : ℝ)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) : ℂ :=
  (adU ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ)
    (P.sp (adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) b)).mat 0 1

/-- **The readout identity.**  The readout is the frame coefficient, times an explicit
positive scalar, times the pure phase `e^{-i t(U) x}`.  Everything except the phase is
explicit and nonvanishing, which is what makes the frame parameter accessible to an analytic
argument for the first time. -/
theorem n2Readout_eq (hS2 : P.FirstArgContinuous) {b : HermitianMat (Fin 2) ℂ}
    (hb : IsEffect b) {x : ℝ} (hx : 0 ≤ x) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    n2Readout P b x U
      = ((Real.sqrt (Real.exp (-x)) : ℝ) : ℂ)
        * Complex.exp (((-(n2FrameTwist P hS2 U * x) : ℝ) : ℂ) * Complex.I)
        * n2Coef b U := by
  have hcls := n2_sp_eq_twistSeq_frame P hS2 U (basePt_exponent_nonpos hx)
    (a := adU (U : Matrix (Fin 2) (Fin 2) ℂ) (basePt x)) rfl hb
  unfold n2Readout
  rw [hcls, adU_conj_twistSeq _ (unitaryGroup_conjTranspose_mul U)
    (unitaryGroup_mul_conjTranspose U)]
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

/-- **An independent derivation of the readout formula, as a standing cross-check on the sign.**

`n2Readout_eq` reaches the formula through `n2_sp_eq_twistSeq_frame` and `adU_conj_twistSeq`.
This states the same formula for the twist product at the standard frame, derived directly from
`twistSeq_diagFamily_entry` and nothing else.  Two routes, one formula: if a refactor ever flips
the phase in either chain, these stop agreeing.

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

end RankTwoExtraction

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
