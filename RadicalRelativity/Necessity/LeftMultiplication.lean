/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SequentialProduct
import RadicalRelativity.Hermitian.OrderUnit
import RadicalRelativity.Vendor.HermitianMat.Proj

set_option linter.style.longLine false

/-!
# The left multiplication of an unknown sequential product is linear
(campaign LEDGER 2.1, first unit: paper `lem:homog`(i))

Throughout, `P` is an **arbitrary** `SequentialProductOn (HermitianMat n ℂ)` — the
unknown product of the necessity direction over the carrier's FIXED Loewner
order-unit structure (see the design note in `SequentialProduct.lean`: an
instance-quantified formulation cannot see the carrier's order).  This file proves
the paper's `lem:homog`(i) matrix-concretely: for every effect `a`, the map
`b ↦ P.sp a b` extends uniquely from the effect interval to a positive linear map
`seqLeftMul P a : H_n(ℂ) →ₗ[ℝ] H_n(ℂ)`.

The ladder (only S1, its derived monotonicity, effect closure, and the carrier's
full Archimedean property are used — no S2, matching the paper's hypothesis
accounting):

1. `sp_nat_smul` / `sp_div_nat_smul` / `sp_rat_smul` — ℕ- and ℚ≥0-homogeneity on
   effects, by finite additivity (S1) alone.
2. `sp_smul_of_mem_unitInterval` — real homogeneity `P.sp a (t•b) = t•(P.sp a b)`
   for `t ∈ [0,1]`, by an order squeeze between rationals; the Archimedean step is
   `HermitianMat.le_zero_of_forall_le_smul_one`.
3. `spPos` — the positive-cone extension in the second argument, canonically
   normalized by `‖x‖ + 1`, with `spPos_eq_smul` (independence of normalization),
   `spPos_add`, `spPos_smul`.
4. `seqLeftMul` — the linear map, via the vendored decomposition `x = x⁺ - x⁻`;
   well-definedness over arbitrary difference representations is
   `spPos_sub_congr`.  Agreement on effects is `seqLeftMul_apply_effect`;
   positivity `seqLeftMul_nonneg`; monotonicity `seqLeftMul_mono`; unit law
   `seqLeftMul_one`.

`Θ_a := Q_{√a}⁻¹ ∘ seqLeftMul P a` (LEDGER 2.1 proper) builds on this file.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## Step 1: ℕ- and ℚ-homogeneity on effects, from finite additivity -/

theorem sp_nat_smul {a c : HermitianMat n ℂ} (ha : IsEffect a) (hc : IsEffect c) :
    ∀ j : ℕ, (j : ℝ) • c ≤ 1 →
      P.sp a ((j : ℝ) • c) = (j : ℝ) • P.sp a c := by
  intro j
  induction j with
  | zero => intro _; simp [P.sp_zero_right ha]
  | succ j ih =>
    intro hle
    have hjc_le : (j : ℝ) • c ≤ ((j + 1 : ℕ) : ℝ) • c := by
      apply smul_le_smul_of_nonneg_right _ hc.1
      push_cast; linarith
    have hj1 : (j : ℝ) • c ≤ 1 := le_trans hjc_le hle
    have hjc : IsEffect ((j : ℝ) • c) := ⟨smul_nonneg (by positivity) hc.1, hj1⟩
    have hsplit : ((j + 1 : ℕ) : ℝ) • c = (j : ℝ) • c + c := by
      push_cast
      rw [add_smul, one_smul]
    rw [hsplit] at hle
    rw [hsplit, P.sp_add_right ha hjc hc hle, ih hj1]
    push_cast
    rw [add_smul, one_smul]

theorem sp_div_nat_smul {a b : HermitianMat n ℂ} (ha : IsEffect a) (hb : IsEffect b)
    {p k : ℕ} (hpk : p ≤ k) (hk : 0 < k) :
    P.sp a (((p : ℝ) / (k : ℝ)) • b) = ((p : ℝ) / (k : ℝ)) • P.sp a b := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set c : HermitianMat n ℂ := ((k : ℝ))⁻¹ • b with hcdef
  have hc0 : 0 ≤ c := smul_nonneg (by positivity) hb.1
  have hkc : (k : ℝ) • c = b := by
    rw [hcdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]
  have hc1 : c ≤ 1 := by
    calc c = (1 : ℝ) • c := (one_smul ℝ c).symm
      _ ≤ (k : ℝ) • c := smul_le_smul_of_nonneg_right (Nat.one_le_cast.mpr hk) hc0
      _ = b := hkc
      _ ≤ 1 := hb.2
  have hc : IsEffect c := ⟨hc0, hc1⟩
  have hpc_le : (p : ℝ) • c ≤ 1 := by
    calc (p : ℝ) • c ≤ (k : ℝ) • c := by
          apply smul_le_smul_of_nonneg_right _ hc0
          exact_mod_cast hpk
      _ = b := hkc
      _ ≤ 1 := hb.2
  have hkc_le : (k : ℝ) • c ≤ 1 := by rw [hkc]; exact hb.2
  have hp := sp_nat_smul P ha hc p hpc_le
  have hkk := sp_nat_smul P ha hc k hkc_le
  rw [hkc] at hkk
  have hdiv : ((p : ℝ) / (k : ℝ)) • b = (p : ℝ) • c := by
    rw [hcdef, smul_smul, div_eq_mul_inv]
  rw [hdiv, hp, hkk, smul_smul]
  congr 1
  field_simp

theorem sp_rat_smul {a b : HermitianMat n ℂ} (ha : IsEffect a) (hb : IsEffect b)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp a ((q : ℝ) • b) = (q : ℝ) • P.sp a b := by
  have hnum : ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0)
  have hcast : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
    rw [hnum, Rat.cast_def]
  have hden : 0 < q.den := q.den_pos
  have hpk : q.num.toNat ≤ q.den := by
    have hden0 : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hden
    have h1 := hq1
    rw [hcast, div_le_one hden0] at h1
    exact_mod_cast h1
  rw [hcast]
  exact sp_div_nat_smul P ha hb hpk hden

/-! ## Step 2: real homogeneity on effects, by the Archimedean squeeze -/

/-- **Real scalar homogeneity in the second argument** for `t ∈ [0,1]`
(paper `lem:homog`, effect level).  Uses only S1-derived structure and the
carrier's full Archimedean property. -/
theorem sp_smul_of_mem_unitInterval {a b : HermitianMat n ℂ}
    (ha : IsEffect a) (hb : IsEffect b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp a (t • b) = t • P.sp a b := by
  set y := P.sp a b with hy
  have hy_eff : IsEffect y := P.sp_effect ha hb
  have htb : IsEffect (t • b) :=
    ⟨smul_nonneg ht0 hb.1,
      le_trans (smul_le_smul_of_nonneg_right ht1 hb.1) (by simpa using hb.2)⟩
  set z := P.sp a (t • b) with hz
  have hupper : ∀ ε : ℝ, 0 < ε → z - t • y ≤ ε • 1 := by
    intro ε hε
    rcases lt_or_ge t 1 with htlt | htge
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min htlt (lt_add_of_pos_right t hε))
      have hq0 : (0 : ℚ) ≤ q := by
        have h0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt ht0 hq1)
        exact_mod_cast h0
      have hqle1 : (q : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))
      have hqb : IsEffect ((q : ℝ) • b) :=
        ⟨smul_nonneg (by positivity) hb.1,
          le_trans (smul_le_smul_of_nonneg_right hqle1 hb.1) (by simpa using hb.2)⟩
      have hmono : z ≤ (q : ℝ) • y := by
        rw [hz, hy, ← sp_rat_smul P ha hb hq0 hqle1]
        exact P.sp_mono_right ha htb hqb
          (smul_le_smul_of_nonneg_right (le_of_lt hq1) hb.1)
      calc z - t • y ≤ (q : ℝ) • y - t • y := sub_le_sub_right hmono _
        _ = ((q : ℝ) - t) • y := (sub_smul _ _ _).symm
        _ ≤ ((q : ℝ) - t) • 1 :=
            smul_le_smul_of_nonneg_left hy_eff.2 (by linarith)
        _ ≤ ε • 1 := by
            apply smul_le_smul_of_nonneg_right _ zero_le_one
            have h2 := lt_of_lt_of_le hq2 (min_le_right _ _)
            linarith
    · have ht : t = 1 := le_antisymm ht1 htge
      subst ht
      have hzy : z = y := by rw [hz, hy, one_smul]
      rw [hzy, one_smul, sub_self]
      exact smul_nonneg (le_of_lt hε) zero_le_one
  have hlower : ∀ ε : ℝ, 0 < ε → t • y - z ≤ ε • 1 := by
    intro ε hε
    rcases eq_or_lt_of_le ht0 with ht | htpos
    · rw [hz, ← ht]
      simp only [zero_smul]
      rw [P.sp_zero_right ha]
      simpa using smul_nonneg (le_of_lt hε) (zero_le_one (α := HermitianMat n ℂ))
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self t (lt_min htpos hε))
      have hq0 : (0 : ℚ) ≤ q := by
        have h0 : (0 : ℝ) < (q : ℝ) := by
          have hmin : min t ε ≤ t := min_le_left _ _
          linarith
        exact_mod_cast le_of_lt h0
      have hqle1 : (q : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hq2 ht1)
      have hqb : IsEffect ((q : ℝ) • b) :=
        ⟨smul_nonneg (by positivity) hb.1,
          le_trans (smul_le_smul_of_nonneg_right hqle1 hb.1) (by simpa using hb.2)⟩
      have hmono : (q : ℝ) • y ≤ z := by
        rw [hz, hy, ← sp_rat_smul P ha hb hq0 hqle1]
        exact P.sp_mono_right ha hqb htb
          (smul_le_smul_of_nonneg_right (le_of_lt hq2) hb.1)
      calc t • y - z ≤ t • y - (q : ℝ) • y := sub_le_sub_left hmono _
        _ = (t - (q : ℝ)) • y := (sub_smul _ _ _).symm
        _ ≤ (t - (q : ℝ)) • 1 := by
            apply smul_le_smul_of_nonneg_left hy_eff.2
            linarith
        _ ≤ ε • 1 := by
            apply smul_le_smul_of_nonneg_right _ zero_le_one
            have hmin : min t ε ≤ ε := min_le_right _ _
            linarith
  have h1 : z - t • y ≤ 0 := HermitianMat.le_zero_of_forall_le_smul_one hupper
  have h2 : t • y - z ≤ 0 := HermitianMat.le_zero_of_forall_le_smul_one hlower
  exact le_antisymm (sub_nonpos.mp h1) (sub_nonpos.mp h2)

/-! ## Step 3: positive-cone extension in the second argument -/

/-- The extension of `b ↦ P.sp a b` to the positive cone, canonically normalized. -/
def spPos (a x : HermitianMat n ℂ) : HermitianMat n ℂ :=
  (‖x‖ + 1) • P.sp a ((‖x‖ + 1)⁻¹ • x)

theorem norm_smul_inv_effect {x : HermitianMat n ℂ} (hx : 0 ≤ x) {μ : ℝ}
    (hμ : 0 < μ) (hxμ : x ≤ μ • 1) : IsEffect (μ⁻¹ • x) := by
  refine ⟨smul_nonneg (by positivity) hx, ?_⟩
  calc μ⁻¹ • x ≤ μ⁻¹ • (μ • 1) := smul_le_smul_of_nonneg_left hxμ (by positivity)
    _ = 1 := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hμ), one_smul]

theorem le_norm_add_one_smul_one (x : HermitianMat n ℂ) : x ≤ (‖x‖ + 1) • 1 :=
  le_trans (HermitianMat.le_norm_smul_one x)
    (smul_le_smul_of_nonneg_right (by linarith [norm_nonneg x]) zero_le_one)

/-- The normalization is irrelevant: any admissible scale computes `spPos`. -/
theorem spPos_eq_smul {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x : HermitianMat n ℂ} (hx : 0 ≤ x) {μ : ℝ} (hμ : 0 < μ) (hxμ : x ≤ μ • 1) :
    spPos P a x = μ • P.sp a (μ⁻¹ • x) := by
  have key : ∀ ν ν' : ℝ, 0 < ν → ν ≤ ν' → x ≤ ν • 1 →
      ν' • P.sp a (ν'⁻¹ • x) = ν • P.sp a (ν⁻¹ • x) := by
    intro ν ν' hν hνν' hxν
    have hν' : 0 < ν' := lt_of_lt_of_le hν hνν'
    have heff : IsEffect (ν⁻¹ • x) := norm_smul_inv_effect hx hν hxν
    have hratio0 : (0 : ℝ) ≤ ν / ν' := by positivity
    have hratio1 : ν / ν' ≤ 1 := (div_le_one hν').mpr hνν'
    have hscale : ν'⁻¹ • x = (ν / ν') • (ν⁻¹ • x) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [hscale, sp_smul_of_mem_unitInterval P ha heff hratio0 hratio1, smul_smul]
    congr 1
    field_simp
  have hx_can : x ≤ (‖x‖ + 1) • 1 := le_norm_add_one_smul_one x
  have hcan : (0 : ℝ) < ‖x‖ + 1 := by positivity
  rcases le_total μ (‖x‖ + 1) with h | h
  · rw [spPos, key μ (‖x‖ + 1) hμ h hxμ]
  · rw [spPos, key (‖x‖ + 1) μ hcan h hx_can]

theorem spPos_of_effect {a b : HermitianMat n ℂ} (ha : IsEffect a) (hb : IsEffect b) :
    spPos P a b = P.sp a b := by
  rw [spPos_eq_smul P ha hb.1 one_pos (by simpa using hb.2), inv_one, one_smul, one_smul]

theorem spPos_zero {a : HermitianMat n ℂ} (ha : IsEffect a) : spPos P a 0 = 0 := by
  rw [spPos_eq_smul P ha le_rfl one_pos (by simp), smul_zero, P.sp_zero_right ha, smul_zero]

theorem spPos_nonneg {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x : HermitianMat n ℂ} (hx : 0 ≤ x) : 0 ≤ spPos P a x := by
  rw [spPos]
  have heff := norm_smul_inv_effect hx (μ := ‖x‖ + 1) (by positivity)
    (le_norm_add_one_smul_one x)
  exact smul_nonneg (by positivity) (P.sp_nonneg ha heff)

/-- Positive homogeneity of the cone extension. -/
theorem spPos_smul {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x : HermitianMat n ℂ} (hx : 0 ≤ x) {t : ℝ} (ht : 0 < t) :
    spPos P a (t • x) = t • spPos P a x := by
  have hcan : (0 : ℝ) < ‖x‖ + 1 := by positivity
  have hxc : x ≤ (‖x‖ + 1) • 1 := le_norm_add_one_smul_one x
  have htx : t • x ≤ (t * (‖x‖ + 1)) • 1 := by
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left hxc (le_of_lt ht)
  rw [spPos_eq_smul P ha (smul_nonneg (le_of_lt ht) hx) (mul_pos ht hcan) htx,
    spPos_eq_smul P ha hx hcan hxc]
  have hcollapse : (t * (‖x‖ + 1))⁻¹ • t • x = (‖x‖ + 1)⁻¹ • x := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [hcollapse, mul_smul]

/-- Additivity of the cone extension. -/
theorem spPos_add {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x y : HermitianMat n ℂ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    spPos P a (x + y) = spPos P a x + spPos P a y := by
  set μ : ℝ := ‖x‖ + ‖y‖ + 1 with hμdef
  have hμ : (0 : ℝ) < μ := by positivity
  have hxμ : x ≤ μ • 1 :=
    le_trans (HermitianMat.le_norm_smul_one x)
      (smul_le_smul_of_nonneg_right (by simp only [hμdef]; linarith [norm_nonneg y]) zero_le_one)
  have hyμ : y ≤ μ • 1 :=
    le_trans (HermitianMat.le_norm_smul_one y)
      (smul_le_smul_of_nonneg_right (by simp only [hμdef]; linarith [norm_nonneg x]) zero_le_one)
  have hxyμ : x + y ≤ μ • 1 := by
    calc x + y ≤ ‖x‖ • 1 + ‖y‖ • 1 :=
          add_le_add (HermitianMat.le_norm_smul_one x) (HermitianMat.le_norm_smul_one y)
      _ = (‖x‖ + ‖y‖) • 1 := (add_smul _ _ _).symm
      _ ≤ μ • 1 := smul_le_smul_of_nonneg_right (by simp only [hμdef]; linarith) zero_le_one
  have hxe := norm_smul_inv_effect hx hμ hxμ
  have hye := norm_smul_inv_effect hy hμ hyμ
  have hxye := norm_smul_inv_effect (_root_.add_nonneg hx hy) hμ hxyμ
  have hsum_le : μ⁻¹ • x + μ⁻¹ • y ≤ 1 := by
    rw [← smul_add]
    exact hxye.2
  rw [spPos_eq_smul P ha (_root_.add_nonneg hx hy) hμ hxyμ, spPos_eq_smul P ha hx hμ hxμ,
    spPos_eq_smul P ha hy hμ hyμ, smul_add,
    P.sp_add_right ha hxe hye hsum_le, smul_add]

/-! ## Step 4: the linear extension `seqLeftMul` -/

/-- Well-definedness over difference representations: if `u - v = u' - v'` with all
four in the cone, the extension values agree as differences. -/
theorem spPos_sub_congr {a : HermitianMat n ℂ} (ha : IsEffect a)
    {u v u' v' : HermitianMat n ℂ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hu' : 0 ≤ u') (hv' : 0 ≤ v')
    (h : u - v = u' - v') :
    spPos P a u - spPos P a v = spPos P a u' - spPos P a v' := by
  have hsum : u + v' = u' + v := sub_eq_sub_iff_add_eq_add.mp h
  have h3 := congrArg (spPos P a) hsum
  rw [spPos_add P ha hu hv', spPos_add P ha hu' hv] at h3
  exact sub_eq_sub_iff_add_eq_add.mpr h3

/-- **The left multiplication of the unknown product, as a linear map**
(paper `lem:homog`(i), matrix-concrete): the unique positive linear extension of
`b ↦ P.sp a b` from the effect interval to all of `H_n(ℂ)`. -/
def seqLeftMul (a : HermitianMat n ℂ) (ha : IsEffect a) :
    HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ where
  toFun x := spPos P a x⁺ - spPos P a x⁻
  map_add' x y := by
    have hrep : (x + y)⁺ - (x + y)⁻ = (x⁺ + y⁺) - (x⁻ + y⁻) := by
      rw [HermitianMat.posPart_add_negPart,
        show (x⁺ + y⁺) - (x⁻ + y⁻) = (x⁺ - x⁻) + (y⁺ - y⁻) from by abel,
        HermitianMat.posPart_add_negPart, HermitianMat.posPart_add_negPart]
    rw [spPos_sub_congr P ha (HermitianMat.posPart_nonneg _) (HermitianMat.negPart_nonneg _)
      (_root_.add_nonneg (HermitianMat.posPart_nonneg _) (HermitianMat.posPart_nonneg _))
      (_root_.add_nonneg (HermitianMat.negPart_nonneg _) (HermitianMat.negPart_nonneg _)) hrep,
      spPos_add P ha (HermitianMat.posPart_nonneg _) (HermitianMat.posPart_nonneg _),
      spPos_add P ha (HermitianMat.negPart_nonneg _) (HermitianMat.negPart_nonneg _)]
    abel
  map_smul' t x := by
    simp only [RingHom.id_apply]
    rcases lt_trichotomy t 0 with htneg | htzero | htpos
    · have hrep : (t • x)⁺ - (t • x)⁻ = (-t) • x⁻ - (-t) • x⁺ := by
        rw [HermitianMat.posPart_add_negPart]
        have hx := HermitianMat.posPart_add_negPart x
        rw [show (-t) • x⁻ - (-t) • x⁺ = t • (x⁺ - x⁻) from by
          rw [neg_smul, neg_smul, sub_neg_eq_add, smul_sub]; abel, hx]
      rw [spPos_sub_congr P ha (HermitianMat.posPart_nonneg _) (HermitianMat.negPart_nonneg _)
        (smul_nonneg (by linarith) (HermitianMat.negPart_nonneg _))
        (smul_nonneg (by linarith) (HermitianMat.posPart_nonneg _)) hrep,
        spPos_smul P ha (HermitianMat.negPart_nonneg _) (by linarith : (0:ℝ) < -t),
        spPos_smul P ha (HermitianMat.posPart_nonneg _) (by linarith : (0:ℝ) < -t)]
      rw [neg_smul, neg_smul, smul_sub]
      abel
    · subst htzero
      simp only [zero_smul]
      have h0 : (0 : HermitianMat n ℂ)⁺ - (0 : HermitianMat n ℂ)⁻ =
          (0 : HermitianMat n ℂ) - 0 := by
        rw [HermitianMat.posPart_add_negPart]
        simp
      rw [spPos_sub_congr P ha (HermitianMat.posPart_nonneg _) (HermitianMat.negPart_nonneg _)
        le_rfl le_rfl h0, spPos_zero P ha]
      simp
    · have hrep : (t • x)⁺ - (t • x)⁻ = t • x⁺ - t • x⁻ := by
        rw [HermitianMat.posPart_add_negPart, ← smul_sub, HermitianMat.posPart_add_negPart]
      rw [spPos_sub_congr P ha (HermitianMat.posPart_nonneg _) (HermitianMat.negPart_nonneg _)
        (smul_nonneg (le_of_lt htpos) (HermitianMat.posPart_nonneg _))
        (smul_nonneg (le_of_lt htpos) (HermitianMat.negPart_nonneg _)) hrep,
        spPos_smul P ha (HermitianMat.posPart_nonneg _) htpos,
        spPos_smul P ha (HermitianMat.negPart_nonneg _) htpos, smul_sub]

/-- `seqLeftMul` agrees with the cone extension on the positive cone. -/
theorem seqLeftMul_apply_nonneg {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x : HermitianMat n ℂ} (hx : 0 ≤ x) : seqLeftMul P a ha x = spPos P a x := by
  show spPos P a x⁺ - spPos P a x⁻ = spPos P a x
  have hrep : x⁺ - x⁻ = x - 0 := by rw [HermitianMat.posPart_add_negPart, sub_zero]
  rw [spPos_sub_congr P ha (HermitianMat.posPart_nonneg _) (HermitianMat.negPart_nonneg _)
    hx le_rfl hrep, spPos_zero P ha, sub_zero]

/-- **Agreement on effects**: `seqLeftMul P a` restricts to `b ↦ P.sp a b`. -/
theorem seqLeftMul_apply_effect {a b : HermitianMat n ℂ} (ha : IsEffect a)
    (hb : IsEffect b) : seqLeftMul P a ha b = P.sp a b := by
  rw [seqLeftMul_apply_nonneg P ha hb.1, spPos_of_effect P ha hb]

/-- **Positivity** of the extension. -/
theorem seqLeftMul_nonneg {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x : HermitianMat n ℂ} (hx : 0 ≤ x) : 0 ≤ seqLeftMul P a ha x := by
  rw [seqLeftMul_apply_nonneg P ha hx]
  exact spPos_nonneg P ha hx

/-- **Monotonicity** of the extension. -/
theorem seqLeftMul_mono {a : HermitianMat n ℂ} (ha : IsEffect a)
    {x y : HermitianMat n ℂ} (h : x ≤ y) : seqLeftMul P a ha x ≤ seqLeftMul P a ha y := by
  have h2 := seqLeftMul_nonneg P ha (sub_nonneg.mpr h)
  rw [map_sub] at h2
  exact sub_nonneg.mp h2

/-- **The unit law**: `seqLeftMul P a 1 = a` (via the derived `a & 𝟙 = a`). -/
theorem seqLeftMul_one {a : HermitianMat n ℂ} (ha : IsEffect a) :
    seqLeftMul P a ha 1 = a := by
  have h1 : IsEffect (1 : HermitianMat n ℂ) := isEffect_unit
  rw [seqLeftMul_apply_effect P ha h1]
  exact P.sp_unit_right ha

end Necessity
