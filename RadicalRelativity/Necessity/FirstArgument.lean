/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.LeftMultiplication

set_option linter.style.longLine false

/-!
# First-argument homogeneity of an unknown sequential product
(campaign LEDGER 2.1b: paper `lem:homog`(ii), vdW Prop 3.9 adapted)

For an arbitrary `P : SequentialProductOn (HermitianMat n ℂ)` satisfying S2
(`P.FirstArgContinuous`), this file proves `P.sp (t • a) b = t • P.sp a b` for
`t ∈ [0,1]` and effects `a, b` — the paper's `lem:homog`(ii).

The ladder mirrors van de Wetering's Proposition 3.9, with the σ-SEA normality
passage replaced by exactly one use of S2, as the paper's hypothesis accounting
prescribes:

1. `sp_comm_nat_smul` — if `y` is compatible with `x`, it is compatible with
   `j • x` (iterated S6b).
2. `sp_comm_rat_smul_self` — `a` is compatible with `q • a` for rational
   `q ∈ [0,1]` (the `1/k`-piece ladder, both directions).
3. `sp_comm_rat_one_smul` — `a` is compatible with `q • 1`: apply step 2 to the
   orthocomplement, S6a to flip `1 - a` back to `a`, and S6b to assemble
   `q•a + q•(1-a) = q•1`.
4. `sp_rat_one_smul_left` — the value: `P.sp (q•1) a = q • a`.
5. `sp_smul_one_left` — **the S2 limit**: `P.sp (t•1) b = t • b` for real
   `t ∈ [0,1]`, by a rational approximating sequence in the FIRST argument;
   this is the only point in `lem:homog` where S2 is used.
6. `sp_smul_left` — `lem:homog`(ii) itself, by S5 through the compatibility
   `a |' t•1` (both sides of which equal `t • a` by steps 4–5).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## Step 1: compatibility propagates to natural multiples (iterated S6b) -/

theorem sp_comm_nat_smul {x y : HermitianMat n ℂ} (hx : IsEffect x) (hy : IsEffect y)
    (hcomm : P.sp y x = P.sp x y) :
    ∀ j : ℕ, (j : ℝ) • x ≤ 1 → P.sp y ((j : ℝ) • x) = P.sp ((j : ℝ) • x) y := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_smul]
    rw [P.sp_zero_right hy, P.sp_zero_left hy]
  | succ j ih =>
    intro hle
    have hjx_le : (j : ℝ) • x ≤ ((j + 1 : ℕ) : ℝ) • x :=
      smul_le_smul_of_nonneg_right (by push_cast; linarith) hx.1
    have hj1 : (j : ℝ) • x ≤ 1 := le_trans hjx_le hle
    have hjx : IsEffect ((j : ℝ) • x) := ⟨smul_nonneg (by positivity) hx.1, hj1⟩
    have hsplit : ((j + 1 : ℕ) : ℝ) • x = (j : ℝ) • x + x := by
      push_cast
      rw [add_smul, one_smul]
    rw [hsplit] at hle ⊢
    exact P.compatible_add hy hjx hx hle (ih hj1) hcomm

/-! ## Step 2: an effect is compatible with its own rational multiples -/

private theorem rat_decomp {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    ∃ p k : ℕ, p ≤ k ∧ 0 < k ∧ (q : ℝ) = (p : ℝ) / (k : ℝ) := by
  refine ⟨q.num.toNat, q.den, ?_, q.den_pos, ?_⟩
  · have hden0 : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
    have hcast : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) from by
        exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0), Rat.cast_def]
    have h1 := hq1
    rw [hcast, div_le_one hden0] at h1
    exact_mod_cast h1
  · rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num : ℤ) : ℝ) from by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq0), Rat.cast_def]

theorem sp_comm_rat_smul_self {a : HermitianMat n ℂ} (ha : IsEffect a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp a ((q : ℝ) • a) = P.sp ((q : ℝ) • a) a := by
  obtain ⟨p, k, hpk, hk, hq⟩ := rat_decomp hq0 hq1
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set x : HermitianMat n ℂ := ((k : ℝ))⁻¹ • a with hxdef
  have hx0 : 0 ≤ x := smul_nonneg (by positivity) ha.1
  have hkx : (k : ℝ) • x = a := by
    rw [hxdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]
  have hx1 : x ≤ 1 := by
    calc x = (1 : ℝ) • x := (one_smul ℝ x).symm
      _ ≤ (k : ℝ) • x := smul_le_smul_of_nonneg_right (Nat.one_le_cast.mpr hk) hx0
      _ = a := hkx
      _ ≤ 1 := ha.2
  have hx : IsEffect x := ⟨hx0, hx1⟩
  have hkx_le : (k : ℝ) • x ≤ 1 := by rw [hkx]; exact ha.2
  have hpx_le : (p : ℝ) • x ≤ 1 := by
    calc (p : ℝ) • x ≤ (k : ℝ) • x := by
          apply smul_le_smul_of_nonneg_right _ hx0
          exact_mod_cast hpk
      _ = a := hkx
      _ ≤ 1 := ha.2
  -- x is compatible with a = k • x, hence a is compatible with x
  have hxa : P.sp x ((k : ℝ) • x) = P.sp ((k : ℝ) • x) x :=
    sp_comm_nat_smul P hx hx rfl k hkx_le
  rw [hkx] at hxa
  -- and then a is compatible with p • x = q • a
  have hax : P.sp a ((p : ℝ) • x) = P.sp ((p : ℝ) • x) a :=
    sp_comm_nat_smul P hx ha hxa.symm p hpx_le
  have hpx : (p : ℝ) • x = (q : ℝ) • a := by
    rw [hxdef, smul_smul, hq, div_eq_mul_inv]
  rw [hpx] at hax
  exact hax

/-! ## Step 3: an effect is compatible with rational multiples of the unit -/

theorem sp_comm_rat_one_smul {a : HermitianMat n ℂ} (ha : IsEffect a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp a ((q : ℝ) • 1) = P.sp ((q : ℝ) • 1) a := by
  have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hac : IsEffect (1 - a) := ⟨sub_nonneg.mpr ha.2, by simpa using sub_le_self 1 ha.1⟩
  have h1 : P.sp a ((q : ℝ) • a) = P.sp ((q : ℝ) • a) a :=
    sp_comm_rat_smul_self P ha hq0 hq1
  have h2 : P.sp (1 - a) ((q : ℝ) • (1 - a)) = P.sp ((q : ℝ) • (1 - a)) (1 - a) :=
    sp_comm_rat_smul_self P hac hq0 hq1
  have hqac : IsEffect ((q : ℝ) • (1 - a)) :=
    ⟨smul_nonneg hq0' hac.1,
      le_trans (smul_le_smul_of_nonneg_right hq1 hac.1) (by simpa using hac.2)⟩
  -- S6a: compatibility with 1 - (1 - a) = a
  have h3 := P.compatible_ortho hqac hac h2.symm
  rw [HermitianMat.ousUnit_eq_one, sub_sub_cancel] at h3
  -- S6b assembly
  have hqa : IsEffect ((q : ℝ) • a) :=
    ⟨smul_nonneg hq0' ha.1,
      le_trans (smul_le_smul_of_nonneg_right hq1 ha.1) (by simpa using ha.2)⟩
  have hsum : (q : ℝ) • a + (q : ℝ) • (1 - a) = (q : ℝ) • (1 : HermitianMat n ℂ) := by
    rw [← smul_add]
    congr 1
    abel
  have hle : (q : ℝ) • a + (q : ℝ) • (1 - a) ≤ 1 := by
    rw [hsum]
    calc (q : ℝ) • (1 : HermitianMat n ℂ) ≤ (1 : ℝ) • 1 :=
          smul_le_smul_of_nonneg_right hq1 zero_le_one
      _ = 1 := one_smul _ _
  have h6b := P.compatible_add ha hqa hqac hle h1 h3.symm
  rw [hsum] at h6b
  exact h6b

/-! ## Step 4: the rational value `(q•1) ◦' a = q • a` -/

theorem sp_rat_one_smul_left {a : HermitianMat n ℂ} (ha : IsEffect a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp ((q : ℝ) • 1) a = (q : ℝ) • a := by
  have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have h1eff : IsEffect (1 : HermitianMat n ℂ) := isEffect_unit
  have hu : P.sp a (1 : HermitianMat n ℂ) = a := P.sp_unit_right ha
  rw [← sp_comm_rat_one_smul P ha hq0 hq1,
    sp_smul_of_mem_unitInterval P ha h1eff hq0' hq1, hu]

/-! ## Step 5: the S2 limit — `(t•1) ◦' b = t • b` for real `t` -/

/-- **The single S2 use in `lem:homog`**: real-scalar multiples of the unit act by
scaling in the FIRST argument, by rational approximation and first-argument norm
continuity. -/
theorem sp_smul_one_left (hS2 : P.FirstArgContinuous) {b : HermitianMat n ℂ}
    (hb : IsEffect b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp (t • 1) b = t • b := by
  rcases eq_or_lt_of_le ht0 with h0 | h0pos
  · rw [← h0]
    simp only [zero_smul]
    exact P.sp_zero_left hb
  rcases eq_or_lt_of_le ht1 with h1 | h1lt
  · rw [h1]
    simp only [one_smul]
    exact P.sp_unit_left hb
  -- 0 < t < 1: approximate from below by rationals
  have hq : ∀ i : ℕ, ∃ q : ℚ, max 0 (t - 1 / (i + 1)) < (q : ℝ) ∧ (q : ℝ) < t := by
    intro i
    apply exists_rat_btwn
    apply max_lt h0pos
    have hpos : (0 : ℝ) < 1 / (i + 1) := by positivity
    linarith
  choose q hql hqu using hq
  have hq0 : ∀ i, (0 : ℚ) ≤ q i := by
    intro i
    have h0 : (0 : ℝ) ≤ (q i : ℝ) :=
      le_of_lt (lt_of_le_of_lt (le_max_left _ _) (hql i))
    exact_mod_cast h0
  have hqle1 : ∀ i, ((q i : ℝ)) ≤ 1 := fun i => le_of_lt (lt_of_lt_of_le (hqu i) ht1)
  -- the rational sequence tends to t
  have htend : Filter.Tendsto (fun i : ℕ => ((q i : ℝ))) Filter.atTop (nhds t) := by
    have hlow : Filter.Tendsto (fun i : ℕ => t - 1 / ((i : ℝ) + 1)) Filter.atTop (nhds t) := by
      have h10 : Filter.Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using Filter.Tendsto.const_sub t h10
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    · intro i
      exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (hql i))
    · intro i
      exact le_of_lt (hqu i)
  -- membership and convergence in the effect set
  have hmem : ∀ i : ℕ, ((q i : ℝ) • (1 : HermitianMat n ℂ)) ∈
      {x : HermitianMat n ℂ | IsEffect x} := by
    intro i
    refine ⟨smul_nonneg (by exact_mod_cast hq0 i) zero_le_one, ?_⟩
    calc (q i : ℝ) • (1 : HermitianMat n ℂ) ≤ (1 : ℝ) • 1 :=
          smul_le_smul_of_nonneg_right (hqle1 i) zero_le_one
      _ = 1 := one_smul _ _
  have hteff : IsEffect (t • (1 : HermitianMat n ℂ)) := by
    refine ⟨smul_nonneg ht0 zero_le_one, ?_⟩
    calc t • (1 : HermitianMat n ℂ) ≤ (1 : ℝ) • 1 :=
          smul_le_smul_of_nonneg_right ht1 zero_le_one
      _ = 1 := one_smul _ _
  have hsmultend : Filter.Tendsto (fun i : ℕ => (q i : ℝ) • (1 : HermitianMat n ℂ))
      Filter.atTop (nhds (t • (1 : HermitianMat n ℂ))) :=
    Filter.Tendsto.smul htend tendsto_const_nhds
  -- limit through S2
  have hlim1 : Filter.Tendsto (fun i : ℕ => P.sp ((q i : ℝ) • 1) b) Filter.atTop
      (nhds (P.sp (t • 1) b)) := by
    have hcw := (hS2 hb) (t • 1) hteff
    exact hcw.tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsmultend
        (Filter.Eventually.of_forall hmem))
  -- limit through the rational values
  have hlim2 : Filter.Tendsto (fun i : ℕ => P.sp ((q i : ℝ) • 1) b) Filter.atTop
      (nhds (t • b)) := by
    have heq : ∀ i : ℕ, P.sp ((q i : ℝ) • 1) b = (q i : ℝ) • b :=
      fun i => sp_rat_one_smul_left P hb (hq0 i) (hqle1 i)
    simp only [heq]
    exact htend.smul_const b
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## Step 6: `lem:homog`(ii) -/

/-- Every effect is compatible with real multiples of the unit. -/
theorem sp_comm_smul_one (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp a (t • 1) = P.sp (t • 1) a := by
  have h1eff : IsEffect (1 : HermitianMat n ℂ) := isEffect_unit
  have hu : P.sp a (1 : HermitianMat n ℂ) = a := P.sp_unit_right ha
  rw [sp_smul_one_left P hS2 ha ht0 ht1,
    sp_smul_of_mem_unitInterval P ha h1eff ht0 ht1, hu]

/-- **First-argument homogeneity** (paper `lem:homog`(ii), vdW Prop 3.9):
`(t•a) ◦' b = t • (a ◦' b)` for `t ∈ [0,1]` and effects `a, b`.  S5 through the
compatibility `a |' t•1`. -/
theorem sp_smul_left (hS2 : P.FirstArgContinuous) {a b : HermitianMat n ℂ}
    (ha : IsEffect a) (hb : IsEffect b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp (t • a) b = t • P.sp a b := by
  have ht1eff : IsEffect (t • (1 : HermitianMat n ℂ)) := by
    refine ⟨smul_nonneg ht0 zero_le_one, ?_⟩
    calc t • (1 : HermitianMat n ℂ) ≤ (1 : ℝ) • 1 :=
          smul_le_smul_of_nonneg_right ht1 zero_le_one
      _ = 1 := one_smul _ _
  have hcomp : P.sp a (t • 1) = P.sp (t • 1) a := sp_comm_smul_one P hS2 ha ht0 ht1
  have hassoc := P.sp_assoc_of_compatible ha ht1eff hb hcomp
  -- sp a (sp (t•1) b) = sp (sp a (t•1)) b
  rw [sp_smul_one_left P hS2 hb ht0 ht1,
    sp_smul_of_mem_unitInterval P ha hb ht0 ht1] at hassoc
  rw [show P.sp a (t • 1) = t • a from by
    have h1eff : IsEffect (1 : HermitianMat n ℂ) := isEffect_unit
    have hu : P.sp a (1 : HermitianMat n ℂ) = a := P.sp_unit_right ha
    rw [sp_smul_of_mem_unitInterval P ha h1eff ht0 ht1, hu]] at hassoc
  exact hassoc.symm

end Necessity
