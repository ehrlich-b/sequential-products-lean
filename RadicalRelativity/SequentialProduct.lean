/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.OrderUnitSpace
import Mathlib.Tactic.Abel
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.longLine false

/-!
# Sequential Product Spaces: exact S1--S7 boundary

A **sequential product space** is an order unit space equipped with a binary
operation `&` on the effect space [0,1]_V satisfying axioms S1--S7 from
van de Wetering (arXiv:1803.11139, Definition 2).

This file separates the algebraic core (S1 and S3--S7) from the topological
axiom S2 without weakening the public definition. `SequentialProductCore`
carries the algebraic core and effect closure. `FirstArgContinuous` is the
literal S2 predicate in the norm topology supplied by `OrderUnitSpace`.
`SequentialProduct` extends the core with that S2 proof; on the paper's
finite-dimensional simple EJAs, where the carried norm is equivalent to the
order-unit norm, it is exactly the seven-axiom paper interface.

The sequential product `a & b` encodes: "first test a, then test b" with
intermediate model update. This is the foundational structure from which
quantum mechanics is derived.

## Main definitions

* `SequentialProductCore` — algebraic core: S1, S3--S7, and effect closure
* `FirstArgContinuous` — exact S2, continuity of `a ↦ a & b` on effects
* `SequentialProduct` — exact paper interface, S1--S7
* `SequentialProduct.Compatible` — two effects commute under &
* `SequentialProduct.jordanProd` — the Jordan product `a ∘ b = ½(a & b + b & a)`

## References

* van de Wetering, Sequential product spaces are Jordan algebras, arXiv:1803.11139
-/

noncomputable section

open OrderUnitSpace

/-- The **algebraic core** of a sequential product space: an order unit space
    `(V, 𝟙)` equipped with a binary operation `sp : V → V → V` whose
    restriction to effects satisfies S1 and S3--S7.

    We define `sp` on all of V for convenience; the axioms only constrain
    behavior on the effect space `[0,1]_V`.  `sp_effect` is not an eighth axiom:
    it records the codomain of the paper's effect-level operation.  Paper S2 is
    the separate predicate `FirstArgContinuous` below. -/
class SequentialProductCore (V : Type*) extends OrderUnitSpace V where
  /-- The sequential product operation `a & b`. -/
  sp : V → V → V
  -- S1: Additivity in second argument: a & (b + c) = a & b + a & c when b + c ≤ 𝟙
  sp_add_right : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit → sp a (b + c) = sp a b + sp a c
  -- S3: Unitality: 𝟙 & a = a
  sp_unit_left : ∀ {a : V}, IsEffect a → sp ousUnit a = a
  -- S4: Symmetry of orthogonality: a & b = 0 → b & a = 0
  sp_zero_symm : ∀ {a b : V}, IsEffect a → IsEffect b → sp a b = 0 → sp b a = 0
  -- S5: Associativity of compatible effects: a|b → a & (b & c) = (a & b) & c
  sp_assoc_of_compatible : ∀ {a b c : V},
    IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a (sp b c) = sp (sp a b) c
  -- S6a: Compatibility with orthocomplement: a|b → a|(𝟙 - b)
  compatible_ortho : ∀ {a b : V}, IsEffect a → IsEffect b →
    sp a b = sp b a → sp a (ousUnit - b) = sp (ousUnit - b) a
  -- S6b: Additivity of compatibility: a|b ∧ a|c → a|(b + c) when b + c ≤ 𝟙
  compatible_add : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit →
    sp a b = sp b a → sp a c = sp c a →
    sp a (b + c) = sp (b + c) a
  -- S7: Multiplicativity of compatibility: a|b ∧ a|c → a|(b & c)
  compatible_sp : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a c = sp c a →
    sp a (sp b c) = sp (sp b c) a
  -- Effect closure: sp maps effects to effects
  sp_effect : ∀ {a b : V}, IsEffect a → IsEffect b → IsEffect (sp a b)

namespace SequentialProduct

open SequentialProductCore

variable {V : Type*} [SequentialProductCore V]

/-- Notation for the sequential product. -/
scoped infixl:70 " & " => SequentialProductCore.sp

/-- **Paper axiom S2, exactly.** For every effect `b`, the map
`a ↦ a & b` is continuous on the effect interval in the ambient topology.

The ambient topology is the norm topology carried by `OrderUnitSpace`
(`NormedAddCommGroup`/`NormedSpace ℝ`); on the paper's finite-dimensional simple
EJAs this is the order-unit norm, all norms there being equivalent.  Naming the
predicate prevents the former variable-swap bug, where second-variable
monotonicity was labelled "S2" even though Definition 2 requires first-variable
norm continuity. -/
def FirstArgContinuous : Prop :=
  ∀ ⦃b : V⦄, IsEffect b →
    ContinuousOn (fun a : V => a & b) {a : V | IsEffect a}

/-- The exact S1--S7 sequential-product interface of van de Wetering,
Definition 2. S1 and S3--S7 come from the inherited algebraic core; the field
is precisely first-variable norm continuity S2. -/
class _root_.SequentialProduct (V : Type*) extends SequentialProductCore V where
  sp_continuous_left : FirstArgContinuous (V := V)

/-- Unbundled spelling of the paper's S2 (first-variable continuity), useful in
theorem signatures and statement-fidelity audits; S1 and S3--S7 remain
typeclass-side in `SequentialProductCore`. -/
def PaperS2 : Prop := FirstArgContinuous (V := V)

/-- Two effects are compatible if they commute under &. -/
def Compatible (a b : V) : Prop :=
  IsEffect a ∧ IsEffect b ∧ (a & b) = (b & a)

/-- The Jordan product: `a ∘ᴶ b = ½ (a & b + b & a)`. -/
def jordanProd (a b : V) : V := (1/2 : ℝ) • ((a & b) + (b & a))

scoped infixl:70 " ∘ᴶ " => jordanProd

/-- A sharp effect under the sequential product: p & p = p. -/
def IsIdempotent (p : V) : Prop := IsEffect p ∧ (p & p) = p

/-- The Jordan product is commutative by construction. -/
theorem jordanProd_comm (a b : V) : a ∘ᴶ b = b ∘ᴶ a := by
  unfold jordanProd
  congr 1
  exact add_comm _ _

/-- For compatible effects, the Jordan product equals the sequential product. -/
theorem jordanProd_eq_sp_of_compatible {a b : V}
    (h : Compatible a b) : a ∘ᴶ b = a & b := by
  unfold jordanProd
  rw [h.2.2]
  rw [← two_smul ℝ (b & a)]
  rw [smul_smul]
  norm_num

/-- Sharp effects are compatible with themselves. -/
theorem idempotent_self_compatible {p : V} (hp : IsIdempotent p) :
    Compatible p p :=
  ⟨hp.1, hp.1, rfl⟩

/-- Zero is a right annihilator. -/
theorem sp_zero_right {a : V} (ha : IsEffect a) : a & (0 : V) = 0 := by
  have h0 : (0 : V) + 0 ≤ 𝟙 := by rw [add_zero]; exact ousUnit_nonneg
  have h := sp_add_right ha isEffect_zero isEffect_zero h0
  rw [add_zero] at h
  have key : a & 0 + a & 0 = a & 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel key

/-- Zero is a left annihilator. -/
theorem sp_zero_left {a : V} (ha : IsEffect a) : (0 : V) & a = 0 := by
  exact sp_zero_symm ha isEffect_zero (sp_zero_right ha)

/-- 𝟙 is a right identity for effects. -/
theorem sp_unit_right {a : V} (ha : IsEffect a) : a & (𝟙 : V) = a := by
  have hcompat : a & (0 : V) = (0 : V) & a := by
    rw [sp_zero_right ha, sp_zero_left ha]
  have h := compatible_ortho ha isEffect_zero hcompat
  rw [sub_zero] at h
  rw [h, sp_unit_left ha]

/-- The unit is compatible with everything. -/
theorem unit_compatible {a : V} (ha : IsEffect a) :
    Compatible (ousUnit) a :=
  ⟨isEffect_unit, ha, by rw [sp_unit_left ha, sp_unit_right ha]⟩

/-- The sequential product is nonneg on effects. -/
theorem sp_nonneg {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    (0 : V) ≤ a & b :=
  (sp_effect ha hb).1

/-- Right monotonicity is derived from S1 and effect closure; it is not paper
S2 and therefore is not an independent structure field. -/
theorem sp_mono_right {a b₁ b₂ : V} (ha : IsEffect a)
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂) (hle : b₁ ≤ b₂) :
    a & b₁ ≤ a & b₂ := by
  have hdiff : IsEffect (b₂ - b₁) :=
    ⟨sub_nonneg_of_le hle,
      le_trans (sub_le_self_of_nonneg hb₁.1) hb₂.2⟩
  have hsum : b₁ + (b₂ - b₁) ≤ (𝟙 : V) := by
    have heq : b₁ + (b₂ - b₁) = b₂ := by abel
    rw [heq]
    exact hb₂.2
  have hadd := sp_add_right ha hb₁ hdiff hsum
  have heq : b₁ + (b₂ - b₁) = b₂ := by abel
  rw [heq] at hadd
  rw [hadd]
  exact le_add_of_nonneg_right (sp_effect ha hdiff).1

/-- The sequential product is bounded by the left argument: a & b ≤ a. -/
theorem sp_le_left {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    a & b ≤ a := by
  have h := sp_mono_right ha hb isEffect_unit hb.2
  rw [sp_unit_right ha] at h
  exact h

/-- **Subtractive form of S1**: if `c ≤ b` (both effects), then
    `a & (b - c) = a & b - a & c`.

    Proof: from S1, a & b = a & (c + (b - c)) = a & c + a & (b - c),
    so a & (b - c) = a & b - a & c. -/
theorem sp_sub_right {a b c : V} (ha : IsEffect a) (hb : IsEffect b)
    (hc : IsEffect c) (hle : c ≤ b) (hbc_eff : IsEffect (b - c)) :
    a & (b - c) = a & b - a & c := by
  have hsum : c + (b - c) ≤ 𝟙 := by
    have heq : c + (b - c) = b := by abel
    rw [heq]; exact hb.2
  have h := sp_add_right ha hc hbc_eff hsum
  have heq : c + (b - c) = b := by abel
  rw [heq] at h
  -- h : a & b = a & c + a & (b - c)
  -- goal : a & (b - c) = a & b - a & c
  have : a & b - a & c = a & (b - c) := by
    rw [h]; abel
  exact this.symm

end SequentialProduct

/-! ## Sequential products ON a fixed order-unit space

The necessity direction quantifies over the unknown product while the order-unit
structure stays THE structure of the concrete carrier (the paper fixes the EJA
and classifies operations on its effects).  An instance-quantified
`[SequentialProductCore V]` cannot express this: it carries its own
`toOrderUnitSpace` parent, which the elaborator treats as unrelated to the
carrier's canonical instance, so none of the carrier's order/norm/spectral
lemmas apply to the effects it speaks about.  `SequentialProductOn` is the
carrier-pinned formulation: the same eight fields, elaborated over the *ambient*
`[OrderUnitSpace V]`. -/

/-- An S1, S3–S7 sequential product structure **on** a fixed order-unit space:
the fields of `SequentialProductCore`, with the order-unit parent pinned to the
ambient instance rather than bundled.  Paper S2 for a `P : SequentialProductOn V`
is the unbundled `P.FirstArgContinuous` below. -/
structure SequentialProductOn (V : Type*) [OrderUnitSpace V] where
  /-- The sequential product operation `a & b`. -/
  sp : V → V → V
  sp_add_right : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit → sp a (b + c) = sp a b + sp a c
  sp_unit_left : ∀ {a : V}, IsEffect a → sp ousUnit a = a
  sp_zero_symm : ∀ {a b : V}, IsEffect a → IsEffect b → sp a b = 0 → sp b a = 0
  sp_assoc_of_compatible : ∀ {a b c : V},
    IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a (sp b c) = sp (sp a b) c
  compatible_ortho : ∀ {a b : V}, IsEffect a → IsEffect b →
    sp a b = sp b a → sp a (ousUnit - b) = sp (ousUnit - b) a
  compatible_add : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    b + c ≤ ousUnit →
    sp a b = sp b a → sp a c = sp c a →
    sp a (b + c) = sp (b + c) a
  compatible_sp : ∀ {a b c : V}, IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a c = sp c a →
    sp a (sp b c) = sp (sp b c) a
  sp_effect : ∀ {a b : V}, IsEffect a → IsEffect b → IsEffect (sp a b)

namespace SequentialProductOn

variable {V : Type*} [OrderUnitSpace V]

/-- Repackage as a bundled `SequentialProductCore` whose parent is *definitionally*
the ambient instance — the bridge that lets the derived lemma layer of
`SequentialProduct` apply to a pinned product. -/
def toCore (P : SequentialProductOn V) : SequentialProductCore V :=
  { ‹OrderUnitSpace V› with
    sp := P.sp
    sp_add_right := P.sp_add_right
    sp_unit_left := P.sp_unit_left
    sp_zero_symm := P.sp_zero_symm
    sp_assoc_of_compatible := P.sp_assoc_of_compatible
    compatible_ortho := P.compatible_ortho
    compatible_add := P.compatible_add
    compatible_sp := P.compatible_sp
    sp_effect := P.sp_effect }

/-- Paper S2 for a pinned product: first-argument continuity on effects in the
carrier's norm topology. -/
def FirstArgContinuous (P : SequentialProductOn V) : Prop :=
  ∀ ⦃b : V⦄, IsEffect b → ContinuousOn (fun a : V => P.sp a b) {a : V | IsEffect a}

variable (P : SequentialProductOn V)

/-- A bundled `SequentialProductCore` on any type is a pinned product over its own
parent order-unit structure (the converse packaging). -/
def _root_.SequentialProductCore.toSequentialProductOn
    (W : Type*) [inst : SequentialProductCore W] :
    @SequentialProductOn W inst.toOrderUnitSpace :=
  { sp := SequentialProductCore.sp
    sp_add_right := SequentialProductCore.sp_add_right
    sp_unit_left := SequentialProductCore.sp_unit_left
    sp_zero_symm := SequentialProductCore.sp_zero_symm
    sp_assoc_of_compatible := SequentialProductCore.sp_assoc_of_compatible
    compatible_ortho := SequentialProductCore.compatible_ortho
    compatible_add := SequentialProductCore.compatible_add
    compatible_sp := SequentialProductCore.compatible_sp
    sp_effect := SequentialProductCore.sp_effect }

/- Derived lemmas, transported from the `SequentialProduct` layer through
`toCore` (whose parent is definitionally the ambient instance). -/

theorem sp_zero_right {a : V} (ha : IsEffect a) : P.sp a 0 = 0 :=
  letI := P.toCore
  SequentialProduct.sp_zero_right ha

theorem sp_zero_left {a : V} (ha : IsEffect a) : P.sp 0 a = 0 :=
  letI := P.toCore
  SequentialProduct.sp_zero_left ha

theorem sp_unit_right {a : V} (ha : IsEffect a) : P.sp a ousUnit = a :=
  letI := P.toCore
  SequentialProduct.sp_unit_right ha

theorem sp_nonneg {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    (0 : V) ≤ P.sp a b :=
  letI := P.toCore
  SequentialProduct.sp_nonneg ha hb

theorem sp_mono_right {a b₁ b₂ : V} (ha : IsEffect a)
    (hb₁ : IsEffect b₁) (hb₂ : IsEffect b₂) (hle : b₁ ≤ b₂) :
    P.sp a b₁ ≤ P.sp a b₂ :=
  letI := P.toCore
  SequentialProduct.sp_mono_right ha hb₁ hb₂ hle

theorem sp_le_left {a b : V} (ha : IsEffect a) (hb : IsEffect b) :
    P.sp a b ≤ a :=
  letI := P.toCore
  SequentialProduct.sp_le_left ha hb

theorem sp_sub_right {a b c : V} (ha : IsEffect a) (hb : IsEffect b)
    (hc : IsEffect c) (hle : c ≤ b) (hbc_eff : IsEffect (b - c)) :
    P.sp a (b - c) = P.sp a b - P.sp a c :=
  letI := P.toCore
  SequentialProduct.sp_sub_right ha hb hc hle hbc_eff

end SequentialProductOn

/-! ## The abstract homogeneity ladder (`lem:homog`, second argument)

Ported to abstract order-unit-space generality 2026-08-08 (ARC-6 rung 6.3).  The concrete
versions in `Necessity/LeftMultiplication.lean` are unchanged; these are the same six steps
with the carrier replaced by an arbitrary `OrderUnitSpace` and the carrier's Archimedean
property replaced by the explicit hypothesis `OrderUnitSpace.IsArchimedean`.

This discharges the obstruction recorded for rung 5.1: the ladder's last step is an
ε-squeeze that *is* the Archimedean property, which the class does not carry, so the
generalization was not a change of variable block.  With Archimedean supplied as a `Prop` it
goes through unchanged otherwise — the ladder never used anything else about matrices. -/

namespace SequentialProductOn

open OrderUnitSpace

variable {V : Type*} [OrderUnitSpace V] (P : SequentialProductOn V)

/-! ## Step 1: ℕ- and ℚ-homogeneity in the second argument, from S1 alone -/

theorem sp_natSmul_right {a c : V} (ha : IsEffect a) (hc : IsEffect c) :
    ∀ j : ℕ, (j : ℝ) • c ≤ (𝟙 : V) →
      P.sp a ((j : ℝ) • c) = (j : ℝ) • P.sp a c := by
  intro j
  induction j with
  | zero => intro _; simp [P.sp_zero_right ha]
  | succ j ih =>
    intro hle
    have hjc_le : (j : ℝ) • c ≤ ((j + 1 : ℕ) : ℝ) • c :=
      smul_le_smul_of_le_of_nonneg (by push_cast; linarith) hc.1
    have hj1 : (j : ℝ) • c ≤ (𝟙 : V) := le_trans hjc_le hle
    have hjc : IsEffect ((j : ℝ) • c) := ⟨smul_nonneg' (by positivity) hc.1, hj1⟩
    have hsplit : ((j + 1 : ℕ) : ℝ) • c = (j : ℝ) • c + c := by
      push_cast; rw [add_smul, one_smul]
    rw [hsplit] at hle
    rw [hsplit, P.sp_add_right ha hjc hc hle, ih hj1]
    push_cast
    rw [add_smul, one_smul]

theorem sp_divNat_smul_right {a b : V} (ha : IsEffect a) (hb : IsEffect b)
    {p k : ℕ} (hpk : p ≤ k) (hk : 0 < k) :
    P.sp a (((p : ℝ) / (k : ℝ)) • b) = ((p : ℝ) / (k : ℝ)) • P.sp a b := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set c : V := ((k : ℝ))⁻¹ • b with hcdef
  have hc0 : (0 : V) ≤ c := smul_nonneg' (by positivity) hb.1
  have hkc : (k : ℝ) • c = b := by
    rw [hcdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]
  have hc1 : c ≤ (𝟙 : V) := by
    calc c = (1 : ℝ) • c := (one_smul ℝ c).symm
      _ ≤ (k : ℝ) • c := smul_le_smul_of_le_of_nonneg (Nat.one_le_cast.mpr hk) hc0
      _ = b := hkc
      _ ≤ 𝟙 := hb.2
  have hc : IsEffect c := ⟨hc0, hc1⟩
  have hpc_le : (p : ℝ) • c ≤ (𝟙 : V) := by
    calc (p : ℝ) • c ≤ (k : ℝ) • c :=
          smul_le_smul_of_le_of_nonneg (by exact_mod_cast hpk) hc0
      _ = b := hkc
      _ ≤ 𝟙 := hb.2
  have hkc_le : (k : ℝ) • c ≤ (𝟙 : V) := by rw [hkc]; exact hb.2
  have hp := sp_natSmul_right P ha hc p hpc_le
  have hkk := sp_natSmul_right P ha hc k hkc_le
  rw [hkc] at hkk
  have hdiv : ((p : ℝ) / (k : ℝ)) • b = (p : ℝ) • c := by
    rw [hcdef, smul_smul, div_eq_mul_inv]
  rw [hdiv, hp, hkk, smul_smul]
  congr 1
  field_simp

theorem sp_ratSmul_right {a b : V} (ha : IsEffect a) (hb : IsEffect b)
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
  exact sp_divNat_smul_right P ha hb hpk hden

/-! ## Step 2: real homogeneity in the second argument, by the Archimedean squeeze -/

/-- **Real scalar homogeneity in the second argument** for `t ∈ [0,1]`, at abstract
order-unit-space generality, from S1 plus the Archimedean property. -/
theorem sp_smul_right_of_unitInterval (harch : IsArchimedean V) {a b : V}
    (ha : IsEffect a) (hb : IsEffect b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp a (t • b) = t • P.sp a b := by
  set y := P.sp a b with hy
  have hy_eff : IsEffect y := P.sp_effect ha hb
  have htb : IsEffect (t • b) := isEffect_smul ht0 ht1 hb
  set z := P.sp a (t • b) with hz
  have hupper : ∀ ε : ℝ, 0 < ε → z - t • y ≤ ε • (𝟙 : V) := by
    intro ε hε
    rcases lt_or_ge t 1 with htlt | htge
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min htlt (lt_add_of_pos_right t hε))
      have hq0 : (0 : ℚ) ≤ q := by
        have h0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt ht0 hq1)
        exact_mod_cast h0
      have hqle1 : (q : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))
      have hqb : IsEffect ((q : ℝ) • b) :=
        isEffect_smul (by exact_mod_cast hq0) hqle1 hb
      have hmono : z ≤ (q : ℝ) • y := by
        rw [hz, hy, ← sp_ratSmul_right P ha hb hq0 hqle1]
        exact P.sp_mono_right ha htb hqb
          (smul_le_smul_of_le_of_nonneg (le_of_lt hq1) hb.1)
      calc z - t • y ≤ (q : ℝ) • y - t • y := sub_le_sub_right' hmono _
        _ = ((q : ℝ) - t) • y := (sub_smul _ _ _).symm
        _ ≤ ((q : ℝ) - t) • (𝟙 : V) :=
            smul_nonneg_mono _ (by linarith) hy_eff.2
        _ ≤ ε • (𝟙 : V) := by
            refine smul_le_smul_of_le_of_nonneg ?_ ousUnit_nonneg
            have h2 := lt_of_lt_of_le hq2 (min_le_right _ _)
            linarith
    · have ht : t = 1 := le_antisymm ht1 htge
      subst ht
      have hzy : z = y := by rw [hz, hy, one_smul]
      rw [hzy, one_smul, sub_self]
      exact smul_nonneg' (le_of_lt hε) ousUnit_nonneg
  have hlower : ∀ ε : ℝ, 0 < ε → t • y - z ≤ ε • (𝟙 : V) := by
    intro ε hε
    rcases eq_or_lt_of_le ht0 with ht | htpos
    · rw [hz, ← ht]
      simp only [zero_smul]
      rw [P.sp_zero_right ha, sub_zero]
      exact smul_nonneg' (le_of_lt hε) ousUnit_nonneg
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self t (lt_min htpos hε))
      have hq0 : (0 : ℚ) ≤ q := by
        have h0 : (0 : ℝ) < (q : ℝ) := by
          have hmin : min t ε ≤ t := min_le_left _ _
          linarith
        exact_mod_cast le_of_lt h0
      have hqle1 : (q : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hq2 ht1)
      have hqb : IsEffect ((q : ℝ) • b) :=
        isEffect_smul (by exact_mod_cast hq0) hqle1 hb
      have hmono : (q : ℝ) • y ≤ z := by
        rw [hz, hy, ← sp_ratSmul_right P ha hb hq0 hqle1]
        exact P.sp_mono_right ha hqb htb
          (smul_le_smul_of_le_of_nonneg (le_of_lt hq2) hb.1)
      calc t • y - z ≤ t • y - (q : ℝ) • y := sub_le_sub_left' hmono _
        _ = (t - (q : ℝ)) • y := (sub_smul _ _ _).symm
        _ ≤ (t - (q : ℝ)) • (𝟙 : V) :=
            smul_nonneg_mono _ (by linarith) hy_eff.2
        _ ≤ ε • (𝟙 : V) := by
            refine smul_le_smul_of_le_of_nonneg ?_ ousUnit_nonneg
            have hmin : min t ε ≤ ε := min_le_right _ _
            linarith
  have h1 : z - t • y ≤ 0 := harch _ hupper
  have h2 : t • y - z ≤ 0 := harch _ hlower
  exact le_antisymm (le_of_sub_nonpos h1) (le_of_sub_nonpos h2)

/-! ## Step 3: compatibility propagates to natural multiples (iterated S6b) -/

theorem sp_comm_natSmul {x y : V} (hx : IsEffect x) (hy : IsEffect y)
    (hcomm : P.sp y x = P.sp x y) :
    ∀ j : ℕ, (j : ℝ) • x ≤ (𝟙 : V) →
      P.sp y ((j : ℝ) • x) = P.sp ((j : ℝ) • x) y := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.cast_zero, zero_smul]
    rw [P.sp_zero_right hy, P.sp_zero_left hy]
  | succ j ih =>
    intro hle
    have hjx_le : (j : ℝ) • x ≤ ((j + 1 : ℕ) : ℝ) • x :=
      smul_le_smul_of_le_of_nonneg (by push_cast; linarith) hx.1
    have hj1 : (j : ℝ) • x ≤ (𝟙 : V) := le_trans hjx_le hle
    have hjx : IsEffect ((j : ℝ) • x) := ⟨smul_nonneg' (by positivity) hx.1, hj1⟩
    have hsplit : ((j + 1 : ℕ) : ℝ) • x = (j : ℝ) • x + x := by
      push_cast
      rw [add_smul, one_smul]
    rw [hsplit] at hle ⊢
    exact P.compatible_add hy hjx hx hle (ih hj1) hcomm

/-! ## Step 4: an effect is compatible with its own rational multiples -/

private theorem ratDecomp {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
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

theorem sp_comm_ratSmul_self {a : V} (ha : IsEffect a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp a ((q : ℝ) • a) = P.sp ((q : ℝ) • a) a := by
  obtain ⟨p, k, hpk, hk, hq⟩ := ratDecomp hq0 hq1
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set x : V := ((k : ℝ))⁻¹ • a with hxdef
  have hx0 : (0 : V) ≤ x := smul_nonneg' (by positivity) ha.1
  have hkx : (k : ℝ) • x = a := by
    rw [hxdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]
  have hx1 : x ≤ (𝟙 : V) := by
    calc x = (1 : ℝ) • x := (one_smul ℝ x).symm
      _ ≤ (k : ℝ) • x := smul_le_smul_of_le_of_nonneg (Nat.one_le_cast.mpr hk) hx0
      _ = a := hkx
      _ ≤ 𝟙 := ha.2
  have hx : IsEffect x := ⟨hx0, hx1⟩
  have hkx_le : (k : ℝ) • x ≤ (𝟙 : V) := by rw [hkx]; exact ha.2
  have hpx_le : (p : ℝ) • x ≤ (𝟙 : V) := by
    calc (p : ℝ) • x ≤ (k : ℝ) • x :=
          smul_le_smul_of_le_of_nonneg (by exact_mod_cast hpk) hx0
      _ = a := hkx
      _ ≤ 𝟙 := ha.2
  have hxa : P.sp x ((k : ℝ) • x) = P.sp ((k : ℝ) • x) x :=
    sp_comm_natSmul P hx hx rfl k hkx_le
  rw [hkx] at hxa
  have hax : P.sp a ((p : ℝ) • x) = P.sp ((p : ℝ) • x) a :=
    sp_comm_natSmul P hx ha hxa.symm p hpx_le
  have hpx : (p : ℝ) • x = (q : ℝ) • a := by
    rw [hxdef, smul_smul, hq, div_eq_mul_inv]
  rw [hpx] at hax
  exact hax

/-! ## Step 5: an effect is compatible with rational multiples of the unit -/

theorem sp_comm_ratOneSmul {a : V} (ha : IsEffect a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp a ((q : ℝ) • (𝟙 : V)) = P.sp ((q : ℝ) • (𝟙 : V)) a := by
  have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hac : IsEffect ((𝟙 : V) - a) := ha.ortho
  have h1 : P.sp a ((q : ℝ) • a) = P.sp ((q : ℝ) • a) a :=
    sp_comm_ratSmul_self P ha hq0 hq1
  have h2 : P.sp ((𝟙 : V) - a) ((q : ℝ) • ((𝟙 : V) - a))
      = P.sp ((q : ℝ) • ((𝟙 : V) - a)) ((𝟙 : V) - a) :=
    sp_comm_ratSmul_self P hac hq0 hq1
  have hqac : IsEffect ((q : ℝ) • ((𝟙 : V) - a)) := isEffect_smul hq0' hq1 hac
  have h3 := P.compatible_ortho hqac hac h2.symm
  rw [sub_sub_cancel] at h3
  have hqa : IsEffect ((q : ℝ) • a) := isEffect_smul hq0' hq1 ha
  have hsum : (q : ℝ) • a + (q : ℝ) • ((𝟙 : V) - a) = (q : ℝ) • (𝟙 : V) := by
    rw [← smul_add]
    congr 1
    abel
  have hle : (q : ℝ) • a + (q : ℝ) • ((𝟙 : V) - a) ≤ (𝟙 : V) := by
    rw [hsum]
    exact (isEffect_smul_unit hq0' hq1).2
  have h6b := P.compatible_add ha hqa hqac hle h1 h3.symm
  rw [hsum] at h6b
  exact h6b

/-! ## Step 6: the rational value `(q•𝟙) ◦' a = q • a` -/

theorem sp_ratOneSmul_left (harch : IsArchimedean V) {a : V} (ha : IsEffect a)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : (q : ℝ) ≤ 1) :
    P.sp ((q : ℝ) • (𝟙 : V)) a = (q : ℝ) • a := by
  have hq0' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
  have hu : P.sp a (𝟙 : V) = a := P.sp_unit_right ha
  rw [← sp_comm_ratOneSmul P ha hq0 hq1,
    sp_smul_right_of_unitInterval P harch ha isEffect_unit hq0' hq1, hu]

/-! ## Step 7: the S2 limit — `(t•𝟙) ◦' b = t • b` for real `t` -/

/-- **The single S2 use in `lem:homog`**: real-scalar multiples of the unit act by scaling
in the FIRST argument, by rational approximation and first-argument norm continuity. -/
theorem sp_smulOne_left (harch : IsArchimedean V) (hS2 : P.FirstArgContinuous) {b : V}
    (hb : IsEffect b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp (t • (𝟙 : V)) b = t • b := by
  rcases eq_or_lt_of_le ht0 with h0 | h0pos
  · rw [← h0]
    simp only [zero_smul]
    exact P.sp_zero_left hb
  rcases eq_or_lt_of_le ht1 with h1 | h1lt
  · rw [h1]
    simp only [one_smul]
    exact P.sp_unit_left hb
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
  have hmem : ∀ i : ℕ, ((q i : ℝ) • (𝟙 : V)) ∈ {x : V | IsEffect x} := by
    intro i
    exact isEffect_smul_unit (by exact_mod_cast hq0 i) (hqle1 i)
  have hteff : IsEffect (t • (𝟙 : V)) := isEffect_smul_unit ht0 ht1
  have hsmultend : Filter.Tendsto (fun i : ℕ => (q i : ℝ) • (𝟙 : V))
      Filter.atTop (nhds (t • (𝟙 : V))) :=
    Filter.Tendsto.smul htend tendsto_const_nhds
  have hlim1 : Filter.Tendsto (fun i : ℕ => P.sp ((q i : ℝ) • (𝟙 : V)) b) Filter.atTop
      (nhds (P.sp (t • (𝟙 : V)) b)) := by
    have hcw := (hS2 hb) (t • 𝟙) hteff
    exact hcw.tendsto.comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsmultend
        (Filter.Eventually.of_forall hmem))
  have hlim2 : Filter.Tendsto (fun i : ℕ => P.sp ((q i : ℝ) • (𝟙 : V)) b) Filter.atTop
      (nhds (t • b)) := by
    have heq : ∀ i : ℕ, P.sp ((q i : ℝ) • (𝟙 : V)) b = (q i : ℝ) • b :=
      fun i => sp_ratOneSmul_left P harch hb (hq0 i) (hqle1 i)
    simp only [heq]
    exact htend.smul_const b
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## Step 8: `lem:homog`(ii) at abstract generality -/

/-- Every effect is compatible with real multiples of the unit. -/
theorem sp_comm_smulOne (harch : IsArchimedean V) (hS2 : P.FirstArgContinuous) {a : V}
    (ha : IsEffect a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp a (t • (𝟙 : V)) = P.sp (t • (𝟙 : V)) a := by
  have hu : P.sp a (𝟙 : V) = a := P.sp_unit_right ha
  rw [sp_smulOne_left P harch hS2 ha ht0 ht1,
    sp_smul_right_of_unitInterval P harch ha isEffect_unit ht0 ht1, hu]

/-- **`lem:homog`(ii) — first-argument homogeneity — at abstract order-unit-space
generality**: `(t•a) ◦' b = t • (a ◦' b)` for `t ∈ [0,1]` and effects `a, b`.

Carries exactly S1–S7, the article's own S2, and the Archimedean property that is part of
the definition of its order unit space.  Nothing about matrices enters, so this covers the
article's statement, whose ambient `J` is a Euclidean Jordan algebra and hence in particular
an order unit space.  The article itself attributes this clause to van de Wetering's
Proposition 3.9; here it is proved from the axioms. -/
theorem sp_smul_left (harch : IsArchimedean V) (hS2 : P.FirstArgContinuous) {a b : V}
    (ha : IsEffect a) (hb : IsEffect b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P.sp (t • a) b = t • P.sp a b := by
  have ht1eff : IsEffect (t • (𝟙 : V)) := isEffect_smul_unit ht0 ht1
  have hcomp : P.sp a (t • 𝟙) = P.sp (t • 𝟙) a := sp_comm_smulOne P harch hS2 ha ht0 ht1
  have hassoc := P.sp_assoc_of_compatible ha ht1eff hb hcomp
  rw [sp_smulOne_left P harch hS2 hb ht0 ht1,
    sp_smul_right_of_unitInterval P harch ha hb ht0 ht1] at hassoc
  rw [show P.sp a (t • (𝟙 : V)) = t • a from by
    have hu : P.sp a (𝟙 : V) = a := P.sp_unit_right ha
    rw [sp_smul_right_of_unitInterval P harch ha isEffect_unit ht0 ht1, hu]] at hassoc
  exact hassoc.symm

end SequentialProductOn
