/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit
import RadicalRelativity.Hermitian.RCLikeGeneral
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Matrix.Mul

set_option linter.style.longLine false

/-!
# Extreme points of the effect interval are projections  (LEDGER 1.1 / M3 bridge 1)

For the concrete carrier `HermitianMat n 𝕜` (Loewner order), this file proves that
the extreme points of the effect interval `[0,1]` are exactly the projections
`p ^ 2 = p`.  Mathlib has `Set.extremePoints`, `IsStarProjection`, and the
operator interval, but nothing joining them (inventory 2026-08-04); this is the
from-scratch join.

* `HermitianMat.IsProjection` — `p ^ 2 = p` (Hermitian idempotent).
* `IsProjection.nonneg` / `IsProjection.le_one` — projections are effects, by pure
  algebra (`p = p²` and `1 - p = (1-p)²` are squares), uniform in `RCLike 𝕜`.
* `IsProjection.mem_extremePoints` — projections are extreme, uniform in `𝕜`: the
  kernel/range pinch needs only quadratic-form positivity, no spectral theory.
* `isProjection_of_mem_extremePoints` — extreme effects are projections, over any `RCLike` field:
  fully CFC-native — perturb `a` by `± min(x, 1-x)` applied through the functional
  calculus; extremeness kills the perturbation, forcing the spectrum into `{0,1}`.
* `mem_extremePoints_iff_isProjection`, `extremePoints_unitInterval` — the join.

Downstream (M3, LEDGER 3.1 Route A bridge 1): a unital linear order-automorphism
preserves the effect interval and convex structure, hence maps extreme effects to
extreme effects; by this file it therefore maps projections to projections.
-/

noncomputable section

open ComplexOrder
-- NB: this open must precede `namespace HermitianMat`: the vendored island declares
-- names under `HermitianMat.Matrix`, which would shadow the root `Matrix` namespace
-- and silently deactivate the scoped `*ᵥ` notation (LEDGER H6).
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- A **projection** in `H_n(𝕜)`: a Hermitian idempotent, `p ^ 2 = p`. -/
def IsProjection (p : HermitianMat n 𝕜) : Prop := p ^ 2 = p

theorem isProjection_iff_mat_mul_self {p : HermitianMat n 𝕜} :
    p.IsProjection ↔ p.mat * p.mat = p.mat := by
  unfold IsProjection
  rw [HermitianMat.ext_iff, mat_pow, pow_two]

/-- Projections are positive semidefinite: `p = p²` is a square. -/
theorem IsProjection.nonneg {p : HermitianMat n 𝕜} (hp : p.IsProjection) : 0 ≤ p :=
  hp ▸ sq_nonneg (A := p)

/-- The orthocomplement of a projection is a projection. -/
theorem IsProjection.one_sub {p : HermitianMat n 𝕜} (hp : p.IsProjection) :
    (1 - p).IsProjection := by
  have hpp := isProjection_iff_mat_mul_self.mp hp
  simp only [isProjection_iff_mat_mul_self, mat_sub, mat_one, sub_mul, mul_sub,
    one_mul, mul_one, hpp]
  abel

/-- Projections are dominated by the unit: `1 - p = (1-p)²` is a square. -/
theorem IsProjection.le_one {p : HermitianMat n 𝕜} (hp : p.IsProjection) : p ≤ 1 := by
  have h := sq_nonneg (A := 1 - p)
  have h2 : ((1 - p) ^ 2 : HermitianMat n 𝕜) = 1 - p := hp.one_sub
  rw [h2] at h
  exact sub_nonneg.mp h

/-- Projections are effects. -/
theorem IsProjection.isEffect {p : HermitianMat n 𝕜} (hp : p.IsProjection) :
    0 ≤ p ∧ p ≤ 1 :=
  ⟨hp.nonneg, hp.le_one⟩

/-- **Pinch core**: if `t • b + s • c = p` with `b, c ⪰ 0` and `t, s > 0`, then the
kernel of `p` is contained in the kernel of `b` — quadratic forms only, no spectral
machinery. -/
private theorem mulVec_eq_zero_of_convex_decomp {p b c : HermitianMat n 𝕜}
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) {t s : ℝ} (ht : 0 < t) (hs : 0 < s)
    (h : t • b + s • c = p) {v : n → 𝕜} (hv : p.mat *ᵥ v = 0) :
    b.mat *ᵥ v = 0 := by
  have hmat : p.mat = t • b.mat + s • c.mat := by
    rw [← h, mat_add, mat_smul, mat_smul]
  have hqf : (t : 𝕜) * (star v ⬝ᵥ b.mat *ᵥ v) + (s : 𝕜) * (star v ⬝ᵥ c.mat *ᵥ v) = 0 := by
    have h0 : star v ⬝ᵥ p.mat *ᵥ v = 0 := by rw [hv, dotProduct_zero]
    rw [hmat, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul, RCLike.real_smul_eq_coe_mul,
      RCLike.real_smul_eq_coe_mul] at h0
    exact h0
  have h1 : (0 : 𝕜) ≤ (t : 𝕜) * (star v ⬝ᵥ b.mat *ᵥ v) :=
    mul_nonneg (by exact_mod_cast ht.le) (inner_mulVec_nonneg hb0 v)
  have h2 : (0 : 𝕜) ≤ (s : 𝕜) * (star v ⬝ᵥ c.mat *ᵥ v) :=
    mul_nonneg (by exact_mod_cast hs.le) (inner_mulVec_nonneg hc0 v)
  have htb : (t : 𝕜) * (star v ⬝ᵥ b.mat *ᵥ v) = 0 :=
    ((add_eq_zero_iff_of_nonneg h1 h2).mp hqf).1
  have hqfb : star v ⬝ᵥ b.mat *ᵥ v = 0 := by
    rcases mul_eq_zero.mp htb with h' | h'
    · exact absurd h' (by exact_mod_cast ht.ne')
    · exact h'
  exact ((zero_le_iff.mp hb0).dotProduct_mulVec_zero_iff v).mp hqfb

/-- One side of the extreme-point property: an effect appearing in a proper convex
decomposition of a projection equals that projection. -/
private theorem side_eq_of_convex_decomp {p b c : HermitianMat n 𝕜}
    (hp : p.IsProjection) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hts : t + s = 1)
    (h : t • b + s • c = p) : b = p := by
  have hpp := isProjection_iff_mat_mul_self.mp hp
  -- kernel containment for (b, p)
  have hker : ∀ v : n → 𝕜, p.mat *ᵥ v = 0 → b.mat *ᵥ v = 0 := fun v hv =>
    mulVec_eq_zero_of_convex_decomp hb0 hc0 ht hs h hv
  -- kernel containment for the orthocomplements (1-b, 1-p)
  have hcombo' : t • (1 - b) + s • (1 - c) = 1 - p := by
    rw [smul_sub, smul_sub, ← h]
    have h1 : t • (1 : HermitianMat n 𝕜) + s • 1 = 1 := by
      rw [← add_smul, hts, one_smul]
    have h2 : t • (1 : HermitianMat n 𝕜) - t • b + (s • 1 - s • c) =
        (t • 1 + s • 1) - (t • b + s • c) := by abel
    rw [h2, h1]
  have hker' : ∀ v : n → 𝕜, (1 - p).mat *ᵥ v = 0 → (1 - b).mat *ᵥ v = 0 := fun v hv =>
    mulVec_eq_zero_of_convex_decomp (sub_nonneg.mpr hb1) (sub_nonneg.mpr hc1)
      ht hs hcombo' hv
  -- b agrees with p on range p and on ker p, hence everywhere
  apply HermitianMat.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  have hfix : b.mat *ᵥ (p.mat *ᵥ Pi.single j 1) = p.mat *ᵥ Pi.single j 1 := by
    have h1 : (1 - p).mat *ᵥ (p.mat *ᵥ Pi.single j 1) = 0 := by
      rw [mat_sub, mat_one, Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, hpp, sub_self]
    have h2 := hker' _ h1
    rw [mat_sub, mat_one, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
    exact h2.symm
  have hkerpart : b.mat *ᵥ (Pi.single j 1 - p.mat *ᵥ Pi.single j 1) = 0 := by
    apply hker
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hpp, sub_self]
  calc b.mat *ᵥ Pi.single j 1
      = b.mat *ᵥ (p.mat *ᵥ Pi.single j 1) +
        b.mat *ᵥ (Pi.single j 1 - p.mat *ᵥ Pi.single j 1) := by
        rw [← Matrix.mulVec_add]
        congr 1
        abel
    _ = p.mat *ᵥ Pi.single j 1 := by rw [hfix, hkerpart, add_zero]

/-- **Projections are extreme points** of the effect interval, uniformly in
`RCLike 𝕜`: the argument is a kernel/range pinch via quadratic-form positivity. -/
theorem IsProjection.mem_extremePoints {p : HermitianMat n 𝕜} (hp : p.IsProjection) :
    p ∈ Set.extremePoints ℝ {x : HermitianMat n 𝕜 | 0 ≤ x ∧ x ≤ 1} := by
  rw [_root_.mem_extremePoints]
  refine ⟨⟨hp.nonneg, hp.le_one⟩, ?_⟩
  rintro b ⟨hb0, hb1⟩ c ⟨hc0, hc1⟩ ⟨t, s, ht, hs, hts, habc⟩
  refine ⟨side_eq_of_convex_decomp hp hb0 hb1 hc0 hc1 ht hs hts habc, ?_⟩
  refine side_eq_of_convex_decomp hp hc0 hc1 hb0 hb1 hs ht (by linarith) ?_
  rw [add_comm]
  exact habc

/-- **Extreme effects are projections** (𝕜): perturb `a` through the functional
calculus by `± min(x, 1-x)`; both perturbations stay effects and average back to
`a`, so extremeness forces `min(λᵢ, 1-λᵢ) = 0` for every eigenvalue, i.e. the
spectrum lies in `{0,1}`, i.e. `a² = a`. -/
theorem isProjection_of_mem_extremePoints {a : HermitianMat n 𝕜}
    (ha : a ∈ Set.extremePoints ℝ {x : HermitianMat n 𝕜 | 0 ≤ x ∧ x ≤ 1}) :
    a.IsProjection := by
  rw [_root_.mem_extremePoints] at ha
  obtain ⟨⟨ha0, ha1⟩, hext⟩ := ha
  have hev0 : ∀ i, 0 ≤ a.H.eigenvalues i := eigenvalues_nonneg ha0
  have hev1 : ∀ i, a.H.eigenvalues i ≤ 1 := fun i =>
    le_smul_one_imp_eigenvalues_le' a 1 (by simpa using ha1) i
  -- the two perturbations are effects
  have hb_eff : a.cfc (fun x => x + min x (1 - x)) ∈
      {x : HermitianMat n 𝕜 | 0 ≤ x ∧ x ≤ 1} := by
    constructor
    · rw [cfc_nonneg_iff]
      intro i
      rcases le_total (a.H.eigenvalues i) (1 - a.H.eigenvalues i) with hle | hle
      · rw [min_eq_left hle]; linarith [hev0 i]
      · rw [min_eq_right hle]; linarith [hev0 i]
    · rw [← sub_nonneg]
      have h1 : (1 : HermitianMat n 𝕜) - a.cfc (fun x => x + min x (1 - x)) =
          a.cfc (fun x => 1 - (x + min x (1 - x))) := by
        rw [cfc_sub_apply, cfc_const, one_smul]
      rw [h1, cfc_nonneg_iff]
      intro i
      rcases le_total (a.H.eigenvalues i) (1 - a.H.eigenvalues i) with hle | hle
      · rw [min_eq_left hle]; linarith [hev1 i]
      · rw [min_eq_right hle]; linarith [hev1 i]
  have hc_eff : a.cfc (fun x => x - min x (1 - x)) ∈
      {x : HermitianMat n 𝕜 | 0 ≤ x ∧ x ≤ 1} := by
    constructor
    · rw [cfc_nonneg_iff]
      intro i
      have := min_le_left (a.H.eigenvalues i) (1 - a.H.eigenvalues i)
      linarith
    · rw [← sub_nonneg]
      have h1 : (1 : HermitianMat n 𝕜) - a.cfc (fun x => x - min x (1 - x)) =
          a.cfc (fun x => 1 - (x - min x (1 - x))) := by
        conv_rhs => rw [cfc_sub_apply, cfc_const, one_smul]
      rw [h1, cfc_nonneg_iff]
      intro i
      rcases le_total (a.H.eigenvalues i) (1 - a.H.eigenvalues i) with hle | hle
      · rw [min_eq_left hle]; linarith [hev1 i]
      · rw [min_eq_right hle]; linarith [hev1 i]
  -- they average back to a
  have hmid : (1/2 : ℝ) • a.cfc (fun x => x + min x (1 - x)) +
      (1/2 : ℝ) • a.cfc (fun x => x - min x (1 - x)) = a := by
    simp only [← cfc_const_mul, ← cfc_add_apply]
    have hfun : (fun x : ℝ => 1/2 * (x + min x (1 - x)) + 1/2 * (x - min x (1 - x))) =
        fun x : ℝ => x := by
      funext x; ring
    rw [hfun, cfc_id']
  have hseg : a ∈ openSegment ℝ (a.cfc fun x => x + min x (1 - x))
      (a.cfc fun x => x - min x (1 - x)) :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, hmid⟩
  -- extremeness kills the perturbation
  have hb_eq := (hext _ hb_eff _ hc_eff hseg).1
  have hsplit : a.cfc (fun x => x + min x (1 - x)) =
      a + a.cfc (fun x => min x (1 - x)) := by
    rw [cfc_add_apply, cfc_id']
  rw [hsplit] at hb_eq
  have hcfcmin : a.cfc (fun x => min x (1 - x)) = 0 := by
    have := congrArg (fun z => z - a) hb_eq
    simpa using this
  -- eigenvalues sit in {0,1}
  have hminzero : ∀ i, min (a.H.eigenvalues i) (1 - a.H.eigenvalues i) = 0 := by
    intro i
    have hup : (0 : HermitianMat n 𝕜) ≤ a.cfc (fun x => min x (1 - x)) :=
      hcfcmin ▸ le_rfl
    have hdn : (0 : HermitianMat n 𝕜) ≤ a.cfc (fun x => -(min x (1 - x))) := by
      rw [cfc_neg_apply, hcfcmin, neg_zero]
    rw [cfc_nonneg_iff] at hup hdn
    have h1 := hup i
    have h2 := hdn i
    linarith
  have hev01 : ∀ i, a.H.eigenvalues i = 0 ∨ a.H.eigenvalues i = 1 := by
    intro i
    rcases le_total (a.H.eigenvalues i) (1 - a.H.eigenvalues i) with hle | hle
    · left; have := hminzero i; rwa [min_eq_left hle] at this
    · right; have := hminzero i; rw [min_eq_right hle] at this; linarith
  -- assemble a² = a
  have hsq : ∀ i, (a.H.eigenvalues i) ^ 2 - a.H.eigenvalues i = 0 := by
    intro i
    rcases hev01 i with h | h <;> rw [h] <;> norm_num
  have hzero : a.cfc (fun x => x ^ 2 - x) = 0 := by
    have hdown : (0 : HermitianMat n 𝕜) ≤ a.cfc (fun x => x ^ 2 - x) := by
      rw [cfc_nonneg_iff]; intro i; rw [hsq i]
    have hupp : a.cfc (fun x => x ^ 2 - x) ≤ 0 := by
      have : (0 : HermitianMat n 𝕜) ≤ a.cfc (fun x => -(x ^ 2 - x)) := by
        rw [cfc_nonneg_iff]; intro i; rw [hsq i]; norm_num
      rw [cfc_neg_apply] at this
      exact neg_nonneg.mp this
    exact le_antisymm hupp hdown
  have hdiff : a ^ 2 - a = a.cfc (fun x => x ^ 2 - x) := by
    rw [cfc_sub_apply, cfc_pow, cfc_id']
  unfold IsProjection
  rw [← sub_eq_zero, hdiff, hzero]

/-- **The join** (𝕜): extreme points of the effect interval = projections. -/
theorem mem_extremePoints_iff_isProjection {a : HermitianMat n 𝕜} :
    a ∈ Set.extremePoints ℝ {x : HermitianMat n 𝕜 | 0 ≤ x ∧ x ≤ 1} ↔
      a.IsProjection :=
  ⟨isProjection_of_mem_extremePoints, IsProjection.mem_extremePoints⟩

/-- Set form of the join. -/
theorem extremePoints_unitInterval :
    Set.extremePoints ℝ {x : HermitianMat n 𝕜 | 0 ≤ x ∧ x ≤ 1} =
      {p : HermitianMat n 𝕜 | p.IsProjection} :=
  Set.ext fun _ => mem_extremePoints_iff_isProjection

end HermitianMat
