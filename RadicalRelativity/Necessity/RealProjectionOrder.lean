/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealStrength

set_option linter.style.longLine false

/-!
# Atoms of the real projection order  (the ℝ bridge to real Kadison, part 5a)

Unit 5's only prerequisite is **rank-one transport**: an order automorphism carries rank-one
projections to rank-one projections.  That needs rank-ones to be exactly the *atoms* of the
projection order, since atomicity is what an order automorphism can see.

**Route note — this does NOT port the ℂ proof.**  The ℂ argument (`ProjectionOrder` 136-268)
manipulates `vecMulVec` factorizations directly.  Over ℝ there is a shorter conceptual route,
and it is worth writing down because it is the reason this step is not a boulder:

* for a projection `q`, the quadratic form IS a squared norm: `v·qv = |qv|²`
  (`quadForm_isProjection` below, using `q² = q` and `qᵀ = q`);
* so `q ≤ ψψᵀ` forces `qv = 0` for every `v ⊥ ψ`, because `v·qv ≤ (ψ·v)² = 0`;
* hence `range q ⊆ span{qψ}`, and idempotence applied to `qψ = aψ + v₀` gives `a = 1` or
  `qψ = 0`;
* the first case forces `v₀ = 0` by comparing `|qψ|² = ψ·qψ = 1` with `|ψ|² + |v₀|²`, so
  `q = ψψᵀ`; the second gives `q = 0`.

This file supplies the definition, the engine (`quadForm_isProjection`, plus the
nonvanishing of a rank-one), **and the two-case argument itself** — `rankOneR_isAtom`
below, with the converse `IsAtomProjectionR.exists_rankOne`, so atoms and rank-one
projections coincide over ℝ.
-/

noncomputable section

open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An **atom** of the real projection order: a nonzero projection with no proper nonzero
subprojection. -/
def IsAtomProjectionR (p : HermitianMat n ℝ) : Prop :=
  p.IsProjection ∧ p ≠ 0 ∧
    ∀ q : HermitianMat n ℝ, q.IsProjection → q ≤ p → q = 0 ∨ q = p

/-- **For a projection the quadratic form is a squared norm.**  This is the engine of the
atom argument: it converts an order bound `q ≤ a` into the *vanishing* of `q` on vectors
where `a`'s form vanishes, which is much stronger than an inequality. -/
theorem quadForm_isProjection {q : HermitianMat n ℝ} (hq : q.IsProjection) (v : n → ℝ) :
    v ⬝ᵥ (q.mat *ᵥ v) = (q.mat *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) := by
  have hmul : q.mat * q.mat = q.mat := HermitianMat.isProjection_iff_mat_mul_self.mp hq
  have hsym : q.matᵀ = q.mat := by
    have h : q.matᴴ = q.mat := q.H
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  calc v ⬝ᵥ (q.mat *ᵥ v)
      = v ⬝ᵥ ((q.mat * q.mat) *ᵥ v) := by rw [hmul]
    _ = v ⬝ᵥ (q.mat *ᵥ (q.mat *ᵥ v)) := by rw [Matrix.mulVec_mulVec]
    _ = (q.matᵀ *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) := by
        rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    _ = (q.mat *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) := by rw [hsym]

/-- A subprojection of `ψψᵀ` annihilates everything orthogonal to `ψ`. -/
theorem mulVec_eq_zero_of_le_rankOneR {q : HermitianMat n ℝ} (hq : q.IsProjection)
    {ψ : n → ℝ} (hle : q ≤ rankOneR ψ) {v : n → ℝ} (hv : ψ ⬝ᵥ v = 0) :
    q.mat *ᵥ v = 0 := by
  have hform := (HermitianMat.le_iff_mulVec_le_mulVec _ _).mp hle v
  rw [star_trivial, quadForm_rankOneR, hv] at hform
  rw [quadForm_isProjection hq] at hform
  have hz : (q.mat *ᵥ v) ⬝ᵥ (q.mat *ᵥ v) = 0 :=
    le_antisymm (by simpa using hform) (dotProduct_self_nonnegR _)
  exact dotProduct_self_eq_zero.mp hz

theorem rankOneR_ne_zero {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) : rankOneR ψ ≠ 0 := by
  intro h
  have hq := quadForm_rankOneR ψ ψ
  rw [h, HermitianMat.mat_zero, Matrix.zero_mulVec, dotProduct_zero, hψ] at hq
  norm_num at hq

/-! ## Rank-ones are exactly the atoms -/

/-- Matrices agreeing on every vector are equal. -/
theorem matrix_ext_of_mulVec {M N : Matrix n n ℝ} (h : ∀ v, M *ᵥ v = N *ᵥ v) : M = N := by
  ext i j
  have hij := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using hij

/-- **Rank-one projections are atoms.**  A subprojection `q ≤ ψψᵀ` kills `ψ`'s orthogonal
complement, so `q` is determined by `u = qψ`; idempotence forces `u = (ψ·u)u`, and then either
`u = 0` (so `q = 0`) or `ψ·u = u·u = 1`, whence `|ψ − u|² = 0` and `q = ψψᵀ`.  The last step is
the slick one: rather than decomposing `u` and killing a component, compare `|ψ − u|²` directly. -/
theorem rankOneR_isAtom {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) : IsAtomProjectionR (rankOneR ψ) := by
  refine ⟨rankOneR_isProjection hψ, rankOneR_ne_zero hψ, ?_⟩
  intro q hq hle
  -- `q` is determined by its value on `ψ`
  have hdecomp : ∀ v : n → ℝ, q.mat *ᵥ v = (ψ ⬝ᵥ v) • (q.mat *ᵥ ψ) := by
    intro v
    have hw : ψ ⬝ᵥ (v - (ψ ⬝ᵥ v) • ψ) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hψ, mul_one, sub_self]
    have hqw := mulVec_eq_zero_of_le_rankOneR hq hle hw
    rwa [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at hqw
  have hidem : q.mat *ᵥ (q.mat *ᵥ ψ) = q.mat *ᵥ ψ := by
    rw [Matrix.mulVec_mulVec, HermitianMat.isProjection_iff_mat_mul_self.mp hq]
  -- the norm identity: `ψ·u = u·u`
  have hnorm : ψ ⬝ᵥ (q.mat *ᵥ ψ) = (q.mat *ᵥ ψ) ⬝ᵥ (q.mat *ᵥ ψ) := quadForm_isProjection hq ψ
  by_cases hu : q.mat *ᵥ ψ = 0
  · -- `q` annihilates everything, so it is zero
    left
    apply HermitianMat.ext
    refine matrix_ext_of_mulVec fun v => ?_
    rw [hdecomp v, hu, smul_zero, HermitianMat.mat_zero, Matrix.zero_mulVec]
  · -- `ψ·u = 1`, hence `u = ψ`
    right
    have huu : (q.mat *ᵥ ψ) ⬝ᵥ (q.mat *ᵥ ψ) ≠ 0 := fun h => hu (dotProduct_self_eq_zero.mp h)
    have ha : ψ ⬝ᵥ (q.mat *ᵥ ψ) = 1 := by
      have h1 : (ψ ⬝ᵥ (q.mat *ᵥ ψ)) • (q.mat *ᵥ ψ) = q.mat *ᵥ ψ := by
        rw [← hdecomp (q.mat *ᵥ ψ)]; exact hidem
      have h2 : (ψ ⬝ᵥ (q.mat *ᵥ ψ)) * ((q.mat *ᵥ ψ) ⬝ᵥ (q.mat *ᵥ ψ))
          = (q.mat *ᵥ ψ) ⬝ᵥ (q.mat *ᵥ ψ) := by
        have h3 := congrArg (fun x => x ⬝ᵥ (q.mat *ᵥ ψ)) h1
        simpa [smul_dotProduct] using h3
      exact mul_right_cancel₀ huu (by rw [h2, one_mul])
    have hueq : q.mat *ᵥ ψ = ψ := by
      have hz : (ψ - q.mat *ᵥ ψ) ⬝ᵥ (ψ - q.mat *ᵥ ψ) = 0 := by
        rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hψ, ha, ← hnorm, ha,
          dotProduct_comm (q.mat *ᵥ ψ) ψ, ha]
        ring
      exact (sub_eq_zero.mp (dotProduct_self_eq_zero.mp hz)).symm
    apply HermitianMat.ext
    refine matrix_ext_of_mulVec fun v => ?_
    rw [hdecomp v, hueq, rankOneR_mat, vecMulVec_mulVec]

/-- **Conversely, every atom is a rank-one.**  Take any nonzero range vector, normalize it to
`ψ`; then `pψ = ψ`, and symmetry plus Cauchy-Schwarz give `(ψ·w)² ≤ w·pw`, i.e.
`ψψᵀ ≤ p`.  Atomicity leaves only `ψψᵀ = p`. -/
theorem IsAtomProjectionR.exists_rankOne {p : HermitianMat n ℝ} (hp : IsAtomProjectionR p) :
    ∃ ψ : n → ℝ, ψ ⬝ᵥ ψ = 1 ∧ p = rankOneR ψ := by
  obtain ⟨hproj, hne, hatom⟩ := hp
  have hmul : p.mat * p.mat = p.mat := HermitianMat.isProjection_iff_mat_mul_self.mp hproj
  have hsym : p.matᵀ = p.mat := by
    have h : p.matᴴ = p.mat := p.H
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hmove : ∀ x y : n → ℝ, x ⬝ᵥ (p.mat *ᵥ y) = (p.mat *ᵥ x) ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]
  -- a nonzero range vector
  obtain ⟨v, hv⟩ : ∃ v, p.mat *ᵥ v ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (HermitianMat.ext (matrix_ext_of_mulVec fun w => by
      rw [hall w, HermitianMat.mat_zero, Matrix.zero_mulVec]))
  have hvv : (0 : ℝ) < (p.mat *ᵥ v) ⬝ᵥ (p.mat *ᵥ v) :=
    lt_of_le_of_ne (dotProduct_self_nonnegR _)
      (fun h => hv (dotProduct_self_eq_zero.mp h.symm))
  -- name the constant and the vector so later rewrites cannot reach inside them
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Real.sqrt ((p.mat *ᵥ v) ⬝ᵥ (p.mat *ᵥ v)))⁻¹ := ⟨_, rfl⟩
  obtain ⟨ψ, hψd⟩ : ∃ ψ : n → ℝ, ψ = c • (p.mat *ᵥ v) := ⟨_, rfl⟩
  have hunit : ψ ⬝ᵥ ψ = 1 := by
    rw [hψd, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, hc,
      inv_pow, Real.sq_sqrt hvv.le, inv_mul_cancel₀ hvv.ne']
  have hfix : p.mat *ᵥ ψ = ψ := by
    rw [hψd, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hmul]
  -- `ψψᵀ ≤ p`, by symmetry of `p` and Cauchy-Schwarz
  have hle : rankOneR ψ ≤ p := by
    rw [HermitianMat.le_iff_mulVec_le_mulVec]
    intro w
    rw [star_trivial, quadForm_rankOneR]
    have hstep : ψ ⬝ᵥ w = ψ ⬝ᵥ (p.mat *ᵥ w) := by rw [hmove, hfix]
    rw [hstep]
    have hcs := dotProduct_sq_le ψ (p.mat *ᵥ w)
    rw [hunit, one_mul, ← quadForm_isProjection hproj w] at hcs
    exact hcs
  refine ⟨ψ, hunit, ?_⟩
  rcases hatom _ (rankOneR_isProjection hunit) hle with h | h
  · exact absurd h (rankOneR_ne_zero hunit)
  · exact h.symm

/-! ## Order transport

These two are the purely order-theoretic half of rank-one transport, and they are direct ports
of the ℂ arguments with `ℂ` replaced by `ℝ` — nothing about the scalar field enters.  Being
a projection is *extremality in the effect interval*, and being an atom is a statement about the
projection order; an order isomorphism sees both.
-/

/-- A unital linear order-isomorphism preserves being a projection. -/
theorem isProjection_mapR (Φ : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ)
    (hΦ : ∀ x y : HermitianMat n ℝ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ)
    {p : HermitianMat n ℝ} (hp : p.IsProjection) :
    (Φ p).IsProjection := by
  rw [← HermitianMat.mem_extremePoints_iff_isProjection] at hp ⊢
  obtain ⟨⟨hp0, hp1⟩, hext⟩ := hp
  have hinj : Function.Injective Φ := fun u v huv =>
    le_antisymm ((hΦ u v).mpr (le_of_eq huv)) ((hΦ v u).mpr (le_of_eq huv.symm))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := (hΦ 0 p).mp hp0
    rwa [map_zero] at h
  · have h := (hΦ p 1).mp hp1
    rwa [hunital] at h
  · intro b hb c hc hmem
    obtain ⟨b', hb'⟩ := hsurj b
    obtain ⟨c', hc'⟩ := hsurj c
    have hb0 : b' ∈ {x : HermitianMat n ℝ | 0 ≤ x ∧ x ≤ 1} :=
      ⟨(hΦ 0 b').mpr (by rw [map_zero, hb']; exact hb.1),
        (hΦ b' 1).mpr (by rw [hunital, hb']; exact hb.2)⟩
    have hc0 : c' ∈ {x : HermitianMat n ℝ | 0 ≤ x ∧ x ≤ 1} :=
      ⟨(hΦ 0 c').mpr (by rw [map_zero, hc']; exact hc.1),
        (hΦ c' 1).mpr (by rw [hunital, hc']; exact hc.2)⟩
    have hpmem : p ∈ openSegment ℝ b' c' := by
      obtain ⟨a₁, a₂, ha₁, ha₂, hsum, hpt⟩ := hmem
      refine ⟨a₁, a₂, ha₁, ha₂, hsum, hinj ?_⟩
      rw [map_add, map_smul, map_smul, hb', hc']
      exact hpt
    have he1 := hext hb0 hc0 hpmem
    rw [← hb', he1]

/-- **Atom transport**: a unital linear order-automorphism carries atoms to atoms. -/
theorem isAtomProjection_mapR (Φ : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ)
    (hΦ : ∀ x y : HermitianMat n ℝ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ)
    {p : HermitianMat n ℝ} (hp : IsAtomProjectionR p) :
    IsAtomProjectionR (Φ p) := by
  obtain ⟨hproj, hne, hatom⟩ := hp
  have hinj : Function.Injective Φ := fun u v huv =>
    le_antisymm ((hΦ u v).mpr (le_of_eq huv)) ((hΦ v u).mpr (le_of_eq huv.symm))
  refine ⟨isProjection_mapR Φ hΦ hunital hsurj hproj, ?_, ?_⟩
  · intro h
    exact hne (hinj (by rw [h, map_zero]))
  · intro q hq hle
    obtain ⟨q', hq'⟩ := hsurj q
    have hqproj' : q'.IsProjection := by
      by_cases htriv : q' = 0
      · rw [htriv]
        show (0 : HermitianMat n ℝ) ^ 2 = 0
        simp
      · rw [← HermitianMat.mem_extremePoints_iff_isProjection]
        have hqe : Φ q' ∈ Set.extremePoints ℝ {x : HermitianMat n ℝ | 0 ≤ x ∧ x ≤ 1} := by
          rw [HermitianMat.mem_extremePoints_iff_isProjection, hq']
          exact hq
        obtain ⟨⟨h0, h1⟩, hext⟩ := hqe
        refine ⟨⟨(hΦ 0 q').mpr (by rwa [map_zero]), (hΦ q' 1).mpr (by rwa [hunital])⟩, ?_⟩
        intro b hb c hc hmem
        have hbmem : Φ b ∈ {x : HermitianMat n ℝ | 0 ≤ x ∧ x ≤ 1} := by
          refine ⟨?_, ?_⟩
          · have h := (hΦ 0 b).mp hb.1
            rwa [map_zero] at h
          · have h := (hΦ b 1).mp hb.2
            rwa [hunital] at h
        have hcmem : Φ c ∈ {x : HermitianMat n ℝ | 0 ≤ x ∧ x ≤ 1} := by
          refine ⟨?_, ?_⟩
          · have h := (hΦ 0 c).mp hc.1
            rwa [map_zero] at h
          · have h := (hΦ c 1).mp hc.2
            rwa [hunital] at h
        have hmem' : Φ q' ∈ openSegment ℝ (Φ b) (Φ c) := by
          obtain ⟨a₁, a₂, ha₁, ha₂, hsum, hpt⟩ := hmem
          refine ⟨a₁, a₂, ha₁, ha₂, hsum, ?_⟩
          rw [← map_smul, ← map_smul, ← map_add, hpt]
        exact hinj (hext hbmem hcmem hmem')
    have hle' : q' ≤ p := (hΦ q' p).mpr (by rw [hq']; exact hle)
    rcases hatom q' hqproj' hle' with h0 | hp'
    · left
      rw [← hq', h0, map_zero]
    · right
      rw [← hq', hp']

/-- **Rank-one transport**, the input unit 5 needs: a unital linear order-automorphism carries
each rank-one projection to a rank-one projection, with an explicit unit vector. -/
theorem exists_rankOneR_map (Φ : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ)
    (hΦ : ∀ x y : HermitianMat n ℝ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ)
    {ψ : n → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) :
    ∃ ψ' : n → ℝ, ψ' ⬝ᵥ ψ' = 1 ∧ Φ (rankOneR ψ) = rankOneR ψ' :=
  (isAtomProjection_mapR Φ hΦ hunital hsurj (rankOneR_isAtom hψ)).exists_rankOne

end Necessity
