/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.StrengthProbe
import RadicalRelativity.Necessity.ThetaCocycle

set_option linter.style.longLine false

/-!
# The two Jordan witnesses: conjugation and transpose-conjugation  (M3, 3.2d)

The Wigner dichotomy hands back a unitary or an antiunitary.  Both branches
land on Jordan automorphisms, which is the last step of M3:

* `unitaryConj` — `x ↦ U x U*` as an ℝ-linear map on `H_n(ℂ)`, and
  `unitaryConj_preservesJordan`: it preserves the symmetrized product for any
  `U` with `U* U = 1` (the `U* U` cancellation in the middle of the two
  products).
* `transposeMap` — `x ↦ xᵗ` on `H_n(ℂ)` (well defined: the transpose of a
  Hermitian matrix is Hermitian), and `transposeMap_preservesJordan`: the
  transpose is an *anti*-automorphism of matrix multiplication, hence an
  automorphism of the *symmetrized* product.
* `antiunitaryConj_preservesJordan` — the composite `x ↦ U xᵗ U*`, the
  antiunitary branch.

Together: whichever branch `Projectivization.wigner_rigidity` returns, the
induced order-automorphism satisfies `PreservesJordan`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Unitary conjugation -/

/-- Conjugation by a matrix, as an ℝ-linear map. -/
def unitaryConj (U : Matrix n n ℂ) : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ where
  toFun x := x.conj U
  map_add' x y := map_add (HermitianMat.conj U) x y
  map_smul' c x := by
    ext1
    rw [HermitianMat.conj_apply_mat, HermitianMat.mat_smul, HermitianMat.mat_smul,
      HermitianMat.conj_apply_mat, Matrix.mul_smul, Matrix.smul_mul]
    rfl

@[simp]
theorem unitaryConj_apply (U : Matrix n n ℂ) (x : HermitianMat n ℂ) :
    unitaryConj U x = x.conj U := rfl

/-- **The unitary branch is a Jordan automorphism**: `U* U = 1` cancels in the
middle of each product. -/
theorem unitaryConj_preservesJordan {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    PreservesJordan (unitaryConj U) := by
  intro x y
  ext1
  rw [unitaryConj_apply, HermitianMat.conj_apply_mat, HermitianMat.symmMul_toMat,
    HermitianMat.symmMul_toMat, unitaryConj_apply, unitaryConj_apply,
    HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · calc U * (x.mat * y.mat) * Uᴴ
        = U * x.mat * (Uᴴ * U) * y.mat * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * x.mat * Uᴴ * (U * y.mat * Uᴴ) := by noncomm_ring
  · calc U * (y.mat * x.mat) * Uᴴ
        = U * y.mat * (Uᴴ * U) * x.mat * Uᴴ := by rw [hU]; noncomm_ring
      _ = U * y.mat * Uᴴ * (U * x.mat * Uᴴ) := by noncomm_ring

/-! ## Transposition -/

omit [Fintype n] [DecidableEq n] in
/-- The transpose of a Hermitian matrix is Hermitian. -/
theorem transpose_isHermitian (x : HermitianMat n ℂ) :
    (x.mat.transpose).IsHermitian := by
  show _ᴴ = _
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.transpose_apply]
  have h := congrFun₂ x.property j i
  rw [Matrix.star_apply] at h
  exact h

/-- Transposition as an ℝ-linear map on `H_n(ℂ)`. -/
def transposeMap : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ where
  toFun x := ⟨x.mat.transpose, transpose_isHermitian x⟩
  map_add' x y := by
    ext1
    show (x + y).mat.transpose = _
    rw [HermitianMat.mat_add, Matrix.transpose_add]
    rfl
  map_smul' c x := by
    ext1
    show (c • x).mat.transpose = _
    -- v4.33 leaves the scalar wrapped as `(RingHom.id ℝ) c`, which `rw` will not match.
    simp only [HermitianMat.mat_smul, Matrix.transpose_smul, RingHom.id_apply]
    rfl

omit [Fintype n] in
@[simp]
theorem transposeMap_mat (x : HermitianMat n ℂ) :
    (transposeMap x).mat = x.mat.transpose := rfl

/-- **Transposition is a Jordan automorphism**: it reverses matrix products, but
the symmetrized product is invariant under reversal. -/
theorem transposeMap_preservesJordan :
    PreservesJordan (transposeMap (n := n)) := by
  intro x y
  ext1
  rw [transposeMap_mat, HermitianMat.symmMul_toMat, HermitianMat.symmMul_toMat,
    transposeMap_mat, transposeMap_mat]
  rw [Matrix.transpose_smul]
  congr 1
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul]
  exact add_comm _ _

/-! ## The antiunitary branch -/

/-- **The antiunitary branch is a Jordan automorphism**: the composite of the
two witnesses. -/
theorem antiunitaryConj_preservesJordan {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) :
    PreservesJordan ((unitaryConj U).comp (transposeMap (n := n))) := by
  intro x y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    transposeMap_preservesJordan x y, unitaryConj_preservesJordan hU]

/-! ## Atom transport: an order-automorphism permutes rank-one projections

The bridge-1 characterization `IsAtomProjection` is stated purely in the order
(a nonzero projection with no proper nonzero subprojection), so it transports
along any unital linear order-isomorphism.  Composed with
`IsAtomProjection.exists_rankOne` this says: `Φ` carries rank-one projections
to rank-one projections — the input the ray map needs. -/

/-- A unital linear order-isomorphism preserves being a projection: projections
are exactly the extreme points of the effect interval, which is order data. -/
theorem isProjection_map (Φ : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    (hΦ : ∀ x y : HermitianMat n ℂ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ)
    {p : HermitianMat n ℂ} (hp : p.IsProjection) :
    (Φ p).IsProjection := by
  rw [← HermitianMat.mem_extremePoints_iff_isProjection] at hp ⊢
  obtain ⟨⟨hp0, hp1⟩, hext⟩ := hp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := (hΦ 0 p).mp hp0
    rwa [map_zero] at h
  · have h := (hΦ p 1).mp hp1
    rwa [hunital] at h
  · intro b hb c hc hmem
    obtain ⟨b', hb'⟩ := hsurj b
    obtain ⟨c', hc'⟩ := hsurj c
    have hinj : Function.Injective Φ := by
      intro u v huv
      exact le_antisymm ((hΦ u v).mpr (le_of_eq huv))
        ((hΦ v u).mpr (le_of_eq huv.symm))
    have hb0 : b' ∈ {x : HermitianMat n ℂ | 0 ≤ x ∧ x ≤ 1} := by
      constructor
      · refine (hΦ 0 b').mpr ?_
        rw [map_zero, hb']; exact hb.1
      · refine (hΦ b' 1).mpr ?_
        rw [hunital, hb']; exact hb.2
    have hc0 : c' ∈ {x : HermitianMat n ℂ | 0 ≤ x ∧ x ≤ 1} := by
      constructor
      · refine (hΦ 0 c').mpr ?_
        rw [map_zero, hc']; exact hc.1
      · refine (hΦ c' 1).mpr ?_
        rw [hunital, hc']; exact hc.2
    have hpmem : p ∈ openSegment ℝ b' c' := by
      obtain ⟨a₁, a₂, ha₁, ha₂, hsum, hpt⟩ := hmem
      refine ⟨a₁, a₂, ha₁, ha₂, hsum, hinj ?_⟩
      rw [map_add, map_smul, map_smul, hb', hc']
      exact hpt
    have he1 := hext hb0 hc0 hpmem
    rw [← hb', he1]

/-- **Atom transport**: a unital linear order-automorphism carries atoms of the
projection order to atoms.  Everything in `IsAtomProjection` is order data. -/
theorem isAtomProjection_map (Φ : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    (hΦ : ∀ x y : HermitianMat n ℂ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ)
    {p : HermitianMat n ℂ} (hp : HermitianMat.IsAtomProjection p) :
    HermitianMat.IsAtomProjection (Φ p) := by
  obtain ⟨hproj, hne, hatom⟩ := hp
  have hinj : Function.Injective Φ := by
    intro u v huv
    exact le_antisymm ((hΦ u v).mpr (le_of_eq huv)) ((hΦ v u).mpr (le_of_eq huv.symm))
  refine ⟨isProjection_map Φ hΦ hunital hsurj hproj, ?_, ?_⟩
  · intro h
    exact hne (hinj (by rw [h, map_zero]))
  · intro q hq hle
    obtain ⟨q', hq'⟩ := hsurj q
    have hqproj' : q'.IsProjection := by
      -- pull the projection property back along the inverse order-iso
      by_cases htriv : q' = 0
      · rw [htriv]
        show (0 : HermitianMat n ℂ) ^ 2 = 0
        simp
      · -- `Φ` is injective and order-reflecting, so the extreme-point property
        -- transports backwards exactly as it does forwards
        rw [← HermitianMat.mem_extremePoints_iff_isProjection]
        have hqe : Φ q' ∈ Set.extremePoints ℝ {x : HermitianMat n ℂ | 0 ≤ x ∧ x ≤ 1} := by
          rw [HermitianMat.mem_extremePoints_iff_isProjection, hq']
          exact hq
        obtain ⟨⟨h0, h1⟩, hext⟩ := hqe
        refine ⟨⟨(hΦ 0 q').mpr (by rwa [map_zero]), (hΦ q' 1).mpr (by rwa [hunital])⟩, ?_⟩
        intro b hb c hc hmem
        have hbmem : Φ b ∈ {x : HermitianMat n ℂ | 0 ≤ x ∧ x ≤ 1} := by
          constructor
          · have := (hΦ 0 b).mp hb.1
            rwa [map_zero] at this
          · have := (hΦ b 1).mp hb.2
            rwa [hunital] at this
        have hcmem : Φ c ∈ {x : HermitianMat n ℂ | 0 ≤ x ∧ x ≤ 1} := by
          constructor
          · have := (hΦ 0 c).mp hc.1
            rwa [map_zero] at this
          · have := (hΦ c 1).mp hc.2
            rwa [hunital] at this
        have hmem' : Φ q' ∈ openSegment ℝ (Φ b) (Φ c) := by
          obtain ⟨a₁, a₂, ha₁, ha₂, hsum, hpt⟩ := hmem
          refine ⟨a₁, a₂, ha₁, ha₂, hsum, ?_⟩
          rw [← map_smul, ← map_smul, ← map_add, hpt]
        have := hext hbmem hcmem hmem'
        exact hinj this
    have hle' : q' ≤ p := (hΦ q' p).mpr (by rw [hq']; exact hle)
    rcases hatom q' hqproj' hle' with h0 | hp'
    · left
      rw [← hq', h0, map_zero]
    · right
      rw [← hq', hp']

/-- **Rank-one transport (M3 (a))**: a unital linear order-automorphism carries
each rank-one projection to a rank-one projection, with an explicit unit vector.
This is the input of the ray map. -/
theorem exists_rankOne_map (Φ : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
    (hΦ : ∀ x y : HermitianMat n ℂ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ)
    {ψ : n → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    ∃ ψ' : n → ℂ, star ψ' ⬝ᵥ ψ' = 1 ∧ Φ (HermitianMat.rankOne ψ)
      = HermitianMat.rankOne ψ' :=
  (isAtomProjection_map Φ hΦ hunital hsurj
    (HermitianMat.rankOne_isAtom hψ)).exists_rankOne

end Necessity
