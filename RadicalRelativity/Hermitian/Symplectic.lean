/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit
import RadicalRelativity.Vendor.HermitianMat.Jordan

set_option linter.style.longLine false

/-!
# The quaternionic type inside the complex one: the symplectic involution

The `H_n(ℍ)` row of `mthm:master` looked blocked because `HermitianMat n 𝕜` is
`RCLike`-based and `ℍ` is not `RCLike` (it cannot be — the class demands
commutativity).  But quaternionic Hermitian matrices need no new carrier: they are
the **fixed points of a conjugate-linear involution on complex ones**, via the
standard identification `ℍⁿ ≅ ℂ^{2n}` under which right multiplication by `j`
becomes `v ↦ J₀ v̄`.

A complex matrix is quaternion-linear exactly when it commutes with that map, i.e.

`A = J₀ · Ā · J₀ᵀ`,

so `H_n(ℍ)` sits inside `H_{2n}(ℂ)` as the fixed set of `Φ A := J₀ Ā J₀ᵀ`.  That
route stays entirely inside complex Hermitian matrices — the machinery this campaign
already has — and never needs a Hermitian layer over a noncommutative ring.

* `symplecticJ` — `J₀ = [[0, −1], [1, 0]]` in block form, with `symplecticJ_transpose_mul`
  (`J₀ᵀJ₀ = 1`) and `symplecticJ_mul_transpose`.
* `quatConj` — the involution `Φ A = J₀ Ā J₀ᵀ` at the matrix level, **multiplicative**
  (`quatConj_mul`) because `J₀ᵀJ₀ = 1`, and involutive.
* `IsQuaternionic` — the fixed-point predicate, closed under the additive and real-linear
  structure and — the point — under the **Jordan product** (`IsQuaternionic.symmMul`),
  so the fixed set is a Jordan subalgebra of `H_{2n}(ℂ)`.
-/

noncomputable section

open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The symplectic matrix -/

/-- The standard symplectic matrix `J₀ = [[0, −1], [1, 0]]` on `ℂ^{n} ⊕ ℂ^{n}`. -/
def symplecticJ : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  Matrix.fromBlocks 0 (-1) 1 0

@[simp]
theorem symplecticJ_transpose_mul :
    (symplecticJ (n := n))ᵀ * symplecticJ (n := n) = 1 := by
  rw [symplecticJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

@[simp]
theorem symplecticJ_mul_transpose :
    symplecticJ (n := n) * (symplecticJ (n := n))ᵀ = 1 := by
  rw [symplecticJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/-! ## The conjugate-linear involution -/

/-- `Φ A = J₀ · Ā · J₀ᵀ`: the conjugate-linear involution of `M_{2n}(ℂ)` whose fixed
points are the quaternion-linear maps. -/
def quatConj (A : Matrix (n ⊕ n) (n ⊕ n) ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  symplecticJ * (A.map (starRingEnd ℂ)) * (symplecticJ)ᵀ

/-- **`Φ` is multiplicative** — this is what makes the fixed set an algebra, and it is
exactly where `J₀ᵀJ₀ = 1` is used. -/
theorem quatConj_mul (A B : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    quatConj (A * B) = quatConj A * quatConj B := by
  unfold quatConj
  have hmap : (A * B).map (starRingEnd ℂ)
      = (A.map (starRingEnd ℂ)) * (B.map (starRingEnd ℂ)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
  rw [hmap]
  calc symplecticJ * ((A.map (starRingEnd ℂ)) * (B.map (starRingEnd ℂ))) * symplecticJᵀ
      = symplecticJ * (A.map (starRingEnd ℂ)) *
          (symplecticJᵀ * symplecticJ) * (B.map (starRingEnd ℂ)) * symplecticJᵀ := by
        rw [symplecticJ_transpose_mul]
        simp only [Matrix.mul_one]
        noncomm_ring
    _ = symplecticJ * (A.map (starRingEnd ℂ)) * symplecticJᵀ *
          (symplecticJ * (B.map (starRingEnd ℂ)) * symplecticJᵀ) := by
        noncomm_ring

theorem quatConj_add (A B : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    quatConj (A + B) = quatConj A + quatConj B := by
  unfold quatConj
  rw [Matrix.map_add _ (map_add (starRingEnd ℂ))]
  noncomm_ring

theorem quatConj_real_smul (r : ℝ) (A : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    quatConj (r • A) = r • quatConj A := by
  unfold quatConj
  have hmap : (r • A).map (starRingEnd ℂ) = r • A.map (starRingEnd ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
  rw [hmap]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `Φ` is homogeneous for any **self-conjugate** scalar — which covers the `2⁻¹` in the
Jordan product. -/
theorem quatConj_smul_of_conj_eq {c : ℂ} (hc : (starRingEnd ℂ) c = c)
    (A : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    quatConj (c • A) = c • quatConj A := by
  unfold quatConj
  have hmap : (c • A).map (starRingEnd ℂ) = c • A.map (starRingEnd ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc]
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul]

/-! ## The quaternionic subalgebra -/

/-- **`A` is quaternionic**: it commutes with right multiplication by `j`, i.e. it is a
fixed point of `Φ`.  These are exactly the images of `H_n(ℍ)` in `H_{2n}(ℂ)`. -/
def IsQuaternionic (A : HermitianMat (n ⊕ n) ℂ) : Prop :=
  quatConj A.mat = A.mat

theorem IsQuaternionic.add {A B : HermitianMat (n ⊕ n) ℂ}
    (hA : IsQuaternionic A) (hB : IsQuaternionic B) : IsQuaternionic (A + B) := by
  unfold IsQuaternionic at hA hB ⊢
  show quatConj ((A + B).mat) = (A + B).mat
  rw [HermitianMat.mat_add, quatConj_add, hA, hB]

theorem IsQuaternionic.smul {A : HermitianMat (n ⊕ n) ℂ} (r : ℝ)
    (hA : IsQuaternionic A) : IsQuaternionic (r • A) := by
  unfold IsQuaternionic at hA ⊢
  show quatConj ((r • A).mat) = (r • A).mat
  rw [HermitianMat.mat_smul, quatConj_real_smul, hA]

/-- **The fixed set is closed under the Jordan product**, so it is a Jordan subalgebra
of `H_{2n}(ℂ)`: `Φ` is multiplicative, hence preserves `½(AB + BA)`.  This is the
structural fact the `H_n(ℍ)` row is built on. -/
theorem IsQuaternionic.symmMul {A B : HermitianMat (n ⊕ n) ℂ}
    (hA : IsQuaternionic A) (hB : IsQuaternionic B) :
    quatConj ((A.symmMul B).mat) = (A.symmMul B).mat := by
  rw [HermitianMat.symmMul_toMat]
  have hc : (starRingEnd ℂ) ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
    rw [map_inv₀, show (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) from by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]]
  rw [quatConj_smul_of_conj_eq hc, quatConj_add, quatConj_mul, quatConj_mul, hA, hB]

end HermitianMat
