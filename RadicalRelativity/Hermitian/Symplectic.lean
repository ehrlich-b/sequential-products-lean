/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit
import RadicalRelativity.Hermitian.OperatorInstances
import RadicalRelativity.Vendor.HermitianMat.Jordan
import RadicalRelativity.Hermitian.CfcSqrtContinuous

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

open ComplexOrder
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

/-- `J₀² = −1`: the symplectic matrix squares to minus the identity, which is what makes
`Φ` an involution. -/
theorem symplecticJ_sq : symplecticJ (n := n) * symplecticJ (n := n) = -1 := by
  rw [symplecticJ, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, apply_ite]

/-- **`Φ` is an involution**: `J₀` is real, so conjugating twice returns `J₀² A (J₀ᵀ)²`,
and both squares are `−1`. -/
theorem quatConj_involutive (A : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    quatConj (quatConj A) = A := by
  unfold quatConj
  have hJreal : (symplecticJ (n := n)).map (starRingEnd ℂ) = symplecticJ (n := n) := by
    rw [symplecticJ]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.map_apply, Matrix.one_apply, apply_ite]
  have hJTreal : ((symplecticJ (n := n))ᵀ).map (starRingEnd ℂ)
      = (symplecticJ (n := n))ᵀ := by
    ext i j
    have := congrFun (congrFun hJreal j) i
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  have hmap : ∀ X Y Z : Matrix (n ⊕ n) (n ⊕ n) ℂ,
      (X * Y * Z).map (starRingEnd ℂ)
        = X.map (starRingEnd ℂ) * Y.map (starRingEnd ℂ) * Z.map (starRingEnd ℂ) := by
    intro X Y Z
    have h1 : ∀ P Q : Matrix (n ⊕ n) (n ⊕ n) ℂ, (P * Q).map (starRingEnd ℂ)
        = P.map (starRingEnd ℂ) * Q.map (starRingEnd ℂ) := by
      intro P Q
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
    rw [h1, h1]
  have hdouble : (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by
    ext i j
    simp only [Matrix.map_apply, Complex.conj_conj]
  rw [hmap, hJreal, hJTreal, hdouble]
  calc symplecticJ * (symplecticJ * A * symplecticJᵀ) * symplecticJᵀ
      = (symplecticJ * symplecticJ) * A * (symplecticJᵀ * symplecticJᵀ) := by
        noncomm_ring
    _ = A := by
        rw [symplecticJ_sq, ← Matrix.transpose_mul, symplecticJ_sq,
          Matrix.transpose_neg, Matrix.transpose_one]
        noncomm_ring

/-! ## The quaternionic subalgebra -/

/-- **`A` is quaternionic**: it commutes with right multiplication by `j`, i.e. it is a
fixed point of `Φ`.  These are exactly the images of `H_n(ℍ)` in `H_{2n}(ℂ)`. -/
def IsQuaternionic (A : HermitianMat (n ⊕ n) ℂ) : Prop :=
  quatConj A.mat = A.mat

/-- The identity is quaternionic (`J₀ J₀ᵀ = 1`). -/
theorem isQuaternionic_one : IsQuaternionic (1 : HermitianMat (n ⊕ n) ℂ) := by
  unfold IsQuaternionic quatConj
  rw [HermitianMat.mat_one]
  have h : (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).map (starRingEnd ℂ) = 1 := by
    ext i j
    simp [Matrix.one_apply, apply_ite]
  rw [h, Matrix.mul_one, symplecticJ_mul_transpose]

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

/-! ## The quaternionic set as a real subspace -/

theorem isQuaternionic_zero : IsQuaternionic (0 : HermitianMat (n ⊕ n) ℂ) := by
  unfold IsQuaternionic quatConj
  rw [HermitianMat.mat_zero]
  have h : (0 : Matrix (n ⊕ n) (n ⊕ n) ℂ).map (starRingEnd ℂ) = 0 := by
    ext i j
    simp
  rw [h, Matrix.mul_zero, Matrix.zero_mul]

/-- **`H_n(ℍ)` as a real subspace of `H_{2n}(ℂ)`.**  Packaging the fixed set as a
`Submodule ℝ` is what lets the quaternionic carrier inherit its normed and order
structure from the complex one, rather than being built from scratch over a
noncommutative ring. -/
def quatSubmodule : Submodule ℝ (HermitianMat (n ⊕ n) ℂ) where
  carrier := {A | IsQuaternionic A}
  zero_mem' := isQuaternionic_zero
  add_mem' := fun hA hB => IsQuaternionic.add hA hB
  smul_mem' := fun r _ hA => IsQuaternionic.smul r hA

@[simp]
theorem mem_quatSubmodule {A : HermitianMat (n ⊕ n) ℂ} :
    A ∈ quatSubmodule (n := n) ↔ IsQuaternionic A := Iff.rfl

/-- The unit lies in the quaternionic subspace, so the subspace is a candidate
order-unit space with the inherited order — the carrier the `H_n(ℍ)` row needs. -/
theorem one_mem_quatSubmodule : (1 : HermitianMat (n ⊕ n) ℂ) ∈ quatSubmodule (n := n) :=
  isQuaternionic_one

/-- `Φ` fixes the identity matrix (`J₀J₀ᵀ = 1`). -/
theorem quatConj_one : quatConj (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) = 1 := by
  unfold quatConj
  have h : (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).map (starRingEnd ℂ) = 1 := by
    ext i j
    simp [Matrix.one_apply, apply_ite]
  rw [h, Matrix.mul_one, symplecticJ_mul_transpose]

theorem quatConj_sub (A B : Matrix (n ⊕ n) (n ⊕ n) ℂ) :
    quatConj (A - B) = quatConj A - quatConj B := by
  unfold quatConj
  have hmap : (A - B).map (starRingEnd ℂ)
      = A.map (starRingEnd ℂ) - B.map (starRingEnd ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  rw [hmap]
  noncomm_ring

/-- **`Φ` fixes every power of a quaternionic matrix** — the polynomial half of the
functional-calculus closure.  With `Φ` continuous and additive, Weierstrass plus
`norm_cfc_sub_le_of_sup_le` then carry this to `cfc f` (the same skeleton as
`continuousOn_cfc_sqrt_effects`). -/
theorem quatConj_pow {A : HermitianMat (n ⊕ n) ℂ} (hA : IsQuaternionic A) (k : ℕ) :
    quatConj (A.mat ^ k) = A.mat ^ k := by
  induction k with
  | zero =>
    have h0 : A.mat ^ 0 = (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) := by simp
    rw [h0, quatConj_one]
  | succ k ih => rw [pow_succ, quatConj_mul, ih, hA]

/-- **`Φ` fixes every real matrix polynomial in a quaternionic matrix.**  Real
coefficients are self-conjugate, so the scalar homogeneity applies, and `quatConj_pow`
handles the powers. -/
theorem quatConj_aeval {A : HermitianMat (n ⊕ n) ℂ} (hA : IsQuaternionic A)
    (p : Polynomial ℝ) :
    quatConj (Polynomial.aeval A.mat (p.map (algebraMap ℝ ℂ)))
      = Polynomial.aeval A.mat (p.map (algebraMap ℝ ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, quatConj_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def]
    have hc : (starRingEnd ℂ) ((algebraMap ℝ ℂ) c) = (algebraMap ℝ ℂ) c := by
      simp [Complex.conj_ofReal]
    rw [quatConj_smul_of_conj_eq hc, quatConj_pow hA]

/-- `Φ` is continuous. -/
theorem quatConj_continuous :
    Continuous (quatConj (n := n)) := by
  unfold quatConj
  have hmap : Continuous fun A : Matrix (n ⊕ n) (n ⊕ n) ℂ => A.map (starRingEnd ℂ) := by
    apply continuous_matrix
    intro i j
    exact Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))
  apply Continuous.matrix_mul _ continuous_const
  exact Continuous.matrix_mul continuous_const hmap

/-! ## `Φ` preserves positivity -/

/-- For a Hermitian matrix, entrywise conjugation is transposition. -/
theorem map_conj_eq_transpose (A : HermitianMat (n ⊕ n) ℂ) :
    A.mat.map (starRingEnd ℂ) = A.matᵀ := by
  ext i j
  have h := congrFun (congrFun A.H j) i
  simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply] using h

/-- `J₀` is real, so its transpose is its conjugate transpose. -/
theorem symplecticJ_transpose_eq_conjTranspose :
    (symplecticJ (n := n))ᵀ = (symplecticJ (n := n))ᴴ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [symplecticJ, Matrix.fromBlocks, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, Matrix.one_apply, apply_ite]

/-- **`Φ` preserves positive semidefiniteness**: `Φ A = J₀ Aᵀ J₀ᴴ` for Hermitian `A`
(conjugation is transposition there, and `J₀` is real), which is a congruence. -/
theorem quatConj_posSemidef {A : HermitianMat (n ⊕ n) ℂ} (hA : A.mat.PosSemidef) :
    (quatConj A.mat).PosSemidef := by
  unfold quatConj
  rw [map_conj_eq_transpose, symplecticJ_transpose_eq_conjTranspose]
  exact hA.transpose.mul_mul_conjTranspose_same _

/-! ## `Φ` at the Hermitian level -/

/-- **`Φ` preserves Hermitian-ness.**  For Hermitian `A` it is the congruence
`J₀ Aᵀ J₀ᴴ`, and `Aᵀ` is Hermitian whenever `A` is, so the congruence is too.  This is
what lets the involution — and hence the whole ε-argument for the functional calculus —
live at the `HermitianMat` level, where the norm is. -/
theorem quatConj_isHermitian (A : HermitianMat (n ⊕ n) ℂ) :
    (quatConj A.mat).IsHermitian := by
  unfold quatConj
  rw [map_conj_eq_transpose, symplecticJ_transpose_eq_conjTranspose]
  have hT : (A.matᵀ).IsHermitian := by
    show (A.matᵀ)ᴴ = A.matᵀ
    rw [show (A.matᵀ)ᴴ = A.mat.map (starRingEnd ℂ) from by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]]
    exact map_conj_eq_transpose A
  show (symplecticJ * A.matᵀ * symplecticJᴴ)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hT]
  noncomm_ring

/-- **`Φ` as a self-map of `H_{2n}(ℂ)`** — the form in which the functional-calculus
closure should be stated and proved, because this carrier has a norm (bare `Matrix` does
not). -/
def quatConjH (A : HermitianMat (n ⊕ n) ℂ) : HermitianMat (n ⊕ n) ℂ :=
  ⟨quatConj A.mat, quatConj_isHermitian A⟩

@[simp]
theorem quatConjH_mat (A : HermitianMat (n ⊕ n) ℂ) :
    (quatConjH A).mat = quatConj A.mat := rfl

theorem quatConjH_add (A B : HermitianMat (n ⊕ n) ℂ) :
    quatConjH (A + B) = quatConjH A + quatConjH B := by
  ext1
  rw [quatConjH_mat, HermitianMat.mat_add, quatConj_add]
  rfl

theorem quatConjH_smul (r : ℝ) (A : HermitianMat (n ⊕ n) ℂ) :
    quatConjH (r • A) = r • quatConjH A := by
  ext1
  rw [quatConjH_mat, HermitianMat.mat_smul, quatConj_real_smul]
  rfl

/-- `Φ` at the Hermitian level, as an **ℝ-linear map** — so that finite-dimensionality
gives continuity and a norm bound for free, with no Frobenius computation. -/
def quatConjHLm : HermitianMat (n ⊕ n) ℂ →ₗ[ℝ] HermitianMat (n ⊕ n) ℂ where
  toFun := quatConjH
  map_add' := quatConjH_add
  map_smul' := quatConjH_smul

/-- **`Φ` is norm-bounded on `H_{2n}(ℂ)`**: an ℝ-linear map on a finite-dimensional
normed space is automatically continuous, hence bounded. -/
theorem quatConjH_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : HermitianMat (n ⊕ n) ℂ, ‖quatConjH A‖ ≤ K * ‖A‖ :=
  SemilinearMapClass.bound_of_continuous (quatConjHLm (n := n))
    (LinearMap.continuous_of_finiteDimensional _)

/-! ## Closure under the functional calculus -/

/-- **The quaternionic set is closed under the functional calculus.**  `Φ` fixes every
real matrix polynomial in `A` (`quatConj_aeval`, transported by the bridge
`mat_cfc_polynomial`), it is norm-bounded (`quatConjH_bound`), and Weierstrass makes
polynomials uniformly near `f` on the effect window `[0,1]` — so a three-ε estimate
against `norm_cfc_sub_le_of_sup_le` forces `Φ (A.cfc f) = A.cfc f`.

This is the last structural fact the `H_n(ℍ)` row needs: it is what lets the quaternionic
carrier carry `√a`, hence `Q_{√a}`, hence the whole Θ construction. -/
theorem IsQuaternionic.cfc_of_effect {A : HermitianMat (n ⊕ n) ℂ}
    (hA : IsQuaternionic A) (hAe : OrderUnitSpace.IsEffect A)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    quatConjH (A.cfc f) = A.cfc f := by
  obtain ⟨K, hK0, hK⟩ := quatConjH_bound (n := n)
  set c : ℝ := Real.sqrt (Fintype.card (n ⊕ n)) with hc
  have hcnn : 0 ≤ c := Real.sqrt_nonneg _
  have hall : ∀ ε : ℝ, 0 < ε → ‖quatConjH (A.cfc f) - A.cfc f‖ ≤ 0 + ε := by
    intro ε hε
    set δ : ℝ := ε / (2 * (K + 1) * (c + 1)) with hδ
    have hδpos : 0 < δ := by
      apply div_pos hε
      have h1 : (0 : ℝ) < K + 1 := by linarith
      have h2 : (0 : ℝ) < c + 1 := by linarith
      positivity
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδpos
    -- the approximant is uniformly close in the matrix norm
    have hclose : ‖A.cfc (fun x => p.eval x) - A.cfc f‖ ≤ c * δ :=
      HermitianMat.norm_cfc_sub_le_of_sup_le
        (HermitianMat.spectrum_subset_Icc_of_isEffect hAe) (le_of_lt hδpos)
        (fun x hx => le_of_lt (by simpa using hp x hx))
    -- and it is fixed by `Φ`
    have hfix : quatConjH (A.cfc (fun x => p.eval x)) = A.cfc (fun x => p.eval x) := by
      ext1
      rw [quatConjH_mat, HermitianMat.mat_cfc_polynomial]
      exact quatConj_aeval hA p
    -- `Φ` is ℝ-linear, so it commutes with the difference
    have hsub : quatConjH (A.cfc f) - quatConjH (A.cfc (fun x => p.eval x))
        = quatConjH (A.cfc f - A.cfc (fun x => p.eval x)) := by
      show quatConjHLm (A.cfc f) - quatConjHLm (A.cfc (fun x => p.eval x)) = _
      rw [← map_sub]
      rfl
    have hKd : ‖quatConjH (A.cfc f - A.cfc (fun x => p.eval x))‖ ≤ K * (c * δ) := by
      refine le_trans (hK _) ?_
      have hnorm : ‖A.cfc f - A.cfc (fun x => p.eval x)‖ ≤ c * δ := by
        rw [← norm_neg, neg_sub]
        exact hclose
      exact mul_le_mul_of_nonneg_left hnorm (le_of_lt hK0)
    calc ‖quatConjH (A.cfc f) - A.cfc f‖
        ≤ ‖quatConjH (A.cfc f) - quatConjH (A.cfc (fun x => p.eval x))‖
            + ‖quatConjH (A.cfc (fun x => p.eval x)) - A.cfc f‖ := by
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K * (c * δ) + c * δ := by
          rw [hsub]
          rw [hfix]
          exact add_le_add hKd hclose
      _ ≤ 0 + ε := by
          have hd : (K + 1) * (c + 1) * δ = ε / 2 := by
            rw [hδ]
            have h1 : (0 : ℝ) < K + 1 := by linarith
            have h2 : (0 : ℝ) < c + 1 := by linarith
            field_simp
          nlinarith [mul_nonneg hcnn (le_of_lt hδpos), le_of_lt hδpos, le_of_lt hK0]
  have h0 : ‖quatConjH (A.cfc f) - A.cfc f‖ ≤ 0 := le_of_forall_pos_le_add hall
  have := norm_le_zero_iff.mp h0
  rwa [sub_eq_zero] at this

/-! ## The quaternionic carrier as an order-unit space -/

section Carrier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quaternionic carrier: `H_n(ℍ)` realized as the symplectic-fixed subspace of
`H_{2n}(ℂ)`.  Its normed structure is inherited from the submodule and its order is the
restricted Loewner order — so nothing is built over a noncommutative ring. -/
abbrev QuatCarrier (n : Type*) [Fintype n] [DecidableEq n] : Type _ :=
  quatSubmodule (n := n)

/-- **The quaternionic carrier is an order-unit space.**  Every field is inherited from
`H_{2n}(ℂ)`: the order is the restriction, the unit is `1` (which is quaternionic), and
order-unit boundedness is the ambient bound intersected with the subspace.  This is the
carrier the `H_n(ℍ)` row's `SequentialProductOn` will live on. -/
instance : OrderUnitSpace (QuatCarrier n) where
  add_le_add_left := fun a b h c => by
    show (c : HermitianMat (n ⊕ n) ℂ) + a ≤ (c : HermitianMat (n ⊕ n) ℂ) + b
    exact add_le_add le_rfl h
  ousUnit := ⟨1, one_mem_quatSubmodule⟩
  smul_nonneg_mono := fun r hr {a b} h => by
    show r • (a : HermitianMat (n ⊕ n) ℂ) ≤ r • (b : HermitianMat (n ⊕ n) ℂ)
    exact OrderUnitSpace.smul_nonneg_mono r hr h
  ousUnit_nonneg := by
    show (0 : HermitianMat (n ⊕ n) ℂ) ≤ (1 : HermitianMat (n ⊕ n) ℂ)
    rw [← HermitianMat.ousUnit_eq_one]
    exact OrderUnitSpace.ousUnit_nonneg
  archimedean := fun a => by
    obtain ⟨r, hr0, hr⟩ := OrderUnitSpace.archimedean (a : HermitianMat (n ⊕ n) ℂ)
    refine ⟨r, hr0, ?_⟩
    show (a : HermitianMat (n ⊕ n) ℂ) ≤ r • (1 : HermitianMat (n ⊕ n) ℂ)
    rwa [HermitianMat.ousUnit_eq_one] at hr

@[simp]
theorem quatCarrier_ousUnit_coe :
    ((OrderUnitSpace.ousUnit : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ) = 1 := rfl

end Carrier

end HermitianMat
