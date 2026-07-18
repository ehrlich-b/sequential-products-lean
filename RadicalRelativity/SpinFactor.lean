/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.SequentialProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option linter.style.longLine false

/-!
# Spin Factor V₃: A Non-Commutative Sequential Product Space

The **spin factor** V₃ = ℝ × ℝ² is the simplest non-commutative Euclidean Jordan algebra,
isomorphic to M₂(ℝ)^sa (self-adjoint 2×2 real matrices). It provides a concrete
non-commutative instance of `SequentialProduct`, complementing the commutative
diagonal instance in `M2CInstance.lean`.

## Representation

An element `(a₀, a₁, a₂) : ℝ × ℝ × ℝ` corresponds to the self-adjoint matrix:

  ⎡ a₀ + a₂   a₁ ⎤
  ⎣   a₁    a₀ - a₂⎦

- `a₀` is the "trace part" (half-trace)
- `(a₁, a₂)` is the "Bloch vector"

## Structure

- **Unit**: `(1, 0, 0)` (the identity matrix)
- **Order**: `a ≥ 0` iff `a₀ ≥ 0` and `a₀² ≥ a₁² + a₂²` (positive semidefinite cone)
- **Jordan product**: `(a₀,a₁,a₂) ∘ (b₀,b₁,b₂) = (a₀b₀ + a₁b₁ + a₂b₂, a₀b₁ + b₀a₁, a₀b₂ + b₀a₂)`
- **Sequential product** (Lüders): `a & b = √a · b · √a` (matrix square root product)

## Non-commutativity

We exhibit explicit effects `a`, `b` with `a & b ≠ b & a`, proving V₃ is genuinely
non-commutative. Specifically, the projections `p = (1/2, 1/2, 0)` and
`q = (1/2, 0, 1/2)` do not commute.

## References

* Alfsen-Shultz, *Geometry of State Spaces of Operator Algebras*
* van de Wetering, arXiv:1803.11139, §5
-/

noncomputable section

open OrderUnitSpace

/-- The spin factor V₃, represented as triples `(a₀, a₁, a₂) : ℝ × ℝ × ℝ`. -/
abbrev SpinFactor := ℝ × ℝ × ℝ

namespace SpinFactor

/-- The squared norm of the Bloch vector: `a₁² + a₂²`. -/
def blochNormSq (a : SpinFactor) : ℝ := a.2.1 ^ 2 + a.2.2 ^ 2

/-- An element is positive semidefinite if `a₀ ≥ 0` and `a₀² ≥ a₁² + a₂²`. -/
def IsNonneg (a : SpinFactor) : Prop := 0 ≤ a.1 ∧ a.blochNormSq ≤ a.1 ^ 2

/-- The unit element `(1, 0, 0)`, corresponding to the 2×2 identity matrix. -/
def unit : SpinFactor := (1, 0, 0)

/-! ### Partial Order

We define `a ≤ b` iff `b - a` is in the positive semidefinite cone. -/

instance instLE : LE SpinFactor where
  le a b := IsNonneg (b - a)

instance instLT : LT SpinFactor where
  lt a b := a ≤ b ∧ ¬b ≤ a

theorem le_def (a b : SpinFactor) : a ≤ b ↔ IsNonneg (b - a) := Iff.rfl

private theorem le_refl' (a : SpinFactor) : a ≤ a := by
  refine ⟨?_, ?_⟩ <;> simp [blochNormSq]

private theorem le_antisymm' (a b : SpinFactor) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  obtain ⟨h1_tr, h1_bn⟩ : IsNonneg (b - a) := hab
  obtain ⟨h2_tr, h2_bn⟩ : IsNonneg (a - b) := hba
  simp only [blochNormSq, Prod.fst_sub, Prod.snd_sub] at *
  have h_tr : a.1 = b.1 := by linarith
  have h_bn_zero : (b.2.1 - a.2.1) ^ 2 + (b.2.2 - a.2.2) ^ 2 ≤ 0 := by
    have : b.1 - a.1 = 0 := by linarith
    nlinarith
  have hx : a.2.1 = b.2.1 := by nlinarith [sq_nonneg (b.2.1 - a.2.1), sq_nonneg (b.2.2 - a.2.2)]
  have hy : a.2.2 = b.2.2 := by nlinarith [sq_nonneg (b.2.1 - a.2.1), sq_nonneg (b.2.2 - a.2.2)]
  exact Prod.ext h_tr (Prod.ext hx hy)

private theorem le_trans' (a b c : SpinFactor) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  obtain ⟨h1_tr, h1_bn⟩ : IsNonneg (b - a) := hab
  obtain ⟨h2_tr, h2_bn⟩ : IsNonneg (c - b) := hbc
  constructor
  · simp only [Prod.fst_sub] at *; linarith
  · -- The Lorentz cone is closed under addition (triangle inequality).
    simp only [Prod.fst_sub] at h1_tr h2_tr
    simp only [blochNormSq, Prod.fst_sub, Prod.snd_sub] at h1_bn h2_bn ⊢
    -- Cauchy-Schwarz gives the cross-term bound
    have hcs : (b.2.1 - a.2.1) * (c.2.1 - b.2.1) + (b.2.2 - a.2.2) * (c.2.2 - b.2.2) ≤ (b.1 - a.1) * (c.1 - b.1) := by
      have cs_sq : ((b.2.1 - a.2.1) * (c.2.1 - b.2.1) + (b.2.2 - a.2.2) * (c.2.2 - b.2.2)) ^ 2 ≤
          ((b.1 - a.1) * (c.1 - b.1)) ^ 2 := by
        calc ((b.2.1 - a.2.1) * (c.2.1 - b.2.1) + (b.2.2 - a.2.2) * (c.2.2 - b.2.2)) ^ 2
            ≤ ((b.2.1 - a.2.1) ^ 2 + (b.2.2 - a.2.2) ^ 2) * ((c.2.1 - b.2.1) ^ 2 + (c.2.2 - b.2.2) ^ 2) := by
              nlinarith [sq_nonneg ((b.2.1 - a.2.1) * (c.2.2 - b.2.2) - (b.2.2 - a.2.2) * (c.2.1 - b.2.1))]
          _ ≤ (b.1 - a.1) ^ 2 * (c.1 - b.1) ^ 2 := by
              exact mul_le_mul h1_bn h2_bn
                (by nlinarith [sq_nonneg (c.2.1 - b.2.1), sq_nonneg (c.2.2 - b.2.2)])
                (by nlinarith [sq_nonneg (b.1 - a.1)])
          _ = ((b.1 - a.1) * (c.1 - b.1)) ^ 2 := by ring
      nlinarith [mul_nonneg h1_tr h2_tr, sq_nonneg ((b.1 - a.1) * (c.1 - b.1) - ((b.2.1 - a.2.1) * (c.2.1 - b.2.1) + (b.2.2 - a.2.2) * (c.2.2 - b.2.2)))]
    have h1 : c.2.1 - a.2.1 = (b.2.1 - a.2.1) + (c.2.1 - b.2.1) := by ring
    have h2 : c.2.2 - a.2.2 = (b.2.2 - a.2.2) + (c.2.2 - b.2.2) := by ring
    have h3 : c.1 - a.1 = (b.1 - a.1) + (c.1 - b.1) := by ring
    nlinarith [sq_nonneg (b.2.1 - a.2.1), sq_nonneg (c.2.1 - b.2.1), sq_nonneg (b.2.2 - a.2.2), sq_nonneg (c.2.2 - b.2.2)]

instance : PartialOrder SpinFactor where
  le := instLE.le
  lt := instLT.lt
  le_refl := le_refl'
  le_antisymm := le_antisymm'
  le_trans := le_trans'

/-! ### The Jordan Product

The Jordan product on V₃ is:
  `(a₀,a₁,a₂) ∘ (b₀,b₁,b₂) = (a₀b₀ + a₁b₁ + a₂b₂, a₀b₁ + b₀a₁, a₀b₂ + b₀a₂)`
-/

/-- The Jordan product on V₃. -/
def jordanMul (a b : SpinFactor) : SpinFactor :=
  (a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2,
   a.1 * b.2.1 + b.1 * a.2.1,
   a.1 * b.2.2 + b.1 * a.2.2)

theorem jordanMul_comm (a b : SpinFactor) : jordanMul a b = jordanMul b a := by
  simp only [jordanMul]
  ext <;> ring

theorem jordanMul_unit_left (a : SpinFactor) : jordanMul unit a = a := by
  simp only [jordanMul, unit]
  ext <;> simp

/-! ### Matrix Square Root

For a PSD element `a = (a₀, a₁, a₂)` with eigenvalues `λ± = a₀ ± r` where
`r = √(a₁² + a₂²)`, the square root has eigenvalues `√λ±` and the same eigenvectors.

Explicitly: `√a = (s₀, s₁, s₂)` where
  `s₀ = (√λ₊ + √λ₋) / 2`
  and `(s₁, s₂) = ((√λ₊ - √λ₋) / (2r)) · (a₁, a₂)` when `r > 0`
  or `(0, 0)` when `r = 0`.
-/

/-- The Bloch norm `r = √(a₁² + a₂²)`. -/
def blochNorm (a : SpinFactor) : ℝ := Real.sqrt a.blochNormSq

/-- The matrix square root of a PSD element of V₃. -/
def sqrtPSD (a : SpinFactor) : SpinFactor :=
  let r := blochNorm a
  let sqPlus := Real.sqrt (a.1 + r)
  let sqMinus := Real.sqrt (a.1 - r)
  let s₀ := (sqPlus + sqMinus) / 2
  if r = 0 then
    (s₀, 0, 0)
  else
    let scale := (sqPlus - sqMinus) / (2 * r)
    (s₀, scale * a.2.1, scale * a.2.2)

/-! ### The Sequential Product (Lüders Product)

The sequential product is `a & b = √a · b · √a`, computed via the 2×2 matrix
representation. An element `(a₀, a₁, a₂)` represents the symmetric matrix
`[[a₀ + a₂, a₁], [a₁, a₀ - a₂]]`. The triple product `SBS` of symmetric
matrices is symmetric, so the result lives in V₃.
-/

/-- Triple matrix product `S · B · S` in spin factor coordinates.
Given `S = [[s₀+s₂, s₁], [s₁, s₀-s₂]]` and `B = [[b₀+b₂, b₁], [b₁, b₀-b₂]]`,
computes `SBS` and reads off spin factor components. -/
def matTripleProd (s b : SpinFactor) : SpinFactor :=
  let s₀ := s.1; let s₁ := s.2.1; let s₂ := s.2.2
  let b₀ := b.1; let b₁ := b.2.1; let b₂ := b.2.2
  let sb11 := (s₀ + s₂) * (b₀ + b₂) + s₁ * b₁
  let sb12 := (s₀ + s₂) * b₁ + s₁ * (b₀ - b₂)
  let sb21 := s₁ * (b₀ + b₂) + (s₀ - s₂) * b₁
  let sb22 := s₁ * b₁ + (s₀ - s₂) * (b₀ - b₂)
  let m11 := sb11 * (s₀ + s₂) + sb12 * s₁
  let m12 := sb11 * s₁ + sb12 * (s₀ - s₂)
  let m22 := sb21 * s₁ + sb22 * (s₀ - s₂)
  ((m11 + m22) / 2, m12, (m11 - m22) / 2)

/-- The Lüders sequential product: `a & b = √a · b · √a`. -/
def seqProd (a b : SpinFactor) : SpinFactor :=
  matTripleProd (sqrtPSD a) b

/-! ### Non-commutativity

We exhibit two rank-1 projections in V₃ whose sequential product does not commute.

- `p = (1/2, 1/2, 0)` projects onto `|+⟩` (σ₁ eigenstate)
- `q = (1/2, 0, 1/2)` projects onto `|↑⟩` (σ₃ eigenstate)

For rank-1 projections, `√p = p` (eigenvalues 0 and 1), so `p & q = PQP`.

Matrix computation:
- P = [[1/2, 1/2], [1/2, 1/2]], Q = [[1, 0], [0, 0]]
- PQP = [[1/4, 1/4], [1/4, 1/4]] ↔ (1/4, 1/4, 0)
- QPQ = [[1/2, 0], [0, 0]] ↔ (1/4, 0, 1/4)
-/

def projPlus : SpinFactor := ((1 : ℝ)/2, (1 : ℝ)/2, (0 : ℝ))
def projUp : SpinFactor := ((1 : ℝ)/2, (0 : ℝ), (1 : ℝ)/2)

/-- `projPlus` is a rank-1 projection: `a₀² = a₁² + a₂²`. -/
theorem projPlus_is_projection : projPlus.1 ^ 2 = projPlus.blochNormSq := by
  simp [projPlus, blochNormSq]

/-- `projUp` is a rank-1 projection: `a₀² = a₁² + a₂²`. -/
theorem projUp_is_projection : projUp.1 ^ 2 = projUp.blochNormSq := by
  simp [projUp, blochNormSq]

/-- The square root of a rank-1 projection is itself.
This follows from eigenvalues being 0 and 1, so `√0 = 0` and `√1 = 1`. -/
theorem sqrtPSD_proj_plus : sqrtPSD projPlus = projPlus := by
  simp only [sqrtPSD, projPlus, blochNorm, blochNormSq]
  have key : ((1:ℝ)/2) ^ 2 + (0:ℝ) ^ 2 = 1/4 := by norm_num
  have h_sqrt_quarter : Real.sqrt (1/4 : ℝ) = 1/2 := by
    rw [show (1:ℝ)/4 = (1/2 : ℝ) * (1/2) from by ring]
    exact (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr rfl
  have h_bnorm : Real.sqrt (((1:ℝ)/2) ^ 2 + (0:ℝ) ^ 2) = 1/2 := by
    rw [key, h_sqrt_quarter]
  rw [h_bnorm]
  simp only [if_neg (show (1:ℝ)/2 ≠ 0 from by norm_num)]
  norm_num [Real.sqrt_one, Real.sqrt_zero]

theorem sqrtPSD_proj_up : sqrtPSD projUp = projUp := by
  simp only [sqrtPSD, projUp, blochNorm, blochNormSq]
  have key : ((0:ℝ)) ^ 2 + ((1:ℝ)/2) ^ 2 = 1/4 := by norm_num
  have h_sqrt_quarter : Real.sqrt (1/4 : ℝ) = 1/2 := by
    rw [show (1:ℝ)/4 = (1/2 : ℝ) * (1/2) from by ring]
    exact (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr rfl
  have h_bnorm : Real.sqrt ((0:ℝ) ^ 2 + ((1:ℝ)/2) ^ 2) = 1/2 := by
    rw [key, h_sqrt_quarter]
  rw [h_bnorm]
  simp only [if_neg (show (1:ℝ)/2 ≠ 0 from by norm_num)]
  norm_num [Real.sqrt_one, Real.sqrt_zero]

/-- `p & q = (1/4, 1/4, 0)`. -/
theorem seqProd_projPlus_projUp :
    seqProd projPlus projUp = ((1 : ℝ)/4, (1 : ℝ)/4, (0 : ℝ)) := by
  unfold seqProd
  rw [sqrtPSD_proj_plus]
  simp only [matTripleProd, projPlus, projUp]
  norm_num

/-- `q & p = (1/4, 0, 1/4)`. -/
theorem seqProd_projUp_projPlus :
    seqProd projUp projPlus = ((1 : ℝ)/4, (0 : ℝ), (1 : ℝ)/4) := by
  unfold seqProd
  rw [sqrtPSD_proj_up]
  simp only [matTripleProd, projUp, projPlus]
  norm_num

/-- **Non-commutativity**: The sequential product on V₃ is not commutative.
    `p & q ≠ q & p` for the projections p = (1/2, 1/2, 0), q = (1/2, 0, 1/2). -/
theorem seqProd_noncommutative : seqProd projPlus projUp ≠ seqProd projUp projPlus := by
  rw [seqProd_projPlus_projUp, seqProd_projUp_projPlus]
  intro h
  have : ((1 : ℝ)/4, (1 : ℝ)/4, (0 : ℝ)).2.1 = ((1 : ℝ)/4, (0 : ℝ), (1 : ℝ)/4).2.1 := by
    exact congrArg (fun p => p.2.1) h
  simp at this

/-! ### OrderUnitSpace instance -/

instance : OrderUnitSpace SpinFactor where
  add_le_add_left := by
    intro a b hab c
    obtain ⟨h_tr, h_bn⟩ := hab
    constructor
    · -- 0 ≤ (c + b - (c + a)).1 = b.1 - a.1
      have : (c + b - (c + a)).1 = b.1 - a.1 := by simp only [Prod.fst_sub, Prod.fst_add]; ring
      rw [this]; exact h_tr
    · -- blochNormSq (c + b - (c + a)) = blochNormSq (b - a)
      have h1 : (c + b - (c + a)).1 = (b - a).1 := by simp only [Prod.fst_sub, Prod.fst_add]; ring
      have h21 : (c + b - (c + a)).2.1 = (b - a).2.1 := by simp only [Prod.snd_sub, Prod.snd_add, Prod.fst_sub, Prod.fst_add]; ring
      have h22 : (c + b - (c + a)).2.2 = (b - a).2.2 := by simp only [Prod.snd_sub, Prod.snd_add]; ring
      simp only [blochNormSq, h1, h21, h22]; exact h_bn
  ousUnit := unit
  smul_nonneg_mono := by
    intro r hr a b hab
    obtain ⟨h_tr, h_bn⟩ := hab
    constructor
    · have : (r • b - r • a).1 = r * (b.1 - a.1) := by
        simp [Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; ring
      rw [this]; exact mul_nonneg hr h_tr
    · simp only [blochNormSq, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at *
      nlinarith [sq_nonneg r, sq_nonneg (b.2.1 - a.2.1), sq_nonneg (b.2.2 - a.2.2), sq_nonneg (b.1 - a.1), mul_self_nonneg r]
  ousUnit_nonneg := by
    refine ⟨by norm_num [unit], by simp [blochNormSq, unit]⟩
  archimedean := by
    intro a
    exact ⟨|a.1| + |a.2.1| + |a.2.2| + 1, by positivity, by
      constructor
      · simp [unit, Prod.fst_sub, smul_eq_mul]
        linarith [abs_nonneg a.1, abs_nonneg a.2.1, abs_nonneg a.2.2, le_abs_self a.1]
      · simp only [blochNormSq, unit, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
        simp
        nlinarith [sq_abs a.1, sq_abs a.2.1, sq_abs a.2.2, abs_nonneg a.1, abs_nonneg a.2.1, abs_nonneg a.2.2, le_abs_self a.1, sq_nonneg (|a.2.1| * |a.2.2|)]⟩

/-! ### Helper lemmas for the sequential product axioms -/

/-- The square root of the unit `(1,0,0)` is itself. -/
theorem sqrtPSD_unit : sqrtPSD unit = unit := by
  simp only [sqrtPSD, unit, blochNorm, blochNormSq]
  norm_num [Real.sqrt_one, Real.sqrt_zero]

/-- The matrix triple product `matTripleProd` is additive in its second argument. -/
theorem matTripleProd_add_right (s b c : SpinFactor) :
    matTripleProd s (b + c) = matTripleProd s b + matTripleProd s c := by
  simp only [matTripleProd]
  ext <;> simp <;> ring

/-- The matrix triple product with the unit on the left is the identity. -/
theorem matTripleProd_unit_left (b : SpinFactor) : matTripleProd unit b = b := by
  simp only [matTripleProd, unit]
  ext <;> simp

/-- The trace (first component) of `matTripleProd s b` equals `(s₀²+s₁²+s₂²)b₀+2s₀s₁b₁+2s₀s₂b₂`. -/
theorem matTripleProd_fst (s b : SpinFactor) :
    (matTripleProd s b).1 = (s.1^2 + s.2.1^2 + s.2.2^2) * b.1 + 2*s.1*s.2.1*b.2.1 + 2*s.1*s.2.2*b.2.2 := by
  simp only [matTripleProd]; ring

/-- The determinant identity: `det(SBS) = det(S)² · det(B)` in spin factor coordinates. -/
theorem matTripleProd_det (s b : SpinFactor) :
    (matTripleProd s b).1^2 - (matTripleProd s b).2.1^2 - (matTripleProd s b).2.2^2 =
    (s.1^2 - s.2.1^2 - s.2.2^2)^2 * (b.1^2 - b.2.1^2 - b.2.2^2) := by
  simp only [matTripleProd]; ring

/-- The first component of `matTripleProd s unit` equals `s₀²+s₁²+s₂²`. -/
theorem matTripleProd_unit_right (s : SpinFactor) :
    matTripleProd s unit = (s.1^2 + s.2.1^2 + s.2.2^2, 2*s.1*s.2.1, 2*s.1*s.2.2) := by
  simp only [matTripleProd, unit]
  ext <;> simp <;> ring

/-- Congruence preserves PSD: if `s` and `b` are PSD, then `matTripleProd s b` is PSD. -/
theorem matTripleProd_nonneg (s b : SpinFactor) (hs : IsNonneg s) (hb : IsNonneg b) :
    IsNonneg (matTripleProd s b) := by
  have hs_bn : s.2.1^2 + s.2.2^2 ≤ s.1^2 := hs.2
  have hb_bn : b.2.1^2 + b.2.2^2 ≤ b.1^2 := hb.2
  constructor
  · rw [matTripleProd_fst]
    by_cases hd : 0 ≤ s.2.1 * b.2.1 + s.2.2 * b.2.2
    · have h1 : 0 ≤ (s.1^2 + s.2.1^2 + s.2.2^2) * b.1 :=
        mul_nonneg (by nlinarith [sq_nonneg s.1, sq_nonneg s.2.1, sq_nonneg s.2.2]) hb.1
      linarith [mul_nonneg hs.1 hd]
    · push_neg at hd
      have hA_nn : 0 ≤ (s.1^2 + s.2.1^2 + s.2.2^2) * b.1 :=
        mul_nonneg (by nlinarith [sq_nonneg s.1, sq_nonneg s.2.1, sq_nonneg s.2.2]) hb.1
      have hcs_prod : (s.2.1*b.2.1 + s.2.2*b.2.2)^2 ≤ (s.2.1^2+s.2.2^2)*b.1^2 := by
        calc (s.2.1*b.2.1 + s.2.2*b.2.2)^2
            ≤ (s.2.1^2+s.2.2^2)*(b.2.1^2+b.2.2^2) := by nlinarith [sq_nonneg (s.2.1*b.2.2 - s.2.2*b.2.1)]
          _ ≤ (s.2.1^2+s.2.2^2)*b.1^2 := by nlinarith [sq_nonneg s.2.1, sq_nonneg s.2.2]
      nlinarith [sq_nonneg (s.1^2 - (s.2.1^2+s.2.2^2)), sq_nonneg b.1,
                 sq_nonneg ((s.1^2+s.2.1^2+s.2.2^2)*b.1 + 2*s.1*(s.2.1*b.2.1+s.2.2*b.2.2))]
  · simp only [blochNormSq]
    linarith [matTripleProd_det s b, mul_nonneg (sq_nonneg (s.1^2 - s.2.1^2 - s.2.2^2))
      (show 0 ≤ b.1^2 - b.2.1^2 - b.2.2^2 by linarith)]

/-- The square root of a PSD element is PSD. -/
theorem sqrtPSD_nonneg (a : SpinFactor) (ha : IsNonneg a) :
    IsNonneg (sqrtPSD a) := by
  unfold sqrtPSD blochNorm
  set r := Real.sqrt a.blochNormSq
  have h_bns_nn : 0 ≤ a.blochNormSq := by unfold blochNormSq; positivity
  have h_r_nn : 0 ≤ r := Real.sqrt_nonneg _
  have h_a1_ge_r : r ≤ a.1 := by rw [← Real.sqrt_sq ha.1]; exact Real.sqrt_le_sqrt ha.2
  have hsqP_nn : 0 ≤ Real.sqrt (a.1 + r) := Real.sqrt_nonneg _
  have hsqM_nn : 0 ≤ Real.sqrt (a.1 - r) := Real.sqrt_nonneg _
  by_cases hr0 : r = 0
  · simp only [hr0, ite_true]
    exact ⟨by positivity, by simp [blochNormSq]⟩
  · simp only [hr0, ite_false]
    have h_r_pos : 0 < r := lt_of_le_of_ne h_r_nn (Ne.symm hr0)
    constructor
    · change 0 ≤ (Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) / 2; linarith
    · simp only [blochNormSq]
      have key : ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.1) ^ 2 +
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.2) ^ 2 =
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r)) ^ 2 * a.blochNormSq := by
        unfold blochNormSq; ring
      rw [key, ← Real.sq_sqrt h_bns_nn]
      have goal_eq : ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r)) ^ 2 * r ^ 2 =
          (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) ^ 2 / 4 := by
        field_simp; ring
      rw [goal_eq, div_pow, show (2 : ℝ) ^ 2 = 4 from by norm_num]
      exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hsqP_nn hsqM_nn]) (by norm_num : (0:ℝ) ≤ 4)

/-- `seqProd a unit = a` for PSD `a`: the sequential product with the unit is the identity. -/
theorem seqProd_unit_right (a : SpinFactor) (ha : IsNonneg a) :
    seqProd a unit = a := by
  unfold seqProd
  rw [matTripleProd_unit_right]
  unfold sqrtPSD blochNorm
  set r := Real.sqrt a.blochNormSq
  have h_bns_nn : 0 ≤ a.blochNormSq := by unfold blochNormSq; positivity
  have h_r_nn : 0 ≤ r := Real.sqrt_nonneg _
  have h_a1_ge_r : r ≤ a.1 := by rw [← Real.sqrt_sq ha.1]; exact Real.sqrt_le_sqrt ha.2
  have hsqP_sq : Real.sqrt (a.1 + r) ^ 2 = a.1 + r := Real.sq_sqrt (by linarith)
  have hsqM_sq : Real.sqrt (a.1 - r) ^ 2 = a.1 - r := Real.sq_sqrt (by linarith)
  by_cases hr0 : r = 0
  · simp only [hr0, ite_true]
    have h_bns_zero : a.blochNormSq = 0 := by
      have h_r_sq : r ^ 2 = a.blochNormSq := Real.sq_sqrt h_bns_nn
      linarith [show r ^ 2 = 0 from by rw [hr0]; ring]
    have h1 : a.2.1 = 0 := by nlinarith [sq_nonneg a.2.1, sq_nonneg a.2.2, show a.blochNormSq = a.2.1 ^ 2 + a.2.2 ^ 2 from rfl]
    have h2 : a.2.2 = 0 := by nlinarith [sq_nonneg a.2.1, sq_nonneg a.2.2, show a.blochNormSq = a.2.1 ^ 2 + a.2.2 ^ 2 from rfl]
    simp only [show a.1 + (0:ℝ) = a.1 from by ring, show a.1 - (0:ℝ) = a.1 from by ring]
    ext
    · simp; ring_nf; rw [Real.sq_sqrt ha.1]
    · simp; exact h1.symm
    · simp; exact h2.symm
  · simp only [hr0, ite_false]
    have h_r_pos : 0 < r := lt_of_le_of_ne h_r_nn (Ne.symm hr0)
    have h_scale : (Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) * (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) = 2 * r := by
      nlinarith [hsqP_sq, hsqM_sq]
    ext
    · simp only
      have : ((Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) / 2) ^ 2 +
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.1) ^ 2 +
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.2) ^ 2 =
          ((Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) / 2) ^ 2 +
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r)) ^ 2 * a.blochNormSq := by
        unfold blochNormSq; ring
      rw [this, ← Real.sq_sqrt h_bns_nn]
      field_simp
      nlinarith [hsqP_sq, hsqM_sq, sq_nonneg (Real.sqrt (a.1 + r)), sq_nonneg (Real.sqrt (a.1 - r)), sq_nonneg r]
    · simp only
      have : 2 * ((Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) / 2) *
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.1) =
          (Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) * (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.1 := by ring
      rw [this, h_scale]; field_simp
    · simp only
      have : 2 * ((Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) / 2) *
          ((Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.2) =
          (Real.sqrt (a.1 + r) + Real.sqrt (a.1 - r)) * (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.2 := by ring
      rw [this, h_scale]; field_simp

/-! ### Key identities for sqrtPSD and matTripleProd commutativity -/

/-- For PSD `a`, the sqrtPSD satisfies: `s₀² + s₁² + s₂² = a₀`, `2s₀s₁ = a₁`, `2s₀s₂ = a₂`.
    These follow from `seqProd a unit = a`. -/
theorem sqrtPSD_squares (a : SpinFactor) (ha : IsNonneg a) :
    let s := sqrtPSD a
    s.1^2 + s.2.1^2 + s.2.2^2 = a.1 ∧
    2 * s.1 * s.2.1 = a.2.1 ∧
    2 * s.1 * s.2.2 = a.2.2 := by
  have h := seqProd_unit_right a ha
  simp only [seqProd] at h
  rw [matTripleProd_unit_right] at h
  exact ⟨by have := congrArg Prod.fst h; simpa using this,
         by have := congrArg (fun p => p.2.1) h; simpa using this,
         by have := congrArg (fun p => p.2.2) h; simpa using this⟩

/-- The matrix triple product `matTripleProd` is subtractive in its second argument. -/
theorem matTripleProd_sub_right (s b c : SpinFactor) :
    matTripleProd s (b - c) = matTripleProd s b - matTripleProd s c := by
  simp only [matTripleProd]
  ext <;> simp <;> ring

/-- The matrix triple product `matTripleProd` scales linearly in its second argument. -/
theorem matTripleProd_smul_right (s b : SpinFactor) (r : ℝ) :
    matTripleProd s (r • b) = r • matTripleProd s b := by
  simp only [matTripleProd]
  ext <;> simp [smul_eq_mul] <;> ring

/-- Expanded second component of matTripleProd. -/
theorem matTripleProd_snd_fst (s b : SpinFactor) :
    (matTripleProd s b).2.1 =
    2 * s.1 * s.2.1 * b.1 + (s.1^2 + s.2.1^2 - s.2.2^2) * b.2.1 +
    2 * s.2.1 * s.2.2 * b.2.2 := by
  simp only [matTripleProd]; ring

/-- Expanded third component of matTripleProd. -/
theorem matTripleProd_snd_snd (s b : SpinFactor) :
    (matTripleProd s b).2.2 =
    2 * s.1 * s.2.2 * b.1 + 2 * s.2.1 * s.2.2 * b.2.1 +
    (s.1^2 - s.2.1^2 + s.2.2^2) * b.2.2 := by
  simp only [matTripleProd]; ring

/-- When `s₀² + s₁² + s₂² = a₀` and `2s₀s₁ = a₁` and `2s₀s₂ = a₂`, the second
    component of `matTripleProd s b` can be expressed as `a₁b₀ + a₀b₁ + 2s₂(s₁b₂ - s₂b₁)`. -/
theorem matTripleProd_snd_fst_of_sqrt (s b a : SpinFactor)
    (hsum : s.1^2 + s.2.1^2 + s.2.2^2 = a.1)
    (hprod1 : 2 * s.1 * s.2.1 = a.2.1) (hprod2 : 2 * s.1 * s.2.2 = a.2.2) :
    (matTripleProd s b).2.1 =
    a.2.1 * b.1 + a.1 * b.2.1 + 2 * s.2.2 * (s.2.1 * b.2.2 - s.2.2 * b.2.1) := by
  rw [matTripleProd_snd_fst, ← hsum, ← hprod1]
  ring

/-- When `s₀² + s₁² + s₂² = a₀` and `2s₀s₁ = a₁` and `2s₀s₂ = a₂`, the third
    component of `matTripleProd s b` can be expressed as `a₂b₀ + a₀b₂ - 2s₁(s₁b₂ - s₂b₁)`. -/
theorem matTripleProd_snd_snd_of_sqrt (s b a : SpinFactor)
    (hsum : s.1^2 + s.2.1^2 + s.2.2^2 = a.1)
    (hprod1 : 2 * s.1 * s.2.1 = a.2.1) (hprod2 : 2 * s.1 * s.2.2 = a.2.2) :
    (matTripleProd s b).2.2 =
    a.2.2 * b.1 + a.1 * b.2.2 - 2 * s.2.1 * (s.2.1 * b.2.2 - s.2.2 * b.2.1) := by
  rw [matTripleProd_snd_snd, ← hsum, ← hprod2]
  ring

/-- When `s₀² + s₁² + s₂² = a₀` and `2s₀s₁ = a₁` and `2s₀s₂ = a₂`, the first
    component of `matTripleProd s b` equals `a₀b₀ + a₁b₁ + a₂b₂`. -/
theorem matTripleProd_fst_of_sqrt (s b a : SpinFactor)
    (hsum : s.1^2 + s.2.1^2 + s.2.2^2 = a.1)
    (hprod1 : 2 * s.1 * s.2.1 = a.2.1) (hprod2 : 2 * s.1 * s.2.2 = a.2.2) :
    (matTripleProd s b).1 = a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2 := by
  rw [matTripleProd_fst, ← hsum, ← hprod1, ← hprod2]

/-- The difference `seqProd a b - seqProd b a` has zero first component,
    and the Bloch components are multiples of `a₁b₂ - a₂b₁`. -/
theorem seqProd_comm_diff (a b : SpinFactor) (ha : IsNonneg a) (hb : IsNonneg b) :
    (seqProd a b).1 = (seqProd b a).1 := by
  simp only [seqProd]
  obtain ⟨hsa, hpa1, hpa2⟩ := sqrtPSD_squares a ha
  obtain ⟨hsb, hpb1, hpb2⟩ := sqrtPSD_squares b hb
  rw [matTripleProd_fst_of_sqrt _ _ a hsa hpa1 hpa2,
      matTripleProd_fst_of_sqrt _ _ b hsb hpb1 hpb2]
  ring

set_option maxHeartbeats 800000 in
/-- Key lemma: if seqProd a b = seqProd b a for PSD a, b, then `a₁b₂ = a₂b₁`. -/
theorem seqProd_comm_implies_bloch_parallel (a b : SpinFactor) (ha : IsNonneg a) (hb : IsNonneg b)
    (hcomm : seqProd a b = seqProd b a) :
    a.2.1 * b.2.2 = a.2.2 * b.2.1 := by
  obtain ⟨hsa, hpa1, hpa2⟩ := sqrtPSD_squares a ha
  obtain ⟨hsb, hpb1, hpb2⟩ := sqrtPSD_squares b hb
  -- Extract component equalities from hcomm
  have h21 := congrArg (fun p => p.2.1) hcomm
  have h22 := congrArg (fun p => p.2.2) hcomm
  simp only [seqProd] at h21 h22
  rw [matTripleProd_snd_fst_of_sqrt _ _ a hsa hpa1 hpa2,
      matTripleProd_snd_fst_of_sqrt _ _ b hsb hpb1 hpb2] at h21
  rw [matTripleProd_snd_snd_of_sqrt _ _ a hsa hpa1 hpa2,
      matTripleProd_snd_snd_of_sqrt _ _ b hsb hpb1 hpb2] at h22
  -- Use linear_combination to extract Q*D=S*E and P*D=R*E from h21,h22
  have hc1 : (sqrtPSD a).2.2 * ((sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1) =
             (sqrtPSD b).2.2 * ((sqrtPSD b).2.1 * a.2.2 - (sqrtPSD b).2.2 * a.2.1) := by
    linear_combination h21 / 2
  have hc2 : (sqrtPSD a).2.1 * ((sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1) =
             (sqrtPSD b).2.1 * ((sqrtPSD b).2.1 * a.2.2 - (sqrtPSD b).2.2 * a.2.1) := by
    linear_combination -h22 / 2
  -- Cross-multiply R*hc1 - S*hc2 gives (RQ-SP)*D = 0
  have h_cross : ((sqrtPSD b).2.1 * (sqrtPSD a).2.2 - (sqrtPSD b).2.2 * (sqrtPSD a).2.1) *
      ((sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1) = 0 := by
    linear_combination (sqrtPSD b).2.1 * hc1 - (sqrtPSD b).2.2 * hc2
  -- D = 2*sb₀*(PS-QR): substitute b₁, b₂ using hpb1, hpb2
  have hD : (sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1 =
      2 * (sqrtPSD b).1 * ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1) := by
    rw [← hpb1, ← hpb2]; ring
  -- sb₀*(PS-QR)² = 0: from h_cross and hD
  -- h_cross: (RQ-SP)*D = 0, hD: D = 2*sb₀*(PS-QR)
  -- Substituting: (RQ-SP)*2*sb₀*(PS-QR) = 0
  -- Note: (RQ-SP) = -(PS-QR), so -2*sb₀*(PS-QR)² = 0
  have h_key : (sqrtPSD b).1 * ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1) ^ 2 = 0 := by
    have := hD ▸ h_cross  -- substitute hD into h_cross
    nlinarith [sq_nonneg ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1)]
  -- a₁b₂ - a₂b₁ = 4*sa₀*sb₀*(PS-QR)
  have h_goal : a.2.1 * b.2.2 - a.2.2 * b.2.1 =
      4 * (sqrtPSD a).1 * (sqrtPSD b).1 * ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1) := by
    rw [← hpa1, ← hpa2, ← hpb1, ← hpb2]; ring
  -- Case split on sb₀
  have h_sb_nn := (sqrtPSD_nonneg b hb).1
  rcases eq_or_lt_of_le h_sb_nn with hsb0 | hsb_pos
  · -- sb₀ = 0 → b₁ = 0, b₂ = 0
    have hb1 : b.2.1 = 0 := by rw [← hpb1]; simp [show (sqrtPSD b).1 = 0 from hsb0.symm]
    have hb2 : b.2.2 = 0 := by rw [← hpb2]; simp [show (sqrtPSD b).1 = 0 from hsb0.symm]
    simp [hb1, hb2]
  · have hne : (sqrtPSD b).1 ≠ 0 := ne_of_gt hsb_pos
    have : ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h_key with h | h
      · exact absurd h hne
      · exact h
    have hcross0 : (sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1 = 0 := by
      nlinarith [sq_nonneg ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1)]
    linear_combination h_goal + 4 * (sqrtPSD a).1 * (sqrtPSD b).1 * hcross0

/-- The sqrtPSD preserves the Bloch direction: sa₁b₂ - sa₂b₁ = 0 when a₁b₂ = a₂b₁. -/
theorem sqrtPSD_bloch_parallel (a b : SpinFactor)
    (hpar : a.2.1 * b.2.2 = a.2.2 * b.2.1) :
    (sqrtPSD a).2.1 * b.2.2 = (sqrtPSD a).2.2 * b.2.1 := by
  unfold sqrtPSD blochNorm
  set r := Real.sqrt a.blochNormSq
  by_cases hr : r = 0
  · simp [hr]
  · simp only [hr, ite_false]
    show (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.1 * b.2.2 =
         (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * a.2.2 * b.2.1
    have h0 : a.2.1 * b.2.2 = a.2.2 * b.2.1 := hpar
    linear_combination (Real.sqrt (a.1 + r) - Real.sqrt (a.1 - r)) / (2 * r) * h0

/-- Converse: if `a₁b₂ = a₂b₁`, then `seqProd a b = seqProd b a` for PSD elements. -/
theorem seqProd_comm_of_bloch_parallel (a b : SpinFactor) (ha : IsNonneg a) (hb : IsNonneg b)
    (hpar : a.2.1 * b.2.2 = a.2.2 * b.2.1) :
    seqProd a b = seqProd b a := by
  obtain ⟨hsa, hpa1, hpa2⟩ := sqrtPSD_squares a ha
  obtain ⟨hsb, hpb1, hpb2⟩ := sqrtPSD_squares b hb
  have hsa_par := sqrtPSD_bloch_parallel a b hpar
  have hpar' : b.2.1 * a.2.2 = b.2.2 * a.2.1 := by linarith
  have hsb_par := sqrtPSD_bloch_parallel b a hpar'
  have hsa_zero : (sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1 = 0 := by linarith
  have hsb_zero : (sqrtPSD b).2.1 * a.2.2 - (sqrtPSD b).2.2 * a.2.1 = 0 := by linarith
  simp only [seqProd]
  ext
  · rw [matTripleProd_fst_of_sqrt _ _ a hsa hpa1 hpa2,
        matTripleProd_fst_of_sqrt _ _ b hsb hpb1 hpb2]; ring
  · rw [matTripleProd_snd_fst_of_sqrt _ _ a hsa hpa1 hpa2,
        matTripleProd_snd_fst_of_sqrt _ _ b hsb hpb1 hpb2]
    linear_combination 2 * (sqrtPSD a).2.2 * hsa_zero - 2 * (sqrtPSD b).2.2 * hsb_zero
  · rw [matTripleProd_snd_snd_of_sqrt _ _ a hsa hpa1 hpa2,
        matTripleProd_snd_snd_of_sqrt _ _ b hsb hpb1 hpb2]
    linear_combination -2 * (sqrtPSD a).2.1 * hsa_zero + 2 * (sqrtPSD b).2.1 * hsb_zero

set_option maxHeartbeats 400000 in
theorem sqrtPSD_zero : sqrtPSD (0, 0, 0) = (0, 0, 0) := by
  unfold sqrtPSD blochNorm blochNormSq; simp [Real.sqrt_zero]

theorem matTripleProd_zero_left (b : SpinFactor) : matTripleProd (0, 0, 0) b = (0, 0, 0) := by
  simp only [matTripleProd]; ext <;> ring

theorem seqProd_zero_left (a : SpinFactor) : seqProd (0, 0, 0) a = 0 := by
  show matTripleProd (sqrtPSD (0, 0, 0)) a = 0
  rw [sqrtPSD_zero, show (0 : SpinFactor) = ((0 : ℝ), (0 : ℝ), (0 : ℝ)) from rfl]
  exact matTripleProd_zero_left a

theorem seqProd_zero_right (a : SpinFactor) : seqProd a (0, 0, 0) = 0 := by
  show matTripleProd (sqrtPSD a) (0, 0, 0) = 0
  simp only [matTripleProd]; ext <;> simp <;> ring

/-- If seqProd a b = 0 for PSD a, b with a₀ > 0 and b₀ > 0, then Bloch vectors are parallel. -/
theorem bloch_parallel_of_seqProd_zero (a b : SpinFactor) (ha : IsNonneg a) (hb : IsNonneg b)
    (ha_pos : 0 < a.1) (hb_pos : 0 < b.1) (h0 : seqProd a b = 0) :
    a.2.1 * b.2.2 = a.2.2 * b.2.1 := by
  obtain ⟨hsa, hpa1, hpa2⟩ := sqrtPSD_squares a ha
  have h0_eq : matTripleProd (sqrtPSD a) b = 0 := by simp only [seqProd] at h0; exact h0
  have h0_1 : (matTripleProd (sqrtPSD a) b).1 = 0 := congrArg Prod.fst h0_eq
  rw [matTripleProd_fst_of_sqrt _ _ a hsa hpa1 hpa2] at h0_1
  -- h0_1: a₀b₀ + a₁b₁ + a₂b₂ = 0
  have h_inner : a.2.1 * b.2.1 + a.2.2 * b.2.2 = -(a.1 * b.1) := by linarith
  -- Cauchy-Schwarz: (a₁b₁+a₂b₂)² ≤ (a₁²+a₂²)(b₁²+b₂²)
  -- Light cone: (a₁²+a₂²)(b₁²+b₂²) ≤ a₀²b₀²
  -- Combining: (a₁b₂-a₂b₁)² = 0
  have hpar_sq : (a.2.1 * b.2.2 - a.2.2 * b.2.1) ^ 2 = 0 := by
    have hcs : (a.2.1 * b.2.1 + a.2.2 * b.2.2) ^ 2 ≤
        (a.2.1 ^ 2 + a.2.2 ^ 2) * (b.2.1 ^ 2 + b.2.2 ^ 2) := by
      nlinarith [sq_nonneg (a.2.1 * b.2.2 - a.2.2 * b.2.1)]
    have hlc : (a.2.1 ^ 2 + a.2.2 ^ 2) * (b.2.1 ^ 2 + b.2.2 ^ 2) ≤ (a.1 * b.1) ^ 2 := by
      have h1 : (a.2.1 ^ 2 + a.2.2 ^ 2) * (b.2.1 ^ 2 + b.2.2 ^ 2) ≤ a.1 ^ 2 * (b.2.1 ^ 2 + b.2.2 ^ 2) :=
        mul_le_mul_of_nonneg_right ha.2 (by nlinarith [sq_nonneg b.2.1, sq_nonneg b.2.2])
      have h2 : a.1 ^ 2 * (b.2.1 ^ 2 + b.2.2 ^ 2) ≤ a.1 ^ 2 * b.1 ^ 2 :=
        mul_le_mul_of_nonneg_left hb.2 (by nlinarith [sq_nonneg a.1])
      nlinarith
    have : (a.2.1 * b.2.1 + a.2.2 * b.2.2) ^ 2 = (a.1 * b.1) ^ 2 := by rw [h_inner]; ring
    nlinarith
  nlinarith [sq_nonneg (a.2.1 * b.2.2 - a.2.2 * b.2.1)]

set_option maxHeartbeats 600000 in
/-- Uniqueness of the PSD square root: if two PSD elements have the same
    squaring equations, they are equal. -/
theorem sqrtPSD_unique (u v : SpinFactor) (hu : IsNonneg u) (hv : IsNonneg v)
    (hsum : u.1^2 + u.2.1^2 + u.2.2^2 = v.1^2 + v.2.1^2 + v.2.2^2)
    (hprod1 : 2 * u.1 * u.2.1 = 2 * v.1 * v.2.1)
    (hprod2 : 2 * u.1 * u.2.2 = 2 * v.1 * v.2.2) :
    u = v := by
  have hu_bn : u.2.1 ^ 2 + u.2.2 ^ 2 ≤ u.1 ^ 2 := hu.2
  have hv_bn : v.2.1 ^ 2 + v.2.2 ^ 2 ≤ v.1 ^ 2 := hv.2
  -- From hprod1 and hprod2: u₀u₁ = v₀v₁ and u₀u₂ = v₀v₂
  have h1 : u.1 * u.2.1 = v.1 * v.2.1 := by linarith
  have h2 : u.1 * u.2.2 = v.1 * v.2.2 := by linarith
  -- From hsum: u₀²+u₁²+u₂² = v₀²+v₁²+v₂², call this m₀
  -- Quartic: u₀ and v₀ satisfy 4x⁴ - 4m₀x² + (2u₀u₁)² + (2u₀u₂)² = 0 (substituting u₁,u₂)
  -- Actually: from u₀u₁ = v₀v₁ and u₀u₂ = v₀v₂ and squaring equations:
  -- u₀² + u₁² + u₂² = v₀² + v₁² + v₂²
  -- (u₀u₁)² = (v₀v₁)², (u₀u₂)² = (v₀v₂)²
  -- So u₀²(u₁²+u₂²) = v₀²(v₁²+v₂²)
  -- Let m₀ = u₀²+u₁²+u₂² = v₀²+v₁²+v₂², P = u₁²+u₂², Q = v₁²+v₂²
  -- u₀² = m₀ - P, v₀² = m₀ - Q
  -- u₀²·P = v₀²·Q → (m₀-P)P = (m₀-Q)Q → m₀(P-Q) = P²-Q² = (P-Q)(P+Q)
  -- If P ≠ Q: m₀ = P+Q. Also P ≤ u₀² = m₀-P and Q ≤ v₀² = m₀-Q
  -- P ≤ m₀-P → 2P ≤ m₀ = P+Q → P ≤ Q. Similarly Q ≤ P. So P = Q. Contradiction.
  -- Therefore P = Q, i.e., u₁²+u₂² = v₁²+v₂². Then u₀² = v₀².
  have h_sq_sum : u.1^2 * (u.2.1^2 + u.2.2^2) = v.1^2 * (v.2.1^2 + v.2.2^2) := by
    -- (u₀u₁)² = u₀²u₁², so from h1: u₀²u₁² = v₀²v₁². Similarly for component 2.
    have h1_sq : (u.1 * u.2.1) ^ 2 = (v.1 * v.2.1) ^ 2 := by rw [h1]
    have h2_sq : (u.1 * u.2.2) ^ 2 = (v.1 * v.2.2) ^ 2 := by rw [h2]
    nlinarith [h1_sq, h2_sq]
  -- Let P = u₁²+u₂², Q = v₁²+v₂², m₀ = u₀²+P = v₀²+Q
  -- (m₀-P)P = (m₀-Q)Q → m₀P - P² = m₀Q - Q² → m₀(P-Q) = P²-Q² = (P-Q)(P+Q)
  -- → (P-Q)(m₀-P-Q) = 0
  set P := u.2.1^2 + u.2.2^2
  set Q := v.2.1^2 + v.2.2^2
  set m0 := u.1^2 + P
  have hm0_eq : m0 = v.1^2 + Q := by simp only [m0, P, Q]; linarith
  have h_PQ : (P - Q) * (m0 - P - Q) = 0 := by
    have : (m0 - P) * P = (m0 - Q) * Q := by
      simp only [m0, P, Q] at *; nlinarith
    nlinarith
  rcases mul_eq_zero.mp h_PQ with hPQ | hsum_eq
  · -- P = Q
    have hP_eq_Q : P = Q := by linarith
    have hu0_sq : u.1^2 = v.1^2 := by
      have : m0 = u.1 ^ 2 + P := rfl
      linarith
    have hu0_nn : 0 ≤ u.1 := hu.1
    have hv0_nn : 0 ≤ v.1 := hv.1
    have hu0_eq : u.1 = v.1 := by nlinarith [sq_nonneg (u.1 - v.1)]
    rcases eq_or_lt_of_le hu0_nn with hu0_zero | hu0_pos
    · have hv0_zero : v.1 = 0 := by linarith
      have hu1 : u.2.1 = 0 := by nlinarith [hu_bn]
      have hu2 : u.2.2 = 0 := by nlinarith [hu_bn]
      have hv1 : v.2.1 = 0 := by nlinarith [hv_bn]
      have hv2 : v.2.2 = 0 := by nlinarith [hv_bn]
      exact Prod.ext hu0_eq (Prod.ext (by linarith) (by linarith))
    · have hvne : v.1 ≠ 0 := ne_of_gt (by linarith)
      have h1' : u.2.1 = v.2.1 := by
        have h := h1; rw [hu0_eq] at h; exact mul_left_cancel₀ hvne h
      have h2' : u.2.2 = v.2.2 := by
        have h := h2; rw [hu0_eq] at h; exact mul_left_cancel₀ hvne h
      exact Prod.ext hu0_eq (Prod.ext h1' h2')
  · -- m₀ = P + Q. But P ≤ u₀² = m₀-P, Q ≤ v₀² = m₀-Q. So P=Q.
    -- Then reduce to the first case.
    have hm0_P : m0 = u.1 ^ 2 + P := rfl
    have hm0_Q : m0 = v.1 ^ 2 + Q := hm0_eq
    have hP_le_u : P ≤ u.1 ^ 2 := hu_bn
    have hQ_le_v : Q ≤ v.1 ^ 2 := hv_bn
    -- u₀² = m₀ - P, so P ≤ m₀ - P, so 2P ≤ m₀ = P + Q, so P ≤ Q
    -- Similarly Q ≤ P
    have hPQ_eq : P = Q := by nlinarith
    -- Now same as first case
    have hu0_sq : u.1^2 = v.1^2 := by linarith
    have hu0_eq : u.1 = v.1 := by nlinarith [sq_nonneg (u.1 - v.1), hu.1, hv.1]
    rcases eq_or_lt_of_le hu.1 with hu0_zero | hu0_pos
    · have hv0z : v.1 = 0 := by linarith
      have hu1 : u.2.1 = 0 := by nlinarith [hu_bn]
      have hu2 : u.2.2 = 0 := by nlinarith [hu_bn]
      have hv1 : v.2.1 = 0 := by nlinarith [hv_bn]
      have hv2 : v.2.2 = 0 := by nlinarith [hv_bn]
      exact Prod.ext hu0_eq (Prod.ext (by linarith) (by linarith))
    · have hvne : v.1 ≠ 0 := ne_of_gt (by linarith)
      have h1' : u.2.1 = v.2.1 := by
        have h := h1; rw [hu0_eq] at h; exact mul_left_cancel₀ hvne h
      have h2' : u.2.2 = v.2.2 := by
        have h := h2; rw [hu0_eq] at h; exact mul_left_cancel₀ hvne h
      exact Prod.ext hu0_eq (Prod.ext h1' h2')

/-- Associativity of matTripleProd when Bloch vectors are parallel:
    S(TCT)S = (ST)C(ST) when ST = TS (parallel Bloch vectors). -/
theorem matTripleProd_assoc_parallel (s t c : SpinFactor)
    (hpar : s.2.1 * t.2.2 = s.2.2 * t.2.1) :
    matTripleProd s (matTripleProd t c) = matTripleProd (jordanMul s t) c := by
  simp only [matTripleProd, jordanMul]
  ext
  · -- First component
    linear_combination (c.1 * (s.2.1 * t.2.2 - s.2.2 * t.2.1) - 2 * c.2.1 * (s.1 * t.2.2 + s.2.2 * t.1) + 2 * c.2.2 * (s.1 * t.2.1 + s.2.1 * t.1)) * hpar
  · -- Second component (snd.fst)
    linear_combination (2 * c.1 * (s.1 * t.2.2 + s.2.2 * t.1) - c.2.1 * (s.2.1 * t.2.2 - s.2.2 * t.2.1) + 2 * c.2.2 * (s.1 * t.1 + s.2.1 * t.2.1 + s.2.2 * t.2.2)) * hpar
  · -- Third component (snd.snd)
    linear_combination (-2 * c.1 * (s.1 * t.2.1 + s.2.1 * t.1) - 2 * c.2.1 * (s.1 * t.1 + s.2.1 * t.2.1 + s.2.2 * t.2.2) - c.2.2 * (s.2.1 * t.2.2 - s.2.2 * t.2.1)) * hpar

/-! ### SequentialProduct instance -/

set_option maxHeartbeats 1600000 in
instance : SequentialProduct SpinFactor where
  sp := seqProd
  sp_add_right := by intro a b c _ _ _ _; simp only [seqProd, matTripleProd_add_right]
  sp_mono_right := by
    intro a b₁ b₂ ha _ _ hle
    -- seqProd a b₂ - seqProd a b₁ = matTripleProd(√a, b₂ - b₁) by linearity.
    -- Since b₂ - b₁ ≥ 0 and √a ≥ 0, matTripleProd_nonneg gives the result.
    change IsNonneg (seqProd a b₂ - seqProd a b₁)
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have h_eq : seqProd a b₂ - seqProd a b₁ = matTripleProd (sqrtPSD a) (b₂ - b₁) := by
      simp only [seqProd, matTripleProd]; ext <;> simp <;> ring
    rw [h_eq]
    exact matTripleProd_nonneg _ _ (sqrtPSD_nonneg a ha_nn) hle
  sp_unit_left := by intro a _; change seqProd unit a = a; simp only [seqProd, sqrtPSD_unit, matTripleProd_unit_left]
  sp_zero_symm := by
    intro a b ha hb h0
    change seqProd a b = 0 at h0
    change seqProd b a = 0
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have hb_nn : IsNonneg b := by have h := hb.1; simp only [le_def] at h; simpa using h
    -- Case split: if a₀ = 0 or b₀ = 0, one of them is the zero element
    have ha_bn : a.2.1 ^ 2 + a.2.2 ^ 2 ≤ a.1 ^ 2 := ha_nn.2
    have hb_bn : b.2.1 ^ 2 + b.2.2 ^ 2 ≤ b.1 ^ 2 := hb_nn.2
    rcases eq_or_lt_of_le ha_nn.1 with ha0_eq | ha0_pos
    · have ha1 : a.2.1 = 0 := by nlinarith [sq_nonneg a.2.1, sq_nonneg a.2.2]
      have ha2 : a.2.2 = 0 := by nlinarith [sq_nonneg a.2.1, sq_nonneg a.2.2]
      rw [show a = (0, 0, 0) from Prod.ext ha0_eq.symm (Prod.ext ha1 ha2)]
      exact seqProd_zero_right b
    rcases eq_or_lt_of_le hb_nn.1 with hb0_eq | hb0_pos
    · have hb1 : b.2.1 = 0 := by nlinarith [sq_nonneg b.2.1, sq_nonneg b.2.2]
      have hb2 : b.2.2 = 0 := by nlinarith [sq_nonneg b.2.1, sq_nonneg b.2.2]
      rw [show b = (0, 0, 0) from Prod.ext hb0_eq.symm (Prod.ext hb1 hb2)]
      exact seqProd_zero_left a
    · -- Both a₀ > 0 and b₀ > 0: derive Bloch parallelism from seqProd a b = 0
      have hpar := bloch_parallel_of_seqProd_zero a b ha_nn hb_nn ha0_pos hb0_pos h0
      rw [← seqProd_comm_of_bloch_parallel a b ha_nn hb_nn hpar, h0]
  sp_assoc_of_compatible := by
    intro a b c ha hb hc hcomm
    change seqProd a b = seqProd b a at hcomm
    change seqProd a (seqProd b c) = seqProd (seqProd a b) c
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have hb_nn : IsNonneg b := by have h := hb.1; simp only [le_def] at h; simpa using h
    obtain ⟨hsa_sum, hsa_p1, hsa_p2⟩ := sqrtPSD_squares a ha_nn
    obtain ⟨hsb_sum, hsb_p1, hsb_p2⟩ := sqrtPSD_squares b hb_nn
    have hsa_nn := sqrtPSD_nonneg a ha_nn
    have hsb_nn := sqrtPSD_nonneg b hb_nn
    -- Extract explicit blochNormSq bounds (needed for nlinarith)
    have hsa_bn : (sqrtPSD a).2.1 ^ 2 + (sqrtPSD a).2.2 ^ 2 ≤ (sqrtPSD a).1 ^ 2 := hsa_nn.2
    have hsb_bn : (sqrtPSD b).2.1 ^ 2 + (sqrtPSD b).2.2 ^ 2 ≤ (sqrtPSD b).1 ^ 2 := hsb_nn.2
    -- Bloch parallelism from commutativity
    have hpar := seqProd_comm_implies_bloch_parallel a b ha_nn hb_nn hcomm
    -- sqrtPSD Bloch parallel
    have hsa_par := sqrtPSD_bloch_parallel a b hpar
    -- Derive sa₁·sb₂ = sa₂·sb₁ from sa₁·b₂ = sa₂·b₁
    have hsa_sb_par : (sqrtPSD a).2.1 * (sqrtPSD b).2.2 = (sqrtPSD a).2.2 * (sqrtPSD b).2.1 := by
      rcases eq_or_lt_of_le hsb_nn.1 with hsb0_eq | hsb0_pos
      · have sb1 : (sqrtPSD b).2.1 = 0 := by nlinarith [sq_nonneg (sqrtPSD b).2.1, sq_nonneg (sqrtPSD b).2.2]
        have sb2 : (sqrtPSD b).2.2 = 0 := by nlinarith [sq_nonneg (sqrtPSD b).2.1, sq_nonneg (sqrtPSD b).2.2]
        simp [sb1, sb2]
      · -- sb₀ > 0. From hsa_par: sa₁·b₂ = sa₂·b₁, substitute b₂=2sb₀sb₂, b₁=2sb₀sb₁
        have h_prod : (sqrtPSD a).2.1 * (2 * (sqrtPSD b).1 * (sqrtPSD b).2.2) =
            (sqrtPSD a).2.2 * (2 * (sqrtPSD b).1 * (sqrtPSD b).2.1) := by
          rw [hsb_p2, hsb_p1]; exact hsa_par
        have : (sqrtPSD b).1 * ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
    -- LHS: seqProd a (seqProd b c) = matTripleProd sa (matTripleProd sb c)
    -- By matTripleProd_assoc_parallel: = matTripleProd (jordanMul sa sb) c
    have hlhs : seqProd a (seqProd b c) = matTripleProd (jordanMul (sqrtPSD a) (sqrtPSD b)) c := by
      show matTripleProd (sqrtPSD a) (matTripleProd (sqrtPSD b) c) = _
      exact matTripleProd_assoc_parallel _ _ _ hsa_sb_par
    rw [hlhs]
    -- RHS: seqProd (seqProd a b) c = matTripleProd (sqrtPSD (seqProd a b)) c
    -- Show jordanMul sa sb = sqrtPSD (seqProd a b) by uniqueness
    -- Step 1: jordanMul sa sb is PSD
    -- Step 2: jordanMul sa sb satisfies the squaring equations for seqProd a b
    set ab := seqProd a b
    set jst := jordanMul (sqrtPSD a) (sqrtPSD b)
    have hab_nn : IsNonneg ab := matTripleProd_nonneg _ _ hsa_nn hb_nn
    -- PSD of jordanMul sa sb
    have hjst_nn : IsNonneg jst := by
      constructor
      · -- jst₀ ≥ 0: sa₀sb₀ + sa₁sb₁ + sa₂sb₂ ≥ 0 by Cauchy-Schwarz
        show 0 ≤ jst.1; simp only [jst, jordanMul]
        nlinarith [mul_nonneg hsa_nn.1 hsb_nn.1,
          sq_nonneg ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1),
          mul_le_mul_of_nonneg_right hsa_bn (show 0 ≤ (sqrtPSD b).2.1^2 + (sqrtPSD b).2.2^2 from by nlinarith [sq_nonneg (sqrtPSD b).2.1, sq_nonneg (sqrtPSD b).2.2]),
          mul_le_mul_of_nonneg_left hsb_bn (show 0 ≤ (sqrtPSD a).1^2 from by nlinarith [sq_nonneg (sqrtPSD a).1]),
          sq_nonneg ((sqrtPSD a).1 * (sqrtPSD b).1 + (sqrtPSD a).2.1 * (sqrtPSD b).2.1 + (sqrtPSD a).2.2 * (sqrtPSD b).2.2)]
      · -- blochNormSq ≤ jst₀²: uses det(sa)·det(sb) ≥ 0
        show jst.2.1 ^ 2 + jst.2.2 ^ 2 ≤ jst.1 ^ 2
        simp only [jst, jordanMul]
        nlinarith [hsa_bn, hsb_bn, hsa_sb_par,
          sq_nonneg ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1),
          mul_nonneg (show 0 ≤ (sqrtPSD a).1^2 - (sqrtPSD a).2.1^2 - (sqrtPSD a).2.2^2 from by nlinarith)
                     (show 0 ≤ (sqrtPSD b).1^2 - (sqrtPSD b).2.1^2 - (sqrtPSD b).2.2^2 from by nlinarith)]
    -- sqrtPSD (seqProd a b) is PSD
    have hab_sqrt_nn := sqrtPSD_nonneg ab hab_nn
    -- sqrtPSD_squares for sqrtPSD(ab)
    obtain ⟨hsab_sum, hsab_p1, hsab_p2⟩ := sqrtPSD_squares ab hab_nn
    -- Squaring equations for jordanMul sa sb w.r.t. seqProd a b
    -- Using the factored forms: diffs are multiples of (sa₁sb₂-sa₂sb₁)
    have hjst_sum : jst.1^2 + jst.2.1^2 + jst.2.2^2 = ab.1 := by
      -- Step 1: rewrite ab.1 using matTripleProd_fst_of_sqrt
      have hab1 : ab.1 = a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2 := by
        show (seqProd a b).1 = _; simp only [seqProd]
        exact matTripleProd_fst_of_sqrt _ _ a hsa_sum hsa_p1 hsa_p2
      -- Step 2: substitute all a, b components with sqrtPSD expressions
      rw [hab1, ← hsa_sum, ← hsb_sum, ← hsa_p1, ← hsb_p1, ← hsa_p2, ← hsb_p2]
      -- Step 3: expand jordanMul; goal is now purely in sqrtPSD components
      simp only [jst, jordanMul]
      -- diff = -(sa₁sb₂-sa₂sb₁)², which is 0 by hsa_sb_par
      nlinarith [hsa_sb_par, sq_nonneg ((sqrtPSD a).2.1 * (sqrtPSD b).2.2 - (sqrtPSD a).2.2 * (sqrtPSD b).2.1)]
    have hjst_p1 : 2 * jst.1 * jst.2.1 = ab.2.1 := by
      -- Use _of_sqrt formula for clean RHS expression
      have hrhs : ab.2.1 = a.2.1 * b.1 + a.1 * b.2.1 +
          2 * (sqrtPSD a).2.2 * ((sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1) := by
        show (seqProd a b).2.1 = _; simp only [seqProd]
        exact matTripleProd_snd_fst_of_sqrt _ _ a hsa_sum hsa_p1 hsa_p2
      -- Substitute a components with sqrtPSD a squared forms
      rw [← hsa_p1] at hrhs
      rw [← hsa_sum] at hrhs
      -- Substitute b components with sqrtPSD b squared forms
      rw [← hsb_sum] at hrhs
      rw [← hsb_p1] at hrhs
      rw [← hsb_p2] at hrhs
      -- Now hrhs is purely in sqrtPSD components
      rw [hrhs]; simp only [jst, jordanMul]
      linear_combination -2 * ((sqrtPSD a).1 * (sqrtPSD b).2.2 + (sqrtPSD b).1 * (sqrtPSD a).2.2) * hsa_sb_par
    have hjst_p2 : 2 * jst.1 * jst.2.2 = ab.2.2 := by
      -- Use _of_sqrt formula for clean RHS expression
      have hrhs : ab.2.2 = a.2.2 * b.1 + a.1 * b.2.2 -
          2 * (sqrtPSD a).2.1 * ((sqrtPSD a).2.1 * b.2.2 - (sqrtPSD a).2.2 * b.2.1) := by
        show (seqProd a b).2.2 = _; simp only [seqProd]
        exact matTripleProd_snd_snd_of_sqrt _ _ a hsa_sum hsa_p1 hsa_p2
      rw [← hsa_p2] at hrhs
      rw [← hsa_sum] at hrhs
      rw [← hsb_sum] at hrhs
      rw [← hsb_p1] at hrhs
      rw [← hsb_p2] at hrhs
      rw [hrhs]; simp only [jst, jordanMul]
      linear_combination 2 * ((sqrtPSD a).1 * (sqrtPSD b).2.1 + (sqrtPSD b).1 * (sqrtPSD a).2.1) * hsa_sb_par
    -- By uniqueness: jordanMul sa sb = sqrtPSD (seqProd a b)
    have hjst_eq_sqrt : jst = sqrtPSD ab :=
      sqrtPSD_unique jst (sqrtPSD ab) hjst_nn hab_sqrt_nn
        (by rw [hjst_sum, hsab_sum])
        (by rw [hjst_p1, hsab_p1])
        (by rw [hjst_p2, hsab_p2])
    -- Conclude: matTripleProd jst c = matTripleProd (sqrtPSD ab) c = seqProd ab c
    rw [hjst_eq_sqrt]; rfl
  compatible_ortho := by
    intro a b ha hb hcomm
    -- hcomm: seqProd a b = seqProd b a. Need: seqProd a (unit-b) = seqProd (unit-b) a
    change seqProd a (unit - b) = seqProd (unit - b) a
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have hb_nn : IsNonneg b := by have h := hb.1; simp only [le_def] at h; simpa using h
    have hub_nn : IsNonneg (unit - b) := hb.2
    have hpar := seqProd_comm_implies_bloch_parallel a b ha_nn hb_nn hcomm
    -- hpar: a₁b₂ = a₂b₁. Need: a₁(1-b)₂ = a₂(1-b)₁
    -- (unit-b) = (1-b₀, -b₁, -b₂), so (unit-b).2.1 = -b₁, (unit-b).2.2 = -b₂
    have hpar' : a.2.1 * (unit - b).2.2 = a.2.2 * (unit - b).2.1 := by
      simp only [unit, Prod.snd_sub, Prod.fst_sub]; ring_nf; linarith
    exact seqProd_comm_of_bloch_parallel a (unit - b) ha_nn hub_nn hpar'
  compatible_add := by
    intro a b c ha hb hc hbc hab hac
    -- hab: seqProd a b = seqProd b a, hac: seqProd a c = seqProd c a
    -- Need: seqProd a (b+c) = seqProd (b+c) a
    change seqProd a (b + c) = seqProd (b + c) a
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have hb_nn : IsNonneg b := by have h := hb.1; simp only [le_def] at h; simpa using h
    have hc_nn : IsNonneg c := by have h := hc.1; simp only [le_def] at h; simpa using h
    have hbc_nn : IsNonneg (b + c) := by
      have := IsEffect.add_of_le_unit hb hc hbc
      have h := this.1; simp only [le_def] at h; simpa using h
    have hpar_ab := seqProd_comm_implies_bloch_parallel a b ha_nn hb_nn hab
    have hpar_ac := seqProd_comm_implies_bloch_parallel a c ha_nn hc_nn hac
    -- hpar_ab: a₁b₂ = a₂b₁, hpar_ac: a₁c₂ = a₂c₁
    -- Need: a₁(b+c)₂ = a₂(b+c)₁
    have hpar_bc : a.2.1 * (b + c).2.2 = a.2.2 * (b + c).2.1 := by
      simp only [Prod.snd_add, Prod.fst_add]; ring_nf; linarith
    exact seqProd_comm_of_bloch_parallel a (b + c) ha_nn hbc_nn hpar_bc
  compatible_sp := by
    intro a b c ha hb hc hab hac
    change seqProd a (seqProd b c) = seqProd (seqProd b c) a
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have hb_nn : IsNonneg b := by have h := hb.1; simp only [le_def] at h; simpa using h
    have hc_nn : IsNonneg c := by have h := hc.1; simp only [le_def] at h; simpa using h
    have hbc_nn : IsNonneg (seqProd b c) := by
      exact matTripleProd_nonneg _ _ (sqrtPSD_nonneg b hb_nn) hc_nn
    -- Get Bloch parallelism conditions
    have hpar_ab := seqProd_comm_implies_bloch_parallel a b ha_nn hb_nn hab
    have hpar_ac := seqProd_comm_implies_bloch_parallel a c ha_nn hc_nn hac
    -- sqrtPSD b has Bloch parallel to b, hence to a
    have hpar_ba : b.2.1 * a.2.2 = b.2.2 * a.2.1 := by linarith
    have hsb_par := sqrtPSD_bloch_parallel b a hpar_ba
    -- hsb_par: sb₁*a₂ = sb₂*a₁
    -- We need a₁*(seqProd b c)₂ = a₂*(seqProd b c)₁
    obtain ⟨hsb_sq, hpb1, hpb2⟩ := sqrtPSD_squares b hb_nn
    -- Use the _of_sqrt forms for seqProd b c
    have hbc1 := matTripleProd_snd_fst_of_sqrt (sqrtPSD b) c b hsb_sq hpb1 hpb2
    have hbc2 := matTripleProd_snd_snd_of_sqrt (sqrtPSD b) c b hsb_sq hpb1 hpb2
    -- hbc1: (seqProd b c).2.1 = b₁c₀+b₀c₁+2sb₂(sb₁c₂-sb₂c₁)
    -- hbc2: (seqProd b c).2.2 = b₂c₀+b₀c₂-2sb₁(sb₁c₂-sb₂c₁)
    -- Need: a₁*(b₂c₀+b₀c₂-2sb₁(sb₁c₂-sb₂c₁)) = a₂*(b₁c₀+b₀c₁+2sb₂(sb₁c₂-sb₂c₁))
    -- Using a₁b₂=a₂b₁, a₁c₂=a₂c₁, and sb₁a₂=sb₂a₁:
    -- LHS-RHS = (a₁b₂-a₂b₁)c₀ + (a₁c₂-a₂c₁)b₀ - 2(a₁sb₁+a₂sb₂)(sb₁c₂-sb₂c₁)
    -- = 0 + 0 - 2(a₁sb₁+a₂sb₂)(sb₁c₂-sb₂c₁)
    -- From sb₁*a₂=sb₂*a₁ and a₁*c₂=a₂*c₁:
    -- (sb₁*a₂-sb₂*a₁)(a₁*c₂-a₂*c₁) = 0 gives sb₁*a₂*a₁*c₂ = ... etc
    -- Key: (a₁*sb₁+a₂*sb₂)*(sb₁*c₂-sb₂*c₁) = 0
    -- Proof: sb₁*a₂=sb₂*a₁ → a₁*sb₁ = a₁*sb₁, a₂*sb₂ = a₂*sb₂. Hmm.
    -- Actually: multiply sb₁*a₂=sb₂*a₁ by c₂: sb₁*a₂*c₂ = sb₂*a₁*c₂ = sb₂*a₂*c₁
    -- So a₂*(sb₁*c₂-sb₂*c₁) = 0. Similarly mult by c₁: sb₁*a₂*c₁ = sb₂*a₁*c₁.
    -- And a₁*c₂=a₂*c₁ mult by sb₁: sb₁*a₁*c₂ = sb₁*a₂*c₁ = sb₂*a₁*c₁.
    -- So a₁*(sb₁*c₂-sb₂*c₁) = sb₁*a₁*c₂ - sb₂*a₁*c₁ = sb₂*a₁*c₁ - sb₂*a₁*c₁ = 0.
    -- Therefore both a₁*(sb₁c₂-sb₂c₁) = 0 and a₂*(sb₁c₂-sb₂c₁) = 0.
    -- So (a₁sb₁+a₂sb₂)*(sb₁c₂-sb₂c₁) = sb₁*a₁*(sb₁c₂-sb₂c₁)+sb₂*a₂*(sb₁c₂-sb₂c₁) = 0.
    have h_a1_cross : a.2.1 * ((sqrtPSD b).2.1 * c.2.2 - (sqrtPSD b).2.2 * c.2.1) = 0 := by
      linear_combination (sqrtPSD b).2.1 * hpar_ac + c.2.1 * hsb_par
    have h_a2_cross : a.2.2 * ((sqrtPSD b).2.1 * c.2.2 - (sqrtPSD b).2.2 * c.2.1) = 0 := by
      linear_combination c.2.2 * hsb_par + (sqrtPSD b).2.2 * hpar_ac
    have hpar_bc : a.2.1 * (seqProd b c).2.2 = a.2.2 * (seqProd b c).2.1 := by
      simp only [seqProd]; rw [hbc2, hbc1]
      -- LHS-RHS = (a₁b₂-a₂b₁)c₀+(a₁c₂-a₂c₁)b₀-2(a₁sb₁+a₂sb₂)(sb₁c₂-sb₂c₁)
      -- = 0+0-2(sb₁·0+sb₂·0) = 0 [using h_a1_cross, h_a2_cross, hpar_ab, hpar_ac]
      linear_combination c.1 * hpar_ab + b.1 * hpar_ac -
        2 * (sqrtPSD b).2.1 * h_a1_cross - 2 * (sqrtPSD b).2.2 * h_a2_cross
    exact seqProd_comm_of_bloch_parallel a (seqProd b c) ha_nn hbc_nn hpar_bc
  sp_effect := by
    intro a b ha hb
    -- Extract PSD conditions
    have ha_nn : IsNonneg a := by have h := ha.1; simp only [le_def] at h; simpa using h
    have hb_nn : IsNonneg b := by have h := hb.1; simp only [le_def] at h; simpa using h
    have h_ub_nn : IsNonneg (unit - b) := hb.2
    have h_sqrt_nn : IsNonneg (sqrtPSD a) := sqrtPSD_nonneg a ha_nn
    constructor
    · -- 0 ≤ seqProd a b
      change IsNonneg (seqProd a b - 0); simp
      exact matTripleProd_nonneg _ _ h_sqrt_nn hb_nn
    · -- seqProd a b ≤ unit: show seqProd a b ≤ a ≤ unit
      have h_le_a : seqProd a b ≤ a := by
        change IsNonneg (a - seqProd a b)
        have h_ur : matTripleProd (sqrtPSD a) unit = a := by
          have := seqProd_unit_right a ha_nn; simp only [seqProd] at this; exact this
        have h_sub : matTripleProd (sqrtPSD a) (unit - b) = matTripleProd (sqrtPSD a) unit - matTripleProd (sqrtPSD a) b := by
          simp only [matTripleProd]; ext <;> simp <;> ring
        have h_eq : a - seqProd a b = matTripleProd (sqrtPSD a) (unit - b) := by
          simp only [seqProd]; rw [h_sub, h_ur]
        rw [h_eq]; exact matTripleProd_nonneg _ _ h_sqrt_nn h_ub_nn
      change IsNonneg (ousUnit - seqProd a b)
      change IsNonneg (unit - seqProd a b)
      have h_au : a ≤ (unit : SpinFactor) := ha.2
      -- unit - seqProd a b = (unit - a) + (a - seqProd a b)
      -- Both are PSD, and PSD cone is closed under addition (le_trans')
      have h1 : IsNonneg (unit - a) := h_au
      have h2 : IsNonneg (a - seqProd a b) := h_le_a
      have h_sum : unit - seqProd a b = (unit - a) + (a - seqProd a b) := by ext <;> simp
      rw [h_sum]
      exact ⟨by simp only [Prod.fst_add]; linarith [h1.1, h2.1], by
        simp only [blochNormSq, Prod.fst_add, Prod.snd_add] at *
        have key : ∀ (p q s x y t : ℝ), 0 ≤ s → 0 ≤ t →
            p ^ 2 + q ^ 2 ≤ s ^ 2 → x ^ 2 + y ^ 2 ≤ t ^ 2 →
            (p + x) ^ 2 + (q + y) ^ 2 ≤ (s + t) ^ 2 := by
          intro p q s x y t hs ht hp hq
          have cs := sq_nonneg (p * y - q * x)
          have h12 : (p ^ 2 + q ^ 2) * (x ^ 2 + y ^ 2) ≤ s ^ 2 * t ^ 2 :=
            mul_le_mul hp hq (by nlinarith [sq_nonneg x, sq_nonneg y]) (by nlinarith [sq_nonneg s])
          have hst : 0 ≤ s * t := mul_nonneg hs ht
          by_cases hpos : 0 ≤ p * x + q * y
          · nlinarith [sq_nonneg (s * t - (p * x + q * y))]
          · push_neg at hpos; nlinarith
        exact key _ _ _ _ _ _ h1.1 h2.1 h1.2 h2.2⟩
  sp_sub_right_general := by
    intro a b c ha _ _
    -- seqProd a (b - c) = matTripleProd(√a, b - c) = matTripleProd(√a, b) - matTripleProd(√a, c)
    simp only [seqProd, matTripleProd]; ext <;> simp <;> ring

end SpinFactor
