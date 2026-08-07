/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealWignerBridge
import RadicalRelativity.Necessity.RealStrength

set_option linter.style.longLine false

/-!
# The ray map of an order automorphism  (the ℝ bridge to real Kadison, part 5g)

An order automorphism `Φ` of `H_N(ℝ)` carries rank-one projections to rank-one projections
(`exists_rankOneR_map`), so it induces a self-map of the real projective space: send the ray
of `ψ` to the ray of the vector whose rank-one is `Φ (rankOneR ψ)`.  This file builds that map
and proves it preserves transition probabilities — which is precisely the hypothesis real
Wigner rigidity consumes.

The content is `tprobR_preserved` (the transition probability is ORDER data, so it transports)
plus the vocabulary bridge of part 5e (that on unit vectors the vendored transition probability
IS the squared dot product).  Everything else is representative bookkeeping.

* `Projectivization.transProbR_mk` — the transition probability may be computed from ANY
  nonzero representatives, not just `.rep`.  The vendor file inlines this argument twice; it is
  factored here once.
* `rayVecR` / `rayMapR` — the induced map on rays.
* `rayMapR_transProbPreservingR` — it preserves transition probabilities.
-/

noncomputable section

open scoped Matrix
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The chosen representative of `mk ℝ v` is a nonzero multiple of `v`. -/
theorem exists_units_smul_rep_mk (v : E) (hv : v ≠ 0) :
    ∃ a : ℝˣ, (Projectivization.mk ℝ v hv).rep = a • v :=
  (Projectivization.exists_smul_eq_mk_rep ℝ v hv).imp fun _ ha => ha.symm

/-- **Representative independence**: the transition probability of two rays may be computed
from any nonzero representatives. -/
theorem transProbR_mk (v w : E) (hv : v ≠ 0) (hw : w ≠ 0) :
    transProbR (Projectivization.mk ℝ v hv) (Projectivization.mk ℝ w hw)
      = transProbVecR v w := by
  obtain ⟨a, ha⟩ := exists_units_smul_rep_mk v hv
  obtain ⟨b, hb⟩ := exists_units_smul_rep_mk w hw
  unfold transProbR
  rw [ha, hb]
  simp only [Units.smul_def]
  rw [transProbVecR_smul_left (a : ℝ) a.ne_zero, transProbVecR_smul_right (b : ℝ) b.ne_zero]

end Projectivization

namespace Necessity

variable {N : ℕ}

theorem toLp_repUnitR_ne_zero (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) :
    (WithLp.toLp 2 (repUnitR p) : EuclideanSpace ℝ (Fin N)) ≠ 0 := fun h =>
  repUnitR_ne_zero p ((WithLp.toLp_eq_zero (p := 2)).mp h)

/-- The transition probability of two rays, computed from their unit representatives. -/
theorem transProbR_eq_sq_repUnit (p q : ℙ ℝ (EuclideanSpace ℝ (Fin N))) :
    Projectivization.transProbR p q = (repUnitR p ⬝ᵥ repUnitR q) ^ 2 := by
  conv_lhs => rw [← mk_repUnitR p, ← mk_repUnitR q]
  rw [Projectivization.transProbR_mk,
    transProbVecR_eq_sq_dotProduct (ψ := WithLp.toLp 2 (repUnitR p))
      (φ := WithLp.toLp 2 (repUnitR q)) (repUnitR_unit p) (repUnitR_unit q)]

section RayMap

variable (Φ : HermitianMat (Fin N) ℝ →ₗ[ℝ] HermitianMat (Fin N) ℝ)
  (hΦ : ∀ x y : HermitianMat (Fin N) ℝ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
  (hsurj : Function.Surjective Φ)

/-- The unit vector whose rank-one is the image of the ray's rank-one.  Chosen. -/
def rayVecR (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) : Fin N → ℝ :=
  Classical.choose (exists_rankOneR_map Φ hΦ hunital hsurj (repUnitR_unit p))

theorem rayVecR_unit (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) :
    rayVecR Φ hΦ hunital hsurj p ⬝ᵥ rayVecR Φ hΦ hunital hsurj p = 1 :=
  (Classical.choose_spec (exists_rankOneR_map Φ hΦ hunital hsurj (repUnitR_unit p))).1

/-- **The defining property**: `Φ` sends the ray's rank-one to the chosen vector's rank-one. -/
theorem rayVecR_spec (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) :
    Φ (rankOneR (repUnitR p)) = rankOneR (rayVecR Φ hΦ hunital hsurj p) :=
  (Classical.choose_spec (exists_rankOneR_map Φ hΦ hunital hsurj (repUnitR_unit p))).2

theorem rayVecR_ne_zero (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) :
    rayVecR Φ hΦ hunital hsurj p ≠ 0 := by
  intro h
  have := rayVecR_unit Φ hΦ hunital hsurj p
  rw [h, zero_dotProduct] at this
  exact zero_ne_one this

theorem toLp_rayVecR_ne_zero (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) :
    (WithLp.toLp 2 (rayVecR Φ hΦ hunital hsurj p) : EuclideanSpace ℝ (Fin N)) ≠ 0 := fun h =>
  rayVecR_ne_zero Φ hΦ hunital hsurj p ((WithLp.toLp_eq_zero (p := 2)).mp h)

/-- **The induced map on rays.** -/
def rayMapR (p : ℙ ℝ (EuclideanSpace ℝ (Fin N))) : ℙ ℝ (EuclideanSpace ℝ (Fin N)) :=
  Projectivization.mk ℝ (WithLp.toLp 2 (rayVecR Φ hΦ hunital hsurj p))
    (toLp_rayVecR_ne_zero Φ hΦ hunital hsurj p)

/-- **The ray map preserves transition probabilities** — the hypothesis real Wigner consumes.
The mathematics is `tprobR_preserved` (the transition probability is order data); the rest is
the part-5e identification of the inner product with the dot product. -/
theorem rayMapR_transProbPreservingR :
    Projectivization.TransProbPreservingR (rayMapR Φ hΦ hunital hsurj) := by
  intro p q
  rw [rayMapR, rayMapR, Projectivization.transProbR_mk,
    transProbVecR_eq_sq_dotProduct (ψ := WithLp.toLp 2 (rayVecR Φ hΦ hunital hsurj p))
      (φ := WithLp.toLp 2 (rayVecR Φ hΦ hunital hsurj q))
      (rayVecR_unit Φ hΦ hunital hsurj p) (rayVecR_unit Φ hΦ hunital hsurj q),
    transProbR_eq_sq_repUnit]
  exact (tprobR_preserved Φ hΦ hunital (repUnitR_unit p) (repUnitR_unit q)
    (rayVecR_unit Φ hΦ hunital hsurj p) (rayVecR_unit Φ hΦ hunital hsurj q)
    (rayVecR_spec Φ hΦ hunital hsurj p) (rayVecR_spec Φ hΦ hunital hsurj q)).symm

end RayMap

/-! ## The matrix of a real isometry

Real Wigner returns a `LinearIsometryEquiv`; the Jordan witness `orthConj` needs an orthogonal
MATRIX.  These four declarations are the ℝ analogue of the vendored `unitaryOfIsometry` layer.
They are stated here rather than by generalizing the vendored ℂ file: the definition itself is
`RCLike`-general (`Matrix.toEuclideanLin`), but it lives inside three thousand lines of
ℂ-committed rigidity proof, and the ℝ surface needed is only this.
-/

/-- The matrix of a real linear isometry equivalence in the standard basis. -/
def isometryMatrixR (e : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toEuclideanLin.symm (e : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))

theorem isometryMatrixR_toEuclideanLin
    (e : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    Matrix.toEuclideanLin (isometryMatrixR e)
      = (e : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) :=
  LinearEquiv.apply_symm_apply _ _

/-- **The isometry acts on coordinates as its matrix.** -/
theorem isometryMatrixR_mulVec (e : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (ψ : EuclideanSpace ℝ (Fin N)) :
    isometryMatrixR e *ᵥ (WithLp.ofLp ψ) = WithLp.ofLp (e ψ) := by
  have h : Matrix.toEuclideanLin (isometryMatrixR e) ψ = e ψ := by
    rw [isometryMatrixR_toEuclideanLin]; rfl
  rw [← h]
  rfl

/-- **The matrix is orthogonal.**  Entry `(i, j)` of `Uᵀ U` is the inner product of the images
of the `i`-th and `j`-th basis vectors, which the isometry returns to `δᵢⱼ`. -/
theorem isometryMatrixR_orthogonal
    (e : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    (isometryMatrixR e)ᴴ * isometryMatrixR e = 1 := by
  ext i j
  have hinner : (inner ℝ (e (EuclideanSpace.single i (1 : ℝ)))
        (e (EuclideanSpace.single j (1 : ℝ))) : ℝ)
      = (inner ℝ (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single j (1 : ℝ)) : ℝ) := e.inner_map_map _ _
  rw [inner_eq_dotProductR, inner_eq_dotProductR, ← isometryMatrixR_mulVec,
    ← isometryMatrixR_mulVec] at hinner
  simp only [EuclideanSpace.ofLp_single, Matrix.mulVec_single_one] at hinner
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, Matrix.one_apply,
    dotProduct, Matrix.col_apply, Pi.single_apply] at hinner ⊢
  rw [hinner]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-! ## Rank-ones see only the ray

Over ℝ the ambiguity in a unit representative is a single sign, and `rankOneR` is quadratic, so
the sign cancels.  This is what turns real Wigner's conclusion — an equality of RAYS — into the
equality of rank-one projections that the span argument consumes.
-/

/-- **Sign invariance**: unit vectors spanning the same ray have the same rank-one. -/
theorem rankOneR_eq_of_mk_eq {v w : Fin N → ℝ} (hv : v ⬝ᵥ v = 1) (hw : w ⬝ᵥ w = 1)
    (hv0 : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N)) ≠ 0)
    (hw0 : (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin N)) ≠ 0)
    (h : Projectivization.mk ℝ (WithLp.toLp 2 v) hv0
        = Projectivization.mk ℝ (WithLp.toLp 2 w) hw0) :
    rankOneR v = rankOneR w := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _ hv0 hw0).mp h
  rw [Units.smul_def] at ha
  -- `w = a • v` at the level of functions
  have hvec : v = (a : ℝ) • w := by
    have := congrArg (WithLp.ofLp (p := 2)) ha
    simpa using this.symm
  -- the unit conditions force `a² = 1`
  have hsq : (a : ℝ) ^ 2 = 1 := by
    rw [hvec, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hw] at hv
    nlinarith [hv]
  rw [hvec, rankOneR_smul, hsq, one_smul]

end Necessity
