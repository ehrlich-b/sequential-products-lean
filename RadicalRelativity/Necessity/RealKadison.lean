/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.RealInducedMap
import RadicalRelativity.Necessity.RealJordanWitness

set_option linter.style.longLine false

/-!
# Kadison rigidity on `H_N(ℝ)`  (the ℝ bridge, capstone)

**Every unital `ℝ`-linear order-automorphism of `H_N(ℝ)` IS conjugation by an orthogonal
matrix** (`orderAutoR_eq_orthConj`, 2026-08-08), hence in particular a Jordan automorphism
(`orderAutoR_preservesJordan`).  This is the ℝ analogue of
`KadisonDischarge.orderAuto_classification` / `orderAuto_preservesJordan`, and the Jordan form
is what discharges the hypothesis the whole real row was conditional on.

The classification is **exact**, not one-sided: `orthConj_orderAuto` proves the converse
(orthogonal conjugation *is* a unital order-automorphism), so the order-automorphism group of
`H_N(ℝ)` is exactly `{Ad_O : OᵀO = 1}`.  The ℂ lane is exact too, in both branches
(`KadisonDischarge.orderAuto_classification_realized`).

**The difference from the ℂ lane.**  Both lanes prove their Wigner step inside this
development — `Projectivization.wigner_rigidity` at ℂ, and
`Projectivization.exists_isometry_of_transProbPreservingR` at ℝ — and both capstones close over
Lean core alone.  What was missing at ℝ was not an axiom but a *proof*: the real rigidity
theorem did not exist here (and we are aware of none in any library, not having searched
them systematically), so the real row carried its Jordan property as
a located hypothesis.  That theorem now exists, which is what this file spends.

The structural simplification at ℝ is the absence of the antiunitary alternative: real Wigner
returns an isometry outright, so there is no dichotomy to case on and no transpose branch to
discharge.  That is why this file is a third the length of its ℂ counterpart.

The chain:

1. `exists_rankOneR_map` — `Φ` permutes rank-one projections (atomicity of the projection order
   is order data).
2. `rayMapR` / `rayMapR_transProbPreservingR` — hence `Φ` induces a self-map of `ℝP^{N-1}`
   preserving the transition probability, which is recovered from the order by the
   Busch–Gudder strength.
3. `exists_isometry_of_transProbPreservingR` — such a map is induced by an isometry.  There is
   no antiunitary branch to consider: over ℝ the alternative does not exist.
4. `isometryMatrixR` — extract the orthogonal matrix.
5. `rankOneR_eq_of_mk_eq` — the ray equality of step 3 becomes an equality of rank-ones, the
   sign ambiguity cancelling because `rankOneR` is quadratic.
6. `linearMap_eq_of_eq_on_rankOneR` + `orthConj_preservesJordan` — rank-ones span, so `Φ` IS
   the conjugation, which is a Jordan automorphism.
-/

noncomputable section

open scoped Matrix
open scoped LinearAlgebra.Projectivization

namespace Necessity

variable {N : ℕ}

/-- Equal nonzero vectors give the same ray (the nonzero proofs are irrelevant). -/
theorem mk_congr_vec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v w : E} (h : v = w) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk ℝ v hv = Projectivization.mk ℝ w hw := by
  subst h; rfl

/-- The Jordan property transfers along an equality of linear maps. -/
theorem preservesJordanR_of_eq
    {S T : HermitianMat (Fin N) ℝ →ₗ[ℝ] HermitianMat (Fin N) ℝ}
    (h : S = T) (hT : PreservesJordan T) : PreservesJordan S := by
  rw [h]
  exact hT

/-- The image of a unit vector under an isometry is a unit vector, in dot-product form. -/
theorem isometry_dotProduct_self
    (e : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    {ψ : Fin N → ℝ} (hψ : ψ ⬝ᵥ ψ = 1) :
    (WithLp.ofLp (e (WithLp.toLp 2 ψ))) ⬝ᵥ (WithLp.ofLp (e (WithLp.toLp 2 ψ))) = 1 := by
  rw [← norm_sq_eq_dotProduct_self, e.norm_map, norm_sq_eq_dotProduct_self]
  exact hψ

/-- **REAL KADISON RIGIDITY, CLASSIFIED.**  Every unital `ℝ`-linear order-automorphism of
`H_N(ℝ)` **is conjugation by an orthogonal matrix**: `Φ = O · (−) · Oᵀ` for some `O` with
`OᵀO = 1` (written `Oᴴ * O = 1`, which over ℝ is the same statement).

This is the classification, not just its Jordan corollary.  The proof already had to produce
the witness in order to conclude anything — `linearMap_eq_of_eq_on_rankOneR` upgrades
agreement on rank-one projections to equality of maps — so the classification is what the
argument actually establishes, and `orderAutoR_preservesJordan` below is a one-line
consequence of it.

Closure is Lean core alone.  Unlike the ℂ statement there is no dichotomy: real Wigner
(`Projectivization.exists_isometry_of_transProbPreservingR`, proved in this tree) returns an
isometry outright, so orthogonal conjugation is the only witness — there is no antiunitary
branch and no transpose alternative. -/
theorem orderAutoR_eq_orthConj (hN : 0 < N)
    (Φ : HermitianMat (Fin N) ℝ →ₗ[ℝ] HermitianMat (Fin N) ℝ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℝ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ) :
    ∃ O : Matrix (Fin N) (Fin N) ℝ, Oᴴ * O = 1 ∧ Φ = orthConj O := by
  classical
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin N)) := by
    refine ⟨⟨0, WithLp.toLp 2 (Function.const (Fin N) (1 : ℝ)), ?_⟩⟩
    intro h
    have := congrFun (congrArg (WithLp.ofLp (p := 2)) h) (Classical.arbitrary (Fin N))
    simp at this
  -- step 3: the induced ray map is induced by an isometry
  obtain ⟨e, he⟩ := Projectivization.exists_isometry_of_transProbPreservingR
    (rayMapR_transProbPreservingR Φ hΦ hunital hsurj)
  -- step 4: its matrix
  refine ⟨isometryMatrixR e, isometryMatrixR_orthogonal e,
    linearMap_eq_of_eq_on_rankOneR Φ (orthConj (isometryMatrixR e)) ?_⟩
  intro ψ hψ
  have hne : (WithLp.toLp 2 ψ : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
    intro hz
    have : ψ ⬝ᵥ ψ = 0 := by
      rw [(WithLp.toLp_eq_zero (p := 2)).mp hz, zero_dotProduct]
    rw [hψ] at this
    exact one_ne_zero this
  obtain ⟨p, hp⟩ : ∃ p : ℙ ℝ (EuclideanSpace ℝ (Fin N)),
      p = Projectivization.mk ℝ (WithLp.toLp 2 ψ) hne := ⟨_, rfl⟩
  -- the unit representative of `p` has the same rank-one as `ψ`
  have hrep : rankOneR (repUnitR p) = rankOneR ψ :=
    rankOneR_eq_of_mk_eq (repUnitR_unit p) hψ (toLp_repUnitR_ne_zero p) hne
      ((mk_repUnitR p).trans hp)
  -- the image vector `e ψ`, in coordinates
  have himg : (e (WithLp.toLp 2 ψ) : EuclideanSpace ℝ (Fin N))
      = WithLp.toLp 2 (isometryMatrixR e *ᵥ ψ) := by
    rw [show (ψ : Fin N → ℝ) = WithLp.ofLp (WithLp.toLp 2 ψ) from rfl, isometryMatrixR_mulVec]
  have hunit : (isometryMatrixR e *ᵥ ψ) ⬝ᵥ (isometryMatrixR e *ᵥ ψ) = 1 := by
    have h := isometry_dotProduct_self e hψ
    rw [himg] at h
    exact h
  have hne' : (WithLp.toLp 2 (isometryMatrixR e *ᵥ ψ) : EuclideanSpace ℝ (Fin N)) ≠ 0 := by
    intro hz
    have hzero : (isometryMatrixR e *ᵥ ψ) ⬝ᵥ (isometryMatrixR e *ᵥ ψ) = 0 := by
      rw [(WithLp.toLp_eq_zero (p := 2)).mp hz, zero_dotProduct]
    rw [hunit] at hzero
    exact one_ne_zero hzero
  -- step 5: the ray equality becomes a rank-one equality
  have hray : Projectivization.mk ℝ (WithLp.toLp 2 (rayVecR Φ hΦ hunital hsurj p))
      (toLp_rayVecR_ne_zero Φ hΦ hunital hsurj p)
      = Projectivization.mk ℝ (WithLp.toLp 2 (isometryMatrixR e *ᵥ ψ)) hne' := by
    have h : rayMapR Φ hΦ hunital hsurj p
        = Projectivization.mk ℝ (WithLp.toLp 2 (isometryMatrixR e *ᵥ ψ)) hne' := by
      rw [he p, hp, Projectivization.projMapR_mk]
      exact mk_congr_vec himg _ _
    exact h
  have hvec : rankOneR (rayVecR Φ hΦ hunital hsurj p) = rankOneR (isometryMatrixR e *ᵥ ψ) :=
    rankOneR_eq_of_mk_eq (rayVecR_unit Φ hΦ hunital hsurj p) hunit
      (toLp_rayVecR_ne_zero Φ hΦ hunital hsurj p) hne' hray
  -- step 6: assemble
  rw [orthConj_rankOneR, ← hvec, ← rayVecR_spec Φ hΦ hunital hsurj p, hrep]

/-- **Real Kadison rigidity, the Jordan corollary.**  Every unital `ℝ`-linear
order-automorphism of `H_N(ℝ)` is a Jordan automorphism.

This is the form the real row consumes (`RealRowUnconditional.thetaPreservesJordanR_of_S2`).
It follows from `orderAutoR_eq_orthConj` because orthogonal conjugation preserves the
symmetrized product: `OᵀO = 1` cancels in the middle of each term. -/
theorem orderAutoR_preservesJordan (hN : 0 < N)
    (Φ : HermitianMat (Fin N) ℝ →ₗ[ℝ] HermitianMat (Fin N) ℝ)
    (hΦ : ∀ x y : HermitianMat (Fin N) ℝ, x ≤ y ↔ Φ x ≤ Φ y) (hunital : Φ 1 = 1)
    (hsurj : Function.Surjective Φ) :
    PreservesJordan Φ := by
  obtain ⟨O, hO, hEq⟩ := orderAutoR_eq_orthConj hN Φ hΦ hunital hsurj
  exact preservesJordanR_of_eq hEq (orthConj_preservesJordan hO)

/-! ## The converse, so the classification is exact rather than one-sided -/

/-- For a square matrix `Oᴴ O = 1` gives the other side too; over ℝ, `Oᴴ = Oᵀ`. -/
theorem mul_transpose_eq_one_of {O : Matrix (Fin N) (Fin N) ℝ} (hO : Oᴴ * O = 1) :
    O * Oᵀ = 1 := by
  have h : Oᴴ = Oᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [← h]
  exact Matrix.mul_eq_one_comm.mp hO

/-- Orthogonal conjugation reflects the Loewner order, not just preserves it: conjugating
back by `Oᴴ` is the inverse operation. -/
theorem orthConj_le_iff {O : Matrix (Fin N) (Fin N) ℝ} (hO : Oᴴ * O = 1)
    (x y : HermitianMat (Fin N) ℝ) : orthConj O x ≤ orthConj O y ↔ x ≤ y := by
  constructor
  · intro h
    have h2 : (x.conj O).conj Oᴴ ≤ (y.conj O).conj Oᴴ := HermitianMat.conj_mono h
    rwa [HermitianMat.conj_conj, HermitianMat.conj_conj, hO, HermitianMat.conj_one,
      HermitianMat.conj_one] at h2
  · exact fun h => HermitianMat.conj_mono h

/-- Orthogonal conjugation is unital. -/
theorem orthConj_one {O : Matrix (Fin N) (Fin N) ℝ} (hO : Oᴴ * O = 1) :
    orthConj O (1 : HermitianMat (Fin N) ℝ) = 1 := by
  ext1
  rw [orthConj_apply, HermitianMat.conj_apply_mat]
  simp [mul_transpose_eq_one_of hO]

/-- Orthogonal conjugation is surjective, with `Oᴴ`-conjugation as the preimage. -/
theorem orthConj_surjective {O : Matrix (Fin N) (Fin N) ℝ} (hO : Oᴴ * O = 1) :
    Function.Surjective (orthConj O) := by
  intro y
  refine ⟨y.conj Oᴴ, ?_⟩
  rw [orthConj_apply, HermitianMat.conj_conj]
  simp [mul_transpose_eq_one_of hO]

/-- **The converse, so the classification is exact.**  Conjugation by an orthogonal matrix
*is* a unital order-automorphism, so together with `orderAutoR_eq_orthConj` the
order-automorphism group of `H_N(ℝ)` is exactly `{Ad_O : OᵀO = 1}` — the classification
characterizes it rather than merely embedding it. -/
theorem orthConj_orderAuto {O : Matrix (Fin N) (Fin N) ℝ} (hO : Oᴴ * O = 1) :
    (∀ x y : HermitianMat (Fin N) ℝ, x ≤ y ↔ orthConj O x ≤ orthConj O y)
      ∧ orthConj O 1 = 1 ∧ Function.Surjective (orthConj O) :=
  ⟨fun x y => (orthConj_le_iff hO x y).symm, orthConj_one hO, orthConj_surjective hO⟩

end Necessity
