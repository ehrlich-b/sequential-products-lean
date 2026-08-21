/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockSkew
import RadicalRelativity.MasterTheorem.DiagonalHom
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-
### The one first-party use of `backward.isDefEq.respectTransparency`

Lean v4.33 flipped `backward.isDefEq.respectTransparency`: `isDefEq` at `.instances`
transparency no longer unfolds non-reducible instance definitions. `HermitianMat` carries two
definitionally-equal-but-not-syntactically-equal topologies (see
`RadicalRelativity.Hermitian.OperatorInstances` for the full account), and everywhere else in
this development the fix is an explicit instance bridge, which is permanent and survives the
eventual removal of the `backward.*` compatibility knobs.

That approach does NOT terminate here. `blockSkewSubmodule` is a submodule of the endomorphism
space, so the mismatch has to be bridged at every layer of the submodule's own instance chain:
`NormedAddCommGroup`, then `NormedSpace`, then `IsScalarTower`, and the last of these cannot be
supplied at all — declaring `IsScalarTower ℝ ℝ (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ)`
explicitly still leaves synthesis unable to find it, because by that depth the `SMul` instances
themselves have diverged. Each bridge also widens the diamond it is patching.

So this file uses the knob instead. Consequences, recorded honestly: it is a compatibility
option scheduled for removal, and when it goes this file needs revisiting. Upstream physlib made
the same trade — the vendored `HermitianMat/Basic.lean` carries six such lines, and the island
40 in total.
-/
set_option backward.isDefEq.respectTransparency false

set_option linter.style.longLine false

/-!
# The concrete `DiagonalHomSetup` on `H_N(ℂ)`  (LEDGER 2.6, u5c — the finish)

The differential face, concretely: `V := ℝ × ℝ` models every off-diagonal
block; `Stab` is the submodule of block-skew endomorphisms; `ρ_{ij}` is the
block compression `blockCoord ∘ ξ ∘ blockEmbed` (zero on the diagonal pairs,
where the abstract field's unrestricted quantifier has no content); `dχ` lands
in `Stab` by `dChi_block_skew` (`prop:isotropy`); and `coalescence_diff` is
`dChi_kills_corner` read through the block embedding. The abstract
`toStabilizerCoupling` then **produces the coupling
`ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}` on the concrete carrier**.
-/

noncomputable section

open ComplexOrder
open scoped Matrix InnerProductSpace
open OrderUnitSpace
open MasterTheorem

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## Block coordinates as linear maps -/

/-- Block coordinates `x ↦ (Re x_{ij}, Im x_{ij})`. -/
def blockCoordLm (i j : n) : HermitianMat n ℂ →ₗ[ℝ] ℝ × ℝ :=
  LinearMap.prod (Complex.reLm ∘ₗ entryLm i j) (Complex.imLm ∘ₗ entryLm i j)

@[simp]
theorem blockCoordLm_apply (i j : n) (x : HermitianMat n ℂ) :
    blockCoordLm i j x = ((x.mat i j).re, (x.mat i j).im) := rfl

/-- Block embedding `(v₁, v₂) ↦ blockHerm (v₁ + v₂ i)`. -/
def blockEmbedLm (i j : n) : ℝ × ℝ →ₗ[ℝ] HermitianMat n ℂ where
  toFun v := blockHerm i j ((v.1 : ℂ) + v.2 * Complex.I)
  map_add' u v := by
    have hz : (((u + v).1 : ℂ) + (u + v).2 * Complex.I)
        = ((u.1 : ℂ) + u.2 * Complex.I) + ((v.1 : ℂ) + v.2 * Complex.I) := by
      rw [Prod.fst_add, Prod.snd_add]
      push_cast
      ring
    ext1
    rw [hz]
    simp only [blockHerm_mat, HermitianMat.mat_add, star_add, add_smul]
    abel
  map_smul' c v := by
    have hz : (((c • v).1 : ℂ) + (c • v).2 * Complex.I)
        = (c : ℂ) * ((v.1 : ℂ) + v.2 * Complex.I) := by
      rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul]
      push_cast
      ring
    ext1
    rw [hz]
    simp only [blockHerm_mat, HermitianMat.mat_smul, RingHom.id_apply]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [mul_smul, mul_smul, ← smul_add]
    ext a b
    simp [Complex.real_smul, mul_add]

@[simp]
theorem blockEmbedLm_apply (i j : n) (v : ℝ × ℝ) :
    blockEmbedLm i j v = blockHerm i j ((v.1 : ℂ) + v.2 * Complex.I) := rfl

/-! ## The block-skew stabilizer submodule -/

/-- Block-skewness of an endomorphism: on every off-diagonal block, its
compression is Euclidean-skew. -/
def IsBlockSkew (ξ : HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) : Prop :=
  ∀ (i j : n), i ≠ j → ∀ v1 v2 : ℝ,
    v1 * ((ξ (blockHerm i j ((v1 : ℂ) + v2 * Complex.I))).mat i j).re
      + v2 * ((ξ (blockHerm i j ((v1 : ℂ) + v2 * Complex.I))).mat i j).im = 0

/-- The stabilizer: block-skew endomorphisms form a submodule. -/
def blockSkewSubmodule :
    Submodule ℝ (HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) where
  carrier := {ξ | IsBlockSkew ξ}
  zero_mem' := by
    intro i j hij v1 v2
    simp
  add_mem' := by
    intro ξ η hξ hη i j hij v1 v2
    have h1 := hξ i j hij v1 v2
    have h2 := hη i j hij v1 v2
    simp only [ContinuousLinearMap.add_apply, HermitianMat.mat_add,
      Matrix.add_apply, Complex.add_re, Complex.add_im]
    linarith [h1, h2]
  smul_mem' := by
    intro c ξ hξ i j hij v1 v2
    have h := hξ i j hij v1 v2
    simp only [ContinuousLinearMap.smul_apply, HermitianMat.mat_smul,
      Matrix.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    linear_combination c * h

/-- `dχ(r)` is block-skew (`prop:isotropy`). -/
theorem dChi_mem_blockSkew (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r : n → ℝ) :
    dChi P hS2 hjord r ∈ blockSkewSubmodule (n := n) :=
  fun i j hij v1 v2 => dChi_block_skew P hS2 hjord r hij v1 v2

/-! ## The block compression `ρ` -/

/-- The compression of a stabilizer element to the `(i,j)` block (zero on
diagonal pairs, where the interface's quantifier has no content). -/
def rhoField (i j : n) :
    ↥(blockSkewSubmodule (n := n)) →ₗ[ℝ] ((ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :=
  if i = j then 0 else
  { toFun := fun ξ =>
      (blockCoordLm i j) ∘ₗ ((ξ.val : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ)
        ∘ₗ (blockEmbedLm i j))
    map_add' := by
      intro ξ η
      ext v <;> rfl
    map_smul' := by
      intro c ξ
      ext v <;>
        simp [LinearMap.comp_apply, Submodule.coe_smul, ContinuousLinearMap.coe_smul,
          LinearMap.smul_apply, HermitianMat.mat_smul, Matrix.smul_apply,
          smul_eq_mul] }

theorem rhoField_apply_of_ne {i j : n} (hij : i ≠ j)
    (ξ : ↥(blockSkewSubmodule (n := n))) (v : ℝ × ℝ) :
    rhoField i j ξ v
      = blockCoordLm i j (ξ.val (blockEmbedLm i j v)) := by
  unfold rhoField
  rw [if_neg hij]
  rfl

theorem rhoField_diag (i : n) : rhoField (n := n) i i = 0 := by
  unfold rhoField
  rw [if_pos rfl]

/-! ## The differential into the stabilizer -/

/-- `dχ` as an additive map into the block-skew stabilizer. -/
def dChiStab (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    (n → ℝ) →+ ↥(blockSkewSubmodule (n := n)) where
  toFun r := ⟨dChi P hS2 hjord r, dChi_mem_blockSkew P hS2 hjord r⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' r r' := Subtype.ext (map_add _ _ _)

theorem dChiStab_cont (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    Continuous (dChiStab P hS2 hjord) := by
  apply Continuous.subtype_mk
  exact (dChi P hS2 hjord).continuous_of_finiteDimensional

/-- Differentiated coalescence through the compression: on coalesced pairs the
block compression of `dχ(r)` vanishes. -/
theorem rhoField_dChi_coalesced (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (i j : n) (r : n → ℝ) (h : r i = r j) :
    rhoField i j (dChiStab P hS2 hjord r) = 0 := by
  by_cases hij : i = j
  · rw [hij, rhoField_diag]
    rfl
  · apply LinearMap.ext
    intro v
    rw [rhoField_apply_of_ne hij]
    have hcorner : cornerJ2 i j (blockEmbedLm i j v) := by
      apply blockElt_cornerJ2
      intro k hki hkj
      show jordanBilin (frameProj k)
        (blockHerm i j ((v.1 : ℂ) + v.2 * Complex.I)) = 0
      rw [jordanBilin_apply]
      exact frameProj_symmMul_blockHerm_other hki hkj _
    have hkill := dChi_kills_corner P hS2 hjord h hcorner
    show blockCoordLm i j ((dChiStab P hS2 hjord r).val (blockEmbedLm i j v)) = 0
    rw [show (dChiStab P hS2 hjord r).val = dChi P hS2 hjord r from rfl]
    rw [show (dChi P hS2 hjord r) (blockEmbedLm i j v)
        = dChi P hS2 hjord r (blockEmbedLm i j v) from rfl, hkill]
    simp

/-! ## The instance and the coupling -/

/-- The block model with the L² product structure (`ℝ × ℝ` itself carries only
the sup norm, which admits no inner product). -/
abbrev BlockV : Type := WithLp 2 (ℝ × ℝ)

/-- The compression, transported to the L² model. -/
def rhoFieldL2 (i j : n) :
    ↥(blockSkewSubmodule (n := n)) →ₗ[ℝ] (BlockV →ₗ[ℝ] BlockV) where
  toFun ξ := (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm.toLinearMap
    ∘ₗ (rhoField i j ξ) ∘ₗ (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).toLinearMap
  map_add' ξ η := by
    ext v <;> simp [map_add]
  map_smul' c ξ := by
    ext v <;> simp [map_smul]

theorem rhoFieldL2_apply (i j : n) (ξ : ↥(blockSkewSubmodule (n := n)))
    (x : BlockV) :
    rhoFieldL2 i j ξ x
      = (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm
          (rhoField i j ξ (WithLp.linearEquiv 2 ℝ (ℝ × ℝ) x)) := rfl

/-- The normed structure on the stabilizer, exported so that downstream files
(`Necessity.PhaseAnchor`) inherit it and do NOT need the `respectTransparency` knob above.
Declaring it here keeps that compatibility option confined to this one file. -/
noncomputable instance instNormedAddCommGroupBlockSkew :
    NormedAddCommGroup ↥(blockSkewSubmodule (n := n)) :=
  Submodule.normedAddCommGroup (𝕜 := ℝ)
    (E := HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) (s := blockSkewSubmodule)

/-- Likewise the `ℝ`-normed-space structure, exported for downstream use. -/
noncomputable instance instNormedSpaceBlockSkew :
    NormedSpace ℝ ↥(blockSkewSubmodule (n := n)) :=
  Submodule.normedSpace (𝕜 := ℝ)
    (E := HermitianMat n ℂ →L[ℝ] HermitianMat n ℂ) (s := blockSkewSubmodule)

/-- **The concrete `DiagonalHomSetup` on `H_N(ℂ)`.** Every differential-face
field is a proved theorem of this development; the comparison face is
`coalescenceSetup`, whose only cited field remains `Θ_jordan` (M3). -/
def diagonalHomSetup {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    DiagonalHomSetup (HermitianMat (Fin N) ℂ)
      (↥(blockSkewSubmodule (n := Fin N))) BlockV :=
  { coalescenceSetup hN P hS2 hjord with
    ρ := rhoFieldL2
    ρ_skew := by
      intro i j ξ x
      show ⟪(rhoFieldL2 (n := Fin N) i j) ξ x, x⟫_ℝ = 0
      by_cases hij : i = j
      · rw [rhoFieldL2_apply, hij, rhoField_diag]
        simp
      · rw [rhoFieldL2_apply, rhoField_apply_of_ne (n := Fin N) hij]
        set u := WithLp.linearEquiv 2 ℝ (ℝ × ℝ) x with hu
        have hs := ξ.property i j hij u.1 u.2
        rw [WithLp.prod_inner_apply]
        simp only [blockCoordLm_apply, blockEmbedLm_apply, RCLike.inner_apply,
          starRingEnd_apply, star_trivial]
        exact hs
    dχAdd := dChiStab P hS2 hjord
    dχAdd_cont := dChiStab_cont P hS2 hjord
    coalescence_diff := by
      intro i j r h
      have h0 := rhoField_dChi_coalesced (n := Fin N) P hS2 hjord i j r h
      apply LinearMap.ext
      intro v
      show (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).symm
        ((rhoField (n := Fin N) i j ((dChiStab P hS2 hjord) r))
          ((WithLp.linearEquiv 2 ℝ (ℝ × ℝ)) v)) = 0
      rw [h0]
      simp }

/-- **The stabilizer coupling on `H_N(ℂ)`, PRODUCED**: the coupling field
`ρ_{ij}(dχ(r)) = (r_i − r_j) • T_{ij}` is proved by the abstract
`hyperplane_factorization` applied to the concrete differential face. -/
def stabilizerCoupling {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    StabilizerCoupling N (↥(blockSkewSubmodule (n := Fin N))) BlockV :=
  (diagonalHomSetup hN P hS2 hjord).toStabilizerCoupling

end Necessity
