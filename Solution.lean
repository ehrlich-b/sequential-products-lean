/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import RadicalRelativity.Necessity.OrderUnitS2

/-!
# Solution: the two classification theorems

This module repeats, verbatim, the definitions of `Challenge.lean` and proves the two
theorems stated there.  The definitions must be textually identical to the Challenge's:
Comparator compiles the two modules in separate environments and rejects the submission
unless every declaration reachable from the statements is the same in both.

The mathematics is in `RadicalRelativity`; this file is the bridge from the bare-matrix
statement to the development's `HermitianMat` carrier.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace TwistNormalForm

/-- `Mat N 𝕜` is the algebra of `N × N` matrices over `𝕜`.  The two results below
instantiate `𝕜` at `ℝ` and at `ℂ`. -/
abbrev Mat (N : ℕ) (𝕜 : Type) := Matrix (Fin N) (Fin N) 𝕜

section Order

variable {N : ℕ} {𝕜 : Type} [RCLike 𝕜] [PartialOrder 𝕜]

/-- **The Loewner order.**  `A ≼ B` means `B - A` is positive semidefinite.
`Matrix.PosSemidef M` unfolds to `M.IsHermitian ∧ ∀ x, 0 ≤ ∑ᵢⱼ star xᵢ * Mᵢⱼ * xⱼ`,
so `A ≼ B` carries Hermitianness of `B - A` as well as positivity.

For `𝕜 = ℂ` the ambient `PartialOrder ℂ` is the standard one from the `ComplexOrder`
scope, `z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`, opened at the top of this file; for `𝕜 = ℝ`
it is the usual order on `ℝ`. -/
def Loewner (A B : Mat N 𝕜) : Prop := (B - A).PosSemidef

@[inherit_doc] scoped infix:50 " ≼ " => Loewner

/-- The real scalar `t` times the identity matrix, `t • 𝟙`, written out as a diagonal
matrix so that no `ℝ`-module structure on `Mat N 𝕜` is implicit in the statement. -/
def scalUnit (N : ℕ) (𝕜 : Type) [RCLike 𝕜] (t : ℝ) : Mat N 𝕜 :=
  Matrix.diagonal fun _ => (t : 𝕜)

/-- **An effect** is an element of the order interval `[0, 𝟙]` in the Loewner order.
These are the elements the sequential product is defined on: `0 ≼ A ≼ 𝟙`. -/
def IsEffect (A : Mat N 𝕜) : Prop := (0 : Mat N 𝕜) ≼ A ∧ A ≼ (1 : Mat N 𝕜)

/-- **The order-unit norm** determined by the order unit `𝟙`:
`‖A‖ₑ = inf {t ≥ 0 : -t • 𝟙 ≼ A ≼ t • 𝟙}`.

This is the norm in which the manuscript's continuity axiom S2 is stated.  It is
defined here purely from the order, so that the statement below depends on no
normed-space instance.

★ **This is a junk extension off the Hermitian matrices, and deliberately so.** If `A` is not
Hermitian the defining set is empty (either Loewner inequality would force a real-scalar
translate of `A` to be Hermitian), and Mathlib's `sInf ∅ = 0`, so `ouNorm A = 0`. That value
carries no meaning. It is harmless because every use below is guarded: effects are Hermitian,
differences of effects are Hermitian, and `SeqProd.effect` keeps outputs Hermitian. `ouNorm` is
asserted to be the order-unit norm only on the Hermitian part. -/
def ouNorm (A : Mat N 𝕜) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ -scalUnit N 𝕜 t ≼ A ∧ A ≼ scalUnit N 𝕜 t}

end Order

/-- **A sequential product on the effects of `Mat N 𝕜`**, carrying the algebraic axioms
S1 and S3--S7 of van de Wetering (arXiv:1803.11139, Definition 2) together with closure
of the operation on the effect interval.  The topological axiom S2 is *not* a field: it
is the separate predicate `S2` below, so that it can be read off the statement.

Write `a & b` for `sp a b`, read "first test `a`, then test `b`".  All axioms are
hypothesised only for effects; the values of `sp` off the effect interval are
unconstrained and never occur in the conclusions. -/
structure SeqProd (N : ℕ) (𝕜 : Type) [RCLike 𝕜] [PartialOrder 𝕜] where
  /-- The sequential product operation `a & b`. -/
  sp : Mat N 𝕜 → Mat N 𝕜 → Mat N 𝕜
  /-- **S1** (additivity in the second argument): `a & (b + c) = a & b + a & c`
  whenever `b + c` is again an effect. -/
  add_right : ∀ {a b c : Mat N 𝕜}, IsEffect a → IsEffect b → IsEffect c →
    (b + c) ≼ (1 : Mat N 𝕜) → sp a (b + c) = sp a b + sp a c
  /-- **S3** (unitality): `𝟙 & a = a`. -/
  unit_left : ∀ {a : Mat N 𝕜}, IsEffect a → sp 1 a = a
  /-- **S4** (symmetry of orthogonality): `a & b = 0 → b & a = 0`. -/
  zero_symm : ∀ {a b : Mat N 𝕜}, IsEffect a → IsEffect b → sp a b = 0 → sp b a = 0
  /-- **S5** (associativity for compatible effects): if `a` and `b` commute under `&`
  then `a & (b & c) = (a & b) & c`. -/
  assoc_of_comm : ∀ {a b c : Mat N 𝕜}, IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a (sp b c) = sp (sp a b) c
  /-- **S6a** (compatibility passes to the orthocomplement): if `a` and `b` commute
  under `&` then so do `a` and `𝟙 - b`. -/
  comm_ortho : ∀ {a b : Mat N 𝕜}, IsEffect a → IsEffect b →
    sp a b = sp b a → sp a (1 - b) = sp (1 - b) a
  /-- **S6b** (compatibility is additive): if `a` commutes with `b` and with `c`, and
  `b + c` is an effect, then `a` commutes with `b + c`. -/
  comm_add : ∀ {a b c : Mat N 𝕜}, IsEffect a → IsEffect b → IsEffect c →
    (b + c) ≼ (1 : Mat N 𝕜) →
    sp a b = sp b a → sp a c = sp c a → sp a (b + c) = sp (b + c) a
  /-- **S7** (compatibility is multiplicative): if `a` commutes with `b` and with `c`
  then `a` commutes with `b & c`. -/
  comm_sp : ∀ {a b c : Mat N 𝕜}, IsEffect a → IsEffect b → IsEffect c →
    sp a b = sp b a → sp a c = sp c a → sp a (sp b c) = sp (sp b c) a
  /-- Closure: the sequential product of two effects is an effect. -/
  effect : ∀ {a b : Mat N 𝕜}, IsEffect a → IsEffect b → IsEffect (sp a b)

/-- **Axiom S2, verbatim**: for each fixed effect `b`, the map `a ↦ a & b` is continuous
on the effect interval, with both distances measured in the order-unit norm `‖·‖ₑ`.
Written as an ε--δ condition so that it refers to no topology instance. -/
def S2 {N : ℕ} {𝕜 : Type} [RCLike 𝕜] [PartialOrder 𝕜] (P : SeqProd N 𝕜) : Prop :=
  ∀ ⦃b : Mat N 𝕜⦄, IsEffect b →
    ∀ a₀ : Mat N 𝕜, IsEffect a₀ → ∀ ε > 0, ∃ δ > 0,
      ∀ a : Mat N 𝕜, IsEffect a → ouNorm (a - a₀) < δ →
        ouNorm (P.sp a b - P.sp a₀ b) < ε

/-- **The Lüders product** `a ⊙ b = √a · b · √a`, where `√a` is the continuous
functional calculus of `Real.sqrt` at `a` (Mathlib's `cfc` for Hermitian matrices). -/
def luders {N : ℕ} {𝕜 : Type} [RCLike 𝕜] (a b : Mat N 𝕜) : Mat N 𝕜 :=
  cfc Real.sqrt a * b * cfc Real.sqrt a

-- ★ Mathlib's `cfc` also returns the junk value `0` when its argument is not self-adjoint, so
-- `luders` and `twist` below are likewise meaningful only on Hermitian arguments. Both
-- conclusions are stated only for effects, which are Hermitian.

/-- **The twist factor** `a ^ (1/2 + i t)`, defined by the continuous functional calculus
as `√x · cos(t log x) + i · √x · sin(t log x)` applied to `a`.  On the spectrum of a
positive `a` this is the principal branch of `x ↦ x ^ (1/2 + i t)`; at the eigenvalue `0`
both components vanish, so the singular case is included with the value `0`. -/
def twistFactor {N : ℕ} (t : ℝ) (a : Mat N ℂ) : Mat N ℂ :=
  cfc (fun x : ℝ => Real.sqrt x * Real.cos (t * Real.log x)) a
    + Complex.I • cfc (fun x : ℝ => Real.sqrt x * Real.sin (t * Real.log x)) a

/-- **The twist product** `a ⊙ₜ b = a ^ (1/2 + i t) · b · a ^ (1/2 - i t)`.  At `t = 0`
it is the Lüders product. -/
def twist {N : ℕ} (t : ℝ) (a b : Mat N ℂ) : Mat N ℂ :=
  twistFactor t a * b * (twistFactor t a)ᴴ

/-! ## Bridge to the `HermitianMat` development

The definitions above are stated on bare `Matrix (Fin N) (Fin N) 𝕜` so that
`Challenge.lean` depends on Mathlib alone.  The development in `RadicalRelativity`
works on `HermitianMat (Fin N) 𝕜 = selfAdjoint (Matrix (Fin N) (Fin N) 𝕜)`, its
Loewner order, and its order-unit norm.  This section identifies the two.

Every bridge here is either `rfl` or a one-line rewrite: the carrier is a subtype of
the matrices, `HermitianMat.cfc` is by definition Mathlib's `cfc` on the underlying
matrix, and `HermitianMat.twistSeq` is by definition the twist product above. -/

section Bridge

variable {N : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- The carrier's order is the Loewner order. -/
theorem loewner_iff (A B : HermitianMat (Fin N) 𝕜) : A ≤ B ↔ Loewner A.mat B.mat := by
  rw [HermitianMat.le_iff]; rfl

/-- The carrier's effect interval is the matrix effect interval. -/
theorem isEffect_iff (A : HermitianMat (Fin N) 𝕜) :
    OrderUnitSpace.IsEffect A ↔ IsEffect A.mat := by
  unfold OrderUnitSpace.IsEffect IsEffect Loewner
  rw [HermitianMat.le_iff, HermitianMat.le_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1, by simpa using h2⟩

/-- `HermitianMat.cfc` is Mathlib's `cfc` on the underlying matrix. -/
theorem mat_cfc_sqrt (A : HermitianMat (Fin N) 𝕜) :
    (A.cfc Real.sqrt).mat = cfc Real.sqrt A.mat := rfl

/-- The development's twist product is the twist product of `Challenge.lean`. -/
theorem mat_twistSeq (t : ℝ) (a b : HermitianMat (Fin N) ℂ) :
    (HermitianMat.twistSeq t a b).mat = twist t a.mat b.mat := rfl

/-- The scaled unit of the carrier is the scaled unit matrix. -/
theorem mat_smul_one (t : ℝ) :
    ((t • (1 : HermitianMat (Fin N) 𝕜)) : HermitianMat (Fin N) 𝕜).mat = scalUnit N 𝕜 t := by
  unfold scalUnit
  ext i j
  by_cases h : i = j <;>
    simp [h, Matrix.diagonal, RCLike.real_smul_eq_coe_mul]

/-- The carrier's order-unit norm is the order-unit norm of `Challenge.lean`. -/
theorem ouNorm_eq (A : HermitianMat (Fin N) 𝕜) :
    HermitianMat.ouNorm A = ouNorm A.mat := by
  unfold HermitianMat.ouNorm ouNorm
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, loewner_iff, HermitianMat.mat_neg, mat_smul_one]

/-- **The Hermitian repackaging of a `SeqProd`.**  A `SeqProd` is a total operation on
matrices whose axioms constrain it only on effects; the development's
`SequentialProductOn` lives on the Hermitian subtype.  Off the effect interval the value
is irrelevant, so it is sent to `0`. -/
def spHM (P : SeqProd N 𝕜) (x y : HermitianMat (Fin N) 𝕜) : HermitianMat (Fin N) 𝕜 :=
  haveI : Decidable (IsEffect x.mat ∧ IsEffect y.mat) := Classical.dec _
  if h : IsEffect x.mat ∧ IsEffect y.mat then
    ⟨P.sp x.mat y.mat, by
      have := (P.effect h.1 h.2).1
      unfold Loewner at this
      rw [sub_zero] at this
      exact Matrix.isHermitian_iff_isSelfAdjoint.mp this.1⟩
  else 0

@[simp] theorem spHM_of_effect (P : SeqProd N 𝕜) {x y : HermitianMat (Fin N) 𝕜}
    (hx : IsEffect x.mat) (hy : IsEffect y.mat) :
    (spHM P x y).mat = P.sp x.mat y.mat := by
  unfold spHM; rw [dif_pos ⟨hx, hy⟩]; rfl

/-- **The repackaging carries S1 and S3--S7.**  Each field is the corresponding field of
`P` transported along `isEffect_iff`, `spHM_of_effect` and `HermitianMat.ext`. -/
def toHM (P : SeqProd N 𝕜) : SequentialProductOn (HermitianMat (Fin N) 𝕜) where
  sp := spHM P
  sp_add_right := by
    intro a b c ha hb hc hbc
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    have hc' : IsEffect c.mat := (isEffect_iff c).mp hc
    have hbc' : IsEffect (b + c).mat :=
      (isEffect_iff (b + c)).mp ⟨add_nonneg hb.1 hc.1, hbc⟩
    apply HermitianMat.ext
    rw [HermitianMat.mat_add (spHM P a b) (spHM P a c), spHM_of_effect P ha' hbc',
      spHM_of_effect P ha' hb', spHM_of_effect P ha' hc']
    exact P.add_right ha' hb' hc' hbc'.2
  sp_unit_left := by
    intro a ha
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have h1 : IsEffect (OrderUnitSpace.ousUnit : HermitianMat (Fin N) 𝕜).mat :=
      (isEffect_iff _).mp ⟨OrderUnitSpace.ousUnit_nonneg, le_rfl⟩
    apply HermitianMat.ext
    rw [spHM_of_effect P h1 ha']
    exact P.unit_left ha'
  sp_zero_symm := by
    intro a b ha hb h
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    have h' : P.sp a.mat b.mat = 0 := by
      have hh := congrArg HermitianMat.mat h
      rwa [spHM_of_effect P ha' hb', HermitianMat.mat_zero] at hh
    apply HermitianMat.ext
    rw [spHM_of_effect P hb' ha', HermitianMat.mat_zero]
    exact P.zero_symm ha' hb' h'
  sp_assoc_of_compatible := by
    intro a b c ha hb hc hab
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    have hc' : IsEffect c.mat := (isEffect_iff c).mp hc
    have hbcE : IsEffect (spHM P b c).mat := by
      rw [spHM_of_effect P hb' hc']; exact P.effect hb' hc'
    have habE : IsEffect (spHM P a b).mat := by
      rw [spHM_of_effect P ha' hb']; exact P.effect ha' hb'
    have hab' : P.sp a.mat b.mat = P.sp b.mat a.mat := by
      have hh := congrArg HermitianMat.mat hab
      rwa [spHM_of_effect P ha' hb', spHM_of_effect P hb' ha'] at hh
    apply HermitianMat.ext
    rw [spHM_of_effect P ha' hbcE, spHM_of_effect P habE hc',
      spHM_of_effect P hb' hc', spHM_of_effect P ha' hb']
    exact P.assoc_of_comm ha' hb' hc' hab'
  compatible_ortho := by
    intro a b ha hb hab
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    have hob : IsEffect (OrderUnitSpace.ousUnit - b : HermitianMat (Fin N) 𝕜).mat :=
      (isEffect_iff _).mp
        ⟨OrderUnitSpace.sub_nonneg_of_le hb.2, OrderUnitSpace.sub_le_self_of_nonneg hb.1⟩
    have hab' : P.sp a.mat b.mat = P.sp b.mat a.mat := by
      have hh := congrArg HermitianMat.mat hab
      rwa [spHM_of_effect P ha' hb', spHM_of_effect P hb' ha'] at hh
    apply HermitianMat.ext
    rw [spHM_of_effect P ha' hob, spHM_of_effect P hob ha']
    exact P.comm_ortho ha' hb' hab'
  compatible_add := by
    intro a b c ha hb hc hbc hab hac
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    have hc' : IsEffect c.mat := (isEffect_iff c).mp hc
    have hbc' : IsEffect (b + c).mat :=
      (isEffect_iff (b + c)).mp ⟨add_nonneg hb.1 hc.1, hbc⟩
    have hab' : P.sp a.mat b.mat = P.sp b.mat a.mat := by
      have hh := congrArg HermitianMat.mat hab
      rwa [spHM_of_effect P ha' hb', spHM_of_effect P hb' ha'] at hh
    have hac' : P.sp a.mat c.mat = P.sp c.mat a.mat := by
      have hh := congrArg HermitianMat.mat hac
      rwa [spHM_of_effect P ha' hc', spHM_of_effect P hc' ha'] at hh
    apply HermitianMat.ext
    rw [spHM_of_effect P ha' hbc', spHM_of_effect P hbc' ha']
    exact P.comm_add ha' hb' hc' hbc'.2 hab' hac'
  compatible_sp := by
    intro a b c ha hb hc hab hac
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    have hc' : IsEffect c.mat := (isEffect_iff c).mp hc
    have hbcE : IsEffect (spHM P b c).mat := by
      rw [spHM_of_effect P hb' hc']; exact P.effect hb' hc'
    have hab' : P.sp a.mat b.mat = P.sp b.mat a.mat := by
      have hh := congrArg HermitianMat.mat hab
      rwa [spHM_of_effect P ha' hb', spHM_of_effect P hb' ha'] at hh
    have hac' : P.sp a.mat c.mat = P.sp c.mat a.mat := by
      have hh := congrArg HermitianMat.mat hac
      rwa [spHM_of_effect P ha' hc', spHM_of_effect P hc' ha'] at hh
    apply HermitianMat.ext
    rw [spHM_of_effect P ha' hbcE, spHM_of_effect P hbcE ha', spHM_of_effect P hb' hc']
    exact P.comm_sp ha' hb' hc' hab' hac'
  sp_effect := by
    intro a b ha hb
    have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
    have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
    refine (isEffect_iff _).mpr ?_
    rw [spHM_of_effect P ha' hb']
    exact P.effect ha' hb'

/-- **S2 transports.**  Both sides are the same ε--δ condition once `ouNorm_eq` and
`isEffect_iff` are applied. -/
theorem toHM_S2' (P : SeqProd N 𝕜) (Q : SequentialProductOn (HermitianMat (Fin N) 𝕜))
    (hQ : ∀ x y : HermitianMat (Fin N) 𝕜, IsEffect x.mat → IsEffect y.mat →
      (Q.sp x y).mat = P.sp x.mat y.mat)
    (hS2 : S2 P) : Necessity.FirstArgContinuousOu Q := by
  intro b hb a₀ ha₀ ε hε
  have hb' : IsEffect b.mat := (isEffect_iff b).mp hb
  have ha₀' : IsEffect a₀.mat := (isEffect_iff a₀).mp ha₀
  obtain ⟨δ, hδ, hmain⟩ := hS2 hb' a₀.mat ha₀' ε hε
  refine ⟨δ, hδ, fun a ha hd => ?_⟩
  have ha' : IsEffect a.mat := (isEffect_iff a).mp ha
  have hd' : ouNorm (a.mat - a₀.mat) < δ := by
    rw [← HermitianMat.mat_sub, ← ouNorm_eq]; exact hd
  have hgoal := hmain a.mat ha' hd'
  simp only [ouNorm_eq, HermitianMat.mat_sub, hQ a b ha' hb', hQ a₀ b ha₀' hb']
  exact hgoal

theorem toHM_S2 (P : SeqProd N 𝕜) (hS2 : S2 P) :
    Necessity.FirstArgContinuousOu (toHM P) :=
  toHM_S2' P (toHM P) (fun x y hx hy => spHM_of_effect P hx hy) hS2

end Bridge

/-- Lift a matrix known to be an effect into the Hermitian carrier.  Positivity carries
Hermitianness, so no extra hypothesis is needed. -/
def liftEffect {N : ℕ} {𝕜 : Type} [RCLike 𝕜] {A : Mat N 𝕜}
    (hA : IsEffect A) : HermitianMat (Fin N) 𝕜 :=
  ⟨A, by
    have h := hA.1
    unfold Loewner at h
    rw [sub_zero] at h
    exact Matrix.isHermitian_iff_isSelfAdjoint.mp h.1⟩

@[simp] theorem liftEffect_mat {N : ℕ} {𝕜 : Type} [RCLike 𝕜] {A : Mat N 𝕜}
    (hA : IsEffect A) : (liftEffect hA).mat = A := rfl

theorem isEffect_liftEffect {N : ℕ} {𝕜 : Type} [RCLike 𝕜] {A : Mat N 𝕜}
    (hA : IsEffect A) : OrderUnitSpace.IsEffect (liftEffect hA) := by
  rw [isEffect_iff, liftEffect_mat]; exact hA

/-! ## The two results -/

/-- **The real row.**  On the Hermitian `N × N` real matrices with `N ≥ 1`, every
sequential product satisfying S1--S7 is the Lüders product `a & b = √a · b · √a`.
There is no free parameter: the classification is rigid.

(van de Wetering, arXiv:1803.11139, Definition 2 for the axioms; the classification
statement is Theorem `mthm:master`, real row, of the accompanying manuscript.) -/
theorem real_classification {N : ℕ} (hN : 0 < N)
    (P : SeqProd N ℝ) (hS2 : S2 P)
    {a b : Mat N ℝ} (ha : IsEffect a) (hb : IsEffect b) :
    P.sp a b = luders a b := by
  have key := Necessity.real_classification_ouNorm hN (toHM P) (toHM_S2 P hS2)
    (isEffect_liftEffect hb) (liftEffect ha) (isEffect_liftEffect ha)
  have hm := congrArg HermitianMat.mat key
  rw [show ((toHM P).sp (liftEffect ha) (liftEffect hb)) = spHM P (liftEffect ha) (liftEffect hb)
        from rfl, spHM_of_effect P (by simpa using ha) (by simpa using hb)] at hm
  simp only [liftEffect_mat] at hm
  rw [hm]
  simp only [luders, HermitianMat.conj_apply_mat, mat_cfc_sqrt, liftEffect_mat]
  congr 1
  exact Matrix.isHermitian_iff_isSelfAdjoint.mpr (cfc_predicate Real.sqrt a)

/-- **The complex row.**  On the Hermitian `N × N` complex matrices with `N ≥ 3`, every
sequential product satisfying S1--S7 has the twist normal form
`a & b = a ^ (1/2 + i t) · b · a ^ (1/2 - i t)` for a unique real `t`.

★ What the `∃!` does and does not say. Its existence half is applied to a *given* admissible
`P` and produces the parameter for that `P`; its uniqueness half says no second parameter
works for that same `P`. It does **not** say that every real `t` yields an admissible product,
and this statement would still hold if no `SeqProd` existed at all. The equation is asserted on
*all* effects, including singular ones.

(van de Wetering, arXiv:1803.11139, Definition 2 for the axioms; the classification
statement is Theorem `mthm:master`, complex row, of the accompanying manuscript.) -/
theorem complex_classification {N : ℕ} (hN : 3 ≤ N)
    (P : SeqProd N ℂ) (hS2 : S2 P) :
    ∃! t : ℝ, ∀ a b : Mat N ℂ, IsEffect a → IsEffect b →
      P.sp a b = twist t a b := by
  obtain ⟨t, ht, huniq⟩ :=
    Necessity.complex_classification_unconditional_ouNorm hN (toHM P) (toHM_S2 P hS2)
  refine ⟨t, ?_, ?_⟩
  · intro a b ha hb
    have h := ht (liftEffect ha) (liftEffect hb) (isEffect_liftEffect ha) (isEffect_liftEffect hb)
    have hm := congrArg HermitianMat.mat h
    rw [show ((toHM P).sp (liftEffect ha) (liftEffect hb))
          = spHM P (liftEffect ha) (liftEffect hb) from rfl,
        spHM_of_effect P (by simpa using ha) (by simpa using hb)] at hm
    simpa [mat_twistSeq] using hm
  · intro t' ht'
    refine huniq t' fun A B hA hB => ?_
    have hA' : IsEffect A.mat := (isEffect_iff A).mp hA
    have hB' : IsEffect B.mat := (isEffect_iff B).mp hB
    have := ht' A.mat B.mat hA' hB'
    apply HermitianMat.ext
    rw [show ((toHM P).sp A B) = spHM P A B from rfl, spHM_of_effect P hA' hB']
    simpa [mat_twistSeq] using this

end TwistNormalForm
