/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.UnitaryGeneration

set_option linter.style.longLine false

/-!
# The complex row, UNCONDITIONAL  (`mthm:master` at `H_N(ℂ)`, `N ≥ 3`, hypothesis-free)

`ComplexMaster.complex_classification` proves the complex row conditional on the manuscript's
two frame-graph facts, carried as located hypotheses: a caller-supplied adjacency relation, its
connectivity (`lem:frame-connectivity`), and the cross-coherence overlap of adjacent frames'
`U(1)` characters.  **Both are now theorems of this development.**

* `frameTwistConst` — `frameTwist` is constant: `FrameConstancy.frameTwist_eq_of_adjAxis`
  supplies coherence for one adjacency step, `UnitaryGeneration.adjAxis_connected` supplies the
  walk, and `Globalization.const_of_adjacent` chains them.
* `complex_classification_unconditional` — **THE COMPLEX ROW.**  Every S1–S7 sequential product
  with S2 on `H_N(ℂ)`, `N ≥ 3`, is `a • b = a^{1/2+it} b a^{1/2−it}` for a **unique** real `t`,
  on all effects.

The hypothesis list is now exactly the paper's: an S1–S7 product, S2, and `N ≥ 3`.  Closure is
Lean core alone (`propext`, `Classical.choice`, `Quot.sound`), as it already was for the
conditional form — what changed is not the axiom closure but the *carried hypotheses*.

**The `Adj := True` step is not circular, and the ordering is what makes it so.**  A reader who
sees `complex_classification_of_frameTwistConst` instantiate the adjacency trivially may suspect
connectivity has been assumed away.  It has not: constancy of `frameTwist` is established
*first* and independently, from the genuine `AdjAxis` walk (`frameTwistConst` below, resting on
`adjAxis_connected`, which is proved from a Householder factorization and is *false* for a
trivial relation — `AdjAxis` does not hold of all pairs).  Only afterwards is the capstone reused
with the cheapest possible adjacency, at which point the frame graph plays no role because the
conclusion it would have delivered is already in hand.

**What `a^{1/2+it}` means at singular `a`.**  `twistFactor` is the continuous functional calculus
of `x ↦ √x·cos(t log x)` and `x ↦ √x·sin(t log x)`.  Under Lean's convention `Real.log 0 = 0`
these vanish at `0`, so the factor is `0` on `a`'s kernel — the intended continuous extension of
`a^{1/2+it}`, which is what makes the singular case meaningful at all.

Both flagship rows of `mthm:master` are now hypothesis-free: this one and
`RealRowUnconditional.real_classification`.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {N : ℕ}

/-- **The per-frame twist parameter is constant** — the complex row's whole residue,
discharged.

One adjacency step is `frameTwist_eq_of_adjAxis`: axis-adjacent frames share a one-parameter
family of base points, and comparing the product's value along that family pins the two
parameters to each other exactly.  Any two frames are joined by a walk of three such steps
(`adjAxis_connected`, from the Householder factorization of `F⁻¹G`), and a real assignment
constant across adjacent pairs is constant along a walk. -/
theorem frameTwistConst (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) :
    FrameTwistConst hN P hS2 := by
  intro F G
  exact MasterTheorem.Globalization.const_of_adjacent
    (Adj := AdjAxis) (t := frameTwist hN P hS2)
    (fun _ _ hadj => frameTwist_eq_of_adjAxis hN P hS2 hadj)
    (adjAxis_connected hN F G)

/-- **`mthm:master`, THE COMPLEX ROW — UNCONDITIONAL.**

For every S1–S7 sequential product with S2 on `H_N(ℂ)`, `N ≥ 3`, there is a **unique** real `t`
with

`a • b = a^{1/2+it} · b · a^{1/2−it}`

for **all** effects `a, b`, singular ones included.

Conditional on nothing beyond the paper's own hypotheses.  The frame-graph facts that
`complex_classification` carried — connectivity of the unitary frame graph and cross-coherence
of adjacent frames' characters — are discharged by `frameTwistConst`. -/
theorem complex_classification_unconditional (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) :
    ∃! t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b :=
  complex_classification_of_frameTwistConst hN P hS2 (frameTwistConst hN P hS2)

/-! ## Non-vacuity, certified in-tree

A theorem quantified over a hypothesis class says nothing if the class is empty, and a theorem
producing a parameter says little if the parameter need not be the intended one.  Both are
checked here against a known member of the class.
-/

/-- **The hypothesis class is inhabited.**  M1's twist product with parameter `t` is an S1–S7
product with S2 on `H_N(ℂ)`, so the capstone applies to it: `3 ≤ N`, `SequentialProductOn`, and
`FirstArgContinuous` are simultaneously satisfiable, and the row is not vacuous. -/
theorem twistProductOn_classified (hN : 3 ≤ N) (t : ℝ) :
    ∃! t' : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      (twistProductOn t).sp a b = HermitianMat.twistSeq t' a b :=
  complex_classification_unconditional hN (twistProductOn t)
    (twistProductOn_firstArgContinuous t)

/-- **The recovered parameter is the intended one.**  Run the capstone on the twist product with
parameter `t` and the unique `t'` it returns is `t` itself.  So the classification is sharp: the
twist family is faithfully parameterized, and the `∃!` is not satisfied by some unrelated
value. -/
theorem complex_classification_sharp (hN : 3 ≤ N) (t t' : ℝ) :
    (∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
        (twistProductOn t).sp a b = HermitianMat.twistSeq t' a b)
      ↔ t' = t := by
  constructor
  · intro h
    refine (twist_param_unique (N := N) (by omega) (fun a b ha hb => ?_)).symm
    rw [← twistProductOn_sp t a b]
    exact h a b ha hb
  · intro h a b _ _
    rw [h, twistProductOn_sp]

/-! ## `cor:selectors`, clause (ii): trace-form symmetry selects the Lüders product

The article's `cor:selectors` gives three sufficient conditions for the classified
complex-type product to be the Lüders product (`t = 0`).  Clause (ii) is trace-form
symmetry, `⟪a · b, c⟫ = ⟪b, a · c⟫`, and it is proved here at the article's own
generality — `H_N(ℂ)` with `N ≥ 3`, an S1–S7 product, and S2, exactly the hypotheses
of the classification it consumes.

The mechanism is that the twist product's *own* trace adjoint flips the twist:
`⟪a^{1/2+it} b a^{1/2-it}, c⟫ = ⟪b, a^{1/2-it} c a^{1/2+it}⟫` by cyclicity of the
trace (`inner_twistSeq_left`).  So trace symmetry says the product is represented by
`-t` as well as by `t`, and the `∃!` of `complex_classification_unconditional` closes
it: `-t = t`.  No new analysis is involved; the selector is a corollary of uniqueness.

**Clauses (i) and (iii) are NOT proved here** — see `THEOREM-MAP.md`.  Clause (iii)
(covariance under every unital order automorphism; the article notes the transpose
suffices) needed one missing ingredient, and only one: that transposition commutes with
the real functional calculus, `(cfc f a)ᵀ = cfc f (aᵀ)`.  ★ **That ingredient is now in
this tree** — `Necessity.cfc_transpose` and `Necessity.transposeMap_cfc`, added
2026-08-08 (ARC-6 rung 6.4) by exactly the route below; the sentence that used to stand
here, "Nothing in this tree has it", is retired.  What remains for clause (iii) is the
assembly, not an ingredient.
The route is `StarAlgHomClass.map_cfc` (Mathlib) applied to entrywise complex
conjugation — which is an ℝ-star-algebra hom of `Matrix n n ℂ` because conjugation
does *not* reverse products and `star (conj A) = conj (star A)` — built from
`AlgHom.mapMatrix Complex.conjAe.toAlgHom` plus a `map_star'` field; for Hermitian `a`,
`aᵀ = conj a`.  With that lemma, `transposeMap (twistSeq t a b) = twistSeq (-t)
(transposeMap a) (transposeMap b)` and clause (iii) closes by the same uniqueness step
used below.  Clause (i) additionally needs the coherence-block action on `H_N(ℂ)`. -/

/-- The twist product's **trace adjoint flips the twist**: conjugating the left slot by
`a^{1/2+it}` is adjoint, for the trace form, to conjugating the right slot by
`a^{1/2-it}`.  Pure cyclicity of the trace, with
`twistFactor_conjTranspose : (a^{1/2+it})ᴴ = a^{1/2-it}` supplying the sign flip. -/
theorem inner_twistSeq_left {n : Type*} [Fintype n] [DecidableEq n]
    (t : ℝ) (a b c : HermitianMat n ℂ) :
    inner ℝ (HermitianMat.twistSeq t a b) c
      = inner ℝ b (HermitianMat.twistSeq (-t) a c) := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace,
    HermitianMat.twistSeq_mat, HermitianMat.twistSeq_mat,
    HermitianMat.twistFactor_conjTranspose, HermitianMat.twistFactor_conjTranspose, neg_neg]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **The effects are trace-form separating.**  Two elements with the same trace pairing
against every effect are equal: the effects span (`span_isEffect_eq_top`), so the pairing
agrees everywhere, and the trace form is definite. -/
theorem eq_of_inner_effect_eq {n : Type*} [Fintype n] [DecidableEq n]
    {z w : HermitianMat n ℂ}
    (h : ∀ b : HermitianMat n ℂ, IsEffect b → inner ℝ b z = inner ℝ b w) : z = w := by
  have hall : ∀ x : HermitianMat n ℂ, inner ℝ x z = inner ℝ x w := by
    intro x
    have hx : x ∈ Submodule.span ℝ {b : HermitianMat n ℂ | IsEffect b} := by
      rw [span_isEffect_eq_top]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add y y' _ _ hy hy' => rw [inner_add_left, inner_add_left, hy, hy']
    | smul r y _ hy => rw [real_inner_smul_left, real_inner_smul_left, hy]
  have h0 : inner ℝ (z - w) (z - w) = (0 : ℝ) := by
    rw [inner_sub_right, hall (z - w), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)

/-- **`cor:selectors` clause (ii)** — trace-form symmetry selects the Lüders product.
For an S1–S7 product with S2 on `H_N(ℂ)`, `N ≥ 3`, if `⟪a · b, c⟫ = ⟪b, a · c⟫` on
effects then the product is `twistSeq 0`, i.e. `a · b = √a · b · √a`. -/
theorem selector_traceSymm (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ)) (hS2 : P.FirstArgContinuous)
    (hsym : ∀ a b c : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b → IsEffect c →
      inner ℝ (P.sp a b) c = inner ℝ b (P.sp a c)) :
    ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq 0 a b := by
  obtain ⟨t, ht, huniq⟩ := complex_classification_unconditional hN P hS2
  have hneg : ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq (-t) a b := by
    intro a c ha hc
    rw [ht a c ha hc]
    refine eq_of_inner_effect_eq (fun b hb => ?_)
    rw [← inner_twistSeq_left, ← ht a b ha hb, hsym a b c ha hb hc, ht a c ha hc]
  have ht0 : t = 0 := by have := huniq (-t) hneg; linarith
  intro a b ha hb
  rw [ht a b ha hb, ht0]

/-- The same selector, stated with the Lüders product written out as
`b.conj √a` rather than as `twistSeq 0`. -/
theorem selector_traceSymm_luders (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ)) (hS2 : P.FirstArgContinuous)
    (hsym : ∀ a b c : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b → IsEffect c →
      inner ℝ (P.sp a b) c = inner ℝ b (P.sp a c)) :
    ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = b.conj ((a.cfc Real.sqrt) : Matrix (Fin N) (Fin N) ℂ) := by
  intro a b ha hb
  rw [selector_traceSymm hN P hS2 hsym a b ha hb, HermitianMat.twistSeq_zero]

/-! ## Transposition commutes with the real functional calculus

The one ingredient `cor:selectors` clause (iii) was missing.  Landed 2026-08-08 (ARC-6 rung
6.4) by exactly the route this file's module docstring recorded: entrywise complex
conjugation is an ℝ-star-algebra homomorphism of `Matrix n n ℂ` (conjugation does not reverse
products, and it commutes with `star`), so `StarAlgHomClass.map_cfc` applies to it; and for a
Hermitian matrix `Aᵀ = conj A`, which converts the statement about conjugation into the
statement about transposition. -/

section CfcTranspose

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise complex conjugation of matrices, as an ℝ-star-algebra homomorphism.

Conjugation, unlike transposition, does *not* reverse products, so it is a genuine algebra
homomorphism; and `star (conj A) = conj (star A)`, so it is a star homomorphism.  The
ℝ-algebra structure is what makes it a hom at all: it is only conjugate-linear over ℂ. -/
def conjMatStarAlg : Matrix n n ℂ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { AlgHom.mapMatrix (Complex.conjAe.toAlgHom) with
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        AlgHom.mapMatrix, Matrix.map_apply] }

@[simp]
theorem conjMatStarAlg_apply (A : Matrix n n ℂ) :
    conjMatStarAlg A = A.map (starRingEnd ℂ) := rfl

theorem continuous_conjMatStarAlg :
    Continuous (conjMatStarAlg : Matrix n n ℂ → Matrix n n ℂ) := by
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact Complex.continuous_conj.comp ((continuous_apply j).comp (continuous_apply i))

/-- For a Hermitian matrix, the transpose is the entrywise conjugate. -/
theorem transpose_eq_conj_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.transpose = A.map (starRingEnd ℂ) := by
  ext i j
  have h : star (A j i) = A i j := by
    have h0 := congrFun (congrFun hA i) j
    simpa [Matrix.conjTranspose_apply] using h0
  rw [Matrix.transpose_apply, Matrix.map_apply, ← h]
  simp

/-- **Transposition commutes with the real functional calculus** — the one lemma
`cor:selectors` clause (iii) was missing. -/
theorem cfc_transpose (f : ℝ → ℝ) {A : Matrix n n ℂ} (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    (cfc f A).transpose = cfc f A.transpose := by
  have hherm : A.IsHermitian := hA
  have hcfc : (cfc f A).IsHermitian := by
    have : IsSelfAdjoint (cfc f A) := cfc_predicate f A
    exact this
  rw [transpose_eq_conj_of_isHermitian hcfc, transpose_eq_conj_of_isHermitian hherm]
  have hmap := StarAlgHomClass.map_cfc (conjMatStarAlg (n := n)) f A hf
    continuous_conjMatStarAlg hA (by
      show IsSelfAdjoint (conjMatStarAlg A)
      rw [conjMatStarAlg_apply, ← transpose_eq_conj_of_isHermitian hherm]
      exact (Matrix.isHermitian_transpose_iff A).mpr hherm)
  simpa using hmap

/-- The `HermitianMat` form. -/
theorem transposeMap_cfc (f : ℝ → ℝ) (A : HermitianMat n ℂ)
    (hf : ContinuousOn f (spectrum ℝ A.mat)) :
    transposeMap (A.cfc f) = (transposeMap A).cfc f := by
  rw [HermitianMat.ext_iff]
  rw [transposeMap_mat, HermitianMat.mat_cfc, HermitianMat.mat_cfc, transposeMap_mat]
  exact cfc_transpose f A.H hf

end CfcTranspose

end Necessity
