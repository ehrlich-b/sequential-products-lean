/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Sequential products on `H_N(ℝ)` and `H_N(ℂ)`: the classification

A **sequential product** on the effects of a matrix algebra is a binary operation
`a & b`, read "first test `a`, then test `b` with the state updated by the first
test", satisfying the seven axioms S1--S7 of van de Wetering
(*Sequential product spaces are Jordan algebras*, arXiv:1803.11139, Definition 2).

This file states two classification results.

* `real_classification`: on the Hermitian real matrices the Lüders product
  `√a · b · √a` is the **only** sequential product.
* `complex_classification`: on the Hermitian complex matrices of size `N ≥ 3`
  the sequential products are **exactly** the twist products
  `a ^ (1/2 + i t) · b · a ^ (1/2 - i t)`, one for each real `t`, and `t` is
  determined by the product.

The complex row is the mathematically substantial one: the twist family is a genuine
one-parameter deformation of the Lüders product, all of whose members satisfy S1--S7,
and the theorem says there are no others.  The real row says the analogous deformation
does not exist over `ℝ`.

## Reading this statement

Everything the two theorems mention is defined in this file from Mathlib primitives:
the Loewner order `≼` from `Matrix.PosSemidef`, the effect interval `[0, 𝟙]`, the
order-unit norm as an infimum over the order, the axioms S1--S7 as the fields of
`SeqProd`, the continuity axiom S2 as an ε--δ predicate, and the two reference products
via Mathlib's continuous functional calculus `cfc` for Hermitian matrices.

Two points a reader should check deliberately:

* **The axioms are hypothesised only on effects.**  `SeqProd.sp` is a total function on
  matrices, but every axiom is guarded by `IsEffect`, and both conclusions are asserted
  only for effects.  Values off the effect interval are unconstrained and carry no
  content.
* **S2 is not a field of `SeqProd`.**  It is the separate predicate `S2`, appearing as
  an explicit hypothesis in both theorems, so that the topological assumption is visible
  in the statement rather than hidden in a structure.
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
normed-space instance. -/
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

/-! ## The two results -/

/-- **The real row.**  On the Hermitian `N × N` real matrices with `N ≥ 1`, every
sequential product satisfying S1--S7 is the Lüders product `a & b = √a · b · √a`.
There is no free parameter: the classification is rigid.

(van de Wetering, arXiv:1803.11139, Definition 2 for the axioms; the classification
statement is Theorem `mthm:master`, real row, of the accompanying manuscript.) -/
theorem real_classification {N : ℕ} (hN : 0 < N)
    (P : SeqProd N ℝ) (hS2 : S2 P)
    {a b : Mat N ℝ} (ha : IsEffect a) (hb : IsEffect b) :
    P.sp a b = luders a b := sorry

/-- **The complex row.**  On the Hermitian `N × N` complex matrices with `N ≥ 3`, the
sequential products satisfying S1--S7 are exactly the one-real-parameter family of twist
products `a & b = a ^ (1/2 + i t) · b · a ^ (1/2 - i t)`, and the parameter `t` is
uniquely determined by the product.

The `∃!` is the full classification: existence says every such product is a twist
product, uniqueness says distinct parameters give distinct products.  The equation is
asserted on *all* effects, including singular ones.

(van de Wetering, arXiv:1803.11139, Definition 2 for the axioms; the classification
statement is Theorem `mthm:master`, complex row, of the accompanying manuscript.) -/
theorem complex_classification {N : ℕ} (hN : 3 ≤ N)
    (P : SeqProd N ℂ) (hS2 : S2 P) :
    ∃! t : ℝ, ∀ a b : Mat N ℂ, IsEffect a → IsEffect b →
      P.sp a b = twist t a b := sorry

end TwistNormalForm
