/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Coalescence — the D3 lemma chain (`lem:coalescence`, `lem:frame-fix` second half)

The producer lane, part 1. This module proves the paper's coalescence lemma
(`lem:coalescence`) and the block-preservation half of `lem:frame-fix` from the
`ComparisonSetup` interface, using the Faraut–Korányi simultaneous-diagonalization fact
as **structure fields** of a `CoalescenceSetup` (not free axioms — see the design decision
in `PLAN.md` §5/§7: keeping the audit surface a structure rather than free axioms).

## What is proved here (Lean theorems)

* `block_preserved` (`lem:frame-fix`, second half): `Θ_{a(r)}` preserves each Peirce block
  `V_{ij}`. Proved from `ComparisonSetup.jordanAuto` (`prop:theta`) + `frame_fixed` +
  linearity of `Θ`. **No FK field needed.**
* `coalescence_J2q` (`lem:coalescence`, general form): if `a` is scalar on `range(q)` for
  `q = p_i + p_j` (predicate `ScalarOn`) and `b ∈ J₂(q)` (predicate `J2`), then
  `Θ_a(b) = b`. Proved from the FK field `simDiag_opCommute` + `Θ_fix` (`vdW` Prop 5.5).
  **This pointwise strength on all of `J₂(q)` is what the complex globalization consumes.**
* `coalescence_block` (`lem:coalescence`, first statement): `r_i = r_j ⟹ Θ_{a(r)}` fixes
  `V_{ij}` pointwise. The `r_i = r_j` specialization of `coalescence_J2q`.

## The imported Faraut–Korányi facts (carried as `CoalescenceSetup` fields, not axioms)

A reviewer enumerates these by reading `CoalescenceSetup`. Each is a Faraut–Korányi
Peirce/spectral fact (`Analysis on Symmetric Cones`, Ch. IV), specialized to the setup:

* `simDiag_opCommute` — FK simultaneous diagonalization: an element scalar on `range(q)`
  and an element of `J₂(q)` are simultaneously diagonalizable, hence operator-commute.
  This is the one genuinely-new content item D3 of `C6-TRANSPLANT-TEST`; here it enters as
  a cited FK field and coalescence is derived from it.
* `aOf_scalarOn` — when the two eigenvalues coincide (`r_i = r_j`), the diagonal effect
  `a(r) = Σ e^{r_k} p_k` is scalar (`= e^{r_i}`) on `range(p_i + p_j)`.
* `block_mem_J2` — each Peirce block `V_{ij}` is contained in `J₂(p_i + p_j)`.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*,
  `lem:coalescence`, `lem:frame-fix`.
* `research/qm-genericity-review/C6-TRANSPLANT-TEST-2026-07-13.md`, T2/T3 (= D3).
* Faraut–Korányi, *Analysis on Symmetric Cones*, 1994, Ch. IV (Peirce theory).
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-! ## Peirce-block membership

The paper's `V_{ij}` block is `{x : p_i ∘ x = ½x, p_j ∘ x = ½x, p_k ∘ x = 0 (k ≠ i,j)}`
(Faraut–Korányi Peirce decomposition). We encode membership through the primitive Jordan
data of the setup (`jordan`, `p`) so that `block_preserved` is a genuine Lean derivation
from the Jordan-automorphism property, not an opaque predicate. -/

/-- Membership in the Peirce block `V_{ij}`, expressed through the Peirce eigenrelations
    for the Jordan product `jordan` and the frame `p`. -/
def IsBlockElt {n : ℕ} (jordan : J →ₗ[ℝ] J →ₗ[ℝ] J) (p : Fin n → J) (i j : Fin n) (x : J) :
    Prop :=
  jordan (p i) x = (1 / 2 : ℝ) • x ∧ jordan (p j) x = (1 / 2 : ℝ) • x ∧
    ∀ k, k ≠ i → k ≠ j → jordan (p k) x = 0

/-- Peirce-block membership for a `ComparisonSetup`. -/
def ComparisonSetup.isBlock (C : ComparisonSetup J) (i j : Fin C.n) (x : J) : Prop :=
  IsBlockElt C.jordan C.p i j x

/-! ## `lem:frame-fix` second half: `Θ_{a(r)}` preserves each Peirce block

Proved directly from the interface: `Θ_{a(r)}` is a Jordan automorphism
(`ComparisonSetup.jordanAuto`, i.e. `prop:theta`) fixing every frame idempotent
(`ComparisonSetup.frame_fixed`), so it maps each Peirce eigenrelation to itself. -/

/-- **`lem:frame-fix` (second half, PROVED).** `Θ_{a(r)}` preserves each Peirce block
`V_{ij}`: it sends block elements to block elements. For `x ∈ V_{ij}`,
`p_i ∘ Θ_r(x) = Θ_r(p_i ∘ x) = ½ Θ_r(x)` (and likewise `p_j`), and `p_k ∘ Θ_r(x) = 0`
for `k ≠ i,j`, using `jordanAuto` + `frame_fixed` + linearity of `Θ`. -/
theorem block_preserved (C : ComparisonSetup J) (r : Fin C.n → ℝ) {i j : Fin C.n}
    {x : J} (hx : C.isBlock i j x) : C.isBlock i j (C.Θ (C.aOf r) x) := by
  obtain ⟨hi, hj, hk⟩ := hx
  have hAuto := C.jordanAuto (C.aOf_inv r)
  refine ⟨?_, ?_, ?_⟩
  · have h := hAuto (C.p i) x
    rw [C.frame_fixed r i, hi, map_smul] at h
    exact h.symm
  · have h := hAuto (C.p j) x
    rw [C.frame_fixed r j, hj, map_smul] at h
    exact h.symm
  · intro k hki hkj
    have h := hAuto (C.p k) x
    rw [C.frame_fixed r k, hk k hki hkj, map_zero] at h
    exact h.symm

/-! ## The coalescence setup

`CoalescenceSetup` extends `ComparisonSetup` with the Faraut–Korányi Peirce apparatus
needed for `lem:coalescence`: the predicates `J2` (membership in `J₂(p_i+p_j)`) and
`ScalarOn` (an element is scalar on `range(p_i+p_j)`), and the three cited FK facts. -/

/-- **The coalescence interface.** A `ComparisonSetup` together with the Faraut–Korányi
Peirce/spectral apparatus of `lem:coalescence`, carried as fields (the audit surface for
these FK imports). -/
structure CoalescenceSetup (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    extends ComparisonSetup J where
  /-- Membership predicate for the Peirce-2 subspace `J₂(p_i + p_j)`. -/
  J2 : Fin n → Fin n → J → Prop
  /-- `a` is scalar on `range(p_i + p_j)`: `a = λ(p_i+p_j) + a₀` with `a₀ ∈ J₀(p_i+p_j)`. -/
  ScalarOn : Fin n → Fin n → J → Prop
  /-- **FK simultaneous diagonalization.** An element scalar on `range(q)` (`q = p_i+p_j`)
      and an element of `J₂(q)` are simultaneously diagonalizable in a common Jordan frame,
      hence operator-commute. This is D3 of `C6-TRANSPLANT-TEST`, entering as a cited FK
      field. (Faraut–Korányi, *Analysis on Symmetric Cones*, Ch. IV.) -/
  simDiag_opCommute : ∀ (i j : Fin n) (a b : J),
      ScalarOn i j a → J2 i j b → OpCommute jordan a b
  /-- FK/spectral: when the two eigenvalues coincide (`r_i = r_j`), the diagonal effect
      `a(r)` is scalar (`= e^{r_i}`) on `range(p_i + p_j)`. -/
  aOf_scalarOn : ∀ (r : Fin n → ℝ) (i j : Fin n), r i = r j → ScalarOn i j (aOf r)
  /-- FK Peirce: each block `V_{ij}` sits inside `J₂(p_i + p_j)`. -/
  block_mem_J2 : ∀ (i j : Fin n) (x : J), IsBlockElt jordan p i j x → J2 i j x

namespace CoalescenceSetup

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- **`lem:coalescence` (general form, PROVED).** If `a` is invertible and scalar on
`range(q)` for `q = p_i + p_j`, then `Θ_a` fixes every element of `J₂(q)` pointwise.
Proof: the FK simultaneous-diagonalization field gives operator commutation of `a` with
`b ∈ J₂(q)`, and `Θ_fix` (`vdW` Prop 5.5 + the compatibility bridge) then fixes `b`.
The pointwise strength on all of `J₂(q)` is what the complex globalization consumes. -/
theorem coalescence_J2q (C : CoalescenceSetup J) {a b : J} {i j : Fin C.n}
    (ha : C.Inv a) (hsc : C.ScalarOn i j a) (hb : C.J2 i j b) : C.Θ a b = b :=
  C.Θ_fix a ha b (C.simDiag_opCommute i j a b hsc hb)

/-- **`lem:coalescence` (first statement, PROVED).** If `r_i = r_j`, then `Θ_{a(r)}` fixes
`V_{ij}` pointwise. The `r_i = r_j` specialization of `coalescence_J2q`: `a(r)` is then
scalar on `range(p_i+p_j)` (`aOf_scalarOn`), it is invertible (`aOf_inv`), and
`V_{ij} ⊆ J₂(p_i+p_j)` (`block_mem_J2`). -/
theorem coalescence_block (C : CoalescenceSetup J) {r : Fin C.n → ℝ} {i j : Fin C.n}
    (h : r i = r j) {x : J} (hx : IsBlockElt C.jordan C.p i j x) :
    C.Θ (C.aOf r) x = x :=
  C.coalescence_J2q (C.aOf_inv r) (C.aOf_scalarOn r i j h) (C.block_mem_J2 i j x hx)

end CoalescenceSetup

end MasterTheorem
