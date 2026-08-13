/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.EJA.Bridge
import RadicalRelativity.MasterTheorem.Coalescence
import Mathlib.Analysis.SpecialFunctions.Exp

set_option linter.style.longLine false

/-!
# `EJAComparison`: an interface that says its frame is a frame, and produces a `CoalescenceSetup`

**ARC-9 block 9.22, 2026-08-13.**

`MasterTheorem/Coalescence.lean` proves `lem:coalescence` (manifest row 16) over
`CoalescenceSetup` from four hypotheses. One — `Θ_fix`, van de Wetering's Prop 5.5 — stays
cited. **The other three are produced here as theorems.**

`EJAComparison` extends `ComparisonSetup` with the five equations the interface never states:

* `jordan_id` — the Jordan identity for the `jordan` field (`ComparisonSetup` has only
  `jordan_comm`);
* `p_idem`, `p_orth`, `p_sum` — the frame really is a complete system of orthogonal
  idempotents;
* `aOf_eq` — `aOf r = ∑ exp (r i) • p i`.

`toCoalescenceSetup` then builds a `CoalescenceSetup` in which `simDiag_opCommute`,
`aOf_scalarOn` and `block_mem_J2` are **proved**, via `EJA/Bridge.lean` and the Peirce layer.

## Two design points that were forced, not chosen

★ **The block is a `Finset` sum, `q i j = ∑_{k ∈ {i,j}} p k`, not `p i + p j`.** The interface's
fields carry **no `i ≠ j` hypothesis**, and `p i + p i = 2 pᵢ` is *not* idempotent, so the
`p i + p j` spelling makes the `i = j` instance unprovable. The `Finset` sum collapses to `pᵢ`
and `IsOrthIdemFamily.sum_idem` covers both cases at once.

★ **`p_sum` (completeness) is in the structure because `block_mem_J2` at `i = j` needs it.**
`IsBlockElt jordan p i i x` says `pᵢ ∘ x = ½x` and `p_k ∘ x = 0` for `k ≠ i`, which does not by
itself force `x = 0` — so `J2 i i x` fails without more. Completeness supplies it:
`x = e ∘ x = ∑ p_k ∘ x = ½x`, hence `x = 0`. **This was discovered by the `i = j` case refusing
to close**, and it is a fact about the interface worth recording: two of its FK fields are
stated at a generality that Faraut–Korányi only supports for a *complete* frame.

## Scope — what this does NOT do

★ **No manifest row moves, and row 16 is not closed.** What is proved is an *implication*: if
an interface is told its frame is a frame, the three FK fields follow. Closing row 16 needs an
`EJAComparison` **constructed on the intended carrier** `H_N(ℂ)` — the frame equations proved
there for a concrete frame, `Θ` supplied, and the whole thing reconciled with
`Necessity.comparisonSetup`. None of that is attempted.

★ `Θ_fix` and `Θ_jordan` remain `ComparisonSetup` fields and remain cited; nothing here touches
them. Row 16 rests on `Θ_fix` as much as on the FK three.

★ `ComparisonSetup` itself, its constructor, and `AxiomAudit.lean`'s Layer-6 freeze are
**untouched** — this is an extension structure, deliberately, so that the audited surface does
not move.
-/

namespace RadicalRelativity.EJA

open MasterTheorem Finset

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- A `ComparisonSetup` that additionally *says* its Jordan product is a Jordan product and
its frame is a frame. -/
structure EJAComparison (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    extends ComparisonSetup J where
  jordan_id : ∀ a b : J, jordan (jordan a b) (jordan a a) = jordan a (jordan b (jordan a a))
  p_idem : ∀ i, jordan (p i) (p i) = p i
  p_orth : ∀ i j, i ≠ j → jordan (p i) (p j) = 0
  aOf_eq : ∀ r, aOf r = ∑ i, Real.exp (r i) • p i
  p_sum : ∑ i, p i = e

namespace EJAComparison

variable (E : EJAComparison J)

/-- The block idempotent `q i j = ∑_{k ∈ {i,j}} p k`. Using a `Finset` sum rather than
`p i + p j` is what makes the `i = j` case work: it collapses to `p i`, which is idempotent,
whereas `p i + p i` is not. -/
noncomputable def q (i j : Fin E.n) : J := ∑ k ∈ ({i, j} : Finset (Fin E.n)), E.p k

theorem q_idem (i j : Fin E.n) : E.jordan (E.q i j) (E.q i j) = E.q i j := by
  letI : NonUnitalNonAssocCommRing J := ringOfBilinear E.jordan E.jordan_comm
  exact IsOrthIdemFamily.sum_idem ⟨E.p_idem, E.p_orth⟩ {i, j}

theorem q_of_ne {i j : Fin E.n} (hij : i ≠ j) : E.q i j = E.p i + E.p j :=
  Finset.sum_pair hij

theorem q_self (i : Fin E.n) : E.q i i = E.p i := by
  simp [q]

/-- Peirce-2 membership for the block. -/
def J2' (i j : Fin E.n) (x : J) : Prop := E.jordan (E.q i j) x = x

/-- "Scalar on the range of the block". -/
def ScalarOn' (i j : Fin E.n) (a : J) : Prop :=
  ∃ (mu : ℝ) (a₀ : J), a = mu • E.q i j + a₀ ∧ E.jordan (E.q i j) a₀ = 0

theorem simDiag' (i j : Fin E.n) (a b : J)
    (hsc : E.ScalarOn' i j a) (hb : E.J2' i j b) : OpCommute E.jordan a b := by
  obtain ⟨mu, a₀, ha, ha₀⟩ := hsc
  exact opCommute_scalarOn_interface E.jordan E.jordan_comm E.jordan_id
    (E.q_idem i j) ha ha₀ hb

theorem blockMem' (i j : Fin E.n) (x : J) (hx : IsBlockElt E.jordan E.p i j x) :
    E.J2' i j x := by
  obtain ⟨h1, h2, hrest⟩ := hx
  by_cases hij : i = j
  · -- Completeness forces `x = 0`: `x = e ∘ x = ∑ p k ∘ x = ½ x`.
    subst hij
    have hx0 : x = 0 := by
      have hsum : E.jordan E.e x = (1 / 2 : ℝ) • x := by
        rw [← E.p_sum]
        have : E.jordan (∑ k, E.p k) x = ∑ k, E.jordan (E.p k) x := by
          rw [map_sum, LinearMap.sum_apply]
        rw [this, Finset.sum_eq_single i (fun k _ hk => hrest k hk hk) (by simp), h1]
      rw [E.jordan_unit x] at hsum
      have h2x : ((1 : ℝ) - 1 / 2) • x = 0 := by
        rw [sub_smul, one_smul, ← hsum, sub_self]
      rcases smul_eq_zero.mp h2x with hc | hc
      · norm_num at hc
      · exact hc
    show E.jordan (E.q i i) x = x
    rw [hx0, map_zero]
  · show E.jordan (E.q i j) x = x
    rw [E.q_of_ne hij, map_add, LinearMap.add_apply, h1, h2]
    module

theorem aOfScalar' (r : Fin E.n → ℝ) (i j : Fin E.n) (hr : r i = r j) :
    E.ScalarOn' i j (E.aOf r) := by
  letI : NonUnitalNonAssocCommRing J := ringOfBilinear E.jordan E.jordan_comm
  letI : IsScalarTower ℝ J J := ⟨fun t x y => smul_bilinear E.jordan t x y⟩
  have hfam : IsOrthIdemFamily E.p := ⟨E.p_idem, E.p_orth⟩
  by_cases h : i = j
  · subst h
    refine ⟨Real.exp (r i), ∑ k ∈ Finset.univ \ {i}, Real.exp (r k) • E.p k, ?_, ?_⟩
    · rw [E.aOf_eq, E.q_self]
      have hsd := Finset.sum_sdiff (f := fun k => Real.exp (r k) • E.p k)
        (Finset.subset_univ ({i} : Finset (Fin E.n)))
      rw [← hsd, Finset.sum_singleton]
      abel
    · show E.jordan (E.q i i) _ = 0
      rw [E.q_self]
      show E.p i * _ = 0
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hki : i ≠ k := fun hh => (Finset.mem_sdiff.mp hk).2 (by simp [← hh])
      rw [mul_smul_comm', hfam.orth i k hki, smul_zero]
  · refine ⟨Real.exp (r i), ∑ k ∈ Finset.univ \ {i, j}, Real.exp (r k) • E.p k, ?_, ?_⟩
    · rw [E.aOf_eq, E.q_of_ne h]
      exact diagFamily_scalarOn (fun k => Real.exp (r k)) h
        (by show Real.exp (r i) = Real.exp (r j); rw [hr])
    · rw [E.q_of_ne h]
      exact pair_mul_offblock hfam (fun k => Real.exp (r k)) i j

/-- ★★★ **An `EJAComparison` PRODUCES a `CoalescenceSetup` with the three Faraut-Korányi
fields proved rather than carried.** -/
noncomputable def toCoalescenceSetup : CoalescenceSetup J :=
  { E.toComparisonSetup with
    J2 := E.J2'
    ScalarOn := E.ScalarOn'
    simDiag_opCommute := E.simDiag'
    aOf_scalarOn := E.aOfScalar'
    block_mem_J2 := E.blockMem' }

end EJAComparison

end RadicalRelativity.EJA
