/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity

/-!
# WALL CERTIFICATE — (E1), the Jordan spectral theorem

**Date: 2026-08-12. Arc: ARC-9, block 9.12. Rows: none directly; (E1) is what
`EJA-DIVIDEND.md` says CLOSES manifest row 13 and is one of the two ingredients of rows
16/17.**

Not imported from `RadicalRelativity/`. Verify and compile:

```
grep -rn "^import.*WallCertificates" RadicalRelativity/ RadicalRelativity.lean   # expect no hits
cd /Users/ehrlich/repos/research/twist-normal-form-lean
lake env lean WallCertificates/eja-spectral.lean     # expect: exactly one `sorry` warning
```

## The target

Every element of a finite-dimensional formally real Jordan algebra is a real combination of
pairwise-orthogonal idempotents. `spectral_resolution` below states it in this development's
own vocabulary — `IsOrthIdemFamily` from `EJA/Frame.lean` — with one `sorry`.

★ **Completeness (`∑ cᵢ = e`) is deliberately NOT part of the statement.** This development is
unit-free by construction (`EJA/Peirce.lean` onwards), and the idempotents in the spectral
resolution of `x` sum to the *support* of `x`, not to an algebra unit. Adding `∑ cᵢ = 1` would
require `[One J]` and `x` invertible, and would state a different theorem. The ARC-9 orders'
terminal condition says "summing to the unit"; **this certificate does not meet that wording
and does not claim to** — see the note at the end.

## What is built, and what the four steps are

| step | statement | status |
| --- | --- | --- |
| 1 | `ℝ[x]` is finite-dimensional; the powers satisfy a nontrivial relation | **DONE** — `jspan_finite`, `exists_jpow_relation` (`EJA/Subalgebra.lean`). ★ Neither uses the Jordan identity; step 1 is free |
| 2 | `ℝ[x]` is an associative commutative algebra | **DONE** — `mul_mem_jspan`, `jspan_assoc` (`EJA/Subalgebra.lean`), from Albert's theorem |
| 3 | `ℝ[x]` is *reduced* | **PARTIAL** — `eq_zero_of_jpow_eq_zero` (`EJA/FormallyReal.lean`) gives no-nilpotents for elements of the *ambient* algebra. Repackaging that as `IsReduced` for a ring structure on `jspan x` is not built |
| 4 | a finite-dimensional reduced commutative `ℝ`-algebra is `ℝ^k`, and the idempotents are its coordinate projections | **ABSENT** |

## The obstruction that is worth recording, because it is structural and not effort

Step 4 wants ring theory, and ring theory wants a **unital ring**. `jspan x` is a
`Submodule ℝ J`, and it carries no unit: it is spanned by `x, x², x³, …` with no constant
term, and this development assumes no `1` in `J` at all.

The classical treatment sidesteps this by working in the *unital* `ℝ[x] = span{1, x, x², …}`.
That is available only after adding `[One J]` and the unit axiom to the setting — a design
change to every file from `EJA/Peirce.lean` onward, all of which are currently unit-free and
gain generality from being so.

★ **It is not obvious that the unit is actually needed**, and this is the honest open question
rather than a task: `jspan x` *is* unital as a ring in its own right, its unit being the
support idempotent of `x` — but that fact is a consequence of the spectral theorem, not an
input to it, so using it here would be circular. Either (a) find a route to step 4 that does
not need a unit, or (b) add `[One J]` and pay the generality. **Not decided.** Deciding it is
the first action on (E1), and it is a design question, not a proof.

## Absence claims, with grep scope (2026-08-12)

1. **Nothing in this tree does step 3 or 4.**
   `grep -rn "IsReduced\|isReduced" RadicalRelativity --include="*.lean"` → **0 hits** (run).
   `grep -n "^def \|^theorem \|^instance \|^abbrev \|^structure \|^noncomputable def " RadicalRelativity/EJA/*.lean | grep -i spectral`
   → **0 hits** (run) — no *declaration* mentions the spectral theorem.
   ★★ **The first draft of this line claimed `grep -rn "spectral" RadicalRelativity/EJA` → 0 hits,
   and that was FALSE: it returns 14.** All fourteen are prose in the EJA layer's own docstrings
   — this arc wrote every one of them, hours earlier — but the number was asserted without being
   run. That is the "verify the verifier saw data" rule broken inside a certificate whose entire
   purpose is to make absence claims falsifiable, and it is the second self-inflicted defect of
   this kind tonight (after the vacuous theorem in `EJA/Witness.lean`). The correction is also the
   arc's standing first move: **grep the declaration list, not the file text** — a topic word
   appears in prose, a declaration does not.
2. **Mathlib's Artinian/reduced machinery exists but is not obviously applicable.**
   `Mathlib/RingTheory/Artinian/Ring.lean` carries the structure theory for commutative
   Artinian rings. ★ Scope: the file was *listed*, not read. Whether it gives
   "finite-dimensional reduced commutative `ℝ`-algebra ⟹ `ℝ^k`" in a usable form, and at what
   unitality cost, is **unassessed** — that assessment is itself part of the first action
   above, and pricing step 4 before doing it would be exactly the mistake
   `eja-power-assoc.lean` made three hours earlier in this arc.

## Scope of the whole certificate

This prices (E1) at "two of four steps done, one structural decision open, step 4 unassessed".
It does **not** price it in hours. ★ That is deliberate: this arc has already produced one
route-price that was wrong by an order of magnitude, in this directory, today. The rule earned
there — *prices about route fail, prices about vocabulary hold* — says to record what is
missing and what is built, and to stop.
-/

namespace WallCertificate.EJASpectral

open RadicalRelativity.EJA

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [Module.Finite ℝ J] [IsFormallyReal J]

/-- **THE GAP: (E1), the single-element spectral theorem.**

Every element of a finite-dimensional formally real Jordan algebra is a real combination of
pairwise-orthogonal idempotents drawn from the subalgebra it generates.

The `IsOrthIdemFamily` and `jspan` vocabulary is this development's own, so the statement is
written at the generality the rest of the EJA layer runs at rather than at a located one. -/
theorem spectral_resolution (x : J) :
    ∃ (n : ℕ) (c : Fin n → J) (lam : Fin n → ℝ),
      IsOrthIdemFamily c ∧ (∀ i, c i ∈ jspan x) ∧ x = ∑ i, lam i • c i := by
  sorry

/-- The steps that are **not** gaps, restated so the certificate is honest about how much of
the route is already in the tree. These use no `sorry`. -/
example (x : J) : Module.Finite ℝ (jspan x) := jspan_finite x

example (x : J) : ∃ (n : ℕ) (c : Fin n → ℝ), (∃ i, c i ≠ 0) ∧ ∑ i, c i • jpow x i = 0 :=
  exists_jpow_relation x

example {x a b : J} (ha : a ∈ jspan x) (hb : b ∈ jspan x) : a * b ∈ jspan x :=
  mul_mem_jspan ha hb

example {x a b c : J} (ha : a ∈ jspan x) (hb : b ∈ jspan x) (hc : c ∈ jspan x) :
    (a * b) * c = a * (b * c) :=
  jspan_assoc ha hb hc

example {x : J} {n : ℕ} (h : jpow x n = 0) : x = 0 := eq_zero_of_jpow_eq_zero n h

end WallCertificate.EJASpectral
