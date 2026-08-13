/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.EJA.PeirceMul

set_option linter.style.longLine false

/-!
# Orthogonal idempotents, and the simultaneous-diagonalisation field

**ARC-9 block 9.6, 2026-08-12.**

This file derives, at the generality of an arbitrary idempotent, the Faraut–Korányi fact that
`MasterTheorem/Coalescence.lean` carries as the cited field
`CoalescenceSetup.simDiag_opCommute` — the load-bearing hypothesis under `lem:coalescence`
(manifest row 16):

> an element **scalar on `range q`** and an element of **`J₂(q)`** operator-commute.

Here `q` is any idempotent `c`, "scalar on `range c`" is `a = μ • c + a₀` with `a₀ ∈ J₀(c)`,
and `J₂(c)` is `J₁(c)` in the eigenvalue naming of `EJA/Peirce.lean`. The proof is four
lines, because `EJA/PeirceMul.lean` already did the work: `L_c` commutes with `L_b` for
`b ∈ J₁(c)`, and `L_{a₀}` commutes with `L_b` for `a₀ ∈ J₀(c)`, so `L_a = μ L_c + L_{a₀}`
commutes with `L_b` by linearity.

The interface's `q` is a *rank-two* idempotent `pᵢ + pⱼ` built from a Jordan frame, so
`add_idem_of_orthogonal` below supplies the shape: a sum of two orthogonal idempotents is an
idempotent, and then the general result applies.

## What this does and does not close

★ It does **not** close row 16. `CoalescenceSetup` also carries `aOf_scalarOn` and
`block_mem_J2`, and — more basically — `ComparisonSetup` carries the frame `p : Fin n → J`
with **no axioms at all**: nothing says the `p i` are idempotent, orthogonal, or sum to the
unit, and nothing says `aOf r = Σ exp (r i) • p i`. Those equations have to be *added* to the
structure before anything can be *derived* from them. That refactor is the pricing recorded
in `LEDGER.md` (ARC-9 block 9.2), and it is not attempted here.

What this file does is remove the mathematical uncertainty from that price: the FK content
is derivable from the Jordan identity, so the remaining work on rows 16/17 is interface
surgery, not Jordan theory.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Ch. IV.
-/

namespace RadicalRelativity.EJA

section Orthogonal

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

omit [IsCommJordan J] [Module ℝ J] in
/-- **A sum of two orthogonal idempotents is an idempotent.** Pure expansion — this needs
only commutativity and distributivity, not the Jordan identity. -/
theorem add_idem_of_orthogonal {p q : J} (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) :
    (p + q) * (p + q) = p + q := by
  have hqp : q * p = 0 := by rw [mul_comm]; exact hpq
  rw [add_mul, mul_add, mul_add, hp, hq, hpq, hqp]
  abel

/-- **Orthogonal idempotents operator-commute.** Not merely `p ∘ q = 0`: the multiplication
operators themselves commute, which is what every simultaneous-diagonalisation argument
needs. Immediate from `opCommute_eigen_one_zero`, since `p ∈ J₁(p)` and `q ∈ J₀(p)`. -/
theorem opCommute_of_orthogonal {p q : J} (hp : p * p = p) (hpq : p * q = 0) (w : J) :
    p * (q * w) = q * (p * w) :=
  opCommute_eigen_one_zero hp hp hpq w

section ScalarTower

variable [IsScalarTower ℝ J J]

/-- **`CoalescenceSetup.simDiag_opCommute`, derived at single-idempotent generality.**

If `a` is scalar on `range c` — that is, `a = μ • c + a₀` with `a₀` in the `0`-Peirce
component — and `b` lies in the `1`-Peirce component `J₂(c)`, then `L_a` and `L_b` commute.

This is the cited Faraut–Korányi hypothesis that `lem:coalescence` (manifest row 16) rests
on, and it is a consequence of the Jordan identity alone. -/
theorem opCommute_scalarOn {c a a₀ b : J} {μ : ℝ} (hc : c * c = c)
    (ha : a = μ • c + a₀) (ha₀ : c * a₀ = 0) (hb : c * b = b) (w : J) :
    a * (b * w) = b * (a * w) := by
  have hcb : c * (b * w) = b * (c * w) := mul_comm_of_eigen_one hc hb w
  have h0 : a₀ * (b * w) = b * (a₀ * w) := (opCommute_eigen_one_zero hc hb ha₀ w).symm
  subst ha
  rw [add_mul, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, hcb, h0, mul_smul_comm']

/-- The interface's actual shape: `c` is the rank-two idempotent `p + q` built from two
orthogonal idempotents of a Jordan frame. -/
theorem opCommute_scalarOn_pair {p q a a₀ b : J} {μ : ℝ} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = 0) (ha : a = μ • (p + q) + a₀) (ha₀ : (p + q) * a₀ = 0)
    (hb : (p + q) * b = b) (w : J) : a * (b * w) = b * (a * w) :=
  opCommute_scalarOn (add_idem_of_orthogonal hp hq hpq) ha ha₀ hb w

end ScalarTower

end Orthogonal

end RadicalRelativity.EJA
