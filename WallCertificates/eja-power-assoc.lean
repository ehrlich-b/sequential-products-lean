/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity

/-!
# WALL CERTIFICATE — power associativity (Albert's theorem) for Jordan algebras

**Date: 2026-08-12. Arc: ARC-9, block 9.8. Row: none — this is (E1) infrastructure, not a
manifest row.**

This file is **not** imported from `RadicalRelativity/`; `lake build` and `AxiomAudit.lean`
never see it, so its `sorry` cannot reach the census. Verify:

```
grep -rn "^import.*WallCertificates" RadicalRelativity/ RadicalRelativity.lean   # expect no hits
grep -n "lean_lib" lakefile.toml                                                 # expect one
```

Compile deliberately:

```
cd /Users/ehrlich/repos/research/twist-normal-form-lean
lake env lean WallCertificates/eja-power-assoc.lean     # expect: exactly one `sorry` warning
```

## The claim this certificate makes

**Exactly one step is missing**, and it is `commuteAt_general` below. Everything downstream
of it — the full power-associativity statement `x^{m+1} ∘ x^{n+1} = x^{m+n+2}` — is already
proved in `RadicalRelativity/EJA/Power.lean` as `jpow_mul_jpow_of_commuteAt`, so this file
derives the target from the gap with **no second `sorry`**. That is the whole point of the
format: if someone discharges the one `sorry`, Albert's theorem lands with no further work.

`CommuteAt x m` is `∀ w, x ∘ (x^{m+1} ∘ w) = x^{m+1} ∘ (x ∘ w)`. It is **proved** for
`m = 0, 1, 2` in `EJA/Power.lean` (`commuteAt_zero`, `commuteAt_one`, `commuteAt_two`); the
gap is `m ≥ 3`.

## What was attempted, 2026-08-12

* The reduction (`jpow_mul_jpow_of_commuteAt`) — **succeeded**, and it turns out not to use
  the Jordan identity at all (`omit [IsCommJordan J]`). All of Albert's difficulty is in
  `CommuteAt`.
* `m = 2` from one instantiation of `two_lin1_apply` at `a := x`, `b := x²` — **succeeded**;
  the first bracket cancels against itself and the second is the statement.
* `m = 3` by the same trick — **not attempted in Lean.** On paper the analogous instantiation
  gives `⁅L_{x²}, L_{x³}⁆ = 2⁅L_x, L_{x⁴}⁆` rather than either bracket separately, so the
  single-instantiation route stops here: from `m = 3` on, two identities have to be combined
  and the coefficients differ per step (the `5⁅M₄,M₁⁆ = 0` step, worked on paper).
* The classical route is a **simultaneous strong induction over pairs** `(i, j)` on both
  `x^i ∘ x^j = x^{i+j}` and `⁅L_{x^i}, L_{x^j}⁆ = 0`, using the cyclic identity
  `four_lin2_raw`. Not attempted. This is Albert's bookkeeping and the honest price is
  "hours, not minutes", with the Lean difficulty being the pair-indexed strong induction
  rather than any single algebraic step.

## Absence claims, with the scope of the grep that supports each (2026-08-12)

1. **Mathlib has no power associativity for Jordan algebras.**
   `grep -rn "IsCommJordan\|IsJordan" .lake/packages/mathlib/Mathlib --include="*.lean" | grep -i pow`
   → **0 hits.** Mathlib's entire Jordan library is `Mathlib/Algebra/Jordan/Basic.lean`,
   237 lines, 12 declarations (`grep -c "^theorem \|^instance \|^class "`).
2. ★ **But the *class* exists and is the right target.**
   `Mathlib/Algebra/Group/PNatPowAssoc.lean` defines
   `class PNatPowAssoc (M) [Mul M] [Pow M ℕ+]` with `ppow_add : x ^ (k + n) = x ^ k * x ^ n`
   — power associativity in exactly the non-unital `ℕ+`-indexed form this development needs.
   `grep -rn "PNatPowAssoc" .lake/packages/mathlib/Mathlib --include="*.lean" -l` → **2 files**
   (its own, plus `Analysis/Complex/UnitDisc/Basic.lean`). So the Mathlib-facing shape of this
   gap is *an instance*, not a new definition, and the upstream contribution would be
   `instance : PNatPowAssoc J` for a real commutative Jordan algebra.
   ★ Scope: this is a claim about what the two files contain, read on 2026-08-12; it is not a
   claim that the `ℕ+`-power instance for `jpow` is free — that translation is unwritten.
3. **Nothing in this tree had powers of a Jordan element before today.**
   `grep -rn "jpow\|powerAssoc\|power_assoc" RadicalRelativity --include="*.lean"` outside
   `EJA/Power.lean` → **0 hits.**

## What this certificate does NOT claim

It does not claim the theorem is hard in any absolute sense — Albert proved it in 1948 and it
is in every textbook. It claims only that **it is not in Lean, here or anywhere**, that the
reduction above is the correct decomposition of the remaining work, and that the residue is
the pair-indexed induction and nothing else.
-/

namespace WallCertificate.EJAPowerAssoc

open RadicalRelativity.EJA

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

/-- **THE GAP.** `L_{x^{m+1}}` commutes with `L_x`, for every `m`.

Proved in-tree for `m = 0, 1, 2`. The general case is Albert's simultaneous induction over
pairs and is the single missing step of power associativity. -/
theorem commuteAt_general (x : J) (m : ℕ) : CommuteAt x m := by
  sorry

/-- **The target, derived from the gap with nothing else missing.** Power associativity:
`x^{m+1} ∘ x^{n+1} = x^{m+n+2}`.

The absence of a second `sorry` here is the certificate's substance — discharge
`commuteAt_general` and Albert's theorem is immediate. -/
theorem power_associative (x : J) (m n : ℕ) :
    jpow x m * jpow x n = jpow x (m + n + 1) :=
  jpow_mul_jpow_of_commuteAt (commuteAt_general x m) n

/-- The three rows that are **not** gaps, restated here so the certificate is honest about
how much of the family is already closed. These use no `sorry`. -/
example (x : J) : CommuteAt x 0 := commuteAt_zero x
example (x : J) : CommuteAt x 1 := commuteAt_one x
example (x : J) : CommuteAt x 2 := commuteAt_two x

/-- And the three closed rows of the power table, likewise `sorry`-free. -/
example (x : J) (n : ℕ) : x * jpow x n = jpow x (n + 1) := rfl
example (x : J) (n : ℕ) : (x * x) * jpow x n = jpow x (n + 2) := sq_mul_jpow x n
example (x : J) (n : ℕ) : jpow x 2 * jpow x n = jpow x (n + 3) := cube_mul_jpow x n

end WallCertificate.EJAPowerAssoc
