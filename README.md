# Lean formalization — Twist Normal Form paper

Standalone Lean 4 development accompanying the paper

> **A Classification of Sequential Products on Simple Euclidean Jordan
> Algebras of Rank ≥ 3** (twist normal form).

This project is a self-contained extract of the paper's modules from the
parent *Radical Relativity* Lean development. It has **zero dependency** on
any other program code; the only external dependency is Mathlib.

## Build

```bash
lake exe cache get   # download prebuilt Mathlib oleans (same pin as manifest)
lake build           # builds the paper's modules; must finish with zero `sorry`
```

- Toolchain: `leanprover/lean4:v4.28.0` (see `lean-toolchain`).
- Mathlib: `v4.28.0`, pinned in `lake-manifest.json` (identical revision to the
  parent development).

## Axiom audit

The capstone theorem is `MasterTheorem.master_chain` (in
`RadicalRelativity/MasterTheorem/Master.lean`). Its axiom closure is exactly
Lean's three core axioms:

```
#print axioms MasterTheorem.master_chain
-- 'MasterTheorem.master_chain' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

No custom `axiom` declarations appear in the `master_chain` import tree.

## SymPy cross-check

`verify_n2.py` corroborates the rank-two algebraic identities (labels V1–V10)
of the paper's §6 in exact symbolic arithmetic:

```bash
python3 verify_n2.py   # prints per-identity PASS lines; exits 0 on success
```

Runs under Python 3 with SymPy (tested: Python 3.14, SymPy 1.14); exact
symbolic arithmetic only, no floating point. It corroborates the
self-contained paper proofs of §6 rather than replacing them.

## Module map

`RadicalRelativity.lean` (root) aggregates the paper's modules.

### Support modules (copied verbatim from the parent development)

These carry program-shared definitions that the paper's modules depend on.
They are copied so this project stands alone; they are **not** paper content.

| Module | Role |
| --- | --- |
| `RadicalRelativity/OrderUnitSpace.lean`     | order-unit-space scaffold (leaf) |
| `RadicalRelativity/SequentialProduct.lean`  | exact S1--S7 interface plus a separately named algebraic core |
| `RadicalRelativity/LocalTomography.lean`    | composite / local-tomography structures |
| `RadicalRelativity/SpinFactor.lean`         | spin-factor algebraic-core instance (S2 not yet claimed) |

### Paper modules

**Twist normal form**
- `RadicalRelativity/TwistNormalForm.lean`

**Exact statement boundary (target, not a classification proof)**
- `RadicalRelativity/PaperA/Statement.lean`

**Master theorem chain — capstone `master_chain` (12 modules including Central)**
- `RadicalRelativity/MasterTheorem/Interface.lean`
- `RadicalRelativity/MasterTheorem/Coalescence.lean`
- `RadicalRelativity/MasterTheorem/DiagonalHom.lean`
- `RadicalRelativity/MasterTheorem/Branches/Real.lean`
- `RadicalRelativity/MasterTheorem/Branches/Quaternionic.lean`
- `RadicalRelativity/MasterTheorem/Branches/Albert.lean`
- `RadicalRelativity/MasterTheorem/Branches/Complex.lean`
- `RadicalRelativity/MasterTheorem/Globalization.lean`
- `RadicalRelativity/MasterTheorem/Adapter.lean`
- `RadicalRelativity/MasterTheorem/Master.lean`
- `RadicalRelativity/MasterTheorem/RankTwo.lean`
- `RadicalRelativity/MasterTheorem/Central.lean`

**Selection — earlier block-core development (pair-local ansatz route)**
- `RadicalRelativity/Selection/BaseEquality.lean`
- `RadicalRelativity/Selection/Descent.lean`
- `RadicalRelativity/Selection/Equidistribution.lean`
- `RadicalRelativity/Selection/NormalFormExistence.lean`
- `RadicalRelativity/Selection/SelectorEquivalence.lean`
- `RadicalRelativity/Selection/TwistIsotropy.lean`

The Selection development carries two cited-import `axiom` declarations
(`RadicalRelativity.aczel_continuous_multiplicative` in `NormalFormExistence`
and `bgw_canonical_composite` in `TwistNormalForm`); these are outside the
`master_chain` import tree and do not affect its axiom closure above.
