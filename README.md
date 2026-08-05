# Lean formalization — Twist Normal Form paper

Standalone Lean 4 development accompanying the paper

> **Sequential Products on Euclidean Jordan Algebras: Classification in Rank
> at Least Three and the Complex Qubit**.

This project is a self-contained extract of the paper's modules from the
parent *Radical Relativity* Lean development. It has **zero dependency** on
any other program code; the only external dependency is Mathlib.

## Theorem-to-file map

`THEOREM-MAP.md` records which paper statements are machine-checked, which are
carried as cited interface hypotheses, and which are not formalized at all.
Its §2 has to be read before any row of §1 is read as a verification claim.

The anonymized archive accompanying the journal submission is this same tree
with two directories renamed — `RadicalRelativity/` to
`SequentialProductsArtifact/` and `PaperA/` to `PaperStatements/` — so that no
path carries a program or paper identifier. Declaration names are identical in
both, so the map's declaration column transfers unchanged.

## Build

```bash
lake exe cache get   # download prebuilt Mathlib oleans (same pin as manifest)
lake build           # builds the paper's modules (no-sorry / axiom-closure gate: AxiomAudit.lean, not this command)
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

The development carries NO custom `axiom` declarations: every tracked
declaration's axiom closure is exactly Lean's three core axioms.
(`Selection.aczel_continuous_multiplicative` was DISCHARGED into a theorem
2026-08-05 — the from-scratch one-parameter-semigroup classification in
`RadicalRelativity/Necessity/OneParameter.lean` proves it; the historical name
and signature are preserved in
`RadicalRelativity/Selection/NormalFormExistence.lean`.)
(A second axiom, `TwistNormalForm.bgw_canonical_composite`, was eliminated
2026-08-04: it asserted only the existence of an operation with nine
specified table values — constructible, hence not falsifiable — and is now
the definition `bgwComposite` with the nine rows proved by `rfl`; the
Barnum–Graydon–Wilce citation attaches to the table's interpretation, in
prose, as before.)
