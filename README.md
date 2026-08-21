# Sequential products on Euclidean Jordan algebras — Lean 4

A **sequential product** on the effects of an order-unit space is a binary operation `a & b`,
read "first test `a`, then test `b` with the state updated by the first test", satisfying the
seven axioms S1–S7 of van de Wetering ([arXiv:1803.11139](https://arxiv.org/abs/1803.11139),
Definition 2). This repository proves how rigid those axioms are on the Hermitian matrix
algebras.

On `H_N(ℝ)`, every sequential product agrees with the Lüders formula `√a · b · √a` on effects:
there is no free parameter. On `H_N(ℂ)` with `N ≥ 3`, every sequential product has the twist
normal form `a^(1/2+it) · b · a^(1/2−it)`, and the parameter `t` is uniquely determined by it.
The complex case is the substantive one: the twist family is a one-parameter deformation of the
Lüders product, and the theorem says nothing outside it satisfies the axioms.

The development also proves two classical theorems along the way, both stated over Mathlib alone:
**Albert's power-associativity theorem** for commutative Jordan rings, and the
**finite-dimensional real, non-bijective Wigner theorem**.

## Registered results

Three [Palomar](https://palomar-registry.org) submissions are prepared here, as three Comparator
configurations. Each `*Challenge.lean` states its theorems against Mathlib alone and is the file a
reader is meant to audit; each `*Solution.lean` proves them.

| Configuration | Statement | Proof | Registers |
| --- | --- | --- | --- |
| [`comparator.json`](comparator.json) | [`Challenge.lean`](Challenge.lean) | [`Solution.lean`](Solution.lean) | `TwistNormalForm.real_classification`, `TwistNormalForm.complex_classification` |
| [`comparator-albert.json`](comparator-albert.json) | [`AlbertChallenge.lean`](AlbertChallenge.lean) | [`AlbertSolution.lean`](AlbertSolution.lean) | `AlbertPowerAssoc.jpow_mul_jpow` |
| [`comparator-wigner.json`](comparator-wigner.json) | [`WignerChallenge.lean`](WignerChallenge.lean) | [`WignerSolution.lean`](WignerSolution.lean) | `WignerReal.exists_isometry_of_transProbPreserving` |

The library declares no axioms of its own and contains no `sorry`. All four registered theorems
close over `propext`, `Classical.choice` and `Quot.sound`. `AxiomAudit.lean` enforces both on
elaboration, over every declaration in the tree.

## Scope

Both classification theorems are statements of **necessity**: a product satisfying the axioms is
supplied, and the theorem gives its normal form. Neither constructs such a product, and neither
converse is registered here.

The manuscript states its results on a finite-dimensional simple Euclidean Jordan algebra. This
development proves them on the real and complex Hermitian matrices; the quaternionic and
exceptional cases are not proved. [`STATEMENT-MANIFEST.md`](STATEMENT-MANIFEST.md) records, result
by result, which of the manuscript's thirty-six numbered statements are formalized here and which
are not.

## Build

```bash
lake exe cache get   # prebuilt Mathlib oleans at the pinned revision
lake build
```

Toolchain `leanprover/lean4:v4.28.0`; Mathlib `v4.28.0`, pinned in `lake-manifest.json`.

The two classification theorems, at the carrier level:

```lean
import RadicalRelativity

#check @Necessity.real_classification
#check @Necessity.complex_classification_unconditional
```

## Provenance

Part of the tree is third-party code, vendored verbatim with per-file copyright headers retained.
Reproduce the line counts with
`find RadicalRelativity RadicalRelativity.lean -name '*.lean' -exec cat {} + | wc -l`, and the
same over `RadicalRelativity/Vendor`.

| Vendored | Upstream | Author(s) | Role |
| --- | --- | --- | --- |
| `Vendor/*.lean`, `Vendor/HermitianMat/`, `Vendor/Tactic/` | [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib) @ `ad1d812` | Alex Meiburg; `HermitianMat/Proj.lean` also Leonardo A Lessa | Hermitian matrices with the Loewner order, trace inner product, continuous functional calculus, Jordan product |
| `Vendor/Wigner/` | [`zblore/csd-lean4`](https://github.com/zblore/csd-lean4) @ `2287f45` | Zayn Blore | complex Wigner rigidity on `ℂP^{N-1}` |

Everything outside `RadicalRelativity/Vendor/` is first-party, including
`RadicalRelativity/Wigner/RealWigner.lean`, the real Wigner theorem. Both vendored islands sit
inside the audit prefix, so `AxiomAudit.lean` checks every vendored declaration on the same terms
as first-party code; the backport edit log is in `RadicalRelativity/Vendor/VENDOR.md`.

The development was produced with Anthropic's Claude models in an agentic coding harness under
the author's direction; see `automation` in [`formalization.yaml`](formalization.yaml).

## Further documentation

- [`STATEMENT-MANIFEST.md`](STATEMENT-MANIFEST.md) — which manuscript results are formalized.
- [`THEOREM-MAP.md`](THEOREM-MAP.md) — result-to-declaration map.
- `WallCertificates/` — for results that are **not** formalized, the missing step stated in Lean
  with a `sorry` marking the gap, rather than estimated in prose. Never imported by the library.
- [`LEDGER.md`](LEDGER.md) — the development record, including retractions.
- `upstream/` — a Mathlib pull request prepared from `RealWigner.lean`; not part of this library.
