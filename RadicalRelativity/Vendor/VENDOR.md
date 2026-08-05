# Vendored code — provenance and edit record

## physlib HermitianMat island

**Upstream:** `leanprover-community/physlib`, commit `ad1d812` (2026-08-04),
Apache 2.0 (per-file headers retained; upstream author Alex Meiburg).
**Why vendored, not required:** physlib pins mathlib/toolchain v4.32.0 (ours:
v4.28.0), and a live dependency on a fast-moving upstream would make this
tree's zero-sorry/axiom claims a continuous audit obligation. Vendoring pins
the exact audited code. Decision record: campaign `LEDGER.md` 1.1 and
`research/PAPER-A-LEAN-ROUTE.md` (blog repo) decision log 2026-08-04.

**Files** (17; upstream paths `QuantumInfo/ForMathlib/…` → here
`RadicalRelativity/Vendor/…`): Matrix, Isometry, Misc, LinearEquiv,
ContinuousLinearMap, IsMaximalSelfAdjoint, Tactic/Commutes,
Tactic/Commutes/Attribute, HermitianMat/{Basic, Order, Inner, Trace, CFC,
NonSingular, Reindex, Jordan, Proj}.

**Edits applied at vendor time (2026-08-04), each mechanical:**
1. Import-path rewrite: `QuantumInfo.ForMathlib` → `RadicalRelativity.Vendor`
   (21 `public import` lines).
2. Deleted every `set_option backward.isDefEq.respectTransparency false in`
   line (23 occurrences): the option was introduced in Lean v4.30.0 and does
   not exist at v4.28.0; its `false` value requests pre-v4.30 behavior, which
   is v4.28.0's behavior, so deletion is intended to be semantics-preserving.
3. Deleted every `set_option linter.overlappingInstances false` line (3
   occurrences): linter option absent at v4.28.0.
4. Any further edits forced by mathlib v4.32→v4.28 API drift are recorded
   below as they are made.

**Audit status:** vendored modules are inside the `RadicalRelativity` census
prefix, so `AxiomAudit.lean` Layer 1 covers every vendored declaration
(closure ⊆ core + the one disclosed axiom; no sorry; no stray axiom), and the
module manifest pins the vendored surface. Upstream was grep-verified
sorry-free and axiom-free in this closure before vendoring.

### Drift-edit log (v4.32 → v4.28 backport, 2026-08-04)

All edits are proof-side only — **zero statement changes** across all 17 files.
Gates verified after the pass: `lake build` green (2976 jobs, no errors; two
style-lint *warnings* whose message text contains the word "error"), audit
Census PASS (44 modules, custom axioms exactly
`[Selection.aczel_continuous_multiplicative]`). The `sorry` tokens in
`Misc.lean` sit inside a `/- -/` block quoting a Zulip-tracked mathlib diamond
(dead text; the kernel-level census confirms no `sorryAx` anywhere).

- **`convert!` → `convert`** at all 19 sites (Matrix ×5, Isometry ×4,
  HermitianMat/Basic ×1, Inner ×3, CFC ×2, Trace ×1, Proj ×3). `convert!` does
  not exist at v4.28; v4.28's plain `convert` uses the unrestricted `Congr!`
  config — the same matching power `convert!` was later introduced to preserve
  — so this is semantics-faithful.
- **Generational renames** (v4.32 camelCase → v4.28 originals):
  `Polynomial.eval_finset_sum` (Matrix ×4, applied at vendor time);
  `AddSubgroup.val_finset_sum` (Basic); `continuous_finset_sum`,
  `integrable_finset_sum`, `intervalIntegral.integral_finset_sum` (CFC);
  `Finset.sum_eq_add_sum_diff_singleton` with the v4.28 hypothesis shape
  (`Finset.mem_univ` supplied directly; Isometry); `PiLp.ofLp_single` →
  `EuclideanSpace.ofLp_single` (Isometry);
  `Matrix.isSymmetric_toEuclideanLin_iff` → `Matrix.isHermitian_iff_isSymmetric`
  with the `.symm` dropped, already-correct direction (Matrix ×1, Isometry ×8,
  Basic ×1); `Submodule.orthogonalProjectionOnto` → `orthogonalProjection`
  (Proj ×9 — cleared six cascading "Invalid field" errors and a whnf timeout).
- **`DFunLike` field name**: `coe_injective` → `coe_injective'` in
  `HermitianMat.instFun` (Basic).
- **Positivity-extension API**: at v4.28 `Mathlib.Meta.Positivity.PositivityExt
  .eval`'s `PartialOrder` argument is non-optional — removed the
  `Option`-match wrapper in all 11 extensions (Order.lean) and fixed the
  `Strictness` argument order at its 2 internal uses.
- **`PosDef.reindex`** (Matrix): `Matrix.PosDef.submatrix` does not exist at
  v4.28 (and `PosDef` is Finsupp-quantified) — added
  `private theorem PosDef.submatrix_of_injective` (mirrors mathlib's
  `PosSemidef.submatrix`, strict positivity via `Finsupp.mapDomain_injective`);
  `PosDef.reindex`'s statement is byte-for-byte unchanged.
- **SharedEigenbasis** (Isometry): one residual `Pi.single` coordinate goal
  after `congr! 3` closed via an explicit `hkey` rewrite
  (`sharedEigenvectorUnitary_mulVec` + `Matrix.mulVec_single_one`) — the one
  non-mechanical repair of the pass.
- **`reindex_reindex`** (Reindex): appended `rfl` (sides defeq at full
  transparency after `simp`, not simp-reducible).
- **Elaboration default**: `set_option relaxedAutoImplicit true` inserted after
  each file's import block (physlib builds with Lean's defaults, under which
  dimension variables like `dA dB` auto-bind; this repo's lakefile is strict).

Known cosmetic wart inherited from upstream: `HermitianMat/Proj.lean` lacks a
closing `end HermitianMat` (style-lint warning only); two docstrings end
without trailing newline (style-lint). Left as-is to minimize diff vs upstream.

Consumer-side trap inherited from upstream (campaign `LEDGER.md` H6): the island
declares `Matrix.*` lemmas inside `namespace HermitianMat` (Inner.lean:405,
NonSingular.lean:18), creating a `HermitianMat.Matrix` namespace that shadows
root `Matrix` for any `open scoped Matrix` issued inside `namespace HermitianMat`
downstream — which silently deactivates the `*ᵥ` notation. Open the scope before
entering the namespace.
