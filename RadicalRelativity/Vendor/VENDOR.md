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

> **UPDATE 2026-08-08 (annotation, not a rewrite).** "The one disclosed axiom"
> above was true when written (2026-08-04) and is now stale in the *tightening*
> direction: `Selection.aczel_continuous_multiplicative` was discharged into a
> theorem on 2026-08-05 (`RadicalRelativity/Necessity/OneParameter.lean`), so
> the gate is now closure ⊆ core alone and **custom axioms exactly `[]`**. The
> census is likewise no longer 44 modules (see the drift-log gate line below):
> the tracked surface has grown to 148. Both numbers below are preserved as the
> historical record of the backport pass, not as current gate values.

### Drift-edit log (v4.32 → v4.28 backport, 2026-08-04)

All edits are proof-side only — **zero statement changes** across all 17 files.
Gates verified after the pass (values as of 2026-08-04; superseded — see the
annotation above): `lake build` green (2976 jobs, no errors; two style-lint
*warnings* whose message text contains the word "error"), audit
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

## csd-lean4 Wigner-rigidity island

**Upstream:** `zblore/csd-lean4`, commit `2287f45` (2026-08-05), Apache 2.0
(per-file headers retained; upstream author Zayn Blore).  The files are
self-labeled "1-Mathlib (CSD-free Mathlib upstream candidate)" and live under
`namespace Projectivization`; nothing from the repo's speculative layers is
imported.

**Why vendored:** upstream is written in the new module system and pins
toolchain v4.33.0-rc1 (ours: v4.28.0), so a live dependency is impossible;
vendoring pins the exact audited code.  Due-diligence record: campaign
`LEDGER.md` 3.0 (2026-08-04) — the WignerRigidity closure was built from
source and `#print axioms Projectivization.wigner_rigidity` was verified to be
`[propext, Classical.choice, Quot.sound]` **before** any vendoring decision,
with statement fidelity checked at the definition level (`transProbVec ψ φ =
‖⟪ψ,φ⟫_ℂ‖²/(‖ψ‖²·‖φ‖²)`, genuine Fubini–Study; conclusion the honest
unitary/antiunitary dichotomy; no surjectivity hypothesis; ℂ-linearity of the
witness an OUTPUT).  Their `EffectGleason.lean` is NOT vendored and remains
UNAUDITED.

**Files** (8, the exact import closure of `WignerRigidity`; upstream paths
`CsdLean4/Mathlib/LinearAlgebra/{Projectivization,Matrix}/…` → here
`RadicalRelativity/Vendor/Wigner/…`): Topology, Unitary, UnitaryCompact,
UnitaryHaar, MeasureSpace, FubiniStudy, TransitionProbability,
WignerRigidity (≈ 4.8kL).

**Not in this island:** `RealWigner.lean` (real Wigner/Uhlhorn rigidity) is
first-party, has no upstream, and imports nothing vendored. It sat in this
directory from 2026-08-06 to 2026-08-08 only because it was drafted against the
complex development; it now lives at `RadicalRelativity/Wigner/RealWigner.lean`.
Anyone diffing this tree against a SHA at or before `ba317b8` will see the move.

**Edits applied at vendor time (2026-08-05), each mechanical:**
1. Module-system strip: the `module` header line deleted, `public import X` →
   `import X`, `@[expose] public section` → `section`.
2. Import-path rewrite to `RadicalRelativity.Vendor.Wigner.<Module>`.
3. v4.33 → v4.28 API drift, FOUR identifier/tactic renames total, all in two
   files, every target grep-confirmed in our pinned mathlib before applying:
   `Set.mem_ofPred_eq` → `Set.mem_setOf_eq`;
   `isOpen_setOfPred_linearIndependent` → `isOpen_setOf_linearIndependent`;
   `push Not` → `push_neg` (all three in `Topology.lean`, inside
   `isClosed_collinearity_relation`); `PiLp.ofLp_single` →
   `EuclideanSpace.ofLp_single` (`WignerRigidity.lean`, inside
   `unitaryOfIsometry_apply`).
4. **ZERO statement changes, zero deletions, zero `sorry`/`axiom`/
   `native_decide` added.**

**Post-vendor verification (first-hand, in this tree):** full `lake build`
green; `#print axioms Projectivization.wigner_rigidity` and
`…wigner_rigidity_unitaryGroup` both `[propext, Classical.choice, Quot.sound]`;
`#check` shows the dichotomy statement unchanged from the audited original.

**Audit-surface note:** like the physlib island, these modules are TRACKED —
imported from the package root and listed in the `AxiomAudit.lean` frozen
manifest (84 names as of this entry) — so the census's closure allowlist and
custom-axiom check run over every declaration in them, not just over the two
headline theorems.  Vendoring therefore does not shrink the audited surface.
