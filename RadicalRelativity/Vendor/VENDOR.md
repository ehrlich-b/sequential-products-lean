# Vendored code — provenance and edit record

## physlib HermitianMat island

**Upstream:** `leanprover-community/physlib`, commit `a50684a191` (its
"chore: Bump 4.33" commit), targeting Lean/Mathlib **v4.33.0**. Apache 2.0
(per-file headers retained; upstream author Alex Meiburg, and
`HermitianMat/Proj.lean` additionally Leonardo A Lessa).
**Why vendored, not required:** a live dependency on a fast-moving upstream
would make this tree's zero-sorry/axiom claims a continuous audit obligation.
Vendoring pins the exact audited code. Decision record: campaign
`docs/history/LEDGER.md` 1.1 and `research/PAPER-A-LEAN-ROUTE.md` (blog repo)
decision log 2026-08-04.

**Files** (17; upstream paths `QuantumInfo/ForMathlib/…` → here
`RadicalRelativity/Vendor/…`): Matrix, Isometry, Misc, LinearEquiv,
ContinuousLinearMap, IsMaximalSelfAdjoint, Tactic/Commutes,
Tactic/Commutes/Attribute, HermitianMat/{Basic, Order, Inner, Trace, CFC,
NonSingular, Reindex, Jordan, Proj}.

### Re-vendor 2026-08-21 (v4.33.0) — CURRENT

The island is now **verbatim upstream `a50684a191`** with exactly two edits:

1. Import-path rewrite: `QuantumInfo.ForMathlib` → `RadicalRelativity.Vendor`
   (21 `public import` lines; every occurrence of the string `QuantumInfo` in
   these files is on an import line, so the rewrite touches nothing else).
2. `set_option relaxedAutoImplicit true` restored in `Matrix.lean` only, marked
   in-file as "Vendor edit 2". This repo's lakefile sets
   `relaxedAutoImplicit = false`, and upstream binds `dA`/`dB` as relaxed
   auto-implicits in the four Kronecker/partial-trace lemmas at
   `Matrix.lean:631-650`. Without the option those 22 occurrences are
   `Unknown identifier` errors. No other vendored module needs it.

There are **no other edits** — no option-line deletions, no renames, no added
helpers, no reformatting. The upstream `module` / `public import` /
`@[expose] public section` headers are retained as-is, and the 40
`set_option backward.isDefEq.respectTransparency false in` lines and 3
`set_option linter.overlappingInstances false` lines upstream carries are
present. Apart from edit 2, the previously inserted
`set_option relaxedAutoImplicit true` lines (one per module) are gone, so this
repo's lakefile options now apply to the rest of the island unmodified.

Everything in the "v4.32 → v4.28 backport" record below is **historical**: that
backport is abandoned as of this re-vendor, and none of its edits survive in
the tree. It is preserved as provenance for anyone diffing a SHA from
2026-08-04 through 2026-08-20, not as a description of current contents.

**Those 40 `respectTransparency` lines are load-bearing — do NOT drop them.**
They are the reason the previous backport's blanket deletion of them was a
mistake waiting to happen, and here is what they are for. Lean v4.33 flipped
`backward.isDefEq.respectTransparency`: `isDefEq` at `.instances` transparency
no longer unfolds non-reducible instance definitions. `HermitianMat` carries two
topologies —

- the `selfAdjoint` subtype topology, `Vendor/HermitianMat/Basic.lean:126`
  (`inferInstanceAs (TopologicalSpace (selfAdjoint _))`), and
- the metric topology induced by `instNormedGroup`,
  `Vendor/HermitianMat/Inner.lean:338`
  (`AddSubgroupClass.normedAddCommGroup _`)

— which are defeq but **not syntactically equal**. Under the new default the
elaborator stops *seeing* them as defeq, so `→L[ℝ]` gets built from one horn
while the normed-structure instances are registered against the other. Upstream
physlib hit this same wall and reached for the compatibility knob; that is why
`Basic.lean` alone carries six of these lines. Deleting them will not produce a
clean error — it produces instance-synthesis failures and `whnf` grind in
whatever downstream file happens to trip the diamond first.

**First-party code deliberately does not use this flag.** It is a compatibility
knob slated for removal, so the first-party fix for the same diamond is explicit
instance bridges, not the `set_option`. Inside the island the lines stay because
the island stays verbatim.

### Local generalizations removed by this re-vendor — RESOLVED 2026-08-21

Two first-party commits had generalized five vendored lemmas from `ℂ` to
`RCLike 𝕜` **in place**, inside the vendored files. Pulling upstream verbatim
removed all five. They were **not** backport scaffolding; they were capability
the first-party tree depends on:

- `HermitianMat/Order.lean` — `le_smul_one_imp_eigenvalues_le` and
  `eigenvalues_le_imp_le_smul_one` (commit 8ac68ca, carried a `DRIFT` note).
  First-party consumers needing the `𝕜` form: `Hermitian/OrderUnit.lean`,
  `Hermitian/ExtremeEffects.lean`, `Necessity/PseudoInverse.lean`,
  `Necessity/ThetaCocycle.lean`, and `Necessity/RealRigidity.lean` — the last
  over `HermitianMat n ℝ`, which no `ℂ`-only statement can serve at all.
- `HermitianMat/CFC.lean` — `norm_cfc_le_sqrt_card_mul_bound`,
  `norm_cfc_sub_cfc_le_sqrt_card`, `norm_cfc_sub_le_of_sup_le` (commit
  084412e, **no annotation of any kind**). Consumer needing the `𝕜` form:
  `Hermitian/CfcSqrtContinuous.lean`.

Nothing about v4.33 forces the narrowing: both enabling results
(`Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff` at `Vendor/Matrix.lean:425`
and `HermitianMat.norm_eq_sum_eigenvalues_sq` at
`Vendor/HermitianMat/CFC.lean:283`) are `𝕜`-general upstream already.

**Resolution.** The five are restated at `RCLike 𝕜`, under primed names, in
first-party code:

> `RadicalRelativity/Hermitian/RCLikeGeneral.lean`

The proofs are the ones from the pre-re-vendor tree, lifted unchanged: they were
carried over verbatim and **compiled first try at v4.33, needing no drift fixes
of any kind**. That is direct evidence the `ℂ` narrowing is an upstream
authorship choice and nothing in the toolchain forces it — the `𝕜`-general
statements are as provable at v4.33 as they were at v4.28.

The vendored `ℂ`-only originals are untouched and still serve the genuinely
complex call sites (`Necessity/TwistGeneral.lean`, `Hermitian/Symplectic.lean`). **The
island itself was not patched** — that is the whole point: the generalization
now lives in a module that *imports* the vendor instead of editing it, so a
future bump is a pure re-pull with no patch-reapplication step, and a wiped
generalization becomes a compile error instead of silent capability loss.

### STANDING INSTRUCTION FOR THE NEXT BUMP

After any re-vendor of this island, **diff declaration signatures against the
previous pin** before declaring the bump done:

Run this from the package root, with the working tree holding the freshly
re-vendored files. `OLD` is the commit the island was vendored at *last* time
(for the 2026-08-21 bump that was the pre-bump `main`). Anything it prints is a
statement that changed shape across the bump — inspect every block:

```sh
OLD=<pre-bump-sha>
SIG='^(private |protected |noncomputable |@\[[^]]*\] )*(theorem|lemma|def|abbrev|instance|structure|class) '
for f in $(git ls-tree -r --name-only "$OLD" -- RadicalRelativity/Vendor | grep '\.lean$'); do
  git show "$OLD:$f" | grep -E "$SIG" | sed 's/ *$//' > /tmp/sig-old.txt
  grep -E "$SIG" "$f" 2>/dev/null | sed 's/ *$//' > /tmp/sig-new.txt
  if ! diff -q /tmp/sig-old.txt /tmp/sig-new.txt >/dev/null; then
    echo "=== $f ==="
    diff /tmp/sig-old.txt /tmp/sig-new.txt
  fi
done
```

Verified against the 2026-08-21 bump: with `OLD=` the pre-bump commit, this
prints the `HermitianMat/CFC.lean` block showing all three 084412e lemmas going
`HermitianMat d 𝕜` → `HermitianMat d ℂ`, and the `HermitianMat/Order.lean` block
showing the 8ac68ca pair doing the same. It also correctly surfaces the removed
`private theorem PosDef.submatrix_of_injective` in `Matrix.lean`, and two benign
entries — a line-wrapping change in `Reindex.lean` and new upstream declarations
in the Wigner island. Two caveats: a docstring line that happens to begin with
the word `theorem` shows up as a spurious `>` line, and the loop's last `diff`
sets a non-zero exit status even on success, so do not gate a script on `$?`.

**Do not rely on `DRIFT` comment markers.** Commit 084412e left no marker of any
kind; a marker sweep found only the Order pair, and the CFC trio was recovered
solely by the signature diff. Note also that the narrowing does not always
present as a clean type mismatch: at `Hermitian/CfcSqrtContinuous.lean` it
surfaced as `whnf` **timeouts**, because forcing `𝕜 := ℂ` makes the elaborator
grind rather than fail outright.

**Inherited from upstream (still true at `a50684a191`):**

- `HermitianMat/Proj.lean` lacks a closing `end HermitianMat` (style-lint
  warning only); some docstrings end without a trailing newline. Left as-is to
  keep the diff against upstream at exactly the import rewrite.
- The `sorry` tokens in `Misc.lean` (lines 30, 34) sit inside a `/- -/` block
  quoting a Zulip-tracked mathlib diamond — dead text, not proof obligations.
- Consumer-side trap (campaign `docs/history/LEDGER.md` H6): the island declares
  `Matrix.*` lemmas inside `namespace HermitianMat` (`Inner.lean:402` and
  `Inner.lean:411` at this pin — `NonSingular.lean` no longer does, it opens
  `namespace Matrix` directly), creating a `HermitianMat.Matrix` namespace that
  shadows root `Matrix` for any `open scoped Matrix` issued inside
  `namespace HermitianMat` downstream, silently deactivating the `*ᵥ` notation.
  Open the scope before entering the namespace.

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

### Drift-edit log (v4.32 → v4.28 backport, 2026-08-04) — SUPERSEDED 2026-08-21

> **SUPERSEDED — HISTORICAL RECORD ONLY.** The backport this log describes was
> abandoned on 2026-08-21 when the island was re-vendored verbatim from physlib
> `a50684a191` at v4.33.0 (see "Re-vendor 2026-08-21" above). **None of the
> edits below are present in the tree any more**: the deleted option lines are
> back, the renames are reverted to upstream spellings, `convert!` is restored
> at all 19 sites, the inserted `set_option relaxedAutoImplicit true` lines are
> removed, and the hand-written `private theorem PosDef.submatrix_of_injective`
> is gone (upstream now provides `Matrix.PosDef.submatrix` natively). Read this
> section only to interpret a SHA between 2026-08-04 and 2026-08-20.
>
> One count below is also **wrong as written**: item 2 of the old vendor-time
> edit list claimed 23 `set_option backward.isDefEq.respectTransparency false in`
> occurrences were deleted. The true count at the old pin `ad1d812` is **18**
> across these 17 files (verified against upstream at that commit on
> 2026-08-21). The current pin `a50684a191` carries **40** — upstream added 22
> more between the two commits.

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

The cosmetic wart and the H6 consumer-side trap that were described here both
still hold at the current pin, but their line references had drifted
(`Inner.lean:405, NonSingular.lean:18` was accurate for `ad1d812` only). The
live, re-verified versions are in "Inherited from upstream" under the
Re-vendor 2026-08-21 section above — read those, not this paragraph.

## csd-lean4 Wigner-rigidity island

**Upstream:** `zblore/csd-lean4`, commit `2287f45` (2026-08-05), Apache 2.0
(per-file headers retained; upstream author Zayn Blore).  The files are
self-labeled "1-Mathlib (CSD-free Mathlib upstream candidate)" and live under
`namespace Projectivization`; nothing from the repo's speculative layers is
imported.

**Why vendored:** upstream is written in the new module system and pins
toolchain v4.33.0-rc1 (ours: v4.28.0), so a live dependency is impossible;
vendoring pins the exact audited code.  Due-diligence record: campaign
`docs/history/LEDGER.md` 3.0 (2026-08-04) — the WignerRigidity closure was built from
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

**Not in this island:** `RealWigner.lean` (the finite-dimensional real, non-bijective Wigner theorem) is
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
