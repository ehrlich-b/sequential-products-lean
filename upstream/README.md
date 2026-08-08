# `upstream/` — Mathlib contribution candidates, STAGED

**Status: STAGED, NOT SUBMITTED. Nothing here has been sent anywhere.** Submission is
Bryan's decision, not this directory's. Created 2026-08-08 (campaign `LEDGER.md` item 4.4).

Contents:

| File | What it is |
| --- | --- |
| `Wigner.lean` | Wigner's theorem over ℝ, PR-shaped: Mathlib naming, Mathlib-style module docstring, no campaign references, zero warnings under `linter.mathlibStandardSet`. |
| `PR-DESCRIPTION.md` | The PR body, ready to paste. |

## Why this one file and nothing else

The 2026-08-08 tri-agent audit asked what in this tree is worth upstreaming. The answer was
one clear YES and one maybe:

- **YES — real Wigner/Uhlhorn rigidity.** It exists in no proof assistant (see the collision
  check below), it is elementary and self-contained, and Mathlib has nothing in this area at
  all. In-tree it is `RadicalRelativity/Wigner/RealWigner.lean` (first-party, ~1.07 kL).
- **Maybe, behind it — real Kadison rigidity** (`Necessity/RealKadison.lean`,
  `orderAutoR_eq_orthConj`): a unital order-automorphism of `H_N(ℝ)` is orthogonal
  conjugation. Not staged here, because it depends on the `HermitianMat` carrier, which is
  vendored third-party code (physlib, Alex Meiburg) and belongs to that author's upstream
  track, not ours.
- Everything else is either someone else's code (the two vendored islands), already in
  Mathlib in stronger form, or correctly paper-specific.

## Collision check (performed 2026-08-08, read-only)

Method: GitHub API/code search against each target's default branch. Recorded here because
the answer is the whole reason this PR is worth preparing.

| Target | Result |
| --- | --- |
| `leanprover-community/mathlib4` (master) | **No Wigner's theorem and no Uhlhorn, in any field.** Code search for `wigner` returns exactly one hit — `docs/1000.yaml`, the "1000 theorems" wishlist entry *Wigner–Eckart theorem*, which is a different theorem and is listed precisely because it is not formalized. `uhlhorn` and `transProb` return nothing. `Mathlib/LinearAlgebra/Projectivization/` contains `Action, Basic, Cardinality, Collinear, Constructions, Independence, PSL, Subspace` — no topology, no metric or measure structure, nothing about transition probabilities. |
| `zblore/csd-lean4` | Complex only. The `Projectivization/` directory has grown since our vendor pin `2287f45` (now also `Bargmann`, `FubiniStudyUnique`, `PhaseRigidity`, `UnitaryTransitive`, `WignerUniqueness`), all over ℂ. Code search finds no real-field transition probability; the only `InnerProductSpace ℝ` hit is prose in `specs/plan-b-detail.md` about instance resolution for a Gaussian measure. `BACKLOG.md` lists no real-field Wigner. **So we are not pre-empting that author's track — and the ℂ case is his, not ours.** |
| `leanprover-community/physlib` | No `Wigner` or `Projectivization` files at all. |

Consequence worth stating in the PR: **the real case needs no missing Mathlib
prerequisites.** The complex case requires projective topology and Fubini–Study measure
theory (an entire eight-module island in our tree). The real proof imports exactly
`Mathlib.Analysis.InnerProductSpace.PiL2` and `Mathlib.LinearAlgebra.Projectivization.Basic`
and nothing else.

## Prepared answers to the reviewer questions we expect

**"Why not unify over `RCLike`?"** The *definitions* would unify — `transProbVec`,
`transProb`, `TransProbPreserving`, `projMap` all make sense over any `RCLike` field. The
*theorem* does not: over ℂ the conclusion carries a second, antiunitary branch with no real
counterpart, so a common statement would either weaken the real result or be a disjunction
that is vacuous on one side. Deliberately not unified here for a second reason as well: the
complex case is being developed independently by another author (see the collision table),
and pre-empting his naming with a general definition would be the wrong way to arrive at a
shared API. If maintainers prefer the general definitions now, they generalize mechanically
and we are happy to do it — that is a maintainer call.

**"Why `projMap` instead of `Projectivization.map`?"** It *is* `Projectivization.map`:
`projMap e = Projectivization.map e.toLinearEquiv.toLinearMap e.injective` by definition
(`Wigner.lean:119`). It exists only to avoid writing that spelling in every statement. If
reviewers would rather see `Projectivization.map` inline, the abbreviation can be deleted
and every use rewritten mechanically.

**"Is bijectivity hidden in the hypothesis?"** No. `TransProbPreserving f` unfolds to
`∀ p q, transProb (f p) (f q) = transProb p q` and nothing else — this is the Uhlhorn form,
strictly stronger than the version that assumes a bijection. Injectivity is *derived*
(`transProb = 1` forces equality of rays) and surjectivity comes out with the isometry.

## Remaining work before this could be submitted

Listed so that "staged" is not mistaken for "ready to send":

1. **Rebase onto Mathlib master.** The file is verified against the Mathlib revision pinned
   in this repo (`v4.28.0`), which is behind master. Every name it uses must be re-checked
   there; expect a handful of generational renames.
2. **Add `references.bib` entries.** The module docstring cites `[wigner1959]` and
   `[uhlhorn1963]`; Mathlib's `docs/references.bib` currently contains **neither** (checked
   2026-08-08), so the PR must add both.
3. **Choose the file path.** Proposal: `Mathlib/Analysis/InnerProductSpace/Wigner.lean`
   (it is analysis-flavored and needs `PiL2`); alternative
   `Mathlib/LinearAlgebra/Projectivization/Wigner.lean` if maintainers prefer to keep the
   projective material together, at the cost of an analysis import in that directory.
4. **Split or don't split.** The transition-probability definitions could go in their own
   file, which is what the complex development did upstream-of-itself. One file is proposed
   here because it is only ~1.07 kL and the definitions have no other consumer yet.
5. **Contact the complex author.** Courtesy, and the right way to avoid an API fork.
6. **Verification etiquette.** A Mathlib PR is a public, outward-facing action; per the
   standing rule it does not happen without Bryan saying so.

## Relation to the in-tree file

`upstream/Wigner.lean` is a **copy** of `RadicalRelativity/Wigner/RealWigner.lean` with:

- the `R` suffixes dropped (`transProbVecR → transProbVec`, `transProbR → transProb`,
  `TransProbPreservingR → TransProbPreserving`, `projMapR → projMap`, and every compound).
  In-tree those suffixes are *required*, because the vendored complex development occupies
  the unsuffixed names in the same `Projectivization` namespace; in a Mathlib PR there is no
  complex version to collide with;
- the module docstring rewritten in Mathlib's `## Main definitions / ## Main results /
  ## Implementation notes / ## References` shape, with all campaign, paper, and vendoring
  references removed;
- `set_option linter.style.longLine false` deleted — it was vestigial, no line exceeds 100
  characters;
- the license header in Mathlib's exact wording.

- the capstone's own docstring rewritten (Mathlib phrasing, no reference to the vendored
  complex theorem).

Both copies additionally had two unused `[DecidableEq ι]` instance arguments removed
(`eq_sum_over_support`, `eq_pair_expansion`, now using `classical` in the proof).

**Verified, not asserted.** Apply the five renames to the in-tree file and diff the bodies:

```bash
sed -e 's/TransProbPreservingR/TransProbPreserving/g' \
    -e 's/transProbPreservingR/transProbPreserving/g' \
    -e 's/transProbVecR/transProbVec/g' \
    -e 's/transProbR/transProb/g' \
    -e 's/projMapR/projMap/g' \
    RadicalRelativity/Wigner/RealWigner.lean > /tmp/renamed.lean
diff <(sed -n '/^noncomputable section/,$p' /tmp/renamed.lean) \
     <(sed -n '/^noncomputable section/,$p' upstream/Wigner.lean)
```

Result 2026-08-08: the *only* hunk is the capstone docstring above. Every definition,
statement, and proof is byte-identical.

**Audit scope.** `AxiomAudit.lean`'s census walks the `RadicalRelativity` prefix only, so
`upstream/Wigner.lean` is deliberately **outside** every gate in this repo — it is a copy
destined for a different project, and `lake build` does not compile it either (the library
root does not import it; job count is unchanged at 3106). The audited artifact is the in-tree
twin. Do not read a green audit as covering this directory.

**Divergence risk:** these are two copies of one proof, and nothing enforces that they stay
in sync. If the in-tree file changes, this one must be regenerated — the rename is
mechanical (five `sed` substitutions, recorded above) plus the header/docstring swap.

## Verification of the staged file

```bash
# from the repo root
lake env lean -Dlinter.mathlibStandardSet=true upstream/Wigner.lean
```

Result 2026-08-08: exits 0, **zero warnings and zero errors** under Mathlib's standard
linter set. The in-tree twin is covered by `AxiomAudit.lean`, which certifies closure
⊆ `{propext, Classical.choice, Quot.sound}` and no `sorry`/custom axiom.
