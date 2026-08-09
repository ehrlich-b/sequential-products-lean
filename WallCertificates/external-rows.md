# The six pre-registered external rows — best interior form and the external delta

**Date: 2026-08-09, ARC-7 block 7.5.** Tag `paperA-arc7-cp1`. Pin: `main.tex` blob `205fdf5a`.

These six rows are **not** wall certificates. They are the arc's second terminal state: decided
external in ARC-5/6, not re-litigated, and closing them is out of scope *by design*. What is in
scope is their best interior form, and that is what this file records — so that "external" never
becomes a place to hide work that is actually interior.

This file is Markdown, not Lean, because there is no missing step to state: the delta in each case
is a citation, not a gap.

| Row | Label | Why external | Best interior form reached | The external delta, exactly |
| --- | --- | --- | --- | --- |
| 4 | `thm:vdw1` | Cited result; the paper never claims to reprove it | none, by design | van de Wetering's theorem that a f.d. sequential product space is order-isomorphic to a Euclidean Jordan algebra |
| 10 | `prop:bridge` | Cited result | none, by design | that standard-product compatibility is exactly Jordan operator commutation |
| 1 | `mthm:master` | Stated over an *abstract* simple EJA, so the one-theorem form needs Jordan–von Neumann–Wigner | **the ℝ and ℂ rows outright** (`real_classification`, `complex_classification_unconditional`, both `+ _ouNorm`), each carrying only S1–S7 + S2 + a dimension bound, both Lean-core | JvNW: that every f.d. simple EJA is one of the four types. The campaign's one pre-registered permanent import |
| 2 | `mthm:omnibus` | Same, plus the summand decomposition | `MasterTheorem.Central.central_decomposition` (componentwise identity) | JvNW again, plus summand inheritance of S1–S7 (which is row 12's interior part, and is **not** external — see `abstract-tier.lean`) |
| 14 | `prop:theta` | The article states it at van Ittersum–Reijnders' JB-algebra generality | derived on **both** concrete carriers from in-tree Kadison rigidity | vIR's JB-algebra-level statement |
| 21 | `thm:albert` | Needs the unscoped Albert-algebra M2 machinery | `MasterTheorem.luders_albert_produced` at skeleton level, from cited Spin(8) block injectivity | the M2-for-Albert equational algebra. ★ **NOT the octonions** — see below |

## Two things about this table that are easy to get wrong

**`thm:albert` is not blocked on octonions, and the claim that it was got retracted.** The
octonions are absent from *Mathlib* but they are **built** in this project, at
`~/repos/research/lean/Octonions.lean`: 0 sorries, same toolchain v4.28.0, compiles clean, and its
one computational input `nucleus(𝕆) = ℝ` is **proved** (`Octonion.nucleus_real`, Lean-core axioms).
That file is out-of-tree, so it does not change the coverage count — but the row's obstruction is
the Albert-algebra equational machinery (`ALBERT-KERNEL-MEMO.md` rescoped it to "weeks of equational
algebra" on 2026-08-04), never the octonions. This distinction was asserted wrongly once and
corrected when challenged; it is recorded here so it is not re-asserted.

**"Needs JvNW" is a statement about the *one-theorem* form only.** Rows 1 and 2 have genuine
interior content that is *not* external, and it has been proved: the ℝ and ℂ rows of `mthm:master`
are machine-checked at the article's own generality on the concrete carriers. Reading rows 1 and 2
as "external" full stop would understate the tree by two of its strongest results. **Never rank the
ℝ row above the ℂ row or vice versa** — they are equally founded, each carrying only S1–S7 + S2 + a
dimension bound, both Lean-core. (The claim "ℝ is the only clean row" is false and superseded.)

## Ceiling arithmetic, restated with these six removed

36 rows − 6 external = **30 interior**, which is the ceiling. A realistic ceiling is **26–28**, once
`lem:simple-bridge` is read as ~3/4 cited (its own certificate prices it per clause) and the ℍ row
is priced honestly. As of this date the interior count is 10 FORMALIZED, so the interior remainder
is 16–18 rows, every one of which now carries a dated certificate in this directory.
