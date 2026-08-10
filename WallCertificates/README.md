# Wall certificates

**Created 2026-08-09 as block 7.5 of the ARC-7 orders (`../LEDGER.md`).**

## Why this directory exists

This project's recorded failure mode is that **prices decay**. Over arcs 5 and 6 it accumulated
five false absence claims, two walls mispriced CHEAP, four wrong "Mathlib lacks X", and one row
(`lem:n2-bounded`) mispriced twice *in opposite directions* — first "one step, nothing but
plumbing", then "four steps, one genuinely analytic", when the truth was three steps and none of
them the kind first named. Every one of those was a **prose** price: a paragraph asserting a cost,
with nothing behind it that could fail.

A wall certificate is the same claim made falsifiable. Each file here:

1. **states the missing step in Lean**, at the article's own generality, with `sorry` at exactly
   the gap and nothing else;
2. **compiles** under `lake env lean` from the repo root;
3. carries a header recording the date, every absence claim *with the scope of the grep that
   supports it*, and what was actually attempted.

Where the wall is the *vocabulary* itself — no Lean statement can even be written down — the
certificate states the nearest statable approximation and names what is missing. That a statement
cannot be written is itself the strongest available evidence of depth, so it gets recorded rather
than asserted.

## The hygiene rule that makes this safe

**No file here is ever imported from `RadicalRelativity/`.** The library root
(`RadicalRelativity.lean`) does not reference this directory, so `lake build` and `AxiomAudit.lean`
never see it: the `sorry`s here cannot leak into the census, and the tree's "custom axioms exactly
`[]`" claim is unaffected. Verify with:

```
grep -rn "^import.*WallCertificates" RadicalRelativity/ RadicalRelativity.lean   # expect no hits
grep -n "lean_lib\|defaultTargets" lakefile.toml    # expect only RadicalRelativity
```

★ **The first version of this recipe was `grep -rn WallCertificates …` with "expect no hits", and it
was wrong** — caught 2026-08-09 by the certificate-refutation review. That pattern returns two hits
(`Necessity/LeftMultiplication.lean` and `Necessity/FrameConstancy.lean`), both harmless prose
cross-references inside docstrings. A verification recipe that reports failure on a healthy tree is
worse than none: it trains the reader to ignore it. The substance was independently confirmed —
`lakefile.toml` declares exactly one `lean_lib`, so `lake build` never compiles this directory.

Compile a certificate deliberately, one at a time:

```
cd /Users/ehrlich/repos/research/twist-normal-form-lean
lake env lean WallCertificates/<row>.lean      # expect: only `declaration uses 'sorry'` warnings
```

## One file, sometimes several rows

The ARC-7 orders said `WallCertificates/<row>.lean`. In practice several rows are open *for the same
reason* — EJA generality that is not statable, or one shared missing object — and splitting them
would mean repeating the same evidence and the same greps five times, which is how records drift
apart. So a file is named for its primary row and its header lists every row it covers. The index:

| File | Rows covered |
| --- | --- |
| `lem-n2-descent.lean` | 34 — ★ **row now FORMALIZED (ARC-8 8.1(d))**; the file's row conclusion is discharged in-file and its two surviving `sorry`s are labelled off-route. Kept for the retractions, not as a live price |
| `prop-n2-sufficiency.lean` | 30, 35 — ★ **ZERO gaps (ARC-8)**: row 30 FORMALIZED, and row 35's gap statement (the `∃!`-moduli claim) is discharged. ★★ Note that discharge does NOT close row 35 — the gap statement was weaker than the row, which is the under-specified-price defect kind |
| `differential-trio.lean` | 16, 17, 18 — ★ **ZERO gaps (ARC-8)**; the ℂ converse was already in the tree when the file was written |
| `abstract-tier.lean` | 3, 5, 6(i), 8, 9, 12, 13 |
| `frame-geometry.lean` | 15, 22, 26, 29(b), 31, 36(i) |
| `eja-gated.lean` | 5, 6, 13, 15, 16, 17 — the **EJA-GATED** certificate (ARC-8 8.6). States the three gates (E1) Jordan spectral / (E2) Peirce+FK / (E3) vIR once each rather than six rows six ways. ★ (E3) is row 14, pre-registered external, so rows 16/17 terminate here and cannot reach FORMALIZED by axiomatization alone |
| `thm-quaternionic.lean` | 20 |
| `external-rows.md` | 1, 2, 4, 10, 14, 21 — *not* certificates; the pre-registered external six |

## How to read a certificate

A certificate is **not** a claim that the row is unreachable. It is a claim about *where the work
is*, stated precisely enough that a reviewer can attack the statement rather than the prose. The
correct response to a certificate is to try to discharge its `sorry` — and if that succeeds
cheaply, the certificate was wrong and the row moves. That has already happened three times on
this project to prose prices; the point of the format is to make it happen faster.

Certificates are inputs to the arc's refutation review, and they are dated: a certificate is
evidence about the tree **on its date**, not a standing verdict.
