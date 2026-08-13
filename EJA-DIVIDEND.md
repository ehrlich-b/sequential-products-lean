# EJA-DIVIDEND.md — what the EJA axiomatization would buy Paper A

★★★ **STATUS 2026-08-12 (ARC-9): PART OF THE AXIOMATIZATION IS NOW BUILT, and this file's dependency
graph was wrong.** `RadicalRelativity/EJA/` (9 modules) contains the Peirce decomposition, all six
Faraut–Korányi multiplication rules, orthogonal idempotent families, **Albert's power-associativity
theorem**, formal reality with no-nilpotents, and the one-generator subalgebra. Consequences for the
table below:

* **"(E2) depends on (E1)" is STRUCK.** (E2) at a given idempotent needs the Jordan identity and the
  invertibility of `2`; nothing else. (E1) is what *produces* idempotents. **The order inverts.**
* **Three of the four hypotheses under `lem:coalescence` (row 16) are now theorems** —
  `opCommute_scalarOn_frame`, `mem_J2_of_half_half`, `diagFamily_scalarOn`. Only van de Wetering's
  Prop 5.5 stays cited. ★ Only one of the three uses the Jordan identity; the other two are
  bookkeeping that becomes available once the frame equations exist.
* **(E1) is certificated, not done** — `WallCertificates/eja-spectral.lean`, two of four steps built,
  and the obstruction is structural (ring theory wants a unit; this layer is unit-free).
* **No row in the table below has moved**, and the CLOSES/PARTIAL/NOTHING verdicts are unchanged. What
  changed is that the *work* those verdicts price is partly done, and that the residue for rows 16/17
  is now interface surgery on `ComparisonSetup` — which carries `p : Fin n → J` with **no axioms** —
  rather than Jordan theory.


**Created 2026-08-09, ARC-8 block 8.6. Required deliverable of the ARC-8 ORDERS.**
**Pin:** `STATEMENT-MANIFEST.md`'s 36 rows, main.tex blob `205fdf5a` (never re-pinned).
**Status snapshot:** written against 12 FORMALIZED / 19 PARTIAL / 5 ABSENT; **refreshed 2026-08-10** to 12 FORMALIZED / **3** EJA-GATED / 16 PARTIAL / 5 ABSENT. ★★ **EJA-GATED was briefly claimed for six rows and withdrawn the same day for rows 5, 6 and 15** — their residues include NON-EJA clauses (row 5's ball clause needs the order-unit norm; row 6's clause (ii) is already abstract via `SequentialProductOn.sp_smul_left`; row 15's `Stab(F)°` clause needs identity-component vocabulary). **So this table's "CLOSES" column is NOT the EJA-GATED list**: CLOSES means the axiomatization would move the row, which for rows 5, 6, 15 is true of *part* of the residue only — see `WallCertificates/eja-gated.lean`, which states the three gates.

---

## What "the EJA axiomatization" means here, precisely

`RadicalRelativity/MasterTheorem/Interface.lean`'s `structure ComparisonSetup` carries the abstract
Jordan-algebra layer the master theorem runs on: a Jordan product `jordan`, a unit `e`, a rank `n`
with `rank_ge : 3 ≤ n`, a Jordan frame `p : Fin n → J`, a cone `nonneg`, `Inv`, `aOf`, and
`Theta : J → (J ≃ₗ[ℝ] J)` with `Theta_unital` / `Theta_orderIso` / `Theta_jordan`. Its own docstring
states the limitation: it **does not encode the JB-algebra premises** — the Jordan identity, formal
reality, and the cone-of-squares reading of `nonneg`.

So the axiomatization is: **encode those premises, and derive as theorems what the structure now
carries as fields.** Concretely the deliverables would be

* **(E1) a Jordan spectral theorem** at f.d. formally-real Jordan generality — spectral resolution
  into a Jordan frame with real eigenvalues, and a functional calculus on it;
* **(E2) the Peirce decomposition** `J = ⊕ J_{ij}` for a Jordan frame, with the Faraut–Korányi
  multiplication rules — currently carried as `CoalescenceSetup` fields.
  ★★★ **PARTLY BUILT, AND THE DEPENDENCY BELOW IS CORRECTED, 2026-08-12 (ARC-9 blocks 9.2/9.3).**
  The Peirce decomposition **at a single given idempotent** is in the tree
  (`RadicalRelativity/EJA/Peirce.lean`): the polynomial identity `2L_c³ − 3L_c² + L_c = 0`, the three
  projections, existence *and* uniqueness of `J = J₁(c) ⊕ J_{1/2}(c) ⊕ J₀(c)`, and the eigenvalue
  trichotomy. It needs the Jordan identity and the invertibility of `2` — no spectral theorem, no
  formal reality, no finite dimension, no unit.
  ★★ **This cell was written at block 9.3 and was stale by 9.4, in two ways, both caught on the
  re-read after the arc's own diff audit.** (a) It said "and nothing else", the same overclaim the
  audit had just fixed in two `.lean` docstrings — a third copy, in a third file. (b) It said the FK
  **multiplication rules** were "still absent": they were built at block 9.4
  (`EJA/PeirceMul.lean`, all six), together with the orthogonal-idempotent layer at 9.6/9.7.
  ★ What *is* still absent is the **frame** decomposition `⊕_{i≤j} J_{ij}` as a single statement —
  the rules and the pairwise machinery exist, the assembled direct sum over a frame does not;
* **(E3) `Theta_jordan` derivable** — van Imhoff–Roelands: an order isomorphism of the cone that is
  unital preserves the Jordan product. Currently a field, and pre-registered EXTERNAL as row 14.

**★ Scope warning that governs every line below.** (E3) is *the content of a cited external theorem*
(row 14, `prop:theta`, pre-registered external at vIR generality). Building the axiomatization does
NOT prove it; it makes it *statable* at the right generality so it can be cited or proved separately.
Rows whose only residue is (E3) therefore move from "carried as an unexaminable field" to
"EJA-GATED behind a named external theorem" — a real gain in honesty, **not** a move to FORMALIZED.
Any reading of this table that converts (E3)-dependence into FORMALIZED is wrong.

---

## The table

Column meaning: **CLOSES** = the axiomatization would move the row to FORMALIZED.
**PARTIAL** = it removes some but not all of the residue. **NOTHING** = the residue is orthogonal.

| # | row | residue today | axiomatization would… | why |
|---|-----|---------------|------------------------|-----|
| 1 | `mthm:master` | the one-theorem form (JvNW), pre-registered external | **NOTHING** | the residue is a cited classification theorem, not the Jordan layer |
| 2 | `mthm:omnibus` | one-theorem form; external | **NOTHING** | same |
| 3 | `def:sp` | Lean *packaging* of the article's eight clauses + restriction/extension maps | **NOTHING** | pure interface work on an order-unit space; no Jordan structure enters |
| 4 | `thm:vdw1` | external (vdW) | **NOTHING** | cited theorem |
| 5 | `lem:span` | the Peirce half **and** the ball clause | **PARTIAL** | ★ **CORRECTED 2026-08-10**: the ball clause needs the norm to *be* the order-unit norm and is not an EJA gap. For the Peirce half, the statement is a Peirce-span identity, and with (E2) it becomes statable and provable where today only the concrete carrier is. ★ The first version of this cell contained a stray table-separator character, giving it 8 fields where every other row has 7, so the explanation rendered as a dropped column. Found by the diff audit by counting fields per row; and the first attempt to *record* that fact reintroduced the same defect, because the note itself named the character. |
| 6 | `lem:homog` | clause (i)'s abstract port | **PARTIAL** | ★ **CORRECTED 2026-08-10**: clause (ii) is **already proved at abstract order-unit generality** (`SequentialProductOn.sp_smul_left`, S1–S7 + S2 + `IsArchimedean`), so the earlier "(E1), a Jordan-spectral fact" was wrong — it came from citing a theorem about the *twist* product rather than an arbitrary one. Clause (i)'s port needs the order-unit route (`span_isEffect_eq_top`), not spectral theory |
| 8 | `lem:simple-bridge` | clause (ii) at EJA generality (clauses i/iii/iv cited to vdW) | **PARTIAL** | (E1) gives clause (ii) — "every effect is simple" IS the Jordan spectral theorem. Clauses (i), (iii), (iv) stay cited, so the row is ~3/4 external either way |
| 9 | `lem:normality` | order-**infimum** form; abstract f.d. order-unit generality | **NOTHING** | needs `⨅` for the Loewner/order-unit order and Loewner monotone convergence. An order-theoretic gap, not a Jordan one |
| 10 | `prop:bridge` | external | **NOTHING** | cited |
| 12 | `prop:central` | the **restriction** direction (= `prop:central`'s splitting) | **NOTHING** | needs "a product is compatible with each central idempotent"; the carrier is `V × W` order-unit spaces, no Jordan layer involved |
| 13 | `prop:pseudo-transfer` | EJA generality (proved on the concrete carrier in normalized form) | **CLOSES** | the pseudo-inverse is defined by functional calculus — (E1) |
| 14 | `prop:theta` | vIR generality; **pre-registered external** | **PARTIAL** | ★★ **The identification is OPEN (2026-08-10):** `gate_E3` as stated assumes `Φ` LINEAR, so it is the classical Koecher/Alfsen–Shultz theorem, not vIR's JB-generality version — the two may not be the same row. Formerly: (E3) *is* this row. The axiomatization makes it statable at vIR generality; proving it is the external import. Improving the interior form is in scope, closing it is not |
| 15 | `lem:frame-fix` | Peirce-block clauses **and** the `Stab(F)°` clause | **PARTIAL** | ★ **CORRECTED 2026-08-10**: the `Stab(F)°` clause needs identity-component vocabulary and is not an EJA gap. The Peirce-block clauses are (E2) |
| 16 | `lem:coalescence` | **citation/axiomatization gap only** — both clauses are already proved over `ComparisonSetup` | **CLOSES** | this is the cleanest case in the table: the mathematics is done at the interface's generality; what is missing is that `Theta_jordan` and the FK fields are *carried* rather than derived. (E2)+(E3) |
★★★ **ARC-9 UPDATE (2026-08-13) on row 16: the (E2) half is DISCHARGED on the concrete carrier.** `EJA/ConcreteInstance.lean` builds `ejaComparison` from `Necessity.comparisonSetup` plus the five equations, and `toCoalescenceSetup` produces a `CoalescenceSetup` on `H_N(ℂ)` with `simDiag_opCommute`, `aOf_scalarOn` and `block_mem_J2` **proved**. The row does not close: `Θ_fix` and `Θ_jordan` remain cited, so what is left of the gate is **(E3) only**. ★ The same work showed `WallCertificates/eja-gated.lean`'s `gate_E2_peirce` is under-hypothesised — its `haOf` does not tie the coefficients to `r`.

| 17 | `lem:homomorphism` | generality only (hyperplane clause closed ARC-6) | **CLOSES** | same shape as row 16 |
| 18 | `prop:stabilizers` | the `T^{n-1}` packaging; the ℝ/ℍ/𝕆 rows | **NOTHING** | ℂ row is done in `U(n)`; the remainder is a quotient-by-global-phase packaging and three concrete type-specific computations. No Jordan generality needed |
| 20 | `thm:quaternionic` | the **transfer** (`Θ_r = id` for an arbitrary product) | **NOTHING** | the carrier is concrete (`QuatCarrier n`, symplectic-fixed subspace of `H_{2n}(ℂ)`) and the product now exists on it; the open question is whether `Z(ℍ) ∩ Im ℍ = {0}` survives the embedding — a concrete computation |
| 21 | `thm:albert` | Albert M2 equational machinery; **pre-registered external** | **NOTHING** | not blocked on octonions; blocked on weeks of equational algebra. ★ Octonion claim re-checked 2026-08-10 (dry-pass round 4) and the path corrected: the file is `~/repos/research/lean/RadicalRelativity/Octonions.lean` (a **different Lean project**, toolchain v4.28.0), and `grep -c sorry` on it returns **0**. ★ Scope: that is a grep for the token, not a compile — this arc did not build that project, and the "0 sorries" claim is carried from the 2026-07 record rather than re-verified by elaboration |
| 22 | `lem:orientation` | the coherence space as a carrier (`J_{q,k}`, splitting-independence, `Ad_{a^{it}}`) | **PARTIAL** | (E2) supplies the Peirce/coherence vocabulary the statement needs; the `Ad_{a^{it}}` formula and splitting-independence are additional work |
| 26 | `lem:frame-connectivity` | Givens/Jacobi factorization into rank-two block rotations | **NOTHING** | absent from the tree AND from Mathlib (`Givens` over v4.28.0: zero hits); a matrix-group fact, orthogonal to the Jordan layer. Standalone Mathlib contribution. ★ Do not "refute" this with `Necessity/BlockRotation.lean` — that file is the rotation *acting on* a Peirce block, not a factorization *into* block rotations; see the note in `frame-geometry.lean` |
| 29 | `prop:n2-necessity` | gap (b): the Θ-level vs product-level equivalence | **NOTHING** | rank two, concrete carrier |
| 31 | `thm:qubit-boundary` | unimodular cocycle subcases; clause (iii) in the `(Φ,t)`-conjugation form | **NOTHING** | rank two, concrete |
| 35 | `cor:qubit-classification` | agreement on **effect × effect** — proved at positive-definite first arguments, open at singular ones | **NOTHING** | rank two, concrete. ★★ **This cell's earlier residue ("the onto half at singular effects, an S2 limiting argument") was REFUTED at checkpoint 2**: the onto half is FALSE, not unwritten — the tree's own `Necessity.badP` has the same moduli function and a different `.sp` (`RankTwo.not_exists_moduli_of_badP`). The target is products up to agreement on effects |
| 36 | `cor:selectors` | clause (i): the Peirce-exchange action on `H_N(ℂ)` | **NOTHING** | the carrier is concrete `H_N(ℂ)`; the missing object is a concrete coherence-block action, and the mechanism is already machine-checked at rank two |

---

## The decision, on this evidence

**Counting, CORRECTED 2026-08-10: CLOSES 3 rows (13, 16, 17); PARTIAL on 6 (5, 6, 8, 14, 15, 22); NOTHING on 15.** ★ The verdict below is unchanged in direction — the axiomatization is still the largest available block of row movement and still the only thing that touches rows 13/16/17 — but it now moves **three** rows outright rather than six, and the ★★ qualification about rows 16/17 is itself **OPEN** (see the terminal-state ledger: `gate_E3` as stated is the classical linear theorem, not vIR's).

So the axiomatization is **not** nothing — it is the single largest remaining block of row movement
available, and it is the *only* thing that CLOSES rows **13, 16, 17** — and the only thing that moves
the EJA *part* of rows 5, 6, 15, whose residues also contain non-EJA clauses (the ball clause, clause
(i)'s order-unit port, the `Stab(F)°` clause). The
do-it-unless-it-does-literally-nothing test is therefore **passed with room to spare**: the ARC-8
orders' pre-registered condition for skipping it does not fire.

**★★ But three qualifications, and they are why this table exists rather than a headline number.**

1. **The three CLOSES rows are all "generality-only" rows.** Each is already proved on the concrete
   carrier or over `ComparisonSetup`; what the axiomatization buys is that the *article's own*
   hypothesis class becomes expressible. That is exactly the standing bar ("FORMALIZED at the
   article's own generality, no located hypothesis"), so the movement is real — but a reader should
   know that none of these three is a row where the *mathematics* is missing.
   ★ **This numeral said "six" in three places until 2026-08-12 (ARC-9 block 9.1)**, one day after
   the count was corrected to three at the head of this section — the appended correction, the
   un-rewritten summary. Sixth instance on this project; the check is `grep -n "six" EJA-DIVIDEND.md`
   and it costs one command.
2. **Row 14 is the load-bearing one and it is external.** Rows 16 and 17 close only if
   `Theta_jordan` becomes derivable, and deriving it *is* `prop:theta` at vIR generality — a
   pre-registered external import. So the honest form of "16 and 17 close" is: **they become
   EJA-GATED behind a named citation instead of carrying an unexaminable field.** If the
   axiomatization is built and vIR is still cited, rows 16/17 end at EJA-GATED, not FORMALIZED.
   ★ This is the single most likely way this table gets misread.
3. **Nothing in the rank-two lane depends on it.** Rows 29–36 — the whole qubit crown, including the
   two that closed today — are concrete-carrier work. The axiomatization and the rank-two lane are
   independent programs, and the rank-two lane is the one with a paper-facing headline.

**Estimated shape of the work, for the record and not as a commitment:** (E1) a Jordan spectral
theorem is the large piece and has no Mathlib support (`lean-formalization-landscape`: essentially
none of the Jordan/EJA stack is formalized in any prover); ~~(E2) Peirce decomposition depends on
(E1)~~; (E3) is a citation. So the axiomatization is one big theorem plus its corollaries, and its
natural home is upstream of this paper — a Mathlib-grade EJA layer — not inside `RadicalRelativity`.

★★★ **"(E2) depends on (E1)" is STRUCK, 2026-08-12 (ARC-9 blocks 9.2/9.3), and the order inverts.**
The Peirce decomposition at a *given* idempotent is derivable from the Jordan identity alone and is
now in the tree. (E1) is what *produces* idempotents; rows 13, 16, 17 never ask anyone to produce
one, because `ComparisonSetup` carries the frame as **data** (`p : Fin n → J`). So (E2) comes first
and (E1) is not on the critical path for rows 16/17.

★ **And the pre-registered "Peirce-facts-as-hypotheses" test below is ANSWERED: the refactor is
viable, and it is larger than it sounds.** `ComparisonSetup.p` carries **no axioms** — not
idempotence, not orthogonality, not summing to `e`, and not `aOf r = Σ exp (r i) • p i`. The refactor
must add those equations before it can derive `frame_opCommute`, `aOf_scalarOn`, `block_mem_J2` and
`simDiag_opCommute`. Bounded work, none of it a spectral theorem. Full pricing in `LEDGER.md`,
ARC-9 blocks 9.2/9.3.

**What would change this verdict:** if (E1) turns out to require the spectral theorem only for the
*specific* frames the article uses (rather than in general), the three CLOSES rows might be reachable
by a much smaller "Peirce-facts-as-hypotheses" refactor of `ComparisonSetup` that keeps them
EJA-GATED but removes the unexaminable-field objection. That refactor is cheap and has not been
priced; it is the first thing to test before committing to (E1).
