# Campaign discharge ledger — Paper A full verification

**Created 2026-08-04 (M0 design pass). Route:** `research/PAPER-A-LEAN-ROUTE.md`
(blog repo). **Division of labor:** `THEOREM-MAP.md` states what the tree IS
(the governing honesty ledger, updated every milestone); this file states what
REMAINS and how each item discharges. An item leaves this ledger only when
THEOREM-MAP's corresponding row moves to "machine-checked."

**Target restated:** zero-sorry per-type proofs of `mthm:master`
(H_n(ℝ), H_n(ℂ) n≥3, H_n(ℍ), H₃(𝕆)), `cor:qubit-classification`,
`mthm:omnibus`; closure = Lean core + at most JvNW as disclosed import; every §2
interface structure instantiated on the intended algebras.

---

## ★★★ ARC-8 ORDERS (2026-08-09, Fable design pass — the ceiling campaign). READ THIS FIRST.

**SCOPE DECISION (Bryan, 2026-08-09):** this arc does everything interior EXCEPT the EJA
axiomatization — encoding the JB-algebra premises (Jordan identity, formal reality, cone of
squares) so the vIR/FK facts that `MasterTheorem/Interface.lean` carries as *fields* become
theorems. That work is **COMMITTED, scheduled before Paper A's submission, unless the
dividend table (block 8.6) shows it would do literally nothing for Paper A** — the table is
this arc's decision instrument, and building it is not optional. The six pre-registered
external rows stay external (tranche-4 work — JvNW, vdW's theorems, vIR generality, Albert
M2 — is downstream of the axiomatization and equally out of scope).

**TERMINAL CONDITION (the whole goal; nothing else ends the arc):** every one of
`STATEMENT-MANIFEST.md`'s 36 rows (pinned to blob `205fdf5a` — never re-pin) is in exactly
one of FOUR states —

1. **FORMALIZED** at the article's own generality, no located hypothesis (the standing bar);
2. **EXTERNAL by pre-registration** — the same six, not re-litigated: `thm:vdw1`,
   `prop:bridge`, `mthm:master`/`mthm:omnibus` one-theorem form (JvNW), `prop:theta` at vIR
   generality, `thm:albert`. Improving their interior form is in scope; closing them is not;
3. **EJA-GATED** — a fresh certificate, dated this arc, establishing that the row's ENTIRE
   remaining residue is exactly the EJA axiomatization gap: every non-EJA clause is closed
   in-tree first, and the certificate states the article-generality statement in Lean with
   `sorry` exactly at the axiomatization gap, naming WHICH ingredient gates it (Jordan
   spectral theorem, Peirce decomposition at generality, formal reality, `Theta_jordan`
   derivable, FK fields derivable). Claiming EJA-GATED without having closed the non-EJA
   clauses does not count — that is the "external as a place to hide interior work" failure
   `external-rows.md` warns about, applied one ring in;
4. **WALL-CERTIFIED this arc** — ARC-7's certificate spec unchanged (compiling file in
   `WallCertificates/`, never imported from `RadicalRelativity/`, `sorry` at exactly the
   gap, dated absence claims carrying the grep's scope), with one tightening: **attack
   evidence must be FROM THIS ARC.** Carried-over evidence does not terminate a row —
   ARC-7's refutation review falsified six certificate entries in a day; a certificate that
   was not re-attacked this arc is a prose price with a `.lean` extension.

— AND `EJA-DIVIDEND.md` exists at the repo root: one row per non-FORMALIZED manifest row,
stating exactly what the axiomatization would move (closes it / partially / not at all,
and why), so the do-it-unless-it-does-nothing decision is decidable on evidence; AND the
block-8.6 dry pass over every non-FORMALIZED row has produced zero movement; AND at least
four checkpoint reviews have reported, their findings verified at source and applied or
rejected with evidence. Do not stop at block boundaries; the count is an OUTPUT, not a
quota (10/19/7 at these orders; 20 rows in play = 36 − 10 FORMALIZED − 6 external;
realistic ceiling 26–28, and the gap between that and 30 is mostly the axiomatization this
arc defers).

**THE BLOCKS (in order; wall protocol = write the certificate and continue):**

* **8.0 Audit before build.** The six ARC-7 certificates ARE the work orders — re-read them
  as attack plans, not records. Verify tree state (build, census `[]`, tags). Standing
  first moves everywhere: `grep -n "^def \|^theorem \|^instance \|^abbrev \|^structure "`
  on any file before claiming absence in its subject area; full-output error counts +
  `#print axioms` for any compile claim; `lake` only from the repo root.
* **8.1 The rank-two corollary — the crown.** In dependency order:
  (a) finish the compatibility chain — steps 3(b) and 4 as mapped in
  `WallCertificates/prop-n2-sufficiency.lean`; two of four are in-tree
  (`offdiag_zero_of_commute_diagonal`, `eigen_diagonal_fin2`);
  (b) **`prop:n2-sufficiency`** — all seven axioms for the frame-dependent family,
  generalizing `twistSequentialProduct`'s constant-`t` machinery; the hard half of
  compatibility is in-tree as `commute_of_twistSeq_comm_param`;
  (c) `thm:qubit-boundary`'s bundled S1–S7 clause as an instantiation of (b), plus the
  unimodular cocycle subcases;
  (d) `lem:n2-descent` assembly — the `U(2) → ℂP¹` first-column ray map, "same ray ⟹
  monomial difference", the quotient construction of `C(ℝP², ℝ)`, and the
  `QubitFrame`/`FrameSpace` homeomorphism (priced 40–60 lines by a reviewer, ★ NEVER
  TESTED — treat the price as SUSPECTED);
  (e) `prop:n2-necessity` gap (b) — the Θ-level vs product-level equivalence;
  (f) **`cor:qubit-classification`** — the bijection, from (a)–(e) plus rows 32/33 (done).
  ★ CHECKPOINT after (f).
* **8.2 The cheap interior sweep.** Row 18's ℂ converse (`frame_stabilizer_is_torus`,
  stated ready in `WallCertificates/differential-trio.lean`, priced a short matrix
  argument); row 8 clause (ii) on the concrete carrier (Mathlib's spectral theorem); row
  9's remaining clauses (compatibility-passes-to-infima, plus the article's f.d.
  order-unit generality — that is `⨅`-vocabulary work, NOT EJA); row 12's restriction
  direction (the converse assembly already exists — `SequentialProductOn.prod`); row 3's
  packaging (the article's eight clauses as a structure + an equivalence with
  `SequentialProductOn`; flagged the highest movement-per-effort item on the board);
  `cor:selectors`(i)'s Peirce exchange object on the concrete carrier (the mechanism is
  machine-checked at rank two). ★ CHECKPOINT.
* **8.3 The quaternionic transfer (row 20) — the arc's biggest single build.** The named
  route, per `WallCertificates/thm-quaternionic.lean`: a `SequentialProductOn
  (QuatCarrier n)` (carrier + `OrderUnitSpace` instance exist); a functional calculus on
  the carrier assembled from `quatQuadRep`; then the transfer — whether the article's
  `Z(ℍ) ∩ Im ℍ = {0}` mechanism (in-tree at skeleton level,
  `luders_quaternionic_produced`) survives the `H_n(ℍ) ↪ H_{2n}(ℂ)` embedding is
  **genuinely open**; land `thm:quaternionic` at the article's own `H_n(ℍ)`, `n ≥ 3`, or
  certificate the exact step that resists. The `Gen`-layer impossibility (ℍ is never
  `RCLike`) is settled — do not re-derive it; the involution route is the only route.
  ★ CHECKPOINT.
* **8.4 The geometry pair.** `lem:frame-connectivity` — Givens/Jacobi factorization of a
  unitary into rank-two block rotations (absent from tree AND Mathlib; build it
  Mathlib-grade, it is a standalone contribution); `lem:orientation` — the coherence space
  as a carrier: `J_{q,k}`, splitting-independence, commutation with stabilizing inner
  automorphisms, the `Ad_{a^{it}}` formula.
* **8.5 The stabilizer rows + frame-fix.** Row 18's ℝ row (trivial stabilizer); ℍ row
  (`Sp(1)^n` action — reuses 8.3's carrier); 𝕆 row certificate-only (Spin(8)/triality is
  Albert-adjacent — do NOT sink time); `lem:frame-fix`'s non-EJA content, then EJA-GATED
  or certificated.
* **8.6 The dividend table, dry pass, refutation review.** Write `EJA-DIVIDEND.md` from
  the terminal states; dry pass over every non-FORMALIZED row, repeated until a full round
  produces zero movement; certificate-refutation review over EVERY certificate standing at
  arc end (written this arc or carried), attacked the way ARC-7's review attacked absence
  claims — its three defect kinds (FALSE, VACUOUS, SELF-DEFEATING) each get their test.

**REVIEW PROTOCOL — unchanged from ARC-7, with its ten transferable rules pre-paid** (they
are in the ARC-7 EXECUTION RECORD below; read them before the first checkpoint): narrow
one-concern briefs; pinned to fresh tags; reviewers told plain text is not delivered and to
call SendMessage; every finding verified at source before applying OR rejecting; keep at
least one reviewer on a target long enough to audit its own earlier reports; budget a
diff-audit after every fix round (late-round defects are created by the fixes). Mechanical
blocks (lint, porting, pre-mapped plumbing) may run on cheaper-model subagents; ANY claim
that enters a ledger, a certificate, or a status cell gets verified by the main agent at
source regardless of who produced it.

**Standing constraints:** all commits local (public repo — never push, never `sync.sh`);
manuscript untouched (blob `205fdf5a`); frozen tags untouched; JMP reserved, T1/T2 parked;
custom axioms stay exactly `[]`; `THEOREM-MAP.md` and `STATEMENT-MANIFEST.md` update in the
same commit as each status change; never say "fully formalized".

### ARC-8 EXECUTION RECORD (append per block; the orders above stay as written)

**Block 8.0 — audit before build (done).** Tree verified at `81feb05`: `lake build` clean (3106
jobs), `AxiomAudit.lean` Census PASS, custom axioms exactly `[]`, tags through
`paperA-arc7-cp2`. The two `sorry` tokens grep finds in `Vendor/Misc.lean` are inside a block
comment (VENDOR.md already records this); no `sorry` in live code.

★★★ **The audit's real finding was about the orders, not the tree.** Block 8.2's first item —
"row 18's ℂ converse (`frame_stabilizer_is_torus`, stated ready in
`WallCertificates/differential-trio.lean`, priced a short matrix argument)" — was **a work
order for something already done.** `Necessity.offdiag_eq_zero_of_fixes_frameProj` is that exact
statement (same hypotheses, same conclusion) and had been in the tree since ARC-7. The
certificate still carried the `sorry`, and these orders were written from the certificate
instead of from the tree.

★ **TRANSFERABLE RULE (new, and it is one ring out from the grep rule).** The grep rule says an
accurate grep is evidence about a string. This one: **a certificate is evidence about the tree
as of the moment it was written, and a work order derived from a certificate inherits that
timestamp.** So the first move on opening a block is not to read its certificate — it is to
check the certificate against the tree. A certificate whose gap has closed is worse than a
prose price: it is a prose price wearing a compiler's badge. The arc's own "attack evidence must
be FROM THIS ARC" rule was aimed at exactly this and was violated by the document stating it.

**Block 8.1(a) — the compatibility chain, CLOSED.** `Necessity.n2FrameTwist_eq_of_compatible`
(plus `frameMap_eq_or_compl_of_compatible`, `eq_frameProj_of_diag_projection`, and the general
helpers `adU_mul_self`/`trace_adU`/`commute_adU`). The certificate's `frame_param_eq_of_compatible`
`sorry` is replaced by a citation of it. ★ **The price was right about size and wrong about
route:** step 3's "`M` is not a scalar, so `eigen_diagonal_fin2` puts `W e₀` on one coordinate"
is not needed at all — writing the two-level family as `e^{s₁}·𝟙 + (e^{s₀} − e^{s₁})·p₀` makes
the conjugated frame projection an *affine* function of the conjugated family, so one invertible
coefficient transfers the vanishing off-diagonal entry, and a diagonal projection of trace one
over `Fin 2` is a frame projection. **A four-step map written from the article's proof is
evidence about the article's route, not about the cheapest Lean route**; "no new mathematics and
no missing vocabulary" was the load-bearing half of that estimate and the step count was not.

**Block 8.1(b) — `prop:n2-sufficiency`'s ALGEBRAIC CORE, landed. Row 30 ABSENT → PARTIAL.** New
module `RadicalRelativity/RankTwo/Sufficiency.lean` (census manifest 149 → 150, deliberately;
root import added). `RankTwo.n2SequentialProduct t` is a `SequentialProductOn (HermitianMat (Fin
2) ℂ)` for an **arbitrary** `t : C(ℝP², ℝ)`, and
`exists_sequentialProduct_of_continuous_moduli` states it in the article's existential form with
the operation pinned: at every spectral effect the product IS the twist product with parameter
`t` at that effect's frame, where the frame is the tree's own `blochFrame (colFrame U)` — the
bridge `blochHerm_frameMap`/`blochHerm_adU_diagFamily`/`n2Tau_adU_diagFamily`, so this is
`prop:n2-sufficiency`'s operation and not a lookalike.

★★ **The mechanism is cheaper than the certificate's, and the reason generalizes.** A Hermitian
`2×2` is `α·𝟙 + n·σ` and its unordered spectral frame IS the `ℝP²` point of `n`; two such
matrices commute exactly when their axes are parallel, and that is an **entrywise identity** —
the three components of `n_a × n_b` are the `(0,0)` and `(0,1)` entries of the commutator
(`blochHerm_parallel_of_commute`). No eigenvectors, no simultaneous diagonalization, so the
Mathlib `JointEigenspace` machinery the certificate warned about pricing is not needed either.
★ The certificate's two named worries both dissolve: "compatible ⟹ same frame ⟹ same parameter"
is `n2Tau_eq_of_commute`, and the scalars cost nothing because
`HermitianMat.twistSeq_smul_one_left` shows a scalar left argument acts by scalar multiplication
*for every* parameter — so the article's convention `t_a = 0` at the scalars is **free rather
than a case to check**, which is the opposite of how the certificate priced it.
★ **Positive homogeneity was obtained from the constant-parameter S5**, not from a
functional-calculus scaling identity: apply `twistSeq_assoc_of_comm` with a scalar left factor
and both sides collapse. That removed the one place this build looked like it needed new `cfc`
lemmas. Worth remembering as a shape: **an axiom the tree already has, instantiated at a
degenerate argument, can replace a lemma about the construction.**

★★★ **WHAT REMAINS OF ROW 30 IS EXACTLY S2**, i.e. the word "norm-continuous" in its statement,
and the same clause is what blocks row 31's "satisfies all seven axioms". Route mapped this arc
and not built: `t` is bounded (ℝP² compact), `n2Tau` is continuous away from the scalars, and at
a scalar `c·𝟙` with `c > 0` the twist factor factors as a **global phase** `e^{is log c}` times
`Y_s = cfc(√x·e^{is(log x − log c)})`, whose deviation from `a^{1/2}` is `O(|s|·(log λ₊ − log λ₋))`
— so the product is continuous there because the *gap* closes, not because the parameter
converges. The global-phase factorization is the step that needs writing (it mixes the two real
`cfc`s), and it is why "S2 is a genuine estimate rather than plumbing" was the right call.

**Block 8.2 — row 18's ℂ converse: NOT WORK, already in the tree** (see 8.0). ★ **CORRECTED at
checkpoint 1: "row 18's residue is now the ℝ/ℍ/𝕆 rows only" was too strong.** The tree proved
*diagonality*; the certificate's name `frame_stabilizer_is_torus` claimed the torus, and the
article's clause asks for the **identity component `T^{n-1}`**, which is a third thing again. The
unimodularity step is now in (`Necessity.normSq_diag_eq_one_of_fixes_frameProj`), so the stabilizer
in `U(n)` is exactly `T^n`; the `T^{n-1}` packaging — the quotient by the globally-acting phase — is
stated nowhere, though its mathematical content (the action sees only phase *differences*) is
`torusU_block`. ★ **An over-strong theorem NAME is a prose price too**; it is read as the claim.
★ Row 12's "restriction direction" is **also mispriced in these orders**: `DirectSum.lean`'s own
docstring says the missing statement is that *every* product on a direct sum is of the form
`P.prod Q`, which is `prop:central`'s splitting — the half the manuscript carries as a paper proof.
It is not a cheap-sweep item.

**Block 8.2 — row 9's compatibility clause, landed.** `Necessity.compatible_of_tendsto`: `a`
compatible with every term of a convergent sequence of effects is compatible with the limit.
★ **And unlike the convergence clause it DOES need S2** — `a·b_k → a·b` is free from `seqLeftMul`'s
linearity, but `b_k·a → b·a` is *first*-argument continuity. A reader carrying the previous clause's
"S2 is not used at all" forward would be wrong. Residue: the article's order-infimum form (needs
Loewner monotone convergence, absent — grep scope recorded at the theorem) and the abstract f.d.
order-unit generality.

**Block 8.3 — the quaternionic carrier now has a product (sufficiency half).**
`HermitianMat.quatLuders : SequentialProductOn (QuatCarrier n)` plus
`quatSp_eq_quatQuadRep` (it IS `Q_{√a}`, against the tree's own `quatQuadRep`). This **falsifies
the certificate's remaining absence claim** — its grep for `SequentialProductOn (QuatCarrier` now
has a hit. ★ **Nothing new about S1–S7 was proved**: every axiom is the ambient one at `t = 0`
through the subtype coercion, and the only content is closure of the quaternionic set under
`Q_{√a}`, which was already in the tree. Recording *that* rather than eight field names is the
honest description. ★★ **The row's own statement is untouched** — `thm:quaternionic` is the
*necessity* direction (`Θ_r = id` for an arbitrary product), i.e. the transfer, still the only
honest residue. Mechanical note for the next attempt: `QuatQuadRep.lean` was a leaf that did not
reach `Hermitian/Sequential.lean`; that import was added.

**Block 8.1(b), second pass — S2 LANDED. ROW 30 IS FORMALIZED (10 → 11).** Its wall certificate's
`sorry` is discharged; that file is down to row 35's gap alone. Row 31's clause (ii) is complete in
the same stroke, since `tauModuliRP2` is one such `t`.

★★★ **The certificate's prediction about WHY S2 is hard was wrong, in the useful direction.** It
said S2 "needs the deviation to vanish fast enough at the scalars, which is a genuine estimate
rather than plumbing". There *is* one genuine analytic input — **joint** continuity of the twist
product in (parameter, matrix), via the vendored `continuous_cfc_joint` plus joint continuity of
`√x·cos(s·log x)` where the squeeze at `x = 0` is uniform in `s`. But the predicted
near-the-scalars comparison is **not needed at all**: at a scalar the product does not depend on
the parameter, so the function is *constant in the parameter* there, and joint continuity plus
compactness of `[-K,K] × effects` (Heine–Cantor) gives a modulus of continuity in the matrix that
is **uniform in the parameter**. **The parameter never has to converge.** No global-phase
factorization appears anywhere. ★ **The same scalar lemma that made the algebra free made the
analysis free** — which is a hint worth generalizing: when a construction's difficulty is localized
at a degeneracy, check first whether the *object* degenerates there too.
★ **Transferable:** a certificate can correctly identify WHICH clause is hard and still be wrong
about WHY, and the "why" is what a reader prices from.

★★★ **AND LEDGER RULE 7 FIRED AGAIN — second instance on this project.** The S2 assembly failed
with a `whnf` heartbeat timeout. Raising `maxHeartbeats` as a *diagnostic* turned it into a real
error message: `ContinuousWithinAt.comp` had solved the higher-order unification
`f x ≡ (n2Tau t a₀, a₀)` by guessing `f := Prod.mk (n2Tau t a₀)` — **arguments in the wrong slots,
not slowness.** Pinning `f` explicitly made it compile with the bump REMOVED. Had I simply raised
the limit and moved on, I would have banked a false explanation *and* left the guess in place.
**Use a heartbeat bump to read the error, never to keep it.**

**Blocks 8.1(d) and 8.1(f) — `lem:n2-descent` FORMALIZED, `cor:qubit-classification` ABSENT →
PARTIAL. Count 11 → 12 FORMALIZED / 19 PARTIAL / 5 ABSENT.** The wall certificate
`WallCertificates/prop-n2-sufficiency.lean` now has **zero gaps** — both of its rows discharged.

`RankTwo.n2QubitModuli P hS2 : C(ℝP², ℝ)` is the frame parameter of an arbitrary norm-continuous
product, descended, continuous, bounded, and representing the product. The mechanism: the
presentation map `blochFrame ∘ colFrame : U(2) → ℝP²` is continuous and surjective from a **compact**
group to a **Hausdorff** space, hence a quotient map, so continuity of the descended function reduces
to continuity of its pullback — which is row 33. ★ Boundedness then comes free from ℝP²'s
compactness rather than as a separate estimate.

★★★ **THE PRICED-BUT-UNNEEDED STEP, and this is now the arc's most repeated finding.** Row 34's
residue was "a map `U(2) → ℂP¹`, the step *same ray ⟹ the unitaries differ by a monomial matrix*,
and the quotient construction". **The monomial-matrix step is not needed at all**: what the transfer
requires is that equal rays give the same *first spectral projection*, which follows from `rankOne`'s
quadratic homogeneity plus the fact that a unitary's column is a unit vector. No statement about
monomial matrices appears in the assembly. **That is the third time this arc that a correctly-sized
price named a longer route than the one that worked** (8.1(a)'s eigenvector step; S2's global-phase
factorization; this). ★ The pattern is specific enough to act on: **these prices were all read off
the ARTICLE's proof, and the article optimizes for a human reader's narrative, not for the shortest
path through a formal library.** Reading the article to find *which* fact is needed has been
reliable; reading it to find *how* has been wrong three times out of three.

Row 35's residue is stated precisely and is **only** the "onto" half at SINGULAR effects: the
products agree at every positive-definite first argument, and agreement at rank ≤ 1 needs the
article's S2 limiting argument (singular effects are limits of positive-definite ones, both sides
continuous), which is not written. So `P.sp = (n2SequentialProduct t).sp` *as functions* is not
established, and the row must not be read as the full bijection.

**Block 8.6 groundwork — `EJA-DIVIDEND.md` WRITTEN, and the certificate sweep found a fourth
staleness.** The dividend table is at the repo root: the axiomatization **CLOSES 6 rows** (5, 6, 13,
15, 16, 17), is **PARTIAL on 3** (8, 14, 22), and does **NOTHING for 15** — including nothing for the
entire rank-two lane. So the orders' skip condition ("would do literally nothing for Paper A") does
**not** fire; the decision stands. ★ Two qualifications the table insists on: the six CLOSES rows are
all *generality-only* rows (the mathematics is already done on the concrete carrier), and rows 16/17
close only if `Theta_jordan` becomes derivable — which IS row 14, pre-registered external — so their
honest terminus is **EJA-GATED behind a named citation**, not FORMALIZED.

★★ **Certificate sweep (partial, ahead of the full 8.6 review).** `prop-n2-sufficiency.lean` and
`differential-trio.lean` now have **zero** gaps. `lem-n2-descent.lean` went from four `sorry`s to two
— and the two that remain are flagged **NOT NEEDED**: the route that actually closed row 34 never used
the diagonal/monomial step or the ray-complementation identity. ★ Note the one price in that file that
*was* exactly right: "the remaining assembly is pure topology and cheap — `U(2)` compact, `ℝP²`
Hausdorff, so a continuous surjection is closed, hence a quotient map." Recording the correct price
next to the two wrong ones is the point: **prices about TOPOLOGY/vocabulary have held; prices about
the ROUTE have not.**

★ A self-audit caught one of my own defects the same way: manifest row 34's cell still *led* with
"PARTIAL" for one commit after the row closed, because the update was appended instead of rewriting
the status word. Found by scanning the manifest's own status fields, not by re-reading the prose.
**Fourth instance of "fix the row, not just the footnote" this arc, and the first committed by the
agent that wrote the rule down.**

**CHECKPOINT 2, second reviewer (rows 34/35) — reported; all findings verified at source and
applied.** Row 34's FORMALIZED status **confirmed**: every clause of the article's sentence maps to a
Lean statement, `surjInv` is choice-independent (the pullback identity pins the value at every point,
and `frameRP2` is surjective), and "no residual line-bundle twist" is excluded by landing in the type
`C(ℝP², ℝ)` at all. The quotient-map instances are real and vendored.

★★★ **FINDING 6 — ROW 35's RESIDUE WAS WRONG, AND THE TREE ALREADY HELD THE REFUTATION.** I recorded
the residue as "the onto half at singular effects — and that is the whole residue". The onto half is
**FALSE, not unwritten**: `Necessity.badP t` is a genuine S1–S7 + S2 product equal to the twist
product *on effects* and `0` off them, so it has the **same** moduli function as
`n2SequentialProduct (const t)` and a **different** `.sp`. Now in-tree and kernel-checked:
`moduli_collide`, `badP_sp_differs`, `not_exists_moduli_of_badP`. So `product ↦ moduli` is not
injective on `SequentialProductOn` values and no bijection onto the products-as-`.sp`-functions
exists; the honest target is **products up to agreement on effects**.
★ **This is the second recorded instance of the same rule: a totalizing phrase inside a residual
claim is where the error lives.** "…and that is the whole residue" was the false clause. The rule has
now caught itself being violated by the agent that wrote it down, twice in one arc (this and the
row-34 status word).
★ **And note WHERE the counterexample came from: the tree's own `badP`**, built in an earlier arc
precisely to exploit the `IsEffect`-guarding of the axioms. The refutation was one grep away from
anyone who asked "does the tree contain a product that is not of this form?" — which is the question
a surjectivity claim should always trigger.

★ **FINDING 7 — a citation that did not say what it was cited for.** The row claimed "the products
are proved to agree at every positive-definite first argument (`sp_eq_twistSeq_n2QubitModuli`)", but
that theorem equates `P.sp` with the **constant-parameter** `HermitianMat.twistSeq`, not with `n2Sp`.
Two-line bridge added as `sp_eq_n2Sp_of_moduli`. Reading a cited theorem's statement rather than its
name is the same discipline as the grep rule, applied to one's own citations.

★ **FINDING 8 — certificate/README staleness, third and fourth instances.**
`WallCertificates/lem-n2-descent.lean`'s header still said "what is missing is the DESCENT ITSELF as
a constructed object", and `WallCertificates/README.md` still indexed it as a live price for row 34.
Both annotated. The README now also records that `prop-n2-sufficiency.lean`'s row-35 gap statement was
**weaker than the row** — discharging it did not close row 35 — which is the under-specified-price
defect kind, and is the reason "zero gaps" and "row closed" must never be read as the same claim.

★ **FINDING 9 — my `git add -A` swept a reviewer's probe in again** (`ColdRevCollide.lean`, second
occurrence in one arc). The probe's content is now proper in-tree theorems and the file is deleted;
`Scratch*.lean` and `ColdRev*.lean` are gitignored. **Two identical hygiene failures in one arc means
the habit, not the incident, is the defect.**

### Block 8.6 — DRY PASS ROUND 7 (post-refutation-review) WENT DRY; ARC-8's TERMINAL CONDITION IS MET

Re-run after the eight refutation-review fixes, because those fixes touched six of the seven
certificates and a dry round before them would not have counted.

**Round 7 moved nothing.** Build errors 0 (using the corrected recipe —
`grep -E ': error' | grep -vc '^warning:'`; the naive count reports 2 on a green tree); census PASS at
150 modules, custom axioms `[]`; all seven certificates compile, and **every one's `sorry`-term count
now equals its `sorry`-declaration count** — the two apparent discrepancies were prose mentions of the
word inside docstrings, checked line by line, so no `sorry` hides inside a statement anywhere;
no certificate imported from `RadicalRelativity/`; manifest counts re-derived from the table
(12 FORMALIZED / 3 EJA-GATED / 16 PARTIAL / 5 ABSENT = 36); terminal-state ledger re-derived from its
own cells (12 + 6 + 3 + 15 = 36); no stray tracked files; working tree clean.

**TERMINAL CONDITION — all four requirements now met:**
1. every one of the 36 rows is in one of the four terminal states (ledger above, re-derived);
2. `EJA-DIVIDEND.md` exists and states per row what the axiomatization would buy — and was itself
   corrected twice this arc (a refuted residue for row 35, then the CLOSES column after rows 5/6/15
   were withdrawn);
3. the dry pass has produced a round with zero movement (round 7; rounds 2–6 each moved something,
   and round 6's dryness was invalidated by the review that followed it);
4. the certificate-refutation review has been applied to every standing certificate, with all eight
   findings verified at source and fixed.

★★ **The honest summary of this arc's last day: the review process found more defects in my own
two-day-old work than in the two arcs before it, and the two worst were FALSE statements inside the
certificate written to prevent false statements.** The count that matters is not 12/6/3/15 — it is
that eight defects were found by asking, mechanically and repeatedly, "does this statement say what
its prose says, and is its complement really empty?"

### CERTIFICATE-REFUTATION REVIEW (tag `paperA-arc8-cp5`; one cold reviewer, all seven certificates)

**Eight confirmed defects, seven of them in work I did in the last two days, two of them FALSE
statements in the certificate written to prevent exactly this.** All verified at source and fixed.

★★★ **1. `gate_E2_peirce` was FALSE — and SELF-DEFEATING.** Its `J2`/`ScalarOn` were **free
universally-quantified predicate variables**, so instantiating both at `fun _ _ _ => True` made it
"every two elements of every JB-premised `ComparisonSetup` operator-commute" — false on `H_n(𝕜)`
(the reviewer compiled it via the tree's own `opCommute_iff_commuteG`). It never used `i ≠ j`.
Discharging it as written would have proved that **no JB-premised `ComparisonSetup` exists on the
intended carriers**, refuting the axiomatization programme the file exists to price. Four of the six
rows leaned on it. **RESTATED** as producing the three `CoalescenceSetup` FK fields, with the first two
conjuncts pinning `ScalarOn`/`J2` from below so `False` cannot cheat it.
★ **RULE: a free predicate variable in a gap statement is an unconstrained hypothesis, and an
unconstrained hypothesis is where vacuity and falsity both hide.** In the field it was meant to
reproduce, those predicates are *fields constrained by two other fields*; demoting them to variables
silently deleted the constraints.

★★ **2. `gate_E1_spectral` was FALSE as stated** — no finite-dimensionality. `J = ℝ[X]` with polynomial
multiplication satisfies every `ComparisonSetup` field and all three `JBPremises`, yet is a domain, so
only `0, 1` are idempotent and `x = X` has no spectral resolution. **FIXED** with
`[FiniteDimensional ℝ J]`. ★ **RULE: an "at the article's generality" statement must carry the
article's STANDING hypotheses, not only its premises.** I transcribed the three premises the interface
docstring lists and forgot that f.d. is standing for EJAs.

★★★ **3. Rows 5, 6, 15 are NOT EJA-GATED — claim WITHDRAWN the same day it was made.** Each has a
non-EJA residue: row 5's ball clause needs the order-unit norm; row 6's clause (ii) is **already
abstract** (`SequentialProductOn.sp_smul_left`) and I had cited `twistSeq_smul_left`, a theorem about
*one product*, then assigned the row to the Jordan spectral theorem on that misreading; row 15's
`Stab(F)°` clause needs identity-component vocabulary. ★★ **One error made three times: I classified
each row by its BIGGEST residue and let that stand for its WHOLE residue. EJA-GATED is a claim about
the complement, and a claim about a complement cannot be checked by inspecting the largest item in
it.** Same shape as row 35's "and that is the whole residue".

★★ **4. The load-bearing (E3) claim was overstated and is now OPEN.** `gate_E3_theta_jordan` assumes
`Φ` **linear**, so it is the classical Koecher/Alfsen–Shultz theorem — which `Interface.lean` itself
calls "classical corroboration" and the tree discharges concretely — not vIR's JB-generality version.
So "rows 16/17 cannot reach FORMALIZED by axiomatization alone" does **not** follow: a Mathlib-grade
f.d. EJA layer could discharge it in-tree. ★ Also flagged, not guessed: `external-rows.md` names row
14's source "van Ittersum–Reijnders" while `Interface.lean` names it "van Imhoff–Roelands" — **two
names for the theorem that terminates two rows.**

★★ **5. `quaternionic_luders` was VACUOUS** — its conclusion ended `… ∨ True`, provable by
`Or.inr trivial` with **every hypothesis deleted**. **RESTATED** as the row's actual content,
`P.sp a b = HermitianMat.quatSp a b`, which is expressible only because `quatLuders` landed this arc.
★★ **A `∨ True` is a `True`** — the directory's already-retracted placeholder defect, wearing a
disjunction. ★ And I refreshed that file's header earlier in this arc **without reading its gap
statement**: updating prose is not re-attacking a gap.

★★ **6. `orientation_complex_structure` was FALSE for the second time** — with `q p` arbitrary
Hermitian, `q = 𝟙`, `p = (1/2)•𝟙` makes the coherence hypothesis hold for *every* `x` while `J ≡ 0`;
the reviewer compiled it at the article's own `N = 3`. **FIXED** by hypothesizing orthogonal
idempotents. ★★ **The prose knew `q, p` were frame projections both times; the Lean never said so. A
hypothesis stated only in a docstring is not a hypothesis.** ★ Same declaration also had `by sorry`
**inside its statement** — the defect `prop-n2-sufficiency.lean` repaired in itself a day earlier,
surviving one file over; now the proved lemma `orientation_isHermitian`.

★ **7. `prop-n2-sufficiency.lean`'s standing absence claim is now FALSE and went unretracted for a
day** — `n2SequentialProduct` IS the "frame-dependent structure for a general `t`", as that file's own
header announces three screens up. ★ **When a row closes, its certificate's ABSENCE CLAIMS are the
part most likely to survive stale, because the header gets rewritten and the evidence block does not.**

★ **8. `differential-trio.lean`'s summary still asserted row 18's converse was unwritten**, contradicting
its own later retraction — "fix the row, not just the footnote", in the file that teaches the rule.
Also fixed: `abstract-tier.lean`'s `normality` is under-hypothesized (no f.d./Archimedean) while the
*same file* flags exactly that for its neighbour twelve lines below; and its row-3 block promised an
"equivalence" that `badP` proves cannot exist (extension is not unique).

★ **Reviewer correction to my own brief, worth keeping:** my instruction to count build errors with
`grep -cE ': error'` **reports 2 on a green tree** — two style-linter *warnings* whose message text
contains `error:`. Use `grep -E ': error' | grep -vc '^warning:'`. A verification recipe that
false-positives is the thing the README already fixed once for the import grep.

**Terminal-state ledger corrected: 12 FORMALIZED + 6 EXTERNAL + 3 EJA-GATED + 15 WALL-CERTIFIED = 36.**
Of twelve `sorry`-bearing declarations, the reviewer judged exactly two to be live, sound, row-moving
gap statements before these fixes (`n2_necessity_theta_level`, `adjBlock_connected` — both written
this arc, both confirmed NO DEFECT, including an independent re-derivation of the phase convention with
no sign or factor error).

### Block 8.6 — DRY PASS: ROUND 6 WENT DRY (2026-08-10)

Rounds 2–5 each moved something; **round 6 moved nothing.** Round 6 is the consolidated mechanical
pass: build errors 0; census PASS at 150 modules with custom axioms `[]`; all seven certificates
compile with their expected `sorry` counts (abstract-tier 2, differential-trio 0, eja-gated 3,
frame-geometry 4, lem-n2-descent 2, prop-n2-sufficiency 0, thm-quaternionic 1); **zero certificates
imported from `RadicalRelativity/`**; every recorded absence grep re-executed and still holding;
manifest counts re-derived from the table itself (12/6/13/5 = 36); no stray tracked files; working tree
clean.

**What the earlier rounds moved, so "went dry" is not read as "was always dry":**
* round 2 — caught my own row-29 gap statement being **FALSE**: it applied `Θ_a` to the *standard*
  coherence block while taking `a = Ad_U(diagFamily r)`, mixing frame indices. ★ The test that caught
  it was not a counterexample hunt but asking **"which frame is each object in this statement indexed
  by?"** — two of three were indexed by `U` and one was not. That is the specific shape to look for
  here, and it is the same shape as the retracted `frame_param_eq_of_compatible`.
* round 3 — caught row 9's recorded grep scope **undercounting** (`iInf|⨅` has ~38 non-comment hits, not
  the two I described). The substantive absence held: exactly one hit touches `HermitianMat`, and it is
  an infimum over real *eigenvalues*, not over the Loewner order. ★ **A recorded scope must be the
  count plus the classification, or it is a recollection.**
* round 4 — two findings. (a) `RadicalRelativity/Necessity/BlockRotation.lean` **EXISTS**, and row 26's
  residue is phrased "rank-two block rotations", so the next reader would have found it and declared an
  eleventh false absence claim. It is not one: that file is the rotation *acting on* a Peirce block
  (`chiEntryCLM`, `chiEntry_is_rotation`), not a factorization *into* block rotations. Disarmed in the
  certificate and in `EJA-DIVIDEND.md`. ★ **An absence claim phrased in the same words as an existing
  filename invites its own refutation.** (b) `EJA-DIVIDEND.md` was itself carrying row 35's
  **already-refuted** residue and a stale header count.
* round 5 — audited `THEOREM-MAP.md` for non-existent identifiers and stale "NOT proved" claims:
  **clean** (the 11 flagged names are Mathlib, structure fields, or the properly-marked eliminated
  axiom).

★ Honest scope of the claim: round 6 is dry on every *mechanical* check across all 36 rows, and the
substantive "is any residue now closable" question was worked in rounds 2–5. The remaining gate is the
certificate-refutation review over every standing certificate, which is out with a cold reviewer.

### Block 8.6 — ALL 36 ROWS NOW IN A TERMINAL STATE (2026-08-10)

`STATEMENT-MANIFEST.md` carries a TERMINAL-STATE LEDGER: **12 FORMALIZED + 6 EXTERNAL + 6 EJA-GATED +
12 WALL-CERTIFIED-this-arc = 36.** Status words in the table stay FORMALIZED/PARTIAL/ABSENT because the
census depends on that taxonomy; the terminal state is recorded separately, per the row-20 rule.

`WallCertificates/eja-gated.lean` (new) gates rows 5, 6, 13, 15, 16, 17 on (E1)/(E2)/(E3), one `sorry`
per gate. ★★ **(E3) IS row 14, pre-registered external — so rows 16/17 cannot reach FORMALIZED by
axiomatization work at all.** `abstract-tier.lean` and `frame-geometry.lean` were refreshed with
this-arc evidence for rows 3, 8, 9, 12 and 22, 26, 29, 31, 36.

★★ **Two vacuous gaps became real ones, which is the refutation review doing its job on this
directory's own placeholders.** Row 29(b)'s `theorem … : True` is replaced by the Θ-level conclusion
itself (`Necessity.theta` + `blockHerm` + `n2FrameTwist` — **no vocabulary wall existed; the sentence
was never written**, the same failure mode already retracted at row 18). Row 26's connectivity is
**stated for the first time**, in `AdjBlock` + `Relation.ReflTransGen`, again with no new vocabulary —
and its ingredient re-confirmed absent from the tree AND from Mathlib.

★ **Two rows were deliberately NOT restated, and the refusals are findings.** Row 36(i): the obvious
restatement (exchange = conjugation by a permutation matrix) would be **inert a second time**, because
conjugation commutes with the twist so every twist product is covariant under it — so the article's
clause must carry an anti-linear ingredient, and that needs `main.tex` at source. Row 22: the last
attempt to sidestep the missing carrier produced a FALSE statement. **A row already broken once by a
plausible guess does not get a second guess.**

★ **Row 8 is blocked on a missing DEFINITION from vdW, not on Lean** — a different kind of blocker from
every other row here, and the next action on it is a reading task. **Row 12's refutation attempt
FAILED**, and informatively: unlike row 35, the unit axiom reaches into both summands, so no totality
trick refutes it — the row is genuinely open in the positive direction.

★★★ **A PROCESS DEFECT OF MINE, caught by its own inconsistency.** Two earlier certificate edits used
`str.replace` **without an assert** and silently no-op'd, so `prop-n2-sufficiency.lean` kept a stale
"GAP … cannot be written down until row 34's object exists" docstring *and* lacked the `badP` evidence —
while the manifest's new terminal-state ledger already cited that certificate for row 35. I committed
that inconsistency and then caught it by grepping the file for `badP`. **RULE: an edit that isn't
asserted isn't an edit. A no-op `replace` is the textual form of the empty-glob failure the project
already has a rule about** ("verify the verifier saw data") — it exits successfully and reads as done.

**Still owed:** the dry pass repeated until a full round produces zero movement (rounds so far have all
moved something), and the certificate-refutation review applied to every standing certificate.

### Block 8.6 — DRY PASS, first round (partial; the full round is still owed)

Method: for each non-FORMALIZED row whose residue names a concrete object, run the declaration-list
first move on the file that object would live in, then re-check the row's absence claim against the
tree rather than against its own prose. Results so far:

* **row 26 `lem:frame-connectivity` — absence CONFIRMED, twice over.** `Givens`/`jacobiRot`/
  `blockRotation` over `RadicalRelativity/`: one hit, and it is the prose sentence in
  `FrameConstancy.lean` that records the gap. `Givens` over Mathlib v4.28.0: **zero hits.** So this
  really is absent from the tree AND from Mathlib, and the row's "standalone contribution" framing is
  right.
* **row 22 `lem:orientation` — absence CONFIRMED.** No declaration in `Necessity/` matches
  `coheren|orientat|J_q`. The coherence space is not a carrier anywhere.
* **row 36(i) `cor:selectors` — the "different machinery" claim CONFIRMED, and it survived a real
  near-miss.** `Necessity.theta_conj_exchange` exists and is named "exchange", so the obvious grep
  finds it — but it is **vdW 5.7(1)** (Θ commutes with Lüders conjugation at a commuting base point),
  not the frame-atom exchange automorphism clause (i) needs. Reading the statement rather than the
  name is what settled it. ★ This is the near-miss the grep rule exists for, run in the *other*
  direction: an accurate grep found a real declaration with the right word in its name and the wrong
  content.
* **rows 3, 12, 18, 20, 30, 34, 35 — already re-checked earlier this arc** (see above).

★★ **One thing the dry pass found that it should NOT fix by guessing.** `frame-geometry.lean`'s
`exists_peirce_exchange` is correctly flagged VACUOUS and its own instruction is to restate with the
coherence-block action as an explicit conclusion. **I stopped short of restating it**, because the
obvious restatement is wrong in a way that matters: if the exchange is taken to be conjugation by a
permutation matrix, then *every* twist product is covariant under it (conjugation commutes with the
twist), so covariance would carry no information and the restated gap would be **inert for a second
time**. The article's clause (i) must therefore involve an anti-linear ingredient — as clause (iii)'s
transpose did — and getting that right requires reading `main.tex`'s definition of Peirce exchange at
source, not inferring it. **Recorded as the next action on row 36 rather than executed, precisely
because this row has already been broken once by a plausible guess.**

### CHECKPOINT 2 (tag `paperA-arc8-cp4`, two cold reviewers, one concern each)

Reviewer on S2 reported; both of its findings verified at source and **applied**. Reviewer on rows
34/35 still out at the time of writing.

★★★ **FINDING 4 — the non-collapse theorems separated the wrong things.** Checkpoint 1's
`exists_n2Sp_tau_ne_twistSeq` and friends are true, but their separating witness takes
`δ = π/(t₁ − t₂)`, which is **positive whenever `t₁ > t₂`**, so the first argument has an eigenvalue
`e^δ > 1` and is **not an effect**. Since S1–S7 and the article's operation constrain effects only,
those statements separate the *total extensions*, not the operations — and the reading they exist to
support ("a genuinely frame-dependent product satisfies all seven axioms") needs the effects.
**FIXED**: `not_forall_effects_eq_twistSeq` / `not_forall_effects_tau_eq_twistSeq`, which go through
`n2FrameTwist_unique_param` (whose quantifiers are already `r ≤ 0` and `IsEffect b`) and never touch
an entry probe. ★ **RULE: a separation theorem is only as strong as the class its witnesses live in.**
An `∃ a b` with no `IsEffect` guard *reads* as a separation of operations and *is* a separation of
extensions. This one is worth generalizing beyond separations: any existential witness in this project
should be checked against the class the surrounding theory quantifies over.

★★ **FINDING 5 — S2 was proved in the wrong norm's topology.** The tree's `FirstArgContinuous` is the
carried Frobenius topology; the article's S2 is the **order-unit** norm. The bridge was already
generic in the tree (`Necessity.firstArgContinuousOu_iff`, `Necessity/OrderUnitS2.lean`) and simply
was not connected to the rank-two product. **FIXED**: `n2SequentialProduct_firstArgContinuousOu`.
★ Note the shape: this is not a hole in the proof, it is a hole in the *claim* — "norm-continuous"
was true in a norm the row never named. A recorded nit, not fixed: `PaperA/AuditPins.lean` freezes the
*class-side* S2 predicate, not the `SequentialProductOn` spelling row 30 proves; the two bodies were
read and are identical, but the pin does not cover this spelling.

★ **FINDING 10 — my own hygiene defect.** `git add -A` swept two reviewers' scratch files into the
repo at `d6768b7`. Removed, and `Scratch*.lean` is now in `.gitignore`. A blanket `add -A` in a repo
that concurrent agents are writing scratch files into is a commit of other people's work product.

### CHECKPOINT 1 (tag `paperA-arc8-cp1`, two cold reviewers, one concern each)

Both verified the build independently (0 errors over full output, Census PASS, no `sorryAx`), and
both returned findings I verified at source before acting. Net: **the two "gap closed" claims are
true as stated, and both were FRAMED wrong.** The framing errors were the valuable part.

★★★ **FINDING 1 — a closed gap that was not on the row's path.** `n2FrameTwist_eq_of_compatible`
(block 8.1(a)) has **zero consumers in the tree**, and row 30 was closed by a *different*,
**P-free** mechanism (`RankTwo.n2Tau_eq_of_commute`). It could not have been otherwise: the
certificate's form is quantified over a `SequentialProductOn P`, and the compatibility facts are
needed *before* the structure is assembled, so instantiating at `P := n2SequentialProduct t` is
circular. Verified: `grep -rn n2FrameTwist_eq_of_compatible` finds only its own docstring, its
statement, and the certificate. ★ **RULE: "the certificate's named gap is closed" and "the row
moved" are two different claims, and a certificate must say which it is asserting.**
`n2FrameTwist_eq_of_compatible` is a *necessity*-side lemma (it extracts from an arbitrary product —
rows 29/34/35) that this certificate had mis-filed under a *sufficiency* row. My own block-8.1(a)
headline, "THE CHAIN, CLOSED", inherited the mis-filing.

★★★ **FINDING 2 — two rows in two encodings the tree never linked read as one result.** Row 30
certified that the axioms hold for arbitrary `t`; row 31 certified "frame dependence is real"
(`sp_luders_ne_unit_twist`) — but that theorem is about the **entry-level** family
`MasterTheorem.RankTwo.sp = Fdiag·b·Fdiagᴴ`, and no theorem identified it with
`HermitianMat.twistSeq`. So a reader combining the rows would conclude the qubit's escape from
`mthm:master` was machine-checked while the two halves did not meet. **CLOSED, not merely
recorded**: `RankTwo.exists_twistSeq_diagFamily_ne` (the twist product separates its parameter —
pick the spectral gap so the phase difference is exactly `π`, so no `2π` ambiguity survives),
`RankTwo.surjective_colFrame` (every `ℂP¹` point is a unitary's first-column ray, via
`Necessity.frameU`), hence `exists_n2Sp_ne_twistSeq_of_nonconstant` and
`exists_n2Sp_tau_ne_twistSeq`. ★ **RULE: when two rows are about the same mathematics in two
encodings, the missing theorem is the identification, and its absence is invisible to both rows'
status cells.** Scope kept honest: this is "not *literally* a constant twist"; the article's
`(Φ, t)`-conjugation form is stronger and is not proved.

★★★ **FINDING 3 — a status cell went on issuing a retracted work order.** `STATEMENT-MANIFEST.md`
row 18 still instructed the reader that the ℂ converse was unwritten and "writable today",
**citing a grep as its evidence**, for a theorem in the tree since ARC-7 — while `LEDGER.md` had
already retracted the corresponding order. This is "fix the row, not just the footnote" in its
purest form, and it is how the staleness got into these orders in the first place (block 8.2 was
written from that row). ★ **RULE: a status cell that carries a grep as its absence evidence must be
re-checked against the tree, not against its own prose.**

★ Minor, applied: row 30's pinning is on the **open posdef cone** (silent at singular effects and
non-psd first arguments); the frame identification is proved at posdef effects with **distinct**
eigenvalues; and `blochFrame` appears nowhere in `Necessity/`, so nothing ties row 30's frame
coordinate to row 29's `n2FrameTwist` — both use column 0, but that agreement is prose. All three
now recorded in the row. Row 31 updated in the same commit (clause (ii) gets S1, S3–S7; clause (iii)
gets the `twistSeq`-encoding form).

---

## ★★★ ARC-7 ORDERS (2026-08-09, Fable design pass — the interior-closure campaign). **EXECUTED 2026-08-09 — terminal condition met (see EXECUTION RECORD); superseded as campaign SSOT by ARC-8 above; the certificate spec and lessons remain binding.**

**This arc IS "finish it."** Not a ladder of targets — a terminal condition over the whole
denominator. Previous arcs came in at 1–3 hours because a ladder plus prose banking made
"done" cheap: every listed rung either closed or banked a paragraph, and the goal was
satisfied. This arc removes both exits. The denominator is all 36 rows of
`STATEMENT-MANIFEST.md` (pinned to blob `205fdf5a` — never re-pin), and banking now costs a
compiling artifact, not a sentence.

**TERMINAL CONDITION (the whole goal; nothing else ends the arc):** every one of the 36
rows is in exactly one of three states —

1. **FORMALIZED** at the article's own generality, no located hypothesis (the standing bar);
2. **EXTERNAL by pre-registration** — exactly these six, decided in ARC-5/6 and not
   re-litigated: `thm:vdw1`, `prop:bridge` (cited), `mthm:master`/`mthm:omnibus`
   one-theorem-over-abstract-EJA form (JvNW, the one permanent import), `prop:theta` at
   vIR's JB generality, `thm:albert` (Albert M2). For these six the terminal state is
   "best interior form reached, external delta named in the row" — which the manifest
   already records; improving their interior form is in scope, closing them is not;
3. **WALL-CERTIFIED this arc** — see the certificate spec below. A prose price with no
   certificate does not terminate a row.

— AND the final dry pass (rung 7.5) has run over every non-FORMALIZED row and produced
zero movement, AND all checkpoint reviews (protocol below) have reported and their findings
are verified at source and applied. Do not stop at block boundaries; do not stop to report;
the count is an OUTPUT, not a quota (8/19/9 at these orders; interior ceiling 30, realistic
26–28; 22 rows are in play = 36 − 8 FORMALIZED − 6 external).

**WALL CERTIFICATES (the new banking currency).** This project's recorded failure mode is
that prices decay: five false absence claims in two arcs, two walls mispriced CHEAP, four
false "Mathlib lacks X". A banked wall is therefore no longer prose. A certificate is a
file `WallCertificates/<row>.lean` at the repo root — **never imported from
`RadicalRelativity/`**, so `lake build` and the census never see it — that (a) states the
missing step in Lean at the article's generality with `sorry` for exactly the missing
part, (b) compiles under `lake env lean` from the repo root, and (c) carries a header
comment: date, scope of every absence claim in it, and attack evidence (what was tried,
what failed, at which commit). Where the wall is the *vocabulary* itself (no Lean statement
is even statable), the certificate states the nearest statable approximation and names the
missing vocabulary — that a statement cannot be written down is itself the strongest
evidence of depth, and it gets recorded, not asserted. Certificates are inputs to the
rung-7.5 refutation review: reviewers attack the certificates the way this arc's reviews
attacked absence claims.

**THE BLOCKS (in order; the wall protocol = write the certificate and continue):**

* **7.0 Reviewer-first on the readout block.** Before building on it, spawn ONE narrow
  reviewer (protocol below) on `n2Readout_eq`'s `hb`/`hx` and the readout chain in
  `Necessity/FrameConstancy.lean` — the one load-bearing block that has never had an
  outside read (ARC-6's rank-two reviewer went idle). Runs in parallel with 7.1; do not
  wait for it to start building, but its findings gate the 7.1 checkpoint. While there:
  remove the redundant `hU`/`hU'` pair still on `adU_isEffect` (`ConjTransport.lean:117`
  — same redundancy already removed from `adU_conj_twistSeq`), and take the two
  pre-existing lint warnings recorded in the ARC-6 lint sweep (now in-scope: we are in
  those files).
* **7.1 The rank-two lane to the corollary — the crown.** In order:
  (a) **`lem:n2-bounded` assembly** — the four steps itemized in manifest row 32, with the
  reviewer's cheaper legs pre-loaded: S2 at the single point `a = 𝟙` gives δ uniform in U
  free (`‖Ad_U(basePt x) − 𝟙‖ = |e^{−x} − 1|` by Frobenius conj-invariance), and the
  `(e₀+ie₁)/√2` probe gives an explicit `1/(2√2)` weight bound — no compactness needed on
  either leg. Step (i), stripping the modulus, is the genuinely analytic one: triangle
  inequality plus a δ small enough that `1 − √(e^{−δ})` eats only part of the budget.
  (b) **`lem:n2-continuity` via the arg route, NOT the article's SO(3) Log** — pre-loaded
  design: with `M` from (a), fix `δ < π/M`; the readout gives `U ↦ exp(−i·t̃(U)·δ)`
  continuous (already proved at fixed first argument via `continuousOn_n2Readout`), and
  `|t̃(U)·δ| ≤ Mδ < π` keeps the phase on the unit circle minus `{−1}`, where
  `Complex.arg` is continuous and `arg (exp (iθ)) = θ`; so `t̃ = −arg(phase)/δ` is
  continuous as a composition. Row 33's recorded route-refutations were all about routes
  WITHOUT boundedness; with (a) in hand this is the article's order at a fraction of its
  price. If the arg route walls, the SO(3) trace formula is the fallback, certificate on
  resistance.
  (c) **`lem:n2-descent`'s continuity clause** — build the actual `ℝP² → ℝ` function for an
  arbitrary product by quotient lifting; the vocabulary (`RP2`, `QubitFrame`, `tauModuli`)
  exists in `RankTwo/` for the concrete element and the invariances
  (`n2FrameTwist_mul_diagonal_swap`, `n2FrameTwist_reverse`) are proved.
  (d) **`prop:n2-sufficiency`** — generalize `lem:twist-sufficiency`'s constant-`t`
  machinery to continuous `t : ℝP² → ℝ`, reusing the τ-family partials banked under
  `thm:qubit-boundary`. This is the block's biggest single build: all seven axioms again,
  with the frame-dependent parameter.
  (e) **`cor:qubit-classification`** — assemble the bijection from (a)–(d).
  (f) **`thm:qubit-boundary`'s bundled S1–S7 clause** as an instantiation of (d), plus the
  unimodular cocycle subcases.
  (g) **`prop:n2-necessity` gap (b)** — the Θ-level vs product-level equivalence, closing
  the row. ★ CHECKPOINT after (e).
* **7.2 The differential/necessity sweep.** `lem:coalescence` (identify the in-tree shadow
  WITH the article's differential — the identification is the open part);
  `prop:stabilizers` (construct the representation from Θ, ℂ row first; ℝ/ℍ/𝕆 rows
  certificate-bankable); `lem:frame-fix` general statement; `lem:orientation` (concrete
  `H_n(ℂ)` work throughout — the complex structure `J_{q,k}`, splitting-independence,
  commutation, the `Ad_{a^{it}}` formula); `lem:frame-connectivity` via a Givens/Jacobi
  factorization into rank-two block rotations (the three Householder factors do NOT
  suffice — `AdjBlock` is strictly finer than `AdjAxis`).
* **7.3 The abstract/vdW tier sweep.** `lem:homog`(i) abstract port (`seqLeftMul` exists on
  the carrier; port the order-bounded-extension argument to `OrderUnitSpace` +
  `IsArchimedean`, same pattern as the (ii) ladder — rung 6.3 proved this tier is cheaper
  than priced); `prop:pseudo-transfer` to the article's `a·a⁻¹ = 𝟙` form by dividing out
  `pseudoInvCoef` through `spCone` (the tool now exists — this is why `lem:cone-ext` was
  built); `lem:span`'s ball clause (ε-ball about `½𝟙` in `ouNorm`, where the Archimedean
  `Prop` and `Necessity/OrderUnitS2.lean`'s `ouNorm` apparatus already live) and Peirce
  clause (needs `J₂(q)` as an order unit space on the concrete carrier); `lem:normality`
  (f.d. + S1 + S2 ⟹ vdW-normal; monotone convergence in f.d. order topology);
  `prop:central`'s summand inheritance + converse assembly; `lem:simple-bridge` clause (ii)
  on the concrete carrier (Mathlib's spectral theorem); `def:sp` restated clause-for-clause
  with an equivalence proof to `SequentialProductOn` (moves the definition row);
  `cor:selectors`(iii) assembly — `twistFactor (aᵀ)(−t) = conj (twistFactor a t)` by
  cos-even/sin-odd, then the `∃!` step that closed clause (ii); then clause (i).
  ★ CHECKPOINT after this block.
* **7.4 The ℍ row — the big build, no longer a stretch.** `thm:quaternionic` via
  `H_n(ℍ) ↪ H_{2n}(ℂ)` as the fixed points of a conjugate-linear involution (the `Gen`
  layer is impossible at ℍ — `RCLike` is commutative and two-dimensional — so this route
  is forced, and it was priced, not attempted, in ARC-6). Build the carrier and the
  embedding first; whether the classification transfers through the embedding or the
  stabilizer-coupling route is cheaper is decided by what compiles, not in advance.
  Quaternionic Wigner may fall to the `RealWigner` rank-one technique. Certificate on
  resistance — but the certificate must contain the embedding, not just name it.
* **7.5 The dry pass — the arc's exit gate.** Re-run the 6.0-style audit over EVERY row not
  FORMALIZED: grep the whole tree for ingredients (absence claims scoped and dated), run
  the STRONG inert-hypothesis test (disprove the hypothesis-free statement, not fail to
  prove it) on the nearest declaration, and either move the row or write/refresh its
  certificate. Then the certificate-refutation review: reviewers attack the certificates'
  absence claims and prices. Zero movement + reviews applied = terminal.

**REVIEW PROTOCOL (four checkpoints minimum: 7.0, after 7.1(e), after 7.3, and 7.5's
refutation pass).** Everything ARC-6 learned, pre-paid: narrow one-concern briefs sized to
~25 tool calls — a whole-arc brief failed twice; tell every reviewer explicitly that plain
text is NOT delivered and it must call `SendMessage`; pin each review to a fresh tag
(`paperA-arc7-cpN`) and tell the reviewer the tag — a reviewer on a stale checkout reports
already-fixed defects as live; verify every finding at source before applying OR rejecting
(reviewers have been confidently wrong in both directions, and so have I); check
Mathlib-scoped claims against the vendored tree before accepting them; a silent channel is
not a dead channel — "no report yet" is never written as "failed"; and audit your own
corrections — late-round defects are created by the fixes, so after applying a round of
findings, diff-audit the round itself.

**Pre-paid field hazards (from the ARC-6 record; details below):** a `whnf` heartbeat
timeout is about the unification path — prove an explicit lambda and transfer via `congr`,
never unify a composite against a `def`'s unfolding; grep before any "Mathlib lacks X"
(wrong four times); `decide` fails on free variables — standalone `have := by decide` then
`rcases`; `lake` commands from the repo root by absolute path; over-correcting under review
is its own error mode — verify the correction too; fix the row, not just the footnote —
grep every summary instance of a changed claim.

**Per-commit gates, unchanged:** `lake build` green; census custom axioms exactly `[]`;
`THEOREM-MAP.md` + `STATEMENT-MANIFEST.md` in the same commit as any status change; single-
sentence commit messages; all commits LOCAL (repo is public — never push, never `sync.sh`);
manuscript untouched (blob `205fdf5a` must survive the arc); everything outward
Bryan-gated. Never say "fully formalized".

### ARC-7 EXECUTION RECORD (append per block; the orders above stay as written)

**7.0 reviewer-first on the readout block — DELIVERED, and it paid for itself immediately.** One
narrow reviewer, pinned to tag `paperA-arc7-cp0` (`d0f1312`), briefed on four concerns and told
explicitly that plain text is not delivered and it must call `SendMessage`. It reported. Findings,
each verified at source before applying **or** rejecting:

| Finding | Disposition |
| --- | --- |
| ★★ **`n2Readout_eq`'s `hb` and `hx` are BOTH load-bearing in the STRONG form** — not "reasoned", *disproved without them*, with compiled witnesses and axioms `[propext, Classical.choice, Quot.sound]`. The vehicle is `badP`: the twist product on effects, `0` off them. It is a genuine S1–S7+S2 product because **every** `SequentialProductOn` field guards all arguments with `IsEffect` and `FirstArgContinuous` is a `ContinuousOn` over the effects, so off-effect values are unconstrained. | **ADOPTED AND BANKED IN-TREE** (`badSp`, `badP`, `badP_S2`, `hb_is_load_bearing`, `hx_is_load_bearing`, `FrameConstancy.lean` section `EffectHypothesisWitness`). ★ This **discharges the whole "four hypotheses needing a bespoke product" debt**, not just two of them: one construction certifies *any* hypothesis whose only job is to place an argument in the effect set. The debt had stood since ARC-6 with a correct diagnosis of why it was hard and no route; the route was "the axioms say nothing off the effect set", which was in the class docstring the whole time. |
| **A sign check that bypasses `twistSeq_diagFamily_entry`.** `readout_direct` was known non-independent (both chains rewrite that lemma); this one goes through `twistFactor_diagFamily_diagonal` instead. | **ADOPTED** as `sign_check`. The sign is now guarded *below* the entry lemma, which `readout_direct` could not do. |
| **STALE DOCSTRING** at `n2Comb_eq`: "that upgrade is not yet assembled", of the weight-positivity upgrade — which is assembled sixty lines below (`n2Weight_pos`, `exists_n2Weight_lower_bound`). | **FIXED.** ★ This is the **second** instance in this one file of telling a top-down reader that a theorem beneath them does not exist. The transferable rule: **a docstring that asserts an absence has to be re-read every time the file grows**, because the file grows underneath it. |
| `n2Weight_pos`'s one-line docstring ("the two-effect weight never vanishes") reads as a claim about an arbitrary pair; it holds for a *fixed* pair (`U` is arbitrary, the pair is not). | **FIXED** — scope now in the docstring, with why the fixed pair is essential. |
| **Step (iii) of the banked plan — "assemble continuity of `n2Comb`" — is UNNECESSARY.** The argument needs only a two-point comparison against `x = 0`, which the one-point S2 argument gives directly; joint continuity does not yield U-uniformity anyway. | **CONFIRMED BY THE COMPILED PROOF** — `exists_n2FrameTwist_bound` never uses `n2Comb`'s continuity, and `continuousOn_n2Readout` is **not on the critical path**. See the pricing note below. |
| Advice: route the ε–δ extraction through `ouNorm` (`Necessity/OrderUnitS2.lean`), because "`FirstArgContinuous` is a topological `ContinuousOn`, so the extraction MUST route through" it. | ★ **REJECTED WITH EVIDENCE.** `FirstArgContinuous` is `ContinuousOn` in the *carrier's own* norm topology, and on `HermitianMat` that norm **is** Frobenius (`Vendor/HermitianMat/Inner.lean` `instNormedGroup`). So `Metric.continuousWithinAt_iff` applies directly and no norm-equivalence bridge is needed. The compiled proof is the certificate. The reviewer's route is sound but strictly more work. *Reviewers are confidently wrong in both directions — this arc's first instance was the reviewer, not me.* |
| Its account of *why* step (i) gives a U-uniform scale: "not from a norm identity" but from anchoring at the same point. | **HALF ADOPTED.** Both are needed and the proof uses both: anchoring (`basePt 0 = 𝟙`, `Ad_U 𝟙 = 𝟙`) is why one point suffices, and the isometry (`norm_adU`) is what makes the *distance* U-independent. Neither alone closes it. |
| Toolchain note: `lake env lean` from any cwd other than the repo root silently picks up elan default v4.32.2 and fails with "unknown module prefix RadicalRelativity". | **RECORDED** (already a standing hazard in the ARC-7 orders; now confirmed by an outside party). |

**7.1(a) `lem:n2-bounded` — PROVED. `Necessity.exists_n2FrameTwist_bound`.** Row 32 ABSENT →
**FORMALIZED**; coverage **8/19/9 → 9/19/8**. Gates at the commit: `lake build` 3106 jobs, census
149, custom axioms exactly `[]`, and **zero warnings anywhere in the added region** (the file's
pre-existing `show`-style warnings are all above it). New infrastructure, in
`Necessity/ConjTransport.lean`: `norm_conj_unitary` / `norm_adU` (conjugation is a Frobenius
isometry — by *trace cyclicity*, three lines, no entrywise argument) and `norm_entry_le_norm`.
`LEDGER-ARCHIVE-M1-M7.md` had recorded that Mathlib has `frobenius_norm_def` "but no congruence
invariance"; that remains true of Mathlib and is why these are first-party, but the price was
nothing like what "no congruence invariance" suggests.

★★ **THE ROW WAS MISPRICED TWICE, IN OPPOSITE DIRECTIONS, AND BOTH PRICINGS WERE MINE.**
ARC-6 banked "one uniform-continuity step, nothing but plumbing" — too cheap, and a review
retracted it. On 2026-08-09 I replaced that with "four steps, one genuinely analytic" — **too
expensive**. The real count is **three**, and *none of them is a uniform-continuity step*: the
fourth item ("assemble continuity of `n2Comb`") was never needed, and the outside reviewer said so
before the proof existed. What the two errors have in common is that both were estimates written
*instead of* an attempt. The lesson is not "price more carefully"; it is **that a price quoted
without an attempt is a guess, and this project's guesses have been wrong in both directions about
the same row.** Prefer attempting the cheapest step to re-pricing the whole row.

The three steps as executed, and what each actually cost: (i) **the uniform scale** —
`exists_uniform_sp_close`, S2 applied at the *single* effect `a = 𝟙`, uniform in `U` because
conjugation is an isometry; **no compactness**, and not even the explicit value of
`‖Ad_U(basePt x) − 𝟙‖` (continuity of `basePt` at `0` plus `basePt 0 = 𝟙` suffices — cheaper than
the reviewer's own explicit-`|e^{−x}−1|` route). (ii) **stripping the modulus** —
`norm_phase_sub_one_le`, the step ARC-6 missed entirely; genuinely analytic but small. (iii) **the
budget in order** — `ε := ε₀/(4(C+1))` chosen *after* the weight bound, each defect eating a
quarter. Compactness of `U(2)` enters at exactly one point, `exists_n2Weight_lower_bound`, which
was already in the tree.

Two earlier plan errors are recorded in `STATEMENT-MANIFEST.md` row 32 rather than repeated here:
there is no "product metric" argument available and **none is needed** (the uniformity is
algebraic), and `Ici 0 ×ˢ univ` is not compact, which is why nothing extremizes over it.
Consequence for the next rung: `lem:n2-continuity`'s recorded blocker — "cannot be attempted
before boundedness" — is **lifted**.

**7.1(c) the rank-two descent — CLOSED, and by a route a reviewer supplied after refuting mine.**
`RankTwo.blochFrame_eq_iff` first: the Bloch map's fibres on the frame space are **exactly**
complementary pairs. That is the converse of the in-tree `blochFrame_orthoFrame` and was the
descent's documented missing ingredient — the tree knew `blochFrame` identifies a ray with its
complement, and a descent needs that it identifies *nothing else*. Content is one positive-scalar
computation; the negative case is free from `blochVec_orthoVec`. The step that makes it work is
`blochVec_normSq` pinning the *scale* of the proportionality, after which the coordinates determine
the ray.

★★ **Then checkpoint 1 refuted the caveat I had written on rows 32/33 and I rebuilt instead of
re-wording.** The caveat said fibre-constancy plus surjectivity of "the frame map" made those rows
the article's frame-indexed statements. Two things were wrong. (a) **No map from `U(2)` to any frame
space existed anywhere in the tree**, so the surjectivity clause was prose about an undefined
object. (b) For CONTINUITY the inference is not merely unproved but **invalid**: continuity of a
pullback along a bare surjection does not give continuity downstairs — that needs a quotient map.
The reviewer recommended downgrading row 33. Landed instead: `frameMap`, `FrameSpace`,
`toFrameSpace`, `isQuotientMap_toFrameSpace`, `n2Moduli`, **`continuous_n2Moduli`**,
**`exists_n2Moduli_bound`** — both rows now hold for a genuine *frame-indexed* function.

★★ **The reviewer also found something stronger already latent in the tree, and it deleted the
expensive step of my own wall certificate.** `n2FrameTwist_eq_of_base_eq` at `m = m' = 0` gives
constancy on the fibres of `U ↦ Ad_U(frameProj 0)` — genuine fibre-constancy, not invariance at two
group words — because `basePt x = 𝟙 + (e^{−x}−1)·frameProj 0`. `WallCertificates/lem-n2-descent.lean`
had priced the descent's first leg at ~200 lines of `ℂ²` ray algebra; **rays are unnecessary if one
descends along the projection**. The quotient step is then free: `U(2)` compact + frame space
Hausdorff ⟹ closed ⟹ quotient map. **Why I missed it, because this is the transferable part: I
reached for rays because `RankTwo/` is written in `ℂP¹`, and never asked whether the parameter's own
defining identity already descended along something cheaper.** A reviewer with no attachment to that
vocabulary saw it at once.

**7.3 abstract/vdW tier — three rows moved.**
* **`cor:selectors` clause (iii) CLOSED** (`selector_transpose`): transposition **flips the twist**
  (`transposeMap_twistSeq`), so covariance forces the parameter to equal its own negative and the
  `∃!` closes it. ARC-6 predicted "assembly, not an ingredient" and the prediction held — three
  short lemmas. ★ One correction to that prediction: the sign flip does *not* come from cos-even /
  sin-odd as banked, but from `twistFactor_conjTranspose` plus `(Mᵀ)ᴴ = (Mᴴ)ᵀ`.
* **`HermitianMat.isArchimedean` PROVED** — and this retires a real caveat. ARC-6 landed
  `lem:homog`(ii) and `lem:cone-ext` FORMALIZED *carrying* `IsArchimedean` as a hypothesis, defended
  on the ground that the squeeze is part of the article's definition. Sound, but it left the gap
  that **no carrier was known to satisfy it**, so the abstract tier applied, as far as the machine
  knew, to nothing. `H_n(𝕜)` satisfies it — quadratic-form characterization plus one real
  ε-argument, no spectral theorem, no topology, no closedness of the cone.
* **`prop:pseudo-transfer` in the article's own form** (`spCone_specInv_eq_one`): `a⁻¹ · a = 𝟙` with
  the *true* spectral inverse and **no coefficient**, via `spCone` at the admissible normalization
  `1/c`. This is what `lem:cone-ext` was built for in ARC-6, and it needed `isArchimedean` to be
  usable at all — so the cone extension went from a formality to load-bearing on the same day.
  ★ Scope: `spCone` extends the FIRST argument only, so `a · a⁻¹ = 𝟙` is NOT proved.

**7.5 the dry pass — `WallCertificates/`, and the format falsified two of its own entries the day it
was created.** Prose prices are replaced by compiling Lean: each certificate states the missing step
at the article's generality with `sorry` at exactly the gap, plus dated absence claims *with the
scope of the grep that supports them*. Hygiene: nothing in that directory is imported from
`RadicalRelativity/`, so the `sorry`s cannot reach `lake build` or the census — verified, and the
census still reports custom axioms exactly `[]`. Coverage: all 36 rows are now FORMALIZED (10),
pre-registered external (6), or certificated (20).

★★ **The format works, and the evidence is that it refuted itself twice within the hour.**
`lem:normality` (row 9) was certificated "plausibly cheap; never attempted" and then closed —
`sp_tendsto_of_tendsto`, **and it needs no S2 at all**, since additivity alone gives the linear map
`seqLeftMul` and a linear map on a finite-dimensional space is automatically continuous. That makes
the result *stronger than the article's own statement*, which assumes S1 and S2. `lem:n2-descent`
(row 34) had its step (1) deleted by the checkpoint-1 review. Both corrections are recorded **inside
the certificates**, not appended elsewhere.

★★ **A NEW LEAN LESSON, and it is a sharpening of the standing one.** The standing lesson is "a
heartbeat timeout is about the unification path, not goal difficulty". Sharper version, learned
landing the descent: **a timeout can be a symptom of arguments supplied in the WRONG SLOTS.** Three
attempts hit `(deterministic) timeout at isDefEq`; I "fixed" it twice by changing the formulation
(`abbrev` for `def`, `surjInv` for `Classical.choose`) and once by raising `maxHeartbeats` to
1000000 with a comment blaming the range subtype. All three were wrong. The real cause: I had
reordered `n2FrameTwist_eq_of_frameMap_eq`'s parameters when landing it, so `refine … P _ U hS2 ?_`
put the metavariable in the `U` slot instead of `V` and asked the unifier to match `n2Moduli …`
against `n2FrameTwist …`. With the order fixed it compiles at the file's **default** budget and the
`set_option` is gone. **Had I kept the raise, I would have banked a false explanation for a
timeout** — the prose-price failure mode, in Lean.

★★ **CHECKPOINT 1 THEN VERIFIED ITS OWN FIX, and caught that my NEW caveat repeated the OLD one's
shape.** Row 32's replacement caveat said "Residual, and it is the whole residue" and named one
item. There are three: (a) surjectivity onto all rank-one projections; (b) a *homeomorphism* to `S²`
(surjectivity buys only a set-level identification — and `grep -rn Homeomorph RadicalRelativity/`
returns **zero** hits, whole tree); (c) for `ℝP²`, the further quotient by `p ↦ 𝟙 − p`, which is
row 34's sentence rather than 32's. **The catch matters more than the omission: the content got
upgraded and a totalizing word survived the upgrade.** That is the same construction that made the
caveat it replaced wrong. **A totalizing phrase inside a residual claim is where this project's
errors live** — treat "and that is all that remains" as a smell, always.

The same pass confirmed by compiling: `FrameSpace` carries exactly the subspace topology (no
instance diamond, despite being a `def` with `unfold`-built instances); the descent is **not
vacuous** (`frameMap_swap_ne_one` — the one way the section could have been true and empty); and it
sharpened the well-definedness question correctly — `Classical.choose` *cannot* be ill-defined
(proof irrelevance), so the real failure mode was that `n2Moduli` might agree with `n2FrameTwist` at
the chosen preimage **and nowhere else**, which `n2Moduli_toFrameSpace` is precisely the certificate
against. Two of its contributions landed: `n2_sp_eq_twistSeq_n2Moduli` (ties `n2Moduli` back to the
*product*, so the labels are self-evidencing instead of a reader's exercise) and
`frameMap_swap_ne_one`. It advised **against** the two `_ouNorm` capstones, with a good reason:
`firstArgContinuousOu_iff` is an **iff on the hypothesis**, so nothing downstream can be weakened,
and unlike the flagship rows `hS2` appears inside these rows' conclusions, making a converted
restatement less readable than the iff. Not landed.

★★ **THE AXIOM-FIDELITY AUDIT IS DONE, and it was the reviewer's own earlier "did not get to".**
Every field of `SequentialProductOn` compared against the pinned `main.tex:363–392`: S1 →
`sp_add_right` (same `b+c ≤ 𝟙` rider), S2 → `FirstArgContinuous` (equivalent to the ouNorm form), S3
→ `sp_unit_left`, S4 → `sp_zero_symm`, S5 → `sp_assoc_of_compatible`, S7 → `compatible_sp`, S6 →
split across `compatible_ortho`/`compatible_add` (a conjunction split, not an addition), `sp_effect`
= the article's own codomain declaration. **No field is stronger than the article's axioms, so no row
is a special case** — which was the live risk under every FORMALIZED label in this development, not
just the two new ones. In one respect the class is strictly **weaker** (total operation, every axiom
guarded by `IsEffect`), making the rows *more* general; the tree exploits exactly that in `badP`.
★ Scope: this certifies **Lean-vs-article**. The article claims to restate vdW's Definition 2 with
the domain riders made explicit; vdW was not opened, so Lean-vs-vdW rests on that claim.

★ **A COUNTING HAZARD, recorded because the count is the thing most often quoted.** Verifying
10/19/7 by parsing `STATEMENT-MANIFEST.md` programmatically reported 33 rows, not 36 — because three
rows' *statements* contain LaTeX `|` (`\Theta_a|_{J_2(q)}`, `\mathcal{J}_n`'s restriction bars), which
breaks naive pipe-splitting of a Markdown table. Rows 16, 22 and 29 were the casualties. **A script
that silently drops rows reads exactly like a script that found nothing wrong** — the standing
"verify the verifier saw data" rule, in a new costume: print the row count before believing the
tally. Count confirmed 10/19/7 over all 36 after the fix.

★★★ **CHECKPOINT 3 — THE CERTIFICATE-REFUTATION REVIEW — WAS THE MOST DAMAGING AND MOST USEFUL PASS
OF THE ARC.** It refuted one certificate in full, found two more false absence claims of mine, one
vacuous gap statement, one false gap statement, and three inaccurately recorded greps. Everything
below was verified at source before applying.

* ★★★ **`thm-quaternionic.lean` was superseded IN FULL by the file it imports.** All three of its
  `sorry`s are proved in `Hermitian/Symplectic.lean` — `quatConj` (:70) is character-for-character the
  `quatInv` body I wrote as a gap; `quatConj_isHermitian` (:322), `quatConj_involutive` (:130),
  `IsQuaternionic.symmMul` (:196) are the three obligations; and the "vocabulary wall" I recorded does
  not exist: **`HermitianMat.QuatCarrier n` (:455) IS the fixed-point subalgebra as a type**, with an
  `OrderUnitSpace` instance (:462) whose docstring says it is "the carrier the `H_n(ℍ)` row's
  `SequentialProductOn` will live on", and `QuatQuadRep.lean:105` already builds the raw material for
  `theta`. My "forced route's first step" was *behind* where the tree stood. **SIXTH false absence
  claim.** ★ Root cause, and the rule is narrower than the one already on the record: I greped for
  `Quaternion`, the *Mathlib* type name, while the tree's layer is `quatConj`/`QuatCarrier`/
  `quatQuadRep` — an accurate grep supporting a false claim. **NEW RULE: before writing a gap for
  anything in a file's subject area, run `grep -n "^def \|^theorem \|^instance \|^abbrev " <that
  file>`. An import line is a declaration that the file is relevant; reading its declarations costs
  one command.** The certificate is rewritten around the one genuine gap (the *transfer* of the
  classification to `QuatCarrier`), which is now statable precisely because the carrier exists.
* ★★ **"no direct sum of order unit spaces" was FALSE** — `DirectSum.lean:38` is
  `instance instProd : OrderUnitSpace (V × W)`. **SEVENTH false absence claim**, and the second today
  where the grep was accurate and the inference was not: the pattern required both words on one line,
  and the instance is `instProd` in a file named `DirectSum.lean`. **This de-prices row 12
  `prop:central`, whose recorded blocker was exactly this object.**
* ★★ **The second-argument cone extension was discharged and is now IN THE TREE**, which closes the
  other half of row 13. `spConeRight` + `sp_coneNorm_indep_right`, ~25 lines, because its only
  ingredient (`sp_smul_right_of_unitInterval`) was already present and needs `IsArchimedean` but **no
  S2** — so the right slot is strictly *cheaper* than the left. `spConeRight_specInv_eq_one` gives
  `a · a⁻¹ = 𝟙`; with `spCone_specInv_eq_one` the article's identity holds in **both slots**. My
  "nothing in the tree has it" was true of the object and misleading about the cost.
* ★★ **`exists_peirce_exchange` was VACUOUS** — satisfied by conjugation by a permutation matrix, with
  **both** `hN` and `hij` returning as unused-variable lints. A statement that does not need `i ≠ j`
  cannot be capturing "swaps two frame atoms and acts on the coherence blocks". ★ **This is the mirror
  of the row-22 defect in the same file**: row 22 stated a gap FALSELY, row 36(i) states it VACUOUSLY,
  and the consequence is identical — the next person discharges the `sorry` and the row does not move.
  **One lesson: apply the inert-hypothesis test to the GAP statement, not only to theorems.**
* Three recorded greps were inaccurate (`Givens` hits `FrameConstancy.lean:1925`; `blockRotation` is
  case-sensitive and missed `Necessity/BlockRotation.lean`; `crossCoherence` hits
  `Globalization.lean`) — **all three prices survive on inspection at source, but the recorded results
  did not.** Case-sensitivity is exactly how the quaternionic claim went false the same day.
* The Jordan/EJA claim's *inference* was overstated: **Mathlib HAS `IsJordan`/`IsCommJordan`**; what it
  lacks is formal reality and a Jordan-frame API. "EJA generality is not statable" was a tree-scoped
  grep supporting a scope-free claim, and it was load-bearing for rows 16/17/18.
* The README's own hygiene recipe was wrong (it returns two harmless docstring hits, so it reports
  failure on a healthy tree — which trains readers to ignore it). Recipe fixed; the substance was
  independently confirmed.

★★ **AND THE SIGN AUDIT ENDED IN A RETRACTION BY THE REVIEWER OF ITS OWN PRICING, which is the
sharpest methodological finding of the arc.** It had flagged twice that a sign slip in
`twistSeq_diagFamily_entry` "would flip both rows 32/33". It then confirmed the sign correct by an
independent re-derivation from the definitions — and retracted: **rows 32 and 33 conclude `|t̃| ≤ M`
and `Continuous t̃`, and both are invariant under `t̃ ↦ −t̃`.** A sign error could not have falsified
either row; it would only mis-set the *dictionary* between Lean's `t` and the manuscript's. The error
mode: **treating a shared dependency as load-bearing for every consumer without asking what each
consumer's STATEMENT is sensitive to.** What actually needed guarding, and had nothing:
`readout_nonconstant_in_param` — the phase must see `t` through a factor not vanishing at the probe
(`r₀ − r₁ = −x`); had it been proportional to `r_k + r_l` the readout would be **blind to `t`** and the
route silently vacuous. Landed. ★ Its independent probe was deliberately **not** landed, on its own
advice: it shares `cfc_diagonal` and `ofReal_polar` with the tree's route, so it is worth what
`readout_direct` was worth before its scope was corrected. **The largest unexamined risk is now
`tvalLm`/`twist_param_unique_of_scaled`** — they carry the *identification* of the parameter, which
unlike the sign is invariant under nothing either row concludes.

★★★ **THE EIGHTH FALSE ABSENCE CLAIM, AND THE NEW RULE CAUGHT IT ON ITS FIRST USE.** Checkpoint 3
de-priced row 12 `prop:central` by showing "no direct sum of order unit spaces" was false, and said
its summand inheritance and converse assembly "should now be attempted, not deferred". I attempted
it — by applying the rule that same review had just handed over (list a file's declarations rather
than grep for a guessed name) — and **the converse assembly was already built**:
`SequentialProductOn.prod` (`DirectSum.lean:84`) assembles a product on `V × W` from summand
products, all eight fields, with `prod_sp`, `prod_fst`, `prod_snd` and `sp_eq_of_prod_eq`, and its
own docstring says "This is the *sufficiency* half of the omnibus's factorwise assembly".

★★ Note who missed it and why: the reviewer found `instProd` **in that same file** and stopped
there, twenty lines short of `prod`. It had grepped for a pattern rather than read the declaration
list — the exact mistake its own new rule forbids. Listing the declarations found it immediately.
**A rule that catches its author's own error on first use is the strongest evidence a rule can
have**, and it is now the project's standing first move before any absence claim.

What actually remains of row 12 is the **restriction** direction only: that an *arbitrary* product on
`V × W` restricts to S1–S7 products on each summand (`grep restrict\|toSummand\|ofProd
RadicalRelativity/DirectSum.lean` → prose only, 2026-08-09). The converse is done.

★★★ **THE ARC'S FORMER TOP RISK IS CLOSED, BY REMOVING THE QUESTION RATHER THAN ANSWERING IT.**
`n2FrameTwist_unique_param` / `n2FrameTwist_pinned`: `n2FrameTwist P hS2 U` is **the unique real
number** at which the product acts as the twist product at `U`'s frame — which is the article's
*definition* of `t̃(n)`. So `tvalLm`'s internals cannot make the number wrong; a defect there could
only surface as `n2_sp_eq_twistSeq_frame` failing to compile, and it compiles. Rows 32/33 are
provably about the article's object. Non-vacuity is automatic — the `∃!` carries its own witness.

★★★ **AND THE REVIEWER RETRACTED ITS FRAMING OF THAT RISK, WHICH IS THE ARC'S BEST METHODOLOGICAL
FINDING.** Twice it listed "I have not read the proofs of X" as the top risk; twice I accepted it, and
once promoted it to the top item — so my acceptance cost a pass too. **"Unread proof" does not belong
on a risk list for a kernel-checked theorem with a clean `#print axioms`: the kernel read it, and it
is stricter than any reviewer.** What a reviewer must read is **statements**, **definitions** (a `def`
can silently be the wrong object with no error anywhere), and **`Prop`-valued hypotheses** (a located
stand-in typechecks fine). This item was closable two passes earlier by reading three *statements*.
★ The exception that keeps the rule honest is kernel bypasses, and those were checked rather than
assumed: `native_decide` appears twice in the tree and both are prose; all 26 `sorry` and 4 `axiom`
hits are docstrings asserting their own absence; no `unsafe`/`implemented_by` on any path; and
`#print axioms` on every flagship declaration returns exactly `[propext, Classical.choice, Quot.sound]`
— `sorryAx` and `Lean.ofReduceBool` would both appear there if anything upstream used them.

★★★ **A THIRD DEFECT KIND FOR GAP STATEMENTS: SELF-DEFEATING.** The certificate-refutation review's
second pass found that `prop-n2-sufficiency.lean`'s load-bearing ingredient — the one the file told the
reader to attack *first* — implies `n2FrameTwist` is **globally constant for every product**, because
its hypothesis `a = Ad_U a` says `U` *commutes with* `a`, not that it diagonalizes it (at `a = 𝟙`
every unitary qualifies). Global constancy is the negation of what rows 34/35 need, and the tree proves
nonconstant frame functions exist (`tauModuliRP2_nonconstant`). **So the ingredient, if true, would
refute the very row its own certificate covers.** Restated with the diagonalizing idiom
(`a = Ad_U (diagFamily r)` — eleven lines from a theorem the same file cites, and the idiom that
file's *other* statement already used correctly) plus the non-scalar hypotheses its own prose asked
for. The three kinds and their tests, because they are different:
  * **FALSE** (row 22) — refutable by counterexample;
  * **VACUOUS** (row 36(i)) — provable, moves nothing; caught by the inert-hypothesis test applied to
    the *gap*;
  * **SELF-DEFEATING** (row 30) — caught by neither. **Test: assume the gap statement and check it does
    not contradict the row it feeds.** One step.
★ Also found: **two propositions carried an inline `(by sorry)` INSIDE the statement**, so the file's
warning count understated it by two and those propositions were **not fully written down** — they could
not be attacked as stated at all. Discharged (`col_ne_zero`). ★ And the review confirmed every
*judgement* in that certificate's pricing block while refuting its *statement*: **a certificate's prose
and its proposition fail independently — getting the price right is no evidence that the statement says
it.**

★★★ **THE FOURTH AND FIFTH REVIEW ROUNDS BROKE OPEN THE TWO CERTIFICATES NOBODY HAD ATTACKED, AND
PRODUCED THE PROJECT'S NINTH AND TENTH FALSE ABSENCE CLAIMS.**

**`differential-trio.lean` was substantially refuted, and rows 16 and 18 were understated by a
level.** Row 18's status text said the stabilizer representations are "stated as a constructor's
conclusion rather than constructed from Θ" — false: `Necessity/StabilizerInstance.lean` builds
`rhoField`, `dChiStab`, `blockSkewSubmodule`, `diagonalHomSetup` and `stabilizerCoupling` all from
`(P, hS2, hjord)`, and its docstring says it "produces the coupling". Row 16's said the tree has "a
differential shadow" and the gap is identifying it with the article's differential — false:
`coalescence_J2q` and `coalescence_block` are the article's **two clauses, proved at the Θ (group)
level, at abstract generality**, and instantiated at the concrete carrier with the three Faraut–Korányi
fields proved. **Row 18's remaining content, which I had parked behind a `True` placeholder justified
as needing "the stabilizer group as a Lie group with an identity component", is now a THEOREM IN THE
TREE** (`tvalCoef_realized_by_stabilizer`, `stabilizer_group_action_complex`): `torusU` fixes every
frame projection and rotates each Peirce block by the predicted phase, four lines, no Lie theory.
What remains for the ℂ row is only the **converse** — a frame-fixing unitary must be such a torus
element — which is writable today and is now the certificate's single stated gap.

★★★ **THE TENTH FALSE ABSENCE CLAIM: that the article's own generality is unstatable.**
`MasterTheorem/Interface.lean`'s `structure ComparisonSetup` carries a Jordan product (a **field**
named `jordan`), a unit, `jordan_comm`, `rank_ge : 3 ≤ n`, **a Jordan frame** `p : Fin n → J`, a cone,
`Inv`, and `Θ` with its three properties — and row 16 is proved over it. My grep
(`class.*Jordan|structure.*Jordan|EuclideanJordan|class EJA`) structurally could not see it. **Same
failure mode as the quaternionic `Quaternion` grep, one file over in the same directory, on the same
day.** ★ Over-correction guard, preserved from the reviewer: this is *not* an EJA class —
`Interface.lean` says it "does not encode the JB-algebra premises". So rows 16/17 at the article's
generality **are** statable; what is absent is an axiomatization making the cited vIR/FK fields
derivable rather than carried. That reframing propagates to `abstract-tier.lean`'s rows 5 and 6(i),
which had leaned on "not statable".

★ Two further defects in that certificate: "the exp-generator route bypasses differentiation entirely"
is **false** — `CoalescenceDiff.lean` differentiates the χ̃ curve; what the tree never does is *state*
a `HasDerivAt` about Θ or χ (keep the nuance, drop the clause). And a recorded grep **misreported its
own output** (written "no hits", returns five, all docstrings) — the substantive reading survived, the
recorded result did not, which is exactly what the README says trains readers to ignore recipes.

**`prop-n2-sufficiency.lean`'s load-bearing ingredient was SELF-DEFEATING** (recorded above), and the
independent review of the `spConeRight` layer added three corrections that do not touch soundness but
do touch the record:
* ★★ **The pseudo-inverse row is BIGGER than my brief said, and what landed is FIDELITY, not reach.**
  `prop:pseudo-transfer` has three clauses; I described one. Clauses (ii) and (iii) — order
  preservation and vdW Prop. 5.3's hypotheses, which is the payload the proposition exists to deliver
  — were **already in the tree** via the *normalized* route (`seqLeftMul_reflectsNonneg`,
  `seqLeftMul_injective`, `theta_one` and the order-iso), because a positive scalar affects neither
  order-reflection nor injectivity. So `specInv`/`spConeRight` buy the article's literal
  coefficient-free form of clause (i) and nothing more. Both docstrings read as reach and now say
  fidelity.
* ★★ **My asymmetry claim was HALF-CERTIFIED, and it had gone into the ledger as a general fact about
  the axioms.** "The right slot is cheaper because it needs no S2": the *no-S2* half is compiled; the
  *needs-S2* half is not established at all — there is no independence result, and by this project's
  own strong-form standard it would require a counterexample. Reworded to "proved without S2; the
  tree's left-slot route uses it". ★ And `spConeRight_specInv_eq_one` **itself consumes S2**: the
  no-S2 property belongs to the extension, not the identity.
* `specInv` is confirmed to be `b.cfc (1/·)`. **Hygiene warning added**: the def is total and
  `1/0 = 0`, so at a singular `b` it is the Moore–Penrose pseudo-inverse — no present defect, since
  every theorem carries `PosDef`, but the *name* invites dropping it. One inert hypothesis removed
  (`specInv_nonneg`'s `IsEffect`).

★★★ **TWO MORE ROWS ADVANCED, AND THE ARC'S LAST FINDING IS ABOUT EVIDENCE RATHER THAN MATHEMATICS.**

**Row 18's converse is PROVED** (`offdiag_eq_zero_of_fixes_frameProj`): a unitary fixing every frame
projection is diagonal, so the frame stabilizer is exactly the torus. The rewritten
`differential-trio.lean` had recorded this as the row's **single** remaining stated gap, judged
"writable today… a short matrix argument" — and it was: multiplying the fixing condition through by
`U` turns it into commutation with the matrix unit `E_kk`, and the `(i,k)` entry gives the result.
**That certificate's one gap closed within the hour of the certificate being written** — the fourth
time an entry in that directory has been falsified by an attempt.

**Residual item (a) of the rows 32/33 caveat is CLOSED** (`exists_frameMap_eq_rankOne`): every
unit-vector rank-one projection is `frameMap U` for the explicit unitary
`!![ψ₀, -conj ψ₁; ψ₁, conj ψ₀]`, ~25 lines, and `RankTwo.orthoVec` is not needed. Two of the three
residual items remain, and the reviewer's observation that the third sub-part is *avoidable* by
phrasing the identification against `QubitFrame` (defined as rays) rather than "all rank-one
projections" stands.

★★★ **AND A RETRACTION I HAVE TO OWN, not just record.** The reviewer's earlier report said the
substantive half of that surjectivity "COMPILES"; **it did not**. The proof had an unsolved goal,
Lean's error recovery inserted a `sorry`, and the top-level theorem carried `sorryAx`. The cause was
reading `lake env lean` output through a `head` window that earlier failures had already filled — the
**truncating-pipe** failure this project has had a rule about since before this arc. The reviewer
committed it; **I then propagated it into the manifest on its word, without an independent check**,
which is the second time this arc I accepted a reviewer's claim about its own work and paid for it
(the first was the sign mispricing). The conclusion survived and is now genuinely compiled; the
evidence did not exist when it was claimed.

★ **The check, now standing protocol for scratch work:** count errors over the FULL output
(`grep -cE error`, never a `head` window) **and** `#print axioms` the final theorem looking for
`sorryAx`. Note what this is *not*: it is a different rule from the statements-vs-proofs rule — that
one is about what to read, this one is about how to verify a compile, and both belong in the review
protocol. ★ For the library itself the check is already automatic and strictly stronger:
`AxiomAudit.lean` requires every tracked declaration's closure to lie in
`[propext, Classical.choice, Quot.sound]`, and `sorryAx` is not in that list — **which is why the tree
was never at risk even while a claim about it was false.** I verified all six certificates the same
way afterwards: zero errors in every one, sorry counts exactly the intended gaps.

★★ **The reviewer's own closing observation is worth keeping:** of its seven passes, the two most
useful findings were both corrections of its *own* earlier claims rather than of mine — the sign
mispricing and this one. That is an argument for keeping a reviewer on a target long enough to audit
its earlier reports, not only the code, and it is the opposite of the instinct to rotate reviewers for
freshness.

★★★ **THE DRY PASS WENT DRY — round 2 produced ZERO movement, and here is the evidence.**

The terminal condition asks for a 7.5 pass over every non-FORMALIZED row that finds nothing. Earlier
rounds kept finding things, so the pass was run again after every flagged-cheap item had been either
closed or attempted:

* **Round 1** (declaration-list sweep over the remaining rows' subject areas — Peirce/`J₂` carriers,
  restriction-to-a-summand, coherence space, Peirce exchange): **no row moved.** It found two pieces of
  *adjacent* machinery worth naming rather than a false absence claim —
  `n2_exchange_selects_luders` (`MasterTheorem/RankTwo.lean`), which machine-checks the **mechanism**
  of `cor:selectors`(i) at rank two, and `theta_conj_exchange` (vdW 5.7(1)), a different "exchange".
  ★ Neither moves row 36, because `rem:n2-selection` is one of the **seven excluded remarks** of the
  denominator and clause (i) is about `H_N(ℂ)`, `N ≥ 3`, with Peirce exchange. Recorded in the
  certificate so nobody rebuilds the idea while looking for the object.
* **Round 2** (declaration-list sweep for *every* remaining missing object: the `ouNorm` ball,
  `J₂(q)` as a carrier, effect simplicity, order-infima, Givens/Jacobi, the coherence-space complex
  structure, a product on `QuatCarrier`): **zero declaration hits.** Every remaining missing object is
  genuinely absent.

Round 2 is the dry round. What made it possible was exhausting the cheap items first — the last four
closed in this final stretch were row 18's converse (`offdiag_eq_zero_of_fixes_frameProj`), the frame-map
surjectivity (`exists_frameMap_eq_rankOne`), residual item (c) (`frameMap_mul_swap`), and two of the
four steps of the compatibility chain (`offdiag_zero_of_commute_diagonal`, `eigen_diagonal_fin2`) —
after which nothing left in the manifest was priced cheap on evidence rather than on a guess.

★ **What is honestly NOT claimed by "dry".** It means a full audit round found no movement, not that
the remaining rows are unreachable. Three items were attempted and not finished, and each is recorded
as budget rather than resistance: the compatibility chain's steps 3(b) and 4 (matrix plumbing over
`Fin 2`, no new mathematics), residual item (b) (the `QubitFrame`/`FrameSpace` homeomorphism, priced by
a reviewer at 40–60 lines and never tested), and the ℍ transfer onto the carrier that already exists.

★ **Running total of this arc's own corrections, stated plainly because the pattern is the finding:**
five false absence claims (quaternionic carrier, direct sum, direct-sum assembly, twist-product
compatibility, and the article's own generality being unstatable — nos. 6-10),
one FALSE gap statement (`lem:orientation`), one VACUOUS gap statement (`exists_peirce_exchange`), one
SELF-DEFEATING gap statement (`frameRay_eq_of_compatible`), two propositions with sorries hidden inside
them, two dependencies mispriced as fatal (the sign and the `tvalLm` identification — both retracted by
the reviewer who raised them, both accepted uncritically by me), one totalizing residual claim, one half-certified
claim about the axioms, one row whose three clauses I described as one, five inaccurately recorded
greps, one broken verification recipe, two `True` placeholders that recorded awkwardness and got read
as depth, one compile claim that was false when made and which I propagated without checking, and one
timeout "fixed" three times before its real cause was found. **Every one of them was mine or a reviewer's,
and every one was caught inside a single day by making the claims falsifiable instead of asserting
them.** That is the case for the certificate format, and it is stronger than any coverage number.

**Coverage at end of ARC-7's landed work: 10 FORMALIZED / 19 PARTIAL / 7 ABSENT.** Gates green at
every commit: `lake build` 3106 jobs, census 149 modules, custom axioms exactly `[]`, zero warnings
in every region touched. Tags `paperA-arc7-cp0` (`d0f1312`), `paperA-arc7-cp1` (`ab87ed3`),
`paperA-arc7-cp2` (`fd53252`).

**Reviews: three checkpoints delivered, all findings verified at source before applying OR
rejecting.** Checkpoint 0 (readout block, its first outside read) **certified `n2Readout_eq`'s `hb`
and `hx` load-bearing in the STRONG form** with compiled counterexamples, via `badP` — the twist
product on effects and `0` off them, a genuine S1–S7+S2 product because every
`SequentialProductOn` field guards its arguments with `IsEffect`. That single construction
**discharges the whole "four hypotheses needing a bespoke product" debt**: it certifies any
hypothesis whose only job is to place an argument in the effect set. It also supplied `sign_check`,
a sign guard below `twistSeq_diagFamily_entry` which `readout_direct` could not provide, and caught
a **second** instance in one file of a docstring asserting that a theorem sixty lines below did not
exist. ★ I **rejected** one piece of its advice with evidence — that the ε–δ extraction "MUST route
through `ouNorm`" — because `FirstArgContinuous` is `ContinuousOn` in the carrier's *own* norm
topology, which on `HermitianMat` is Frobenius; checkpoint 1 independently **confirmed** I was right,
and went further by compiling the row with `FirstArgContinuousOu` as its hypothesis. **Reviewers are
confidently wrong in both directions too** — this arc's first such instance was a reviewer, not me.

---

## ★★ ARC-6 ORDERS (2026-08-08, Fable design pass — the big-chunk climb). **Superseded as campaign SSOT by ARC-7 above (2026-08-09); the execution record and lessons below remain binding.**

**Sizing:** this is a ~24-hour-of-work campaign, set as ONE goal on purpose. Do not stop at
rung boundaries to report; continue until the ladder is exhausted or every remaining item
is banked with a measured wall. Every decision needed is pre-made below; anything
Bryan-gated is out of scope by definition, so there is nothing to ask mid-arc.

**Standing decision records — do not re-litigate:** literal 36/36 REJECTED and EJA-first
REJECTED (rationale in the ARC-5 block below); the six by-design-external rows are
`thm:vdw1` + `prop:bridge` (cited), `mthm:master`/`mthm:omnibus` one-theorem form (JvNW),
`prop:theta` at vIR generality, `thm:albert` (Albert M2). Interior ceiling 30, realistic
26–28. The count is an OUTPUT, not a quota — the census (`custom axioms exactly []`) and
`THEOREM-MAP.md` are the product. Baseline at these orders was **7 / 19 / 10**; **as executed the arc ended at 8 / 19 / 9** —
see the EXECUTION RECORD below and `STATEMENT-MANIFEST.md`, which is authoritative; the denominator stays pinned to blob `205fdf5a` — never re-pin.

**THE LADDER (in order; the wall protocol below governs every rung):**

* **6.0 Audit before build.** Two of arc-5's seven FORMALIZED rows were undercounted rows,
  not new proofs. Before any new proof this arc, for every row targeted below: (a) grep the
  WHOLE tree for the *ingredients*, not the assembled statement; (b) run the
  inert-hypothesis test on the nearest existing declaration (compile the conclusion with
  the hypothesis deleted). Specifically: re-price `lem:homomorphism` by reading what
  `chiTilde_eq_exp_dChi` actually proves (it exists and feeds `dChi_kills_corner`, so
  "Lean never differentiates Θ" may be another directory-scoped absence claim), and price
  `lem:simple-bridge` clause by clause (attempt later only the clauses this audit shows
  cheap). Verdicts recorded in `THEOREM-MAP.md` in one commit.
* **6.1 Close the rank-two lane — the crown.** In order: (a) diagonal-phase-fibre
  constancy of `n2FrameTwist` (the `U(2) → S²` gap in `prop:n2-necessity`);
  (b) `lem:n2-bounded`; (c) `lem:n2-continuity` — check Mathlib for topology/compactness
  instances on `Matrix.unitaryGroup` before hand-rolling anything, and if continuity plus
  compactness gives (b) for free, take that order; (d) the remaining descent clause of
  `lem:n2-descent` (a continuous function on `ℝP²`); (e) `prop:n2-sufficiency` —
  generalize the constant-`t` machinery of `lem:twist-sufficiency` to continuous
  `t : ℝP² → ℝ`, reusing the τ-family partials already banked under `thm:qubit-boundary`;
  (f) assemble `cor:qubit-classification` as the bijection; (g) discharge
  `thm:qubit-boundary`'s bundled S1–S7 clause as an instantiation of (e).
  ★ CHECKPOINT REVIEW after (f) — see the review protocol.
* **6.2 The differential trio.** `lem:homomorphism` (the carrier is a normed space, so
  Mathlib `fderiv` applies; pre-registered fallback = the pointwise-derivative version,
  banked as PARTIAL with the delta named), then `lem:coalescence` (identify the in-tree
  shadow WITH the article's differential — the identification is the open part, not the
  shadow), then `prop:stabilizers` (construct the representation from Θ; ℂ row first — it
  is the one the flagships consume; the ℝ/ℍ/𝕆 rows are bankable).
* **6.3 The abstract tier.** Supply the Archimedean property as an explicit `Prop`/mixin —
  NOT a change to `SequentialProductCore.mk` (`AxiomAudit.lean` Layer 5 freezes the
  printed constructor type). Then: abstract `lem:homog`(ii), abstract `lem:cone-ext`, and
  divide the `pseudoInvCoef` out of `prop:pseudo-transfer` to reach the article's
  `a·a⁻¹ = 𝟙` form. ★ **This next sentence was falsified during the arc and is retained only as
  the order as written:** "`lem:homog`(i) needs a positive-linear-extension construction:
  attempt it, bank on resistance." The construction **already existed** —
  `Necessity.seqLeftMul` — so what (i) actually needs is the abstract port, not a construction
  (see the EXECUTION RECORD and `THEOREM-MAP.md` §3b). ★ CHECKPOINT REVIEW after this rung.
* **6.4 The caveat sweep, in yield order.** `cor:selectors`(iii) — exactly one missing
  lemma, `(cfc f a)ᵀ = cfc f (aᵀ)`, recipe recorded in `ComplexRowUnconditional.lean` —
  then clause (i); `lem:normality` (f.d. order-unit space, S1+S2 ⟹ vdW-normal);
  `lem:frame-fix` general statement; `lem:frame-connectivity` via a Givens/Jacobi
  factorization into rank-two block rotations (`AdjBlock` is strictly finer than
  `AdjAxis` — the three Householder factors in the tree do NOT suffice); `lem:orientation`;
  `prop:central`'s summand inheritance + converse assembly; any `lem:simple-bridge`
  clauses that 6.0 priced cheap.
* **6.5 The ℍ row — stretch.** `thm:quaternionic` via `H_n(ℍ) ↪ H_{2n}(ℂ)` as the fixed
  points of a conjugate-linear involution (the blocker is ℍ ∉ `RCLike`, not missing
  quaternions — Mathlib has them); quaternionic Wigner may fall to the `RealWigner`
  rank-one technique. Bank freely; this rung is allowed to end as a measured remainder.

### ARC-6 EXECUTION RECORD (append per rung; the orders above stay as written)

**6.0 audit — DONE 2026-08-08, and it repriced the arc's biggest row before a line was
written.** Two verdicts:
* ★★ **`lem:homomorphism` was ABSENT for a false reason.** §2 of `THEOREM-MAP.md` said "Lean
  neither differentiates `Θ` nor proves `dχAdd` is its derivative"; that describes the
  *abstract skeleton* and was generalized to the whole tree. In fact `chiTilde` constructs the
  character by the article's own `min(x,0)` decomposition and `chiTilde_eq_exp` **proves** the
  real-linear differential exists and is unique, via `multiParameter_eq_exp` — no Lie theory,
  and needing only line continuity where the article assumes joint. Only the hyperplane
  factorization was genuinely missing, and rung 6.2 closed it the same day (below). §3's
  summary line "the construction of the comparison character and its differential from `Θ_a`"
  was removed for the same reason. Row: ABSENT → **PARTIAL**; detail in `THEOREM-MAP.md` §3c.
* **`lem:simple-bridge` priced per clause: it is ~3/4 cited.** The article's own proof assigns
  (i) to vdW Thm. A.6, (iii) to vdW Props. 4.19–4.20, (iv) to a vdW remark. Only (ii) is
  interior (the Jordan spectral theorem). Honest target = clause (ii) on the concrete carrier.
  This is the row the ceiling arithmetic flagged for honest pricing.

**6.1 rank-two lane — (a) CLOSED; (b)(c) BANKED with a named, available enabler.**
* **(a) DONE.** `n2FrameTwist_mul_diagonal` closes the `U(2) → S²` diagonal-phase-fibre gap
  the arc-5 cold review identified, so the frame function is a function of the ordered frame,
  and with `n2FrameTwist_reverse` of the *unordered* frame — a point of `ℝP²`. Both fall out
  of one new engine, `n2FrameTwist_eq_of_base_eq` (same base points ⟹ same parameter), plus
  `diagonal_conj_diagFamily`. `Necessity/FrameConstancy.lean`; no `2π` argument anywhere.
* **(b)/(c) BANKED — and the orders' own suggested reordering is REFUTED.** The orders said to
  try continuity first and take boundedness free from compactness of `U(2)`. Compactness *is*
  in-tree (`Vendor/Wigner/UnitaryCompact.lean`, vendored, axiom-clean), so that implication
  holds — but it runs the wrong way. Continuity needs a principal branch, which needs
  `sM < π`, which needs the bound. So the article's order (b then c) is forced. Three distinct
  routes to continuity were examined and all funnel through boundedness; the two that bypass
  it fail for stated reasons (a discontinuous section of a covering need not equal a
  continuous lift, even over the now-simply-connected `S²`; two incommensurable `δ`s pin the
  value but not continuity). Recorded per row in `STATEMENT-MANIFEST.md` rows 32/33.
* ★★ **The gate is one input, and it is NOT missing from Mathlib.** Both (b) and (c) reduce to
  **operator-norm continuity of `a ↦ Θ_a` in the matrix argument** — the dependency this
  project banked earlier as the real row's "final dependency … the functional calculus's
  continuity in the matrix argument". Mathlib has it:
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean` supplies
  `continuousOn_cfc` (`cfc f` continuous on elements whose spectrum lies in a fixed compact
  set), with `ContinuousAt.cfc` and `Filter.Tendsto.cfc` alongside; and this tree's carrier
  already goes through `HermitianMat.cfc` (`Hermitian/Twist.lean`). So the remainder is
  **ABSENT with a named route, never BLOCKED** — S2 gives `L_a` pointwise, finite dimension
  upgrades pointwise to operator norm, and `continuousOn_cfc` gives `a ↦ Q_{a^{-1/2}}`. Cost
  is the contradiction argument's plumbing, not a missing theorem. **This is the fourth time
  in two arcs that "Mathlib lacks X" was wrong: grep the library before writing it.**

**6.3 abstract tier — DONE, and it was much cheaper than rung 5.1 priced it.** Two rows moved:
* **`lem:homog`(ii) proved at abstract order-unit-space generality** —
  `SequentialProductOn.sp_smul_left`, carrying S1–S7 + the article's S2 +
  `OrderUnitSpace.IsArchimedean` as an explicit `Prop`. The full ten-step ladder is now
  abstract (second argument: `sp_natSmul_right`, `sp_divNat_smul_right`, `sp_ratSmul_right`,
  `sp_smul_right_of_unitInterval` ← Archimedean consumed here; first argument:
  `sp_comm_natSmul`, `sp_comm_ratSmul_self`, `sp_comm_ratOneSmul`, `sp_ratOneSmul_left`,
  `sp_smulOne_left` ← the single S2 use, `sp_comm_smulOne`, `sp_smul_left`), in
  `SequentialProduct.lean`. The concrete versions are untouched. ★ **Rung 5.1's obstruction
  was correctly diagnosed but wrongly priced.** It was right that the ε-squeeze *is* the
  Archimedean property and that the class carries only order-unit boundedness. It was wrong to
  conclude the work was large: with Archimedean supplied as a `Prop`, the ladder ports
  essentially verbatim, because it never used anything about matrices. Cost was three missing
  order lemmas (`sub_le_sub_right'`, `sub_le_sub_left'`, `le_of_sub_nonpos` — Mathlib's need
  ordered-group instances this class does not provide) and one Mathlib import.
* **`lem:cone-ext` FORMALIZED, with a norm-free admissibility condition** (the row still carries S2, which is a norm-topology hypothesis — ARC-6 review correction; do not call the row "norm-free") — `sp_coneNorm_indep` (independence of the
  normalization), `sp_coneNorm_smul` (positive homogeneity), `sp_coneNorm_eq_of_isEffect`
  (agreement on effects), `exists_isConeNorm` (existence). ★ **Better than the article's
  route**: the article's admissibility is `μ ≥ ‖v‖` and it derives `v ≤ μ𝟙` from that "in an
  order unit space", which presupposes the carrier's norm *is* the order-unit norm — a fact
  this class does not carry, and the reason arc-5 had to hedge `lem:span`'s abstract claim.
  `IsConeNorm v μ := 0 < μ ∧ IsEffect (μ⁻¹ • v)` states the same requirement without the norm,
  and the class's own order-unit boundedness supplies an admissible `μ`, so no norm hypothesis
  is needed at all. Self-caught: `sp_coneNorm_smul` had **inert** `IsArchimedean` and S2
  hypotheses; both were removed before landing (the inert-hypothesis test, applied to my own
  work rather than waiting for the reviewer to apply it).

**6.4 caveat sweep — the head item's ingredient landed.** `Necessity.cfc_transpose` /
`transposeMap_cfc`: **transposition commutes with the real functional calculus**, which
`ComplexRowUnconditional.lean` recorded as the *one* thing `cor:selectors`(iii) was missing,
with the sentence "Nothing in this tree has it" (now retired). Built exactly as that file's
recipe predicted: entrywise conjugation is an ℝ-star-algebra hom of `Matrix n n ℂ`
(`conjMatStarAlg`, from `AlgHom.mapMatrix Complex.conjAe.toAlgHom` plus `map_star'`), so
`StarAlgHomClass.map_cfc` applies; and `Aᵀ = conj A` for Hermitian `A` converts it. Clause
(iii) now needs assembly only, and the assembly is checked on paper:
`twistFactor (aᵀ) (-t) = conj (twistFactor a t)` because `cos` is even and `sin` is odd, so
`transposeMap (a ∘_t b) = (transposeMap a) ∘_{-t} (transposeMap b)`, and the `∃!` closes it as
in clause (ii).

**Coverage after 6.3/6.4: 8 FORMALIZED / 19 PARTIAL / 9 ABSENT** (`lem:cone-ext` is the new
row; `lem:homomorphism` moved ABSENT → PARTIAL earlier in the arc). Gates green at every
commit: 3106 jobs, census 149, custom axioms exactly `[]`.

**6.5 ℍ row — NOT ATTEMPTED, but PRICED, and this is the arc's one genuine BLOCKED.** Given
this arc's record (five false absence claims, four wrong "Mathlib lacks X"), the stated blocker
was checked at source rather than inherited. Result: **it holds, and for a stronger reason than
recorded.** Mathlib *does* have quaternions (`Quaternion`, `Mathlib/Algebra/Quaternion.lean`),
so that was never the obstacle. The obstacle is that the tree's field-general `Gen` layer is
written for `RCLike 𝕜`, and **ℍ can never be `RCLike`** — the class extends
`DenselyNormedField`, hence *commutative*, and its `re_add_im_ax` demands a **two**-dimensional
real decomposition `z = re z + (im z)·I`, while ℍ is noncommutative and four-dimensional. That
is an impossibility, not an absent instance. ★ **But the ARC-6 cold review corrected the
conclusion I drew from it:** the row stays **PARTIAL**, because what this blocks is the `Gen`
*layer*'s reuse at ℍ, not the row, which remains reachable by the embedding route — and because
"BLOCKED" is a fourth status word outside the FORMALIZED/PARTIAL/ABSENT taxonomy the coverage
count depends on, and row 32 already forbids that vocabulary ("ABSENT-with-a-named-route, never
BLOCKED"). Keep status words inside the taxonomy; put the obstruction in prose. Consequence: the `Gen` layer
cannot be reused at ℍ at any price, and the route is forced to be
`H_n(ℍ) ↪ H_{2n}(ℂ)` as the fixed points of a conjugate-linear involution — the quaternionic
structure carried by the involution instead of by a scalar field, exactly as the orders said.

### ★ ARC-6 REVIEW OUTCOME — attempt 1 failed, attempt 2 delivered (2 of 3), and the findings are applied

**Attempt 1 failed; attempt 2 SUCCEEDED, 2 reviewers of 3. This section was itself wrong for
several hours and is corrected here — see the note at the end, which is the most useful thing
in it.**

*Attempt 1 — failed.* One reviewer against frozen tag `paperA-arc6-review` (`9c2aa88`) with a
brief covering the whole arc. Asked five times, including "partial findings now beat complete
findings later". Nothing returned.

*Attempt 2 — succeeded.* Diagnosing attempt 1 as too broad a brief, **three** reviewers were
spawned in parallel, each narrowly scoped to finish inside ~25 tool calls: the abstract tier's
two FORMALIZED claims; the rank-two lane and the phase sign; the retractions plus documentation
consistency. **Two of the three delivered substantive reports; the rank-two reviewer went idle
without reporting.** So the narrowing worked, and the fix was real rather than cosmetic. One
reviewer also reported *why* its earlier attempts vanished: it had written them as plain text
instead of calling `SendMessage`. That is a mechanism worth knowing — a subagent's prose is not
delivered.

★★ **THE REVIEWS EARNED THEIR KEEP, AND CAUGHT THINGS SELF-REVIEW DID NOT.** Findings, all
verified at source before applying:

| Finding | Disposition |
| --- | --- |
| **`cfc_transpose`'s BOTH hypotheses are inert** — outside its domain `cfc` is junk-valued at `0` and degrades on both sides together, since `spectrum ℝ Aᵀ = spectrum ℝ A`. The reviewer supplied a compiled hypothesis-free proof. | **ADOPTED.** `spectrum_transpose` + `cfc_transpose_unconditional` are in the tree; `transposeMap_cfc` is unconditional too. **Third inert hypothesis this arc**, and the first found by someone other than me. |
| **`IsArchimedean` ⟺ the textbook ℕ-form** (Alfsen–Shultz / Paulsen–Tomforde), proved in both directions, unprompted. | **ADOPTED** as `OrderUnitSpace.arch_iff` (+ `IsArchNat`). This makes the "part of the definition, not a located hypothesis" defense of both FORMALIZED labels *machine-checked* instead of asserted. I would not have thought to ask for it. |
| "The *statement* of `sp_smul_left` never mentions the norm" — **FALSE**: `hS2` unfolds to `ContinuousOn` in the carried norm topology. | **RETRACTED.** Never call `lem:homog`(ii) "norm-free". The label survives on a different argument (S2 *is* the article's norm-continuity axiom, and `ouNorm_le_norm` makes the topologies agree on the carrier). |
| "`IsConeNorm` states the same requirement without the norm" — **FALSE**: strictly *weaker*, hence a *larger* admissible set, hence the independence clause is *stronger* than the article's. | **CORRECTED** in the docstring and the manifest row. |
| "covers every EJA" — **not machine-checked**: there is no Jordan/EJA class anywhere in the tree. | **CORRECTED** to "every EJA instantiates it by standard mathematics this tree does not itself formalize". |
| `mthm:master` listed under "no Lean counterpart" while the manifest rates it PARTIAL. | **RE-SCOPED** to the `master_chain` *declaration* — the same scope-loss the list corrects two bullets down. |
| The ORDERS block still ordered "`lem:homog`(i) needs a positive-linear-extension construction: attempt it, bank on resistance", falsified by my own retraction. | **FIXED** at both sites. |
| Three stale present-tense counts (`LEDGER` ×2, `THEOREM-MAP` ×1), one inside the SSOT block and one phrased as a standing rule. | **FIXED**; historical figures now dated. |
| `thm:quaternionic` called "genuinely BLOCKED, not ABSENT" while row 32 forbids that vocabulary, and BLOCKED is a fourth term outside the taxonomy the count depends on. Also: the RCLike argument blocks the `Gen` **layer**, not the row. | **CORRECTED**; row stays PARTIAL, obstruction described in prose. |
| `sp_coneNorm_smul`'s `IsConeNorm` hypothesis used only for `μ ≠ 0` — over-strong. | **WEAKENED** to `μ ≠ 0`. |

Both reviewers independently **CONFIRMED** the two retractions (`lem:homomorphism` wrongly
ABSENT; `lem:homog`(i) is `seqLeftMul`), that `multiParameter_eq_exp` is a genuine theorem with
no located hypothesis, that `conjMatStarAlg` is a real ℝ-star-algebra hom, that the
cos-even/sin-odd reasoning behind the banked `cor:selectors`(iii) assembly holds, that `spCone`'s
`else 0` branch is unreachable, that the coverage count is 8/19/9 (counted independently), and
that **both FORMALIZED labels stand**. One added a fact I did not have: the **real** lane also
discharges the Jordan hypothesis from S2 (`thetaPreservesJordanR_of_S2`).

★ **One nuance to preserve verbatim:** the tree contains **no `HasDerivAt`/`fderiv` statement
about `Θ` or `χ` anywhere** — the `exp`-generator route bypasses differentiation entirely. The
retracted sentence's *inference* was false, which is what mattered; but **never upgrade §3c to
"Lean differentiates Θ"**.

★★ **The lesson I got wrong, recorded because it is the most transferable thing here.** I wrote
"the review channel failed on BOTH attempts … this is a tooling failure, not a scoping failure"
— and then two reports arrived. **Both halves were wrong: attempt 2 worked, and the cause was
scoping (plus one reviewer not calling `SendMessage`).** I declared a systemic failure from two
data points while the second was still running, which is the same impatience that produces
premature absence claims. **A silent channel is not a dead channel; "no report yet" is not "no
report".** Wait, or say "not yet returned" — never "failed".

**Lint sweep over the five files this arc touched.** One warning was mine and is fixed
(`transpose_eq_conj_of_isHermitian` carried unused section variables; now `omit`ted). Two are
**pre-existing and left alone** rather than drive-by fixed, but recorded here so they are not
lost: `SequentialProduct.lean` `sp_sub_right` has an unused hypothesis `hle` — a small inert
hypothesis in the abstract derived layer, predating this arc — and `OrderUnitSpace.lean:73` has
two unused `simp` arguments. Neither is mine to fix silently; both are cheap when someone is in
those files.

★★ **The inert-hypothesis test has a STRONGER form, and it should be the default.** Instead of
trying to prove the conclusion without the hypothesis and reporting failure, **try to disprove
the hypothesis-free statement.** A compiled counterexample certifies the hypothesis is
load-bearing; a failed proof search certifies nothing. Demonstrated on
`abs_le_of_phase_near_one`: at `δ = 0` the premise ranges over `0 ≤ x ≤ 0` only, so it holds for
*every* `t`, while Lean's `π/(3*0) = 0` forces `|t| ≤ 0` — and `t = 1` refutes it. `hδ` is
therefore *proved* necessary. Use this form on every hypothesis whose necessity matters; the
weaker form is what left `cfc_transpose`'s two inert hypotheses standing until a reviewer
found them.

**Which hypotheses actually got the strong test — recorded, because the distinction is what let
`cfc_transpose` slip.** STRONG (disproved without it, hence *certified* load-bearing):
`abs_le_of_phase_near_one`'s `hδ`. FOUND SPURIOUS and removed: `n2FrameTwist_eq_of_base_eq`'s
`hs` (automatically true for every `m : Fin 2`, so it was an obligation no caller ever needed
to discharge). WEAK ONLY (reasoned load-bearing, not certified): `n2Readout_eq`'s `hb`/`hx`
and `adU_conj_twistSeq`'s `hU`/`hU'`. The obstacle for those four is real rather than laziness:
refuting them needs a *bespoke* product that agrees with the twist product on effects and
differs off them — for the twist product itself `sp = twistSeq` everywhere, so it cannot witness
the failure. On paper `adU_conj_twistSeq` does fail at `U = 2·1` (both sides scale by different
powers), which is the sketch to formalize if these ever need certifying.

**On the limits of the WEAK inert-hypothesis test, stated so the record is not overclaimed.** The
test has real teeth *when the conclusion is actually provable without the hypothesis*: that is
how `rhoChi_eq_smul_generator`'s `i ≠ j` was caught this arc (proof found, theorem strengthened)
and how `sp_coneNorm_smul`'s `IsArchimedean`/S2 were caught and removed. But a *failure* to find
such a proof is not a certificate of load-bearingness — Lean cannot certify that no proof
exists. For the abstract ladder I have only a mathematical argument that `IsArchimedean` is
load-bearing (it is the sole bridge from ℚ-homogeneity to ℝ-homogeneity; delete it and the
ε-squeeze has no replacement), plus positive controls confirming every new theorem does go
through with its stated hypotheses. **Do not read "inert test run" as "hypothesis proved
necessary".**

**Self-review is structurally weaker than cold review, and this arc is the proof — in both
directions.** Self-probing did real work: it caught `rhoChi_eq_smul_generator`'s inert
hypothesis, two doc rows still asserting superseded claims, and the one failure mode that would
have voided the FORMALIZED labels (`IsArchimedean` inhabited). But the reviewers produced two
things it structurally could not: a **compiled refutation** of hypotheses I believed were
load-bearing (`cfc_transpose`), and a **theorem I did not know to want** (`arch_iff`). An author
does not probe the claims he is confident in.

### ★★ CHECKPOINT 3 (rank-two) — REVIEWED, by four reviewers, and it was the most productive review of the arc

All three checkpoints are now discharged by outside review. The rank-two block took four
reviewers across three spawn rounds; the last two rounds delivered. Two mechanisms mattered:
**narrow one-concern briefs**, and **telling the reviewer explicitly to call `SendMessage`** —
one reported that its earlier reports "returned success" yet never reached me, and another sent
the same finding four times.

**CONFIRMED by independent work (not merely agreed with).** The phase sign in `n2Readout_eq` is
right — two reviewers derived it from `twistSeq_diagFamily_entry` on separate routes and got my
RHS; one also recompiled the crown probe. The `π/3` constant is exactly right, no factor error,
and both reviewers independently derived the sharp form as the strict `<` I had already
strengthened to. `n2FrameTwist_mul_diagonal` is non-vacuous at `diag(i,1)`. The `ℝP²` group
argument is valid (monomial matrices are exactly the right-stabilizer of the unordered pair of
column lines). Axioms exactly `[propext, Classical.choice, Quot.sound]` on every new
declaration; zero linter warnings.

**REFUTED — six of my claims, all applied.**
1. ★★ **"a fixed test effect whose frame coefficient never vanishes" — that object PROVABLY DOES
   NOT EXIST**, and three reviewers proved it independently. `n2Coef b U` is the `(0,1)` entry of
   `Uᴴ b U`, so taking `U` to be an eigenbasis of `b` makes the conjugate diagonal and the
   coefficient zero; the readout is then identically `0` in `x`, carrying no information. Every
   fixed probe is blind at its own eigenframe. **The sentence also contradicted the two-effect
   plan in the same file.** Retracted.
2. **"needs continuity of the product in its second argument" — wrong requirement.** `b` is
   fixed, so S2 alone suffices. The `seqLeftMul` justification solved a non-problem.
3. **Three self-contradicting docstrings**, the worst being a banked note saying the
   `ContinuousOn` assembly "is NOT proved" sitting 115 lines above the theorem that proves it —
   a top-down reader was told the theorem beneath them did not exist. Also `n2Readout_eq`'s
   "everything except the phase is explicit and **nonvanishing**", contradicted 25 lines later by
   my own correct statement that every non-scalar `b` is blind at its diagonalizing frames.
4. **`readout_direct` is not an independent cross-check** — both chains bottom out in
   `twistSeq_diagFamily_entry`, so a sign error *there* flips both. It guards the classification
   chain only. Narrowed.
5. **Swap-invariance alone does not give unordered-frame descent** (needs the diagonal-fibre
   clause proved 80 lines later); and **"invariance under the FULL stabilizer, machine-checked"**
   overstates — two group words are checked, exhaustion is prose, and no `ℝP²` object exists in
   Lean. Both narrowed.
6. **My recorded obstruction for `adU_conj_twistSeq` was wrong.** I wrote that refuting its
   hypotheses "needs a bespoke product… the twist product cannot witness failure". False for
   `hU`: what fails at `U = 2·1` is *unitarity*, not effect-ness, so the plain twist product
   witnesses it with `a = b = 1`. Two reviewers compiled that counterexample (`16` vs `4`), so
   **`hU` is CERTIFIED load-bearing**. Only `hb`/`hx` remain weakly tested.

**NEW, adopted: `hU'` was REDUNDANT.** `U * Uᴴ = 1` follows from `Uᴴ * U = 1` by
`mul_eq_one_comm` for square matrices — one assumption stated twice. Removed from
`adU_conj_twistSeq`; the tree already used this move at `KadisonDischarge.lean:444`. A reviewer
notes `adU_isEffect` (`ConjTransport.lean:117`) carries the same redundant pair — **not fixed
here, recorded as a follow-up.** Also adopted: the `hδ` necessity claim had nothing banked behind
it, so it is now the theorem `not_abs_le_of_phase_near_one_without_pos`.

★ **ONE REVIEWER FINDING REJECTED, with evidence — and it is the project's own recurring error,
committed by a reviewer this time.** A reviewer stated that "Mathlib has ZERO results on
compactness of unitary groups (grep = 0 hits), so that leg was a hidden build", and concluded the
compactness route was unsound. The grep is accurate and **the inference is wrong**: the instance
is *in this tree*, vendored at `Vendor/Wigner/UnitaryCompact.lean:141`, it resolves by
`infer_instance`, and `exists_n2Weight_lower_bound` already compiles through it with Lean-core
axioms. **A Mathlib-scoped grep is not a search of the tree** — the same scope error that
produced five false absence claims in this campaign. Reviewers get checked at source too, in both
directions.

**BANKED, from a reviewer, and it is better than my route.** S2 applied at the *single point*
`a = 1` already gives a `δ` uniform in `U`, because `‖adU U (basePt x) − 1‖ = |e^{−x} − 1|` by
unitary invariance of the Frobenius norm — no joint continuity and no compactness needed for that
leg. And replacing `frameProj 0` with the projection onto `(e₀ + i e₁)/√2` yields the explicit
bound `max ≥ 1/(2√2)` from column orthogonality alone, removing compactness from the weight leg
too. **If the assembly is picked up, take that route rather than mine.**

### ★★ WHERE `lem:n2-bounded` ACTUALLY STANDS — and a retraction of my own "one step" claim

**Every ingredient is proved, all Lean-core:** `n2Readout_eq` (with `readout_direct` guarding the
classification chain), `continuousOn_n2Readout` (joint continuity), `n2Comb_eq` (combination =
scalar × pure phase × weight), `n2Weight_pos` and `exists_n2Weight_lower_bound` (weight positive
pointwise, and bounded below on the compact `U(2)`), `abs_lt_of_phase_near_one` (sharp, with
`hδ` certified necessary by the banked `not_abs_le_of_phase_near_one_without_pos`), plus the
in-tree `CompactSpace` instance.

★★ **RETRACTED: I wrote that "exactly one uniform-continuity step" remained and that "nothing but
plumbing" stood in the way. Both overstate. A cold reviewer itemized four gaps, and one of them is
mathematics I had simply not noticed:**

1. ★ **The modulus is never stripped — the real gap.** `n2Comb_eq`'s scalar factor is
   `√(e^{−x})·e^{−itx}`, so bounding `|n2Comb x U − W(U)|` bounds `W·|√(e^{−x})e^{−itx} − 1|`,
   whereas `abs_lt_of_phase_near_one` needs `normSq(e^{−itx} − 1) < 1`. Bridging them needs a
   triangle inequality plus a `δ` small enough that `1 − √(e^{−δ})` eats only part of the budget:
   `|e^{−itx} − 1| ≤ |√(e^{−x})e^{−itx} − 1| + (1 − √(e^{−x}))`. **Nothing in the tree does this,
   and my recorded plan never mentioned it.**
2. **There is no metric to state the comparison in.** `PseudoMetricSpace (Matrix.unitaryGroup
   (Fin 2) ℂ)` does **not** synthesize — verified: `UniformSpace` does, `PseudoMetricSpace` does
   not — so `Metric.uniformContinuousOn_iff` will not typecheck, and my phrase "control at `(x,U)`
   versus `(0,U)` in the product metric" names a metric that does not exist. The step is still
   sound in entourage form (`((x,U),(0,U))` lies in a basic `W₁ ×ᵤ W₂` once `(x,0) ∈ W₁`, by
   reflexivity in the second factor), but that is a filter argument. Cheaper still, per the
   reviewer: a tube-lemma argument from continuity at each `(0,U)` plus `continuous_n2Weight`,
   using no uniform continuity at all.
3. **`n2Comb`'s own continuity is not proved** — `continuousOn_n2Readout` and `continuous_n2Coef`
   exist separately; the sum-of-products has not been assembled.
4. **`Ici 0 ×ˢ univ` is not compact**, so a `ContinuousOn.mono` down to `Icc 0 δ₀ ×ˢ univ` comes
   first; and `ε` must be chosen *after* the weight bound, since it is divided by it.

**Honest status: ingredients complete, assembly is four steps, one of them genuinely analytic.**
"One step, no missing theorem" was wrong — the same overclaim pattern this arc produced repeatedly,
in my freshest prose, caught by review rather than by me.

★ **Two of that reviewer's own claims were retracted by it, confirming rejections I had already
made at source.** It had said the compactness leg was "a hidden build" because Mathlib lacks a
unitary-compactness result, and that no `ℝP²` object exists in Lean. Both wrong: the instance is
vendored in this tree and compiles, and `RP2`/`QubitFrame`/`tauModuli` exist in `RankTwo/`. The
second retraction also **narrowed my own over-correction** — I had written "nor is any `ℝP² → ℝ`
object constructed", which overshot; the accurate statement is that none is constructed *for an
arbitrary product's* `n2FrameTwist`, while `tauModuli` exists for the concrete `τ` family. Fixed
in `FrameConstancy.lean`.

★ **And two findings in that report were already fixed before it arrived** — the stale "assembly
is NOT proved" note and the `frameProj_pairProj_not_commute` "It cannot" inference were both
corrected in `bbb8ee5`; the reviewer was reading `871caa7`. Verified at source rather than
re-applied. **A reviewer reading a stale checkout reports fixed defects as live** — worth pinning
the review to a tag and telling the reviewer which one.

**What remains as review debt, now genuinely narrow.** Only `n2Readout_eq`'s `hb` and `hx` are
weakly tested, and their obstruction is the real one: certifying them needs a *bespoke* product
that agrees with the twist product on effects and differs off them, because for the twist product
itself the identity holds without either hypothesis (a reviewer compiled that). `hU` is certified
and `hU'` is gone. **The rank-two block has now had adversarial outside reading**, so the earlier
instruction to review it first is discharged; what the next arc should review first is whatever
it *builds* first.

**Process note for the next arc, corrected twice by what actually happened.** A narrowly-scoped
reviewer works; a whole-arc brief does not. **Put "call `SendMessage`; your prose is not
delivered" in every brief** — one reviewer's reports "returned success" and still never arrived
until told this, and another sent the same finding four times. Ask for an early interim report,
demand an `ACK` as the *first* tool call, and **never conclude failure from silence**: I twice
declared this channel dead while reviewers were still working, and both times they came back with
findings I could not have produced myself.

**Review protocol (binding).** Three isolated cold reviews: after 6.1(f), after 6.3, and
at end of arc. Each reviewer reads the diffs at source and COMPILES probes
(inert-hypothesis tests; strongest-available probe on any new map — arc-5's was
`n2FrameTwist (twistProductOn t) U = t`); ≤3 fix loops per review; every finding verified
at source before applying OR rejecting (reviewers have been confidently wrong in both
directions, and so have I — twice each, last arc). After every fix round, one diff-audit
pass: read the sentence after every inserted clause, grep each corrected file for the
claim being corrected, and rewrite EVERY summary instance (the fix-the-row rule; six
instances on record). Sub-agents for stuck proofs (repair/golf) are authorized; their
output goes through the same at-source verification.

**Gates per commit — all of them, every commit:** `lake build` green from
`/Users/ehrlich/repos/research/twist-normal-form-lean` (cwd matters: elsewhere `lake env
lean` resolves the wrong toolchain); `AxiomAudit.lean` census PASS with custom axioms
exactly `[]`; `#print axioms` on each new named result = `[propext, Classical.choice,
Quot.sound]`; `THEOREM-MAP.md` and `STATEMENT-MANIFEST.md` row updates in the SAME commit
as the proof they describe; single-sentence commit messages.

**Wall protocol:** a target that resists three genuinely distinct strategies gets its
measured remainder banked HERE — a named missing lemma or a named obstruction, ABSENT vs
BLOCKED vocabulary per the manifest — and the ladder continues. Absence claims carry
their scope and date, always.

**Hard boundaries:** all commits LOCAL (the repo is public; never push, never `sync.sh`);
`main.tex`/`supplementary.tex` and everything outward-facing untouched (frozen tags
inviolate; the supplementary APPLICATION and the Mathlib PR decision stay Bryan-gated);
never claim "fully formalized"; a row counts FORMALIZED only with no located hypothesis
at the article's own generality. Field hazards from arc-5, pre-paid so they cost zero
time now: `fin_cases` produces atoms `rw` cannot match — use `by decide` case
enumeration; one-sided rewrites need `conv_lhs`; the guardrail blocks `git checkout --` —
use `git stash push -- <abs path>`; destructive ops take absolute paths only.

**Expected landing, for calibration only:** a full-yield arc ends in the high teens
FORMALIZED of 36. The number is not the deliverable; the per-row honesty is.

---

## ARC-5 ORDERS (2026-08-08, Fable design pass — the coverage ladder). EXECUTED through 5.3 + cold review 2026-08-08; 5.4/5.5 carried into ARC-6 above; superseded as campaign SSOT.

**The question that produced this arc:** Bryan asked what it would take to reach 36/36 of
the paper's numbered results in Lean, and what the concerns are with setting exactly that
goal.

**Decision record — literal 36/36 REJECTED as the goal (do not re-litigate).** Verified at
source: the final ticks are FIVE separate research-scale programs, four of them other
people's mathematics: `thm:vdw1` (van de Wetering's Jordan representation theorem — the
paper's central import); **JvNW hiding inside `mthm:master`/`mthm:omnibus`** (both are
stated over an abstract simple EJA, so "one theorem at article generality" needs the
Jordan–von Neumann–Wigner classification — the campaign's pre-registered PERMANENT import,
see the target restated above: "Lean core + at most JvNW as disclosed import");
`prop:bridge` (cited external); `prop:theta` at vIR's JB-algebra generality; and the Albert
row's M2 machinery (unscoped since the 08-04 memo — the octonions themselves are NOT the
wall, see the H₃(𝕆) correction below). **Interior honest ceiling ≈ 26–28 of 36.** A 36/36
chased through located hypotheses or disclosed axioms would trade the census (`custom
axioms exactly []`) — the asset's entire distinguishing value — for a number. The count is
a LaTeX artifact (43 environments minus 7 remarks); the census and THEOREM-MAP are the
product.

**EJA-first also REJECTED for this arc.** The abstract-generality gaps an EJA layer closes
are supporting-lemma rows, not headline rows; several "abstract" rows (`lem:span`,
`lem:normality`, `lem:cone-ext`) are stated at ORDER-UNIT-SPACE generality, which the
skeleton already carries — no EJA needed. The EJA/Peirce/symmetric-cone layer remains what
the 07-19 scouting memo said: the high-leverage **Mathlib-upstream** project, run as its
own initiative later, never welded to this paper's count (it also drags toward JvNW).

**THE LADDER (execute in order; on a genuine wall, bank the measured remainder HERE and
continue with the next item — the ARC-4 rule):**

* **5.0 Freeze the denominator — DONE 2026-08-08.** `STATEMENT-MANIFEST.md` exists: all 36
  labels, one-line statements, per-row status and rung target, pinned to `main.tex` blob
  **`205fdf5a`** — which is *byte-identical* at frozen tag `paperA-jpa-submitted` (blog
  `035c337`) and in today's working copy, so the manifest pins one object, not two. The
  36 = 43 environments − 7 remarks derivation is written out and reproducible from a single
  grep. Coverage claims now cite the manifest, so a renumbering can't silently move the
  target. It also computes the ceiling arithmetic: 6 rows are outside this arc by design
  (2 cited external, 2 needing JvNW, 1 needing vIR at JB generality, 1 needing Albert M2)
  ⟹ interior ceiling **30**, realistic **26–28**. No manuscript edit. Side finding, fixed
  in the same pass: the staged supplementary rewrite (blog
  `research/paperA-supplementary-rewrite-draft.md`) still asserted "the octonions do not
  exist in any prover" in two places and "exists in no other proof assistant" for real
  Wigner — the retracted absence claims, sitting in text staged to enter the manuscript.
  Rewritten with their scope attached ("absent from Mathlib, checked 2026-08-08") and the
  ℍ/𝕆 rows changed from "cannot be" to "not built; not known to be out of reach".
* **5.1 Small-lemma tier — PARTLY DONE 2026-08-08, and the rung was mis-billed.** Landed:
  `lem:span`'s two load-bearing clauses at **full abstract order-unit generality**
  (`OrderUnitSpace.span_isEffect_eq_top`, `linearMap_eq_of_eq_on_effects`) — proved from
  order-unit boundedness alone, avoiding the article's norm route, which this interface
  cannot express; and `cor:selectors` **clause (ii)** at the article's own generality
  (`Necessity.selector_traceSymm`: trace-form symmetry makes `-t` a second representing
  parameter, so the classification's `∃!` forces `t = 0`). Also, and for free: the audit
  that writing 5.0 forced found **three rows carried as ABSENT that were already covered** —
  `lem:aone` was FORMALIZED all along (`SequentialProduct.sp_unit_right`, abstract, the
  article's own S1/S3/S4/S6 route), `lem:span` and `prop:pseudo-transfer` were PARTIAL. The
  coverage table drifts in *both* directions; every row now names a declaration or says
  ABSENT.
  **★ The mis-billing, banked: "machinery in hand" is false for the abstract sub-tier.**
  `lem:homog`(ii) and `lem:cone-ext` are stated by the article at EJA generality, so the
  concrete-carrier proofs cannot close them — and the concrete proof runs through
  `sp_smul_of_mem_unitInterval`, whose last step is an ε-squeeze that **is the Archimedean
  property**, which `OrderUnitSpace` does not carry (its `archimedean` field is boundedness
  only). Generalizing is therefore not a variable-block change; it needs Archimedean supplied
  as an explicit `Prop` (legitimate — it is part of the definition of the article's "order
  unit space", not a stand-in for a cited result) threaded through the six-step ladder, and
  `lem:homog`(i) *additionally* needs a positive-linear-extension construction that does not
  exist. Full recipe in `THEOREM-MAP.md` §3b. Not attempted this arc: `lem:normality`,
  `lem:orientation`, `lem:frame-fix` general statement, `cor:selectors` clauses (i)/(iii)
  (clause (iii) is blocked on exactly one absent lemma, `(cfc f a)ᵀ = cfc f (aᵀ)`, recipe
  recorded in `ComplexRowUnconditional.lean`).
* **5.2 Caveat + hygiene closure — DONE 2026-08-08, with one order corrected.**
  (a) **DONE.** `AdjAxis` non-vacuity is now a theorem (`Necessity.adjAxis_not_total`, witness
  `not_adjAxis_one_house`): the Householder reflection in the all-ones direction has every
  off-diagonal entry `-2/N`, so it fixes no axis. The caveat that said this was "asserted in a
  docstring but is not itself a theorem" is retired.
  (b) **RELABELLED after the cold review: this was an UNDERCOUNTED ROW, not new mathematics.**
  `lem:adjacent` is FORMALIZED, but its honest witness is **`frameTwistConst`**, already in the
  tree at tag `paperA-arc4`, which proves `frameTwist` constant across *all* frames — so the
  article's adjacent-frame case follows for any relation whatsoever. The reviewer compiled the
  conclusion of `frameTwist_eq_of_adjBlock` with the hypothesis **deleted**, and again with an
  arbitrary relation in its place. So this row belongs beside `lem:aone` (carried as unproved
  while a proof existed), *not* beside `cor:selectors`(ii) or the rank-two extraction. The
  commit message ("Close lem:adjacent at the article's own frame adjacency") overstates;
  `THEOREM-MAP.md` governs and now says so. `AdjBlock`, `adjAxis_of_adjBlock` and
  `frameTwist_eq_of_adjBlock` stay as documentation of the article's relation in the tree's
  coordinates; they add no provable content.
  ★ **The fidelity note written to justify the row was FALSE.** It said "`AdjBlock` is a
  *superset* of the article's relation, which makes the theorem stronger". Refuted by compiled
  counterexample: the 3-cycle permutation of the standard basis of `ℂ³` has *literally the
  standard frame* as its Jordan frame, yet fails `AdjBlock` — because `AdjBlock` forbids
  relabelling the shared atoms while the article's frames are **unordered** sets of atoms
  (verified at source, `main.tex`:1269–1273). `AdjBlock` is a relation on *labelled* frames,
  neither a superset nor a subset. Never repeat the superset claim.
  `lem:frame-connectivity` remains open and that reason stands: `AdjBlock` is strictly finer
  than `AdjAxis`, so connectivity for it is strictly stronger and needs a Givens/Jacobi
  factorization into rank-two block rotations.
  (c) **DONE.** `THEOREM-MAP.md` §3b now carries rows for `lem:homog`, `lem:cone-ext`,
  `lem:frame-fix`, and `prop:bridge`, so the map covers all 36 like the manifest does.
* **5.3 THE BOULDER — the rank-two classification map. THE INPUT NOW EXISTS (2026-08-08);
  the assembly does not.** Landed: `Necessity.n2FrameTwist : (P : SequentialProductOn
  (H₂(ℂ))) → P.FirstArgContinuous → U(2) → ℝ`, the frame function extracted from an
  **arbitrary** product, plus `n2_sp_eq_twistSeq_frame` — at every ordered frame `U` and
  every nonpositive `r`, `P.sp a b = twistSeq (n2FrameTwist P hS2 U) a b` for
  `a = Ad_U (diagFamily r)` and all effects `b`. Lean-core closure. In
  `Necessity/FrameConstancy.lean`, section `RankTwoExtraction`.
  **★ The pre-registered wall did not bite, and the reason is a corrected diagnosis.** The
  route was billed as needing the frame-function extraction built from scratch because "the
  `N ≥ 3` machinery cannot be reused (`StabilizerCoupling` carries `rank_ge : 3 ≤ n`)". In
  fact only 15 of 76 `Necessity/` modules carry a rank-3 hypothesis and **none of the needed
  pieces is among them**: `prop:theta` on the carrier is rank-free (correctly — unital order
  automorphisms of `H₂(ℂ)` are `O(3)` on the Bloch ball, still `{Ad_U} ∪ {Ad_U∘ᵗ}`; the
  dimension-3 requirement in this area is *Uhlhorn's*, whose hypothesis is weaker), and so
  are `dChi_kills_corner`, `conjProduct`, `sp_eq_twistSeq_transport`,
  `sp_eq_twistSeq_diagFamily`, `tval_antisymm`. The genuinely rank-3-gated step is
  `tvalLm_of_coupling` — the cross-frame constancy, which at rank two is *false*, which is
  exactly why the moduli space is `C(ℝP²,ℝ)` and not `ℝ`.
  **★ And the "lifting step" was never missing.** THEOREM-MAP said Lean "*assumes* `angle` is
  linear … the universal-cover lift `ℝ² → SO(2)` ⟹ linear functional is supplied by the
  paper." But `Necessity.tvalLm` is a **constructed** `(n → ℝ) →ₗ[ℝ] ℝ` with no rank
  hypothesis: the linear functional `n2_necessity` takes as a parameter was already in the
  tree, unused at rank two. The replacement argument is exact and `2π`-free — a linear
  functional on `ℝ²` vanishing on `⟨(1,1)⟩` factors through `r ↦ r 0 − r 1`.
  **Still open, exactly:** boundedness (`lem:n2-bounded`), continuity (`lem:n2-continuity`)
  and frame-reversal invariance/`ℝP²`-descent (`lem:n2-descent`) **of that function**, plus
  `prop:n2-sufficiency` for the reverse direction, before `cor:qubit-classification`
  assembles. Those three are now statements about a function that exists, which they were
  not this morning.
  ★ **Corrected by the cold review: "presentational only" was wrong.** Two real gaps remain in
  `prop:n2-necessity` — `U(2) → S²` is a quotient by the diagonal-phase fibre and nothing proves
  `n2FrameTwist` constant on those fibres, so Lean does not yet have a function of the *ordered
  frame*; and the equivalence between the article's `Θ_a|_{W_n}` form and Lean's product-level
  identity is the route, not a proved statement.
  **Two theorems adopted from the review, both now in the tree:** `n2_every_posDef_effect` (the
  `(U, r)` form covers **every invertible effect**, via the spectral theorem — the section proved
  this but never said it) and ★ **`n2FrameTwist_reverse`**, the **frame-reversal clause of
  `lem:n2-descent` for an arbitrary product**: `n2FrameTwist (U * swapU) = n2FrameTwist U`, so
  the frame function is order-blind and is a function of the *unordered* frame. That clause had
  been banked as remaining boulder work and was mispriced — it is ~35 lines given what landed.
  Open rank-two work is now **boundedness and continuity** of the frame function, plus
  `prop:n2-sufficiency`.
  **Lesson banked:** the old entry inferred "the classification map does not exist in Lean at
  all" from `grep -c SequentialProductOn RadicalRelativity/RankTwo/*.lean` → 0. The grep was
  accurate; the inference was wrong, because the map got built in `Necessity/`. Scoping an
  absence claim to a *directory* is the same error as scoping one to a library — the third
  instance of this failure in a week.
* **5.4 The differential trio.** `lem:homomorphism` (differentiate Θ in the matrix
  argument; prove `dχAdd` IS its derivative — the development currently *begins after*
  this transition), `lem:coalescence` identification, `prop:stabilizers` construction.
  Wall: Fréchet machinery on the carrier (a normed space, so Mathlib `fderiv` applies).
  Fallback: pointwise-derivative version, banked.
* **5.5 STRETCH — the ℍ row.** Route per the 08-06 correction: `H_n(ℍ) ↪ H_{2n}(ℂ)` as
  fixed points of a conjugate-linear involution (ℍ is not `RCLike`; that, not missing
  quaternions, is the blocker). Quaternionic Wigner may fall to the RealWigner rank-one
  technique. This is plausibly its own arc; any progress banks.

**Constraints (welded, not advisory):** a result counts FORMALIZED only with no located
hypothesis standing in for a cited result, at the article's own generality; custom axioms
stay exactly `[]` and the census+manifest run green at every commit; the THEOREM-MAP row
updates in the same commit as each proof; never write "fully formalized"; all commits
LOCAL (public repo, push Bryan-gated, NEVER sync.sh); manuscript, `upstream/` submission,
and everything outward untouched; T1/T2 PARKED; JMP RESERVED; frozen tags never touched.
End of arc: ONE isolated cold review of the arc's diffs against a frozen tag (ARC-4
pattern — it earned its keep), then compact this ledger's arc narrative.

**Expected movement if no wall bites:** 5/36 → ~14 after 5.1–5.2 → ~21 after 5.3 → ~24
after 5.4; the stretch adds ~1 plus a first-party quaternionic Wigner. Unlike ARC-4 (six
bounded refactors, one hour), 5.3 and 5.4 are NEW MATHEMATICS in Lean — expect walls, use
the fallbacks, report the remainder honestly.

**ACTUAL after 5.0–5.3 (2026-08-08): 5/36 → 7/36 formalized, 19 partial, 10 absent.** Short
of the ~14 projection, and the reason is a repricing, not a shortfall in effort: the 5.1
projection assumed the abstract sub-tier was mechanical, and it is not (the Archimedean
finding above). Two rows moved to FORMALIZED (`lem:aone`, by audit; `lem:adjacent`, by
proof), one row gained a clause at article generality (`cor:selectors`(ii)), one row was
upgraded from concrete to fully abstract (`lem:span`'s two load-bearing clauses), two rows
were corrected upward from ABSENT to PARTIAL, and two caveats were retired
(`AdjAxis` non-vacuity; the frame-adjacency mismatch, now narrowed to `lem:frame-connectivity`
alone). Every gate green throughout: `lake build` 3106 jobs, census 149 modules, **custom
axioms exactly `[]`**, every new declaration's closure = the three core axioms.
The count understates 5.3: the rank-two frame function is a new *capability* rather than a
row, and it is the input every remaining rank-two row consumes. Three superseded claims were
corrected on the record in the process (the abstract tier is not mechanical; `AdjBlock` is
finer than `AdjAxis` so connectivity does not follow; the rank-two lifting step was never
missing).

Commits: `6f2442a` (5.0) · `51cfbb9` (coverage corrections) · `287cff3` (selector ii) ·
`4e12d84` (abstract span + AdjAxis non-vacuity) · `88aba62` (article adjacency) · `9248f3d`
(5.2 close + 5.1 repricing) · `5e3e3e5` (5.3 rank-two extraction); blog `650aa12` · `326aedb` ·
`8900e4b` · `168e9a7` · `174e3ff` · `2d2c6cc`.

## ARC-5 COLD REVIEW — RAN, and it earned its keep twice over

One isolated adversarial reviewer, given frozen tag `paperA-arc5-review` @ `5e3e3e5`, read-only,
told to write its own Lean probes and to refute rather than confirm. It compiled six probe files
and re-ran both gates itself. Outcome:

**CONFIRMED, by its own compiled probes, not by reading:**
* `selector_traceSymm` — and it went further than asked: it proved the Lüders product *satisfies*
  trace symmetry (class inhabited), that the selector returns `t = 0` on it, and **that for
  `t ≠ 0` the twist product provably does NOT satisfy trace symmetry** — so the hypothesis is
  genuinely selective. That sharpness check was not in the orders and should have been.
* `adjAxis_not_total`, the abstract `lem:span` proof, `cornerJ2_all`, `n2_tval_eq`, and the
  arithmetic 7 + 19 + 10 = 36 against the manifest row by row.
* ★ **The crown probe on rung 5.3: `n2FrameTwist (twistProductOn t) U = t` for every `U`.** The
  extraction returns the *expected* parameter — no sign error, no factor of two, no frame
  confusion. This is the strongest available confirmation that `n2FrameTwist` is the right map and
  that its hypothesis class is inhabited at `N = 2`.
* `lem:aone` FORMALIZED — it read all nine fields of `SequentialProductCore` to confirm
  `sp a ousUnit = a` is not among them, i.e. genuinely derived rather than restated.

**REFUTED, both by compiled counterexample, both mine, both now corrected above:**
1. `lem:adjacent`'s adjacency hypothesis is **inert** (`frameTwistConst` already gave global
   constancy at the previous tag) — so 5.2(b) was an undercounted row, not new mathematics.
2. The "`AdjBlock` is a superset of the article's relation" fidelity note is **false** (3-cycle
   counterexample; the article's frames are unordered).

**OVERSTATED, corrected:** "full order-unit-space generality" for `lem:span` (the *interface*
extends `NormedAddCommGroup`, so the statement presupposes a norm even though the proof never
touches one); "presentational reason only" for `prop:n2-necessity` (the `U(2) → S²` phase fibre is
a real gap).

**MISPRICED IN THE CHEAP DIRECTION — and it just did the work:** the frame-reversal clause of
`lem:n2-descent` was banked as boulder work; the reviewer proved it for an arbitrary product in
~35 lines. Adopted as `n2FrameTwist_reverse`, with `n2_every_posDef_effect` alongside it.

**Three same-file contradictions found — the project's documented failure mode, and this diff
created them** (a summary cell and a note in the same file that cannot both be true):
`THEOREM-MAP.md`'s rank-two summary still said the extraction "remains" 60 lines below the
correction saying it exists; `LEDGER.md`'s `cor:qubit-classification` cell still said the map was
ABSENT; and `THEOREM-MAP.md` §3 ("no Lean counterpart") still listed `lem:n2-descent` and
`lem:n2-continuity`, which the manifest rates PARTIAL — taken literally the *governing* file
implied 7/17/12 against the manifest's 7/19/10. All three fixed. Plus two lint warnings the
reviewer caught in `adjBlock_one_house_pair`, also fixed.

**Could not check, flagged honestly:** the reviewer had no access to the blog repo, so every
"at the article's own generality" judgement it saw rested on the manifest's paraphrases. It asked
for finding 2 above to be re-checked against `main.tex`:1269 directly — **done, at source, and
the reviewer was right.**

**Rungs 5.4 (differential trio) and 5.5 (ℍ row) NOT STARTED.** They remain as written above.
5.4's `lem:homomorphism` is worth re-checking against the same lesson that just paid off
three times: read what `dChi`/`chiTilde` actually prove before accepting "Lean never
differentiates Θ" — `chiTilde_eq_exp_dChi` exists and is used by `dChi_kills_corner`, so the
exponential/differential relationship is at least partly in the tree already.

---

## ★★ ARC-4 RESULT (2026-08-08) — **the asset is truthful, sharper, and PR-staged. All six items landed.**

Gates at the end of the arc: `lake build` green at **3106 jobs**; `AxiomAudit.lean`
PASS at **149 tracked modules** (== frozen 149-name manifest); **custom axioms exactly
`[]`**; every tracked persisted declaration's closure ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}. All commits LOCAL. Frozen tags: `paperA-arc4-review` @ `7cdf690` (the state
the cold review read) and **`paperA-arc4` @ `53b32ee`** (the arc's final state, after the
review-driven fix below).

Commits: `8727fff` (4.1) · `0d2fec9` (4.2) · `3f89c8f` (4.3) · `7cdf690` (4.4) ·
`f4deb30` (4.6 compaction) · `0e1c366` (4.6 review fix) · `53b32ee` (4.6 review record);
blog `fb65b07` (4.5) · `f1a79b6` · `12e7c24`.

**The tree carries zero `sorry`.** The only two occurrences of the token live inside a
comment block in `Vendor/Misc.lean` (illustrative code for what those declarations should
become once a Mathlib `ConditionallyCompleteLattice` diamond is fixed) — they are not
declarations and reach no proof. Soundness of the tree and *coverage of the article* are
different questions: see the coverage count below.

**4.6 cold review — RAN, and it earned its keep.** One isolated adversarial reviewer, given
the frozen SHA and told to write its own Lean probes. It confirmed the 4.2/4.3 diffs on every
vector it checked — round-tripping both `_ouNorm` rows back to the originals, composing each
converse into its forward theorem, showing `ContinuousOnOu` on `univ` forces genuine global
continuity (so it is not satisfiable by a pathological map), showing the `√(card n)` factor
is *necessary* (`‖1‖ = √2 > 1 = ouNorm 1` on `H_2(ℝ)`) and *optimal*, checking that the
refactored Jordan capstones still prove their pre-refactor statements verbatim, and
exhibiting `O = !![2]` to show the orthogonality hypothesis in `orthConj_one` is
load-bearing rather than a `simp` artifact. **And it found one real defect** — see 4.3.

**4.1 Truth sweep — DONE, and it found more than the orders listed.** Six stale
docstrings, not four: the four named plus `RealRigidity.lean:209` ("real Kadison being
unavailable in any prover") and `RealProjectionOrder.lean:29` ("the two-case argument is
the remaining step" — it is `rankOneR_isAtom`, in the same file), plus the root import
comment calling `prop:real` "in progress", plus `THEOREM-MAP.md`'s own real-row preamble,
which said the ℝ Jordan property is "carried, not derived" while its own table two lines
below said the row is unconditional. **`RealWigner.lean` de-vendored** to
`RadicalRelativity/Wigner/RealWigner.lean`; its `Vendor.Wigner.TransitionProbability`
import was dropped and replaced by two Mathlib imports, confirming the audit's
declaration-level finding that the import was dead. README now has a provenance section
naming Meiburg / Lessa / Blore with upstream pins and line counts (41,135 total, 12,409
vendored), a directory-level completion of the module map (the old map listed ~25 of 147
modules), and `master_chain` is billed as an abstract skeleton rather than a capstone.
`VENDOR.md`'s stale "one disclosed axiom" / census-44 lines are annotated, not rewritten.

**4.2 S2 order-unit-norm bridge — DONE, and it closed the caveat for the necessity
direction, not just for sufficiency.** New module `Necessity/OrderUnitS2.lean`. The
insight that made it tractable: `ContinuousOn` *cannot* express order-unit-norm continuity,
because the carrier has exactly one `TopologicalSpace` instance and it is the Frobenius
one — so the paper's S2 has to be written out in ε–δ form against `ouNorm` on both sides
(`HermitianMat.ContinuousOnOu`) and proved equivalent
(`continuousOnOu_iff_continuousOn`, from the two-sided sandwich, one ε-rescaling in each
direction). `abs_eigenvalues_le_ouNorm` and `norm_le_sqrt_card_mul_ouNorm` were ℂ-only
and are now `RCLike 𝕜`-general (one-token change; they never used ℂ). Both rows are
restated with the paper's S2 verbatim: `real_classification_ouNorm`,
`complex_classification_unconditional_ouNorm`, both Lean-core.
`twistProductOn_firstArgContinuousOu` pins the hypothesis class inhabited.

**4.3 Kadison classifications EXPOSED — DONE, and the ℝ one is EXACT.**
* ℝ: `orderAutoR_eq_orthConj` — every unital order-automorphism of `H_N(ℝ)` **is** `Ad_O`
  for an orthogonal `O`. `orderAutoR_preservesJordan` is now a two-line corollary of it.
  **Plus the converse** (`orthConj_le_iff`, `orthConj_one`, `orthConj_surjective`,
  packaged as `orthConj_orderAuto`), so the order-automorphism group of `H_N(ℝ)` is
  characterized as exactly `{Ad_O : OᵀO = 1}`, not merely embedded in it.
* ℂ: `orderAuto_classification` — `∃ U, UᴴU = 1 ∧ (Φ = Ad_U ∨ Φ = Ad_U ∘ ᵗ)`. Landed by
  extracting the rank-one agreement each Wigner branch already established
  (`agrees_unitaryConj_of_rayMap_eq_projMap`,
  `agrees_antiunitaryConj_of_rayMap_eq_projMap_conj`) and drawing *two* conclusions from
  it instead of one. No proof was weakened: the old `preservesJordan_of_*` theorems are
  now one-liners over the extracted lemmas.
* **BOTH classifications are EXACT** (`orthConj_orderAuto` over ℝ;
  `unitaryConj_orderAuto` + `antiunitaryConj_orderAuto` + `orderAuto_classification_realized`
  over ℂ), so each order-automorphism group is *characterized*, not merely embedded.
  ★ **The ℂ antiunitary converse landed only because the cold review refuted me.** I wrote
  that it was blocked on a "`PosSemidef`-under-transpose lemma Mathlib does not have"; the
  reviewer grep-checked and produced a compiling proof — `Matrix.posSemidef_transpose_iff`
  is in Mathlib (`LinearAlgebra/Matrix/PosDef.lean:91`) and the branch follows in a dozen
  lines. **Lesson, now binding: a claimed library obstruction is a claim. Grep the library
  before writing "Mathlib does not have X" into a docstring** — the cost of being wrong is
  that real work gets deferred as impossible.

**4.4 Real-Wigner Mathlib PR package — STAGED in `upstream/`, NOT SUBMITTED.**
`upstream/Wigner.lean` (Mathlib naming, Mathlib-shaped docstring, Mathlib license header)
compiles with **zero warnings under `-Dlinter.mathlibStandardSet=true`**; the `longLine`
suppression turned out to be vestigial (no line exceeds 100 *characters* — the earlier
count was bytes). Verified by diff that the PR copy and the in-tree twin differ only in the
capstone docstring. `upstream/README.md` records the collision check with evidence:
**Mathlib master has no Wigner's theorem and no Uhlhorn in any field** (the one `wigner`
hit is the unformalized *Wigner–Eckart* wishlist entry in `docs/1000.yaml`), `zblore/csd-lean4`
is ℂ-only with no real track in its backlog, `physlib` has nothing. Best argument for the
PR, found while checking: **the real case needs no missing Mathlib prerequisites** — it
imports `Analysis.InnerProductSpace.PiL2` and `LinearAlgebra.Projectivization.Basic` and
nothing else, where the ℂ case needs projective topology plus Fubini–Study measure theory.
Pre-submission list (rebase onto master; add `wigner1959`/`uhlhorn1963` to
`docs/references.bib`, which currently has neither; agree the file path; contact the ℂ
author) is in that README. `upstream/` is outside the census and outside `lake build` by
construction, and says so.

**4.5 Supplementary rewrite DRAFT — DONE**, blog `research/paperA-supplementary-rewrite-draft.md`.
Manuscript untouched. **The 5/17/14 coverage split was re-derived independently and agrees
with the 08-08 audit exactly** (36 = the 43 numbered environments minus 7 `remark`s, which
share the theorem counter): formalized = `prop:real`, `thm:complex`, `prop:per-frame`,
`prop:singular`, `lem:twist-sufficiency`. Both flagship rows are FORMALIZED **at the
article's own generality** — verified at source: the article states `prop:real` on
`H_n(ℝ)`, `n ≥ 2` (Lean: `0 < N`) and `thm:complex` on `H_n(ℂ)`, `n ≥ 3` (Lean: `3 ≤ N`).
The draft itemizes eight stale/false disclosure claims with line numbers, the five fidelity
caveats, and the re-pin off `b7db3e8`.

**Banked follow-ups (small, ordinary, not blocking anything):**
1. `AdjAxis` non-vacuity is asserted in a docstring but is not a theorem of the tree. The
   arc-3 reviewer proved `¬ AdjAxis 1 cycU` in a scratch file; making that an in-tree lemma
   would turn the last load-bearing prose assertion in the ℂ row's story into a proof.
2. ~~The ℂ antiunitary converse~~ — **CLOSED 2026-08-08** by the cold review's refutation;
   see 4.3 above. Left listed so the correction is visible, not silently dropped.
3. `THEOREM-MAP.md` cites only 20 of the paper's 36 labels; 4 more have Lean counterparts
   under unlabelled names (`lem:frame-fix`, `lem:coalescence`, `lem:homog`, `prop:bridge`
   appear in `.lean` docstrings but not in the map). Adding those rows would make the map's
   own coverage match the tree's.
4. `upstream/` and the in-tree twin are two copies of one proof with nothing enforcing
   sync; regeneration is five `sed` substitutions, recorded in `upstream/README.md`.

---

## ★★ ARC-4 ORDERS (2026-08-08, Fable handoff — Bryan funded a second 18h Opus arc)

**Provenance.** Tri-agent adversarial audit 2026-08-08 (isolated cold agents:
coverage, upstream, holistic skeptic; all reviewed frozen `ba317b8`; key claims
re-verified at source by the orchestrator). Verdicts that bind this arc:

- **"Fully formalized" is FALSE and must never appear in prose.** ★ The counts in this
  ARC-4-era bullet (5 / 17 / 14) are **STALE — current is 8 / 19 / 9**, see
  `STATEMENT-MANIFEST.md`. The *rule* stands; the numbers do not. (Flagged by the ARC-6 cold
  review: the rule is phrased so a reader grepping for it lands on stale figures.) What IS
  banked survived a hostile audit untouched: both flagship rows unconditional,
  Lean-core closure re-verified by the auditor's own scratch probes, zero live
  sorry, zero axiom declarations tree-wide.
- **The campaign's original target (this file's "Target restated," all four
  rows + omnibus) is SUPERSEDED — unreachable on any controlled timeline**
  (ℍ needs quaternionic Wigner, 𝕆 needs octonions; neither exists in any
  prover). No new rows. Marginal Lean toward the old target ≈ 0.
- **Every disclosure surface understates the tree** (paper pins `b7db3e8` =
  07-19 skeleton, 27 files; supplementary claims two `axiom` declarations that
  are now theorems). All overstatement risk is internal; all public staleness
  is in the understating direction.
- **Upstream: one clear YES (real Wigner, S-friction), real Kadison behind it
  (M).** A third of the tree (12,409 L) is Meiburg's/Blore's, both already on
  their own Mathlib tracks — not ours to PR. ITP/CPP paper: skip.

**ARC-4 GOAL: convert the verified asset into a truthful, sharper, ship-ready
one.** Six items, in order. All commits LOCAL. Outward actions (push, PR
submission, manuscript edits, sync.sh) remain Bryan-gated and OUT OF SCOPE.

### 4.1 Truth sweep (docs only; ~3h)
- `Vendor/Wigner/RealWigner.lean:14-33` — header still says the rigidity is
  unproved and needs a bijection; the file proves the full theorem at :1041
  with no bijectivity hypothesis. Rewrite.
- `Necessity/RealRigidity.lean:35-38` — "real Kadison/Uhlhorn is not available
  in any prover" is FALSE in this tree (`RealKadison.orderAutoR_preservesJordan`,
  discharged into the row via `RealRowUnconditional.thetaPreservesJordanR_of_S2`).
- `MasterTheorem/Interface.lean:195` — "no concrete instance is constructed in
  this tree" is FALSE since `Necessity.comparisonSetup`
  (`ComparisonInstance.lean:363`, 08-05).
- `THEOREM-MAP.md:~380-395` — the n2-descent entry contradicts its own ★ note:
  descent is machine-checked for the CONCRETE Bloch example only; the
  classification map does not exist (`grep -c SequentialProductOn RankTwo/*.lean`
  = 0 across all seven files, verified). Make the ★ note's reading govern the row.
- `README.md` — add a Vendor/provenance section pointing at
  `RadicalRelativity/Vendor/VENDOR.md` and naming Meiburg (physlib @ `ad1d812`),
  Blore (csd-lean4 @ `2287f45`), Lessa (`Proj.lean`); grep for any residual
  "capstone" billing of `master_chain` and align with THEOREM-MAP §3.
- `Vendor/VENDOR.md:31-45` — "the one disclosed axiom" / census-44 lines are
  stale; annotate (axiom discharged 08-05, `Necessity/OneParameter.lean:220`;
  custom axioms now exactly []). Annotate, don't rewrite history.
- **De-vendor RealWigner**: move `Vendor/Wigner/RealWigner.lean` (Bryan's
  copyright, misfiled) to `RadicalRelativity/Wigner/RealWigner.lean`; drop its
  only import (`Vendor.Wigner.TransitionProbability` — VERIFIED dead at
  declaration level: zero island declarations, zero instances, zero
  topology/measure used; the one grep hit is docstring prose) and let the
  compiler dictate the replacement Mathlib imports. Update root imports,
  `AxiomAudit.lean` manifest (module rename), and every importer
  (grep `Vendor.Wigner.RealWigner`).

### 4.2 S2 order-unit-norm bridge (~2h)
The auditor's one real fidelity gap: `FirstArgContinuous` is `ContinuousOn` in
the CARRIED norm; the paper's S2 is the ORDER-UNIT norm. The two-sided bound
(`ouNorm ≤ ‖·‖ ≤ √(card n)·ouNorm`, `Hermitian/OrderUnit.lean`) is proved but
never converted into a `ContinuousOn` equivalence. Prove the bridge (equivalent
norms ⇒ same topology ⇒ same `ContinuousOn`) and add wrapper capstones
(`real_classification_ouNorm`, `complex_classification_unconditional_ouNorm`)
whose hypothesis is order-unit-norm continuity verbatim. `twistSeq_continuousAt_ouNorm`
already exists as material. New module → root import + AxiomAudit manifest.

### 4.3 Expose the Kadison classifications (~4-5h)
Both proofs derive the classification internally and discard it, exposing only
`PreservesJordan`. State it: ℝ (`Necessity/RealKadison.lean`) — ∃ orthogonal U,
Φ = Ad_U; ℂ (`Necessity/KadisonDischarge.lean`, rewire
`preservesJordan_of_rayMap_eq_projMap`/`_conj` at :159/:223 to surface the
witness from `rayMap_dichotomy` :102) — ∃ unitary U, Φ = Ad_U ∨ Φ = Ad_U∘transpose.
Converse witnesses already exist (`JordanWitness.lean:59,111,126`,
`RealJordanWitness.lean:61`) — package the iff if cheap. Strengthens the banked
theorem AND is the statement shape Mathlib demands. If a genuine wall: bank the
measured remainder here and move on.

### 4.4 Real-Wigner PR package (staged at the gate; ~3-4h)
On the de-vendored file: Mathlib-idiom rename pass (kill the `R` suffixes),
longline fixes, standalone PR-shaped copy + PR description in `upstream/`
(new dir, in-repo). MUST include collision check against Mathlib master and
`zblore/csd-lean4` and `leanprover-community/physlib` (read-only web/GitHub —
Blore's `WignerRigidity.lean:190-195` self-stages the ℂ side; his header cites
a v4.33 `Projectivization/Topology.lean` that may have landed). Prepared answer
for the inevitable reviewer question "unify over RCLike": over ℝ there is no
antiunitary branch; the ℂ case belongs to its own author. NO submission — the
package parks at Bryan's gate.

### 4.5 Supplementary §S1/§S3 rewrite DRAFT (~3h)
Staged in the BLOG repo as `research/paperA-supplementary-rewrite-draft.md`
(draft, NOT applied — `main.tex`/`supplementary.tex` are Bryan-gated). Contents:
corrected "What Is Machine-Checked" + "Lean skeleton" sections against the
arc-4 final SHA; the honest 5/17/14 coverage table; axiom-claims corrections
(zero axioms; Aczél + BGW now theorems; vIR DERIVED for both rows); re-pin
instruction (fresh frozen tag replacing `b7db3e8`); the auditor's fidelity
caveats stated once each (OrderUnitSpace `archimedean` = boundedness;
`AdjAxis` ≠ the paper's frame graph, discharges the same residue; `sp_effect`
as field). Never "fully formalized."

### 4.6 Compaction + gates + cold review (~1h)
Compact this file's M1–M7 history (keep top blocks, six-targets table, arc
records; archive the rest — THEOREM-MAP is the asset). Full gates after 4.1–4.3:
`lake build` green + `AxiomAudit` custom axioms exactly `[]`. Freeze a SHA and
run ONE isolated cold review over the 4.2 + 4.3 diffs (machine-checked probes
allowed, scratchpad only). Bank everything; single-sentence local commits.

**OUT OF SCOPE (do not relitigate):** ℍ/𝕆 rows, rank-two classification map,
`prop:central` discharge, `mthm:omnibus`, any manuscript edit, any push/PR
submission, T1/T2 (PARKED), the frozen tag `paperA-jpa-submitted`.

---

## ★★ ARC-3 RESULT (2026-08-07) — **THE ℂ ROW IS HYPOTHESIS-FREE. GOAL MET.**

`Necessity.complex_classification_unconditional` (`Necessity/ComplexRowUnconditional.lean`)
carries exactly `{3 ≤ N, P : SequentialProductOn (HermitianMat (Fin N) ℂ), hS2}` — verified by
`#check`, not prose — and `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Gates at the end of the arc (all four units in): `lake build` green **3105 jobs**,
`AxiomAudit` PASS at **148** tracked modules, custom axioms exactly `[]`.

**What was built** (three new modules, 811 lines, no new capstone — the existing one was
instantiated, exactly as the attack plan called for):
* `Necessity/FrameConstancy.lean` — `sp_eq_twistSeq_frame` (the workhorse: `ComplexMaster`'s
  chain with the frame a FREE parameter, not `a.H.eigenvectorUnitary` — this is the unlock,
  and it worked because `sp_eq_twistSeq_transport` already took the unitary as a parameter);
  `twistSeq_adU_mat` / `twistSeq_eq_of_adU` (conjugation cancels); `star_phase_factor`,
  `exp_eq_of_twistSeq_diagFamily_eq`, `twist_param_unique_of_scaled` (uniqueness against a
  prescribed scaled family — `twist_param_unique` generalized from its fixed probe);
  `axisSplit`, `AdjAxis`, `diag_commute_of_axis`, `adU_eq_of_commute`,
  **`frameTwist_eq_of_adjAxis`** (cross-coherence).
* `Necessity/UnitaryGeneration.lean` — `axisVec` helpers; `AxisFixing`, `axisFixing_of_col`;
  `nrm2` (squared norm as a real, so no square root enters the reflection); `lineProj`,
  `house` and its involution/Hermitian/unitary lemmas; `house_axisFixing` (a reflection fixes
  every axis its vector misses — the fact that makes reflections usable as adjacency steps);
  `house_mulVec_align`; `exists_alignTarget`; `exists_align_off_axis`;
  `exists_clear_column`; **`exists_axisFixing_factor`**; **`adjAxis_connected`**.
* `Necessity/ComplexRowUnconditional.lean` — **`frameTwistConst`**,
  **`complex_classification_unconditional`**, plus two **in-tree non-vacuity certificates**:
  `twistProductOn_classified` (the hypothesis class is inhabited — `3 ≤ N` + S1-S7 + S2 are
  simultaneously satisfiable, witnessed by M1's twist product, so the row is not vacuous) and
  `complex_classification_sharp` (run the capstone on `twistProductOn t` and the unique
  parameter it returns is `t` itself — the twist family is faithfully parameterized and the
  `∃!` is not met by some unrelated value). These answer the vacuity question *in the tree*
  rather than by argument, which is the same discipline that killed the OpCommute escape class.

**Design decisions that mattered, for anyone extending this:**
* Adjacency was defined as "`F* G` fixes a coordinate axis" (`AdjAxis`), NOT as the general
  coordinate-splitting relation the plan sketched. The two-level spectrum `axisSplit m` is
  all the cross-coherence argument needs, and the singleton form makes both the commutation
  check and the Householder connectivity argument shorter.
* Connectivity went through **Householder reflections**, not Givens rotations. A reflection
  whose vector has one zero coordinate is automatically axis-fixing, so an *arbitrary*
  reflection can be an adjacency step; that turns the plan's "~150-300 line elementary
  induction" into a fixed 2-step column clear with no induction at all. Within the NEW material
  `N ≥ 3` is needed in exactly one place — it frees the axis the second reflection's vector must
  miss (three distinct indices in `exists_clear_column`). Precision: the row as a whole needs
  `N ≥ 3` for a second, PRE-EXISTING reason as well, namely the per-frame theorem
  `complex_perFrame_unconditional`, which is the paper's own rank-≥3 hypothesis. So do not read
  "enters exactly once" as "the ℂ row would work at `N = 2` but for connectivity" — it would
  not, and rank two is a genuinely different theorem (`cor:qubit-classification`).
* Two `rw`-nesting traps cost time and will recur: rewriting `v` inside a term that also
  *defines* the reflection vector (fixed by proving linearity as a separate `have` instead of
  rewriting `v`), and `rw [← hsp]` reaching inside `√(normSq …)` (fixed by obtaining the
  square roots opaquely via `obtain ⟨b, hbne, hb⟩`).
* `frameTwistConst` needs `intro F G` + explicit `(Adj := …) (t := …)`; term-mode with
  implicit unification times out at `whnf` on `frameTwist`'s `Classical.choose` body.
* ★ **A prediction in the ORDERS below was WRONG, and the record must not imply otherwise.**
  The orders said `frameTwist_unique` (built 08-06) would be the tool that ties the transported
  parameter to `frameTwist` "without fighting `choose`". **It is not used at all** — verified by
  grep: nothing outside its own definition site references it. The reason is that the winning
  route compares PRODUCT VALUES (`twistSeq t_F a b = twistSeq t_G a b`, then strip the
  conjugation and probe) rather than comparing stabilizer couplings, so `choose` never had to
  be fought: `frameTwist_spec` is applied at each frame separately and the two conclusions are
  chained through `P.sp a b`. `frameTwist_unique` remains a true and worthwhile theorem — it is
  what makes `frameTwist` an invariant rather than a choice artefact — but it is **not
  load-bearing for the unconditional capstone**, and anyone budgeting future work should not
  assume the coupling-comparison route was the one that worked.

**Item 7.3 (statement layer) — also DONE for the ℝ and ℂ rows.**
`RadicalRelativity/PaperA/CertifiedConfiguration.lean`: both reference maps instantiated
concretely with effect closure proved, the pinned-product→class bridge built, and both frozen
shapes discharged (`PaperA.real_meets_ludersConclusion`,
`PaperA.complex_meets_uniqueTwistConclusion`, both Lean-core). Final gates: `lake build` green
**3105 jobs**, `AxiomAudit` PASS at **148** modules, custom axioms exactly `[]`. See item 7.3
in the roadmap below for what is still open there (ℍ/𝕆 shapes, README, paper §App).

**★ COLD ADVERSARIAL REVIEW (2026-08-07, isolated agent, refute-first charter): ALL SIX ATTACK
VECTORS SOUND; verdict "the claim is justified as stated."** Vectors run: vacuity, circularity,
junk/stub, conclusion strength, the interval argument, `N ≥ 3` usage. What it independently
machine-checked rather than argued: `AdjAxis` is satisfiable (`AdjAxis F F`) **and not total**
(`¬ AdjAxis 1 cycU` for the 3-cycle permutation unitary on `Fin 3`) — so connectivity is real
content, not a disguised tautology; and `frameTwist hN (twistProductOn t) _ U = t` at EVERY frame,
so `frameTwist` computes the right number on a known model rather than being a `choose` artefact.
It confirmed no `sorry`/`axiom`/`native_decide` anywhere in the closure, that the conclusion has
no `PosDef` (all effects, singular included, and the invertible→all step is genuine density plus
S2), and that `ExistsUnique` is the real thing. Three DOC-ONLY items were raised and all three
are now FIXED in the source:
* the file-header gloss "which is why the family, and not a single base point, is the object
  being compared" overstated: that is true of THIS probe (one entry ⟹ one phase equation ⟹ mod
  `2π/Δ`), not a mathematical necessity — for `N ≥ 3` a single base point with incommensurable
  gaps read at two index pairs would also force exactness. Reworded; **if that sentence ever
  migrates into the manuscript, weaken it to "a single phase equation cannot pin `t`."**
* the `Adj := True` instantiation LOOKS like it assumes connectivity away. It does not, and the
  ORDERING is what makes it non-circular: constancy is established first from the genuine
  `AdjAxis` walk, and only then is the capstone reused with the cheapest adjacency. Now
  pre-empted in `ComplexRowUnconditional`'s docstring — say this before a referee asks.
* `a^{1/2+it}` at singular `a`: under Lean's `Real.log 0 = 0` the factor vanishes on the kernel,
  which is the intended continuous extension. Now stated in the docstring.
**The one seam no `#print axioms` can certify** (reviewer's words, and correct): "hypothesis-free"
means free relative to the Lean ENCODING of van de Wetering Def 2 — `SequentialProductOn`
(S1, S3-S7, plus `sp_effect` as codomain) + `FirstArgContinuous` as S2. That mapping is a human
judgment. The reviewer read it as faithful. This is the honest residue of the whole campaign and
must never be described as machine-checked.
**PROCESS LESSON (cost the reviewer a re-read):** the tree moved under the cold reviewer mid-review
(HEAD advanced and `ComplexRowUnconditional.lean` gained the two non-vacuity certificates between
its first read and its greps), so its verdict was briefly about a state that no longer existed.
**Freeze the tree or hand the reviewer a tag/SHA next time** — do not run a cold review against a
live edit session.

**ARC-3 SCORECARD.** U1 cross-coherence ✓ · U2 connectivity ✓ · U4 capstone ✓ · U5 statement
layer ✓ (ℝ/ℂ). Nothing in the arc hit a wall; no out-of-scope row was touched. Total: five new
declarations of record (`sp_eq_twistSeq_frame`, `frameTwist_eq_of_adjAxis`, `adjAxis_connected`,
`frameTwistConst`, `complex_classification_unconditional`) plus the statement-layer pair.

---

## ARC-3 ORDERS (2026-08-07, Fable handoff — Bryan funded 18h of Opus and delegated scoping)

*All four units (U1, U2, U4, U5) are DONE — see the RESULT block above, which supersedes the
attack plan below wherever they differ (notably: Householder rather than Givens for
connectivity, and axis adjacency rather than the general splitting relation). This block is
retained for its SCOPE DECISIONS, which still bind, and as the record of what was planned
versus what the mathematics actually wanted.*

**THE GOAL OF THIS ARC:** make the ℂ row hypothesis-free. Deliver
`Necessity.complex_classification_unconditional` whose signature carries ONLY
`{3 ≤ N, P : SequentialProductOn (HermitianMat (Fin N) ℂ), hS2 : P.FirstArgContinuous}`
and concludes `∃! t, ∀ a b effects, P.sp a b = twistSeq t a b`. Then re-point the
certified-configuration statement layer (item 7.3) at the ℝ and ℂ capstones. Verify with
`#check` + `#print axioms` in-transcript; both gates green after every unit.

**SCOPE DECISIONS, made under delegated authority — do not relitigate this arc:**
* ℍ refactor: DEFERRED. Even after the 7-file abstract-carrier lift, the row needs
  quaternionic Wigner rigidity — a second from-scratch classical theorem. Cannot close in
  any near window; the refactor's real payoff (ℝ/ℂ/ℍ as one theorem) is post-submission work.
* H₃(𝕆): out of scope (no octonions in any prover — separately fundable program).
* `prop:central`, rank-two classification map: out of scope (open mathematics).
* Standing gates unchanged: all commits LOCAL, no push, no sync.sh, frozen tag untouched,
  JMP reserved, T1/T2 parked.

**THE ATTACK PLAN (verified against source 08-07 — every named ingredient exists):**
The capstone `complex_classification` already takes `(Adj, connected, overlap)`. Do NOT build
a new globalization: INSTANTIATE it. Define
`AdjSplit F G := ∃ (S : Finset (Fin N)), S.Nonempty ∧ Sᶜ.Nonempty ∧ (F⁻¹*G preserves the
coordinate splitting S ⊕ Sᶜ)` and discharge the two hypotheses:

* **U1 (overlap = cross-coherence, the crux).** If `W := F⁻¹G` preserves a splitting, both
  frames diagonalize the common scaled family `a_x = diag(exp(x·s))` (s constant on each part,
  distinct across, s ≤ 0 so a_x is a posdef effect for x > 0 — the `log_eigenvalues_nonpos`
  trick). Route via PRODUCT VALUES, not couplings: the per-frame product formula
  (`ComplexMaster.lean:78-79` — `sp_eq_twistSeq_transport` + `sp_eq_twistSeq_diagFamily` +
  `eq_adU_diagFamily`) gives `P.sp a_x b = twistSeq t_F a_x b = twistSeq t_G a_x b` for ALL b.
  Evaluate both twistSeq at a block b with distinct part-eigenvalues: entries carry
  `exp(i·t·x·(s_i − s_j))`, agreement on an interval of x, then
  `MasterTheorem.real_character_unique` (Globalization.lean:98) forces `t_F = t_G` EXACTLY
  (single-point agreement only pins t mod 2π — the interval is not optional).
  Tie the transported t to `frameTwist` via `frameTwist_unique` (built 08-07 for exactly this:
  it converts "some parameter works" into "the parameter equals" without fighting `choose`).
  FALLBACK ROUTE if the product-value route jams: compare stabilizer couplings directly
  through `conjProduct` composition (`Ad` functoriality; add `SequentialProductOn.ext` by
  sp-equality — all other fields are Props over sp).
* **U2 (connected = Givens generation, the only new development).** Every `U ∈ U(N)` is a
  finite product of plane unitaries (supported on `span{e_k, e_l}`) and a diagonal phase.
  Constructive induction on N: zero out the first column with plane rotations, recurse.
  ~150-300 lines, elementary. Each factor step preserves the `({k,l}, rest)` splitting —
  nonempty complement needs only N ≥ 3 ✓. Chain: `U_{p+1} = U_p · (plane factor)` gives
  `Relation.ReflTransGen (SymmStep AdjSplit) F G` for all F, G.
* **U3 (cheap invariances, do first as warm-up).** Permutation W: per-frame t is
  label-independent (the per-frame theorem is one t across ALL blocks). Diagonal-phase W:
  fixes every diagonal matrix; its block action is an SO(2) rotation commuting with `rotJ`.
* **U4 (assembly).** `complex_classification_unconditional := complex_classification hN P hS2
  AdjSplit (U2) (U1)`. One-liner once U1/U2 land.
* **U5 (packaging, item 7.3).** Instantiate `PaperA/Statement.lean`'s parameterized
  `LudersConclusion`/`UniqueTwistConclusion` with the CONCRETE references (conj-Lüders,
  `twistSeq`), prove the ℝ and ℂ capstones meet them, refresh AuditPins/THEOREM-MAP/README
  and this file's state-of-six block. Mechanical.

**Estimate:** U3 0.5-1h · U1 4-6h · U2 3-5h · U4 <1h · U5 2-3h · banking ~1h ≈ 12-17h.
P(complete) ≈ 0.8 at demonstrated velocity. **Failure protocol:** if a component hits a
genuine wall, bank the measured remainder declaration-by-declaration here (as the ℝ bridge
did), finish U5 against whatever IS certified, and say plainly which conjunct failed.
Documented failure ≠ completion; do not grind past a measured wall, and do not touch
out-of-scope rows to manufacture progress.

**Working discipline that produced the last two rows — keep all of it:** unit-by-unit with
both gates after each; single-sentence commits with explicit paths; bank each unit to the
blog route file + memory; THEOREM-MAP wins over this file on any disagreement; check
hypothesis lists with `#check`, never prose; no vacuous stub theorems; when a rewrite target
sits under a dependent proof argument, look for the defeq.

---

## ★ STATE OF THE SIX TARGETS — as of 2026-08-08 (read this first)

Tree: `lake build` green at 3106 jobs; `AxiomAudit.lean` PASS at 149 tracked modules;
**custom axioms exactly `[]`**, every tracked declaration's closure ⊆
{`propext`, `Classical.choice`, `Quot.sound`}. All commits LOCAL (repo is public;
pushing is Bryan-gated).

**Coverage of the paper, stated as a count so it is never overstated** — ★ the figures in this
ARC-4-era block (5 / 17 / 14) are **STALE; current is 8 / 19 / 9** per
`STATEMENT-MANIFEST.md`, which is authoritative. Historical figures are retained for
provenance only. Never
write "fully formalized". Itemization: blog `research/paperA-supplementary-rewrite-draft.md`
§3; per-statement evidence: `THEOREM-MAP.md`, which governs.

| Row | Status | Capstone |
| --- | --- | --- |
| `H_N(ℂ)`, N ≥ 3 | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `∃! t`, twist on ALL effects; both frame-graph facts DISCHARGED in-tree (cross-coherence + connectivity). Carries only S1-S7 + S2 + `3 ≤ N`. **08-08: also stated with S2 in the ORDER-UNIT norm** (`complex_classification_unconditional_ouNorm`), so the paper's S2 is the literal hypothesis | `Necessity.complex_classification_unconditional` |
| `H_n(ℝ)` | **MACHINE-CHECKED, HYPOTHESIS-FREE (2026-08-07)** — `a•b = √a·b·√a` on ALL effects, no twist; Jordan hypothesis DISCHARGED by real Kadison proved in-tree, now stated as the full **classification** (`orderAutoR_eq_orthConj`, exact — converse packaged). **08-08: also stated with S2 in the ORDER-UNIT norm** (`real_classification_ouNorm`) | `Necessity.real_classification` |
| `H_n(ℍ)` | **FOUNDATION COMPLETE + `Q_{√a}` restricts** (carrier, order-unit, unital Jordan subalgebra, positivity, cfc-closure, `quatQuadRepEquiv`); **NOT a short lane — see the carrier-genericity finding in `LEDGER-ARCHIVE-M1-M7.md`** | `QuatCarrier`, `quatQuadRepEquiv` |
| `H₃(𝕆)` | **ABSENT, not blocked** (row corrected 08-08 — see below). Octonions are BUILT and sorry-free in the sibling project `~/repos/research/lean/`, same toolchain; the scary Yokota/triality import was re-scoped to an elementary argument by `ALBERT-KERNEL-MEMO.md` on 08-04, and **its one computational input `nucleus(𝕆) = ℝ` is now PROVED** (08-08). Remaining: the model, (I)/(II), and M2-for-Albert (unscoped) | `lean/…/Octonions.lean`, `Octonion.nucleus_real` (both out-of-tree) |
| `cor:qubit-classification` | moduli space + one nonconstant element + certified `ℂP¹→ℝP²` descent + separation; **the classification map's INPUT now exists (2026-08-08, see rung 5.3): `Necessity.n2FrameTwist` extracts the frame function from an arbitrary product, `n2FrameTwist_reverse` proves it order-blind. The bijection is still not assembled — boundedness and continuity of that function, plus `prop:n2-sufficiency`, remain** | `RankTwo.tauModuliRP2`, `RankTwo.tauRP2_blochFrame`, `Necessity.n2FrameTwist` |
| `mthm:omnibus` | **carrier + BOTH assembly halves** (sufficiency `prod`, determination `sp_eq_of_prod_eq`); conditional on the SPLITTING (`prop:central`, paper proof) | `SequentialProductOn.prod` |

★★**`H₃(𝕆)` ROW CORRECTED 2026-08-08 — "BLOCKED, octonions exist in no prover" was FALSE.**
Bryan challenged the claim; verified at source. The original check (archive line 104) was
scoped to **pinned Mathlib only** and its conclusion was then written down as a statement
about *every* prover. Both halves need retracting:
* Mathlib octonions: genuinely absent — the four `octonion` grep hits are prose comments.
  But Mathlib **does** have `IsJordan`/`IsCommJordan` (`Algebra/Jordan/Basic.lean`, 237
  lines, Jordan axioms + `L`/`R` commutation lemmas), so "no Jordan-algebra files at all"
  is retracted too.
* **Our own octonions exist and are sorry-free.** `~/repos/research/lean/RadicalRelativity/`
  `Octonions.lean`: 310 lines, 37 declarations, **0 sorries**, toolchain `v4.28.0` — the
  same toolchain this project pins, so it is portable, not a rewrite. Proved: explicit
  Cayley-table `mul`, `one_mul`/`mul_one`, `non_associative` (with witness),
  `left_alternative`, `right_alternative`, `norm_multiplicative`, `mul_eq_zero_iff`,
  `conj_mul` (anti-automorphism), `conj_conj`, `mul_conj`, all three Moufang identities,
  and full bilinearity (`mul_add`/`add_mul`/`smul_mul`/`mul_smul`). Compare
  `ALBERT-KERNEL-MEMO.md` §2's "inputs consumed, in full" — that list is **already met**
  except ingredient (N).
* `lean/…/Albert.lean` also exists (350 lines, 31 declarations) with `h3O` and `jordanMul`,
  but its 3 sorries include `jordan_identity` itself; all three are marked "expository, not
  referenced by any downstream file", so the carrier is scaffolding, not a usable Jordan
  algebra yet.

**Honest work list for the row** (nothing here is a wall; none of it is done):
1. Port `Octonions.lean` in-tree (same toolchain; it would enter the census and the manifest).
2. ~~`nucleus(𝕆) = ℝ` — memo ingredient (N)~~ **DONE 2026-08-08, same session as this
   correction.** `~/repos/research/lean/RadicalRelativity/OctonionNucleus.lean`,
   `Octonion.nucleus_real`, axioms `[propext, Classical.choice, Quot.sound]`, no
   `native_decide`, `lake build` green at 2862 jobs, zero warnings beyond the expected
   `setOption` note. Statement: if `c` associates with every pair then all seven imaginary
   coordinates vanish. Recipe, for whoever ports it: reduce the basis product FIRST
   (`tbl_i_j : e_i * e_j = e_k`, each by `ext m; fin_cases m <;> simp [mul, basisVec]`),
   then read off coordinates, then `simp only [mul, basisVec, Fin.isValue]` followed by
   `simp +decide only [...]` per triple — each imaginary coordinate outside the quaternion
   subalgebra falls out as `c.coords m = -c.coords m` and `linarith` finishes. Three
   triples suffice mathematically; all seven are used for margin.
   Two traps that cost most of the time: (a) unfolding `mul` against a symbolic `c` on
   both sides times out `simp`, and `norm_num [Fin.ext_iff]` blows the interpreter stack —
   reduce the basis product before touching coordinates; (b) `fin_cases i` on the goal
   `∀ i ≠ 0, c.coords i = 0` produces an index atom that does NOT match the `c.coords 1`
   in the hypotheses, so `linarith` fails with the winning equation sitting right there —
   state the conclusion as an explicit conjunction over numeral literals instead.
3. Build `H₃(𝕆)`: 27-dim ℝ-module, symmetrized product, frame `E_11,E_22,E_33`, Peirce
   blocks as `F_ij` images; prove the Jordan identity for real (not expository).
4. Identities (I)/(II) in the chosen convention (§4's caveat: re-derive, don't quote), plus
   (P1)/(P2) generically → the unit-slot argument discharges `block_injective` with **no
   Spin(8), no triality, no rank certificate**. Memo estimate: weeks of equational algebra.
5. **The genuinely unscoped part:** the M2 `DiagonalHomSetup` machinery (`Θ`, `dχ`, `ρ` from
   the actual sequential product) specialized to the Albert model. The memo explicitly puts
   this outside its own question and calls it "the heavy remaining Albert work". No estimate
   exists for it. This, not the octonions, is what stands between us and the row.

**Lesson, third occurrence of this exact shape** (see the `feedback-fix-the-row-not-just-the-footnote`
and "grep before claiming the library lacks X" rules): a library-absence check has a SCOPE,
and the scope must travel with the claim. "Absent from pinned Mathlib" became "exists in no
prover" became "BLOCKED", and a memo that superseded it four days earlier sat unread in the
same directory. Status words: use **ABSENT** for "nobody built it", **BLOCKED** only for a
named wall with evidence.

★★**THE ℝ ROW'S CONDITION IS GONE (2026-08-07).** `Necessity.real_classification`
(`Necessity/RealRowUnconditional.lean`) proves: for any S1-S7 product with S2 on
`H_N(ℝ)`, `N > 0`, `P.sp a b = b.conj (a.cfc sqrt).mat` on ALL effects. Hypothesis list
is exactly the paper's; `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
The discharge chain, all in-tree:
  * `Wigner/RealWigner.exists_isometry_of_transProbPreservingR` (de-vendored 08-08; first-party) — real Wigner
    rigidity, PROVED (the theorem that existed in no library);
  * `Necessity/RealInducedMap.lean` — `rayMapR` (order automorphism ⟹ ray self-map via
    choice) + `rayMapR_transProbPreservingR` (it preserves transition probability, by
    `tprobR_preserved`) + `isometryMatrixR` (the orthogonal MATRIX of the isometry, with
    `isometryMatrixR_orthogonal`) + `rankOneR_eq_of_mk_eq` (ray equality ⟹ rank-one
    equality: the sign cancels because `rankOneR` is quadratic — this is the step that
    has no ℂ analogue and is why ℝ needs no dichotomy);
  * `Necessity/RealKadison.orderAutoR_preservesJordan` — REAL KADISON RIGIDITY: every
    unital ℝ-linear order-automorphism of `H_N(ℝ)` is conjugation by an orthogonal matrix,
    hence Jordan;
  * `Necessity/RealRowUnconditional.thetaPreservesJordanR_of_S2` — `theta` is a unital
    surjective linear order-iso (`theta_le_iff`/`theta_one`/`thetaEquiv`, all already
    field-general), so real Kadison applies in every eigenframe.
**CORRECTION to an earlier framing in this ledger and in the new files' first drafts:**
the ℂ row's Wigner step is a vendored *proof* (`Vendor/Wigner/WignerRigidity.lean`), NOT
an axiom — `#print axioms Necessity.complex_classification` is Lean core too. The ℝ row's
gap was never a cited axiom that ℂ also had; it was a MISSING THEOREM. Do not write "ℝ is
better founded than ℂ" anywhere: both rows now close over Lean core alone.
Scope note: the unconditional statement is at `n := Fin N` (the paper's `H_N(ℝ)`);
`sp_eq_luders_of_effect` remains stated at generic `[Fintype n] [DecidableEq n]` and the
Kadison bridge is `Fin N`-bound because it needs `Matrix.toEuclideanLin`. Generalizing the
bridge to arbitrary `n` is mechanical (nothing uses `Fin`'s order) but was not done.

★★**LABEL CORRECTION 2026-08-07 — the ℂ row was mislabelled in THIS TABLE, and the mislabel
was repeated in session reports. Verified by `#check`, not by reading prose.**
```
@Necessity.real_classification    : ∀ {N}, 0 < N → ∀ P, P.FirstArgContinuous → … (nothing else)
@Necessity.complex_classification : ∀ {N}, 3 ≤ N → ∀ P, P.FirstArgContinuous →
                                      ∀ (Adj), (connected …) → (overlap …) → ∃! t, …
```
The ℂ row takes `Adj` plus `connected` plus `overlap` as CALLER-SUPPLIED arguments. Those are
paper-proved and located, never axioms — but a theorem with located hypotheses is **not
unconditional**, which is exactly the standard this ledger applied to the ℝ row when it read
"modulo the cited Jordan property". Applying one standard to ℝ and another to ℂ is the error.
`THEOREM-MAP.md` was RIGHT throughout (it calls the two "the honest residue of this row");
only this summary table and the session reports drifted. THEOREM-MAP remains the governing
honesty ledger — **when the two disagree, THEOREM-MAP wins.**
The lesson generalizes and still binds: **check hypothesis lists with `#check`, never by
reading prose**, and apply one standard to every row.

★★**SUPERSEDED LATER THE SAME DAY — do not cite the two paragraphs that stood here.** They
read "`H_n(ℝ)` is the ONLY row that carries nothing beyond S1-S7 + S2 … On CARRIED HYPOTHESES
ℝ is now strictly cleaner" and "to make ℂ genuinely hypothesis-free, `connected` and `overlap`
must be discharged … Neither is started." Both were true when written and are now FALSE: the
ℂ row's two frame-graph facts were discharged on 2026-08-07 (see the ARC-3 RESULT block at the
top of this file). **Current standing: `H_N(ℂ)` for `N ≥ 3` and `H_n(ℝ)` are BOTH
hypothesis-free, and they are equally well founded on both axes** — identical axiom closure
(Lean core) and identical carried hypotheses (S1-S7 + S2 + a dimension bound). Never rank one
above the other on either axis.

## Milestone history M1–M7 — ARCHIVED

The arc-2/arc-3 narrative and the full M1–M7 discharge records (about 3,000
lines) were moved to **`LEDGER-ARCHIVE-M1-M7.md`** on 2026-08-08 (item 4.6).
They are provenance, not orders: every milestone whose row in `THEOREM-MAP.md`
reads machine-checked has left this ledger, and THEOREM-MAP is the asset.

Two pointers that other parts of this file still make, now resolved there:

* the **ℍ carrier-genericity finding** referenced by the six-targets table
  (`H_n(ℍ)` row) — archive, "SECOND CORRECTION TO THE ℍ ESTIMATE";
* the **ℂ residue** sharpening that preceded its discharge — archive,
  "ℂ RESIDUE SHARPENED 2026-08-07".

## Cross-cutting / hygiene

- **H1. Stale `PLAN.md` references.** Interface/Coalescence docstrings cite a
  `PLAN.md` that does not exist in this repo (predates the public deposit).
  Point them at `THEOREM-MAP.md` + this ledger. ~30 min.
- **H2. Interface evolution discipline.** Any field change during instantiation
  work must update: the structure, Layer-6 freeze, witnesses, THEOREM-MAP §2,
  this ledger — in one commit.
- **H3. No `native_decide` anywhere** (audit census rejects it); certificates
  must be kernel-`decide` scale or structured proofs.
- **H4. Audit-your-own-corrections:** diff-audit every round; verify verifiers
  saw data (print counts; no `| head` on gate output).
- **H6. `HermitianMat.Matrix` namespace shadow (vendor-inherited parser trap).**
  The vendored island declares `Matrix.*` lemmas inside `namespace HermitianMat`
  (`Vendor/HermitianMat/Inner.lean:405`, `NonSingular.lean:18`), so an
  `open scoped Matrix` written INSIDE `namespace HermitianMat` resolves to the
  notation-free `HermitianMat.Matrix` and silently fails to activate `*ᵥ` — the
  parser then lexes `*ᵥ` as `*` + a subscript-term `ᵥ…`, yielding baffling
  "`Mathlib.Tactic.subscriptTerm` has not been implemented" errors. Always
  `open scoped Matrix` BEFORE entering the namespace (or write
  `open scoped _root_.Matrix`). Diagnosed 2026-08-04 (order-unit layer).
  Same family (2026-08-05): the vendor also declares `HermitianMat.pow_zero`
  (Basic.lean:275), which shadows the ROOT `pow_zero` inside the namespace and
  makes `simp only [pow_zero]` a silent no-op on `Matrix`/ℝ powers — write
  `_root_.pow_zero`. Audit any bare root-algebra simp name used inside
  `namespace HermitianMat` against the vendor's declarations.
- **H7. Expected-type elaboration of resolution-shaped lemmas times out.**
  Applying `mat_cfc_of_resolution` with `(R := fun q => …)`/`(c := fun q => …)`
  named AND a type-ascribed `have` makes the unifier grind through `specProj`
  bodies (cfc → eigendecomposition) — deterministic whnf timeout even at 800k
  heartbeats. The fix is forward inference:
  `have hres := fun f => mat_cfc_of_resolution hidem horth hsum hM f` with NO
  type ascription and NO named lambdas — instant, and the (β-unreduced) inferred
  type rewrites fine downstream. Diagnosed 2026-08-05 (S1–S7 unit, bisected via
  probe file).
- **H5. Scoped-instance gotcha (the costliest inventory discovery).** The
  Loewner order + `StarOrderedRing` on `Matrix` require `open scoped
  MatrixOrder` (`Analysis/Matrix/Order.lean`); the matrix C*-norm requires
  `open scoped Matrix.Norms.L2Operator` (or use the `CStarMatrix` type copy,
  which carries the instances globally). Neither is discoverable from
  declaration names. Also: `LinearAlgebra/Matrix/HermitianFunctionalCalculus
  .lean` is a deprecated stub — the real module is
  `Analysis/Matrix/HermitianFunctionalCalculus.lean`. Put the `open scoped`
  lines in every M1/M2 file header from day one.

