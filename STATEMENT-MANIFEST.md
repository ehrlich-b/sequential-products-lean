# Statement manifest — the frozen denominator for Paper A coverage claims

**Purpose.** Every coverage claim about this development ("N of 36") cites *this* file for
what the 36 are. Without a frozen list, a renumbering, a split lemma, or a promoted remark
silently moves the target and makes the count unfalsifiable. Created 2026-08-08 as rung
**5.0** of the ARC-5 orders (`LEDGER.md`, top block).

## The pin

| | |
| --- | --- |
| Source | `landing/papers/twist-normal-form/main.tex`, blog repo `ehrlich-b/blog` |
| Blob hash | **`205fdf5a548c70744cd38cccc25cb8a201cc9771`** |
| Frozen tag | `paperA-jpa-submitted` @ blog commit `035c337` |
| Working copy | 2026-08-08 — **byte-identical to the frozen tag** (same blob hash; the manuscript has not been touched since submission) |

Because the two agree, this manifest pins one object, not two. If `main.tex` is ever edited,
re-run the extraction (below) and record the new blob hash *plus a diff of this table*
before quoting any coverage number.

## How the 36 is derived (reproducible)

The article's `remark` environment shares the `theorem` counter (`preamble.sty`:34–49), so
the numbered-environment count is 43 and the numbered-*result* count is 43 − 7 remarks = 36.
Extraction:

```
grep -n '\\begin{\(maintheorem\|theorem\|lemma\|proposition\|corollary\|definition\)}' main.tex
```

yields exactly the 36 rows below (2 `maintheorem`, 5 `theorem`, 17 `lemma`, 9 `proposition`,
2 `corollary`, 1 `definition`). The 7 excluded remarks are `rem:S2-scope` (597),
`rem:import-hyps` (811), `rem:no-unitary` (878), `rem:moduli` (1416), `rem:n2-selection`
(1550), `rem:qubit-attribution` (1930), `rem:twist-detection` (1941).

**The count is a LaTeX artifact, not a unit of mathematical content.** `def:sp` is a
definition (encoding it is not "proving" it); `thm:vdw1` and `prop:bridge` are cited
external results the paper never claims to reprove; `mthm:master`/`mthm:omnibus` are stated
over an *abstract* simple Euclidean Jordan algebra, so proving either "at the article's own
generality" requires the Jordan–von Neumann–Wigner classification — the campaign's one
pre-registered permanent import. Read the count with `THEOREM-MAP.md`, never instead of it.

## Status vocabulary

* **FORMALIZED** — a Lean theorem states the article's statement at the article's own
  generality and proves it: no located hypothesis standing in for a cited result, no
  restriction to a special case.
* **PARTIAL** — a Lean declaration covers part of it: one clause of several, a concrete
  carrier where the article is abstract, the statement with one of its own inputs carried as
  a hypothesis, a generator-level rather than operation-level version, or a certified
  concrete example in place of the general lemma.
* **ABSENT** — no Lean counterpart. *ABSENT means nobody has built it.* It does **not** mean
  blocked; a wall gets called BLOCKED only with named evidence for the wall (see the
  `H₃(𝕆)` correction in `LEDGER.md`).

**Baseline at manifest creation: 5 FORMALIZED, 17 PARTIAL, 14 ABSENT** — immediately
corrected to **6 / 19 / 11** by the audit the manifest itself provoked (2026-08-08, rung
5.1), then to **6 / 20 / 10** when `cor:selectors` clause (ii) was proved: three rows had
been carried as ABSENT while Lean declarations for them existed.
`lem:aone` is FORMALIZED and had been since the S1–S7 derived-lemma layer was written;
`lem:span` and `prop:pseudo-transfer` are PARTIAL on the concrete carrier. **No proof was
written for those three corrections — the tree was undercounted.** The lesson is the
mirror image of the `H₃(𝕆)` over-claim: a coverage table maintained by prose drifts in
*both* directions, so every row now names its declaration or says ABSENT.
`THEOREM-MAP.md` governs per statement and wins wherever it and this file disagree.

---

## The 36

`§` = line in the pinned `main.tex`. `T` = target rung of the ARC-5 ladder, where one is
assigned; `—` = not targeted this arc; `ext` = cited external result, out of scope by design.

| # | Label | § | Kind | Statement (one line) | Status | T |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `mthm:master` | 124 | maintheorem | On a f.d. simple EJA of rank $n\geq3$, any S1–S7 (+S2) sequential product is Lüders on the real, quaternionic and exceptional types, and $a^{1/2+it}b\,a^{1/2-it}$ for a unique $t$ on the complex type; block-diagonality of the update is derived, not assumed. | PARTIAL (ℝ and ℂ rows outright; ℍ, 𝕆, and the one-theorem-over-abstract-EJA form open) | — |
| 2 | `mthm:omnibus` | 187 | maintheorem | For a f.d. EJA whose rank-two summands are the real or complex qubit, the product decomposes over simple summands and is Lüders / constant-twist / frame-dependent-twist per summand, giving a bijection $\mathcal{M}_{\mathrm{SP}}(J)\cong\prod\mathbb{R}\times\prod C(\mathbb{RP}^2,\mathbb{R})$. | ABSENT (needs JvNW at article generality) | — |
| 3 | `def:sp` | 363 | definition | A sequential product space: an order unit space with a binary operation on effects satisfying S1 additivity, S2 order-unit-norm continuity in the first argument, S3 unitality, S4 symmetry of orthogonality, S5 compatible associativity, S6 additivity of compatibility, S7 multiplicativity of compatibility. | PARTIAL (encoded as `SequentialProductOn`/`SequentialProduct`; effect-closure carried as the codomain condition `sp_effect` rather than as a clause) | — |
| 4 | `thm:vdw1` | 399 | theorem | A finite-dimensional sequential product space is order-isomorphic to a Euclidean Jordan algebra. | ABSENT | ext |
| 5 | `lem:span` | 418 | lemma | In an order unit space the effects contain the ball of radius $\tfrac12$ about $\tfrac12\id$, hence span $V$, so linear maps agreeing on effects are equal; likewise $[0,q]$ spans the Peirce subalgebra $J_2(q)$. | PARTIAL, **upgraded to abstract 2026-08-08**: the spanning and extensionality clauses are now proved at *full order-unit-space generality* (`OrderUnitSpace.span_isEffect_eq_top`, `linearMap_eq_of_eq_on_effects`) from order-unit boundedness alone — no norm, no Archimedean property. Open: the ball clause (needs the norm to *be* the order-unit norm plus Archimedean; it is the article's route, not its content) and the Peirce clause (which the article gets by instantiating this lemma at $(J_2(q),q)$ — so it follows *once* the tree knows $J_2(q)$ is an order unit space, which it does not) | 5.1 |
| 6 | `lem:homog` | 446 | lemma | For each effect $a$: (i) $L_a$ is additive and order bounded, hence extends uniquely to a positive linear map on $J$; (ii) $(\lambda a)\cdot b=\lambda(a\cdot b)$ for $\lambda\in[0,1]$. | PARTIAL (clause (ii) on effects, `Necessity/FirstArgument.lean`) | 5.1 |
| 7 | `lem:cone-ext` | 477 | lemma | The product extends from effect to arbitrary positive-cone first arguments by $v\cdot b:=\mu((v/\mu)\cdot b)$, independently of the normalization $\mu\geq\lVert v\rVert$, positively homogeneously, agreeing with the original on effects. | PARTIAL (normalization extension on the concrete carrier: `Necessity.thetaNorm`, `theta_smul`) | 5.1 |
| 8 | `lem:simple-bridge` | 505 | lemma | On a f.d. EJA: the standard product makes the effects a convex $\sigma$-sequential effect algebra hence an SES; every effect is simple ($E=E_0$), so vdW's simplicity hypotheses hold for the unknown product too; every invertible effect is order preserving for both products; and the standard product is invariant under unital order isomorphisms. | ABSENT | — |
| 9 | `lem:normality` | 568 | lemma | On a f.d. order-unit space, any operation satisfying S1 and S2 is normal in vdW's sense: $b_k\downarrow b\Rightarrow a\cdot b_k\downarrow a\cdot b$, and compatibility passes to order-infima. | ABSENT | 5.1 |
| 10 | `prop:bridge` | 612 | proposition | For EJA effects under the standard product, $\lprod{a}{b}=\lprod{b}{a}\iff[Q_a,Q_b]=0\iff[T_a,T_b]=0$: standard-product compatibility is exactly Jordan operator commutation. | ABSENT | ext |
| 11 | `lem:aone` | 637 | lemma | $a\cdot\id=a$ for every effect $a$. | **FORMALIZED** — `SequentialProduct.sp_unit_right`, abstract `[SequentialProductCore V]`, by the article's own S1/S3/S4/S6 route. *Was listed ABSENT until 2026-08-08; the row was already true.* | — |
| 12 | `prop:central` | 650 | proposition | For $J=\bigoplus J_\alpha$ and an S1–S7 product, $a\cdot b=\sum_\alpha a_\alpha\cdot b_\alpha$ with each restriction an S1–S7 product on the summand; conversely summand products assemble. Distinct simple summands cannot couple. | PARTIAL (componentwise identity `MasterTheorem.Central.central_decomposition`; summand inheritance of S1–S7 and the converse assembly open) | — |
| 13 | `prop:pseudo-transfer` | 719 | proposition | For an invertible effect $a$ with spectral inverse $a^{-1}$, $a\cdot a^{-1}=a^{-1}\cdot a=\id$ for the unknown product as well as the standard one, so $a$ is order preserving for both and vdW Prop. 5.3's hypotheses hold at every invertible effect. | PARTIAL (concrete carrier, in the *normalized* form `Necessity.sp_pseudoInv_eq_smul_one`/`sp_pseudoInv_cancel`: Lean's `pseudoInv` is rescaled into the effects, so the identity carries `pseudoInvCoef b •` where the article has $\id$ — the article's form needs `lem:cone-ext` to divide it out) | 5.1 |
| 14 | `prop:theta` | 759 | proposition | For every invertible effect $a$ there is a Jordan automorphism $\Theta_a$ with $a\cdot b=Q_{\sqrt a}\Theta_a(b)$; $\Theta_a$ fixes everything operator-commuting with $a$, and $\Theta$ is multiplicative on operator-commuting invertibles. | PARTIAL (derived on both concrete carriers from in-tree Kadison rigidity; vIR's JB-algebra generality open) | — |
| 15 | `lem:frame-fix` | 908 | lemma | $\Theta_r$ fixes each frame atom and the diagonal pointwise, preserves each Peirce block, and lies in $\Stab(F)^\circ$; hence $L_{a(r)}$ is Peirce-block-diagonal. | PARTIAL (certificate for the produced setup, `MasterTheorem/Master.lean`; general statement open) | 5.1 |
| 16 | `lem:coalescence` | 940 | lemma | If $r_i=r_j$ then $\Theta_r$ fixes $V_{ij}$ pointwise; more generally an invertible $a=\lambda q+a_0$ scalar on $J_2(q)$ with no Peirce 1-part has $\Theta_a|_{J_2(q)}=\mathrm{id}$. | PARTIAL (differential shadow in strong pointwise form; that the shadow *is* the cited lemma's differential open) | 5.4 |
| 17 | `lem:homomorphism` | 968 | lemma | $r\mapsto\Theta_r$ is a continuous homomorphism $((-\infty,0]^n,+)\to\Stab(F)^\circ$, extending to $\chi:(\mathbb{R}^n,+)\to\Stab(F)^\circ$ with real-linear differential $d\chi$ satisfying $\rho_{ij}(d\chi(r))=(r_i-r_j)T_{ij}$ for a single $T_{ij}\in\mathfrak{so}(V_{ij})$. | ABSENT (Lean's `dχAdd` begins *after* this transition; Θ is never differentiated) | 5.4 |
| 18 | `prop:stabilizers` | 1020 | proposition | For each of the four simple types of rank $n$, the identity component of the frame stabilizer and its induced action on each Peirce block $V_{ij}$: $\{1\}$/0 for ℝ, $T^{n-1}$/$i(\theta_i-\theta_j)z$ for ℂ, $Sp(1)^n/\{\pm1\}$/$\xi_ix-x\xi_j$ for ℍ, $\Spin(8)$/triality for 𝕆. | PARTIAL (coupling identity as a conclusion of the `StabilizerCoupling` constructor; construction of the representation from Θ open) | 5.4 |
| 19 | `prop:real` | 1086 | proposition | On $\MnKsa{n}{\mathbb{R}}$, $n\geq2$: $\Theta_r=\mathrm{id}$, so $a\cdot b=Q_{\sqrt a}b$; in particular the real qubit is rigid. | **FORMALIZED** — `Necessity.real_classification` (+ `_ouNorm`) | — |
| 20 | `thm:quaternionic` | 1102 | theorem | On $\MnKsa{n}{\mathbb{H}}$, $n\geq3$: $\Theta_r=\mathrm{id}$, so $a\cdot b=Q_{\sqrt a}b$. | PARTIAL (`MasterTheorem.luders_quaternionic_produced` at skeleton level, with $Z(\mathbb{H})\cap\operatorname{Im}\mathbb{H}=\{0\}$ computed; no concrete quaternionic carrier) | 5.5 |
| 21 | `thm:albert` | 1131 | theorem | On $H_3(\mathbb{O})$: $\Theta_r=\mathrm{id}$, so $a\cdot b=Q_{\sqrt a}b$. | PARTIAL (`MasterTheorem.luders_albert_produced` at skeleton level, from cited $\Spin(8)$ block injectivity; no concrete exceptional carrier) | — |
| 22 | `lem:orientation` | 1172 | lemma | On $\Mnsa{n}$, $n\geq3$, with $q$ rank-two and $p_k$ an orthogonal atom, $\mathcal{J}_{q,k}(x)=iz-i z^*$ ($z=qxp_k$) is a complex structure on the cross-coherence space depending only on $q,p_k,i$ and not on any splitting of $q$; it commutes with stabilizing inner automorphisms; and $\Ad_{a^{it}}|_X=\exp(t(\log\lambda-\log\lambda_k)\mathcal{J}_{q,k})$. | ABSENT | 5.1 |
| 23 | `prop:per-frame` | 1225 | proposition | On $\Mnsa{n}$, $n\geq3$, for each Jordan frame there is a single $t_F\in\mathbb{R}$, depending only on the unordered frame, with $\Theta_r=\Ad_{a(r)^{it_F}}$ for every $r$. | **FORMALIZED** — `Necessity.complex_perFrame_unconditional` | — |
| 24 | `lem:adjacent` | 1269 | lemma | For $n\geq3$, adjacent frames — differing by a rotation inside a rank-two block $q=p_1+p_2=p'_1+p'_2$ and sharing $p_3,\dots,p_n$ — have $t_F=t_{F'}$. | PARTIAL (proved for *axis*-adjacency, `frameTwist_eq_of_adjAxis`; the article's own adjacency open) | 5.2 |
| 25 | `thm:complex` | 1315 | theorem | On $H_n(\mathbb{C})=\Mnsa{n}$, $n\geq3$: there is a single $t\in\mathbb{R}$ with $a\cdot b=a^{1/2+it}b\,a^{1/2-it}$ for all effects. | **FORMALIZED** — `Necessity.complex_classification_unconditional` (+ `_ouNorm`), uniqueness as $\exists!$ | — |
| 26 | `lem:frame-connectivity` | 1331 | lemma | For $n\geq2$ the graph on Jordan frames of $\Mnsa{n}$ with $F\sim F'$ iff they share $n-2$ atoms is connected. | PARTIAL (connectivity for axis-adjacency via a Householder factorization, `adjAxis_connected`; the article's graph open) | 5.2 |
| 27 | `prop:singular` | 1356 | lemma | In each type row the stated formula extends from invertible to all effects by S2-continuity. | **FORMALIZED** — `MasterTheorem.prop_singular`, applied by both flagship rows | — |
| 28 | `lem:twist-sufficiency` | 1386 | lemma | For every $n\geq2$ and $t\in\mathbb{R}$ the twisted product $\circ_t$ is a norm-continuous S1–S7 sequential product on the effects of $H_n(\mathbb{C})$. | **FORMALIZED** — `HermitianMat.twistSequentialProduct`, all seven clauses, S2 in both norms | — |
| 29 | `prop:n2-necessity` | 1488 | proposition | For a norm-continuous S1–S7 product on $\Mnsa{2}$ and each ordered frame $(P_n,P_{-n})$ there is a single real $\widetilde t(n)$ with $\Theta_a|_{W_n}=\exp(\ell\,\widetilde t(n)\,\mathcal{J}_n)$, $\ell=\log(\lambda_+/\lambda_-)$ — one parameter per ordered frame, independent of which diagonal effect is used; no cross-frame constancy follows. | PARTIAL (generator-level `MasterTheorem.RankTwo.n2_necessity`; Lean *assumes* the angle map linear and proves only the factorization) | 5.3 |
| 30 | `prop:n2-sufficiency` | 1580 | proposition | For every continuous $t:\mathbb{RP}^2\to\mathbb{R}$ the operation $a\cdot b:=a^{1/2+it_a}b\,a^{1/2-it_a}$ ($t_a=t(\mathrm{fr}\,a)$, $0$ for scalar $a$) is a norm-continuous S1–S7 sequential product on $\Mnsa{2}$. | ABSENT | 5.3 |
| 31 | `thm:qubit-boundary` | 1718 | theorem | With $\tau(a)=(2\operatorname{tr}(PR)-1)^2$ for the spectral frame of $a$, the family $a\cdot b=a^{1/2+i\tau(a)}b\,a^{1/2-i\tau(a)}$ (i) maps effects to effects with the stated rotation on $W_n$, (ii) satisfies all seven axioms, and (iii) is genuinely frame-dependent — no $(\Phi,t)$ conjugates it to a constant twist, so the complex conclusion of `mthm:master` fails at rank two. | PARTIAL (parts (i) and (iii), plus the cocycle and backward compatibility; the bundled S1–S7 verification of the $\tau$ family and the unimodular cocycle subcases open) | 5.3 |
| 32 | `lem:n2-bounded` | 1788 | lemma | For any norm-continuous S1–S7 product on $\Mnsa{2}$, $M:=\sup_{n\in S^2}\lvert\widetilde t(n)\rvert<\infty$. | ABSENT (the classification map does not exist in Lean) | 5.3 |
| 33 | `lem:n2-continuity` | 1820 | lemma | The ordered-frame parameter $\widetilde t$ is continuous on $S^2$. | PARTIAL (continuity of the frame function and of the $\mathbb{RP}^2$ moduli element for one concrete distinguished element; an arbitrary product's moduli function open) | 5.3 |
| 34 | `lem:n2-descent` | 1852 | lemma | $\widetilde t(-n)=\widetilde t(n)$ — the two sign changes cancel — so the frame parameter descends to a single continuous bounded $t:\mathbb{RP}^2\to\mathbb{R}$ with no residual line-bundle twist. | PARTIAL (complementation involution, invariance of frame function and Bloch map, and the $\mathbb{RP}^2$ bridge, for that same concrete element; descent for an arbitrary product open) | 5.3 |
| 35 | `cor:qubit-classification` | 1888 | corollary | $t\mapsto\circ_t$ is a bijection from $C(\mathbb{RP}^2,\mathbb{R})$ onto the norm-continuous S1–S7 products on $\Mnsa{2}$. | ABSENT (the classification map does not exist in Lean) | 5.3 |
| 36 | `cor:selectors` | 1995 | corollary | On $H_n(\mathbb{C})$, $n\geq3$, the complex-type product is Lüders ($t=0$) if any of: (i) Peirce exchange covariance, (ii) trace-form symmetry, (iii) covariance under every unital order automorphism (the transpose suffices on $\Mnsa{n}$). | PARTIAL — **clause (ii) proved 2026-08-08 at the article's own generality**: `Necessity.selector_traceSymm` / `selector_traceSymm_luders` ($N\geq3$, S1–S7, S2, no other hypothesis). Clauses (i) and (iii) open; (iii) needs exactly one missing lemma, $(\mathrm{cfc}\,f\,a)^{\mathsf T}=\mathrm{cfc}\,f\,(a^{\mathsf T})$, recipe recorded in `ComplexRowUnconditional.lean` | 5.1 |

---

## Ceiling arithmetic

Of the 36: **2 are cited external results** (`thm:vdw1`, `prop:bridge`) that the paper does
not claim to prove; **2 more need JvNW** to be stated at the article's abstract generality
(`mthm:master`, `mthm:omnibus`); **1 needs vIR's JB-algebra generality** (`prop:theta`); and
**1 needs the unscoped Albert M2 machinery** (`thm:albert` — the octonions themselves are
*not* the wall; see `LEDGER.md`'s `H₃(𝕆)` correction and `ALBERT-KERNEL-MEMO.md`). That is
6 rows outside this arc's reach on purpose, giving an interior ceiling of **30**, and a
realistic one of **26–28** once `lem:simple-bridge` (a four-clause bridge into vdW's paper)
and the ℍ row are priced honestly.

Rung assignments above are targets, not promises. When a rung banks a remainder instead of
closing a row, the row's Status cell here is updated in the same commit as `THEOREM-MAP.md`.
