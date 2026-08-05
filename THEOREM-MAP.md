# Theorem-to-file map

Paper statements against Lean declarations, plus — equally important — what is
**not** machine-checked. Labels are the manuscript's `\label` keys, which the
`MasterTheorem/` and `PaperA/` docstrings also cite. The legacy
`Selection/` modules predate this manuscript and cite the labels of the earlier
development instead; they are listed in §3, not here.

## 1. Machine-checked, closure = Lean core only

Each of these is pinned in `AxiomAudit.lean` Layer 2 to *exactly* `propext`,
`Classical.choice`, `Quot.sound` — not even the cited axiom enters.

**Read §2 before reading this table as a verification claim.** The rows fall into
three kinds, and only the first is conditional on §2:

- **Conditional on the interface fields of §2**, which are assumed rather than
  proved: `master_chain` and the four typewise-branch rows
  (`luders_real_produced`, `luders_quaternionic_produced`,
  `luders_albert_produced`, `complex_perFrame_produced`), which quantify over
  `ComparisonSetup` / `CoalescenceSetup` / `DiagonalHomSetup` /
  `StabilizerCoupling` / `IsAlbertModel`.
- **Conditional on explicit hypotheses that are not §2 fields**, each discharged by
  a paper proof: `central_decomposition` takes the `SequentialProductCore` class
  (S1 and S3–S7; S2 is not assumed) plus eight named hypotheses;
  `global_twist_of_perFrame` and
  `t_eq_globalT` take frame connectivity and cross-coherence overlap directly.
- **Unconditional**: `real_character_unique` is pure analysis; `n2_necessity` takes
  a linear `angle` with a vanishing hypothesis and no `ComparisonSetup`; three
  concrete `M₂(ℂ)` computations (`sp_blockForm`, `sp_tau_had_is_luders`,
  `sp_tau_std_is_unit_twist`) plus the generator-level exchange selector
  `n2_exchange_selects_luders`, a statement about a linear functional on
  `Fin 2 → ℝ`, carry no interface fields at all.

| Paper statement | Lean declaration | File |
| --- | --- | --- |
| `mthm:master` — **dependency skeleton only**, see §3 | `MasterTheorem.master_chain` | `MasterTheorem/Master.lean` |
| `prop:central`, **componentwise identity only** — the summand inheritance of S1–S7 and the converse assembly remain paper proofs | `MasterTheorem.Central.central_decomposition` | `MasterTheorem/Central.lean` |
| `prop:real` (real type rigid) | `MasterTheorem.luders_real_produced` | `MasterTheorem/Master.lean` |
| `thm:quaternionic` (quaternionic rigid) | `MasterTheorem.luders_quaternionic_produced` | `MasterTheorem/Master.lean` |
| `thm:albert` (exceptional rigid) | `MasterTheorem.luders_albert_produced` | `MasterTheorem/Master.lean` |
| `thm:complex`, per-frame half | `MasterTheorem.complex_perFrame_produced` | `MasterTheorem/Master.lean` |
| `thm:complex`, globalization | `MasterTheorem.global_twist_of_perFrame`, `Globalization.ComplexGlobalizationData.t_eq_globalT` | `MasterTheorem/Adapter.lean`, `MasterTheorem/Globalization.lean` |
| character uniqueness used by the globalization | `MasterTheorem.Globalization.real_character_unique` | `MasterTheorem/Globalization.lean` |
| `prop:n2-necessity`, generator level | `MasterTheorem.RankTwo.n2_necessity` | `MasterTheorem/RankTwo.lean` |
| `rem:n2-selection` (exchange covariance ⟹ Lüders) | `MasterTheorem.RankTwo.n2_exchange_selects_luders` | `MasterTheorem/RankTwo.lean` |
| `thm:qubit-boundary`(i), block form (V1) | `MasterTheorem.RankTwo.sp_blockForm` | `MasterTheorem/RankTwo.lean` |
| `thm:qubit-boundary`(iii), frame-dependence pair (V9) | `RankTwo.sp_tau_had_is_luders`, `RankTwo.sp_tau_std_is_unit_twist` | `MasterTheorem/RankTwo.lean` |

`n2_necessity` is worth reading directly. It takes a **linear** `angle` on `ℝ²`
vanishing on the diagonal and concludes the rotation factors as
`tF * (r 0 - r 1)` for **all** `r : Fin 2 → ℝ` — quantified over both signs of
`r₀ − r₁`, with no ordering of eigenvalue magnitudes. That is the signed
ordered-frame convention the manuscript's §6 uses.

### Statement-fidelity pins

Named theorems in `RadicalRelativity/PaperA/AuditPins.lean`, closure-guarded and
type-frozen, so the audited surface cannot drift from the paper's wording:
`auditPin_s2`, plus
`auditPin_effectProduct`, `auditPin_luders`, `auditPin_uniqueTwist`, and `_body`
pins for the S2 predicate, `IsEffect`, `Effect`, `EffectProduct`.

The S1, S3–S7 fields match the paper's Definition 2.1 clause by clause, including
the effect riders and the `b + c ≤ 1` domain condition; that effects are closed
under the product is carried separately by `sp_effect` as a codomain condition
rather than an eighth axiom. **One literal caveat on (S2):** the paper states
continuity in the *order-unit norm*, whereas `OrderUnitSpace` carries an ambient
norm that Lean never identifies with the order-unit norm. So `auditPin_s2` freezes
first-argument continuity in the *carried* norm. On the intended
finite-dimensional EJA instances the two are equivalent — all norms there induce
the same topology — but the generic interface does not literally state the paper's
(S2), and the direction of the variable (first argument, on effects) is what the
pin does establish.  The concrete carrier now carries the order-unit norm as an
unbundled def (`HermitianMat.ouNorm`, `RadicalRelativity/Hermitian/OrderUnit.lean`)
with the defining infimum attained; identifying it with the carried Frobenius norm
on `H_n(𝕜)` is the discharge tracked as LEDGER 1.4.

### M1 carrier layer (supporting infrastructure, no paper labels)

Census-tracked (46-module manifest), closure = Lean core only:

- `RadicalRelativity/Hermitian/OrderUnit.lean` — `OrderUnitSpace (HermitianMat n 𝕜)`
  instance over the vendored carrier (parents = the existing vendored instances; the
  abstract `OrderUnitSpace.IsEffect` becomes *definitionally* the Loewner unit
  interval, so `Effect (HermitianMat n ℂ)` is the intended effect space and the
  vendored compactness applies verbatim); order-unit boundedness with explicit
  witness `r = ‖a‖`; the **full Archimedean property** over ℂ (strictly stronger
  than the class's order-unit-boundedness field); the order-unit norm `ouNorm` as
  an unbundled def with attainment, minimality, `ouNorm ≤ ‖·‖`, negation/triangle,
  and definiteness.
- `RadicalRelativity/Hermitian/ExtremeEffects.lean` — extreme points of the effect
  interval are exactly the projections `p ^ 2 = p`: projections-are-extreme is
  `RCLike`-uniform (quadratic-form kernel pinch), the converse is proved over ℂ
  through the vendored CFC (perturbation by `± min(x, 1-x)`), and the ℂ join is
  `mem_extremePoints_iff_isProjection`.  This is M3's bridge 1 input
  (order-automorphisms preserve extreme effects, hence projections).
- `RadicalRelativity/Hermitian/Twist.lean` — the twist definition (LEDGER 1.2,
  pair-of-real-cfc route): `twistFactor a t` is `a^{1/2+it}` built from two real
  functional-calculus components (the paper's `0^{1/2±it} = 0` convention holds
  definitionally); `twistSeq t a b := b.conj (twistFactor a t)`; proved:
  `(a^{1/2+it})ᴴ = a^{1/2-it}`, `X·Xᴴ = Xᴴ·X = a` on `0 ≤ a`, both unit laws,
  positivity, S1-additivity and monotonicity in the second argument, effect
  closure, and the `t = 0` Lüders specialization.  S4–S7 and the
  `SequentialProductCore` instance are LEDGER 1.3.

## 2. Carried as cited interface hypotheses — supplied, not proved

The skeleton is **conditional**. Imported results enter as *fields* of five
interface structures. A green build says nothing about their truth; they are
citations, discharged by source review in the manuscript, not by Lean. Note the
structures live in four different files:

**Each of the five structures now has a constructed witness**
(`MasterTheorem/Witnesses.lean`, added 2026-08-04), and `AxiomAudit.lean`
Layer 6 freezes the five constructor types against field drift. (Honesty note:
until 2026-08-04 the "Layer 6" earlier revisions of this paragraph referenced
did not exist in the audit file; both the freezes and the witnesses are now
real and enforced.) The witnesses close the body-hollowing escape this
paragraph used to document: redefining `MasterTheorem.OpCommute`'s *body* to
`False` would have made `ComparisonSetup.frame_opCommute` and
`CoalescenceSetup.simDiag_opCommute` unsatisfiable — the whole skeleton
vacuous — with every printed type, the manifest, and every axiom closure
unchanged. `Witnesses.lean` now proves an actual `OpCommute` (and an actual
`Function.Injective` for the `IsAlbertModel` witness), so that edit class fails
the build. **The witnesses are degenerate** — carrier `ℝ` (or a `PUnit`
stabilizer), zero frame, identity comparison maps, zero block representations:
they establish *inhabitedness*, not truth. They model no rank `≥ 3` EJA, carry
no sequential product, and instantiate none of the cited van de Wetering /
van Imhoff–Roelands / Faraut–Korányi / Yokota content, so the skeleton remains
exactly as conditional as this section states. The discharge plan for the
intended instances is `LEDGER.md`.

| Structure | File |
| --- | --- |
| `ComparisonSetup`, `StabilizerCoupling` | `MasterTheorem/Interface.lean` |
| `CoalescenceSetup` | `MasterTheorem/Coalescence.lean` |
| `DiagonalHomSetup` | `MasterTheorem/DiagonalHom.lean` |
| `IsAlbertModel` | `MasterTheorem/Branches/Albert.lean` |

| Field | Cited source | Paper location |
| --- | --- | --- |
| `ComparisonSetup.Θ_jordan` | van de Wetering Prop. 5.3 + van Imhoff–Roelands Cor. 2.5 / Prop. 2.6, taken as the imported *conclusion*: the Lean structure does not encode the JB-algebra premises | `prop:theta` |
| `ComparisonSetup.Θ_fix` | van de Wetering Prop. 5.5. **Stronger than the source as stated**: the field quantifies over all of `J`, the source is effect-level. The span extension is the manuscript's short argument (the commutant is an order-unit subspace spanned by its effects), not Lean's | `prop:theta` |
| `ComparisonSetup`'s use of `aOf r` outside the negative orthant | van de Wetering's normalization extension `Θ_{λq} = Θ_q`, which defines `Θ_q` for arbitrary positive order-preserving `q` after rescaling | `lem:cone-ext` |
| comparison cocycle | van de Wetering Prop. 5.7, specialized to the commuting diagonal family — **weaker** than the source, not stronger | `prop:theta` |
| `DiagonalHomSetup.dχAdd`, `dχAdd_cont`, differentiated coalescence | **not a rendering of one cited theorem**: these begin *after* the paper's comparison-to-differential analysis. Lean neither differentiates `Θ` nor proves `dχAdd` is its derivative | `lem:homomorphism` |
| `IsAlbertModel.block_injective` | Yokota's triality identification of the pointwise frame stabilizer with `Spin(8)`, **plus** a standard simplicity/kernel argument (nontrivial representation of a simple Lie algebra has zero kernel). Injectivity is a composite consequence, not Yokota's literal text | `thm:albert` |

One cited result is recorded as an `axiom` declaration, deliberately outside the
Layer-2 cones. Its printed type is frozen by Layer 4; fidelity to the cited
literature remains a human audit, and the attribution is compound:

- `Selection.aczel_continuous_multiplicative` — Aczél supplies the scalar
  functional-equation lineage; the operator-valued conclusion
  `h(x) = exp((log x)·A)` is finite-dimensional one-parameter-group theory
  (Engel–Nagel). Not a theorem of Aczél alone in this form. Scheduled for
  discharge in campaign M2 (`LEDGER.md` 2.7).
- `TwistNormalForm.bgw_canonical_composite` — **ELIMINATED 2026-08-04
  (`LEDGER.md` 2.8).** The former axiom asserted the existence of an operation
  with nine specified table values — a constructible statement that cannot be
  false — and it quantified over all natural-number labels, broader than the
  BGW citation (the attribution imprecision previously flagged here). It is now
  the definition `TwistNormalForm.bgwComposite` with the nine rows proved by
  `rfl` (`bgwComposite_table`); the Barnum–Graydon–Wilce 2020 citation attaches
  to the table's *interpretation* (that it is their canonical standard-embedding
  composite), as prose provenance in the module docstring — which is all
  `#print axioms` ever certified anyway. The tracked tree now carries exactly
  ONE custom axiom.

## 3. Not machine-checked at all

State these plainly rather than inferring coverage from a green build. This list
is intended to be exhaustive; where it and the supplement's inventory differ, the
supplement governs.

**Supplied rather than derived, in addition to the interface fields of §2:** the
construction of the comparison character and its differential from `Θ_a`; the
operator-to-character translation on the cross-coherence space; the geometric
two-plane frame-connectivity move; the concrete `(S2)` and invertible-density
inputs; the remaining rank-two cocycle and compatibility cases; the complete
seven-axiom verification; and the contents of the cited van de Wetering
propositions themselves.

**Statements with no Lean counterpart:**

- **`mthm:master` itself.** `master_chain` audits the *composition* of the case
  split over one abstract algebra; it constructs no concrete simple EJA, and does
  not prove that a given algebra is of a particular coordinate type, that an
  operation satisfies S1–S7, that `L_a = Q_{√a}Θ_a`, that `Θ_a = id`, or any
  product equality. Its own docstring says so.
- **The lifting step in `prop:n2-necessity`** — that a continuous homomorphism
  `ℝ² → SO(2)` lifts through the universal cover to a linear functional. Lean
  *assumes* `angle` is linear and proves only the factorization, so this step is
  supplied by the paper, not checked.
- **`lem:n2-bounded`, `lem:n2-continuity`, `lem:n2-descent`** (boundedness,
  continuity, evenness/descent to `ℝP²`) and the assembled bijection
  `cor:qubit-classification`. The rank-two Lean content is the fixed-frame
  *algebraic* core on concrete `M₂(ℂ)`, not the classification.
- **`mthm:omnibus`** (the finite-dimensional omnibus classification) and
  **`prop:pseudo-transfer`**.
- **`prop:singular`** exists as a standalone lemma but is *not* invoked by
  `master_chain`.
- Analytic content generally: norm continuity arguments, spectral theory, and
  the singular-effect extensions live in the paper.

## 4. SymPy labels

**Label convention.** The manuscript cites these checks as `V1`–`V10`; the script
itself prints its groups as `1.`–`10c.` **without the `V` prefix**. Paper label
`Vk` is script group `k`; sub-labels (`4a`, `5b'`, …) are individual checks
within a group. The 33 `PASS` lines are:

| Paper label | Script group | Content |
| --- | --- | --- |
| `V1` | `1.` | block normal form in `a`'s eigenbasis |
| `V2` | `2a`–`2b` | scalar effects are twist-invisible |
| `V3` | `3.` | rank-deficient first argument gives the Lüders value |
| `V4` | `4a`–`4c` | trace identities behind the compatibility lemma |
| `V5` | `5a`–`5d` | phase cocycle `F_a F_b = ζ F_{ab}`, including scalar and zero-eigenvalue cases |
| `V6` | `6a`–`6e` | S5 across the compatible cases |
| `V7` | `7a`–`7b` | compatibility, backward direction |
| `V8` | `8a`–`8c` | remaining displayed identities |
| `V9` | `9a`–`9e` | frame-dependence pair of `thm:qubit-boundary` |
| `V10` | `10a`–`10c` | auxiliary constant (critical point and boundary values) |

These corroborate finite calculations in exact arithmetic with the twist carried
as a free real parameter. They do not replace the proof, and they cover no
continuity, infinite-dimensional, or descent claim.
