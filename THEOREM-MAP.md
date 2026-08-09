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
  `Fin 2 → ℝ`, carry no interface fields at all.  The `lem:twist-sufficiency`
  row is likewise unconditional: it is proved on the concrete carrier
  `HermitianMat n ℂ` with no §2 structures anywhere in its closure.

| Paper statement | Lean declaration | File |
| --- | --- | --- |
| `mthm:master` — **dependency skeleton only**, see §3; the complex row is now proved concretely, see the subsection below | `MasterTheorem.master_chain` | `MasterTheorem/Master.lean` |
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
| `lem:twist-sufficiency` — every twist product satisfies S1–S7 on `H_n(ℂ)`, packaged per `t`; S2 holds in the carried norm AND (ε–δ, `twistSeq_continuousAt_ouNorm`) in the order-unit norm — the norm caveat is discharged for this row | `HermitianMat.twistSequentialProductCore`, `HermitianMat.twistSequentialProduct` | `Hermitian/Sequential.lean` |

### `lem:adjacent` — FORMALIZED, but it was an UNDERCOUNTED ROW, not new mathematics

★★ **Corrected 2026-08-08 by the arc-5 cold review, which refuted the first version of this
entry twice over. Read this, not the commit message.**

The row is FORMALIZED. Its honest witness is **`frameTwistConst`**
(`Necessity/ComplexRowUnconditional.lean`), which was **already in the tree at tag
`paperA-arc4`** and states that `frameTwist` is constant across *all* frames:
`∀ F G, frameTwist hN P hS2 F = frameTwist hN P hS2 G`. The article's `lem:adjacent` asks only
for equality across *adjacent* frames, so it is an immediate consequence — for any adjacency
relation whatsoever. The reviewer compiled exactly that: the conclusion of
`frameTwist_eq_of_adjBlock` with the hypothesis **deleted**, and again with an arbitrary
relation substituted. So this row belongs with `lem:aone` — a row carried as unproved while a
proof existed — and **not** with `cor:selectors`(ii) or the rank-two extraction, which are new
proofs. The arc-5 commit message for it overstates; this ledger governs.

`AdjBlock` and `frameTwist_eq_of_adjBlock` remain in the tree as documentation of what the
article's relation is in the tree's coordinates, and `adjAxis_of_adjBlock` (at rank `n ≥ 3` a
two-element block cannot exhaust `Fin N`, so an article-adjacent pair shares a whole coordinate
axis) is a true and mildly useful bridge. But they add no provable content.

★ **The fidelity note that was here — "`AdjBlock` is therefore a *superset* of the article's
relation, which makes the theorem stronger, not weaker" — is FALSE, and was refuted by a
compiled counterexample.** The reviewer exhibited the 3-cycle permutation of the standard basis
of `ℂ³`: its Jordan frame is *literally the standard frame* (`cyc_frame_is_standard`: every atom
maps to an atom of the same frame), yet `¬ AdjBlock 1 ⟨cyc, _⟩`. `AdjBlock` requires the
connecting unitary to be diagonal outside one index pair, which forbids **relabelling** the
shared atoms — while the article's frames are *unordered* sets of atoms (verified at source,
`main.tex`:1269–1273: "frames differing by a rotation inside a rank-two block … and **sharing
the atoms** `p₃,…,p_n`") and its `t_F` is a function of the unordered frame. So `AdjBlock` is
neither a superset nor a subset of the article's relation: it is a relation on *labelled*
frames. Do not repeat the superset claim.

The relation is still pinned from both sides, which is worth keeping:
`adjBlock_one_house_pair` exhibits a pair with `F ≠ G` satisfying it, and
`not_adjAxis_one_house` shows the coarser relation is not total.

★ **`lem:frame-connectivity` does NOT come along with it, and the ARC-5 orders were wrong to
pair them.** `AdjBlock` is *strictly finer* than `AdjAxis`: the former fixes all but two axes,
the latter merely some axis. Connectivity for a finer relation is a *stronger* statement, so
`adjAxis_connected` cannot supply it. The article's graph needs every unitary to factor into
rank-two block rotations — a Givens/Jacobi decomposition — where the tree currently has
`exists_axisFixing_factor`, three axis-fixing Householder factors. That row stays PARTIAL and
the remainder is exactly the Givens decomposition.

### `lem:homog`(ii) — at abstract order-unit-space generality (2026-08-08, ARC-6 rung 6.3)

`SequentialProductOn.sp_smul_left` : for `[OrderUnitSpace V]`, a `SequentialProductOn V`,
`OrderUnitSpace.IsArchimedean V`, S2, and effects `a b` with `t ∈ [0,1]`,
`P.sp (t • a) b = t • P.sp a b`.

**Why this counts at the article's generality.** The article states `lem:homog` with ambient
`J`; a Euclidean Jordan algebra is in particular an order unit space, and the proof here uses
*nothing* about the carrier beyond the order-unit structure — no Jordan product, no norm, no
matrices. So the abstract statement subsumes the article's.

★ **The precise scope, stated so it cannot drift** (this is the correction arc-5's cold review
forced on `lem:span`, applied here pre-emptively): the `OrderUnitSpace` *class* extends
`NormedAddCommGroup`, so this is not a statement about every mathematician's order unit space —
those carry no norm. It is a statement about every instance of this interface, and the norm
plays no role in either the statement or the proof of `sp_smul_left`. What matters for the row
is that **every EJA instantiates the interface**, which is the article's ambient, so nothing
the article claims is left uncovered. Say "at the generality of this tree's order-unit
interface, which covers every EJA" — never "at full order-unit-space generality". The one
hypothesis added, `IsArchimedean`, is part of the *definition* of the article's order unit
space (the class's `archimedean` field is order-unit boundedness only — the long-standing
caveat 1), not a located stand-in for a cited result. Note also that the article merely
*cites* this clause — van de Wetering's Proposition 3.9, with S2 substituted for his σ-SEA
infimum passage — whereas Lean proves it from S1–S7 + S2.

**The ladder, all abstract, in `SequentialProduct.lean`:** second argument —
`sp_natSmul_right`, `sp_divNat_smul_right`, `sp_ratSmul_right`,
`sp_smul_right_of_unitInterval` (this is where Archimedean is consumed, as the ε-squeeze);
first argument — `sp_comm_natSmul`, `sp_comm_ratSmul_self`, `sp_comm_ratOneSmul`,
`sp_ratOneSmul_left`, `sp_smulOne_left` (the single S2 use, by rational approximation),
`sp_smul_left`. Closure `[propext, Classical.choice, Quot.sound]` throughout; census still
149 modules, custom axioms exactly `[]`. Three small order lemmas were added to
`OrderUnitSpace.lean` for the port (`sub_le_sub_right'`, `sub_le_sub_left'`,
`le_of_sub_nonpos`) because Mathlib's versions need ordered-group instances this class does
not provide.

★ **This discharges the obstruction recorded at rung 5.1** ("generalizing is not a change of
variable block"). It was correct that Archimedean is needed and that the class does not carry
it; it was *incomplete* in implying the work was therefore large. Supplied as a `Prop`, the
ladder ports essentially verbatim. The concrete versions in
`Necessity/LeftMultiplication.lean` and `Necessity/FirstArgument.lean` are untouched.

### `lem:span` — the two load-bearing clauses, at full abstract generality (2026-08-08)

`OrderUnitSpace.span_isEffect_eq_top` and `OrderUnitSpace.linearMap_eq_of_eq_on_effects`
(`OrderUnitSpace.lean`): over an arbitrary `[OrderUnitSpace V]`, the effects span `V` and two
linear maps agreeing on effects are equal. Previously this existed only on the concrete
carrier (`Necessity.span_isEffect_eq_top`, still there and still used).

**It is proved from order-unit boundedness alone** — no norm and no Archimedean property.
That matters because the article's proof goes through the *norm* (`‖v‖ ≤ ½ ⟹ 0 ≤ ½𝟙+v ≤ 𝟙`),
which this interface cannot express: its carried norm is not asserted to be the order-unit
norm and its `archimedean` field is only boundedness. The route here — bound `x` above by
`r•𝟙` and `-x` above by `s•𝟙`, rescale `x + s•𝟙` by `r+s+1` into the effects — needs
neither, so it is strictly more general than the article's argument at exactly the
interface's own strength.

The row stays **PARTIAL**. Not formalized: the ball clause (`eff V` contains the ball of
radius ½ about ½𝟙), which genuinely needs both missing properties and is the article's route
rather than its content; and the Peirce clause, which the article obtains by *instantiating*
this same lemma at the order unit space `(J_2(q), q)` — so it comes for free the moment the
tree knows a Peirce 2-subalgebra is an order unit space, which it does not.

### `AdjAxis` non-vacuity — now a theorem, not a docstring (2026-08-08)

`Necessity.adjAxis_not_total` (`Necessity/UnitaryGeneration.lean`), with witness
`not_adjAxis_one_house`: for `N ≥ 2`, the identity frame is **not** axis-adjacent to the
Householder reflection in the all-ones direction, whose off-diagonal entries are uniformly
`-2/N ≠ 0` so that it fixes no coordinate axis. This closes the caveat that
`adjAxis_connected` might be vacuous: if `AdjAxis` were total, the walk would always be one
step and the Householder factorization would be doing no work.

★ **This supersedes a caveat that said the opposite.** The supplementary caveat list read
"that non-vacuity is asserted in a docstring but is not itself a theorem of the tree … until
then it should not be described as machine-checked." It now is one, and the staged
supplementary text (blog `research/paperA-supplementary-rewrite-draft.md`, caveat 2) has been
rewritten rather than annotated.

### `cor:selectors` clause (ii) — machine-checked at article generality (2026-08-08)

`Necessity.selector_traceSymm` (`Necessity/ComplexRowUnconditional.lean`): for an S1–S7
product with S2 on `H_N(ℂ)`, `N ≥ 3`, trace-form symmetry `⟪a·b, c⟫ = ⟪b, a·c⟫` on
effects forces the Lüders product, stated both as `twistSeq 0` and (in
`selector_traceSymm_luders`) as `b.conj √a`. Hypotheses are exactly the article's; closure
is Lean core. Supporting lemmas, also new: `inner_twistSeq_left` (the twist product's trace
adjoint flips `t`, by trace cyclicity plus `twistFactor_conjTranspose`) and
`eq_of_inner_effect_eq` (effects are trace-form separating, from `span_isEffect_eq_top` and
definiteness). The proof is a corollary of the classification's `∃!`: trace symmetry makes
`-t` a second representing parameter, so `-t = t`.

**Clauses (i) and (iii) are not proved, and the row stays PARTIAL.** Banked with the
remainder measured rather than guessed: clause (iii) — covariance under every unital order
automorphism, for which the article notes the transpose suffices — is blocked on exactly one
absent lemma, `(cfc f a)ᵀ = cfc f (aᵀ)`, i.e. that transposition commutes with the real
functional calculus. Nothing in this tree has it, and the route is written out in the
module docstring (`StarAlgHomClass.map_cfc` applied to entrywise complex conjugation, which
is an ℝ-star-algebra hom of `Matrix n n ℂ` since conjugation does not reverse products;
build it from `AlgHom.mapMatrix Complex.conjAe.toAlgHom` with a `map_star'` field, and use
`aᵀ = conj a` for Hermitian `a`). With that lemma, `transposeMap (twistSeq t a b) =
twistSeq (-t) (transposeMap a) (transposeMap b)` and clause (iii) closes by the same
uniqueness step. Clause (i) additionally needs the coherence-block action on `H_N(ℂ)`.

### `lem:aone` — machine-checked at full abstract generality (recorded 2026-08-08)

★ **This row was carried as "no Lean counterpart" and that was wrong.**
`SequentialProduct.sp_unit_right` (`SequentialProduct.lean`:163) states
`IsEffect a → a & 𝟙 = a` over an arbitrary `[SequentialProductCore V]` — i.e. over any
order-unit space with an S1, S3–S7 product — and proves it by the article's own route:
`a·0 = 0` from S1, `0·a = 0` from S4, hence `a |' 0`, then S6a to `a |' 𝟙`, then S3.
Closure is exactly `[propext, Classical.choice, Quot.sound]` (verified by `#print axioms`).
S2 is *not* used, matching the article's hypothesis accounting (S1/S3/S4/S6).

Two honest qualifications, neither new to this row: it inherits the tree-wide `sp_effect`
codomain condition carried as a structure field (the standing caveat that applies equally
to both flagship rows), and it is covered by the Layer-1 census — which visits every
persisted declaration — but is **not** one of the Layer-2 exact-closure sentinels, so
"pinned by `#guard_msgs`" does not apply to it. The correction was found by writing
`STATEMENT-MANIFEST.md`, which is the argument for having written it.

### The complex row of `mthm:master`, on the concrete carrier (2026-08-06)

Everything above quantifies over the §2 *interface structures*. The rows below
are different in kind: they are proved **on the concrete carrier**
`HermitianMat (Fin N) ℂ` about an arbitrary pinned product
`P : SequentialProductOn (HermitianMat (Fin N) ℂ)`, so no §2 field is assumed.
The comparison map's Jordan property — the manuscript's `prop:theta`, formerly
the `ComparisonSetup.Θ_jordan` field of §2 — is **derived** here
(`Necessity.thetaPreservesJordan_of_S2`, M3, Kadison rigidity through the
vendored `Projectivization.wigner_rigidity`).

| Paper statement | Lean declaration | File |
| --- | --- | --- |
| `mthm:master`, **complex row**: `∃! t`, `a • b = a^{1/2+it} b a^{1/2−it}` on **all** effects — **UNCONDITIONAL** | `Necessity.complex_classification_unconditional` | `Necessity/ComplexRowUnconditional.lean` |
| the same, with the manuscript's two frame-graph facts as located hypotheses | `Necessity.complex_classification` | `Necessity/ComplexMaster.lean` |
| the same, with the frame-graph apparatus replaced by one internal hypothesis (`frameTwist` constant) | `Necessity.complex_classification_of_frameTwistConst` | `Necessity/ComplexResidue.lean` |
| **the residue, discharged**: `frameTwist` is constant | `Necessity.frameTwistConst` | `Necessity/ComplexRowUnconditional.lean` |
| cross-coherence: axis-adjacent frames have equal twist parameter | `Necessity.frameTwist_eq_of_adjAxis` | `Necessity/FrameConstancy.lean` |
| `lem:frame-connectivity`: any two frames are joined by an axis-adjacency walk | `Necessity.adjAxis_connected` | `Necessity/UnitaryGeneration.lean` |
| every unitary is a product of three axis-fixing unitaries (`N ≥ 3`) | `Necessity.exists_axisFixing_factor` | `Necessity/UnitaryGeneration.lean` |
| the twist form at an arbitrary frame (frame a free parameter) | `Necessity.sp_eq_twistSeq_frame` | `Necessity/FrameConstancy.lean` |
| **non-vacuity**: the hypothesis class is inhabited | `Necessity.twistProductOn_classified` | `Necessity/ComplexRowUnconditional.lean` |
| **sharpness**: the capstone recovers `t` on `twistProductOn t` | `Necessity.complex_classification_sharp` | `Necessity/ComplexRowUnconditional.lean` |
| the per-frame parameter is unique, so `frameTwist` is an invariant of the frame | `Necessity.frameTwist_unique` | `Necessity/ComplexResidue.lean` |
| the same, invertible effects only, one global `t` | `Necessity.sp_eq_twistSeq_of_frameGraph` | `Necessity/ComplexMaster.lean` |
| `prop:singular` **applied** (invertible ⟹ all effects) | `Necessity.sp_eq_twistSeq_of_effect` | `Necessity/ComplexClassification.lean` |
| uniqueness of the twist parameter | `Necessity.twist_param_unique` | `Necessity/TwistUniqueness.lean` |
| `prop:theta` (`Θ` is a Jordan automorphism) — **derived, no longer assumed** | `Necessity.thetaPreservesJordan_of_S2` | `Necessity/KadisonDischarge.lean` |
| complex Kadison **CLASSIFIED** (2026-08-08): a unital order-automorphism of `H_N(ℂ)` is `Ad_U` or `Ad_U∘ᵗ` for a unitary `U` — stronger than `prop:theta`, which needs only the Jordan corollary | `Necessity.orderAuto_classification` | `Necessity/KadisonDischarge.lean` |
| the converse, so the ℂ classification is **exact** in BOTH branches: `Ad_U` and `Ad_U∘ᵗ` are each unital order-automorphisms | `Necessity.unitaryConj_orderAuto`, `Necessity.antiunitaryConj_orderAuto`, `Necessity.orderAuto_classification_realized` | `Necessity/KadisonDischarge.lean` |

**Exact hypothesis accounting for `complex_classification_unconditional` (2026-08-07)**:
the `SequentialProductOn` fields (S1, S3–S7); S2 (`P.FirstArgContinuous`); and `3 ≤ N`.
That is the paper's own list — the row is **UNCONDITIONAL** and may be described as such.
Verified by `#check`, not by prose:

```
@Necessity.complex_classification_unconditional : ∀ {N : ℕ}, 3 ≤ N →
  ∀ (P : SequentialProductOn (HermitianMat (Fin N) ℂ)), P.FirstArgContinuous →
    ∃! t, ∀ (a b), IsEffect a → IsEffect b → P.sp a b = HermitianMat.twistSeq t a b
```

`#print axioms` is Lean core only (`propext`, `Classical.choice`, `Quot.sound`).

**What changed, precisely.** `complex_classification` still takes the manuscript's two
frame-graph facts as located hypotheses — `connected` (`lem:frame-connectivity`) and
`overlap` (cross-coherence of adjacent frames' `U(1)` characters). Both are now **theorems
of this development**, so the located form is no longer the best available statement.
Prefer `complex_classification_unconditional` when citing the row. The discharge chain:

* `sp_eq_twistSeq_frame` — `ComplexMaster`'s chain with the frame left a free parameter
  instead of specialized to `a.H.eigenvectorUnitary`. This is what lets two different frames
  that diagonalize the *same* base point be compared at all.
* `frameTwist_eq_of_adjAxis` — cross-coherence. If `F* G` fixes a coordinate axis `m`, the
  scaled family `Ad_F (diagFamily (x • s))`, with `s` two-valued across `{m} ⊕ {m}ᶜ`,
  commutes with `F* G` and so is diagonal in both frames. The workhorse computes the product
  at it twice; reading the `(m, m')` entry against the pair projection over an *interval* of
  `x` and applying `real_character_unique` forces `frameTwist F = frameTwist G` exactly. The
  interval is not optional: a single base point pins the difference only mod `2π/(r_m − r_m')`.
* `adjAxis_connected` — connectivity, from `exists_axisFixing_factor`: two Householder
  reflections clear the first column of `F⁻¹G` onto one axis, and a unitary whose column is
  supported on one axis fixes that axis. A reflection `1 − 2ww*/⟪w,w⟫` fixes every axis its
  vector misses, which is what makes it usable as an adjacency step; `N ≥ 3` is exactly what
  frees the axis the second reflection must miss.

**Two vacuity questions are answered in the tree, not by argument.** A theorem quantified over a
hypothesis class says nothing if the class is empty, and a theorem producing a parameter says
little if the parameter need not be the intended one. `twistProductOn_classified` instantiates
the capstone at M1's twist product, so `3 ≤ N` + S1–S7 + S2 are demonstrably simultaneously
satisfiable; `complex_classification_sharp` shows the unique parameter returned for
`twistProductOn t` is `t` itself. This is the same discipline that closed the OpCommute
vacuity-escape class: construct the witness rather than assert the non-emptiness.

**Superseded claim, do not restore.** The prior entry read that the residue is
"sufficient, not proved equivalent — write 'suffices for', not 'equivalent to'". That
caution applied to `FrameTwistConst` as a *carried* hypothesis. It is now discharged
outright, so the row needs no such qualifier. `frameTwist_unique` remains true and is what
makes `frameTwist` an invariant rather than a `choose` artefact; the *converse* direction
(that the row's conclusion forces `frameTwist` constant) is still not proved, and nothing
in this development claims it.

### The real row of `mthm:master`, on the concrete carrier (2026-08-06)

Same kind as the complex block above — proved on the concrete carrier about an
arbitrary pinned `P : SequentialProductOn (HermitianMat n ℝ)`, no §2 field assumed —
and the Jordan property of the comparison map is **derived, not carried**.

**CORRECTED 2026-08-08.** This block previously read "over ℝ the Jordan property is
carried, not derived… real Kadison/Uhlhorn exists in no proof assistant," which was
true when written (2026-08-06) and was already contradicted by its own table rows
below by 08-07. The actual state: M3's ℂ discharge routes through the vendored
`Projectivization.wigner_rigidity`, which is intrinsically complex, so the real
analogue had to be **proved from scratch in this tree** —
`Projectivization.exists_isometry_of_transProbPreservingR`
(`Wigner/RealWigner.lean`, first-party, no bijectivity hypothesis) → real Kadison
`Necessity.orderAutoR_preservesJordan` (`RealKadison.lean`) →
`Necessity.thetaPreservesJordanR_of_S2` (`RealRowUnconditional.lean`), which supplies
`ThetaPreservesJordanG` from S2 alone. `ThetaPreservesJordanG` is therefore a
hypothesis of the *intermediate* declarations in `RealRigidity.lean` (row 2 of the
table) and of nothing the row itself depends on: `real_classification` is
unconditional. The manuscript's van Imhoff–Roelands citation for this step is, in this
tree, a theorem.

| Paper statement | Lean declaration | File |
| --- | --- | --- |
| `prop:real`, **real row**: `a • b = √a·b·√a` on **all** effects, no twist parameter — **UNCONDITIONAL** | `Necessity.real_classification` | `Necessity/RealRowUnconditional.lean` |
| the same, with the eigenframe Jordan property as a hypothesis | `Necessity.sp_eq_luders_of_effect` | `Necessity/RealRigidity.lean` |
| real Kadison **CLASSIFIED** (2026-08-08): a unital order-automorphism of `H_N(ℝ)` **is** `Ad_O` for an orthogonal `O` — no dichotomy, no transpose branch | `Necessity.orderAutoR_eq_orthConj` | `Necessity/RealKadison.lean` |
| the converse, so the classification is exact: `Ad_O` *is* a unital order-automorphism | `Necessity.orthConj_orderAuto` | `Necessity/RealKadison.lean` |
| real Kadison, the Jordan corollary (the form the row consumes) | `Necessity.orderAutoR_preservesJordan` | `Necessity/RealKadison.lean` |
| real Wigner rigidity: a transition-probability preserving ray map is induced by an isometry | `Projectivization.exists_isometry_of_transProbPreservingR` | `Wigner/RealWigner.lean` (first-party) |
| the same, invertible effects only | `Necessity.sp_eq_luders_of_posDef` | `Necessity/RealRigidity.lean` |
| the comparison character is the identity (`Θ_a = id`) | `Necessity.chiTilde_eq_id` | `Necessity/RealRigidity.lean` |
| `prop:singular` applied over ℝ | `Necessity.dense_posDef_effectsR` + `MasterTheorem.prop_singular` | `Necessity/RealRigidity.lean` |

**Exact hypothesis accounting for `real_classification` (2026-08-07)**: the
`SequentialProductOn` fields (S1, S3–S7); S2; and `0 < N`. That is the paper's own list —
the row is **UNCONDITIONAL** and may be described as such. `#print axioms` is Lean core
only (`propext`, `Classical.choice`, `Quot.sound`).

`sp_eq_luders_of_effect` remains as stated, carrying `ThetaPreservesJordanG` in each
eigenframe; `real_classification` is that theorem with the hypothesis discharged by
`thetaPreservesJordanR_of_S2`, which applies real Kadison to the comparison map. Prefer
`real_classification` when citing the row.

Two accuracy notes. (i) The ℂ row's Wigner input is a vendored **proof**, not an axiom, so
"ℝ avoids an import that ℂ needs" is FALSE — both rows close over Lean core. What ℝ lacked
was a theorem that existed in no library, and it is now proved here. (ii) The
unconditional statement is at `n := Fin N`; `sp_eq_luders_of_effect` is stated at generic
`n`, and the Kadison bridge is `Fin N`-bound because it needs `Matrix.toEuclideanLin`.

**Standing as of 2026-08-07: both flagship rows are unconditional.** `H_N(ℂ)` for `N ≥ 3`
(`complex_classification_unconditional`) and `H_n(ℝ)` (`real_classification`) each carry
exactly S1–S7 + S2 + a dimension bound, and each closes over Lean core alone. Neither row is
"better founded" than the other on axioms — that axis is identical. The remaining rows of
`mthm:master` are unchanged: `H_n(ℍ)` has its foundation built but is blocked on quaternionic
Wigner rigidity, and `H₃(𝕆)` is ABSENT.

★★**CORRECTION 2026-08-08 — "`H₃(𝕆)` is blocked on octonions, which exist in no prover" was
FALSE and is retracted.** Verified at source this session. It is true of *Mathlib* (the four
`octonion` hits are prose comments; Mathlib does however have `IsJordan`/`IsCommJordan` in
`Algebra/Jordan/Basic.lean`, so the archive's "no Jordan-algebra files at all" is also
retracted). It is **false of our own work**: `~/repos/research/lean/RadicalRelativity/`
`Octonions.lean` is 310 lines, 37 declarations, **zero sorries**, on the **same toolchain**
(`v4.28.0`) — explicit Cayley-table `mul`, `conj` proved an anti-automorphism (`conj_mul`),
`norm_multiplicative`, `mul_conj`, both alternativity laws, all three Moufang identities, and
full bilinearity. That is precisely the input list `ALBERT-KERNEL-MEMO.md` §2 says the row
consumes. The memo (2026-08-04) already re-scoped this row to "weeks of equational algebra";
that re-scope was never propagated into this summary. **The status word is ABSENT (nobody has
built the row), never BLOCKED (no wall).** See `LEDGER.md`'s `H₃(𝕆)` row for the work list.

Same session, the memo's one remaining computational input was **proved**:
`Octonion.nucleus_real` (`~/repos/research/lean/RadicalRelativity/OctonionNucleus.lean`) —
associating with every pair forces all seven imaginary coordinates to vanish, i.e.
`nucleus(𝕆) = ℝ·1`. Axioms `[propext, Classical.choice, Quot.sound]`, no `native_decide`,
that project's `lake build` green at 2862 jobs. **It is OUT-OF-TREE**: it lives in the
`lean/` project, not in `twist-normal-form-lean/`, so it is outside this campaign's census
and manifest and contributes nothing to the coverage count (**8/36** as of 2026-08-08, after ARC-6) until ported.

The supporting field-general infrastructure (of independent interest, all
`RCLike 𝕜`): `HermitianMat.sqrt_mul_of_commute` (square roots multiply on commuting
positives — absent from Mathlib), `HermitianMat.eq_zero_of_commute_hermitian_of_trace_zero`
(the commutant kill), `HermitianMat.continuous_cfc_polynomial` and
`HermitianMat.continuousOn_cfc_sqrt_effects` (continuity of the functional calculus
with **no C⋆ machinery** — Mathlib's `CStarAlgebra` class is complex by definition, so
its own continuity lemma cannot be generalized).

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

**The frozen shapes are now MET, for the ℝ and ℂ rows (2026-08-07).**
`PaperA/Statement.lean` deliberately leaves the Lüders and twist reference maps as
*parameters*, and its original docstring said the concrete maps "do not yet exist in this
development." They exist now, and `PaperA/CertifiedConfiguration.lean` closes the loop:

| Paper statement | Lean declaration | File |
| --- | --- | --- |
| the real row satisfies the frozen Lüders shape | `PaperA.real_meets_ludersConclusion` | `PaperA/CertifiedConfiguration.lean` |
| the complex row satisfies the frozen unique-twist shape | `PaperA.complex_meets_uniqueTwistConclusion` | `PaperA/CertifiedConfiguration.lean` |
| the concrete reference maps, effect closure proved | `PaperA.ludersRefR`, `PaperA.twistRefC` | `PaperA/CertifiedConfiguration.lean` |
| pinned product + S2 is a `SequentialProduct` instance | `SequentialProductOn.toSequentialProduct` | `PaperA/CertifiedConfiguration.lean` |
| `√a · √a = a`, field-general | `HermitianMat.cfcSqrt_mul_self` | `PaperA/CertifiedConfiguration.lean` |

Both are Lean-core. What this establishes and nothing more: for `H_N(ℝ)` and `H_N(ℂ)` (`N ≥ 3`)
the *audited shape* and the *proved theorem* are the same statement, so neither capstone can be
described as a theorem about the paper's sequential product while concluding something weaker.
The reference maps are no longer parameters that a caller could instantiate favourably — they
are pinned to conj-Lüders and `HermitianMat.twistSeq`. **For `H_n(ℍ)` and `H₃(𝕆)` the shapes
remain shapes**: there is no theorem to point at, and constructing the proposition is still not
evidence that it holds.

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
pin does establish.  **On the concrete carrier this caveat is now discharged**
(LEDGER 1.4, 2026-08-05): `HermitianMat.ouNorm` carries the two-sided comparison
`ouNorm ≤ ‖·‖ ≤ √(card n) · ouNorm` (`ouNorm_le_norm`,
`norm_le_sqrt_card_mul_ouNorm`, `Hermitian/OrderUnit.lean`), and
`twistSeq_continuousAt_ouNorm` (`Hermitian/Sequential.lean`) states first-argument
ε–δ continuity of the twist product *in the order-unit norm itself* — the paper's
literal (S2) for `lem:twist-sufficiency`.

**CLOSED for the necessity direction too, 2026-08-08 (LEDGER 4.2).** What remained
was the *necessity* rows' S2 hypothesis: a two-sided comparison of norms is not by
itself a statement about `ContinuousOn`, and `ContinuousOn` cannot express
"continuous in the order-unit norm" at all, because the carrier has exactly one
`TopologicalSpace` instance and it is the Frobenius one. So the order-unit
hypothesis is written out in ε–δ form against `ouNorm` on both sides of the map —
which is how the manuscript states (S2) — and proved equivalent:

| Paper statement | Lean declaration | File |
| --- | --- | --- |
| (S2) as the manuscript states it: ε–δ first-argument continuity on effects in `‖·‖_e` | `HermitianMat.ContinuousOnOu`, `Necessity.FirstArgContinuousOu` | `Necessity/OrderUnitS2.lean` |
| order-unit-norm continuity ⟺ `ContinuousOn` on the concrete carrier | `HermitianMat.continuousOnOu_iff_continuousOn`, `Necessity.firstArgContinuousOu_iff` | `Necessity/OrderUnitS2.lean` |
| `mthm:master` real row, S2 in the order-unit norm | `Necessity.real_classification_ouNorm` | `Necessity/OrderUnitS2.lean` |
| `mthm:master` complex row, S2 in the order-unit norm | `Necessity.complex_classification_unconditional_ouNorm` | `Necessity/OrderUnitS2.lean` |

Both `_ouNorm` capstones have the same conclusions and the same closure (Lean core)
as the rows they wrap; the only change is that no prose argument about which norm
(S2) refers to is load-bearing any more. The residual caveat is now *only* about the
abstract interface: generic `OrderUnitSpace` still never identifies its carried norm
with the order-unit norm, so the bridge is a theorem about `HermitianMat n 𝕜`
(where the sandwich is available), not about the abstract class. Since both flagship
rows live on that concrete carrier, no row depends on the abstract gap.

### M1 carrier layer (supporting infrastructure, no paper labels)

Census-tracked (49-module manifest), closure = Lean core only:

- `RadicalRelativity/Hermitian/OrderUnit.lean` — `OrderUnitSpace (HermitianMat n 𝕜)`
  instance over the vendored carrier (parents = the existing vendored instances; the
  abstract `OrderUnitSpace.IsEffect` becomes *definitionally* the Loewner unit
  interval, so `Effect (HermitianMat n ℂ)` is the intended effect space and the
  vendored compactness applies verbatim); order-unit boundedness with explicit
  witness `r = ‖a‖`; the **full Archimedean property** over ℂ (strictly stronger
  than the class's order-unit-boundedness field); the order-unit norm `ouNorm` as
  an unbundled def with attainment, minimality, negation/triangle, definiteness,
  and the two-sided carried-norm comparison `ouNorm ≤ ‖·‖ ≤ √(card n) · ouNorm`
  (LEDGER 1.4, via `abs_eigenvalues_le_ouNorm`).
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
  closure, and the `t = 0` Lüders specialization.
- `RadicalRelativity/Hermitian/Resolution.lean` — value-indexed spectral
  projections `specProj a μ := a.cfc 1_{x=μ}` with the expansion of *every*
  `a.cfc f` over them (`mat_cfc_eq_sum_specProj`), and the **resolution lemma**
  (`mat_cfc_of_resolution`): the functional calculus respects any presentation of
  `M` by a pairwise-orthogonal idempotent family summing to `1`, proved by
  Lagrange interpolation at the nodes `{c i} ∪ σ(M)` plus ring algebra — no
  simultaneous-diagonalization machinery anywhere.
- `RadicalRelativity/Hermitian/Sequential.lean` — the S1–S7 verification
  (LEDGER 1.3, `lem:twist-sufficiency`): S4 by the trace route (a PSD matrix with
  zero trace is zero); **compatibility ⟺ commutation** — the forward direction is
  the Frobenius certificate `tr(C·Cᴴ) = 0` for `C = [b^{1/2+it}, a]` (Gudder–Nagy
  normality trick at general twist), the converse rides the vendored
  `Commute.cfc_right`; the two-variable law `(ab)^{1/2+it} = a^{1/2+it}·b^{1/2+it}`
  on commuting positives via the joint resolution `P_μ·Q_ν` and the resolution
  lemma, with the scalar character law handling zero eigenvalues definitionally;
  S5–S7 from these; S2 as *global* norm continuity of `a ↦ a &ₜ b` (squeeze at the
  spectral origin); and the packaged `twistSequentialProductCore` /
  `twistSequentialProduct` per twist parameter `t`.

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
intended instances is `LEDGER.md`. **As of 2026-08-05 a concrete instance
exists**: `Necessity.comparisonSetup : ComparisonSetup (HermitianMat (Fin N) ℂ)`
(`Necessity/ComparisonInstance.lean`), with every field discharged by a proved
theorem of the necessity development except `Θ_jordan`, which enters as the
isolated hypothesis `ThetaPreservesJordan` (= campaign milestone M3). The rows
below describe the *interface*; the instance column of truth for what is still
imported on `H_N(ℂ)` is that single hypothesis plus the S2 continuity field.

| Structure | File |
| --- | --- |
| `ComparisonSetup`, `StabilizerCoupling` | `MasterTheorem/Interface.lean` |
| `CoalescenceSetup` | `MasterTheorem/Coalescence.lean` |
| `DiagonalHomSetup` | `MasterTheorem/DiagonalHom.lean` |
| `IsAlbertModel` | `MasterTheorem/Branches/Albert.lean` |

| Field | Cited source | Paper location |
| --- | --- | --- |
| `ComparisonSetup.Θ_jordan` | van de Wetering Prop. 5.3 + van Imhoff–Roelands Cor. 2.5 / Prop. 2.6, taken as the imported *conclusion*: the Lean structure does not encode the JB-algebra premises | `prop:theta` |
| `ComparisonSetup.Θ_fix` | van de Wetering Prop. 5.5. **Stronger than the source as stated**: the field quantifies over all of `J`, the source is effect-level. On the concrete carrier the span extension IS now Lean's (`Necessity.theta_fix_general`, 2026-08-05, via `b = b⁺ − b⁻` + normalization), and so is the compatibility bridge it rides on (`Necessity.opCommute_iff_commute`: Jordan-operator commutation = matrix commutation, quarter identity `[L_a,L_b]y = ¼[[a,b],y]`) | `prop:theta` |
| `ComparisonSetup`'s use of `aOf r` outside the negative orthant | van de Wetering's normalization extension `Θ_{λq} = Θ_q`, which defines `Θ_q` for arbitrary positive order-preserving `q` after rescaling. On the concrete carrier this is proved: `Necessity.thetaNorm` (total on PosDef points) + the 2.3 law `theta_smul` | `lem:cone-ext` |
| comparison cocycle | van de Wetering Prop. 5.7, specialized to the commuting diagonal family — **weaker** than the source, not stronger | `prop:theta` |
| `DiagonalHomSetup.dχAdd`, `dχAdd_cont`, differentiated coalescence | **not a rendering of one cited theorem**: as *skeleton fields* these are hypotheses, assumed where the abstract interface needs them. **Corrected 2026-08-08 (ARC-6 rung 6.0): the old wording here — "Lean neither differentiates `Θ` nor proves `dχAdd` is its derivative" — was FALSE on the concrete carrier**, and it is the sentence that had `lem:homomorphism` carried as ABSENT. `Necessity.chiTilde_eq_exp` *proves* `∃!` real-linear `dχ` with `χ̃ = exp ∘ dχ`, from the homomorphism law (`chiTilde_add`) plus line continuity (`continuous_chiTilde_line`) via `multiParameter_eq_exp` — so on `H_n(ℂ)` the additivity and continuity these fields carry are derived, not assumed, and by a route that imports no Lie theory. See §3c | `lem:homomorphism` |
| `IsAlbertModel.block_injective` | Yokota's triality identification of the pointwise frame stabilizer with `Spin(8)`, **plus** a standard simplicity/kernel argument (nontrivial representation of a simple Lie algebra has zero kernel). Injectivity is a composite consequence, not Yokota's literal text | `thm:albert` |

NO cited result remains as an `axiom` declaration (as of 2026-08-05 the
tracked tree's every closure is exactly Lean's three core axioms):

- `Selection.aczel_continuous_multiplicative` — **DISCHARGED 2026-08-05
  (`LEDGER.md` 2.7).** Formerly the sole custom axiom (Aczél scalar lineage +
  Engel–Nagel operator form). Now a theorem: the from-scratch continuous
  one-parameter-semigroup classification `Necessity.oneParameter_eq_exp` +
  the `Real.exp`-substitution wrapper
  (`RadicalRelativity/Necessity/OneParameter.lean`); the historical name and
  signature are preserved at the original declaration site, and the Layer-4
  pin now freezes the THEOREM's statement.
- `TwistNormalForm.bgw_canonical_composite` — **ELIMINATED 2026-08-04
  (`LEDGER.md` 2.8).** The former axiom asserted the existence of an operation
  with nine specified table values — a constructible statement that cannot be
  false — and it quantified over all natural-number labels, broader than the
  BGW citation (the attribution imprecision previously flagged here). It is now
  the definition `TwistNormalForm.bgwComposite` with the nine rows proved by
  `rfl` (`bgwComposite_table`); the Barnum–Graydon–Wilce 2020 citation attaches
  to the table's *interpretation* (that it is their canonical standard-embedding
  composite), as prose provenance in the module docstring — which is all
  `#print axioms` ever certified anyway. The tracked tree now carries
  ZERO custom axioms.

## 3. Not machine-checked at all

State these plainly rather than inferring coverage from a green build. This list
is intended to be exhaustive; where it and the supplement's inventory differ, the
supplement governs.

**Supplied rather than derived, in addition to the interface fields of §2:** the
operator-to-character translation on the cross-coherence space; the geometric
two-plane frame-connectivity move; the concrete `(S2)` and invertible-density
inputs; the remaining rank-two cocycle and compatibility cases; and the contents
of the cited van de Wetering propositions themselves.
★ **"The construction of the comparison character and its differential from `Θ_a`" was the
first item on this list and has been REMOVED (2026-08-08, ARC-6 rung 6.0): it is false on the
concrete carrier.** `Necessity.chiTilde` constructs the character from `Θ` by the article's
own `min(x,0)` decomposition, `chiTilde_add` proves it a homomorphism, and
`chiTilde_eq_exp` derives the real-linear differential — see §3c. As in the arc-5 review, the
governing file was the one asserting the stale claim, and it was doing so in a *summary*
position where a reader stops.  (The complete seven-axiom
verification of the twist products — formerly on this list — is now
machine-checked on the concrete carrier: `lem:twist-sufficiency` in §1.)

**Statements with no Lean counterpart:**

- **`mthm:master` itself.** `master_chain` audits the *composition* of the case
  split over one abstract algebra; it constructs no concrete simple EJA, and does
  not prove that a given algebra is of a particular coordinate type, that an
  operation satisfies S1–S7, that `L_a = Q_{√a}Θ_a`, that `Θ_a = id`, or any
  product equality. Its own docstring says so.
- **Rank two: `lem:n2-bounded` and the assembled bijection `cor:qubit-classification`.**
  ★ `lem:n2-descent` and `lem:n2-continuity` were listed here and have been MOVED OUT
  (2026-08-08): this section's heading is "no Lean counterpart", and both have one —
  `STATEMENT-MANIFEST.md` rows 33/34 rate them PARTIAL against ten named declarations, and
  as of the arc-5 cold review `lem:n2-descent`'s **frame-reversal clause is proved for an
  arbitrary product** (`Necessity.n2FrameTwist_reverse`). Leaving them here made this file —
  the one the manifest designates as governing — imply a count of 7/17/12 against the
  manifest's 7/19/10. The manifest's rating is the correct one. (The lifting step of `prop:n2-necessity` was on
  this list and has come off it — see the correction below.)

  ★★ **SUPERSEDED IN PART, 2026-08-08 (ARC-5 rung 5.3).** The entry below read: "the
  **classification map `product ↦ moduli` does not exist in Lean at all**", and inferred
  that from `grep -c SequentialProductOn RadicalRelativity/RankTwo/*.lean` → 0. **The grep
  is still accurate and the inference was wrong.** The map's input now exists, built in
  `Necessity/FrameConstancy.lean` (section `RankTwoExtraction`) rather than in `RankTwo/`,
  which is why a `RankTwo/`-scoped grep could not see it and why scoping an absence claim to
  a directory is the same mistake as scoping one to a library:

  * `Necessity.n2FrameTwist : (P : SequentialProductOn (H₂(ℂ))) → P.FirstArgContinuous →
    U(2) → ℝ` — **the frame function, extracted from an arbitrary product**; and
  * `Necessity.n2_sp_eq_twistSeq_frame` — at every ordered frame `U` and every nonpositive
    `r`, `P.sp a b = twistSeq (n2FrameTwist P hS2 U) a b` for `a = Ad_U (diagFamily r)` and
    all effects `b`. Closure: the three core axioms.

  **The lifting step is therefore discharged, and the old entry's account of it was wrong on
  a point of fact.** It said "Lean *assumes* `angle` is linear … so the universal-cover lift
  `ℝ² → SO(2)` ⟹ linear functional is supplied by the paper." But `Necessity.tvalLm` is a
  *constructed* `(n → ℝ) →ₗ[ℝ] ℝ` with **no rank hypothesis** — the linear functional
  `n2_necessity` takes as a parameter was already sitting in the tree, unused at rank two.
  What replaces the article's universal-cover argument here is elementary and exact, with no
  `2π` ambiguity: a linear functional on `ℝ²` vanishing on the diagonal `⟨(1,1)⟩` factors
  through `r ↦ r 0 − r 1`.

  **Why the `rank_ge : 3 ≤ n` worry did not bite.** Only 15 of the 76 `Necessity/` modules
  carry a rank-3 hypothesis, and none of the needed pieces is among them: `Necessity.theta`
  and `thetaPreservesJordan_of_S2` (`prop:theta`) are rank-free — correctly, since unital
  order automorphisms of `H_2(ℂ)` are `O(3)` on the Bloch ball, still exactly
  `{Ad_U} ∪ {Ad_U ∘ ᵗ}`; the dimension-3 requirement in this area belongs to *Uhlhorn's*
  theorem, whose hypothesis is weaker than being an order automorphism. `dChi_kills_corner`,
  `conjProduct`, `sp_eq_twistSeq_transport`, `sp_eq_twistSeq_diagFamily` and `tval_antisymm`
  are rank-free too. What *is* rank-3-gated is `tvalLm_of_coupling`, which uses
  `prop:stabilizers` to pin the rate across index pairs — i.e. precisely the cross-frame
  constancy that is *false* at rank two, which is why the rank-two moduli space is
  `C(ℝP², ℝ)` and not `ℝ`.

  **What is still open, stated exactly.** The frame function exists; nothing yet proves it
  **bounded** (`lem:n2-bounded`), **continuous** (`lem:n2-continuity`), or **invariant under
  reversing the frame** so as to descend to `ℝP²` (`lem:n2-descent`), and so
  `cor:qubit-classification` is not assembled. Those three lemmas are now statements *about
  a function that exists*, which they were not before. `prop:n2-necessity` itself remains
  PARTIAL for a reason that is presentational rather than mathematical: the article states
  its conclusion about `Θ_a|_{W_n}` with frames indexed by `n ∈ S²`, and Lean states the
  equivalent product-level identity with frames indexed by `U ∈ U(2)`.

  What IS machine-checked is the *geometry those lemmas would act on*, for one
  concrete distinguished moduli element rather than for an arbitrary product:
  `RankTwo.orthoFrame` (complementation as an involution on `ℂP¹`, well defined
  because the complement map is *conjugate*-linear), `RankTwo.tauFrame_orthoFrame` and
  `RankTwo.blochFrame_orthoFrame` (both the frame function and the Bloch map are
  complementation invariant), `RankTwo.blochFrame` with
  `blochFrame_continuous`/`blochFrame_surjective`, the moduli element
  `RankTwo.tauModuliRP2 : C(ℝP², ℝ)` with `tauRP2_continuous`, the bridge
  `RankTwo.tauRP2_blochFrame` (the `ℝP²` function pulls back to the frame function),
  `RankTwo.tauModuliRP2_nonconstant`, and the continuity companions
  `tauFrame_continuous`/`tauRP2_continuous`. Files: `RankTwo/Descent.lean`,
  `RankTwo/Bloch.lean`. **Read as coverage of `lem:n2-descent`/`lem:n2-continuity`
  this is a certified concrete example, not the lemma**: it establishes that the
  descent-to-`ℝP²` mechanism is sound and that the moduli space is nontrivial, which
is exactly why building the map was the rank-two work that remained. **SUPERSEDED
  2026-08-08 — see the ★★ correction above: the per-frame extraction from an arbitrary
  rank-two product now exists (`Necessity.n2FrameTwist`, `n2_sp_eq_twistSeq_frame`,
  `n2FrameTwist_reverse`), and the `StabilizerCoupling` `rank_ge : 3 ≤ n` worry did not
  bite because none of the needed machinery was rank-gated.** What remains of this row is
  boundedness and continuity of that function, plus `prop:n2-sufficiency`.
- **`mthm:omnibus`** (the finite-dimensional omnibus classification).
- ~~**`prop:pseudo-transfer`**~~ — **CORRECTED 2026-08-08.** Not "no counterpart":
  `Necessity/PseudoInverse.lean` proves it on the concrete carrier in *normalized* form.
  Lean's `Necessity.pseudoInv b` is the spectral inverse rescaled by
  `pseudoInvCoef b = ∏ eigenvalues > 0` so that it lands in the effects, where the
  article's `a⁻¹` sits in `J⁺` and is reached only through the cone extension. So Lean has
  `sp_pseudoInv_eq_smul_one : P.sp b (pseudoInv b) = pseudoInvCoef b • 1` and
  `sp_pseudoInv_comm`/`sp_pseudoInv_cancel`, together with the order-preservation
  consequences the article draws (`seqLeftMul_reflectsNonneg`, `seqLeftMul_injective`).
  What was missing is exactly the division by that positive scalar, i.e. `lem:cone-ext`.
  ★ **UPDATED 2026-08-08 (ARC-6): both extensions that division needs now exist** — the
  first-argument one abstractly (`SequentialProductOn.spCone`, `lem:cone-ext`, this arc) and
  the second-argument one concretely (`Necessity.seqLeftMul`, `lem:homog`(i), which this file
  had wrongly said was absent). So this row is **assembly-only**: what remains is
  instantiating the abstract cone extension on the concrete carrier and matching Lean's
  `pseudoInvCoef` normalization to the article's `a⁻¹ ∈ J⁺`. Not attempted this arc, and the
  remaining step is bookkeeping about a normalization, not a missing theorem.
  Status: **PARTIAL**, not absent.
- **`prop:singular`** is not invoked by `master_chain` (the abstract skeleton).
  **UPDATED 2026-08-06**: it IS invoked on the concrete carrier, by both finished
  rows — `Necessity.sp_eq_twistSeq_of_effect` (ℂ) via
  `sp_eq_on_effects_of_eq_on_posDef`, and `Necessity.sp_eq_luders_of_effect` (ℝ) via
  `dense_posDef_effectsR` + `MasterTheorem.prop_singular` directly.
- Analytic content generally: norm continuity arguments, spectral theory, and
  the singular-effect extensions live in the paper.

## 3b. The four labels this map used to omit (added 2026-08-08, ARC-5 rung 5.2c)

`STATEMENT-MANIFEST.md` covers all 36 numbered results; this map covered 32. The four that
had no row anywhere, now stated:

| Paper statement | Status | Where it stands |
| --- | --- | --- |
| `lem:homog` — positive linear extension of `L_a` (i), and first-variable homogeneity `(λa)·b = λ(a·b)` (ii) | **PARTIAL** | Clause (ii) is proved, on the concrete carrier only, as `Necessity.sp_smul_left` (`Necessity/FirstArgument.lean`), following vdW Prop. 3.9 with the σ-SEA normality passage replaced by exactly one use of S2. ★ **Clause (i) IS in the tree on the concrete carrier — corrected 2026-08-08 (ARC-6). The previous wording here, "not in the tree in any form", was FALSE.** `Necessity.seqLeftMul` (`Necessity/LeftMultiplication.lean`) *is* the positive linear extension: it is an honest `HermitianMat n 𝕜 →ₗ[ℝ] HermitianMat n 𝕜`, built through `spPos` on the cone and the `x = x⁺ − x⁻` splitting, with `seqLeftMul_apply_effect` (agrees with `P.sp a ·` on effects), `seqLeftMul_nonneg` (positivity), and `seqLeftMul_one`; its own docstring says "paper `lem:homog`(i), matrix-concrete". Uniqueness of the extension is `OrderUnitSpace.linearMap_eq_of_eq_on_effects` (abstract, arc-5). So clause (i) is PARTIAL for the same single reason as clause (ii) — concrete carrier vs the article's EJA generality — and **not** for want of a construction. This was the fifth absence claim in two arcs that was wrong on the page rather than in the tree. See the Archimedean note below for why clause (ii) does not generalize for free. |
| `lem:cone-ext` — extension of the product to positive-cone first arguments | **FORMALIZED 2026-08-08** (ARC-6 rung 6.3) | ★ **Row rewritten; the previous text said PARTIAL and "inherits that row's Archimedean obstruction", which is now discharged.** All three clauses are proved at abstract order-unit-space generality, **about a defined extension** `SequentialProductOn.spCone`: `spCone_eq` (well-defined — agrees with every admissible normalization), `spCone_of_isEffect` (agreement on effects), `spCone_smul` (positive homogeneity). Self-audit note: the first version proved these only at the normalization level (`sp_coneNorm_indep`, `sp_coneNorm_smul`, `sp_coneNorm_eq_of_isEffect`, `exists_isConeNorm` — retained as ingredients), which stated homogeneity about expressions rather than about the extension; `spCone` closes that gap before it could be called an overstatement. It does consume `lem:homog`(ii) — which is why it landed only once that was abstract — and it is **norm-free**, unlike the article, whose `μ ≥ ‖v‖` presupposes the carrier's norm is the order-unit norm. `sp_coneNorm_smul` carries neither `IsArchimedean` nor S2: both were inert there and were removed before landing. |
| `lem:frame-fix` — `Θ_r` fixes the frame and the diagonal, preserves each Peirce block, lies in `Stab(F)°`, hence `L_{a(r)}` is Peirce-block-diagonal | **PARTIAL** | A certificate for the *produced* setup exists inside `MasterTheorem/Master.lean`; the general statement, quantified over frames and over `r`, does not. |
| `prop:bridge` — standard-product compatibility is exactly Jordan operator commutation | **ABSENT, by design** | A cited external result (`Wetering2018three` Props. A.1, A.3). It enters the skeleton as an interface field and the paper does not claim to reprove it. Not a target of any rung. |

★ **The Archimedean note — why the abstract sub-tier of rung 5.1 is not "machinery in hand"
(finding, 2026-08-08).** `lem:homog`(ii) and `lem:cone-ext` are stated by the article at EJA
generality, so a concrete-carrier proof cannot close them; they need the abstract layer. But
the concrete proof of `lem:homog`(ii) runs through
`Necessity.sp_smul_of_mem_unitInterval` (`Necessity/LeftMultiplication.lean`), whose final
step is an ε-squeeze — `∀ ε > 0, z − t•y ≤ ε•𝟙` therefore `z ≤ t•y` — and **that step is
exactly the Archimedean property**, which this tree's `OrderUnitSpace` class does not carry:
its `archimedean` field is order-unit *boundedness* only (the long-standing caveat 1). So
generalizing the ladder is not a change of variable block; it requires the Archimedean
property to be supplied, and the interface cannot be extended to carry it without breaking
`AxiomAudit.lean` Layer 5, which freezes the printed constructor type of
`SequentialProductCore.mk`. The clean route, when this is taken up: introduce Archimedean as
an explicit `Prop` hypothesis (it is part of the *definition* of the article's "order unit
space", not a located stand-in for a cited result, so a row proved under it still counts as
formalized at the article's generality) and thread it through the six-step ladder. Then
`lem:homog`(i) needs only that same generalization — **not** a positive-linear-extension construction, which
**does** exist on the concrete carrier (`Necessity.seqLeftMul`; the claim that it does not was retracted 2026-08-08, see the
`lem:homog` row above). What the abstract version needs is `spPos`/`seqLeftMul` rebuilt over an order unit space with
Archimedean supplied, which is the same thread, not a second one.
Contrast `lem:span`, whose two load-bearing clauses were proved at abstract generality
*without* Archimedean — see §1 — because the article's norm route is avoidable there and
here it is not.

## 3c. `lem:homomorphism` — repriced from ABSENT, and the missing clause proved (2026-08-08, ARC-6 rungs 6.0/6.2)

**The audit verdict first, because it is the more important half.** This row was carried as
**ABSENT** on the strength of one sentence in §2 of this file: "Lean neither differentiates
`Θ` nor proves `dχAdd` is its derivative." That sentence was **false**, and it is now
rewritten at its own row. It described the *abstract skeleton*, where `dχAdd` is indeed a
hypothesis field — and then generalized to the whole tree, which had already built the
concrete analysis. This is the third instance in two arcs of an absence claim losing its
scope; the rule stands: **an absence claim's scope travels with it, permanently.**

What the tree already had, unread:

| Article clause | Lean | Note |
| --- | --- | --- |
| `Θ` a continuous homomorphism on the negative orthant | `Necessity.thetaUnit_mul`, `thetaUnit_zero`, `continuous_thetaUnit_val` | |
| extends to `χ : (ℝⁿ,+) → Stab(F)°` | `Necessity.chiTilde` (**constructed**), `chiTilde_add`, `chiTilde_of_nonpos` | Built by the article's *own* canonical decomposition `sᵢ(x) = min(xᵢ,0)` — literally `r ⊓ 0` |
| real-linear differential `dχ` | `Necessity.chiTilde_eq_exp` (`∃!` linear `D` with `χ̃ = exp ∘ D`), `dChi`, `chiTilde_eq_exp_dChi` | **Proved, not imported.** The article argues "a continuous homomorphism of f.d. Lie groups is smooth"; Lean routes through `multiParameter_eq_exp` instead, so no Lie theory enters, and it needs only *line* continuity where the article assumes joint |
| `dχ` lands in `𝔰𝔱𝔞𝔟(F)`, acting skewly on each block | `Necessity.dChi_mem_blockSkew` into `blockSkewSubmodule` (whose membership *is* block-skewness), `dChi_block_skew`, `dChiStab` | This is what makes `T_ij ∈ 𝔰𝔬(V_ij)` automatic rather than a further obligation |
| `ρ_ij(dχ(r)) = (rᵢ − rⱼ) T_ij`, single `T_ij` | **the one genuinely missing clause** | Now proved, below |

**Proved this arc (`Necessity/PhaseAnchor.lean`, all rank-free):**
`blockHerm_cornerJ2` (a block element sits in the Peirce 2-space of `q = pᵢ + pⱼ`);
`tvalLm_of_diag_eq` (the phase rate kills the coalesced diagonal, from
`dChi_kills_corner`); `tvalCoef` and `tvalLm_eq_coef_mul` (the coordinate factorization
`tvalLm(r) = (rᵢ − rⱼ)·c_ij`); `dChiEntry_eq_mul_generator`; and — matching the article's own
phrasing — `rhoChi` with **`rhoChi_eq_smul_generator` : `ρ_ij(dχ(r)) = (rᵢ − rⱼ) • ρ_ij(dχ(eᵢ))`**.
Closure `[propext, Classical.choice, Quot.sound]` on each.

Where the article spans the hyperplane `{rᵢ = rⱼ}` by differences of coalesced orthant
vectors, Lean takes the vanishing directly from the differentiated coalescence
(`dChi_kills_corner` / `rhoField_dChi_coalesced`) and then factors a linear functional that
kills a hyperplane — exact, and with no `2π` bookkeeping, the same simplification that
replaced the universal-cover lift in the rank-two lane.

**Honest status: PARTIAL, not FORMALIZED**, for one reason only — `lem:homomorphism` sits in
the article's *general machinery* section (before the type-by-type branches) and is stated
for a simple EJA with a Jordan frame, whereas all of the above lives on the concrete `H_n(ℂ)`
carrier (with the `Gen` variants covering `RCLike 𝕜`). Same generality gap as `prop:theta`
and `prop:pseudo-transfer`, and it is the *only* thing between this row and FORMALIZED. The
secondary gap is packaging, not content: the tree never names `Stab(F)°` as a Lie group with
an identity component, working instead with `blockSkewSubmodule` and `dChiStab`.

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
