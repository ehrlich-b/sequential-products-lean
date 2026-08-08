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
| real Kadison rigidity: a unital order-automorphism of `H_N(ℝ)` is orthogonal conjugation | `Necessity.orderAutoR_preservesJordan` | `Necessity/RealKadison.lean` |
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
Wigner rigidity, and `H₃(𝕆)` is blocked on octonions, which exist in no prover.

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
| `DiagonalHomSetup.dχAdd`, `dχAdd_cont`, differentiated coalescence | **not a rendering of one cited theorem**: these begin *after* the paper's comparison-to-differential analysis. Lean neither differentiates `Θ` nor proves `dχAdd` is its derivative | `lem:homomorphism` |
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
construction of the comparison character and its differential from `Θ_a`; the
operator-to-character translation on the cross-coherence space; the geometric
two-plane frame-connectivity move; the concrete `(S2)` and invertible-density
inputs; the remaining rank-two cocycle and compatibility cases; and the contents
of the cited van de Wetering propositions themselves.  (The complete seven-axiom
verification of the twist products — formerly on this list — is now
machine-checked on the concrete carrier: `lem:twist-sufficiency` in §1.)

**Statements with no Lean counterpart:**

- **`mthm:master` itself.** `master_chain` audits the *composition* of the case
  split over one abstract algebra; it constructs no concrete simple EJA, and does
  not prove that a given algebra is of a particular coordinate type, that an
  operation satisfies S1–S7, that `L_a = Q_{√a}Θ_a`, that `Θ_a = id`, or any
  product equality. Its own docstring says so.
- **Rank two, all of it: `lem:n2-bounded`, `lem:n2-descent`, `lem:n2-continuity`,
  the lifting step of `prop:n2-necessity`, and the assembled bijection
  `cor:qubit-classification`.**

  ★ **The governing statement (2026-08-08, correcting the 2026-08-06 entry that
  removed `lem:n2-descent` from this section — that entry contradicted its own
  footnote and the footnote was right).** NO declaration in `RankTwo/` takes a
  `SequentialProductOn` (verify: `grep -c SequentialProductOn
  RadicalRelativity/RankTwo/*.lean` → 0 in all seven files), and `n2_necessity` takes
  a linear `angle` rather than a product. So the **classification map
  `product ↦ moduli` does not exist in Lean at all.** Each rank-two lemma above is a
  statement about that map, or about the moduli function of an *arbitrary* rank-two
  product; at that generality none of them is machine-checked. The lifting step is
  separately unchecked even at generator level: Lean *assumes* `angle` is linear and
  proves only the factorization, so the universal-cover lift `ℝ² → SO(2)` ⟹ linear
  functional is supplied by the paper.

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
  is exactly why building the map is the rank-two work that remains. Building it
  needs per-frame parameter extraction from an arbitrary rank-two product, and the
  `N ≥ 3` machinery cannot be reused (`StabilizerCoupling` carries `rank_ge : 3 ≤ n`).
- **`mthm:omnibus`** (the finite-dimensional omnibus classification) and
  **`prop:pseudo-transfer`**.
- **`prop:singular`** is not invoked by `master_chain` (the abstract skeleton).
  **UPDATED 2026-08-06**: it IS invoked on the concrete carrier, by both finished
  rows — `Necessity.sp_eq_twistSeq_of_effect` (ℂ) via
  `sp_eq_on_effects_of_eq_on_posDef`, and `Necessity.sp_eq_luders_of_effect` (ℝ) via
  `dense_posDef_effectsR` + `MasterTheorem.prop_singular` directly.
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
