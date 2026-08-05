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

**M0 status (day 1, complete by evening):** witnesses for all five interface
structures constructed (`MasterTheorem/Witnesses.lean`) and audit Layer 6
(interface constructor freezes) added — six-layer audit green at 27 modules.
Albert import expected to DISCHARGE via the unit-slot argument
(`ALBERT-KERNEL-MEMO.md`), demoting the route file's "6–12 months with Albert"
to the 3–5 month track. Mathlib inventory COMPLETE (all areas, v4.28.0-era
checkout) — [INV✓] markers below are settled; see H5 for the scoping gotcha
that cost the most to discover. Landscape check COMPLETE: Nuccio lead DEAD
(his "octonions" repo is a mathlib mirror by that name); live octonions effort
= mathlib4 PR #41919 (Cayley-Dickson, defers alternativity, no Albert — do not
wait for it); EJA/Peirce/Kadison/FTPG/effect-algebras are greenfield in EVERY
prover. WILDCARD: `zblore/csd-lean4` (Apache-2.0, solo, CI green) claims a
sorry-free Wigner rigidity — see 3.0.

---

## M1 — Complex sufficiency (twists satisfy S1–S7 on H_n(ℂ))

- **1.1 Carrier + instances — DECIDED 2026-08-04: VENDOR physlib's HermitianMat
  island** (evaluation report banked; not `lake require` — physlib pins mathlib
  v4.32 and is fast-moving, which would chain our zero-sorry claim to a live
  upstream; not reimplement — their design is the one we'd pick and the CFC
  plumbing is ~2kL already done). Vendored 2026-08-04: 17 files ≈ 7kL from
  physlib @ `ad1d812` (Apache-2.0, headers retained) into
  `RadicalRelativity/Vendor/` — carrier `HermitianMat n α :=
  selfAdjoint (Matrix n n α)` (opaque def synonym), Loewner `PartialOrder` via
  scoped MatrixOrder, trace inner product + Frobenius `NormedSpace ℝ` +
  `CompleteSpace`, `HermitianMat.cfc` (ℝ→ℝ) with continuity block,
  `symmMul` Jordan product + scoped `HermMul` `IsCommJordan` instance,
  `Proj.lean` (projectors, posPart/negPart, `{A ≤ₚ B}`). Provenance + edit log:
  `RadicalRelativity/Vendor/VENDOR.md`. **Backport v4.32→v4.28 DONE 2026-08-04**
  (drift log in VENDOR.md; zero statement changes; gates verified first-hand:
  build green, census 44 modules / one axiom). **What the vendor does NOT give (= 1.1's
  remaining work):** order-unit norm (the `Norm` slot is occupied by Frobenius
  — the OU norm must be an unbundled def or type synonym, NEVER a competing
  instance), order unit + Archimedean statements (`le_trace_smul_one`,
  `lt_smul_of_norm_lt` are the starting bounds), an effect-interval object
  (only `unitInterval_IsCompact` exists), extreme-points-are-projections
  (feeds M3 bridge 1), and everything Jordan-structural past the `IsCommJordan`
  mixin. Risk LOW-MED (backport residue).
  **Order-unit layer DONE 2026-08-04** (`Hermitian/OrderUnit.lean` +
  `Hermitian/ExtremeEffects.lean`; census green at 46 modules, one axiom): the
  OU norm as an unbundled def with the defining infimum ATTAINED via the closed
  PSD cone (`isClosed_nonneg` + `IsClosed.csInf_mem` — no eigenvalue
  bookkeeping, `RCLike`-uniform) plus minimality / `ouNorm ≤ Frobenius` / neg /
  triangle / definiteness; order-unit boundedness with witness `r = ‖a‖`
  (`lt_smul_of_norm_lt`); the FULL Archimedean property over ℂ (eigenvalue
  route); `instance OrderUnitSpace (HermitianMat n 𝕜)` whose parents are the
  existing vendored instances (no second normed/order structure) and under
  which `OrderUnitSpace.IsEffect` is DEFINITIONALLY the Loewner `[0,1]`
  (`isEffect_iff := Iff.rfl`; `unitInterval_IsCompact` restates verbatim; the
  abstract `Effect V` subtype now instantiates on the carrier); and
  extreme-points-of-`[0,1]` = projections (`p^2 = p`): forward direction
  𝕜-uniform (quadratic-form kernel pinch, `dotProduct_mulVec_zero_iff`),
  converse over ℂ fully CFC-native (perturb by `± min(x, 1-x)` through
  `HermitianMat.cfc`; extremeness kills the perturbation; spectrum lands in
  `{0,1}` — zero eigenvector-basis bookkeeping). Feeds M3 bridge 1.
  **1.1 is CLOSED**; the only norm item left anywhere is the 1.4 equivalence.
- **1.2 Twist definition.** `a^{1/2+it} b a^{1/2-it}` via CFC. [INV✓]: matrix
  CFC instance is `Matrix.IsHermitian.instContinuousFunctionalCalculus` (over ℝ,
  predicate `IsSelfAdjoint`, real file `Analysis/Matrix/
  HermitianFunctionalCalculus.lean` — the LinearAlgebra path is a deprecated
  stub); **NO cpow for positive elements exists** (only `CFC.rpow`/`nnrpow`/
  `sqrt`). Two routes for the complex power: (a) pair-of-real-cfc,
  `a^{1/2+it} := hA.cfc (x^{1/2}cos(t log x)) + i·hA.cfc (x^{1/2}sin(t log x))`
  — identities become manual but bonus applies: `hA.cfc_eq` carries NO
  continuity hypothesis (finite spectrum), so 0-eigenvalue conventions are
  free; (b) `CStarMatrix` type copy + the ℂ-CFC over `IsStarNormal`. Pick at M1
  start. Risk MED (was LOW-MED; the gap is confirmed, the routes are clear).
  **DECIDED 2026-08-04: route (a), pair-of-real-cfc** — the S1–S7 statements
  live on `HermitianMat` (the 1.1 `OrderUnitSpace` instance), so route (b)
  would add a parallel carrier plus an order/positivity transfer layer while
  offering no cpow API to harvest (inventory-confirmed absent); and the
  vendored `HermitianMat.conj` AddMonoidHom makes the twist product
  `b.conj (twistFactor a t)` with S1-additivity, monotonicity, positivity, and
  effect closure riding `map_add`/`conj_mono`/`conj_nonneg` directly. The
  paper's `0^{1/2±it} = 0` convention is DEFINITIONAL on this route: every
  component is `√x·(…)`, which vanishes at `x = 0` regardless of the
  `Real.log 0 = 0` junk value. Implemented in `Hermitian/Twist.lean`:
  `twistRe`/`twistIm`/`twistFactor` (= `a^{1/2+it}` as a plain matrix),
  `twistSeq t a b := b.conj (twistFactor a t)`, with `Xᴴ = twistFactor a (-t)`,
  `X·Xᴴ = Xᴴ·X = a.mat` (on `0 ≤ a`; Pythagorean cancellation through
  `cfc_self_commute` + `cfc_congr_of_nonneg`), `twistFactor 1 t = 1`,
  unit laws `a &ₜ 1 = a` / `1 &ₜ b = b`, positivity, right-additivity,
  right-monotonicity, effect closure, and `twistSeq 0 a b = √a·b·√a` (Lüders).
  **1.2 definitional layer DONE 2026-08-04** (census 47, gates green). What
  moves to 1.3: S4 zero-symmetry, S5 compatible associativity, S6a/S6b, S7,
  and packaging as a `SequentialProductCore (HermitianMat n ℂ)` instance
  (plus S2 continuity from `conj` continuity in the carried norm).
- **1.3 S1–S7 verification.** [INV✓]: cfc identity suite is rich (`cfc_mul`,
  `cfc_comp'`, `cfc_pow`, order lemmas `cfc_mono`/`cfc_le_iff`, commutation
  `Commute.cfc`, norms `norm_cfc`). The SymPy V1–V10 checks are the
  computational shadow; each becomes a lemma. Risk LOW, volume moderate.
  **DONE 2026-08-05** (`Hermitian/Resolution.lean` + `Hermitian/Sequential.lean`;
  census green at 49 modules, one axiom; paper row `lem:twist-sufficiency` now in
  THEOREM-MAP §1, unconditional — no §2 interface structures in its closure).
  Proof architecture, chosen to avoid ALL simultaneous-diagonalization machinery
  (none exists in Mathlib for matrices):
  (i) *Resolution layer*: `specProj a μ := a.cfc 1_{x=μ}` (matrix cfc needs no
  continuity, so indicators are legal), `mat_cfc_eq_sum_specProj` (every cfc
  expands over the value-indexed family, by cfc-congruence on the spectrum plus
  linearity), and `mat_cfc_of_resolution` — cfc respects ANY pairwise-orthogonal
  idempotent presentation `M = Σ cᵢ•Rᵢ`, by Lagrange interpolation at the nodes
  `{cᵢ} ∪ σ(M)` (`Mathlib.LinearAlgebra.Lagrange`) reducing to the polynomial
  case, which is ring algebra.
  (ii) *Compat ⟹ commute* (the Gudder–Nagy trick at general twist): from
  `a &ₜ b = b &ₜ a`, the Frobenius certificate `C := b^{1/2+it}·a − a·b^{1/2+it}`
  has `tr(C·Cᴴ) = 2tr(ba²) − τ − τ̄ = 0` (where `τ = tr((b &ₜ a)·a)` equals
  `tr(ba²)` by the hypothesis plus the one-variable identity
  `tr((a &ₜ b)·a) = tr(ba²)`), so `C = 0` via
  `Matrix.trace_mul_conjTranspose_self_eq_zero_iff`; conjugate-transposing gives
  commutation with `b^{1/2-it}` too, and their product is `b`. No Fuglede, no
  spectral theory.
  (iii) *Commute ⟹ compat + value*: `a &ₜ b = a·b` for commuting pairs rides the
  vendored `Commute.cfc_right` — free.
  (iv) *S5*: reduces to `(ab)^{1/2+it} = a^{1/2+it}·b^{1/2+it}` on commuting
  positives (`twistFactor_mul_of_commute`): present `ab` by the JOINT family
  `P_μ·Q_ν` (products of the two spectral-projection families — commuting
  orthogonal idempotents summing to 1), apply the resolution lemma, and finish
  with the scalar character law `g(μν) = g(μ)g(ν)` on `[0,∞)` — the paper's
  `g(0) = 0` convention makes the zero-eigenvalue cases definitional.
  (v) *S4*: trace route — `tr(a &ₜ b) = tr(b·a)`, trace symmetry, PSD +
  trace-zero ⟹ zero (eigenvalue sum). (vi) *S6a/S6b/S7*: one-line consequences
  of (ii)+(iii) and `Commute` algebra. (vii) *S2*: GLOBAL norm continuity of
  `a ↦ a &ₜ b` — the component functions `√x·cos/sin(t·log x)` are continuous on
  all of ℝ (squeeze `|√x·c| ≤ √x` at the spectral origin; the junk values for
  `x < 0` vanish identically), then the vendored `HermitianMat.cfc_continuous` +
  `Continuous.matrix_mul`. Packaged as `twistSequentialProductCore t` /
  `twistSequentialProduct t` (defs per twist parameter, parents = the 1.1
  instance; `IsEffect`/`ousUnit` discharge definitionally). The V1–V10 shadow is
  superseded pointwise by these lemmas on the n≥3 side; V9/V10's rank-two content
  was already in `MasterTheorem/RankTwo.lean`.
- **1.4 (S2) norm caveat discharge.** Prove order-unit norm ≡ carried norm on
  the finite-dim instance (all norms equivalent, Mathlib has finite-dim
  equivalence) — closes THEOREM-MAP's S2 literal-fidelity caveat. Risk LOW.
  Half done 2026-08-04: `ouNorm_le_norm` (OU ≤ Frobenius) is proved.
  **DONE 2026-08-05** (same-day as 1.3; census unchanged at 49): the reverse
  comparison `norm_le_sqrt_card_mul_ouNorm : ‖a‖ ≤ √(card n) · ouNorm a` via
  `abs_eigenvalues_le_ouNorm` (upper bound from the attained `le_ouNorm_smul_one`
  + vendored `le_smul_one_imp_eigenvalues_le`; lower bound through `-a` and the
  `cfc_eigenvalues` permutation — no new spectral machinery) and
  `norm_eq_sum_eigenvalues_sq`; plus the paper-facing transfer
  `twistSeq_continuousAt_ouNorm` (ε–δ first-argument continuity of the twist
  product IN THE ORDER-UNIT NORM, `Hermitian/Sequential.lean`), which is the
  literal (S2) reading on the concrete carrier. smul homogeneity of `ouNorm`
  was NOT needed (the ε–δ route uses only the two inequalities) — not proved,
  by design. **M1 IS COMPLETE.**

## M2 — Complex necessity core

- **2.1 Θ construction (vdW Prop 5.2/5.3) — CLOSED 2026-08-05 (all six units
  2.1a–2.1f below).** Define `Θ_a := Q_{√a}⁻¹ ∘ L_a` on
  invertible effects; prove unital linear order-iso. Matrix-concrete. Risk MED.
  **First unit DONE 2026-08-05 — `lem:homog`(i)** (`Necessity/LeftMultiplication.lean`,
  census 50, gates green): for an ARBITRARY product on the carrier, `seqLeftMul P a`
  is the positive linear extension of `b ↦ P.sp a b` to all of `H_n(ℂ)`, with
  effect-agreement, positivity, monotonicity, and the unit law
  `seqLeftMul P a 1 = a`. Ladder: ℕ→ℚ homogeneity by finite additivity (S1 only),
  ℝ-homogeneity by the rational order squeeze closed with
  `le_zero_of_forall_le_smul_one` (this is where the full Archimedean property
  earns its keep), cone extension normalized by `‖x‖+1` with normalization
  independence, and the `posPart/negPart` difference construction with a
  representation-independence lemma (`spPos_sub_congr`). NO S2 used — matches the
  paper's hypothesis accounting for lem:homog(i).
  **DESIGN DECISION (binding for all of M2–M5): the unknown product is
  `SequentialProductOn V` — the S1/S3–S7 fields over the AMBIENT `[OrderUnitSpace V]`
  (added to `SequentialProduct.lean`, with `toCore` bridging to the derived-lemma
  layer; parent definitionally the ambient instance).** An instance-quantified
  `[SequentialProductCore (HermitianMat n ℂ)]` is WRONG for necessity statements:
  it bundles its own `toOrderUnitSpace`, which the elaborator treats as unrelated
  to the carrier's canonical instance, so no carrier order/norm/spectral lemma
  applies (discovered as an instance-mismatch wall at the first 2.1 build). The
  final per-type `mthm:master` statements must quantify over
  `SequentialProductOn (HermitianMat n ℂ)` + unbundled S2 for the same reason.
  **(2.1b) DONE 2026-08-05** (`Necessity/FirstArgument.lean`, census 51, gates
  green): `sp_smul_left` = lem:homog(ii), first-argument homogeneity for
  `t ∈ [0,1]`, with the compat ladder `sp_comm_nat_smul` (iterated S6b),
  `sp_comm_rat_smul_self` (1/k-piece ladder both directions),
  `sp_comm_rat_one_smul` (orthocomplement + S6a flip + S6b assembly),
  `sp_rat_one_smul_left` (rational value law), and `sp_smul_one_left` = the
  SINGLE S2 use (rational sequence in the first argument, ContinuousWithinAt
  composed with `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`,
  `tendsto_nhds_unique` closes). Traps: interface fields produce `ousUnit`
  forms — rewrite `HermitianMat.ousUnit_eq_one` before matching, and phrase
  effect-of-1 / unit-law facts as `have h : … (1 : HermitianMat n ℂ) … := ⟨abstract⟩`
  so unification binds `1` not `ousUnit`; pin
  `tendsto_one_div_add_atTop_nhds_zero_nat`'s carrier by ascription before use.
  Remaining in 2.1 — **PROOF PLAN DECODED AT SOURCE 2026-08-05**
  (arXiv:1803.08453 = Wetering2018three, fetched via curl+pdftotext; §3.9, §4.17–4.22,
  §5.2–5.7 read in full). Unit ladder, in dependency order:
  (2.1b) **lem:homog(ii) = first-argument homogeneity** `(λa)◦'b = λ(a◦'b)`,
  λ ∈ [0,1] — vdW 3.9 adapted: (i) rational-multiples self-compat ladder
  `qa |' a` by iterated S6b from `(1/n)a |' (1/n)a`; (ii) `qa⊥ |' a⊥` same, then
  S6a gives `qa⊥ |' a`; (iii) S6b: `a |' (qa + qa⊥) = q·1`, and
  `(q1)◦'a = a◦'(q1) = qa` by second-arg homogeneity (HAVE) + unit law;
  (iv) the ONLY S2 use: `(λ1)◦'b = λb` by rational approximation in the first
  argument (qᵢ1 → λ1 in norm, S2 passes the limit); `a |' λ1` then holds since
  both sides equal λa by (iii)-style computation, NO normality needed;
  (v) S5 with `a |' λ1`: `(λa)◦'b = (a◦'(λ1))◦'b = a◦'((λ1)◦'b) = a◦'(λb) = λ(a◦'b)`.
  (2.1c) **Sharp-effect base layer — DONE 2026-08-05**
  (`Necessity/SharpEffects.lean`, census 52, gates green): `proj_pinch`
  (product-independent sharpness of projections by two conjugation pinches +
  the √e Frobenius kill), `sp_proj_compl`/`sp_proj_self` (p◦'(1−p) = 0 and
  p◦'p = p — S6a applied to the TRIVIAL self-compat `p |' p` makes the two S1
  splittings pinch it; this is the whole Gudder–Greechie sharpness theorem in
  ~20 lines on the carrier), `orth_compl_isProjection`/`proj_orth_le_one_sub`
  (1−p−q is a projection when pq = 0), `sp_proj_orth`/`sp_proj_orth'` (S4 for
  the flip), `sp_comm_proj_orth`. No S2 anywhere in this unit.
  (2.1d) **vdW 5.2 transfer on matrices — DONE 2026-08-05** (appended to
  `Necessity/SharpEffects.lean`, census unchanged 52, gates green):
  `sp_orthFamily_value` — over any pairwise-orthogonal projection family,
  `(∑λᵢ•pᵢ) ◦' (∑μᵢ•pᵢ) = ∑(λᵢμᵢ)•pᵢ` (the STANDARD value) for any S1–S7+S2
  product — and `sp_orthFamily_comm` (compatibility transfer). Supporting:
  `sum_proj_isProjection` (rides Resolution's `resolution_mul` with x=y=1),
  `sum_smul_proj_isEffect`, `sp_sum_right` (S1 over families, dominated-sum
  side conditions via `Finset.sum_le_sum_of_subset_of_nonneg`),
  `sp_add_left_of_comm` + `sp_comm_sum` + `sp_sum_left_of_comm` (first-argument
  additivity over compatible summands: S6b-fold then S1-flip — NOT an axiom).
  S2 enters only through `sp_smul_left`. The pseudo-inverse compatibility
  `b |' ν` is now an instantiation: both are diagonal in b's `specProj` family
  (2.1e wires it).
  (2.1e) **Pseudo-inverse + order reflection — DONE 2026-08-05**
  (`Necessity/PseudoInverse.lean`, census 53, gates green): `pseudoInv b :=
  ∑(c/μ)•specProj b μ` with the normalization `c := ∏ μ` (0 < c ≤ μ with NO
  nonemptiness split — the erase-product trick); `sp_pseudoInv_eq_smul_one`
  (`ν◦'b = c•1` via the 2.1d value law after `rw [sum_smul_specProj] at hval`
  — conv-rewriting b would loop the pattern into pseudoInv's own b);
  `sp_pseudoInv_cancel` (S5 + first-arg homog + S3); `span_isEffect_eq_top`;
  `seqLeftMul_pseudoInv_comp` (`L'_ν ∘ L'_b = c·id` via `LinearMap.ext_on`,
  which at this pin takes `span = ⊤` directly); `seqLeftMul_reflectsNonneg` +
  `seqLeftMul_injective`. Surjectivity deferred to 2.1f (finite-dim
  injective ⟹ bijective at the LinearEquiv packaging).
  (2.1f) **Θ assembly — DONE 2026-08-05, and with it 2.1 IS CLOSED**
  (`Necessity/Theta.lean`, census 54, gates green; compiled clean on the first
  pass): `quadRepEquiv` (`Q_{√a}` as a `LinearEquiv` via vendored `conjLinear`;
  inverse = conj at `(√·)⁻¹` through `cfc_congr_of_posDef`, no `NonSingular`
  machinery needed — `conj_conj_mat` composes conjugations); `theta P ha hbd :=
  Q⁻¹ ∘ₗ seqLeftMul`, `quadRep_theta` (the paper's defining equation
  `L'_a = Q_{√a} Θ_a`), `thetaEquiv` (injective from 2.1e cancellation,
  surjective by `LinearMap.injective_iff_surjective` + the vendored
  `FiniteDimensional` instance), `theta_one` (UNITAL, vdW 5.3), and
  `theta_nonneg_iff`/`theta_le_iff` (ORDER ISO both directions: forward =
  2.1e reflection, backward = conj positivity). `Θ_fix` (vdW 5.5) = 2.2 next
  (via the JOINT specProj family of two commuting effects, both diagonal in it —
  same construction as M1's `twistFactor_mul_of_commute` family);
  `Θ_cocycle` = 2.4 (needs only Lüders invariance, no Kadison). `Θ_jordan`
  stays M3. vdW 5.3's quotient universal property was never needed; 5.4
  (`Θ_{λq} = Θ_q`) is 2.3 and falls out of (2.1b).
- **2.2 Θ_fix (vdW 5.5) + span extension.** Effect-level fixing + extension to
  J by linearity (the span argument the paper supplies). Risk MED.
  **Effect-level fixing DONE 2026-08-05** (`Necessity/ThetaFix.lean`, census 55,
  gates green): `jointProj` (the joint spectral family `P_μ·Q_ν` of a commuting
  pair — Hermitian by commutation, projections, pairwise orthogonal), the padding
  lemmas (`sum_smul_specProj_pad`/`_pad_left`: any `cfc` of one factor is
  diagonal in the joint family), `a_eq_sum_jointProj`/`b_eq_sum_jointProj`,
  `sp_eq_quadRep_of_commute` (**the unknown product takes the standard Lüders
  value on commuting pairs**: unknown side = 2.1d value law over the joint
  family; standard side = two `resolution_mul` passes + `√μ·ν·√μ = μν`), and
  `theta_fix : Θ_a b = b` by cancelling `Q_{√a}` through `quadRep_theta`.
  The span extension to all of J is definitionally free here (Θ is already a
  total linear map — vdW needed the span argument only because his Θ lived on
  an order ideal). Traps: no `Finset.sum_product_comm` at this pin (use
  `Finset.sum_product` + `Finset.sum_comm`); inside a `set s := …` scope, state
  `show`-terms over `s` so `rw` matches syntactically (ascription checks by
  defeq, rewriting does not).
- **2.3 cone-ext (Θ_{λq} = Θ_q normalization).** Cheap once 2.1 lands. LOW.
  **DONE 2026-08-05** (appended to `Necessity/Theta.lean` + `Hermitian/Resolution.lean`,
  census unchanged 55, gates green): `theta_smul : Θ_{t•a} = Θ_a` for `t ∈ (0,1]`
  (vdW 5.4), by cancelling through `quadRepEquiv_smul` (`Q_{√(t•a)} = t•Q_{√a}`,
  via the NEW general `HermitianMat.cfc_smul_arg : (r•a).cfc f = a.cfc (f (r·))`
  — another resolution-lemma payoff, no sign hypothesis) and `seqLeftMul_smul`
  (first-argument homogeneity at the linear-map level, ext_on the effect span).
  So Θ extends scale-invariantly to the whole positive-definite cone.
- **2.4 Θ_cocycle (vdW 5.7, commuting diagonal family).** Matrix-concrete
  computation in the joint eigenbasis. Risk MED.
- **2.5 frame_opCommute + simDiag_opCommute (FK facts).** Direct block-form
  computations on matrices. LOW.
- **2.6 THE ANALYTIC CORE: dχAdd + continuity + coalescence_diff.** Construct
  the character χ̃ from Θ on the orthant (group-level pieces `chi_hom`,
  `chi_comm`, `chi_extend_wellDefined` already proved), extend to ℝⁿ,
  differentiate. Continuous-additive⟹linear is PRESENT
  (`AddMonoidHom.toRealLinearMap` [INV✓]); the differentiation/smoothing of χ̃
  itself is bespoke analysis — the single largest M2 line-count risk. Risk
  HIGH (budget, not feasibility).
- **2.7 Aczél axiom DISCHARGE (`Selection.aczel_continuous_multiplicative`).**
  Scalar Cauchy machinery present [INV✓ area 7a]; multiplicative classification
  absent [INV✓ 7d — build it]: continuous hom (0,∞)→ℂ* via log/exp covering
  (Complex.isCoveringMap_exp [INV✓]) reduction to additive case. Operator-valued
  form [INV✓ area 6]: NO one-parameter-group theory exists anywhere in Mathlib
  (no Stone, no "continuous hom ℝ → GL is exp(tA)", zero generator-extraction);
  raw material = `hasDerivAt_exp_smul_const` + the local unitary log
  `Unitary.argSelfAdjoint` (`Analysis/CStarAlgebra/Unitary/Connected.lean`).
  Precedent: PR #33813 (Cauchy-log characterization) was closed unmerged
  2026-01 — build in-repo, harvest to Mathlib later (T4). ~200–350 lines
  estimate stands, lean high. Risk MED.
- **2.8 `bgw_canonical_composite` ELIMINATION — DONE 2026-08-04.** Replaced the
  axiom (a constructible existence claim, hence not falsifiable) with the
  pattern-match definition `bgwComposite` + `rfl`-proved `bgwComposite_table`;
  non-matrix rows = documented junk-total `.real 0`, consumed nowhere. Audit
  updated (allowlist + citedAxioms to one, Layer-4 bgw pin removed, docstrings);
  README / THEOREM-MAP §2 / NormalFormExistence / Interface docstrings updated.
  **Custom-axiom count: 2 → 1** (Aczél alone); → 0 after 2.7.
- **2.9 prop:singular (singular-effect extension).** Boundary continuity
  argument; standalone lemma exists but is unwired. Risk MED, tail item.

## M3 — THE BOULDER: Θ_jordan (Kadison/vIR rigidity)

- **3.0 DUE DILIGENCE: DONE 2026-08-04 — VERDICT CLEAN.** Built
  `zblore/csd-lean4`'s `WignerRigidity` module from source (2588 jobs, green);
  `#print axioms Projectivization.wigner_rigidity` (and
  `wigner_rigidity_unitaryGroup`) = **[propext, Classical.choice, Quot.sound]
  exactly** — the transitive proof tree contains no custom axiom, no sorry, no
  native_decide, which clears every claim-shaped-placeholder concern for THIS
  theorem regardless of the repo's other layers. Statement fidelity verified
  at the definition level: `TransProbPreserving f = ∀ p q, transProb (f p)
  (f q) = transProb p q` with `transProbVec ψ φ = ‖⟪ψ,φ⟫_ℂ‖²/(‖ψ‖²·‖φ‖²)`
  (genuine Fubini–Study), conclusion the honest unitary/antiunitary dichotomy
  (`e : ≃ₗᵢ[ℂ]`, `conjProj` = standard-basis conjugation), NO surjectivity
  hypothesis needed. **Vendor surface** (Apache-2.0, files self-labeled
  "1-Mathlib, CSD-free upstream candidates" under `namespace Projectivization`):
  8 files ≈ 4.8kL — WignerRigidity ← TransitionProbability ← FubiniStudy ←
  {Unitary, MeasureSpace, Matrix/UnitaryHaar} ← {Topology, Matrix/
  UnitaryCompact}. Caveat: written in the NEW module system (`module` +
  `public import` + `@[expose] public section`, toolchain v4.33.0-rc1) — our
  tree is v4.28.0, so either (i) bump our toolchain+mathlib (whole-tree
  re-elaboration risk) or (ii) mechanical backport (strip module keywords,
  absorb Mathlib API drift). Decide at M3 start. Their `EffectGleason.lean`
  (Busch, de-axiomatized per their AXIOMS.md) remains UNAUDITED — same audit
  procedure before ever citing it.
- **3.1** Unital order-autos of H_n(ℂ)sa are Jordan autos, matrix-concrete,
  n ≥ 3. No prover has Kadison/Uhlhorn/FTPG (landscape-confirmed 08-04:
  Magaud/Narboux Coq and AFP Projective_Geometry are incidence-axiomatic only,
  no coordinatization). **Route A (if 3.0 audits clean):** (i) bridge 1 —
  order-auto Φ preserves extreme effects ⟹ maps rank-1 projections to rank-1
  projections; NOTE [INV✓ area 5]: "extreme points of [0,I] = projections" is
  FROM SCRATCH (Mathlib has `IsStarProjection`, generic `extremePoints`,
  `CStarAlgebra.mem_Icc_iff_norm_le_one`, and NOTHING joining them); (ii)
  bridge 2 — Φ preserves transition probabilities via the Busch–Gudder strength
  function: λ(p, a) = sup{t : t·p ≤ a} is order-definable, and for rank-1 p
  the family a = q + ε(1−q) gives λ = ε/(ε·τ + (1−τ)) with τ = tr(pq), so a
  unital LINEAR order-iso preserves τ (matrix-concrete PSD computation); (iii)
  apply `wigner_rigidity` to the induced ray map; (iv) unitary/antiunitary ⟹
  Jordan auto (both branches: conjugation and transpose-conjugation preserve
  the symmetrized product). **Route B (fallback, original):** coordinates
  Uhlhorn from orthogonality alone — build the unitary column-by-column, phase
  gauge, antiunitary casework. Risk: **MED (was HIGH)** — 3.0 audited clean, so
  M3 = extreme-effects-are-projections + the strength-function bridge + the
  vendor/backport of an already-machine-checked rigidity theorem; Route B and
  the disclosed-axiom exit remain pre-registered fallbacks.

## M4 — Real + quaternionic branches

- **4.1 Real.** Rides M2 machinery over ℝ; discreteness kill (characters into
  O(1) trivial — `real_character_unique` pattern already proved). Risk LOW.
- **4.2 Quaternionic.** H_n(ℍ) ↪ H_{2n}(ℂ) symplectic embedding. [INV✓ area
  10]: ℍ itself is well-developed (NormedDivisionRing, CStarRing,
  InnerProductSpace ℝ) but **matrices over ℍ are total greenfield — zero
  declarations — and ℍ is not RCLike, so NONE of the areas-1-4 matrix stack
  applies to H_n(ℍ) directly.** The embedding route is therefore the only
  route: everything happens in the J-invariant complex picture
  (`LinearAlgebra/SymplecticGroup.lean` has `Matrix.J`, `J_squared`,
  `symplecticGroup` — isolated but present) and transports back through an
  explicit ℝ-linear iso. Risk MED, estimate leans to the high end of +1-2mo.

## M5 — Rank-two classification (parallelizable with M2–M4)

- **5.1 Lifting step (lem in prop:n2-necessity).** Continuous hom ℝ² → SO(2)
  lifts to a linear functional. ALL ingredients present [INV✓ area 8]:
  `Circle.isCoveringMap_exp`, `existsUnique_continuousMap_lifts` (simply
  connected + loc path-conn domain, Hatcher 1.33), hom-normalization via
  ker exp = 2πℤ discreteness, then `AddMonoidHom.toRealLinearMap`. Risk LOW
  (was MED pre-inventory).
- **5.2 ℝP² + descent (lem:n2-bounded/continuity/descent).** ℝP² absent from
  Mathlib in any form [INV✓ area 9]; build S²/± via orbit-quotient machinery
  (complete: ProperlyDiscontinuous free for finite Γ, T2, open quotient,
  compactness inherit [INV✓]). Two small genuine gaps to write: MulAction of a
  2-element group packaging `InvolutiveNeg`/`ContinuousNeg` on the sphere, and
  the `Function.Even → Function.FactorsThrough` bridge; then
  `IsQuotientMap.liftEquiv` gives C(ℝP²,ℝ) ↔ even C(S²,ℝ) [INV✓]. HARVEST
  option (08-04): csd-lean4's `Projectivization/Topology.lean` (466L, general
  `[DivisionRing K]`, Mathlib-staged, inside the audited 3.0 vendor closure)
  gives `ℙ ℝ ℝ³` a quotient topology directly — evaluate using it as the ℝP²
  carrier instead of a bespoke sphere quotient. Risk MED (volume), no unknowns.
- **5.3 Assembly (cor:qubit-classification).** Bijection between the M₂(ℂ)
  algebraic core (sp_blockForm etc., already proved) and the parameter space.
  Risk MED.

## M6 — Albert branch

- **6.1 block_injective discharge.** See `ALBERT-KERNEL-MEMO.md`: unit-slot
  argument (elementary; inputs = matrix-unit identities (I)/(II), Peirce
  bookkeeping (P1)/(P2), nucleus(𝕆) = ℝ finite check). Fallbacks: 128-unknown
  kernel certificate; disclosed axiom. Risk MED (was HIGH; validity verified at
  sketch level in the standard convention — re-derive (I)/(II) in the chosen
  model). Weeks, not months.
- **6.2 H₃(𝕆) construction.** On the existing octonion formalization
  (`~/repos/research/lean/Octonions.lean`, 0 sorries). Landscape-settled
  08-04: the "Nuccio octonions WIP" lead is DEAD (a mathlib mirror named
  "octonions", last activity 2023; zero octonion PRs by him); the live effort
  is mathlib4 PR #41919 (junjihashimoto, Cayley-Dickson tower, explicitly
  defers alternativity and the multiplicative norm, no Jordan/Albert,
  awaiting-author) — track it for eventual T4 alignment, do NOT wait for it.
  Only other prover artifact: Isabelle AFP `Octonions` (2018). Bryan's
  Octonions.lean is the mainline foundation. Risk MED.
- **6.3 Albert-instance analytic data.** Θ/dχ/ρ on H₃(𝕆) = M2 machinery
  specialized (rank exactly 3, no globalization needed). Risk MED-HIGH,
  shared shape with 2.6.

## M7 — Omnibus + statement upgrade + re-audit

- **7.1 mthm:omnibus.** Direct-sum assembly; summand inheritance of S1–S7 +
  converse (the documented paper-only halves of prop:central). Risk LOW-MED.
- **7.2 prop:pseudo-transfer.** Small. Risk LOW.
- **7.3 Statement upgrade.** Replace the skeleton capstone with concrete
  per-type theorems; rewrite `PaperA/Statement.lean`, AuditPins, THEOREM-MAP,
  README, paper §App + disclosure paragraph to the certified configuration.
- **7.4 Full audit re-elaboration** at every milestone boundary, not just M7
  (`lake env lean AxiomAudit.lean`; never truncate its output — tail-truncation
  hid a real failure on 2026-08-04 day 1).

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
