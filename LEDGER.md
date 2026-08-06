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
  **DONE 2026-08-05** (`Necessity/ThetaCocycle.lean`, census 56, gates green) —
  with the honest hypothesis accounting made explicit: vdW's 5.7(1) exchange
  consumes invariance of the standard product under unital order isos, which IS
  the Kadison content the campaign carries as `Θ_jordan` (M3). So the file
  proves unconditionally: `conj_eq_jordan` (the fundamental identity
  `s·y·s = 2 s∘(s∘y) − (s∘s)∘y`, closed by the `module` tactic after
  association-normalization), `sqrt_isEffect`, `sp_comm_of_commute` (commuting
  effects are ◦'-compatible, joint family, no PosDef), `seqLeftMul_mul_of_commute`
  (the S5 splitting `L'_{a◦'b} = L'_a∘L'_b`), `quadRepEquiv_mul_of_commute`
  (`Q_{√(ab)} = Q_{√a}∘Q_{√b}` — DIRECT REUSE of M1's
  `twistFactor_mul_of_commute` at `t = 0`); and conditionally on
  `PreservesJordan Θ`: `theta_conj_exchange` (5.7(1)) and
  `theta_cocycle_of_preservesJordan` (5.7(2), `Θ_m = Θ_a∘Θ_b`). At
  instantiation the condition is fed by the same `Θ_jordan` field the
  ComparisonSetup already carries — no NEW import, no circularity (both fields
  discharged independently: Θ_jordan by M3, Θ_cocycle by this + M3).
- **2.5 frame_opCommute + simDiag_opCommute (FK facts).** Direct block-form
  computations on matrices. LOW.
  **Concrete kit DONE 2026-08-05** (appended to `Necessity/ThetaCocycle.lean`,
  census unchanged 56, gates green): `symmMul_opCommute_of_commute` (matrix
  commutation ⟹ Jordan operator commutation `a∘(b∘·) = b∘(a∘·)` — targeted
  assoc-rewrites + `module`; this discharges BOTH opCommute fields since the
  concrete frame/diagonal/scalar elements all matrix-commute) and
  `conj_eq_self_of_symmMul_eq_self` (Peirce compression: `e∘x = x ⟹ e·x·e = x`,
  the `J₂(e)`-membership normal form for `block_mem_J2`). Instantiation-time
  predicate choices recorded: `J2 i j b := q·b·q = b`, `ScalarOn i j a :=
  ∃ lam a₀, a = lam•q + a₀ ∧ q·a₀ = 0 ∧ a₀·q = 0` (q = pᵢ+pⱼ), under which
  `simDiag_opCommute` reduces to a two-line matrix-commute check and
  `aOf_scalarOn` is the diagonal split at `rᵢ = rⱼ`.
- **2.6 THE ANALYTIC CORE: dχAdd + continuity + coalescence_diff.** Construct
  the character χ̃ from Θ on the orthant (group-level pieces `chi_hom`,
  `chi_comm`, `chi_extend_wellDefined` already proved), extend to ℝⁿ,
  differentiate. Continuous-additive⟹linear is PRESENT
  (`AddMonoidHom.toRealLinearMap` [INV✓]); the differentiation/smoothing of χ̃
  itself is bespoke analysis — the single largest M2 line-count risk. Risk
  HIGH (budget, not feasibility).
  **GENERIC CORE DONE 2026-08-05** (appended to `Necessity/OneParameter.lean`,
  census 57 unchanged, gates green — closure pure Lean core):
  `multiParameter_eq_exp` — a multiplicative family `χ : E → 𝔸` (E any real
  vector space) with `χ 0 = 1` and continuity ALONG LINES equals
  `r ↦ exp (D r)` for a unique LINEAR `D`. **The risk-HIGH item collapsed**:
  the line generators from `oneParameter_eq_exp` are ℝ-homogeneous and
  additive BY THE UNIQUENESS CLAUSE (reparametrize / merge commuting
  exponentials via `commute_of_commute_exp`, generators of commuting flows
  commute by differentiating twice), so linearity needs NO continuity input —
  Cartan smoothness is free, and `dχAdd_cont` is then automatic on the
  finite-dimensional source (`LinearMap.continuous_of_finiteDimensional`).
  REMAINING in 2.6 (instantiation side): build χ̃ from Θ on the concrete
  carrier (2.4's cocycle + `thetaEquiv` inverses per `chi_extend_wellDefined`),
  verify line-continuity from S2, choose the concrete ρ/Stab, and derive
  `coalescence_diff` from the group-level coalescence by differentiating the
  fixed-subspace property (the derivative of a curve constant on V_ij has
  vanishing V_ij-component). First instantiation ingredient DONE 2026-08-05:
  `theta_base_one` (`Necessity/Theta.lean`) — `Θ_1 = id` (χ̃(0) = 1), from S3
  and `cfc_apply_one`. Second ingredient DONE 2026-08-05:
  `Necessity/DiagonalFamily.lean` (census 58) — `frameProj` (standard frame:
  projections, orthogonality, `∑ = 1` via `Matrix.diagonalAddMonoidHom`
  map_sum) and `diagFamily r = diag(exp rᵢ)` (semigroup law `diagFamily_mul`,
  PosDef everywhere, effects on the negative orthant, frame decomposition
  `diagFamily_eq_sum_frameProj`, frame commutation) — the concrete `p`/`aOf`
  data for ComparisonSetup. Traps: vendored `HermitianMat.diagonal 𝕜 f` takes
  𝕜 explicitly but `diagonal_mat`/`diagonal_one` take it implicitly; no
  `Matrix.diagonal_sum` at pin — use `map_sum diagonalAddMonoidHom`;
  `Matrix.PosSemidef.diagonal` wants the Pi-order `0 ≤ d` (show-normalize
  `0 i`); rw cannot rewrite under `∑`-binders — `simp only [show …]`.
  **WIRING EXECUTED 2026-08-05** (`Necessity/ComparisonInstance.lean`, census 60,
  gates green): `comparisonSetup {N} (hN : 3 ≤ N) (P) (hS2) (hjord :
  ThetaPreservesJordan P) : ComparisonSetup (HermitianMat (Fin N) ℂ)` — every
  interface field discharged by a proved theorem except `Θ_jordan := hjord` (the
  isolated M3 import). Upgraded-from-cited-to-PROVED along the way: the FK/vdW
  **compatibility bridge** `opCommute_iff_commute` (quarter identity
  `[L_a,L_b]y = ¼[[a,b],y]`; commutator commutes with all Hermitians ⟹ scalar via
  `Matrix.mem_range_scalar_of_commute_single` ⟹ traceless ⟹ 0), the
  **span-extended vdW 5.5** `theta_fix_general` (posPart/negPart + normalization
  cancel), and `thetaNorm` (Θ total on PosDef via the 2.3 normalization law —
  vdW 5.4's raison d'être). Downstream abstract layers (`Coalescence`,
  `DiagonalHom`) now instantiate on the concrete carrier through this def.
  Traps: HermitianMat is a subtype ⟹ posPart dot-notation resolves to `Subtype.*`
  (use `b⁺`/`b⁻` notation; lemmas are `posPart_eq_cfc_max`/`negPart_eq_cfc_min`);
  `dite` on PosDef needs `letI := Classical.dec`; the (r+r')-orthant proof must be
  ascribed `∀ i, (r + r') i ≤ 0` or unification pins `fun i => r i + r' i` (H7).

  **χ̃ PART 2a DONE 2026-08-05** (`Necessity/ChiExtension.lean`, census 61, gates
  green): `thetaUnit r` (comparison map as a UNIT of End(H_n(ℂ)) — total in r,
  inverse carried by the LinearEquiv, no operator inversion), units-level
  cocycle + abelian image, `thetaUnit_div_eq` (representative-freedom of
  Θ_s Θ_t⁻¹ — the paper's well-definedness argument, done in the units group
  with `group` + two Commute-swaps), and `chiTilde r := thetaUnit (r ⊓ 0) *
  (thetaUnit (r ⊓ 0 − r))⁻¹` — case-free canonical representative — with
  `chiTilde_add` (homomorphism on all of ℝⁿ), `chiTilde_zero`,
  `chiTilde_of_nonpos`. All conditional on `ThetaPreservesJordan` where the
  cocycle enters, as everywhere in this lane. Remaining for 2.6:
  part 2b = line-continuity of `t ↦ (chiTilde (t•v)).val` (S2 for the L'-part
  on effects; explicit diagonal cfc for the Q⁻¹-part; `Ring.inverse`-continuity
  at units for the inverse factor; `continuous_clm_apply` findim reduction),
  part 2c = `multiParameter_eq_exp` ⟹ linear dχ with `χ̃ r = exp (dχ r)`;
  then ρ/coalescence_diff/Setup instantiations.

  **χ̃ PARTS 2b+2c DONE 2026-08-05** (`Necessity/ChiContinuity.lean`, census 62,
  gates green): the ANALYTIC HALF of `lem:homomorphism`, which the interface
  docstrings explicitly scope out of the abstract tree, is now machine-checked
  on the concrete carrier. Continuity ladder: S2 `ContinuousOn` composed with
  the effect-valued diagonal curve (`comp_continuous`) → `spPos` → `seqLeftMul`
  (posPart-split, all `show`-rfl unfolds) → `theta` (Q⁻¹-part = EXPLICIT
  diagonal conj via `cfc_diagonal`, `Continuous.matrix_diagonal/_mul/
  _conjTranspose`) → `thetaUnit.val` (`continuous_clm_apply` findim reduction)
  → inverse factor (`Ring.inverse_unit` + `NormedRing.inverse_continuousAt`) →
  `continuous_chiTilde_line`. Then `chiTilde_eq_exp` = `multiParameter_eq_exp`
  at 𝔸 := End(H_n(ℂ)): ∃! LINEAR dχ with χ̃(r) = exp(dχ(r)); `dChi` = the data.
  The abstract `dχAdd`/`dχAdd_cont` fields are thereby PROVED for the intended
  instance (a linear map is additive; findim linear is continuous).
  TRAPS (all resolved, remember these): (1) CLM's ambient TopologicalSpace =
  strong topology ≠ (syntactically) the norm topology — `IsTopologicalRing`/
  `ContinuousMul` DO NOT synthesize although plain-`rfl` proves the topologies
  defeq at default transparency; registered a local Prop-mixin instance
  `IsTopologicalRing (H →L H)` via `by exact @NonUnitalSeminormedRing.
  toIsTopologicalRing _ _` (explicit type arg, else stuck metas). (2) The Units
  instance diamond: `ˣ` elaborates over `ContinuousLinearMap.monoidWithZero`,
  `NormedRing.inverse_continuousAt` over `NormedRing.toRing`-path — rigid
  unification REFUSES though `Ring.inverse`-A = `Ring.inverse`-B by plain rfl;
  fix = repackage the unit field-by-field ⟨val, inv, val_inv, inv_val⟩ inside
  `by exact`. (3) `ContinuousAt.comp` higher-order unification grabs
  `f := Units.val` from a coerced point — pin `(f := …) (x := t₀)` explicitly.
  (4) `import Mathlib.Analysis.Normed.Ring.Lemmas` required for the
  seminormed→topological-ring instance at all.
  Remaining for 2.6: coalescence_diff (differentiate the fixed-subspace
  property: exp(t·dχ(r)) fixes the {i,j}-block when rᵢ = rⱼ ⟹ dχ(r) kills it),
  concrete ρ (block compression), CoalescenceSetup/DiagonalHomSetup wiring.

  **COALESCENCE INSTANCE DONE 2026-08-05** (`Necessity/CoalescenceInstance.lean`,
  census 63, gates green): `coalescenceSetup` extends `comparisonSetup`; all
  three FK fields DISCHARGED. `cornerQ i j` = diagonal indicator of {i,j}
  (idempotent for ALL i j incl. i = j — this dodges the i=j degenerate case the
  abstract field quantifies over); `simDiag_opCommute` (the FK
  simultaneous-diagonalization citation) reduced to: q absorbs J2(q)-elements
  (qbq = b + q² = q ⟹ qb = bq = b), so (λq + a₀)b = λb = b(λq + a₀);
  `aOf_scalarOn` = diagonal split-off; `block_mem_J2` = PURE RING ALGEBRA:
  Σ_{k∉{i,j}} Peirce-annihilations give (1−q)x + x(1−q) = 0 ⟹ qx + xq = 2x,
  then q-multiplications + idempotence give qxq = qx = xq ⟹ 2qxq = 2x. The
  abstract `coalescence_J2q`/`coalescence_block`/`block_preserved` now hold
  concretely. Trap notes: `Matrix.diagonal_add` is stated sum-on-LEFT (use
  FORWARD rw to merge diagonal sums); `IsBlockElt` is Fin-hardwired (state
  concrete lemmas over general index n via the raw relations, wrap at Fin N);
  mixed ℝ/ℂ-smul chains — convert (1/2:ℝ)• to (2:ℂ)⁻¹• entrywise
  (`Complex.real_smul`) BEFORE cancelling; rw rewrites ALL occurrences (use
  nth_rewrite when combining hqx/hxq). Remaining 2.6: DiagonalHomSetup's
  differential face (ρ, ρ_skew, coalescence_diff — the Stab-design question in
  the memory note) + dχAdd/dχAdd_cont (ALREADY PROVED via dChi: linear ⟹
  additive, findim ⟹ continuous).

  **ℂ-LANE ENDGAME DESIGN (banked 2026-08-05, after reading
  Branches/Complex.lean consumption).** `complex_perFrame_rho` consumes a
  StabilizerCoupling + the TORUS MODEL `hmodel : ρ_{ij}(dχ r) = (θᵢ(r) −
  θⱼ(r)) • J` — the model is MORE than the coupling (per-index characters θᵢ,
  not per-pair). Decoded discharge route, in order:
  (u1) **ouNorm-isometry of Θ** (order-iso + unital ⟹ preserves order-unit
  intervals ⟹ ouNorm-isometric) — cheap, uses the M1 ouNorm kit.
  (u2) **Block ouNorm = Euclidean**: on V_{ij}, x = zE_ij + z̄E_ji has
  x² = |z|²(E_ii + E_jj), so ouNorm x = |z| — the block order-unit norm IS the
  ℝ²-norm. Skewness mechanism: exp(t·dχ) preserves blocks + is
  ouNorm-isometric ⟹ block restriction is a Euclidean isometry group ⟹
  generator skew (d/dt ‖exp(tT)v‖² = 0 at t = 0). NO trace-preservation, NO
  compactness import.
  (u3) **dχ(r) preserves blocks** (differentiate concrete block-preservation).
  (u4) **coalescence_diff — STRONG form** (dχ(r) kills the block pointwise
  when rᵢ = rⱼ): χ̃(t•r) fixes corner elements ∀t (corner_commute +
  thetaNorm-fix at both canonical exponents, which inherit rᵢ = rⱼ), and
  exp(t•dχ(r))x ≡ x differentiates to dχ(r)x = 0 (hasDerivAt_exp_smul_const +
  CLM-apply + constant-curve uniqueness).
  (u5) **Stab := the submodule of block-skew CLMs**; ρ i j := block
  compression via ε_{ij}/β_{ij} (ℝ² coordinates a+bi ↦ zE_ij + z̄E_ji);
  ρ_skew holds ∀ξ ∈ Stab BY MEMBERSHIP; dχ(r) ∈ Stab by u2/u3.
  DiagonalHomSetup instance: dχAdd := (dChi …).toAddMonoidHom, dχAdd_cont by
  findim, coalescence_diff from u4 (compression of a pointwise-killed block).
  (u6) **hmodel via the phase cocycle**: V_ij ∘ V_jk ⊆ V_ik with the ℂ-mult
  formula (zE_ij + z̄E_ji)∘(wE_jk + w̄E_kj) = ½(zwE_ik + conj), so hjord forces
  the block rotations to satisfy R_ik(zw) = R_ij(z)·R_jk(w); orthogonal +
  multiplicative + connected-to-identity ⟹ R_ij = rotation by φ_{ij} with
  φ_{ij} + φ_{jk} = φ_{ik} ⟹ φ_{ij} = θᵢ − θⱼ (anchor θᵢ := φ_{i,i₀}). This is
  the paper's torus identification, machine-checkable without classifying
  Aut(H_n(ℂ)).

  **u4 (coalescence_diff) DONE 2026-08-05** (`Necessity/CoalescenceDiff.lean`,
  census 64, gates green): `dChi_kills_corner` — when rᵢ = rⱼ the differential
  ANNIHILATES the Peirce-2 corner pointwise (strong form; any compression ρ
  then discharges the abstract field). Chain: both canonical exponents of
  χ̃(t•r) inherit the coalescence → `corner_commute` + `thetaNorm_fix_of_commute`
  (+ inverse-fix through the LinearEquiv) → χ̃(t•r) x ≡ x → `exp_apply_const_kill`
  (hasDerivAt_exp_smul_const + HasDerivAt.clm_apply against the constant curve).
  Trap: `rw [zero_smul]` will NOT match `(0:ℝ) • A` inside exp (OfNat-vs-Zero
  zero forms); use `rw [show (0:ℝ) • A = 0 from zero_smul ℝ A]`. Remaining for
  2.6: u1/u2 (ouNorm-isometry + block-Euclidean skewness), u3 (block
  invariance of dχ), u5 (Stab submodule + DiagonalHomSetup instance), u6
  (phase-cocycle torus model).

  **u1 (ouNorm-isometry) DONE 2026-08-05** (`Necessity/ThetaIsometry.lean`,
  census 65, gates green): `ouNorm_thetaNorm`/`ouNorm_thetaUnit`(+inv)/
  `ouNorm_chiTilde` — a unital order-iso transports the ouNorm defining set
  verbatim (thetaNorm_le_iff from nonneg_iff by sub; the two interval bounds
  via map_smul + thetaNorm_one); inverse-factor isometry by applying the
  forward isometry at the image and cancelling with `Units.mul_inv` (rw
  [← ContinuousLinearMap.mul_apply, Units.mul_inv]; rfl — do NOT try congrArg
  on val_inv, simp collapses it to True). Remaining: u2 (block-Euclidean +
  skewness), u3 (block invariance of dχ), u5, u6.

  **u3 (block invariance) DONE 2026-08-05** (`Necessity/BlockInvariance.lean`,
  census 66, gates green): `cornerJ2 ⟺ q∘x = x` (Jordan eigenrelation; forward
  by absorption, backward via `cornerJ2_of_double`, which was refactored out of
  `blockElt_cornerJ2` for reuse); `thetaNorm_preserves_cornerJ2` (+ .symm via
  the 5-line inverse-Jordan argument `thetaNorm_symm_jordan`, injectivity +
  apply_symm_apply — NO dimension plumbing) → `chiTilde_preserves_cornerJ2` →
  `dChi_preserves_corner` (cornerConjCLM kernel-characterization + the same
  exp-differentiation pattern as u4, now against the invariance curve).
  Traps: stale .olean — after refactoring a lemma into an imported file, `lake
  build` the import BEFORE `lake env lean` on the consumer; `hasDerivAt_const`
  with a CLM-valued constant hits a zero-instance-path mismatch when the
  derivative slot is ascribed `0` — drop the ascription and let simpa
  normalize. Remaining: u2 (block-Euclidean + skewness), u5 (Stab +
  DiagonalHomSetup), u6 (phase cocycle → hmodel).

  **u2 PART 1 (block model) DONE 2026-08-05** (`Necessity/BlockModel.lean`,
  census 67, gates green): `blockHerm i j z = z E_ij + z̄ E_ji`; the SQUARE LAW
  `blockHerm_symmMul_self : x∘x = |z|²•(pᵢ+pⱼ)` (four single-products, the
  e1–e4 haves by simp with the ne-facts); entry helpers
  `single_one_mul_apply`/`mul_single_one_apply`; and the SUPPORT
  CHARACTERIZATION `eq_blockHerm_of_peirce` (Peirce relations ⟹
  x = blockHerm i j x_{ij}; rows/cols kill via the annihilations, diagonals
  via the ½-relations + linear_combination, 7-case entry bash subst-free with
  eq_true/eq_false condition facts + conv_lhs). TRAPS: `subst` on ext-locals
  can eliminate THEOREM PARAMETERS (i became a — later i-references break) —
  case-bash subst-free; lambdas in simp-arg lists parse badly — use
  eq_false/eq_true `have`s; `Complex.mul_conj` is stated with starRingEnd —
  `rw [Complex.star_def]` first; `if_pos rfl` may be pre-reduced to `if True`
  by the rewriting lemma — `simp only [if_true]`.
  REMAINING u2 part 2 (next stretch, plan): `thetaNorm_fixes_frameProj`
  (fix_of_commute + diagFamily_commute_frameProj), blockHerm Peirce relations
  (frameProj∘blockHerm computations, same four products), Θ-transport of the
  relations (hjord 3-line pattern) ⟹ `thetaNorm_block : Θ(blockHerm z) =
  blockHerm (entry)`, then the CAPSTONE `normSq_thetaNorm_block`: square law
  on both sides + Θ(x∘x) = Θx∘Θx + Θ fixes pᵢ+pⱼ ⟹ |w|² = |z|² by the (i,i)
  entry (ofReal_inj). Then u5: V := EuclideanSpace ℝ (Fin 2), blockCoord/
  blockEmbed CLMs, R(t) := coord∘χ̃(t•r)∘embed norm-preserving ⟹ generator
  skew (differentiate ‖R(t)v‖² via exp_apply_hasDerivAt), Stab := submodule of
  block-skew CLMs, DiagonalHomSetup instance, toStabilizerCoupling. Then u6.

  **u2 COMPLETE 2026-08-05** (`Necessity/BlockTransport.lean`, census 68,
  gates green): `thetaNorm_fixes_frameProj`; the three blockHerm Peirce
  relations (per-relation four single-products by simp with ne-facts; the
  ½-coefficient by entrywise push_cast + ring); `thetaNorm_block` (Θ maps
  blocks to blocks — eq_blockHerm_of_peirce fed by the hjord 3-line transport
  ×3); and the CAPSTONE `normSq_thetaNorm_block`: |w|² = |z|² by comparing the
  square law on both sides of Θ(x∘x) = Θx∘Θx with Θ fixing pᵢ+pⱼ, read off at
  the (i,i) entry (if_true again — the ite pre-reduces; ofReal cast via
  exact_mod_cast). **Θ acts on every off-diagonal block by a Euclidean
  isometry — no ouNorm, no trace, no compactness.** Remaining: u5 (V :=
  EuclideanSpace ℝ (Fin 2), blockCoord/blockEmbed, R(t) := coord∘χ̃(t•r)∘embed
  isometric ⟹ skew generator via exp_apply_hasDerivAt differentiation of
  ‖R(t)v‖², Stab := block-skew submodule, DiagonalHomSetup instance,
  toStabilizerCoupling), u6 (phase cocycle ⟹ hmodel ⟹ complex_perFrame_rho).

  **u5a DONE 2026-08-05** (`Necessity/BlockChi.lean`, census 69, first-pass
  clean): `blockHerm_entry` (coordinate readback), `thetaNorm_block_exists` /
  `thetaNorm_symm_block_exists` (inverse via inverse-Jordan relation transport
  + forward-isometry-at-image + Θ∘Θ⁻¹-cancel), and
  **`chiTilde_block_exists`: χ̃(r) acts on every off-diagonal block by a
  Euclidean isometry, for every r** (chain the two factors through the
  canonical exponents). REMAINING u5b/c (plan in memory later-25): entryLm/
  blockCoord/blockEmbed over V := ℝ × ℝ (avoid EuclideanSpace PiLp friction;
  Prod has the ℝ-inner instance), the skew punchline `v.1*w.re + v.2*w.im = 0`
  for w := entry of dχ(r)(blockEmbed v) — differentiate F(t) := normSq(entry
  of χ̃(t•r)(blockEmbed v)) ≡ normSq z₀ at t = 0 (exp_apply_hasDerivAt ∘
  entryCLM, re/im split, HasDerivAt.mul/add, unique vs const) — then Stab :=
  block-skew submodule, ρ := coord∘ξ∘embed, DiagonalHomSetup instance
  (dχAdd := toAddMonoidHom, cont := findim, coalescence_diff := block⊆corner ∘
  dChi_kills_corner), toStabilizerCoupling fires. Then u6.

  **u5b DONE 2026-08-05** (`Necessity/BlockSkew.lean`, census 70, gates
  green): `dChi_block_skew` — **prop:isotropy machine-checked**: for
  z₀ = v₁ + v₂i and w := entry of dχ(r)(blockHerm z₀), the Euclidean dot
  v₁·w.re + v₂·w.im = 0. Proof: entry curve c(t) := entryCLM(exp(t•A)x) has
  derivative w at 0 (exp_apply_hasDerivAt + const.clm_apply); re/im components
  via Complex.reCLM/imCLM the same way; F := re·re + im·im is CONSTANT ≡
  normSq z₀ (chiTilde_block_exists + blockHerm_entry readback); (hre.mul
  hre).add (him.mul him) + unique-vs-const + hval0 (exp(0) = 1) ⟹
  2(v₁w.re + v₂w.im) = 0. No compactness, no invariant measure — the square
  law + one-variable calculus. `entryLm`/`entryCLM` + `entryCLM_apply` built
  here. REMAINING u5c: Stab := block-skew submodule of the CLM space, ρ i j ξ
  := blockCoord ∘ ξ ∘ blockEmbed over V := ℝ × ℝ, dχ ∈ Stab (this theorem),
  DiagonalHomSetup instance (dχAdd := toAddMonoidHom of dChi-linear, cont by
  findim, coalescence_diff := blockHerm ∈ cornerJ2 + dChi_kills_corner) →
  toStabilizerCoupling. Then u6 (phase cocycle → hmodel).

  **u5c DONE 2026-08-05 — 2.6 COMPLETE, THE COUPLING IS PRODUCED**
  (`Necessity/StabilizerInstance.lean`, census 71, gates green):
  `blockCoordLm`/`blockEmbedLm` (ℝ-linear block coordinates), `IsBlockSkew` +
  `blockSkewSubmodule` (Stab; dχ ∈ it by prop:isotropy), `rhoField` (the
  compression, 0 on diagonal pairs — dodges the field's unrestricted
  quantifier), `dChiStab` (+continuity by findim), `rhoField_dChi_coalesced`
  (through blockElt_cornerJ2 + dChi_kills_corner), the `diagonalHomSetup`
  instance over **BlockV := WithLp 2 (ℝ × ℝ)** (bare ℝ × ℝ has NO inner
  product — sup norm! — the L2 synonym does; `WithLp.prod_inner_apply` is
  rfl-simp), and **`stabilizerCoupling` := `.toStabilizerCoupling` — the
  coupling ρ_{ij}(dχ(r)) = (r_i − r_j)•T_{ij} is now a machine-checked THEOREM
  on H_N(ℂ)**, conditional only on S2 + ThetaPreservesJordan (M3). TRAPS: the
  setup's index type is `Fin (setup.n)` — defeq to Fin N but rw is syntactic:
  pin every helper-lemma use with `(n := Fin N)` and open field proofs with
  `show`-retyped goals; final skew goal closes by `exact hs` (pure defeq —
  ofLp/toLp/linearEquiv all reduce) after prod_inner_apply + RCLike.inner_apply
  + star_trivial; coalescence via pointwise `LinearMap.ext` + `show` + rw of
  the vanishing map (never rewrite under the composition form). REMAINING for
  the ℂ-lane: u6 (phase cocycle ⟹ hmodel ⟹ complex_perFrame_rho), then
  Globalization wiring, then the per-type statement. M2 else: 2.9.

  **u6a DONE 2026-08-05** (`Necessity/PhaseCocycle.lean`, census 72, gates
  green): (1) `skew_linear_eq_I_smul` — the 2×2 skew classification: ℝ-linear
  `T : ℂ → ℂ` with `z.re*(Tz).re + z.im*(Tz).im = 0` everywhere equals
  `z ↦ (T 1).im • (I*z)` (polarization at 1, I, 1+I; decompose z by
  `z = z.re•1 + z.im•I` in a `conv_lhs`-scoped `have` — a bare `rw [hz]`
  rewrites the RHS z too and strands mixed `(↑z.re).im` terms). (2)
  `blockHerm_symmMul_blockHerm` — cross-block product: for pairwise distinct
  i,j,k, `blockHerm i j z ∘ blockHerm j k v = (1/2:ℝ) • blockHerm i k (z*v)`
  (eight single-products, only E_ij·E_jk and E_kj·E_ji survive; `star_mul`
  aligns the z̄v̄ coefficient; ℝ-vs-ℂ ½ via entrywise push_cast+ring).
  REMAINING u6: (6c) dχ(r) is a Jordan derivation (differentiate the
  Jordan-preservation of χ̃(t•r) at t=0 via exp_apply_hasDerivAt + the
  bilinear symmMul CLM), (6d) entry maps T_ij := (D(blockHerm i j ·)).mat i j,
  Leibniz across blocks ⟹ cocycle t_ik = t_ij + t_jk, antisymmetry, anchor
  θ_i := t_{i,i₀} ⟹ hmodel ⟹ `complex_perFrame_rho` fires on H_N(ℂ).

  **u6c DONE 2026-08-05** (`Necessity/JordanDerivation.lean`, census 73, gates
  green): `chiTilde_jordan` (χ̃(r) is a Jordan automorphism at every r —
  forward factor by thetaNorm_jordan, inverse factor by thetaNorm_symm_jordan,
  through the two-factor unit definition via a `show`-unfolded hval),
  `exp_smul_dChi_symmMul` (exp(t•dχ(r)) = χ̃(t•r) via map_smul on dChi),
  `exp_entry_hasDerivAt` (entry functions of a flow differentiate to the
  generator's entry: entryCLM.hasFDerivAt.comp_hasDerivAt, two-step have to
  dodge the ∘-vs-λ HO-unification), and **`dChi_jordan_derivation` — dχ(r) is
  a Jordan derivation, D(x∘y) = Dx∘y + x∘Dy, machine-checked**. TRAP (major):
  the curried-bilinear route `jordanCLM : E →L (E →L E)` is DEAD —
  `ContinuousLinearMap.hasFDerivAt` at codomain `E →L E` requires unifying the
  ambient strong-topology instance with the operator-norm topology path at
  depth 2; the defeq check exhausts 1.6M heartbeats and then fails as a type
  mismatch. Route around it ENTRYWISE: all calculus in ℂ (HasDerivAt.mul +
  HasDerivAt.fun_sum — NOT .sum, which in current Mathlib is the
  function-valued-sum form with a Finset metavariable — + const_mul with
  (2:ℂ)⁻¹), then one funext to χ̃'s automorphism property and
  HasDerivAt.unique; entry extraction via BlockSkew's entryCLM whose codomain
  ℂ has a unique instance path. Import chain: JordanDerivation imports
  BlockSkew (for entryCLM), not PhaseCocycle; the u6d file will import both.

  **u6d DONE 2026-08-05 — LEDGER 2.6 FULLY COMPLETE, `complex_perFrame_rho`
  FIRES** (`Necessity/PhaseAnchor.lean`, census 74, gates green):
  `symmMul_blockHerm_entry`/`blockHerm_symmMul_entry` (the (i,k)-entry of a
  cross-block Jordan product — the blockHerm factor's structure does all the
  killing, NO corner-support lemma needed), `blockHermLm` (z ↦ blockHerm z
  ℝ-linear), `dChiEntry` (the block entry map as ℂ →ₗ[ℝ] ℂ),
  `dChiEntry_eq` (skew classification: multiplication by i·t_{ij}(r)),
  `tvalLm` (the phase rate, linear in r), **`tval_cocycle`
  (t_{ik} = t_{ij} + t_{jk} — Leibniz + cross-block product at the (i,k)
  entry)**, `tval_antisymm` (Hermiticity), `thetaAnchor`/`tval_eq_theta_sub`
  (anchor at i₀ collapses pairs to characters), `cMatrix`/`thetaAnchor_expand`
  (θ_i(r) = Σ_l c_{il} r_l via univ_sum_single + map_sum), `rotJ` (+ ≠ 0),
  the `stabilizerCoupling_rho_dChi` bridge, and
  **`complex_perFrame_concrete`: for any S1–S7 sequential product on H_N(ℂ)
  (N ≥ 3, S2, M3-hjord) there is a single per-frame t_F with
  ρ_{ij}(dχ(r)) = (t_F(r_i − r_j)) • J — the paper's `thm:complex` per-frame
  half, PRODUCED on the concrete carrier.** TRAPS: `unfold A B` processes
  sequentially — a constant B whose body mentions A must be unfolded FIRST
  (`unfold cMatrix thetaAnchor`, not the reverse); norm_num at a hypothesis
  re-normalizes HermitianMat entry atoms into a coe-form that no longer
  matches the goal's mat-form (drop norm_num, use smul_eq_mul + linarith);
  `set u := equiv v` fights simp's WithLp.fst/snd normal form — unfold via
  `simp [hu]` at the end; Finset.sum_eq_single side goals arrive with the
  ∧-condition pre-reduced (provide `Ne.symm hm`, not the ∧-shaped eq_false).
  REMAINING for the ℂ-lane per-type statement: Globalization wiring (adjacent
  frames, global t) — check `Globalization.lean` for what it consumes — then
  assemble mthm:master (ℂ) with M1's twistSequentialProduct as sufficiency
  witness. M2 else: 2.9 (prop:singular wiring). Then M3–M7.

  **WIRING DESIGN (banked 2026-08-05, before χ̃ part 2):** build the
  `ComparisonSetup (HermitianMat (Fin N) ℂ)` instance NEXT — the abstract
  DiagonalHom layer then supplies `chi_hom`/`chi_comm`/`chi_extend_wellDefined`
  (the ℝⁿ-extension bookkeeping) FOR FREE. Field discharge map: jordan :=
  symmMul-bilinear (build the bilinear map; vendored comm/one lemmas);
  e := 1; p := frameProj; aOf := diagFamily; nonneg := (0 ≤ ·);
  **Inv := (·.mat.PosDef)** (aOf_inv must hold for ALL r, so effects cannot
  enter Inv); **Θ total via normalization**: `Θ a := thetaEquiv at
  ((‖a‖+1)⁻¹ • a)` when PosDef (always an effect by `norm_smul_inv_effect`,
  PosDef preserved), `LinearEquiv.refl` otherwise — the 2.3 law `theta_smul`
  makes every Θ-property scale-invariantly inherited and is WHY vdW 5.4
  exists; Θ_unital/Θ_orderIso/Θ_fix/Θ_cocycle from the 2.1f/2.2/2.4+Chi
  theorems (cocycle threads the Θ_jordan hypothesis, which is also the
  Θ_jordan field — take a global `hjord` parameter); frame_opCommute :=
  `symmMul_opCommute_of_commute` + `diagFamily_commute_frameProj`; rank_ge =
  parameter. Then χ̃ part 2 = the abstract extension applied at the instance +
  line-continuity from S2 + `multiParameter_eq_exp`.
  Third ingredient (χ̃ part 1) DONE 2026-08-05 (`Necessity/Chi.lean`, census
  59, compiled clean first pass): `theta_congr` (base-point congruence, subst +
  proof irrelevance), `sp_diagFamily` (`a(r) ◦' a(r') = a(r+r')` — the 2.2
  value identity + the √-collapse on the commuting diagonal), `thetaD_zero`
  (χ̃(0) = 1 via `theta_base_one`), and `thetaD_mul` (**the orthant cocycle**,
  conditional on the M3 Jordan field). Part 2 = the ℝⁿ-extension +
  line-continuity from S2 + `multiParameter_eq_exp` ⟹ dχ.
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
  **PROOF PLAN (banked 2026-08-05, design pass done).** Substitute
  `g t := h (Real.exp t)`: continuous everywhere (exp lands in Ioi 0),
  `g (s+t) = g s * g t`, `g 0 = 1` — a continuous one-parameter semigroup in
  the Banach algebra `W →L[ℝ] W`. Classify `g = exp(t • A)` by the classical
  integral-regularization argument, ALL ingredients inventory-confirmed:
  (i) choose δ > 0 with `‖g s − 1‖ ≤ 1/2` on `[0, δ]` (continuity at 0);
  `J := ∫ s in 0..δ, g s` satisfies `‖J − δ•1‖ ≤ δ/2` <
  (`intervalIntegral.norm_integral_le_of_norm_le_const`), so `δ⁻¹•J = 1 − t`
  with `‖t‖ < 1` is a unit (`Units.oneSub`, geometric series);
  (ii) `g t * J = ∫ s in t..(t+δ), g` (translation/`integral_comp_add_left` +
  the semigroup law pulled through `intervalIntegral.integral_const_mul`-style
  linearity — g t is a CONSTANT operator factor, use `ContinuousLinearMap`
  composition under the integral or `intervalIntegral.integral_smul`-analogue
  via `ContinuousLinearMap.integral_comp_comm`), so
  `g t = (F (t+δ) − F t) * J⁻¹` with `F u := ∫ 0..u, g` — differentiable by
  FTC-2 (`intervalIntegral.integral_hasDerivAt_right`), hence g is C¹;
  (iii) `A := deriv g 0`; the difference quotient factorization
  `g (t+h) − g t = g t * (g h − 1)` gives `HasDerivAt g (g t * A) t`;
  (iv) `d/dt [g t * exp(−t•A)] = 0` via `hasDerivAt_exp_smul_const`, product
  rule, and `Commute A (exp (−t•A))` (`Commute.exp_right`-style, from
  self-commutation) ⟹ constant = `g 0 = 1` ⟹ `g t = exp (t•A)`
  (`is_const_of_deriv_eq_zero` on ℝ, or `Constant.of_hasDerivAt_zero`);
  (v) back-substitute `x = exp (log x)` for `x > 0`; uniqueness: from
  `∀ x > 0, exp (log x • A) = exp (log x • B)`, take `x := exp t` ⟹
  `exp (t•A) = exp (t•B)` ∀t, differentiate at 0 ⟹ `A = B`.
  Then DELETE the axiom, replace with the theorem (same name/signature so the
  two call sites in NormalFormExistence.lean are untouched), drop it from the
  audit allowlist — **custom-axiom count 1 → 0; closure = pure Lean core.**
  **CORE LEMMA DONE 2026-08-05** (`Necessity/OneParameter.lean`, census 57,
  gates green): `oneParameter_eq_exp` — continuous one-parameter semigroups in
  a real Banach algebra are `t ↦ exp (t•A)` with unique generator, by exactly
  the banked plan (all five steps; the opaque-generator trick
  `obtain ⟨A, hA0⟩ := ⟨_, hg' 0⟩` avoids `set`-folding fragility in the ODE
  step). Lean notes: the 𝕂-free `exp` refactor puts `exp_add_of_commute` in a
  `[NormedAlgebra ℚ 𝔸]` section with NO instance path from ℝ — route through
  `exp_add_of_commute_of_mem_ball (𝕂 := ℝ)` + `expSeries_radius_eq_top ℝ`;
  `Commute.exp_right` is unconditional (the no-ℚ case has `exp = 1` by
  definition); FTC-2 = `intervalIntegral.integral_hasDerivAt_right` +
  `Continuous.stronglyMeasurable.stronglyMeasurableAtFilter` (no explicit
  args); constancy via `is_const_of_fderiv_eq_zero` (needs the MeanValue
  import; no deriv-named variant exists at pin).
  **2.7 COMPLETE 2026-08-05: THE TREE IS AT ZERO CUSTOM AXIOMS.** The wrapper
  `aczel_multiplicative_classification` (same file) substitutes
  `g := h ∘ Real.exp`; `Selection.aczel_continuous_multiplicative` is now a
  THEOREM aliasing it (name + signature preserved, both call sites untouched);
  audit surgery done (allowlist = the three core axioms, citedAxioms = [],
  Layer-4 pin refrozen on the theorem, prose in AxiomAudit/README/THEOREM-MAP).
  Gate verified first-hand: "custom axioms exactly [], every tracked persisted
  declaration's closure ⊆ [propext, Classical.choice, Quot.sound]".
- **2.8 `bgw_canonical_composite` ELIMINATION — DONE 2026-08-04.** Replaced the
  axiom (a constructible existence claim, hence not falsifiable) with the
  pattern-match definition `bgwComposite` + `rfl`-proved `bgwComposite_table`;
  non-matrix rows = documented junk-total `.real 0`, consumed nowhere. Audit
  updated (allowlist + citedAxioms to one, Layer-4 bgw pin removed, docstrings);
  README / THEOREM-MAP §2 / NormalFormExistence / Interface docstrings updated.
  **Custom-axiom count: 2 → 1** (Aczél alone); → 0 after 2.7.
- **2.9 prop:singular (singular-effect extension) — DONE 2026-08-05, M2
  COMPLETE** (`Necessity/SingularExtension.lean`, census 75, gates green):
  `isEffect_interp`/`posDef_interp` (the boundary sequence a + t(𝟙−a) is an
  effect for t ∈ [0,1] and PosDef for t ∈ (0,1] — split as t•𝟙 + (1−t)•a,
  PosDef.one.smul + zero_le_iff/PosSemidef.smul + add_posSemidef),
  `dense_posDef_effects` (density in the effect SUBTYPE via
  mem_closure_of_tendsto + tendsto_subtype_rng; sequence 1/(k+1)),
  `sp_eq_on_effects_of_eq_on_posDef` — **prop_singular is now INVOKED**: two
  S1–S7 products with S2 agreeing on PosDef effects agree on ALL effects
  (continuousOn_iff_continuous_restrict turns S2 into subtype-continuity).
  TRAP: Matrix.PosDef over ℂ needs `open ComplexOrder` (scoped PartialOrder ℂ)
  — without it the statements themselves fail to elaborate; and
  OrderUnitSpace shadows `add_nonneg` (qualify `_root_.add_nonneg`).

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
