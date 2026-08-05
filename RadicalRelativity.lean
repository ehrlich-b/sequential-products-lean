-- Standalone Lean development for the paper:
--   "A Classification of Sequential Products on Simple Euclidean Jordan
--    Algebras of Rank >= 3" (twist normal form).
--
-- This root aggregates exactly the paper's modules. The four modules
-- OrderUnitSpace, SequentialProduct, LocalTomography, SpinFactor are the
-- program-shared support definitions copied verbatim from the parent
-- Radical Relativity development so that this project has ZERO dependency
-- on any other program code; they are pulled in transitively below.

-- Twist normal form (operator-level normal form; statement-level scaffold).
import RadicalRelativity.TwistNormalForm

-- Part II selection: block-restricted equidistribution and the selector core.
import RadicalRelativity.Selection.Equidistribution
import RadicalRelativity.Selection.NormalFormExistence
import RadicalRelativity.Selection.SelectorEquivalence
import RadicalRelativity.Selection.Descent
import RadicalRelativity.Selection.TwistIsotropy

-- Part I type exclusion: base-equality dichotomy.
import RadicalRelativity.Selection.BaseEquality

-- Master theorem chain (capstone `master_chain`), 12 modules including Central.
import RadicalRelativity.MasterTheorem.Interface
import RadicalRelativity.MasterTheorem.Coalescence
import RadicalRelativity.MasterTheorem.DiagonalHom
import RadicalRelativity.MasterTheorem.Branches.Real
import RadicalRelativity.MasterTheorem.Branches.Quaternionic
import RadicalRelativity.MasterTheorem.Branches.Albert
import RadicalRelativity.MasterTheorem.Branches.Complex
import RadicalRelativity.MasterTheorem.Globalization
import RadicalRelativity.MasterTheorem.Adapter
import RadicalRelativity.MasterTheorem.Master
import RadicalRelativity.MasterTheorem.RankTwo

-- Central decomposition (`prop:central`): an S1–S7 product on a direct-sum EJA is
-- componentwise. Adds the machine-checked componentwise formula; summand-inheritance
-- is a documented paper-only follow-up.
import RadicalRelativity.MasterTheorem.Central

-- Interface inhabitedness witnesses: one degenerate instance per interface
-- structure (vacuity guard; certifies inhabitedness only, NOT the intended EJA
-- instantiation — see the module docstring and LEDGER.md).
import RadicalRelativity.MasterTheorem.Witnesses

-- Vendored physlib HermitianMat island (Apache 2.0, pinned; see
-- RadicalRelativity/Vendor/VENDOR.md): the M1 carrier substrate — Hermitian
-- matrices with Loewner order, trace inner product, CFC, and the symmetrized
-- (Jordan) product. Importing Jordan + Proj pulls the whole 17-file closure.
import RadicalRelativity.Vendor.HermitianMat.Jordan
import RadicalRelativity.Vendor.HermitianMat.Proj

-- M1 order-unit layer on the concrete carrier (LEDGER 1.1): the
-- `OrderUnitSpace (HermitianMat n 𝕜)` instance (making the abstract effect
-- predicate definitionally the Loewner unit interval), the full Archimedean
-- property over ℂ, the order-unit norm as an unbundled def, and
-- extreme-points-of-the-effect-interval = projections (M3 bridge 1).
import RadicalRelativity.Hermitian.OrderUnit
import RadicalRelativity.Hermitian.ExtremeEffects

-- M1 twist definition (LEDGER 1.2, pair-of-real-cfc route): `a^{1/2+it}` from two
-- real functional-calculus components, the twist sequential product as a `conj`
-- (S1/monotonicity/effect-closure ride the vendored conj lemmas), unit laws, and
-- the t = 0 Lüders specialization.
import RadicalRelativity.Hermitian.Twist

-- M1 spectral-resolution infrastructure (LEDGER 1.3): value-indexed spectral
-- projections `specProj` with the expansion of every cfc over them, and the
-- resolution lemma (cfc respects ANY orthogonal-idempotent presentation, via
-- Lagrange interpolation) — the two-variable engine behind the S5 verification.
import RadicalRelativity.Hermitian.Resolution

-- M1 S1–S7 verification (LEDGER 1.3, paper `lem:twist-sufficiency`): S4 by the
-- trace route, compatibility ⟺ commutation (Frobenius certificate / Gudder–Nagy
-- at general twist), the two-variable law `(ab)^{1/2+it} = a^{1/2+it}·b^{1/2+it}`
-- on commuting positives, S5–S7, S2 norm continuity, and the packaged
-- `twistSequentialProductCore` / `twistSequentialProduct` per twist parameter.
import RadicalRelativity.Hermitian.Sequential

-- M2 necessity core, first unit (LEDGER 2.1, paper lem:homog(i)): for an ARBITRARY
-- sequential product on the carrier's fixed Loewner order (`SequentialProductOn`,
-- the carrier-pinned formulation added to SequentialProduct.lean), the left
-- multiplication b ↦ a & b extends to a positive linear map `seqLeftMul` —
-- ℕ/ℚ/ℝ-homogeneity by finite additivity plus the Archimedean squeeze, cone
-- extension, and the posPart/negPart difference construction.
import RadicalRelativity.Necessity.LeftMultiplication

-- M2 necessity core, second unit (LEDGER 2.1b, paper lem:homog(ii)): first-argument
-- homogeneity (t•a) & b = t•(a & b) for the unknown product — the rational
-- compatibility ladder (iterated S6b, S6a orthocomplement flip), the rational value
-- law, the SINGLE S2 limit (t•1) & b = t•b, and the S5 assembly.
import RadicalRelativity.Necessity.FirstArgument

-- M2 necessity core, third unit (LEDGER 2.1c, sharp-effect base layer): projections
-- are sharp product-independently (the conjugation pinch), hence idempotent under
-- ANY sequential product (S6a on trivial self-compatibility + the S1 splitting),
-- and orthogonal projections annihilate in both orders (S4) and are compatible.
import RadicalRelativity.Necessity.SharpEffects

-- M2 necessity core, fourth unit (LEDGER 2.1e, vdW 4.19-4.20): the normalized
-- spectral pseudo-inverse of a positive-definite effect, the cancellation
-- L'_nu (L'_b x) = c x through S5 and the 2.1d value law, and the payoff:
-- the unknown product's left multiplication is order-REFLECTING and injective.
import RadicalRelativity.Necessity.PseudoInverse

-- M2 necessity core, fifth unit (LEDGER 2.1f, closing 2.1; vdW 5.3): the comparison
-- map Theta_a := Q_{sqrt a}^{-1} composed with the unknown left multiplication, as a
-- LinearEquiv (injectivity from the pseudo-inverse cancellation, surjectivity from
-- finite dimension), UNITAL, and an ORDER ISOMORPHISM in both directions.
import RadicalRelativity.Necessity.Theta

-- M2 necessity core, sixth unit (LEDGER 2.2, vdW 5.5): Theta fixes commuting
-- effects — the joint spectral family of a commuting pair (both effects diagonal
-- in it via the padding lemmas), the unknown product takes the standard Lueders
-- value on commuting pairs, and theta_fix by cancelling the quadratic
-- representation through the defining equation.
import RadicalRelativity.Necessity.ThetaFix

-- M2 necessity core, seventh unit (LEDGER 2.4, vdW 5.7): the Theta cocycle —
-- the fundamental identity (Lueders conjugation is a Jordan polynomial), the S5
-- splitting of left multiplications, Q-multiplicativity riding M1's twist factor
-- at t = 0, the 5.7(1) exchange, and the cocycle Theta_m = Theta_a Theta_b,
-- stated conditionally on PreservesJordan (discharged by the Theta_jordan field
-- at instantiation, i.e. by M3's Kadison content — exactly vdW's own hypothesis
-- accounting for invariance).
import RadicalRelativity.Necessity.ThetaCocycle

-- M2 necessity core, eighth unit (LEDGER 2.7 core lemma): continuous one-parameter
-- semigroups in a real Banach algebra are exponentials, with a unique generator —
-- the classical integral-regularization argument (geometric-series unit, FTC-2
-- differentiability upgrade, multiplicative derivative law, ODE kill) built from
-- scratch; Mathlib has no one-parameter-group theory. This is the engine that
-- discharges the Aczel axiom in the next unit.
import RadicalRelativity.Necessity.OneParameter

-- M2 necessity core, ninth unit (LEDGER 2.6 instantiation data): the exponential
-- diagonal family aOf r = diag(exp r_i) and the standard frame — the semigroup
-- law, positive definiteness, effect-ness on the negative orthant, the frame
-- decomposition, and frame commutation; product-independent matrix bookkeeping.
import RadicalRelativity.Necessity.DiagonalFamily

-- M2 necessity core, tenth unit (LEDGER 2.6, chi part 1): the comparison character
-- on the diagonal family — base-point congruence, the value law
-- a(r) sp a(r') = a(r+r'), chi(0) = 1 through theta_base_one, and the orthant
-- cocycle Theta_{a(r+r')} = Theta_{a(r)} compose Theta_{a(r')} (conditional on
-- the M3 Jordan-preservation field, per vdW's own accounting).
import RadicalRelativity.Necessity.Chi

-- The concrete ComparisonSetup instance on H_N(C): jordanBilin, the machine-checked
-- FK/vdW compatibility bridge (operator commutation = matrix commutation, via the
-- quarter identity [L_a,L_b]y = (1/4)[[a,b],y]), the span-extended vdW 5.5, and
-- thetaNorm (Theta made total by 2.3-normalization); the only remaining field
-- hypothesis is ThetaPreservesJordan (= milestone M3).
import RadicalRelativity.Necessity.ComparisonInstance

-- chi-tilde extended to all of R^n: thetaUnit (the comparison map as a unit of
-- the endomorphism algebra, total in r), the units-level orthant cocycle and
-- abelian image, representative-freedom of Theta_s Theta_t^{-1} (the paper's
-- well-definedness argument), and chiTilde r := thetaUnit(r inf 0) *
-- thetaUnit(r inf 0 - r)^{-1} with chiTilde_add/zero/of_nonpos.
import RadicalRelativity.Necessity.ChiExtension

-- Exact paper-facing S1--S7 and product-conclusion statement boundary.  This
-- freezes the target signature; it does not claim the classification is proved.
import RadicalRelativity.PaperA.Statement

-- Persisted statement-fidelity pins for the audit harness.  Named theorems (not
-- anonymous `example`s) so the axiom census in AxiomAudit.lean visits them: a
-- `sorry` or stray axiom substituted for any pin's direct proof fails the census.
import RadicalRelativity.PaperA.AuditPins
