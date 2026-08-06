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

-- Vendored csd-lean4 Wigner-rigidity island (Apache 2.0, pinned; see
-- RadicalRelativity/Vendor/VENDOR.md): the exact import closure of
-- `Projectivization.wigner_rigidity` -- every transition-probability-preserving
-- self-map of CP^{N-1} is induced by a unitary or an antiunitary.  This is the
-- M3 rigidity input; it is TRACKED (in the census and the frozen manifest), so
-- its axiom closure is audited alongside first-party development.
import RadicalRelativity.Vendor.Wigner.WignerRigidity

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

-- The analytic half of lem:homomorphism on H_n(C): the S2 continuity ladder
-- (sp -> spPos -> seqLeftMul -> theta via the explicit diagonal Q-inverse),
-- line-continuity of chi-tilde, and multiParameter_eq_exp giving the LINEAR
-- differential dChi with chiTilde r = exp (dChi r) -- linearity/continuity of
-- the abstract dChiAdd fields PROVED here, not imported.
import RadicalRelativity.Necessity.ChiContinuity

-- The concrete CoalescenceSetup on H_N(C): the FK simultaneous-diagonalization
-- import replaced by corner-projection matrix algebra (q absorbs J2(q), so
-- scalar-on-corner elements commute), a(r) scalar on coalesced corners, and
-- block_mem_J2 by pure ring algebra (qx + xq = 2x with q idempotent gives
-- qxq = x). Only cited field in the combined structure: Theta_jordan (M3).
import RadicalRelativity.Necessity.CoalescenceInstance

-- Differentiated coalescence in the STRONG pointwise form: when r_i = r_j the
-- differential dChi(r) annihilates the Peirce-2 corner (chiTilde fixes corners
-- at both canonical exponents; exp(t . dChi r) x = x differentiates to
-- dChi(r) x = 0). Any block compression rho then satisfies the abstract
-- DiagonalHomSetup.coalescence_diff field.
import RadicalRelativity.Necessity.CoalescenceDiff

-- Theta is an order-unit-norm isometry (unital order-iso transports the
-- defining interval set verbatim), hence so are thetaUnit, its inverse, and
-- chiTilde -- the isometry input for the skewness of dChi with no trace
-- preservation or compactness anywhere.
import RadicalRelativity.Necessity.ThetaIsometry

-- Block invariance: corner membership = the Jordan eigenrelation q.x = x;
-- Theta, its inverse, and chiTilde preserve every corner (fixing q + hjord);
-- differentiating gives dChi_preserves_corner. With dChi_kills_corner this
-- completes the differential-face geometry of dChi.
import RadicalRelativity.Necessity.BlockInvariance

-- The off-diagonal block model: blockHerm i j z = z E_ij + conj z E_ji, the
-- square law x.x = |z|^2 (p_i + p_j), and the support characterization (the
-- Peirce eigenrelations force x = blockHerm i j x_ij) -- the concrete V_ij
-- coordinates for the stabilizer coupling.
import RadicalRelativity.Necessity.BlockModel

-- Theta transports blocks isometrically: blockHerm satisfies the Peirce
-- relations, Theta preserves them (M3 + frame-fixing), and the square law on
-- both sides of Theta(x.x) = Theta x . Theta x forces |w| = |z| -- a Euclidean
-- isometry on every off-diagonal block with no norm imports.
import RadicalRelativity.Necessity.BlockTransport

-- chi-tilde transports blocks isometrically at EVERY parameter: the inverse
-- factor by inverse-Jordan transport + forward-isometry-at-image, the
-- composite by chaining the two Theta factors.
import RadicalRelativity.Necessity.BlockChi

-- prop:isotropy on H_n(C): the block generator is skew -- differentiate the
-- constant function t -> |entry of chiTilde(t.r)(blockHerm z)|^2 at t = 0.
-- One-variable calculus; no compactness, no invariant measure.
import RadicalRelativity.Necessity.BlockSkew

-- The concrete DiagonalHomSetup on H_N(C) and the PRODUCED StabilizerCoupling:
-- Stab = the block-skew submodule (dChi lands in it by prop:isotropy), rho =
-- the L2 block compression (zero on diagonal pairs), coalescence_diff from
-- dChi_kills_corner through the embedding; toStabilizerCoupling then proves
-- the coupling rho_ij(dChi(r)) = (r_i - r_j) . T_ij on the concrete carrier.
import RadicalRelativity.Necessity.StabilizerInstance

-- Phase cocycle, part 1: the 2x2 skew classification (skew R-linear maps on C
-- are multiplication by it) and the cross-block product formula
-- blockHerm i j z . blockHerm j k v = (1/2) blockHerm i k (zv).  Inputs to the
-- Leibniz rule for the entry maps of dChi and hence the cocycle t_ik = t_ij + t_jk.
import RadicalRelativity.Necessity.PhaseCocycle

-- dChi(r) is a Jordan derivation: chiTilde is a Jordan automorphism at every
-- parameter (forward thetaNorm_jordan + inverse thetaNorm_symm_jordan through
-- the two-factor definition), and the Leibniz rule follows by differentiating
-- at t = 0 ENTRYWISE in C -- scalar product/sum rules only, sidestepping the
-- operator-topology diamond on nested continuous-linear-map spaces.
import RadicalRelativity.Necessity.JordanDerivation

-- The phase anchor (u6d, closing LEDGER 2.6): entry maps of dChi are
-- multiplication by i*t_ij (skew classification), the Leibniz rule across
-- blocks gives the cocycle t_ik = t_ij + t_jk, anchoring at i0 gives the
-- character matrix, and complex_perFrame_rho FIRES on the produced coupling:
-- a single per-frame parameter t_F with rho_ij(dChi(r)) = t_F(r_i - r_j) J.
import RadicalRelativity.Necessity.PhaseAnchor

-- prop:singular WIRED (LEDGER 2.9, closing M2): the positive-definite effects
-- are dense in the effect interval (boundary sequence a + (1/(k+1))(1-a) -> a),
-- and prop_singular extends any agreement of two S1-S7+S2 products on
-- positive-definite effects to ALL effects.
import RadicalRelativity.Necessity.SingularExtension

-- M3 bridge layer part 1: the projection order (absorption q <= p iff qp = q),
-- rank-one projections, and the equivalence "atom of the projection order =
-- rank-one projection".  Atomicity is purely order-theoretic, so any unital
-- order-automorphism transports rank-one projections to rank-one projections.
import RadicalRelativity.Necessity.ProjectionOrder

-- M3 bridge layer part 2a: the Busch-Gudder strength function
-- Str(p, a) = sup {t | t.p <= a}, built from the ORDER and the real scalar
-- action alone -- hence preserved by every linear order-isomorphism
-- (strength_map).  This is the mechanism that converts order data into the
-- metric datum Wigner rigidity consumes.
import RadicalRelativity.Necessity.Strength

-- M3 bridge layer part 2b: the probe family probe(phi) = (1/2)(1 + phi phi*),
-- the transition probability tau = |<phi,psi>|^2 with 0 <= tau <= 1, the
-- witness-vector collapse probe(phi) . (2 psi - <phi,psi> phi) = psi (the
-- inverse computed without any inverse), and the FORWARD strength bound
-- Str(psi psi*, probe phi) <= (2 - tau)^{-1}.
import RadicalRelativity.Necessity.StrengthProbe

-- M3, final leg (3.2d): the TWO Jordan witnesses the Wigner dichotomy returns.
-- Unitary conjugation x -> U x U* preserves the symmetrized product (the U* U
-- cancellation), and transposition preserves it because reversing a product
-- leaves the SYMMETRIZED product fixed; the antiunitary branch is the
-- composite.  So whichever branch wigner_rigidity returns, the induced
-- order-automorphism satisfies PreservesJordan.
import RadicalRelativity.Necessity.JordanWitness

-- M3, final leg: RANK-ONE PROJECTIONS SPAN H_n(C) over R, so two R-linear maps
-- agreeing on them are equal.  Proved WITHOUT the spectral theorem: the
-- vendored trace inner product pairs y against a rank-one as the quadratic
-- form, so a y orthogonal to every rank-one has vanishing quadratic form,
-- whence 0 <= y and y <= 0.  This is what upgrades the Wigner output ("acts as
-- a unitary/antiunitary on rank-ones") to an identity of maps.
import RadicalRelativity.Necessity.RankOneSpan

-- Exact paper-facing S1--S7 and product-conclusion statement boundary.  This
-- freezes the target signature; it does not claim the classification is proved.
import RadicalRelativity.PaperA.Statement

-- Persisted statement-fidelity pins for the audit harness.  Named theorems (not
-- anonymous `example`s) so the axiom census in AxiomAudit.lean visits them: a
-- `sorry` or stray axiom substituted for any pin's direct proof fails the census.
import RadicalRelativity.PaperA.AuditPins
