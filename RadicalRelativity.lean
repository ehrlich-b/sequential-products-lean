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

-- Exact paper-facing S1--S7 and product-conclusion statement boundary.  This
-- freezes the target signature; it does not claim the classification is proved.
import RadicalRelativity.PaperA.Statement

-- Persisted statement-fidelity pins for the audit harness.  Named theorems (not
-- anonymous `example`s) so the axiom census in AxiomAudit.lean visits them: a
-- `sorry` or stray axiom substituted for any pin's direct proof fails the census.
import RadicalRelativity.PaperA.AuditPins
