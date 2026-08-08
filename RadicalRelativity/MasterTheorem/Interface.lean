/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.LocalTomography
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — the abstract interface

Foundation module for the machine-checked formalization of the master theorem of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`, `mthm:master`).

**Master theorem (`mthm:master`).** On a finite-dimensional simple Euclidean Jordan
algebra of rank `n ≥ 3`, every norm-continuous S1–S7 sequential product is the
Lüders product on the real, quaternionic, and exceptional types, and equals
`a^{1/2+it} b a^{1/2-it}` for one global real `t` on the complex type `Hₙ(ℂ)`.

The author's mandate: *Lean is to make sure everything passes machine analysis, not
just LLM non-deterministic checking*. What this tree delivers is the **conditional
dependency skeleton** of the paper's proof: an abstract interface whose fields carry
the cited imports, with everything downstream machine-checked `sorry`-free and with
**zero custom axiom declarations** (the capstone `master_chain` closes over Lean core
only). It is NOT a formalization of the paper theorem itself — see the scope-honesty
notes below and `PLAN.md` §1–§2.

## The two faces of the interface

The proof has two seams, and this module supplies the object each downstream lane
consumes:

1. **`ComparisonSetup`** — the *comparison-map face*. An abstract carrier `J` with a
   commutative unital Jordan product, a frame, a `nonneg` predicate, and van de
   Wetering's comparison map `Θ_a` together with its cited properties carried as
   **structure fields** (`vdW` Prop 5.3 unital linear order iso; the van Imhoff–Roelands
   Jordan-automorphism conclusion `Θ_jordan`; Prop 5.5 fixing `Θ_fix`; Prop 5.7 cocycle).
   Consumed by `Coalescence`, `DiagonalHom`. **Scope honesty:** this interface does NOT
   encode S1–S7, the Jordan identity, formal reality, or that `nonneg` is the cone of
   squares — it begins *downstream* of the paper's order-unit-space axioms, at the
   comparison map. So its fields are *cited imported hypotheses*, audited by reading the
   structure; `ComparisonSetup.jordanAuto` simply projects `Θ_jordan` (the paper's
   `prop:theta` conclusion). See `PLAN.md` §2 for the located-hypothesis ledger.

2. **`StabilizerCoupling`** — the *differential face*. The output of the Lie
   differential reduction (`lem:homomorphism`): the frame-stabilizer Lie algebra
   `Stab`, its block representations `ρ_{ij}` (valued in `𝔰𝔬(V)`), the differential
   `dχ : ℝⁿ → Stab`, and the coupling `ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}`
   (`lem:homomorphism`). Consumed by the four typewise `Branches` lanes.

`DiagonalHom` produces a `StabilizerCoupling` from a `DiagonalHomSetup` — the
comparison face plus the *differential-face fields* (`ρ`, `dχAdd`, `dχAdd_cont`,
`coalescence_diff`; the analytic differentiation of `Θ` that yields them is the paper's,
not Lean's). Its differential `dχ` comes from `lieHom_smooth`, a **proved `def`**
(continuous-additive ⟹ ℝ-linear, `AddMonoidHom.toRealLinearMap`; continuity carried as
the cited `DiagonalHomSetup.dχAdd_cont` field) — not an axiom. What the constructor
*proves* is the coupling normal form from those fields.

## The axiom ledger (full statement/citation table in `PLAN.md`)

**This foundation module declares ZERO custom axioms.** The van Imhoff–Roelands
content that was formerly the global `axiom vanImhoffRoelands` is now the
`ComparisonSetup.Θ_jordan` **field** (a cited hypothesis scoped to the instances a
caller builds), because as a global axiom over the weak `ComparisonSetup` interface it
was *false* — it asserted the source theorem for structures encoding no JB-algebra. So
`#print axioms` on this module's results shows only Lean core axioms — as it does on
every result in the tree: **no module of `MasterTheorem/` declares any custom axiom.**
The remaining genuinely-classical inputs live where a reviewer can enumerate them
(full ledger in `PLAN.md` §2):

* the continuous-additive-to-linear upgrade (`DiagonalHom.lieHom_smooth`) is a
  **proved** `def` via Mathlib's `AddMonoidHom.toRealLinearMap`; the Cartan-smoothness
  content survives only as the cited continuity field `DiagonalHomSetup.dχAdd_cont`;
* uniqueness of continuous characters of `ℝ` is **proved**
  (`Globalization.real_character_unique`);
* the Yokota `Spin(8)`-triality faithfulness (Thm 2.7.1 + 1.16.2) enters as the cited
  hypothesis field `IsAlbertModel.block_injective` in `Branches/Albert`.

The **Faraut–Korányi** Peirce / frame-conjugacy facts likewise enter as interface
fields (`ComparisonSetup.frame_opCommute`, `CoalescenceSetup.simDiag_opCommute`),
documented with their FK citation — never as free-standing axioms.

The vdW comparison propositions (5.2/5.3/5.5/5.7, Prop 4.20, EJA-appendix
compatibility bridge) are **not** free-standing axioms: they are `ComparisonSetup`
fields, so a reviewer enumerates them by reading the structure. `#print axioms` on
any downstream theorem shows Lean core only — a syntactic-closure figure, not a
faithfulness certificate; the field lists are the real import ledger.

## Naming convention (read before quoting any theorem name)

Theorem names in this tree are the **paper's lane labels** (`real_luders`,
`albert_luders`, `master_chain`, …), kept aligned with the manuscript for
cross-referencing. The Lean *content* of every declaration is exactly its **type** —
e.g. `real_luders : S.T i j = 0` states the vanishing of a block generator, and the
passage from `T = 0` to "the product is Lüders" is the paper's normal-form reading,
not restated in Lean. When in doubt, quote the type, never the name.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*.
* van de Wetering, arXiv:1803.08453 (`Wetering2018three`), §5 + EJA appendix.
* van Imhoff–Roelands, arXiv:1904.09278, Cor. 2.5 / Prop. 2.6.
* Faraut–Korányi, *Analysis on Symmetric Cones*, 1994 (Peirce theory, Ch. IV).
* Yokota, *Exceptional Lie Groups*, arXiv:0902.0431, Thm 2.7.1 + 1.16.2.
-/

noncomputable section

open scoped InnerProductSpace
open LocalTomography

namespace MasterTheorem

/-! ## Peirce/block multiplicity `d`

The off-diagonal Peirce multiplicity `d = dim V_{ij}` classifies the branch:
`1, 2, 4, 8` for `Hₙ(ℝ), Hₙ(ℂ), Hₙ(ℍ), H₃(𝕆)` (Faraut–Korányi). Redefined locally
(rather than imported from `TwistNormalForm`) to keep the master-chain foundation
independent of the Part-II selection development. (Historical note: until
2026-08-04 `TwistNormalForm` declared the `bgw_canonical_composite` axiom, which
this isolation kept out of the closure; that axiom is now a proved-table
definition, and the isolation is retained as layering hygiene.) -/

/-- Off-diagonal Peirce multiplicity `d = dim V_{ij}` of a simple EJA type
    (Faraut–Korányi). -/
def blockDim : EJAType → ℕ
  | .real _    => 1
  | .complex _ => 2
  | .quatern _ => 4
  | .albert    => 8
  | .spin n    => n - 2

@[simp] theorem blockDim_real (n : ℕ) : blockDim (.real n) = 1 := rfl
@[simp] theorem blockDim_complex (n : ℕ) : blockDim (.complex n) = 2 := rfl
@[simp] theorem blockDim_quatern (n : ℕ) : blockDim (.quatern n) = 4 := rfl
@[simp] theorem blockDim_albert : blockDim .albert = 8 := rfl

/-- **Among the matrix types (spin factors excluded), `blockDim = 2` characterizes the
    complex type** — the arithmetic shadow of the dial dichotomy: only a two-dimensional
    block carries a one-dimensional `𝔰𝔬(V_{ij})`, the room for exactly one rotation
    generator. Both directions are proved (`1, 4, 8 ≠ 2` by computation). Spin factors
    are excluded honestly: `blockDim (.spin 4) = 2` as well, and the paper handles the
    rank-two spin family separately. (This strengthens the former one-directional
    `blockDim_complex_unique_dial`, whose name promised a uniqueness its statement did
    not contain — adversarial-review fix, 2026-07-15.) -/
theorem blockDim_eq_two_iff_complex (t : EJAType) (hspin : ∀ n, t ≠ .spin n) :
    blockDim t = 2 ↔ ∃ n, t = .complex n := by
  constructor
  · intro h2
    cases t with
    | real n => simp [blockDim] at h2
    | complex n => exact ⟨n, rfl⟩
    | quatern n => simp [blockDim] at h2
    | albert => simp [blockDim] at h2
    | spin n => exact absurd rfl (hspin n)
  · rintro ⟨n, rfl⟩; rfl

/-! ## Operator commutation on an abstract Jordan algebra

For the multiplication operator `T_x(y) = x ∘ y`, elements *operator commute* when
`[T_x, T_y] = 0` (Faraut–Korányi). This is the notion the compatibility bridge
(`vdW` EJA appendix) equates with standard-product compatibility, and the hypothesis
of the `Θ_fix` field below. -/

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- The Jordan multiplication operator `T_x(y) = x ∘ y`. -/
def mulOp (jordan : J →ₗ[ℝ] J →ₗ[ℝ] J) (x : J) : J →ₗ[ℝ] J := jordan x

/-- **Operator commutation** `[T_x, T_y] = 0` (Faraut–Korányi): `x` and `y` operator
    commute iff their Jordan multiplication operators commute. -/
def OpCommute (jordan : J →ₗ[ℝ] J →ₗ[ℝ] J) (x y : J) : Prop :=
  (mulOp jordan x).comp (mulOp jordan y) = (mulOp jordan y).comp (mulOp jordan x)

theorem OpCommute.symm {jordan : J →ₗ[ℝ] J →ₗ[ℝ] J} {x y : J}
    (h : OpCommute jordan x y) : OpCommute jordan y x := Eq.symm h

/-! ## The comparison-map face: `ComparisonSetup`

`ComparisonSetup J` bundles the paper's hypotheses on `J` together with the outputs
of the cited comparison machinery. Its **fields are the audit ledger** for the
imported vdW/FK facts; the van Imhoff–Roelands Jordan-automorphism conclusion is the
`Θ_jordan` field (a cited hypothesis, no global axiom), projected by `jordanAuto`. -/

/-- **The comparison-map interface** (`sec:machinery`). An abstract simple Euclidean
Jordan algebra `J` of rank `n ≥ 3` carrying a norm-continuous S1–S7 sequential
product, presented through van de Wetering's comparison map `Θ_a` and its cited
properties. A concrete simple EJA with a sequential product is *intended* to furnish
one of these — that instantiation is the paper's analytic work — and the
master-theorem chain consumes it.

**Concrete instances exist in this tree** (2026-08-05, superseding the earlier
docstring's "no concrete instance is constructed here"): `Necessity.comparisonSetupG`
(`Necessity/ComparisonInstanceGen.lean`) builds one on `H_N(𝕜)` for `𝕜 ∈ {ℝ, ℂ}` and
`Necessity.comparisonSetup` (`Necessity/ComparisonInstance.lean`) the ℂ specialization,
from an S1–S7 product with S2; every field is discharged by a machine-checked theorem
except `Θ_jordan`, which enters as the hypothesis `ThetaPreservesJordanG P` — itself
now discharged for both flagship rows (ℂ: `Necessity.KadisonDischarge`; ℝ:
`Necessity.RealKadison`). So the vacuity worry below is answered for the intended
algebras, not merely acknowledged.

**Vacuity honesty (adversarial review, 2026-07-15).** The field names carry the
*intended* semantics (frame, cone, invertibles); the fields themselves impose no
idempotency/orthogonality/simplicity conditions, and degenerate inhabitants exist
(e.g. `J = ℝ`, `p = 0`, `nonneg = Inv = fun _ => True`, `Θ = fun _ => 1`). Nothing
downstream claims otherwise: every theorem over this structure states exactly the
implication from these fields, and the *physical* content of the chain is as large as
the paper's analytic work that instantiates them on the intended EJAs — that is the
"conditional" in *conditional dependency skeleton*.

Field ledger (imported facts; cited inline):
* `jordan`, `e`, `jordan_comm`, `jordan_unit` — the Euclidean Jordan product and unit
  (the paper's `(J, ∘, e)`; `jordan_comm`/`jordan_unit` are the cheap correctness
  anchors — full formal reality / the Jordan identity are EJA data, cited FK, and are
  not needed by the chain, which consumes `Θ`).
* `p`, `frame_opCommute` — a Jordan frame `{p_i}` and the FK fact that each `p_i`,
  being diagonal in `F`, operator-commutes with every diagonal effect `a(r)`.
* `nonneg` — the symmetric cone `J⁺` (the order for the order-isomorphism property).
* `Inv`, `aOf`, `aOf_inv` — invertible effects and the diagonal family
  `a(r) = Σ_i e^{r_i} p_i` (invertible for every `r`, `vdW` Prop 4.20 / spectral).
* `Θ`, `Θ_unital`, `Θ_orderIso` — `vdW` **Prop 5.3**: for invertible `a`, the
  comparison map `Θ_a` is a unital linear order isomorphism with `L_a = Q_{√a} Θ_a`.
* `Θ_fix` — `vdW` **Prop 5.5** + EJA-appendix compatibility bridge: `Θ_a` fixes every
  `b` operator-commuting with `a`.
* `Θ_cocycle` — `vdW` **Prop 5.7**: on the commuting diagonal family the comparison
  maps compose, `Θ_{a(r+r')} = Θ_{a(r)} ∘ Θ_{a(r')}` (invariance of the reference
  Lüders product supplies the hypothesis; abelian image). -/
structure ComparisonSetup (J : Type*) [NormedAddCommGroup J] [InnerProductSpace ℝ J] where
  /-- The Euclidean Jordan product `x ∘ y`. -/
  jordan : J →ₗ[ℝ] J →ₗ[ℝ] J
  /-- The Jordan unit `e`. -/
  e : J
  /-- The Jordan product is commutative. -/
  jordan_comm : ∀ x y, jordan x y = jordan y x
  /-- `e` is a left (hence two-sided) unit. -/
  jordan_unit : ∀ x, jordan e x = x
  /-- The rank `n`. -/
  n : ℕ
  /-- Rank hypothesis of `mthm:master`. -/
  rank_ge : 3 ≤ n
  /-- A Jordan frame `{p_1, …, p_n}` (complete orthogonal system of primitive
      idempotents). -/
  p : Fin n → J
  /-- The symmetric cone `J⁺` (the order carrying the order-isomorphism property). -/
  nonneg : J → Prop
  /-- The invertible-effect predicate. -/
  Inv : J → Prop
  /-- The **invertible diagonal family** `a(r) = Σ_i e^{r_i} p_i`, `r ∈ ℝⁿ`. NOT a family
      of effects in general: for a coordinate `r_i > 0`, `e^{r_i} > 1`, so `a(r)` exceeds
      the unit; `a(r)` is an effect *exactly* on the negative orthant `r ≤ 0`. The
      comparison-map fields apply to it as an *invertible element* (`Inv`) — the scope the
      cited vdW propositions need — not as an effect. -/
  aOf : (Fin n → ℝ) → J
  /-- Each `a(r)` is invertible (`vdW` Prop 4.20 / spectral): carried as the imported
      hypothesis `Inv (aOf r)`, *not* the (false) claim that every `a(r)` is an effect. -/
  aOf_inv : ∀ r, Inv (aOf r)
  /-- van de Wetering's comparison map `Θ_a` (defined on invertible effects). -/
  Θ : J → (J ≃ₗ[ℝ] J)
  /-- `vdW` Prop 5.3: `Θ_a` is unital, `Θ_a(e) = e`. -/
  Θ_unital : ∀ a, Inv a → Θ a e = e
  /-- `vdW` Prop 5.3: `Θ_a` is an order isomorphism of the cone. -/
  Θ_orderIso : ∀ a, Inv a → ∀ x, nonneg x ↔ nonneg (Θ a x)
  /-- **van Imhoff–Roelands, Cor. 2.5 / Prop. 2.6** (arXiv:1904.09278), carried as a
      cited **hypothesis**: on the intended Euclidean/JB-algebra instance, applying vIR
      to the unital linear order isomorphism `Θ_a` (`Θ_unital` + `Θ_orderIso`, `vdW`
      Prop 5.3) yields that `Θ_a` preserves the Jordan product. **This interface does not
      encode the JB-algebra premises** (the Jordan identity, formal reality, the
      cone-of-squares reading of `nonneg`), so this field is the *imported conclusion* of
      vIR on the intended EJA instances — NOT a Lean transcription of vIR that would hold
      for an arbitrary `ComparisonSetup`. It replaces the former global `vanImhoffRoelands`
      axiom (which was false off genuine JB-algebras). Classical corroboration:
      Alfsen–Shultz, *Geometry of State Spaces*, Thm 2.80. -/
  Θ_jordan : ∀ a, Inv a → ∀ x y, Θ a (jordan x y) = jordan (Θ a x) (Θ a y)
  /-- `vdW` **Prop 5.5** + EJA-appendix compatibility bridge, in **span-extended** form:
      `Θ_a` fixes every `b ∈ J` (all of `J`, not only effects) operator-commuting with
      `a`. Prop 5.5 is stated at the effect level; the paper extends it to all of `J` by
      linearity (effects span `J`). Lean does not reprove that extension here, so this
      field carries the **span-extended strength as an imported hypothesis**, not the
      bare effect-level Prop 5.5. -/
  Θ_fix : ∀ a, Inv a → ∀ b, OpCommute jordan a b → Θ a b = b
  /-- FK: each frame idempotent operator-commutes with every diagonal effect. -/
  frame_opCommute : ∀ (r : Fin n → ℝ) (i : Fin n), OpCommute jordan (aOf r) (p i)
  /-- `vdW` Prop 5.7 (cocycle): the comparison maps of the commuting diagonal *effect*
      family compose additively in the exponent. Stated on the negative orthant
      `r, r' ≤ 0` (where `a(r), a(r')` are effects, exactly Prop 5.7's simple commuting
      invertible effects); `DiagonalHom` *proves* the extension to all of `ℝⁿ` via
      `χ̃(s − t) := Θ_s Θ_t⁻¹` (the paper's `lem:homomorphism`), so the field is not
      stronger than the source. -/
  Θ_cocycle : ∀ r r' : Fin n → ℝ, (∀ i, r i ≤ 0) → (∀ i, r' i ≤ 0) →
      Θ (aOf (r + r')) = (Θ (aOf r)).trans (Θ (aOf r'))

namespace ComparisonSetup

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- **`prop:theta` (assembly).** For invertible `a`, the comparison map `Θ_a` is a
Jordan automorphism of `J` — it preserves the Jordan product. This **projects the
`Θ_jordan` field**, which carries (as a cited hypothesis, *not* a global axiom) the
conclusion of applying van Imhoff–Roelands Cor. 2.5 / Prop. 2.6 to `Θ_a` on the intended
EJA instance — the paper's assembly step (`vdW` Prop 5.3 unital linear order iso,
upgraded by vIR, bypassing the Hilbert-space bicommutant step `vdW` Lemma 5.8). **No
custom axiom is used:** the vIR content is an interface field, so it is scoped to the
instances a caller actually builds, rather than a global `axiom` that would (falsely)
assert the source theorem for every `ComparisonSetup`, including ones encoding no
JB-algebra structure. -/
theorem jordanAuto (C : ComparisonSetup J) {a : J} (ha : C.Inv a) :
    ∀ x y, C.Θ a (C.jordan x y) = C.jordan (C.Θ a x) (C.Θ a y) :=
  C.Θ_jordan a ha

/-- **`lem:frame-fix` (first half, PROVED).** The comparison map of a diagonal effect
fixes each frame idempotent: `Θ_{a(r)}(p_i) = p_i`. Immediate from `Θ_fix` (`vdW`
Prop 5.5) and `frame_opCommute` (FK): each `p_i` operator-commutes with `a(r)`. -/
theorem frame_fixed (C : ComparisonSetup J) (r : Fin C.n → ℝ) (i : Fin C.n) :
    C.Θ (C.aOf r) (C.p i) = C.p i :=
  C.Θ_fix (C.aOf r) (C.aOf_inv r) (C.p i) (C.frame_opCommute r i)

end ComparisonSetup

/-! ## The differential face: `StabilizerCoupling`

The output of the Lie differential reduction `lem:homomorphism`: after `DiagonalHom`
produces the smooth character `χ : ℝⁿ → Stab(F)°` and its real-linear differential
`dχ`, the branch lanes work entirely with the linear-algebra data below. All Peirce
blocks `V_{ij}` are modelled by a single real inner product space `V` (they are
mutually isomorphic as inner product spaces; the *representations* `ρ_{ij}` differ,
which is exactly the `8_v/8_s/8_c` triality distinction on the exceptional block). -/

variable (n : ℕ) (Stab : Type*) [AddCommGroup Stab] [Module ℝ Stab]
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **`lem:homomorphism` (differential form).** The frame-stabilizer coupling consumed
by the four typewise branches: the block representations `ρ_{ij} : 𝔰𝔱𝔞𝔟(F) → 𝔰𝔬(V)`,
the real-linear differential `dχ : ℝⁿ → 𝔰𝔱𝔞𝔟(F)`, and the coupling identity
`ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}` (`lem:homomorphism`). `ρ_skew` records that the
stabilizer acts orthogonally on each block (`T_{ij} ∈ 𝔰𝔬(V_{ij})`, `prop:isotropy`),
so `ρ_{ij}(ξ)` is skew for the trace inner product. -/
structure StabilizerCoupling where
  /-- Block representation `ρ_{ij} : 𝔰𝔱𝔞𝔟(F) → End(V_{ij})`. -/
  ρ : Fin n → Fin n → Stab →ₗ[ℝ] (V →ₗ[ℝ] V)
  /-- `ρ_{ij}(ξ) ∈ 𝔰𝔬(V)`: the stabilizer acts by skew-adjoint operators
      (`prop:isotropy`). -/
  ρ_skew : ∀ i j (ξ : Stab) (x : V), ⟪(ρ i j ξ) x, x⟫_ℝ = 0
  /-- The real-linear differential `dχ : ℝⁿ → 𝔰𝔱𝔞𝔟(F)` (`lem:homomorphism`;
      real-linearity is the Lie smoothness of `χ`). -/
  dχ : (Fin n → ℝ) →ₗ[ℝ] Stab
  /-- The single per-block twist generator `T_{ij}` (`lem:homomorphism`). -/
  T : Fin n → Fin n → (V →ₗ[ℝ] V)
  /-- **The coupling** `ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}` (`lem:homomorphism`): the
      block twist is a single stabilizer element read through `ρ_{ij}`, pinned by
      coalescence to the difference `r_i − r_j`. -/
  coupling : ∀ i j (r : Fin n → ℝ), ρ i j (dχ r) = (r i - r j) • T i j
  /-- Rank hypothesis of `mthm:master` (supplies the third index in the branches). -/
  rank_ge : 3 ≤ n

namespace StabilizerCoupling

variable {n Stab V} [AddCommGroup Stab] [Module ℝ Stab]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Coalescence at the differential level (PROVED).** On the coalescence hyperplane
`r_i = r_j` the block coupling vanishes: `ρ_{ij}(dχ(r)) = 0`. This is the differential
shadow of `lem:coalescence` (the twist is `∝ (r_i − r_j)`), and is what makes the
`r_l`-coefficient (`l ≠ i,j`) drop out in every typewise branch. -/
theorem coalescence (S : StabilizerCoupling n Stab V) (i j : Fin n)
    (r : Fin n → ℝ) (h : r i = r j) : S.ρ i j (S.dχ r) = 0 := by
  rw [S.coupling, h, sub_self, zero_smul]

/-- **Twist recovery (PROVED).** From the coupling with any `r` for which
`r_i − r_j = 1`, the twist generator is `T_{ij} = ρ_{ij}(dχ(r))`. Lets a branch pass
between "kill `dχ`" and "kill `T_{ij}`". -/
theorem T_eq (S : StabilizerCoupling n Stab V) (i j : Fin n)
    (r : Fin n → ℝ) (h : r i - r j = 1) : S.T i j = S.ρ i j (S.dχ r) := by
  rw [S.coupling, h, one_smul]

/-- **Faithful-kill reduction (PROVED).** Once the differential vanishes, `dχ = 0`,
every *off-diagonal* twist `T_{ij}` (`i ≠ j`) is zero, so the block action is Lüders.
This is the tail of the exceptional (and real) branch: the faithfulness of the
triality representations of the simple `𝔰𝔭𝔦𝔫(8)` (Yokota, ledgered in the `Branches`
lane) forces `dχ = 0`, and this lemma reads off `T_{ij} = 0` from there. -/
theorem faithful_kill (S : StabilizerCoupling n Stab V)
    (hdχ : S.dχ = 0) {i j : Fin n} (hij : i ≠ j) : S.T i j = 0 := by
  have hr : (Pi.single i 1 : Fin n → ℝ) i - (Pi.single i 1 : Fin n → ℝ) j = 1 := by
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), sub_zero]
  rw [S.T_eq i j (Pi.single i 1) hr, hdχ]
  simp

end StabilizerCoupling

end MasterTheorem
