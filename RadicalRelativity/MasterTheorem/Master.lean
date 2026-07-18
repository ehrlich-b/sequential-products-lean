/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.DiagonalHom
import RadicalRelativity.MasterTheorem.Branches.Real
import RadicalRelativity.MasterTheorem.Branches.Quaternionic
import RadicalRelativity.MasterTheorem.Branches.Albert
import RadicalRelativity.MasterTheorem.Branches.Complex
import RadicalRelativity.MasterTheorem.Globalization
import RadicalRelativity.MasterTheorem.Adapter
import Mathlib.Topology.Basic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem — the dependency-skeleton assembly (`master_chain`)

The capstone module. Its theorem `master_chain` is the machine-checked **logical
dependency-skeleton** of the master theorem of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`, `mthm:master`).

It records that the typewise kill lemmas and the complex globalization **compose** over the
produced frame-stabilizer couplings (`DiagonalHomSetup.toStabilizerCoupling`, not free
hypotheses), so `#print axioms` audits the whole chain. It is emphatically **not** the paper
theorem itself: it states no effect algebra, no S1–S7 operation, and no product equality —
see `master_chain`'s own docstring (adversarial review §5.7) for the explicit "does not
state" list. The paper's analytic content is carried through the interface fields and the
prose, not re-proved here.

## The whole-chain axiom audit — ZERO custom axioms

After the repairs of adversarial review §5.2–§5.4, `#print axioms master_chain` is exactly
Lean's three core axioms: `propext`, `Classical.choice`, `Quot.sound` — **no custom
axiom remains** (`Classical.choice` is itself a classical axiom of Lean's core; "zero"
counts custom declarations). Every classical import is now either a proved theorem or an auditable
structure field / hypothesis a reviewer reads off the signature:

* **A2 (Cartan smoothness)** — a proved `def` `lieHom_smooth` (a *continuous* additive map
  is ℝ-linear, `AddMonoidHom.toRealLinearMap`); the smoothness content is the
  `DiagonalHomSetup.dχAdd_cont` continuity **field**.
* **A3 (real characters)** — proved as `Globalization.real_character_unique` (differentiate
  the character at a point — no `2π` ambiguity).
* **A1 (van Imhoff–Roelands / vdW comparison)** — carried as the
  `ComparisonSetup.Θ_jordan` **field** (a cited hypothesis; `jordanAuto`/`block_preserved`
  project it), after the interface lane's §5.4 repair.
* **A4 (Yokota `Spin(8)`-triality faithfulness)** — carried as the
  `IsAlbertModel.block_injective` **field** (the injectivity of each block rep, a cited
  interface assumption), after the Albert lane's §5.3 repair; `albert_luders` consumes it.

The remaining van de Wetering / Faraut–Korányi comparison propositions are likewise
`ComparisonSetup`/`CoalescenceSetup` structure **fields**. The auditor reads the entire
classical-import surface off the field lists; `#print axioms` shows only Lean core.

## Scope (rank two is a separate boundary; see `RankTwo.lean`)

`master_chain` is the rank `n ≥ 3` skeleton (the `rank_ge` field). The rank-two boundary —
the rigid real qubit versus the explicit frame-dependent `τ(F)` family for the complex qubit
— is the separate necessity-only development in `RadicalRelativity/MasterTheorem/RankTwo.lean`
(`prop:n2-necessity`, `thm:qubit-boundary`), which is **not** imported here and carries its
own concrete `M₂(ℂ)` proofs. No exhaustiveness claim is made at rank two.

## `prop_singular` — a STANDALONE lemma (not invoked by the capstone)

`prop_singular` proves the honest kernel of `prop:singular`: two continuous maps agreeing on
a dense set agree everywhere (`Set.EqOn.closure`). This is the extension mechanism the paper
uses to pass from invertible to all effects (`a_ε = (1−ε)a + εe → a`, S2-continuity), with
the continuity and density carried as explicit disclosed hypotheses. It is a **standalone
generic lemma** — it is **not** applied to any product inside `master_chain`, which lives on
the interface data and states nothing about singular effects.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*,
  `mthm:master`, `prop:singular`, `lem:frame-fix`.
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

/-! ## `prop:singular` — the S2 continuity/density extension kernel -/

/-- **`prop:singular` (S2 extension, PROVED kernel).** Two continuous maps that agree on a
dense set agree everywhere. This is the mathematical content of `prop:singular`: the
sequential product is determined on the invertible effects (the typewise theorems), and
every effect is a limit of invertibles (`a_ε = (1−ε)a + εe → a`, S2-continuity), so the
Lüders / single-twist form extends from the invertibles to all effects.

The S2-continuity (`hf`, `hg`) and the density of the invertible effects (`hdense`) are the
explicit disclosed hypotheses; the extension itself is proved (`Set.EqOn.closure`). Stated
over abstract spaces `X` (effects) and `W` (product actions). **Standalone**: this lemma is
the extension *mechanism*; it is not invoked by `master_chain` (which carries no product
object), and makes no claim about any concrete sequential product. -/
theorem prop_singular {X W : Type*} [TopologicalSpace X] [TopologicalSpace W] [T2Space W]
    {Inv : Set X} (hdense : Dense Inv) (Lref Lunknown : X → W)
    (hf : Continuous Lref) (hg : Continuous Lunknown)
    (hagree : Set.EqOn Lref Lunknown Inv) : Lref = Lunknown := by
  funext a
  exact hagree.closure hf hg (hdense.closure_eq ▸ Set.mem_univ a)

/-! ## Per-type building blocks (each over the PRODUCED coupling)

Each lemma runs its typewise branch on `D.toStabilizerCoupling` — the coupling *produced*
by the Lie-differential reduction from the comparison-map face — so the assembly never
takes the `StabilizerCoupling` as a free hypothesis. -/

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- **`lem:frame-fix` certificate (A1).** For the produced setup, `Θ_{a(r)}` preserves each
Peirce block `V_{ij}`. This is the frame-fixing that makes the differential face legitimate
(`prop:theta` ⟹ block-preservation), and it is the step through which the master theorem
depends on `vanImhoffRoelands` (A1). -/
theorem frame_block_fixed {Stab : Type*} [NormedAddCommGroup Stab] [NormedSpace ℝ Stab]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : DiagonalHomSetup J Stab V) (r : Fin D.n → ℝ) {i j : Fin D.n} {x : J}
    (hx : (D.toCoalescenceSetup.toComparisonSetup).isBlock i j x) :
    (D.toCoalescenceSetup.toComparisonSetup).isBlock i j
      ((D.toCoalescenceSetup.toComparisonSetup).Θ ((D.toCoalescenceSetup.toComparisonSetup).aOf r) x) :=
  block_preserved _ r hx

/-- **Real branch over the produced coupling (`prop:real`).** -/
theorem luders_real_produced {Stab : Type*} [NormedAddCommGroup Stab] [NormedSpace ℝ Stab]
    (D : DiagonalHomSetup J Stab ℝ) {i j : Fin D.n} (hij : i ≠ j) :
    (D.toStabilizerCoupling).T i j = 0 :=
  real_luders _ hij

/-- **Quaternionic branch over the produced coupling (`thm:quaternionic`).** The two-slot
model form of `ρ_{ij}` (`hρ`, with imaginary coordinates `im`) is the explicit typewise
data; `Z(ℍ) ∩ Im ℍ = 0` and the `n ≥ 3` spectator index do the rest. -/
theorem luders_quaternionic_produced {Stab : Type*} [NormedAddCommGroup Stab] [NormedSpace ℝ Stab]
    (D : DiagonalHomSetup J Stab (Quaternion ℝ))
    (im : Stab → Fin D.n → Quaternion ℝ)
    (himag : ∀ (ξ : Stab) (k : Fin D.n), (im ξ k).re = 0)
    (hρ : ∀ (i j : Fin D.n) (ξ : Stab) (x : Quaternion ℝ),
      (D.toStabilizerCoupling).ρ i j ξ x = im ξ i * x - x * im ξ j)
    {i j : Fin D.n} (hij : i ≠ j) : (D.toStabilizerCoupling).T i j = 0 :=
  Quaternionic.quaternionic_luders _ im himag hρ hij

/-- **Exceptional branch over the produced coupling (`thm:albert`).** The rank is exactly
`3` (`hn3`) and the coupling models `H₃(𝕆)` (`IsAlbertModel`); the Yokota triality axiom
(A4) supplies faithfulness. -/
theorem luders_albert_produced {Stab : Type*} [NormedAddCommGroup Stab] [NormedSpace ℝ Stab]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : DiagonalHomSetup J Stab V) (hn3 : D.n = 3)
    (hAlb : IsAlbertModel (hn3 ▸ D.toStabilizerCoupling))
    {i j : Fin 3} (hij : i ≠ j) : (hn3 ▸ D.toStabilizerCoupling).T i j = 0 :=
  albert_luders _ hAlb hij

/-- **Complex branch over the produced coupling (`thm:complex`, per-frame).** The torus
model (`J ≠ 0`, character matrix `c`) collapses the per-pair constants to a single per-frame
`t_F`. -/
theorem complex_perFrame_produced {Stab : Type*} [NormedAddCommGroup Stab] [NormedSpace ℝ Stab]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : DiagonalHomSetup J Stab V) (Jc : V →ₗ[ℝ] V) (hJc : Jc ≠ 0)
    (c : Fin D.n → Fin D.n → ℝ)
    (hmodel : ∀ i j (r : Fin D.n → ℝ),
      (D.toStabilizerCoupling).ρ i j ((D.toStabilizerCoupling).dχ r)
        = ((∑ l, c i l * r l) - (∑ l, c j l * r l)) • Jc) :
    ∃ tF : ℝ, ∀ i j (r : Fin D.n → ℝ),
      (D.toStabilizerCoupling).ρ i j ((D.toStabilizerCoupling).dχ r) = (tF * (r i - r j)) • Jc :=
  complex_perFrame_rho _ Jc hJc c hmodel

/-! ## The master theorem -/

/-- **`master_chain` — the Lean dependency-skeleton of `mthm:master` (NOT the paper
theorem).** This theorem records that the typewise kill lemmas and the complex
globalization **compose** over the produced frame-stabilizer couplings. It is the
machine-checked *logical skeleton* of `mthm:master`, over the abstract interface
(`DiagonalHomSetup`, `StabilizerCoupling`) — **conditional** `T_{ij} = 0` and
per-frame/global-scalar conclusions — assembled so `#print axioms` audits the whole chain.

It quantifies over one produced coupling per simple type
(`D*.toStabilizerCoupling`), so no branch takes a free `StabilizerCoupling`. The five
conclusion lanes are **logically independent conditionals**: no conjunct's proof feeds
another's, "chain" names the dependency chain *within* each lane, and the four lanes'
model data are supplied simultaneously over one abstract `J` as a bookkeeping
convenience of the audit (on a genuine simple EJA only one lane's model data exists); for the
complex type the globalization family's reference member is pinned to the produced coupling
(`hanchor : Scfam F₀ = Dc.toStabilizerCoupling`). The conjuncts: (1) frame-fixing / block
preservation (`lem:frame-fix`; the A1 step); (2)–(4) `T_{ij} = 0` for real / quaternionic
(two-slot `im`/`hρh`) / exceptional (`IsAlbertModel`, `n = 3`); (5a) a per-frame `t_F` on
the produced complex coupling; (5b) one **global** `t` across frames (adapter
`complex_global_twist`, with `connected` = `lem:frame-connectivity` and `overlap` =
cross-coherence as disclosed located hypotheses).

**What `master_chain` does NOT state** (adversarial review §5.7 — it is a skeleton over
interface data, not the analytic theorem): it does not state that `J` is a simple EJA of a
particular coordinate type; that an operation satisfies S1–S7; that `L_a = Q_{√a}Θ_a`; that
`Θ_a = id`; that `a•b = Q_{√a}b`; that `a•b = a^{1/2+it} b a^{1/2−it}`; the result for all
(including singular) effects; nor any product equality. Those are the paper's analytic
content, carried through the `ComparisonSetup`/`DiagonalHomSetup` **fields** and the paper's
prose, not proved here. The four typewise setups are supplied simultaneously over one
abstract `J`, whereas the paper theorem is a case split on one concrete simple EJA; this
theorem is the *composition audit* of that case split, not the case split itself.
`prop_singular` (the S2 dense-agreement extension) is a **standalone** lemma above, **not**
invoked by this capstone.

`#print axioms master_chain` is the whole-chain ledger: after the §5.2–§5.4 repairs it is
**Lean core only** (`propext`, `Classical.choice`, `Quot.sound`) — no custom axiom. A2
is the proved `def` `lieHom_smooth`; A3 is `real_character_unique`; A1 is the
`ComparisonSetup.Θ_jordan` field; A4 is the `IsAlbertModel.block_injective` field. -/
theorem master_chain
    -- real type `Hₙ(ℝ)`: block space `V = ℝ` (`blockDim = 1`)
    {Sr : Type*} [NormedAddCommGroup Sr] [NormedSpace ℝ Sr] (Dr : DiagonalHomSetup J Sr ℝ)
    -- quaternionic type `Hₙ(ℍ)`: block space `V = ℍ`, two-slot model `im`/`hρ`
    {Sh : Type*} [NormedAddCommGroup Sh] [NormedSpace ℝ Sh] (Dh : DiagonalHomSetup J Sh (Quaternion ℝ))
    (imh : Sh → Fin Dh.n → Quaternion ℝ)
    (himagh : ∀ (ξ : Sh) (k : Fin Dh.n), (imh ξ k).re = 0)
    (hρh : ∀ (i j : Fin Dh.n) (ξ : Sh) (x : Quaternion ℝ),
      (Dh.toStabilizerCoupling).ρ i j ξ x = imh ξ i * x - x * imh ξ j)
    -- exceptional type `H₃(𝕆)`: `n = 3`, `IsAlbertModel`
    {Sa : Type*} [NormedAddCommGroup Sa] [NormedSpace ℝ Sa]
    {Va : Type*} [NormedAddCommGroup Va] [InnerProductSpace ℝ Va]
    (Da : DiagonalHomSetup J Sa Va) (hn3 : Da.n = 3)
    (hAlb : IsAlbertModel (hn3 ▸ Da.toStabilizerCoupling))
    -- complex type `Hₙ(ℂ)`: torus model `Jc ≠ 0`; produced representative `Dc`, and a
    -- per-frame family `Scfam` whose reference member `Scfam F₀` IS `Dc.toStabilizerCoupling`
    {Sc : Type*} [NormedAddCommGroup Sc] [NormedSpace ℝ Sc]
    {Vc : Type*} [NormedAddCommGroup Vc] [InnerProductSpace ℝ Vc]
    (Dc : DiagonalHomSetup J Sc Vc) (Jc : Vc →ₗ[ℝ] Vc) (hJc : Jc ≠ 0)
    {Frame : Type*} [Nonempty Frame] (F₀ : Frame)
    (Scfam : Frame → StabilizerCoupling Dc.n Sc Vc)
    (hanchor : Scfam F₀ = Dc.toStabilizerCoupling)
    (cfam : Frame → (Fin Dc.n → Fin Dc.n → ℝ))
    (hmodelfam : ∀ (F : Frame) i j (r : Fin Dc.n → ℝ),
      (Scfam F).ρ i j ((Scfam F).dχ r)
        = ((∑ l, cfam F i l * r l) - (∑ l, cfam F j l * r l)) • Jc)
    (Adj : Frame → Frame → Prop)
    (connected : ∀ F G, Relation.ReflTransGen (Globalization.SymmStep Adj) F G)
    (overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧ ∀ x ∈ Set.Ioo a b,
        Complex.exp ((perFrameTwist (Scfam F) Jc hJc (cfam F) (hmodelfam F) : ℂ) * x * Complex.I)
          = Complex.exp ((perFrameTwist (Scfam G) Jc hJc (cfam G) (hmodelfam G) : ℂ) * x * Complex.I)) :
    -- (1) frame-fixing certificate (A1)
    (∀ (r : Fin Dr.n → ℝ) {i j : Fin Dr.n} {x : J},
        (Dr.toCoalescenceSetup.toComparisonSetup).isBlock i j x →
        (Dr.toCoalescenceSetup.toComparisonSetup).isBlock i j
          ((Dr.toCoalescenceSetup.toComparisonSetup).Θ ((Dr.toCoalescenceSetup.toComparisonSetup).aOf r) x))
    -- (2) real Lüders
    ∧ (∀ {i j : Fin Dr.n}, i ≠ j → (Dr.toStabilizerCoupling).T i j = 0)
    -- (3) quaternionic Lüders
    ∧ (∀ {i j : Fin Dh.n}, i ≠ j → (Dh.toStabilizerCoupling).T i j = 0)
    -- (4) exceptional Lüders
    ∧ (∀ {i j : Fin 3}, i ≠ j → (hn3 ▸ Da.toStabilizerCoupling).T i j = 0)
    -- (5a) complex per-frame single `t_F` on the PRODUCED coupling `Dc.toStabilizerCoupling`,
    --      PROVED through the anchored family member `Scfam F₀ = Dc.toStabilizerCoupling`
    ∧ (∃ tF : ℝ, ∀ i j (r : Fin Dc.n → ℝ),
        (Dc.toStabilizerCoupling).ρ i j ((Dc.toStabilizerCoupling).dχ r) = (tF * (r i - r j)) • Jc)
    -- (5b) complex single GLOBAL `t` across all frames (adapter `complex_global_twist`)
    ∧ (∃ tG : ℝ, ∀ F : Frame, perFrameTwist (Scfam F) Jc hJc (cfam F) (hmodelfam F) = tG) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r i j x hx; exact frame_block_fixed Dr r hx
  · intro i j hij; exact luders_real_produced Dr hij
  · intro i j hij; exact luders_quaternionic_produced Dh imh himagh hρh hij
  · intro i j hij; exact luders_albert_produced Da hn3 hAlb hij
  · rw [← hanchor]
    exact complex_perFrame_rho (Scfam F₀) Jc hJc (cfam F₀) (hmodelfam F₀)
  · exact complex_global_twist Scfam Jc hJc cfam hmodelfam Adj connected overlap

end MasterTheorem
