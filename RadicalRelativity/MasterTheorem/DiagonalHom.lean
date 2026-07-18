/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Coalescence
import Mathlib.Topology.Instances.RealVectorSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# DiagonalHom — `lem:homomorphism`: the diagonal character and the coupling

The producer lane, part 2. This module checks the two calc-1 halves of the
Lie-differential reduction (`lem:homomorphism`) and **produces the `StabilizerCoupling`**
consumed by the four typewise branch lanes. Its capstone, `toStabilizerCoupling`, is the
honesty seam of the formalization: the `coupling` field of the produced
`StabilizerCoupling` (`ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}`) is **PROVED** here — via the
linear-algebra anchor `hyperplane_factorization` applied to the differentiated
coalescence — not assumed. Precision (adversarial review 2026-07-15): the constructor
consumes **only the differential-face fields** (`ρ`, `ρ_skew`, `dχAdd`, `dχAdd_cont`,
`coalescence_diff`, `n`, `rank_ge`); the comparison face rides along as the parent
structure but nothing here derives the differential data from `Θ` — so
`toStabilizerCoupling` is the *packager of the post-differentiation assumption package*,
not a comparison-to-differential bridge. The analytic differentiation is the paper's.

## What is proved here (Lean theorems)

* `hyperplane_factorization` — **pure linear algebra, fully proved (the anchor).** A
  real-linear map `L : ℝⁿ → W` vanishing on the hyperplane `{r_i = r_j}` (`i ≠ j`) equals
  `r ↦ (r_i − r_j)·L(e_i)`. This is what pins the single block generator `T_{ij}`.
* `chi_hom` — the diagonal comparison maps form a homomorphism on the negative orthant
  (`Θ_{r+r'} = Θ_r ∘ Θ_{r'}`); this is `Θ_cocycle` (`vdW` Prop 5.7), restated.
* `chi_comm` — the diagonal comparison maps commute pairwise (abelian image), from the
  cocycle; this is the `well-defined by … abelian image` content of the `χ̃` extension.
* `lieHom_smooth` (**PROVED theorem, no axiom**) — a *continuous* additive map is
  ℝ-linear (`AddMonoidHom.toRealLinearMap`); this replaces the earlier unsound axiom.
* `DiagonalHomSetup.dChiLinear` (`dChi_linear`) — the real-linear differential `dχ`,
  obtained from the additive differential of `χ̃` and its continuity via `lieHom_smooth`.
* `DiagonalHomSetup.toStabilizerCoupling` (**capstone**) — packages the differential-face
  fields into the `StabilizerCoupling` the branches consume, proving `coupling`.

## No global axioms in this module

This module declares **no `axiom`s** (the former A2 `lieHom_smooth` is now a proved
theorem). Cartan's smoothness of the character `χ̃` enters only as the *continuity* of the
differential, carried as the cited `DiagonalHomSetup.dχAdd_cont` **field** — a hypothesis a
reviewer reads off the structure, not a global axiom.

## Honesty note on the differential face (adversarial review §5.5)

`DiagonalHomSetup` is **interface data that begins after the paper's analytic
comparison-to-differential step.** It carries the differential-face objects — the block
reps `ρ_{ij}` (orthogonality `ρ_skew`, `prop:isotropy`), the additive differential `dχAdd`
with its continuity `dχAdd_cont`, and `coalescence_diff` — as **fields**. Lean does **not**
construct `dχAdd` from the proved comparison cocycle (`chi_extend_wellDefined`/`chi_comm`), nor equate
it with a derivative of `Θ`: that analytic derivation is the paper's. What Lean **checks
downstream** is only the linear algebra — `lieHom_smooth` (continuity ⟹ linearity) and
`hyperplane_factorization` (the vanishing shadow `coalescence_diff` ⟹ the single-generator
coupling `ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}`, strictly stronger, hence a genuine
conclusion). No "produced from the cocycle" is claimed anywhere.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*,
  `lem:homomorphism`.
* Bröcker–tom Dieck, *Representations of Compact Lie Groups* (Cartan smoothness).
* Faraut–Korányi, *Analysis on Symmetric Cones*, 1994 (frame-stabilizer Lie apparatus).
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

/-! ## The linear-algebra anchor: hyperplane factorization

`lem:homomorphism`'s decisive step, isolated as pure linear algebra. A real-linear map out
of `ℝⁿ` that vanishes on the coalescence hyperplane `{r_i = r_j}` is a scalar multiple of
the linear form `(r_i − r_j)`; the scalar is the single block generator `T_{ij}`. -/

/-- **Hyperplane factorization (PROVED — the anchor).** Let `L : ℝⁿ → W` be real-linear,
`i ≠ j`, and suppose `L r = 0` whenever `r_i = r_j`. Then `L r = (r_i − r_j) • L(e_i)` for
every `r`, where `e_i = Pi.single i 1`. In `lem:homomorphism` this is applied to
`L = ρ_{ij} ∘ dχ`, giving the single generator `T_{ij} = ρ_{ij}(dχ(e_i))`. -/
theorem hyperplane_factorization {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : (Fin n → ℝ) →ₗ[ℝ] W) {i j : Fin n} (hij : i ≠ j)
    (hker : ∀ r : Fin n → ℝ, r i = r j → L r = 0) (r : Fin n → ℝ) :
    L r = (r i - r j) • L (Pi.single i 1 : Fin n → ℝ) := by
  have hpi : (Pi.single i 1 : Fin n → ℝ) i = 1 := by rw [Pi.single_eq_same]
  have hpj : (Pi.single i 1 : Fin n → ℝ) j = 0 := by rw [Pi.single_eq_of_ne (Ne.symm hij)]
  have key : L (r - (r i - r j) • (Pi.single i 1 : Fin n → ℝ)) = 0 := by
    apply hker
    simp only [Pi.sub_apply, Pi.smul_apply, hpi, hpj, smul_eq_mul, mul_one, mul_zero, sub_zero]
    ring
  rw [map_sub, map_smul] at key
  exact sub_eq_zero.mp key

/-! ## Smoothness of the character's differential — PROVED (no axiom)

Formerly the PLAN ledger axiom A2. The earlier axiom form was **unsound**: its type
quantified over an arbitrary additive map `f : (ℝⁿ,+) →+ Stab` and asserted it is
ℝ-linear, which is false (discontinuous Cauchy additive maps). It is now a **theorem**: a
*continuous* additive map between topological ℝ-vector spaces is ℝ-linear
(Mathlib `AddMonoidHom.toRealLinearMap`; ℚ-linearity from additivity, then density of `ℚ`
in `ℝ` + continuity). The only honest content carried from Cartan's smoothness of `χ̃` is
then the **continuity** of the differential, which enters as the `DiagonalHomSetup`
field `dχAdd_cont` (a cited hypothesis, not a global axiom). -/

/-- **`lieHom_smooth` (PROVED, no axiom).** A continuous additive map `f : (ℝⁿ,+) →+ Stab`
into a topological ℝ-vector space upgrades to a real-linear map agreeing with it. This is
the honest consumed form of "the differential of the smooth character `χ̃` is real-linear":
Cartan's theorem supplies the *continuity* of the differential (the `dχAdd_cont` field),
and this converts continuity + additivity into ℝ-linearity via Mathlib's
`AddMonoidHom.toRealLinearMap`. No arbitrary additive map is claimed linear. (A `def`
rather than a `theorem` only because it packages the linear map as data; it is axiom-free
— `#print axioms` shows core only.) -/
noncomputable def lieHom_smooth {n : ℕ} {Stab : Type*} [AddCommGroup Stab] [Module ℝ Stab]
    [TopologicalSpace Stab] [ContinuousSMul ℝ Stab] [T2Space Stab]
    (f : (Fin n → ℝ) →+ Stab) (hf : Continuous f) :
    { d : (Fin n → ℝ) →ₗ[ℝ] Stab // ∀ r, d r = f r } :=
  ⟨(f.toRealLinearMap hf).toLinearMap, fun _ => rfl⟩

/-! ## `lem:homomorphism`: the diagonal character on the orthant -/

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]

/-- **`lem:homomorphism` (orthant homomorphism, PROVED).** On the negative orthant the
diagonal comparison maps compose additively in the exponent: `Θ_{r+r'} = Θ_r ∘ Θ_{r'}`.
This is `Θ_cocycle` (`vdW` Prop 5.7), the seed of the character `χ̃`. -/
theorem chi_hom (C : ComparisonSetup J) {r r' : Fin C.n → ℝ}
    (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    C.Θ (C.aOf (r + r')) = (C.Θ (C.aOf r)).trans (C.Θ (C.aOf r')) :=
  C.Θ_cocycle r r' hr hr'

/-- **`lem:homomorphism` (abelian image, PROVED).** The diagonal comparison maps commute
pairwise on the negative orthant. This is the `abelian image` fact underwriting the
well-definedness of the `χ̃(s − t) := Θ_s Θ_t⁻¹` extension to `(ℝⁿ,+)`. -/
theorem chi_comm (C : ComparisonSetup J) {r r' : Fin C.n → ℝ}
    (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    (C.Θ (C.aOf r)).trans (C.Θ (C.aOf r')) = (C.Θ (C.aOf r')).trans (C.Θ (C.aOf r)) := by
  rw [← C.Θ_cocycle r r' hr hr', ← C.Θ_cocycle r' r hr' hr, add_comm]

/-- **`lem:homomorphism` (extension well-definedness identity, PROVED).** The
cross-product identity that makes the paper's `χ̃(s − t) := Θ_s Θ_t⁻¹` extension
well defined: if `s − t = s' − t'` (all in the orthant), equivalently `s + t' = s' + t`,
then the cross-products agree, `Θ_s Θ_{t'} = Θ_{s'} Θ_t`. Stated inverse-free.
**No extension map `χ̃` is constructed here** (adversarial review 2026-07-15: the former
name `chi_extend_wellDefined` suggested one); this theorem is exactly the one equality the paper's
well-definedness argument needs, and the extension itself is the paper's. -/
theorem chi_extend_wellDefined (C : ComparisonSetup J) {s t s' t' : Fin C.n → ℝ}
    (hs : ∀ i, s i ≤ 0) (ht : ∀ i, t i ≤ 0) (hs' : ∀ i, s' i ≤ 0) (ht' : ∀ i, t' i ≤ 0)
    (hsum : s + t' = s' + t) :
    (C.Θ (C.aOf s)).trans (C.Θ (C.aOf t')) = (C.Θ (C.aOf s')).trans (C.Θ (C.aOf t)) := by
  rw [← C.Θ_cocycle s t' hs ht', ← C.Θ_cocycle s' t hs' ht, hsum]

/-! ## The differential face and the bridge to `StabilizerCoupling` -/

variable (J)
variable (Stab : Type*) [NormedAddCommGroup Stab] [NormedSpace ℝ Stab]
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The differential-face setup — INTERFACE DATA, beginning after the analytic step.**

Honesty scope (adversarial review §5.5): `DiagonalHomSetup` begins **after** the paper's
analytic comparison-to-differential step. It carries the differential-face objects the
paper obtains by differentiating the comparison character `χ̃` — the block reps `ρ_{ij}`
(skew, `prop:isotropy`), the *additive* differential `dχAdd` with its Cartan-smoothness
continuity `dχAdd_cont`, and `coalescence_diff` (the vanishing of `ρ_{ij} ∘ dχ` on the
hyperplane `{r_i = r_j}`) — as **fields**. Nothing here constructs `dχAdd` from the proved
comparison cocycle (`chi_extend_wellDefined`/`chi_comm`), and nothing equates it with a derivative of
`Θ`: that analytic derivation is the paper's, not Lean's. What Lean **proves** downstream
is only the linear algebra: `lieHom_smooth` turns `dχAdd`'s continuity into ℝ-linearity,
and `hyperplane_factorization` turns `coalescence_diff` into the single-generator coupling
`ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}` (strictly stronger than `coalescence_diff`, hence a
genuine conclusion). The `ρ`/`dχAdd`/`coalescence_diff` fields are the audit surface for
the imported Lie apparatus, exactly as `StabilizerCoupling` already carries `ρ`/`dχ`. -/
structure DiagonalHomSetup extends CoalescenceSetup J where
  /-- Block representation `ρ_{ij} : 𝔰𝔱𝔞𝔟(F) → End(V_{ij})`. -/
  ρ : Fin n → Fin n → Stab →ₗ[ℝ] (V →ₗ[ℝ] V)
  /-- `ρ_{ij}(ξ)` is skew for the block inner product (`prop:isotropy`). -/
  ρ_skew : ∀ i j (ξ : Stab) (x : V), ⟪(ρ i j ξ) x, x⟫_ℝ = 0
  /-- The additive differential of the character `χ̃` (interface data; the paper's analytic
      differentiation of `χ̃`, not constructed here). -/
  dχAdd : (Fin n → ℝ) →+ Stab
  /-- Continuity of the differential — the honest content of Cartan smoothness of `χ̃`
      (cited hypothesis, not a global axiom); consumed by `lieHom_smooth` to get linearity. -/
  dχAdd_cont : Continuous dχAdd
  /-- Differentiated coalescence: `ρ_{ij}(dχ(r)) = 0` on the hyperplane `{r_i = r_j}` — the
      differential shadow of the proved group-level `coalescence_block` (interface data;
      the differentiation of the group-level statement is the paper's analytic step). -/
  coalescence_diff : ∀ (i j : Fin n) (r : Fin n → ℝ), r i = r j → ρ i j (dχAdd r) = 0

namespace DiagonalHomSetup

variable {J Stab V}
variable [NormedAddCommGroup Stab] [NormedSpace ℝ Stab] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **`dChi_linear` (via the proved `lieHom_smooth`).** The real-linear differential `dχ`
of `χ̃`, obtained from the additive differential `dχAdd` and its continuity `dχAdd_cont`
by the (now proved, axiom-free) `lieHom_smooth`. -/
def dChiLinear (D : DiagonalHomSetup J Stab V) : (Fin D.n → ℝ) →ₗ[ℝ] Stab :=
  (lieHom_smooth D.dχAdd D.dχAdd_cont).1

@[simp] theorem dChiLinear_apply (D : DiagonalHomSetup J Stab V) (r : Fin D.n → ℝ) :
    D.dChiLinear r = D.dχAdd r :=
  (lieHom_smooth D.dχAdd D.dχAdd_cont).2 r

/-- **The producer capstone (`toStabilizerCoupling`).** Bridges the comparison-map face to
the differential face consumed by the branch lanes. The `coupling` field
`ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}` is **PROVED** (not assumed): for `i ≠ j` it is
`hyperplane_factorization` applied to `ρ_{ij} ∘ dχ` with the differentiated coalescence as
the vanishing hypothesis, pinning `T_{ij} = ρ_{ij}(dχ(e_i))`; for `i = j` both sides are
zero. -/
def toStabilizerCoupling (D : DiagonalHomSetup J Stab V) : StabilizerCoupling D.n Stab V where
  ρ := D.ρ
  ρ_skew := D.ρ_skew
  dχ := D.dChiLinear
  T := fun i j => D.ρ i j (D.dChiLinear (Pi.single i 1 : Fin D.n → ℝ))
  coupling := by
    intro i j r
    by_cases hij : i = j
    · subst hij
      rw [sub_self, zero_smul, dChiLinear_apply]
      exact D.coalescence_diff i i r rfl
    · have hker : ∀ s : Fin D.n → ℝ, s i = s j →
          ((D.ρ i j).comp D.dChiLinear) s = 0 := by
        intro s hs
        rw [LinearMap.comp_apply, dChiLinear_apply]
        exact D.coalescence_diff i j s hs
      have h := hyperplane_factorization ((D.ρ i j).comp D.dChiLinear) hij hker r
      simpa only [LinearMap.comp_apply] using h
  rank_ge := D.rank_ge

end DiagonalHomSetup

end MasterTheorem
