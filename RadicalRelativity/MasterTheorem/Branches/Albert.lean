/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface
import Mathlib.LinearAlgebra.StdBasis

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — the exceptional branch `H₃(𝕆)` (`thm:albert`)

The exceptional typewise branch of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`, `thm:albert`).

**`thm:albert`.** On the Albert algebra `H₃(𝕆)`: `Θ_r = id` for all `r`, so the
sequential product is Lüders, `a•b = Q_{√a}b`.

## The argument (`thm:albert`, note `C1-CROSSTYPE-STABILIZER` Piece 5)

The frame stabilizer of `H₃(𝕆)` is `Spin(8)`, acting on the three octonionic
Peirce lines `(V₁₂, V₁₃, V₂₃)` by the *triality triple* `(8_v, 8_s, 8_c)`
(Yokota; see the `IsAlbertModel.block_injective` hypothesis below). In the
differential face this means: the block representations `ρ_{ij} : 𝔰𝔭𝔦𝔫(8) →
𝔰𝔬(V_{ij})` are the three triality representations, each a **nontrivial**
representation of the **simple** Lie algebra `𝔰𝔭𝔦𝔫(8)`, hence **faithful**
(*unlike* the individual complex (torus) and quaternionic block representations,
whose kernels are nonzero).

The rank of `H₃(𝕆)` is exactly `3`, so a single frame is directly a three-index
configuration and no cross-frame globalization is needed. With `dχ(r) =
Σ_{k} r_k η_k` (`lem:homomorphism`) and `ρ_{ij}(dχ(r)) = (r_i − r_j)T_{ij}`:
for block `V₁₂` the coefficient of `r₃` is `ρ₁₂(η₃) = 0` (coalescence: the RHS is
`∝ r₁ − r₂`), and faithfulness of `ρ₁₂` forces `η₃ = 0`; symmetrically `η₂ = 0`
(block `V₁₃`) and `η₁ = 0` (block `V₂₃`). Thus `dχ ≡ 0`, so `Θ_r = id` and every
off-diagonal twist `T_{ij}` vanishes. Working with `Spin(8)` abstractly sidesteps
octonionic non-associativity.

In the interface this is exactly: **injectivity of every off-diagonal `ρ_{ij}`**
plus `StabilizerCoupling.coalescence` kills `dχ` on each standard basis vector of
`ℝ³`, hence `dχ = 0` (`dchi_eq_zero_of_faithful`), and then
`StabilizerCoupling.faithful_kill` reads off `T_{ij} = 0` (`albert_luders`).

## No axioms — the `Spin(8)`-triality input is a cited hypothesis

This branch declares **no `axiom` and leaves no `sorry`**. The only external input
is the `Spin(8)`-triality faithfulness of the frame-stabilizer block
representations; it is carried as the **explicitly cited hypothesis field**
`IsAlbertModel.block_injective` (the imported Yokota conclusion for the intended
`H₃(𝕆)` instance), *not* as a free-standing axiom. Everything else — the
coalescence kill of `dχ` and the faithful-kill of the twist — is proved from the
interface. Hence `#print axioms albert_luders` is **core only**.

An earlier revision declared a global `axiom` gated on the ambient dimensions
`dim V = 8`, `dim 𝔰𝔭𝔦𝔫(8) = 28`. That gate does **not** identify the simple Lie
structure or the triality representations — a nonzero linear map out of an
arbitrary `28`-dimensional space need not be injective — so the global statement
had counterexamples and was false. Injectivity is now imported as a hypothesis on
the specific model instance, which is the honest form of Yokota's theorem.
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

variable {Stab : Type*} [AddCommGroup Stab] [Module ℝ Stab]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## The Albert model marker -/

/-- `IsAlbertModel S` *names* the object `thm:albert` is about: the rank-`3`
frame-stabilizer coupling of `H₃(𝕆)`, whose stabilizer is `Spin(8)` acting on the
three octonionic Peirce lines by the triality triple `(8_v, 8_s, 8_c)`. Its single
field carries the one imported fact the branch consumes. -/
structure IsAlbertModel (S : StabilizerCoupling 3 Stab V) : Prop where
  /-- **Yokota `Spin(8)`-triality faithfulness (cited hypothesis).** For `H₃(𝕆)`
  with `F₄ = Aut(H₃(𝕆))`, the pointwise stabilizer of the three diagonal primitive
  idempotents is `≅ Spin(8)` (Yokota, *Exceptional Lie Groups*, arXiv:0902.0431,
  **Thm 2.7.1**, p. 51), realized as the triality triple `{(a₁,a₂,a₃) ∈ SO(8)³ :
  (a₁x)(a₂y) = a₃(xy)}` (**Thm 1.16.2**, pp. 28–29), whose three `SO(8)` factors act
  on `(V₁₂, V₁₃, V₂₃)` by the vector and the two half-spin representations — the
  `8_v, 8_s, 8_c` of Baez, *The Octonions*, Bull. AMS **39** (2002), §2.4/4.2. Each is
  a nontrivial representation of the simple Lie algebra `𝔰𝔭𝔦𝔫(8)`, hence faithful.

  Stated here as the **imported conclusion for the `H₃(𝕆)` instance**: each
  off-diagonal block representation `ρ_{ij}` (`i ≠ j`) is injective. This is a cited
  hypothesis (Yokota), not a fact derived in Lean — `Stab` carries no Lie structure
  in the abstract interface, so simplicity of `𝔰𝔭𝔦𝔫(8)` is not available to prove it
  internally. -/
  block_injective : ∀ i j : Fin 3, i ≠ j → Function.Injective (S.ρ i j)

/-! ## The exceptional branch -/

/-- **`thm:albert`, hypothesis-based heart.** If every off-diagonal block
representation `ρ_{ij}` (`i ≠ j`) of a rank-`3` frame-stabilizer coupling is
injective, then the differential vanishes: `dχ = 0`.

The proof kills `dχ` on each standard basis vector `e_k = Pi.single k 1` of `ℝ³`.
For `e_k`, pick the two other indices `i, j` (both `≠ k`, and `i ≠ j`; available
since the block space has three indices `0, 1, 2`): then `(e_k)_i = (e_k)_j = 0`, so
`StabilizerCoupling.coalescence` gives `ρ_{ij}(dχ(e_k)) = 0`, and injectivity of
`ρ_{ij}` forces `dχ(e_k) = 0`. As the `e_k` are a basis, `dχ = 0`. This is the
faithful-triality kill of `thm:albert` with the `Spin(8)` identification abstracted
into the injectivity hypothesis. -/
theorem dchi_eq_zero_of_faithful (S : StabilizerCoupling 3 Stab V)
    (hf : ∀ i j : Fin 3, i ≠ j → Function.Injective (S.ρ i j)) :
    S.dχ = 0 := by
  -- Kill `dχ` on the basis vector `e_k`, using the two indices `i, j ∉ {k}`.
  have kill : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      S.dχ (Pi.single k (1 : ℝ)) = 0 := by
    intro i j k hij hik hjk
    have hcoal : S.ρ i j (S.dχ (Pi.single k (1 : ℝ))) = 0 :=
      S.coalescence i j (Pi.single k (1 : ℝ)) (by
        rw [Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hjk])
    exact hf i j hij (by rw [hcoal, map_zero])
  refine (Pi.basisFun ℝ (Fin 3)).ext fun k => ?_
  simp only [Pi.basisFun_apply, LinearMap.zero_apply]
  fin_cases k
  · exact kill 1 2 0 (by decide) (by decide) (by decide)
  · exact kill 0 2 1 (by decide) (by decide) (by decide)
  · exact kill 0 1 2 (by decide) (by decide) (by decide)

/-- **`thm:albert` (capstone).** On the exceptional type — a rank-`3`
`StabilizerCoupling` modelling `H₃(𝕆)` (marker `IsAlbertModel`) — every
off-diagonal block twist vanishes: `T_{ij} = 0` for `i ≠ j`. In the paper's
normal-form reading this is `Θ_r = id` on every block, i.e. the Lüders product
`a•b = Q_{√a}b`; the Lean statement is exactly `T i j = 0`.

The proof takes the imported injectivity of each `ρ_{ij}` from
`IsAlbertModel.block_injective`, obtains `dχ = 0` via `dchi_eq_zero_of_faithful`,
and reads off `T_{ij} = 0` with `StabilizerCoupling.faithful_kill`. No `axiom`
enters: `#print axioms albert_luders` is core only. -/
theorem albert_luders (S : StabilizerCoupling 3 Stab V) (hAlb : IsAlbertModel S)
    {i j : Fin 3} (hij : i ≠ j) : S.T i j = 0 :=
  S.faithful_kill (dchi_eq_zero_of_faithful S hAlb.block_injective) hij

end MasterTheorem
