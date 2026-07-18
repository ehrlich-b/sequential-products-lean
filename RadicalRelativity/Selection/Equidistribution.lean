/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option linter.style.longLine false

/-!
# Block-restricted equidistribution over a finite field (`lem:equidistribution`)

This file formalizes the manuscript's block-restricted equidistribution lemma
(`lem:equidistribution` in `sections/selection.tex` of "Self-Modeling Selects
Complex Quantum Mechanics", Part II), the finite-field fiber-counting estimate
that drives the classical-suppression density bound `((q+1)/2q)^{a_s - t}` of
`thm:classical-suppression`.

## Manuscript statement

> Let `q` be an odd prime power, `V ⊆ 𝔽_q^M` an affine subspace of codimension
> `t`, `J ⊆ [M]` a coordinate block, and `T_i ⊆ 𝔽_q` arbitrary per-coordinate
> target sets for `i ∈ J`. Then there is a subset `I ⊆ J` with `|I| ≥ |J| - t`
> such that
> `#{v ∈ V : v_i ∈ T_i ∀ i ∈ J} / #V ≤ ∏_{i ∈ I} |T_i| / q`.

## Encoding

* The ambient space `𝔽_q^M` is `Fin M → K` for a finite field `K` with
  `q = Fintype.card K`.
* An affine subspace of codimension `t` is a point `v₀ : Fin M → K` together
  with a direction submodule `V₀ : Submodule K (Fin M → K)` with
  `finrank K V₀ + t = finrank K (Fin M → K) = M`; its carrier is
  `{x | x - v₀ ∈ V₀}`.
* Counting uses `Nat.card` of subtypes; the displayed density inequality is
  the rational form, obtained from the exact cross-multiplied `ℕ` identity.
* **Oddness of `q` is not needed for this lemma.** The manuscript states `q`
  odd because the downstream application (`thm:classical-suppression`) uses the
  square-set density `(q+1)/2q`, which requires `q` odd; the equidistribution
  bound itself holds over every finite field, so we prove the stronger,
  hypothesis-free version.

## Main results

* `Selection.coordMap` — the linear coordinate-restriction map `V₀ → (↥I → K)`.
* `Selection.card_preimage_finset_of_surjective` — fiber counting: a surjective
  `K`-linear map onto a finite target multiplies preimage cardinalities by the
  kernel size (the equidistribution engine).
* `Selection.exists_coord_surjective_block` — the coordinate-extraction step:
  a block `J` contains a subset `I` of size `≥ |J| - t` whose coordinate
  restriction of `V₀` is surjective.
* `Selection.block_restricted_equidistribution_card` — the exact `ℕ`
  cross-multiplied form.
* `Selection.block_restricted_equidistribution` — the displayed rational
  density inequality (`lem:equidistribution`).
* `Selection.fixed_window_suppression_core` — the single-window density bound
  `≤ ((q+1)/2q)^{a_s - t}` of `thm:classical-suppression`, derived from the
  equidistribution lemma under the per-coordinate Gram-square positivity cost
  (fixed-window core only; the asymptotic-over-`𝔇` mass ratio is not formalized).

## References

* Ehrlich 2026, "Self-Modeling Selects Complex Quantum Mechanics",
  Lemma (block-restricted equidistribution bound), used in
  Theorem (classical suppression).
-/

noncomputable section

open Module Function Finset

namespace Selection

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {M : ℕ}

/-- The coordinate-restriction map `V₀ → (↥I → K)`, `w ↦ (i ↦ w i)` for the
    coordinates `i ∈ I`. This is `LinearMap.funLeft` along the inclusion
    `↥I ↪ Fin M`, precomposed with the submodule inclusion. -/
def coordMap (V₀ : Submodule K (Fin M → K)) (I : Finset (Fin M)) :
    V₀ →ₗ[K] ({x // x ∈ I} → K) :=
  (LinearMap.funLeft K K (Subtype.val : {x // x ∈ I} → Fin M)).comp V₀.subtype

@[simp] lemma coordMap_apply (V₀ : Submodule K (Fin M → K)) (I : Finset (Fin M))
    (w : V₀) (i : {x // x ∈ I}) : coordMap V₀ I w i = (w : Fin M → K) i.1 := rfl

/-- The full-space coordinate restriction `(Fin M → K) → (↥J → K)`. -/
def coordMapFull (J : Finset (Fin M)) : (Fin M → K) →ₗ[K] ({x // x ∈ J} → K) :=
  LinearMap.funLeft K K (Subtype.val : {x // x ∈ J} → Fin M)

lemma coordMapFull_surjective (J : Finset (Fin M)) :
    Function.Surjective (coordMapFull (K := K) J) :=
  LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective

/-! ## Fiber counting (the equidistribution engine) -/

/-- **Fiber counting.** For a surjective `K`-linear map `f : V₀ → W` between
    finite `K`-modules and any `Finset B` of the target, the number of `w` with
    `f w ∈ B`, times the target cardinality, equals the domain cardinality times
    `|B|`. Equivalently every fiber has the same size `|ker f|` and `|W| = |V₀| /
    |ker f|`, so `#{w : f w ∈ B} = |B| · |ker f|`. This is the equidistribution
    statement: coordinates in the surjective image are uniformly distributed. -/
lemma card_preimage_finset_of_surjective
    {W : Type*} [AddCommGroup W] [Module K W] [Finite W]
    {V₀ : Type*} [AddCommGroup V₀] [Module K V₀] [Finite V₀]
    (f : V₀ →ₗ[K] W) (hf : Function.Surjective f) (B : Finset W) :
    Nat.card {w : V₀ // f w ∈ B} * Nat.card W = Nat.card V₀ * B.card := by
  -- B1: `Nat.card V₀ = Nat.card (ker f) * Nat.card W`
  have hB1 : Nat.card V₀ = Nat.card (LinearMap.ker f) * Nat.card W := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)]
    rw [Nat.card_congr (f.quotKerEquivOfSurjective hf).toEquiv]
  -- a linear right inverse of `f`
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hfs : ∀ y, f (s y) = y := fun y => by
    have := LinearMap.ext_iff.mp hs y
    simpa using this
  -- B2: `Nat.card {w // f w ∈ B} = Nat.card (ker f) * B.card`
  have hB2 : Nat.card {w : V₀ // f w ∈ B} = Nat.card (LinearMap.ker f) * B.card := by
    let e : {w : V₀ // f w ∈ B} ≃ (LinearMap.ker f) × {y : W // y ∈ B} :=
      { toFun := fun w => (⟨(w : V₀) - s (f w), by
            rw [LinearMap.mem_ker, map_sub, hfs, sub_self]⟩, ⟨f w, w.2⟩)
        invFun := fun p => ⟨(p.1 : V₀) + s (p.2 : W), by
            simp only [map_add, (LinearMap.mem_ker).mp p.1.2, hfs, zero_add]
            exact p.2.2⟩
        left_inv := fun w => by
            apply Subtype.ext
            simp
        right_inv := fun p => by
            apply Prod.ext
            · apply Subtype.ext
              simp only [map_add, (LinearMap.mem_ker).mp p.1.2, hfs, zero_add,
                add_sub_cancel_right]
            · apply Subtype.ext
              simp only [map_add, (LinearMap.mem_ker).mp p.1.2, hfs, zero_add] }
    rw [Nat.card_congr e, Nat.card_prod]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hB2, hB1]
  ring

/-! ## Coordinate extraction -/

/-- Rank lower bound for the block restriction: the coordinate map on the whole
    block `J` has rank at least `|J| - t` when `V₀` has codimension `≤ t`. -/
lemma finrank_range_coordMap_ge
    (V₀ : Submodule K (Fin M → K)) (J : Finset (Fin M)) (t : ℕ)
    (hcod : M ≤ finrank K V₀ + t) :
    J.card ≤ finrank K (LinearMap.range (coordMap V₀ J)) + t := by
  -- rank-nullity on `coordMap V₀ J`
  have h_rn : finrank K (LinearMap.range (coordMap V₀ J))
      + finrank K (LinearMap.ker (coordMap V₀ J)) = finrank K V₀ :=
    LinearMap.finrank_range_add_finrank_ker (coordMap V₀ J)
  -- rank-nullity on `coordMapFull J`, whose ambient space is `Fin M → K`
  have h_full_rn : finrank K (LinearMap.range (coordMapFull (K := K) J))
      + finrank K (LinearMap.ker (coordMapFull (K := K) J)) = M := by
    have := LinearMap.finrank_range_add_finrank_ker (coordMapFull (K := K) J)
    rwa [Module.finrank_pi, Fintype.card_fin] at this
  -- `coordMapFull J` is surjective, so its range has full dimension `|J|`
  have h_full_range : finrank K (LinearMap.range (coordMapFull (K := K) J)) = J.card := by
    rw [LinearMap.range_eq_top.mpr (coordMapFull_surjective J)]
    rw [finrank_top, Module.finrank_pi, Fintype.card_coe]
  -- `ker (coordMap V₀ J)` injects into `ker (coordMapFull J)`, so its rank is `≤`
  have h_ker_le : finrank K (LinearMap.ker (coordMap V₀ J))
      ≤ finrank K (LinearMap.ker (coordMapFull (K := K) J)) := by
    have hmem : ∀ w : (LinearMap.ker (coordMap V₀ J)),
        (coordMapFull (K := K) J) ((w : V₀) : Fin M → K) = 0 := by
      intro w
      exact (LinearMap.mem_ker).mp w.2
    let g : (LinearMap.ker (coordMap V₀ J)) →ₗ[K] (LinearMap.ker (coordMapFull (K := K) J)) :=
      LinearMap.codRestrict _
        (V₀.subtype.comp (LinearMap.ker (coordMap V₀ J)).subtype) hmem
    have hg_inj : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have : (g a : Fin M → K) = (g b : Fin M → K) := by rw [hab]
      simpa [g, LinearMap.codRestrict] using this
    exact LinearMap.finrank_le_finrank_of_injective hg_inj
  omega

/-- **Coordinate extraction.** For a direction `V₀` of codimension `≤ t` and a
    coordinate block `J`, there is a subset `I ⊆ J` with `|J| ≤ |I| + t` whose
    coordinate restriction `coordMap V₀ I` is surjective onto `↥I → K`. -/
lemma exists_coord_surjective_block
    (V₀ : Submodule K (Fin M → K)) (J : Finset (Fin M)) (t : ℕ)
    (hcod : M ≤ finrank K V₀ + t) :
    ∃ I ⊆ J, J.card ≤ I.card + t ∧ Function.Surjective (coordMap V₀ I) := by
  classical
  set U := LinearMap.range (coordMap V₀ J) with hU
  let proj : {x // x ∈ J} → Module.Dual K ({x // x ∈ J} → K) := fun j => LinearMap.proj j
  let ψ : {x // x ∈ J} → Module.Dual K ↥U := fun j => U.dualRestrict (proj j)
  -- Step A: the restricted coordinate functionals span the dual of `U`
  have hproj_span : Submodule.span K (Set.range proj) = ⊤ := by
    have hb : proj = ⇑((Pi.basisFun K {x // x ∈ J}).dualBasis) := by
      rw [Basis.coe_dualBasis]
      funext j
      apply LinearMap.ext
      intro x
      rw [Basis.coord_apply, Pi.basisFun_repr]
      rfl
    rw [hb]
    exact Basis.span_eq _
  have hψ_span : Submodule.span K (Set.range ψ) = ⊤ := by
    have hrange : Set.range ψ = ⇑(U.dualRestrict) '' Set.range proj := by
      rw [← Set.range_comp]; rfl
    rw [hrange, ← Submodule.map_span, hproj_span, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr Subspace.dualRestrict_surjective
  -- Step B: extract an independent, spanning subfamily indexed by `κ`
  obtain ⟨κ, a, ha_inj, hsp, hli⟩ := exists_linearIndependent' K ψ
  have hκ_fin : Finite κ := Finite.of_injective a ha_inj
  letI : Fintype κ := Fintype.ofFinite κ
  have hspan_top : Submodule.span K (Set.range (ψ ∘ a)) = ⊤ := by rw [hsp, hψ_span]
  have hcard_κ : Fintype.card κ = finrank K ↥U := by
    have h1 : finrank K ↥(Submodule.span K (Set.range (ψ ∘ a))) = Fintype.card κ :=
      finrank_span_eq_card hli
    rw [hspan_top, finrank_top, Subspace.dual_finrank_eq] at h1
    exact h1.symm
  -- Step C: the extracted coordinate set `I`
  let I : Finset (Fin M) := Finset.univ.image (fun k => (a k).1)
  have hval_inj : Function.Injective (fun k => (a k).1) := by
    intro k1 k2 h
    exact ha_inj (Subtype.ext h)
  have hIJ : I ⊆ J := by
    intro x hx
    simp only [I, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, hk⟩ := hx
    rw [← hk]; exact (a k).2
  have hmemI : ∀ k, (a k).1 ∈ I := by
    intro k
    simp only [I, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨k, rfl⟩
  have hI_card : I.card = Fintype.card κ := by
    simp only [I]
    rw [Finset.card_image_of_injective _ hval_inj, Finset.card_univ]
  refine ⟨I, hIJ, ?_, ?_⟩
  · -- Step E: the cardinality bound `|J| ≤ |I| + t`
    have h := finrank_range_coordMap_ge V₀ J t hcod
    rw [← hU] at h
    omega
  · -- Step D: surjectivity of `coordMap V₀ I`
    let incl : {x // x ∈ I} → {x // x ∈ J} := fun i => ⟨i.1, hIJ i.2⟩
    let P : ({x // x ∈ J} → K) →ₗ[K] ({x // x ∈ I} → K) := LinearMap.funLeft K K incl
    have hcomp : coordMap V₀ I = P.comp (coordMap V₀ J) := by
      apply LinearMap.ext; intro w; funext i; rfl
    -- the restriction of `P` to `U` is injective (its common coordinate kernel is trivial)
    have hQinj : Function.Injective (P.domRestrict U) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro u hu
      rw [LinearMap.mem_ker] at hu
      apply (forall_dual_apply_eq_zero_iff K u).mp
      have hsub : Set.range (ψ ∘ a) ⊆ ↑((LinearMap.applyₗ u : Module.Dual K ↥U →ₗ[K] K).ker) := by
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.applyₗ_apply_apply]
        have key : (u : {x // x ∈ J} → K) (a k) = 0 := by
          have h0 := congrFun hu ⟨(a k).1, hmemI k⟩
          exact h0
        change (U.dualRestrict (LinearMap.proj (a k))) u = 0
        rw [Submodule.dualRestrict_apply, LinearMap.proj_apply]
        exact key
      have htop : (⊤ : Submodule K (Module.Dual K ↥U)) ≤ (LinearMap.applyₗ u : Module.Dual K ↥U →ₗ[K] K).ker := by
        rw [← hspan_top]; exact Submodule.span_le.mpr hsub
      intro φ
      have hmem : φ ∈ (LinearMap.applyₗ u : Module.Dual K ↥U →ₗ[K] K).ker :=
        htop Submodule.mem_top
      rw [LinearMap.mem_ker, LinearMap.applyₗ_apply_apply] at hmem
      exact hmem
    rw [← LinearMap.range_eq_top, hcomp, LinearMap.range_comp, ← hU]
    apply Submodule.eq_top_of_finrank_eq
    rw [← LinearMap.range_domRestrict U P, LinearMap.finrank_range_of_inj hQinj,
        Module.finrank_pi, Fintype.card_coe, ← hcard_κ, hI_card]

/-! ## The linear (subspace) core -/

/-- The subspace core of `lem:equidistribution`: over a direction submodule
    `V₀` of codimension `≤ t`, some `I ⊆ J` with `|J| ≤ |I| + t` satisfies the
    cross-multiplied density bound. -/
lemma equidistribution_subspace
    (V₀ : Submodule K (Fin M → K)) (J : Finset (Fin M)) (T : Fin M → Finset K)
    (t : ℕ) (hcod : M ≤ finrank K V₀ + t) :
    ∃ I ⊆ J, J.card ≤ I.card + t ∧
      Nat.card {w : V₀ // ∀ i ∈ J, (w : Fin M → K) i ∈ T i} * (Fintype.card K) ^ I.card
        ≤ Nat.card V₀ * ∏ i ∈ I, (T i).card := by
  obtain ⟨I, hIJ, hcard, hsurj⟩ := exists_coord_surjective_block V₀ J t hcod
  refine ⟨I, hIJ, hcard, ?_⟩
  set box := Fintype.piFinset (fun i : {x // x ∈ I} => T i.1) with hbox
  -- the "∀ i ∈ I" constraint is exactly membership of `coordMap V₀ I w` in the box
  have hpred : ∀ w : V₀, (∀ i ∈ I, (w : Fin M → K) i ∈ T i) ↔ (coordMap V₀ I w ∈ box) := by
    intro w
    rw [hbox, Fintype.mem_piFinset]
    constructor
    · intro h i; simpa using h i.1 i.2
    · intro h i hi; simpa using h ⟨i, hi⟩
  have hcongr : Nat.card {w : V₀ // ∀ i ∈ I, (w : Fin M → K) i ∈ T i}
      = Nat.card {w : V₀ // coordMap V₀ I w ∈ box} :=
    Nat.card_congr (Equiv.subtypeEquivRight hpred)
  -- fiber counting on the surjective coordinate map
  have hfib := card_preimage_finset_of_surjective (coordMap V₀ I) hsurj box
  have hcardfun : Nat.card ({x // x ∈ I} → K) = (Fintype.card K) ^ I.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]
  have hboxcard : box.card = ∏ i ∈ I, (T i).card := by
    rw [hbox, Fintype.card_piFinset]
    exact Finset.prod_coe_sort I (fun i => (T i).card)
  -- weakening `I ⊆ J` only adds solutions
  have hmono : Nat.card {w : V₀ // ∀ i ∈ J, (w : Fin M → K) i ∈ T i}
      ≤ Nat.card {w : V₀ // ∀ i ∈ I, (w : Fin M → K) i ∈ T i} := by
    apply Nat.card_le_card_of_injective
      (fun w => ⟨w.1, fun i hi => w.2 i (hIJ hi)⟩)
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext hab
  calc Nat.card {w : V₀ // ∀ i ∈ J, (w : Fin M → K) i ∈ T i} * (Fintype.card K) ^ I.card
      ≤ Nat.card {w : V₀ // ∀ i ∈ I, (w : Fin M → K) i ∈ T i} * (Fintype.card K) ^ I.card :=
        Nat.mul_le_mul_right _ hmono
    _ = Nat.card {w : V₀ // coordMap V₀ I w ∈ box} * Nat.card ({x // x ∈ I} → K) := by
        rw [hcongr, hcardfun]
    _ = Nat.card V₀ * box.card := hfib
    _ = Nat.card V₀ * ∏ i ∈ I, (T i).card := by rw [hboxcard]

/-! ## The affine statement (`lem:equidistribution`) -/

/-- **Block-restricted equidistribution, exact `ℕ` form.** For an affine
    subspace `{x | x - v₀ ∈ V₀}` of codimension `t` in `𝔽_q^M`, a coordinate
    block `J`, and per-coordinate targets `T`, there is `I ⊆ J` with
    `|I| ≥ |J| - t` and
    `#{x ∈ V : x_i ∈ T_i ∀ i ∈ J} · q^{|I|} ≤ #V · ∏_{i ∈ I} |T_i|`. -/
theorem block_restricted_equidistribution_card
    (v₀ : Fin M → K) (V₀ : Submodule K (Fin M → K)) (J : Finset (Fin M))
    (T : Fin M → Finset K) (t : ℕ)
    (hcod : finrank K V₀ + t = M) :
    ∃ I ⊆ J, J.card ≤ I.card + t ∧
      Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i}
          * (Fintype.card K) ^ I.card
        ≤ Nat.card {x : Fin M → K // x - v₀ ∈ V₀} * ∏ i ∈ I, (T i).card := by
  -- translate every target set by `-v₀ i`, reducing the affine count to the linear one
  let T' : Fin M → Finset K := fun i => (T i).image (fun a => a - v₀ i)
  have hTimg : ∀ i, T' i = (T i).image (fun a => a - v₀ i) := fun i => rfl
  have hcardT : ∀ i, (T' i).card = (T i).card := by
    intro i
    rw [hTimg]
    exact Finset.card_image_of_injective (T i) sub_left_injective
  obtain ⟨I, hIJ, hcard, hb⟩ := equidistribution_subspace V₀ J T' t (by omega)
  refine ⟨I, hIJ, hcard, ?_⟩
  -- `x ↦ x - v₀` identifies the affine carrier with the direction submodule
  have e0 : Nat.card {x : Fin M → K // x - v₀ ∈ V₀} = Nat.card V₀ :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1 - v₀, x.2⟩
        invFun := fun w => ⟨v₀ + (w : Fin M → K), by simp⟩
        left_inv := fun x => by apply Subtype.ext; simp
        right_inv := fun w => by apply Subtype.ext; simp }
  -- the same translation matches the constrained sets (`x i ∈ T i ↔ (x-v₀) i ∈ T' i`)
  have econ : Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i}
      = Nat.card {w : V₀ // ∀ i ∈ J, (w : Fin M → K) i ∈ T' i} := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨⟨x.1 - v₀, x.2.1⟩, ?_⟩
        invFun := fun w => ⟨v₀ + (w.1 : Fin M → K), ?_, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro i hi
      rw [hTimg, Finset.mem_image]
      exact ⟨x.1 i, x.2.2 i hi, rfl⟩
    · simp
    · intro i hi
      have hmem := w.2 i hi
      rw [hTimg, Finset.mem_image] at hmem
      obtain ⟨a, ha, hae⟩ := hmem
      have heq : (v₀ + (w.1 : Fin M → K)) i = a := by
        rw [Pi.add_apply, ← hae]; ring
      rw [heq]; exact ha
    · intro x; apply Subtype.ext; simp
    · intro w; apply Subtype.ext; apply Subtype.ext; simp
  have hprod : ∏ i ∈ I, (T i).card = ∏ i ∈ I, (T' i).card :=
    Finset.prod_congr rfl (fun i _ => (hcardT i).symm)
  rw [e0, econ, hprod]
  exact hb

/-- **Block-restricted equidistribution (`lem:equidistribution`).** The displayed
    rational density inequality: for an affine subspace `V = {x | x - v₀ ∈ V₀}`
    of codimension `t` and targets `T`, some `I ⊆ J` with `|I| ≥ |J| - t` has
    `#{x ∈ V : x_i ∈ T_i ∀ i ∈ J} / #V ≤ ∏_{i ∈ I} |T_i| / q`. -/
theorem block_restricted_equidistribution
    (v₀ : Fin M → K) (V₀ : Submodule K (Fin M → K)) (J : Finset (Fin M))
    (T : Fin M → Finset K) (t : ℕ)
    (hcod : finrank K V₀ + t = M) :
    ∃ I ⊆ J, J.card ≤ I.card + t ∧
      (Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i} : ℚ)
          / Nat.card {x : Fin M → K // x - v₀ ∈ V₀}
        ≤ ∏ i ∈ I, ((T i).card : ℚ) / Fintype.card K := by
  obtain ⟨I, hIJ, hcard, hbound⟩ :=
    block_restricted_equidistribution_card v₀ V₀ J T t hcod
  refine ⟨I, hIJ, hcard, ?_⟩
  have hVne : Nonempty {x : Fin M → K // x - v₀ ∈ V₀} :=
    ⟨v₀, by rw [sub_self]; exact V₀.zero_mem⟩
  have hVpos : (0 : ℚ) < Nat.card {x : Fin M → K // x - v₀ ∈ V₀} := by
    exact_mod_cast Nat.card_pos
  have hKpos : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
  have hqpos : (0 : ℚ) < (Fintype.card K : ℚ) ^ I.card := by positivity
  have hRHS : ∏ i ∈ I, ((T i).card : ℚ) / Fintype.card K
      = (∏ i ∈ I, ((T i).card : ℚ)) / (Fintype.card K : ℚ) ^ I.card := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
  rw [hRHS, div_le_div_iff₀ hVpos hqpos]
  have hb : (Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i} : ℚ)
        * (Fintype.card K : ℚ) ^ I.card
      ≤ (Nat.card {x : Fin M → K // x - v₀ ∈ V₀} : ℚ) * ∏ i ∈ I, ((T i).card : ℚ) := by
    exact_mod_cast hbound
  calc (Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i} : ℚ)
          * (Fintype.card K : ℚ) ^ I.card
      ≤ (Nat.card {x : Fin M → K // x - v₀ ∈ V₀} : ℚ) * ∏ i ∈ I, ((T i).card : ℚ) := hb
    _ = (∏ i ∈ I, ((T i).card : ℚ)) * Nat.card {x : Fin M → K // x - v₀ ∈ V₀} := by ring

/-! ## Fixed-window suppression core (`thm:classical-suppression`, single window)

The single-window density estimate at the heart of the classical-suppression
theorem (`thm:classical-suppression` of `sections/selection.tex`, proof in
supplement §S.4), obtained here directly from
`block_restricted_equidistribution`.

Reading `block_restricted_equidistribution` on the record-interface block `J`
(size `a_s = |J|`, `def:scale`) of an affine cut of codimension `t`, and
imposing the per-coordinate Gram-square *positivity cost* — a classical
interface coordinate must be a square, so its target density is `≤ (q+1)/2q` —
the constrained density is geometrically suppressed by `((q+1)/2q)^{a_s - t}`.

**Scope (faithfulness).** This is the *fixed-window core only*. The full
`thm:classical-suppression` — the mass ratio
`B_{cl,s}/B_{ℂ,s} ≤ exp(-g_q · a_s · (1 - o(1)))` of groupoid masses
(`def:mass`), asymptotic over the declared window sequence `𝔇` — is **not**
formalized; that whole is class (d) of the integration plan. Two further
manuscript ingredients are localized as hypotheses rather than proved here:
(i) the per-coordinate square-set density `(q+1)/2q` enters through the
hypothesis `hcap` — identifying `|Tᵢ|` with the number of squares in `𝔽_q`
needs `q` odd, and that identification is the *only* place oddness is used and
is not carried out here; (ii) the complex family's comparison density `1` is
not part of this single-window inequality. As with `lem:equidistribution`, the
core inequality itself uses no oddness hypothesis. -/

/-- **Fixed-window suppression core (`thm:classical-suppression`, single
    window).** Let `V = {x | x - v₀ ∈ V₀} ⊆ 𝔽_q^M` be an affine subspace of
    codimension `t`, `J` the record-interface block with `a_s = |J|`, and
    suppose every interface coordinate carries the Gram-square positivity cost
    `|Tᵢ|/q ≤ (q+1)/2q` (`hcap`). Then the constrained density is geometrically
    suppressed:
    `#{x ∈ V : xᵢ ∈ Tᵢ ∀ i ∈ J} / #V ≤ ((q+1)/2q)^{a_s - t}`.

    Derived from `block_restricted_equidistribution`: the equidistributed
    coordinate block, of size `≥ a_s - t`, contributes a factor `≤ (q+1)/2q ≤ 1`
    each, and the remaining coordinates only add solutions. Single-window
    estimate only; the asymptotic-over-`𝔇` mass ratio of
    `thm:classical-suppression` is not formalized. -/
theorem fixed_window_suppression_core
    (v₀ : Fin M → K) (V₀ : Submodule K (Fin M → K)) (J : Finset (Fin M))
    (T : Fin M → Finset K) (t : ℕ)
    (hcod : finrank K V₀ + t = M)
    (hcap : ∀ i ∈ J,
      ((T i).card : ℚ) / (Fintype.card K : ℚ)
        ≤ ((Fintype.card K : ℚ) + 1) / (2 * (Fintype.card K : ℚ))) :
    (Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i} : ℚ)
        / Nat.card {x : Fin M → K // x - v₀ ∈ V₀}
      ≤ (((Fintype.card K : ℚ) + 1) / (2 * (Fintype.card K : ℚ))) ^ (J.card - t) := by
  obtain ⟨I, hIJ, hcard, hdens⟩ :=
    block_restricted_equidistribution v₀ V₀ J T t hcod
  set q : ℚ := (Fintype.card K : ℚ) with hq
  set r : ℚ := (q + 1) / (2 * q) with hr
  have hqpos : (0 : ℚ) < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  have h1q : (1 : ℚ) ≤ q := by
    rw [hq]
    have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
    exact_mod_cast h1
  -- the per-coordinate cost `r = (q+1)/2q` lies in `[0,1]`
  have hr0 : (0 : ℚ) ≤ r := by rw [hr]; apply div_nonneg <;> linarith
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one₀ (by linarith : (0 : ℚ) < 2 * q)]; linarith
  -- the equidistributed product collapses to `r ^ |I|`
  have hprod : ∏ i ∈ I, ((T i).card : ℚ) / q ≤ r ^ I.card := by
    calc ∏ i ∈ I, ((T i).card : ℚ) / q
        ≤ ∏ _i ∈ I, r :=
          Finset.prod_le_prod
            (fun i _ => div_nonneg (Nat.cast_nonneg _) hqpos.le)
            (fun i hi => hcap i (hIJ hi))
      _ = r ^ I.card := by rw [Finset.prod_const]
  -- `r ≤ 1` and `|I| ≥ a_s - t` give the geometric suppression
  calc (Nat.card {x : Fin M → K // x - v₀ ∈ V₀ ∧ ∀ i ∈ J, x i ∈ T i} : ℚ)
          / Nat.card {x : Fin M → K // x - v₀ ∈ V₀}
      ≤ ∏ i ∈ I, ((T i).card : ℚ) / q := hdens
    _ ≤ r ^ I.card := hprod
    _ ≤ r ^ (J.card - t) := pow_le_pow_of_le_one hr0 hr1 (by omega)

end Selection
