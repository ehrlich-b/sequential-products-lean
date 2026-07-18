/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finite.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.style.longLine false

/-!
# Descent results of the selection theorem (Part II, `sections/selection.tex`)

This file formalizes four descent results of Part II of "Self-Modeling Selects Complex
Quantum Mechanics", each with zero paper-specific axioms:

* `Selection.inertia_obstruction` — `prop:inertia-obstruction`: for a reachable tower
  presentation the gauge projection `π : Aut(x) → S_A × Aut(Σ)` is injective.
* `Selection.cor_factorial` — `cor:factorial`: hence `|Aut(x)| ≤ r! · |C|!`, a bound
  independent of the presentation dimensions.
* `Selection.findet` — `lem:findet`: finite determinacy — behavior is fixed by words of
  length `≤ dim E_x + dim E_y` (engine: `chain_le_finrank`, the reachability filtration
  stabilizes by dimension).
* `Selection.linear_descent` — `thm:linear-descent`: two minimal realizations with equal
  behavior are related by a unique port/letter-intertwining linear isomorphism.

The first two sit in the `Presentation` model below; the last two use the lighter
`Realization` (weighted-automaton) model in the second section, whose per-section docstrings
give the faithfulness deltas.

## Modeling and faithfulness

The manuscript's `def:tower` / `def:gauge` package a large tuple (structure tensors,
instruments, initial states, record and unit effects, hereditary intertwiners, …) and a
gauge group `G_Σ = (∏ⱼ GL(Vⱼ)) ⋊ (S_A × Aut(Σ))`.  Both results proved here need only a
small fragment of that data, and this file captures exactly that fragment, no more:

* the **state space** `E` (playing the role of `E_x = ⨁ⱼ Vⱼ`), a vector space over the
  regulator field `F`;
* a **letter set** `L` with a linear action `act : L → End(E)` (the typed-letter action
  of `def:behavior` — instrument letters and structural letters together);
* the **input ports** `ports ⊆ E` (the initial states);
* the finite **record-label set** `A` (`|A| = r`) and **signature-channel set** `C`, with
  the levelwise gauge acting on letters through a monoid homomorphism
  `relabel : S_A × S_C → Perm L`.

An **automorphism** (`AutGroup`) is a linear automorphism `S ∈ E ≃ₗ[F] E` together with a
combinatorial part `(γ, β) ∈ S_A × S_C` that fixes every port and intertwines the letter
action along `relabel (γ, β)`.  This is a subgroup of `(E ≃ₗ[F] E) × (Perm A × Perm C)`,
so its group structure is inherited (no bespoke group axioms).  The projection `π`
(`gaugeProj`) reads off `(γ, β)`.

**Reachability** (`Reachable`, the reachable half of `def:minimal`): the letter orbit of
the input ports spans `E`.  `InReach` is the orbit as an inductive set;
`Submodule.span F {v | InReach P v} = ⊤` is reachability.

**What is faithful.** The heart of `prop:inertia-obstruction` — a `ker π` element fixes the
ports, commutes with every letter, hence fixes every reachable vector, hence has identity
linear part — is proved in full (`inertia_core`, `inertia_obstruction`), zero custom
axioms.  The factorial bound is the honest orbit–stabilizer/injectivity count.

**Where the Lean statement is weaker/different from the paper.**
* The paper's target is `S_A × Aut(Σ)` with `Aut(Σ) ≤ S_C`.  We model `Aut(Σ)` by the
  full symmetric group `Perm C = S_C` (an over-approximation), which yields *exactly* the
  paper's stated numeric bound `r! · |C|!` and keeps injectivity strictly easier.  The
  sharper `r! · |Aut(Σ)|` is `≤ r! · |C|!`, so nothing is lost.
* We omit the output-functional-fixing clause of the paper's one-line proof: it is not
  needed, since port-fixing plus letter-commuting already forces the linear part to be the
  identity *on the reachable locus*, and reachability is `⊤`.  (Observability, the other
  half of `def:minimal`, is therefore not modeled here — it plays no role in either result.)
* `relabel` is an arbitrary monoid homomorphism (any gauge action on letters), rather than
  the specific levelwise/record/signature action; the results hold for every such action,
  so this is a faithful generalization, not a gap.
* The `GL(Vⱼ)` factor of `G_Σ` is absorbed into the single linear automorphism `S` of `E`;
  its levelwise/block structure (`thm:linear-descent`) is not needed for these two results
  and is not represented.
-/

namespace Selection

variable {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module F E]

/-- A minimal **tower presentation** (`def:tower`), reduced to exactly the data the inertia
obstruction and the factorial bound require: a state space `E` over the regulator field
`F`, a letter set `L` with a linear action, the input ports, the finite record-label set
`A` (with `|A| = r`) and signature-channel set `C`, and the gauge action on letters
`relabel : S_A × S_C → Perm L`.  See the module docstring for what of `def:tower`/`def:gauge`
is and is not represented. -/
structure Presentation (F : Type*) [Field F] (E : Type*) [AddCommGroup E] [Module F E] where
  /-- The letter set (instrument and structural letters of `def:behavior`). -/
  L : Type*
  /-- The typed-letter action on the state space. -/
  act : L → (E →ₗ[F] E)
  /-- The input ports (initial states). -/
  ports : Set E
  /-- The record-label set; its cardinality is the paper's `r`. -/
  A : Type*
  /-- The signature-channel set; the paper's `Aut(Σ)` sits inside `Perm C = S_C`. -/
  C : Type*
  /-- The gauge action on letters: `S_A × S_C` acts on `L` by a monoid homomorphism. -/
  relabel : (Equiv.Perm A × Equiv.Perm C) →* Equiv.Perm L

/-- The **reachable orbit** of the input ports: the smallest set containing the ports and
closed under the letter action (the letter orbit of `def:minimal`). -/
inductive InReach (P : Presentation F E) : E → Prop
  | port {p : E} : p ∈ P.ports → InReach P p
  | act (ℓ : P.L) {v : E} : InReach P v → InReach P (P.act ℓ v)

/-- **Reachability** (`def:minimal`, reachable half): the letter orbit of the input ports
spans the state space. -/
def Reachable (P : Presentation F E) : Prop :=
  Submodule.span F {v | InReach P v} = ⊤

/-- A linear endomorphism that fixes every input port and commutes with every letter fixes
every reachable vector.  (Proof device for `inertia_core`; the induction is on the orbit.) -/
theorem inReach_fixed (P : Presentation F E) (S : E →ₗ[F] E)
    (hp : ∀ p ∈ P.ports, S p = p)
    (hc : ∀ (ℓ : P.L) (v : E), S (P.act ℓ v) = P.act ℓ (S v))
    {v : E} (hv : InReach P v) : S v = v := by
  induction hv with
  | port hp' => exact hp _ hp'
  | act ℓ _ ih => rw [hc, ih]

/-- **Inertia core** (linear-algebra heart of `prop:inertia-obstruction`).  On a reachable
presentation, a linear automorphism that fixes every input port and commutes with every
letter is the identity: it fixes the reachable orbit, which spans `E`. -/
theorem inertia_core (P : Presentation F E) (hreach : Reachable P)
    (S : E ≃ₗ[F] E)
    (hp : ∀ p ∈ P.ports, S p = p)
    (hc : ∀ (ℓ : P.L) (v : E), S (P.act ℓ v) = P.act ℓ (S v)) :
    S = 1 := by
  have hspan : Submodule.span F {v | InReach P v} = ⊤ := hreach
  have hmap : (S : E →ₗ[F] E) = LinearMap.id := by
    refine LinearMap.ext_on hspan (fun x hx => ?_)
    simpa using inReach_fixed P (S : E →ₗ[F] E) hp hc hx
  have h1 : (S : E →ₗ[F] E) = ((1 : E ≃ₗ[F] E) : E →ₗ[F] E) := by
    rw [hmap, LinearEquiv.coe_toLinearMap_one]
  exact LinearEquiv.toLinearMap_injective h1

/-- The **automorphism group** `Aut(x)` of the presentation: linear automorphisms `S` of
`E` carrying a combinatorial part `(γ, β) ∈ S_A × S_C` that fixes every port and
intertwines the letter action along `relabel (γ, β)`.  Realized as a subgroup of
`(E ≃ₗ[F] E) × (Perm A × Perm C)`, so the group structure is inherited. -/
def AutGroup (P : Presentation F E) :
    Subgroup ((E ≃ₗ[F] E) × (Equiv.Perm P.A × Equiv.Perm P.C)) where
  carrier := {x | (∀ p ∈ P.ports, x.1 p = p) ∧
    ∀ (ℓ : P.L) (v : E), x.1 (P.act ℓ v) = P.act (P.relabel x.2 ℓ) (x.1 v)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro p _
      simp only [Prod.fst_one, LinearEquiv.coe_one, id_eq]
    · intro ℓ v
      simp only [Prod.fst_one, Prod.snd_one, LinearEquiv.coe_one, id_eq, map_one,
        Equiv.Perm.one_apply]
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [Prod.fst_mul, LinearEquiv.mul_apply]
      rw [hy1 p hp, hx1 p hp]
    · intro ℓ v
      simp only [Prod.fst_mul, Prod.snd_mul, LinearEquiv.mul_apply]
      rw [hy2 ℓ v, hx2 (P.relabel y.2 ℓ) (y.1 v), map_mul, Equiv.Perm.mul_apply]
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [Prod.fst_inv, LinearEquiv.coe_inv]
      conv_lhs => rw [← hx1 p hp]
      exact x.1.symm_apply_apply p
    · intro ℓ v
      simp only [Prod.fst_inv, Prod.snd_inv, LinearEquiv.coe_inv]
      have h := hx2 (P.relabel x.2⁻¹ ℓ) (x.1.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      have hrel : P.relabel x.2 (P.relabel x.2⁻¹ ℓ) = ℓ := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
      rw [hrel] at h
      rw [← h, LinearEquiv.symm_apply_apply]

/-- The **gauge projection** `π : Aut(x) → S_A × Aut(Σ)` of `prop:inertia-obstruction`,
reading off the combinatorial part.  (`Aut(Σ)` is modeled by all of `Perm C`; see the
module docstring.) -/
def gaugeProj (P : Presentation F E) :
    AutGroup P →* (Equiv.Perm P.A × Equiv.Perm P.C) :=
  (MonoidHom.snd (E ≃ₗ[F] E) (Equiv.Perm P.A × Equiv.Perm P.C)).comp (AutGroup P).subtype

/-- **Inertia obstruction** (`prop:inertia-obstruction`).  For a reachable presentation the
gauge projection `π : Aut(x) → S_A × Aut(Σ)` is injective: a kernel element fixes the
ports and commutes with every letter (its combinatorial part is trivial), so by
reachability its linear part is the identity, i.e. it is the identity automorphism. -/
theorem inertia_obstruction (P : Presentation F E) (hreach : Reachable P) :
    Function.Injective (gaugeProj P) := by
  refine (injective_iff_map_eq_one (gaugeProj P)).mpr (fun a ha => ?_)
  have hg : a.1.2 = 1 := ha
  have hp : ∀ p ∈ P.ports, a.1.1 p = p := a.2.1
  have hc : ∀ (ℓ : P.L) (v : E), a.1.1 (P.act ℓ v) = P.act ℓ (a.1.1 v) := by
    intro ℓ v
    have h := a.2.2 ℓ v
    rw [hg] at h
    simpa using h
  have hS : a.1.1 = 1 := inertia_core P hreach a.1.1 hp hc
  exact Subtype.ext (Prod.ext_iff.mpr ⟨hS, hg⟩)

/-- **Presentation inertia dies under minimalization** (`cor:factorial`).  Reachability
makes `π` injective, so `|Aut(x)|` is bounded by `|S_A × Aut(Σ)| ≤ r! · |C|!`, a bound
independent of the presentation dimensions. -/
theorem cor_factorial (P : Presentation F E) (hreach : Reachable P)
    [Finite P.A] [Finite P.C] :
    Nat.card (AutGroup P) ≤ (Nat.card P.A).factorial * (Nat.card P.C).factorial := by
  calc Nat.card (AutGroup P)
      ≤ Nat.card (Equiv.Perm P.A × Equiv.Perm P.C) :=
        Nat.card_le_card_of_injective _ (inertia_obstruction P hreach)
    _ = Nat.card (Equiv.Perm P.A) * Nat.card (Equiv.Perm P.C) := Nat.card_prod _ _
    _ = (Nat.card P.A).factorial * (Nat.card P.C).factorial := by
        rw [Nat.card_perm, Nat.card_perm]

end Selection

/-!
## Finite determinacy (`lem:findet`)

This section formalizes the finite-determinacy lemma `lem:findet` of Part II: a formal
behavior `Beh(w) = L·M_w·R` over the free monoid on the letters is determined by its values
on words of bounded length. The engine is the reachability filtration of `def:minimal`
(the letter orbit of the input ports), which strictly increases until it stabilizes and
therefore stabilizes by step `dim E` — exactly the "rank conditions on matrices of
`lem:findet`-bounded word length" the manuscript invokes.

Faithfulness deltas from the manuscript form:
* The bound proved is `w.length ≤ dim E_x + dim E_y` (`= D`), one step looser than the
  paper's `≤ D - 1`. The difference is a harmless off-by-one in the chain-length count and
  changes nothing downstream.
* A "letter" here is any element of the abstract alphabet `L` with a linear action; the
  paper's instrument and structural letters are all instances, so the statement covers them.
* The "polynomial in the presentation" clause of the paper is a remark about entrywise
  dependence, not part of the determinacy claim, and is not modeled.
-/

namespace Selection

section Realizations

variable {F : Type*} [Field F] {L Inp Out : Type*}

/-- The linear action of a word on the state space:
`wordAction act (ℓ :: w) v = act ℓ (wordAction act w v)` and `wordAction act [] = id`.
This is `M_w` of `def:behavior`. -/
def wordAction {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) : List L → (E →ₗ[F] E)
  | [] => LinearMap.id
  | ℓ :: w => (act ℓ).comp (wordAction act w)

/-- The formal behavior `Beh(w) = L·M_w·R` of `def:behavior`: run word `w` from input port
`i`, read output port `o`. -/
def behavior {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) (init : Inp → E) (out : Out → (E →ₗ[F] F))
    (w : List L) (i : Inp) (o : Out) : F :=
  out o (wordAction act w (init i))

/-- The full reachable orbit: every state reachable from the seed set `S` by some word
(the letter orbit of `def:minimal`). -/
def fullOrbit {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) (S : Set E) : Set E :=
  {v | ∃ w : List L, ∃ s ∈ S, v = wordAction act w s}

/-- States reachable from the seed set `S` by words of length `≤ k`. -/
def orbitGen {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) (S : Set E) (k : ℕ) : Set E :=
  {v | ∃ w : List L, w.length ≤ k ∧ ∃ s ∈ S, v = wordAction act w s}

/-- The reachability filtration: span of the states reachable by words of length `≤ k`.
The chain `E_0 ≤ E_1 ≤ ⋯` of `lem:findet`. -/
def orbitFil {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) (S : Set E) (k : ℕ) : Submodule F E :=
  Submodule.span F (orbitGen act S k)

/-- **Chain stabilization by dimension** (the engine of `lem:findet`). A monotone chain of
subspaces of a finite-dimensional space that propagates equality
(`f k = f (k+1) ⟹ f (k+1) = f (k+2)`) is bounded by its value at index `dim M`: every term
lies below `f (finrank F M)`. This is the "strictly increases until it stabilizes, hence
stabilizes by step `dim`" step. -/
theorem chain_le_finrank {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (f : ℕ → Submodule F M) (hmono : Monotone f)
    (hprop : ∀ k, f k = f (k + 1) → f (k + 1) = f (k + 1 + 1)) :
    ∀ k, f k ≤ f (Module.finrank F M) := by
  have hstab : ∃ N ≤ Module.finrank F M, f N = f (N + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ N ≤ Module.finrank F M, f N < f (N + 1) := fun N hN =>
      lt_of_le_of_ne (hmono (Nat.le_succ N)) (hcon N hN)
    have hrank : ∀ k, k ≤ Module.finrank F M + 1 → k ≤ Module.finrank F (f k) := by
      intro k
      induction k with
      | zero => intro _; exact Nat.zero_le _
      | succ n ih =>
        intro hn
        have h1 : n ≤ Module.finrank F (f n) := ih (by omega)
        have h2 : Module.finrank F (f n) < Module.finrank F (f (n + 1)) :=
          Submodule.finrank_lt_finrank_of_lt (hlt n (by omega))
        omega
    have hbig := hrank (Module.finrank F M + 1) (le_refl _)
    have hle : Module.finrank F (f (Module.finrank F M + 1)) ≤ Module.finrank F M :=
      Submodule.finrank_le _
    omega
  obtain ⟨N, hNd, hNeq⟩ := hstab
  have hstill : ∀ n, N ≤ n → f n = f (n + 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hNeq
    | succ m hm ih => exact hprop m ih
  have hconst : ∀ m, N ≤ m → f m = f N := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [← ih]; exact (hstill n hn).symm
  intro k
  rcases Nat.lt_or_ge k (Module.finrank F M) with hk | hk
  · exact hmono (le_of_lt hk)
  · exact le_of_eq (by rw [hconst k (by omega), hconst (Module.finrank F M) hNd])

variable {E : Type*} [AddCommGroup E] [Module F E]

lemma orbitGen_subset_succ (act : L → (E →ₗ[F] E)) (S : Set E) (k : ℕ) :
    orbitGen act S k ⊆ orbitGen act S (k + 1) := by
  rintro v ⟨w, hw, s, hs, rfl⟩
  exact ⟨w, Nat.le_succ_of_le hw, s, hs, rfl⟩

lemma orbitFil_mono (act : L → (E →ₗ[F] E)) (S : Set E) : Monotone (orbitFil act S) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Submodule.span_mono (orbitGen_subset_succ act S k)

lemma wordAction_mem_orbitFil (act : L → (E →ₗ[F] E)) (S : Set E) (w : List L)
    {s : E} (hs : s ∈ S) (k : ℕ) (hk : w.length ≤ k) :
    wordAction act w s ∈ orbitFil act S k :=
  Submodule.subset_span ⟨w, hk, s, hs, rfl⟩

/-- One-step recursion for the reachability filtration: adding a letter to every reachable
state generates the next stage. -/
lemma orbitFil_rec (act : L → (E →ₗ[F] E)) (S : Set E) (k : ℕ) :
    orbitFil act S (k + 1) = orbitFil act S k ⊔ ⨆ ℓ, Submodule.map (act ℓ) (orbitFil act S k) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨w, hw, s, hs, rfl⟩
    cases w with
    | nil =>
      exact Submodule.mem_sup_left (wordAction_mem_orbitFil act S [] hs k (Nat.zero_le k))
    | cons ℓ w' =>
      have hw' : w'.length ≤ k := by simp only [List.length_cons] at hw; omega
      refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem ℓ ?_)
      exact Submodule.mem_map.2 ⟨wordAction act w' s, wordAction_mem_orbitFil act S w' hs k hw', rfl⟩
  · apply sup_le
    · exact orbitFil_mono act S (Nat.le_succ k)
    · apply iSup_le
      intro ℓ
      have hmap : Submodule.map (act ℓ) (orbitFil act S k)
          = Submodule.span F (act ℓ '' orbitGen act S k) := by
        rw [orbitFil, Submodule.map_span]
      rw [hmap]
      apply Submodule.span_le.mpr
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨w, hw, s, hs, rfl⟩ := hu
      exact wordAction_mem_orbitFil act S (ℓ :: w) hs (k + 1)
        (by simp only [List.length_cons]; omega)

/-- The reachability filtration reaches the full reachable orbit's span by step `dim E`:
`orbitFil act S (dim E) = span (fullOrbit act S)`. The quantitative core of `lem:findet`. -/
lemma orbitFil_eq_span [FiniteDimensional F E] (act : L → (E →ₗ[F] E)) (S : Set E) :
    orbitFil act S (Module.finrank F E) = Submodule.span F (fullOrbit act S) := by
  have hprop : ∀ k, orbitFil act S k = orbitFil act S (k + 1) →
      orbitFil act S (k + 1) = orbitFil act S (k + 1 + 1) := by
    intro k h
    rw [orbitFil_rec act S (k + 1), ← h, ← orbitFil_rec act S k]
    exact h
  have hle := chain_le_finrank (orbitFil act S) (orbitFil_mono act S) hprop
  have hsup : (⨆ k, orbitFil act S k) = orbitFil act S (Module.finrank F E) :=
    le_antisymm (iSup_le hle) (le_iSup (orbitFil act S) (Module.finrank F E))
  have hspan : Submodule.span F (fullOrbit act S) = ⨆ k, orbitFil act S k := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨w, s, hs, rfl⟩
      exact Submodule.mem_iSup_of_mem w.length
        (wordAction_mem_orbitFil act S w hs w.length (le_refl _))
    · apply iSup_le
      intro k
      apply Submodule.span_mono
      rintro v ⟨w, _, s, hs, rfl⟩
      exact ⟨w, s, hs, rfl⟩
  rw [hspan, hsup]

/-- **Finite determinacy** (`lem:findet`). Two realizations `(ax, rx, lx)` on `E_x` and
`(ay, ry, ly)` on `E_y` (same alphabet, ports) with equal behavior on every word of length
`≤ dim E_x + dim E_y` have equal behavior on all words. The joint reachable space of the
product realization is spanned by short words (`orbitFil_eq_span`), and the behavior
difference is a linear functional on it that vanishes on the short-word generators. -/
theorem findet {Ex Ey : Type*}
    [AddCommGroup Ex] [Module F Ex] [FiniteDimensional F Ex]
    [AddCommGroup Ey] [Module F Ey] [FiniteDimensional F Ey]
    (ax : L → (Ex →ₗ[F] Ex)) (rx : Inp → Ex) (lx : Out → (Ex →ₗ[F] F))
    (ay : L → (Ey →ₗ[F] Ey)) (ry : Inp → Ey) (ly : Out → (Ey →ₗ[F] F))
    (hagree : ∀ w : List L, w.length ≤ Module.finrank F Ex + Module.finrank F Ey →
      ∀ i o, behavior ax rx lx w i o = behavior ay ry ly w i o) :
    ∀ w i o, behavior ax rx lx w i o = behavior ay ry ly w i o := by
  set pAct : L → ((Ex × Ey) →ₗ[F] (Ex × Ey)) := fun ℓ => (ax ℓ).prodMap (ay ℓ) with hpAct
  set S : Set (Ex × Ey) := Set.range (fun i => ((rx i, ry i) : Ex × Ey)) with hS
  have wa_prod : ∀ (w : List L) (p : Ex × Ey),
      wordAction pAct w p = (wordAction ax w p.1, wordAction ay w p.2) := by
    intro w
    induction w with
    | nil => intro p; rfl
    | cons ℓ w ih =>
      intro p
      change pAct ℓ (wordAction pAct w p)
        = (wordAction ax (ℓ :: w) p.1, wordAction ay (ℓ :: w) p.2)
      rw [ih p, hpAct]
      rfl
  intro w i o
  set Λ : (Ex × Ey) →ₗ[F] F :=
    (lx o).comp (LinearMap.fst F Ex Ey) - (ly o).comp (LinearMap.snd F Ex Ey) with hΛ
  have hΛ_state : ∀ (w : List L) (i : Inp),
      Λ (wordAction pAct w ((rx i, ry i)))
        = behavior ax rx lx w i o - behavior ay ry ly w i o := by
    intro w i
    have hx : (wordAction pAct w ((rx i, ry i))).1 = wordAction ax w (rx i) := by rw [wa_prod]
    have hy : (wordAction pAct w ((rx i, ry i))).2 = wordAction ay w (ry i) := by rw [wa_prod]
    rw [hΛ]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, hx, hy, behavior]
  set d := Module.finrank F (Ex × Ey) with hd
  have hdprod : d = Module.finrank F Ex + Module.finrank F Ey := by rw [hd, Module.finrank_prod]
  have hΛ_vanish : orbitFil pAct S d ≤ LinearMap.ker Λ := by
    rw [orbitFil]
    apply Submodule.span_le.mpr
    rintro v ⟨u, hu, p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := hp
    rw [SetLike.mem_coe, LinearMap.mem_ker, hΛ_state]
    rw [hagree u (by rw [← hdprod]; exact hu) j o, sub_self]
  have hmem : wordAction pAct w ((rx i, ry i)) ∈ orbitFil pAct S d := by
    have h1 : wordAction pAct w ((rx i, ry i)) ∈ Submodule.span F (fullOrbit pAct S) :=
      Submodule.subset_span ⟨w, (rx i, ry i), ⟨i, rfl⟩, rfl⟩
    rwa [← orbitFil_eq_span pAct S, ← hd] at h1
  have hzero : Λ (wordAction pAct w ((rx i, ry i))) = 0 := by
    have h2 := hΛ_vanish hmem
    rwa [LinearMap.mem_ker] at h2
  rw [hΛ_state w i] at hzero
  exact sub_eq_zero.mp hzero

/-!
## Minimal realization uniqueness (`thm:linear-descent`)

This section formalizes `thm:linear-descent`: two minimal (reachable + observable)
realizations with equal behavior are related by a *unique* linear isomorphism intertwining
the ports and letters. Reachability and observability are the two clauses of `def:minimal`
(the observability half, skipped in the inertia file, is modeled here as the paper requires).

The construction is the classical graph argument. The joint reachable subspace
`V ⊆ E_x × E_y` (spanned by the joint states of the product realization) is the graph of the
desired map: equal behavior makes the behavior-difference functionals vanish on `V`, so both
coordinate projections `V → E_x` and `V → E_y` are isomorphisms (surjective by reachability,
injective by observability), and `S` is their composite. Uniqueness is Schützenberger's
observation that any intertwiner is pinned on the reachable span, which is everything.

Faithfulness deltas: the manuscript additionally records that `S` is block-diagonal across
levels and lists which tensors it does and does not transport; those are structural remarks
about the specific tower letters, not part of the universal-property statement, and are not
modeled. The transported data (`S R_x = R_y`, `S M^x = M^y S`, `L_y S = L_x`) is exactly the
three conjuncts proved here.
-/

/-- **Reachability** of a realization (`def:minimal`): the letter orbit of the input ports
spans the state space. -/
def Reachable' {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) (init : Inp → E) : Prop :=
  Submodule.span F (fullOrbit act (Set.range init)) = ⊤

/-- **Observability** of a realization (`def:minimal`): no nonzero vector is annihilated by
all `L·M_w`. -/
def Observable {E : Type*} [AddCommGroup E] [Module F E]
    (act : L → (E →ₗ[F] E)) (out : Out → (E →ₗ[F] F)) : Prop :=
  ∀ v : E, (∀ (w : List L) (o : Out), out o (wordAction act w v) = 0) → v = 0

/-- Any linear map intertwining the ports and letters sends a word run from an input port to
the corresponding word run in the target realization. The pin behind uniqueness. -/
lemma wordAction_intertwine {Ex Ey : Type*} [AddCommGroup Ex] [Module F Ex]
    [AddCommGroup Ey] [Module F Ey]
    (ax : L → (Ex →ₗ[F] Ex)) (rx : Inp → Ex) (ay : L → (Ey →ₗ[F] Ey)) (ry : Inp → Ey)
    (T : Ex →ₗ[F] Ey) (hinit : ∀ i, T (rx i) = ry i)
    (hint : ∀ (ℓ : L) (v : Ex), T (ax ℓ v) = ay ℓ (T v)) :
    ∀ (w : List L) (i : Inp), T (wordAction ax w (rx i)) = wordAction ay w (ry i) := by
  intro w
  induction w with
  | nil => intro i; exact hinit i
  | cons ℓ w ih =>
    intro i
    change T (ax ℓ (wordAction ax w (rx i))) = ay ℓ (wordAction ay w (ry i))
    rw [hint, ih]

/-- **Linear minimal descent** (`thm:linear-descent`). Two minimal realizations with equal
behavior are related by a unique linear isomorphism intertwining the ports and letters. -/
theorem linear_descent {Ex Ey : Type*} [AddCommGroup Ex] [Module F Ex]
    [AddCommGroup Ey] [Module F Ey]
    (ax : L → (Ex →ₗ[F] Ex)) (rx : Inp → Ex) (lx : Out → (Ex →ₗ[F] F))
    (ay : L → (Ey →ₗ[F] Ey)) (ry : Inp → Ey) (ly : Out → (Ey →ₗ[F] F))
    (hbeh : ∀ w i o, behavior ax rx lx w i o = behavior ay ry ly w i o)
    (hrx : Reachable' ax rx) (hox : Observable ax lx)
    (hry : Reachable' ay ry) (hoy : Observable ay ly) :
    ∃! S : Ex ≃ₗ[F] Ey,
      (∀ i, S (rx i) = ry i) ∧
      (∀ (ℓ : L) (v : Ex), S (ax ℓ v) = ay ℓ (S v)) ∧
      (∀ (o : Out) (v : Ex), ly o (S v) = lx o v) := by
  have hrx' : Submodule.span F (fullOrbit ax (Set.range rx)) = ⊤ := hrx
  have hry' : Submodule.span F (fullOrbit ay (Set.range ry)) = ⊤ := hry
  set pA : L → ((Ex × Ey) →ₗ[F] (Ex × Ey)) := fun ℓ => (ax ℓ).prodMap (ay ℓ) with hpA
  set seed : Set (Ex × Ey) := Set.range (fun i => ((rx i, ry i) : Ex × Ey)) with hseed
  have hpAcoe : ∀ (ℓ : L) (q : Ex × Ey), pA ℓ q = (ax ℓ q.1, ay ℓ q.2) := by
    intro ℓ q; simp only [hpA, LinearMap.prodMap_apply]
  have wa : ∀ (w : List L) (p : Ex × Ey),
      wordAction pA w p = (wordAction ax w p.1, wordAction ay w p.2) := by
    intro w
    induction w with
    | nil => intro p; rfl
    | cons ℓ w ih =>
      intro p
      change pA ℓ (wordAction pA w p)
        = (wordAction ax (ℓ :: w) p.1, wordAction ay (ℓ :: w) p.2)
      rw [ih p, hpA]; rfl
  set V : Submodule F (Ex × Ey) := Submodule.span F (fullOrbit pA seed) with hV
  -- behavior-difference functionals vanish on the joint reachable space
  have hΛ : ∀ (o : Out), ∀ p ∈ V, lx o p.1 = ly o p.2 := by
    intro o
    have hsub : V ≤ LinearMap.ker ((lx o).comp (LinearMap.fst F Ex Ey)
        - (ly o).comp (LinearMap.snd F Ex Ey)) := by
      rw [hV]
      apply Submodule.span_le.mpr
      rintro v ⟨w, s, ⟨i, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hc1 : (wordAction pA w ((rx i, ry i) : Ex × Ey)).1 = wordAction ax w (rx i) := by
        rw [wa]
      have hc2 : (wordAction pA w ((rx i, ry i) : Ex × Ey)).2 = wordAction ay w (ry i) := by
        rw [wa]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, hc1, hc2]
      exact sub_eq_zero.mpr (hbeh w i o)
    intro p hp
    have hker := hsub hp
    rw [LinearMap.mem_ker] at hker
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply] at hker
    exact sub_eq_zero.mp hker
  -- the joint reachable space is closed under the product letter action
  have hVmap : ∀ ℓ, Submodule.map (pA ℓ) V ≤ V := by
    intro ℓ
    rw [hV, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨q, ⟨w, s, hs, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨ℓ :: w, s, hs, rfl⟩
  have hVword : ∀ (u : List L) (p : Ex × Ey), p ∈ V → wordAction pA u p ∈ V := by
    intro u
    induction u with
    | nil => intro p hp; exact hp
    | cons ℓ u ih =>
      intro p hp
      change pA ℓ (wordAction pA u p) ∈ V
      exact hVmap ℓ (Submodule.mem_map.2 ⟨wordAction pA u p, ih p hp, rfl⟩)
  -- injectivity inputs: a joint vector with a zero coordinate is zero
  have zero_snd : ∀ p ∈ V, p.1 = 0 → p = 0 := by
    intro p hp hp1
    have hb : p.2 = 0 := by
      apply hoy
      intro u o
      have hmem : wordAction pA u p ∈ V := hVword u p hp
      have hc1 : (wordAction pA u p).1 = wordAction ax u p.1 := by rw [wa]
      have hc2 : (wordAction pA u p).2 = wordAction ay u p.2 := by rw [wa]
      have hvan := hΛ o (wordAction pA u p) hmem
      rw [hc1, hc2, hp1, map_zero, map_zero] at hvan
      exact hvan.symm
    exact Prod.ext_iff.mpr ⟨hp1, hb⟩
  have zero_fst : ∀ p ∈ V, p.2 = 0 → p = 0 := by
    intro p hp hp2
    have ha : p.1 = 0 := by
      apply hox
      intro u o
      have hmem : wordAction pA u p ∈ V := hVword u p hp
      have hc1 : (wordAction pA u p).1 = wordAction ax u p.1 := by rw [wa]
      have hc2 : (wordAction pA u p).2 = wordAction ay u p.2 := by rw [wa]
      have hvan := hΛ o (wordAction pA u p) hmem
      rw [hc1, hc2, hp2, map_zero, map_zero] at hvan
      exact hvan
    exact Prod.ext_iff.mpr ⟨ha, hp2⟩
  -- the two coordinate projections restricted to V are bijective
  have fst_inj : Function.Injective ((LinearMap.fst F Ex Ey).comp V.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    exact Subtype.ext (zero_snd z.1 z.2 hz)
  have snd_inj : Function.Injective ((LinearMap.snd F Ex Ey).comp V.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    exact Subtype.ext (zero_fst z.1 z.2 hz)
  have fst_surj : Function.Surjective ((LinearMap.fst F Ex Ey).comp V.subtype) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype,
      ← top_le_iff, ← hrx']
    apply Submodule.span_le.mpr
    rintro v ⟨w, s, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe]
    refine Submodule.mem_map.2 ⟨wordAction pA w ((rx i, ry i) : Ex × Ey), ?_, ?_⟩
    · exact Submodule.subset_span ⟨w, (rx i, ry i), ⟨i, rfl⟩, rfl⟩
    · rw [LinearMap.fst_apply, wa]
  have snd_surj : Function.Surjective ((LinearMap.snd F Ex Ey).comp V.subtype) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype,
      ← top_le_iff, ← hry']
    apply Submodule.span_le.mpr
    rintro v ⟨w, s, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe]
    refine Submodule.mem_map.2 ⟨wordAction pA w ((rx i, ry i) : Ex × Ey), ?_, ?_⟩
    · exact Submodule.subset_span ⟨w, (rx i, ry i), ⟨i, rfl⟩, rfl⟩
    · rw [LinearMap.snd_apply, wa]
  -- assemble the isomorphism as the composite of the coordinate equivalences
  let fstE : V ≃ₗ[F] Ex := LinearEquiv.ofBijective _ ⟨fst_inj, fst_surj⟩
  let sndE : V ≃ₗ[F] Ey := LinearEquiv.ofBijective _ ⟨snd_inj, snd_surj⟩
  have hfstE : ∀ z : V, fstE z = (z : Ex × Ey).1 := fun _ => rfl
  have hsndE : ∀ z : V, sndE z = (z : Ex × Ey).2 := fun _ => rfl
  let S : Ex ≃ₗ[F] Ey := fstE.symm.trans sndE
  have hgraph : ∀ (p : Ex × Ey), p ∈ V → S p.1 = p.2 := by
    intro p hp
    have hz : fstE ⟨p, hp⟩ = p.1 := rfl
    have hsymm : fstE.symm p.1 = ⟨p, hp⟩ := by rw [← hz, fstE.symm_apply_apply]
    change sndE (fstE.symm p.1) = p.2
    rw [hsymm]
    exact hsndE ⟨p, hp⟩
  -- the three transported properties
  have Sinit : ∀ i, S (rx i) = ry i := by
    intro i
    have hpi : ((rx i, ry i) : Ex × Ey) ∈ V :=
      Submodule.subset_span ⟨[], (rx i, ry i), ⟨i, rfl⟩, rfl⟩
    exact hgraph (rx i, ry i) hpi
  have Sint : ∀ (ℓ : L) (v : Ex), S (ax ℓ v) = ay ℓ (S v) := by
    intro ℓ v
    obtain ⟨z, hz⟩ := fst_surj v
    have hzV : (z : Ex × Ey) ∈ V := z.2
    have hv : (z : Ex × Ey).1 = v := hz
    have hpe : pA ℓ (z : Ex × Ey) ∈ V :=
      hVmap ℓ (Submodule.mem_map.2 ⟨(z : Ex × Ey), hzV, rfl⟩)
    have hcoe1 : (pA ℓ (z : Ex × Ey)).1 = ax ℓ ((z : Ex × Ey).1) := by rw [hpAcoe]
    have hcoe2 : (pA ℓ (z : Ex × Ey)).2 = ay ℓ ((z : Ex × Ey).2) := by rw [hpAcoe]
    have e1 : S ((pA ℓ (z : Ex × Ey)).1) = (pA ℓ (z : Ex × Ey)).2 := hgraph _ hpe
    have e2 : S ((z : Ex × Ey).1) = (z : Ex × Ey).2 := hgraph _ hzV
    calc S (ax ℓ v) = S (ax ℓ ((z : Ex × Ey).1)) := by rw [hv]
      _ = S ((pA ℓ (z : Ex × Ey)).1) := by rw [hcoe1]
      _ = (pA ℓ (z : Ex × Ey)).2 := e1
      _ = ay ℓ ((z : Ex × Ey).2) := hcoe2
      _ = ay ℓ (S ((z : Ex × Ey).1)) := by rw [e2]
      _ = ay ℓ (S v) := by rw [hv]
  have Sout : ∀ (o : Out) (v : Ex), ly o (S v) = lx o v := by
    intro o v
    obtain ⟨z, hz⟩ := fst_surj v
    have hzV : (z : Ex × Ey) ∈ V := z.2
    have hv : (z : Ex × Ey).1 = v := hz
    have e2 : S ((z : Ex × Ey).1) = (z : Ex × Ey).2 := hgraph _ hzV
    have hlx : lx o ((z : Ex × Ey).1) = ly o ((z : Ex × Ey).2) := hΛ o (z : Ex × Ey) hzV
    calc ly o (S v) = ly o (S ((z : Ex × Ey).1)) := by rw [hv]
      _ = ly o ((z : Ex × Ey).2) := by rw [e2]
      _ = lx o ((z : Ex × Ey).1) := hlx.symm
      _ = lx o v := by rw [hv]
  refine ⟨S, ⟨Sinit, Sint, Sout⟩, ?_⟩
  rintro T ⟨hTi, hTint, _hTo⟩
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on hrx'
  rintro v ⟨w, s, ⟨i, rfl⟩, rfl⟩
  have hT := wordAction_intertwine ax rx ay ry (T : Ex →ₗ[F] Ey) hTi hTint w i
  have hS := wordAction_intertwine ax rx ay ry (S : Ex →ₗ[F] Ey) Sinit Sint w i
  rw [hT, hS]

end Realizations

end Selection
