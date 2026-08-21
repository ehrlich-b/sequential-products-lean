/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Logic.Relation

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — complex-type globalization (`thm:complex`, global step)

This module discharges the **global** half of the complex branch of `mthm:master`
(`landing/papers/twist-normal-form/main.tex`, `thm:complex`): the per-frame parameter
`t_F` produced by `Branches/Complex` (`thm:complex`, "one parameter per frame") is in
fact **one global `t`**, so on `Hₙ(ℂ)` the product is a single Liu–Wu twist
`a•b = a^{1/2+it} b a^{1/2−it}`.

## What is proved (`thm:complex`, global step)

The paper's globalization has three moves; all are Lean theorems here:

1. **`real_character_unique`** — *ledger reduction: axiom A3 becomes a theorem.* Two
   continuous real characters of `ℝ` agreeing on an open interval are equal:
   `exp(i α x) = exp(i β x)` for all `x` in `(a,b)` (with `a < b`) forces `α = β`, with
   **no `2π` ambiguity**. The paper's "uniqueness of continuous characters of `ℝ`
   (equivalently, differentiating at `x = 0`)". Proved from Mathlib's `Complex.exp`
   derivative machinery (`HasDerivAt.cexp`, eventual-constancy), so the classical
   axiom `character_of_Rn` of the PLAN ledger is **not needed** — Globalization
   introduces **zero custom axioms**.

2. **`const_of_adjacent`** — the graph-theoretic core: a per-frame real assignment `t`
   that is constant across every adjacent pair is globally constant on a connected
   adjacency graph. This turns the adjacent-frame overlap `t_F = t_{F'}` into a single
   global `t` (`Relation.ReflTransGen` induction).

3. **`ComplexGlobalizationData.global_t`** — the capstone `Master` consumes: assembling
   1 + 2 through the cross-coherence overlap (`thm:complex`,
   `crossCoherence_single_scalar`: adjacent frames' induced `U(1)` characters agree on
   an open interval because the *same* comparison map `Θ_a`, with `a` scalar on the
   shared rank-two block, computes both — `lem:coalescence` fixing `J₂(q)` pointwise).

## Frame connectivity (`lem:frame-connectivity`)

The connectivity of the frame graph (maximal Jordan frames of `Mₙ(ℂ)` adjacent when
they share `n−2` atoms) is **proved in the paper** (`lem:frame-connectivity`), so it is
**never an axiom here**. Two honest layers:

* **The induction is machine-checked.** `connected_of_reducing` proves the paper's
  connectivity *reasoning*: if every `F ≠ G` admits an adjacency move strictly reducing
  a `ℕ`-measure toward `G`, the graph is connected. This is exactly the paper's "one
  2-plane rotation reduces the support by one; induct" argument, with `sorry`-free
  strong induction.
* **One geometric fact remains assumed**, cleanly located: that the reducing rotation
  move exists in `ℂⁿ` (the `hmove` hypothesis of `connected_of_reducing`; the paper's
  "rotate `{v_i,v_j}` toward `u`"). A concrete `ℂⁿ`-orthonormal-frame formalization is
  deferred (unitary orbits + phase quotient are heavy); until then the `connected` field
  of `ComplexGlobalizationData` is supplied via `connected_of_reducing` + this one
  located move, or as an explicit hypothesis by the instantiating `Master` assembly.

Carrying the residual as a structure field / located hypothesis is within the mandate;
axiomatizing it would not be, and nothing here is a `sorry`.

## Interface for `Master` / binding to `Branches/Complex`

`ComplexGlobalizationData Frame` is the Master-facing seam. The `Branches/Complex`
capstone (`complex_perFrame_tF`: the per-frame parameter `t_F` with its adjacent-frame
overlap) supplies the `t`, `Adj`, and `overlap` fields; `lem:frame-connectivity`
supplies `connected`. `global_t` then yields the single global `t`. If the exact
`complex_perFrame_tF` signature differs, only a thin field-packaging adapter changes;
`global_t` is stable.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*,
  `thm:complex`, `lem:frame-connectivity`.
-/

noncomputable section

namespace MasterTheorem.Globalization

/-! ## 1. Character uniqueness (`thm:complex`; PLAN ledger A3, now a theorem) -/

/-- **`thm:complex` character uniqueness (PROVED; ledger A3 → theorem).**
Two continuous real characters of `ℝ` that agree on an open interval are equal:
if `exp(i α x) = exp(i β x)` for every `x ∈ (a,b)` with `a < b`, then `α = β`. No `2π`
ambiguity (the paper differentiates at a point of the interval). Scope precision
(adversarial review 2026-07-15): this is the **uniqueness/frequency-rigidity half**
only — the exponential form is the statement's shape, not derived here; the structure
theorem "every continuous character of `ℝⁿ` is `e^{i⟨c,r⟩}`" is not proved in this
tree (its use enters through the branch model fields). It eliminates the need for the
formerly planned custom axiom `character_of_Rn`. -/
theorem real_character_unique {α β a b : ℝ} (hab : a < b)
    (h : ∀ x ∈ Set.Ioo a b, Complex.exp ((α : ℂ) * x * Complex.I) = Complex.exp ((β : ℂ) * x * Complex.I)) :
    α = β := by
  set s : ℝ := α - β with hs
  -- On the interval the difference character is trivial: `exp(i s x) = 1`.
  have h1 : ∀ x ∈ Set.Ioo a b, Complex.exp ((s : ℂ) * x * Complex.I) = 1 := by
    intro x hx
    have hxeq := h x hx
    have hrw : ((s : ℂ) * x * Complex.I) = ((α : ℂ) * x * Complex.I) - ((β : ℂ) * x * Complex.I) := by
      push_cast [hs]; ring
    rw [hrw, Complex.exp_sub, hxeq, div_self (Complex.exp_ne_zero _)]
  -- Differentiate the (eventually constant) character at the interval midpoint.
  have hxmem : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  set x₀ : ℝ := (a + b) / 2 with hx₀
  have hev : (fun x : ℝ => Complex.exp ((s : ℂ) * x * Complex.I)) =ᶠ[nhds x₀] (fun _ => (1 : ℂ)) := by
    filter_upwards [Ioo_mem_nhds hxmem.1 hxmem.2] with x hx
    exact h1 x hx
  have hd0 : HasDerivAt (fun x : ℝ => Complex.exp ((s : ℂ) * x * Complex.I)) 0 x₀ :=
    (hasDerivAt_const x₀ (1 : ℂ)).congr_of_eventuallyEq hev
  have hofReal : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x₀ := by
    have := Complex.ofRealCLM.hasDerivAt (x := x₀)
    simpa using! this
  have hd1 : HasDerivAt (fun x : ℝ => Complex.exp ((s : ℂ) * ↑x * Complex.I))
      (Complex.exp ((s : ℂ) * ↑x₀ * Complex.I) * ((s : ℂ) * 1 * Complex.I)) x₀ :=
    ((hofReal.const_mul (s : ℂ)).mul_const Complex.I).cexp
  have hzero : Complex.exp ((s : ℂ) * ↑x₀ * Complex.I) * ((s : ℂ) * 1 * Complex.I) = 0 :=
    hd1.unique hd0
  have hI : ((s : ℂ) * 1 * Complex.I) = 0 := by
    rcases mul_eq_zero.mp hzero with he | hsi
    · exact absurd he (Complex.exp_ne_zero _)
    · exact hsi
  have hs0 : (s : ℂ) = 0 := by
    have hh : (s : ℂ) * Complex.I = 0 := by rw [mul_one] at hI; exact hI
    rcases mul_eq_zero.mp hh with h' | h'
    · exact h'
    · exact absurd h' Complex.I_ne_zero
  have hs00 : s = 0 := by exact_mod_cast hs0
  linarith

/-! ## 2. The connectivity kernel (`thm:complex`, global step) -/

variable {Frame : Type*}

/-- Symmetric one-step frame adjacency: `F` and `G` are adjacent, in either direction. -/
def SymmStep (Adj : Frame → Frame → Prop) (a b : Frame) : Prop := Adj a b ∨ Adj b a

/-- **Single global parameter (PROVED, abstract kernel).** A per-frame real assignment
`t` constant across every adjacent pair is constant along any connectivity walk. This
is the graph-theoretic content of `thm:complex`'s globalization: the adjacent-frame
overlap `t_F = t_{F'}`, chained along a `lem:frame-connectivity` walk, gives one global
value. -/
theorem const_of_adjacent {Adj : Frame → Frame → Prop} {t : Frame → ℝ}
    (h : ∀ F G, Adj F G → t F = t G) {F G : Frame}
    (hconn : Relation.ReflTransGen (SymmStep Adj) F G) : t F = t G := by
  induction hconn with
  | refl => rfl
  | tail _ hstep ih =>
      rcases hstep with hfwd | hbwd
      · exact ih.trans (h _ _ hfwd)
      · exact ih.trans (h _ _ hbwd).symm

/-- **`lem:frame-connectivity` induction skeleton (PROVED).** If, relative to a target
frame `G`, every frame `F ≠ G` admits an adjacency move to some `F'` that strictly
reduces a `ℕ`-valued measure `μ · G`, then every frame connects to `G`. This is the
machine-checked form of the paper's connectivity induction: "if `m ≥ 2` coefficients
are nonzero, one 2-plane rotation reduces `m` by one; after `≤ n−1` moves the atom is
fixed; induct." **The graph-theoretic reasoning of `lem:frame-connectivity` is thereby
certified**; the only content left assumed is the single *geometric* fact `hmove` (the
reducing rotation exists in `ℂⁿ`), which is where `Master`'s concrete `Frame` discharges
it. This shrinks the assumed part of `lem:frame-connectivity` from "the whole graph is
connected" to "one located 2-plane-rotation move exists". -/
theorem connected_of_reducing {Adj : Frame → Frame → Prop} {μ : Frame → Frame → ℕ}
    (hmove : ∀ F G, F ≠ G → ∃ F', Adj F F' ∧ μ F' G < μ F G) (G : Frame) :
    ∀ F, Relation.ReflTransGen (SymmStep Adj) F G := by
  have key : ∀ n F, μ F G = n → Relation.ReflTransGen (SymmStep Adj) F G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro F hFn
      by_cases hFG : F = G
      · subst hFG; exact Relation.ReflTransGen.refl
      · obtain ⟨F', hAdj, hlt⟩ := hmove F G hFG
        exact Relation.ReflTransGen.head (Or.inl hAdj) (IH (μ F' G) (hFn ▸ hlt) F' rfl)
  intro F; exact key (μ F G) F rfl

/-! ## 3. The Master-facing data and capstone (`thm:complex`, global step) -/

/-- **Complex-globalization data** — the seam `Master` consumes and `Branches/Complex`
supplies. For the complex type `Hₙ(ℂ)`, `n ≥ 3`:

* `t` — the per-frame twist parameter `t_F` (`Branches/Complex.complex_perFrame_tF`).
* `Adj` — the frame-adjacency relation (frames sharing `n−2` atoms, i.e. differing by
  a rotation inside a rank-two block fixing a third projection).
* `connected` — `lem:frame-connectivity` (paper-proved; carried as an **explicit
  hypothesis**, never an axiom): the adjacency graph is connected.
* `overlap` — `thm:complex` `crossCoherence_single_scalar`: adjacent frames' induced
  `U(1)` characters `x ↦ e^{i t_F x}` agree on an open interval of
  `x = log λ − log λ_k`, because the *same* comparison map `Θ_a` (with `a` scalar on
  the shared rank-two block, so `Θ_a` fixes `J₂(q)` pointwise by `lem:coalescence`)
  computes both frames' actions on the cross-coherence space. -/
structure ComplexGlobalizationData (Frame : Type*) where
  /-- The per-frame twist parameter `t_F`. -/
  t : Frame → ℝ
  /-- Frame adjacency (share `n−2` atoms). -/
  Adj : Frame → Frame → Prop
  /-- `lem:frame-connectivity` (paper-proved; explicit hypothesis, not an axiom). -/
  connected : ∀ F G, Relation.ReflTransGen (SymmStep Adj) F G
  /-- `crossCoherence_single_scalar`: adjacent frames' characters agree on an open
      interval. -/
  overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧
      ∀ x ∈ Set.Ioo a b,
        Complex.exp ((t F : ℂ) * x * Complex.I) = Complex.exp ((t G : ℂ) * x * Complex.I)

namespace ComplexGlobalizationData

variable {Frame : Type*}

/-- **Adjacent-frame equality (PROVED).** For adjacent frames the twist parameters are
exactly equal, `t_F = t_{F'}` — the cross-coherence overlap fed through
`real_character_unique`. This is the `thm:complex` step
"`e^{i t_F x} = e^{i t_{F'} x}` on an interval ⟹ `t_F = t_{F'}` exactly". -/
theorem adjacent_eq (D : ComplexGlobalizationData Frame) {F G : Frame} (hFG : D.Adj F G) :
    D.t F = D.t G := by
  obtain ⟨a, b, hab, hx⟩ := D.overlap F G hFG
  exact real_character_unique hab hx

/-- **`thm:complex` (global step, capstone): one global `t`.** Every frame carries the
same twist parameter as a fixed reference frame `F₀`. In the paper's intended
instance — combined with the per-frame `Θ_{a(r)} = Ad_{a(r)^{it_F}}` reading of
`Branches/Complex` — this yields the single global `t` of `mthm:master`'s complex
case, `a•b = a^{1/2+it} b a^{1/2−it}`; the Lean statement is exactly the
frame-independence of `t`. Rests on
`real_character_unique` (no `2π` ambiguity) and the paper-proved frame connectivity
(the `connected` field), with **no custom axioms**. -/
theorem global_t (D : ComplexGlobalizationData Frame) (F₀ : Frame) :
    ∀ F, D.t F = D.t F₀ := fun F =>
  const_of_adjacent (fun _ _ h => D.adjacent_eq h) (D.connected F F₀)

/-- The single global constant `t`, as an element of `ℝ` (value at any reference
frame). `global_t` certifies it is frame-independent. -/
def globalT (D : ComplexGlobalizationData Frame) [Nonempty Frame] : ℝ :=
  D.t (Classical.arbitrary Frame)

/-- `globalT` is the value at *every* frame (frame independence, the payoff of
`thm:complex`). -/
theorem t_eq_globalT (D : ComplexGlobalizationData Frame) [Nonempty Frame] (F : Frame) :
    D.t F = D.globalT :=
  D.global_t (Classical.arbitrary Frame) F

end ComplexGlobalizationData

end MasterTheorem.Globalization
