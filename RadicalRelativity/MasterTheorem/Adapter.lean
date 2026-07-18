/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Globalization
import RadicalRelativity.MasterTheorem.Branches.Complex

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — complex-type adapter (`thm:complex`, assembly seam)

This module binds the complex branch's per-frame output (`Branches/Complex`,
`complex_perFrame_rho`) to the globalization capstone (`Globalization`,
`ComplexGlobalizationData.global_t`), so `Master` can assemble the complex case of
`mthm:master` from one call. It imports the two lanes read-only and **modifies neither**.

## What is genuinely proved here

* **`perFrameTwist` / `perFrameTwist_spec`** — the per-frame twist `t_F` extracted as a
  concrete real number from the torus-model coupling via `complex_perFrame_rho`
  (`Branches/Complex`), together with its defining property
  `S.ρ_{ij}(S.dχ r) = (t_F(r_i − r_j))·J`. This is the "per-frame `t_F` fills `t`" step,
  wired to the real lemma (`Classical.choose` + `choose_spec`), no re-derivation.
* **`complex_global_twist`** — the assembly: given per-frame couplings (each yielding its
  `t_F` via `perFrameTwist`), a frame adjacency, its connectivity, and the cross-coherence
  overlap, there is a **single global** `t_F` (every frame's parameter equals it). Proved
  by packaging into `ComplexGlobalizationData` and applying `global_t` (whose only
  ingredients are the proved `real_character_unique` and the connectivity kernel — no
  custom axioms).

## Located hypotheses (auditor-visible, same standard as §2 of `PLAN.md`)

Two inputs are carried as explicit hypotheses of `complex_global_twist`, not proved here:

* **`overlap`** — the cross-coherence character equality: for adjacent frames `F, G`,
  the induced `U(1)` characters `x ↦ exp(i t_F x)` and `x ↦ exp(i t_G x)` agree on an
  open interval of `x = log λ − log λ_k`. This is the `crossCoherence_single_scalar`
  content, discharged by the paper's route (`Coalescence.coalescence_J2q`: for `a` scalar
  on `range(q)`, `Θ_a` fixes `J₂(q)` pointwise, so the *same* `Θ_a` computes both frames'
  actions on the cross-coherence space). The operator-level fact routes through
  `coalescence_J2q`; its final translation to the *character* level is the same
  exp/Lie step deferred for `coalescence_diff` (chain-completeness mandate), so it is
  carried here as the located `overlap` hypothesis rather than re-proved.
* **`connected`** — `lem:frame-connectivity` (paper-proved), the disclosed hypothesis of
  `Globalization` (`connected_of_reducing` machine-checks its induction; the geometric
  2-plane-rotation move `hmove` is the residual, discharged when `Master` builds a
  concrete `Frame`).

Everything downstream of these two — the collapse to one global constant — is proved.

## References

* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*,
  `thm:complex` (per-frame + global steps), `lem:coalescence`, `lem:frame-connectivity`.
-/

noncomputable section

open scoped InnerProductSpace
open MasterTheorem.Globalization

namespace MasterTheorem

variable {n : ℕ} {Stab : Type*} [AddCommGroup Stab] [Module ℝ Stab]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Per-frame twist, wired to `complex_perFrame_rho` -/

/-- **Per-frame twist `t_F` (`thm:complex`, per-frame).** The single real parameter of a
frame, extracted from the torus-model coupling by `complex_perFrame_rho`
(`Branches/Complex`). `perFrameTwist_spec` records its defining property. -/
noncomputable def perFrameTwist (S : StabilizerCoupling n Stab V) (J : V →ₗ[ℝ] V) (hJ : J ≠ 0)
    (c : Fin n → Fin n → ℝ)
    (hmodel : ∀ i j (r : Fin n → ℝ),
      S.ρ i j (S.dχ r) = ((∑ l, c i l * r l) - (∑ l, c j l * r l)) • J) : ℝ :=
  (complex_perFrame_rho S J hJ c hmodel).choose

/-- The defining property of `perFrameTwist`: the block action is `(t_F(r_i − r_j))·J`
on every block (`Branches/Complex.complex_perFrame_rho`, `thm:complex` per-frame). -/
theorem perFrameTwist_spec (S : StabilizerCoupling n Stab V) (J : V →ₗ[ℝ] V) (hJ : J ≠ 0)
    (c : Fin n → Fin n → ℝ)
    (hmodel : ∀ i j (r : Fin n → ℝ),
      S.ρ i j (S.dχ r) = ((∑ l, c i l * r l) - (∑ l, c j l * r l)) • J) :
    ∀ i j (r : Fin n → ℝ),
      S.ρ i j (S.dχ r) = (perFrameTwist S J hJ c hmodel * (r i - r j)) • J :=
  (complex_perFrame_rho S J hJ c hmodel).choose_spec

/-! ## The assembly: one global twist -/

/-- **`thm:complex` (complex-case assembly): one global `t`.** For a family of frames,
each carrying a torus-model coupling `S F` (with generator `J`, character matrix `c F`,
model `hmodel F`) so its per-frame twist is `perFrameTwist (S F) …`, a frame adjacency
`Adj` that is `connected` (`lem:frame-connectivity`) and whose adjacent pairs satisfy the
cross-coherence `overlap`, there is a single global `t_F` equal to every frame's
parameter. In the paper's intended instance this is `a•b = a^{1/2+it} b a^{1/2−it}`
with one global `t`; the Lean statement is exactly the constancy of the extracted
per-frame parameters.

Proof: `perFrameTwist` supplies each frame's parameter (via `complex_perFrame_rho`); the
four data package a `ComplexGlobalizationData`; `global_t` collapses them (through the
proved `real_character_unique` — no `2π` ambiguity — and the connectivity kernel).
`overlap` and `connected` are the located hypotheses documented in the module header. -/
theorem complex_global_twist {Frame : Type*} [Nonempty Frame]
    (S : Frame → StabilizerCoupling n Stab V) (J : V →ₗ[ℝ] V) (hJ : J ≠ 0)
    (c : Frame → (Fin n → Fin n → ℝ))
    (hmodel : ∀ F, ∀ i j (r : Fin n → ℝ),
      (S F).ρ i j ((S F).dχ r) = ((∑ l, c F i l * r l) - (∑ l, c F j l * r l)) • J)
    (Adj : Frame → Frame → Prop)
    (connected : ∀ F G, Relation.ReflTransGen (SymmStep Adj) F G)
    (overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧ ∀ x ∈ Set.Ioo a b,
        Complex.exp ((perFrameTwist (S F) J hJ (c F) (hmodel F) : ℂ) * x * Complex.I)
          = Complex.exp ((perFrameTwist (S G) J hJ (c G) (hmodel G) : ℂ) * x * Complex.I)) :
    ∃ tG : ℝ, ∀ F, perFrameTwist (S F) J hJ (c F) (hmodel F) = tG := by
  let D : ComplexGlobalizationData Frame :=
    { t := fun F => perFrameTwist (S F) J hJ (c F) (hmodel F)
      Adj := Adj
      connected := connected
      overlap := overlap }
  exact ⟨D.globalT, fun F => D.t_eq_globalT F⟩

/-- **Thin generic entry point.** If a per-frame parameter `t` already has the
cross-coherence overlap on a connected frame graph, it is globally constant. (The
special case of `complex_global_twist` where `t` is supplied directly rather than through
`perFrameTwist`; convenient when `Master` obtains `t` another way.) -/
theorem global_twist_of_perFrame {Frame : Type*} [Nonempty Frame] (t : Frame → ℝ)
    (Adj : Frame → Frame → Prop)
    (connected : ∀ F G, Relation.ReflTransGen (SymmStep Adj) F G)
    (overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧ ∀ x ∈ Set.Ioo a b,
        Complex.exp ((t F : ℂ) * x * Complex.I) = Complex.exp ((t G : ℂ) * x * Complex.I)) :
    ∃ tG : ℝ, ∀ F, t F = tG :=
  let D : ComplexGlobalizationData Frame := { t := t, Adj := Adj, connected := connected, overlap := overlap }
  ⟨D.globalT, fun F => D.t_eq_globalT F⟩

end MasterTheorem
