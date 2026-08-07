/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Vendor.Wigner.TransitionProbability

set_option linter.style.longLine false

/-!
# Real Wigner/Uhlhorn: the setup and the easy direction

The complex row's Jordan property is discharged (M3) through the vendored
`Projectivization.wigner_rigidity` on `ℂP^{N-1}`.  The **real** row currently carries
its Jordan property as a located hypothesis because no prover has the real analogue.
This file starts that analogue.

Measured before writing (2026-08-06): the complex development is 3179 lines, of which
the bulk is *phase* structure — 85 uses of `Complex.I`, 117 circle/phase references,
179 conjugation/antiunitary references.  **None of that exists over ℝ**: there is no
circle of gauge freedom and no antiunitary branch, only a global sign.  So the real
theorem is not a port of that file, but it is correspondingly much shorter.

This file supplies the definitions and the **easy inclusion**
`O(E) → TransProbPreserving`:

* `transProbVecR` — `|⟨ψ,φ⟩|²/(‖ψ‖²‖φ‖²)` over ℝ, with scale invariance in each slot;
* `transProbR` — the induced function on `ℝP(E)`;
* `TransProbPreservingR`, `projMapR` — the property and the map induced by a real
  linear isometry;
* **`projMapR_transProbPreservingR`** — every orthogonal map preserves transition
  probabilities.

The converse (the rigidity) is the remaining content: a transition-probability
preserving bijection of `ℝP(E)` is `projMapR e` for some orthogonal `e`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Transition probability over ℝ -/

/-- The real transition probability of two vectors. -/
def transProbVecR (ψ φ : E) : ℝ :=
  ‖(inner ℝ ψ φ : ℝ)‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)

theorem transProbVecR_smul_left (c : ℝ) (hc : c ≠ 0) (ψ φ : E) :
    transProbVecR (c • ψ) φ = transProbVecR ψ φ := by
  unfold transProbVecR
  rw [inner_smul_left, norm_mul, norm_smul, mul_pow, mul_pow]
  rcases eq_or_ne ψ 0 with hψ | hψ
  · simp [hψ]
  · rcases eq_or_ne φ 0 with hφ | hφ
    · simp [hφ]
    · have h1 : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
      have h2 : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
      have h3 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
      have h4 : ‖(starRingEnd ℝ) c‖ = ‖c‖ := by simp
      rw [h4]
      field_simp

theorem transProbVecR_smul_right (c : ℝ) (hc : c ≠ 0) (ψ φ : E) :
    transProbVecR ψ (c • φ) = transProbVecR ψ φ := by
  unfold transProbVecR
  rw [inner_smul_right, norm_mul, norm_smul, mul_pow, mul_pow]
  rcases eq_or_ne ψ 0 with hψ | hψ
  · simp [hψ]
  · rcases eq_or_ne φ 0 with hφ | hφ
    · simp [hφ]
    · have h1 : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
      have h2 : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
      have h3 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
      field_simp

/-- The transition probability of two points of `ℝP(E)`. -/
def transProbR (p q : ℙ ℝ E) : ℝ := transProbVecR p.rep q.rep

/-! ## Orthogonal maps preserve it -/

/-- A real linear isometry preserves the vector-level transition probability. -/
theorem transProbVecR_isometry (e : E ≃ₗᵢ[ℝ] E) (ψ φ : E) :
    transProbVecR (e ψ) (e φ) = transProbVecR ψ φ := by
  unfold transProbVecR
  rw [e.inner_map_map, e.norm_map, e.norm_map]

/-- The map on `ℝP(E)` induced by a real linear isometry. -/
def projMapR (e : E ≃ₗᵢ[ℝ] E) : ℙ ℝ E → ℙ ℝ E :=
  Projectivization.map e.toLinearEquiv.toLinearMap e.injective

@[simp]
theorem projMapR_mk (e : E ≃ₗᵢ[ℝ] E) (v : E) (hv : v ≠ 0) :
    projMapR e (Projectivization.mk ℝ v hv)
      = Projectivization.mk ℝ (e v) (by simpa using hv) :=
  Projectivization.map_mk _ _ _ _

/-- Transition-probability preservation, over ℝ. -/
def TransProbPreservingR (f : ℙ ℝ E → ℙ ℝ E) : Prop :=
  ∀ p q, transProbR (f p) (f q) = transProbR p q

/-- **The easy inclusion `O(E) → TransProbPreserving`**: every orthogonal map induces
a transition-probability preserving self-map of `ℝP(E)`.  (The converse — Wigner's
theorem over ℝ — is the remaining content of this file's programme.) -/
theorem projMapR_transProbPreservingR (e : E ≃ₗᵢ[ℝ] E) :
    TransProbPreservingR (projMapR e) := by
  intro p q
  unfold transProbR
  -- both `(projMapR e p).rep` and `e p.rep` represent the same point, so they are
  -- proportional; `transProbVecR` only sees the ray
  obtain ⟨a, ha⟩ : ∃ a : ℝˣ, (projMapR e p).rep = a • e p.rep := by
    have h : projMapR e p = Projectivization.mk ℝ (e p.rep) (by simpa using p.rep_nonzero) := by
      conv_lhs => rw [← p.mk_rep]
      rw [projMapR_mk]
    rw [h]
    exact Projectivization.exists_smul_eq_mk_rep ℝ (e p.rep) (by simpa using p.rep_nonzero)
      |>.imp fun a ha => ha.symm
  obtain ⟨b, hb⟩ : ∃ b : ℝˣ, (projMapR e q).rep = b • e q.rep := by
    have h : projMapR e q = Projectivization.mk ℝ (e q.rep) (by simpa using q.rep_nonzero) := by
      conv_lhs => rw [← q.mk_rep]
      rw [projMapR_mk]
    rw [h]
    exact Projectivization.exists_smul_eq_mk_rep ℝ (e q.rep) (by simpa using q.rep_nonzero)
      |>.imp fun b hb => hb.symm
  rw [ha, hb]
  simp only [Units.smul_def]
  rw [transProbVecR_smul_left (a : ℝ) a.ne_zero, transProbVecR_smul_right (b : ℝ) b.ne_zero,
    transProbVecR_isometry]

end Projectivization
