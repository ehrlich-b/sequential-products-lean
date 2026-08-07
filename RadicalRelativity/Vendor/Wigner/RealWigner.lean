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

/-! ## Step 1 of the rigidity: orthogonality is preserved -/

theorem transProbVecR_eq_zero_iff {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    transProbVecR ψ φ = 0 ↔ (inner ℝ ψ φ : ℝ) = 0 := by
  unfold transProbVecR
  have h1 : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have h2 : ‖φ‖ ≠ 0 := norm_ne_zero_iff.mpr hφ
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      exact norm_eq_zero.mp this
    · exact absurd h (by positivity)
  · intro h
    left
    rw [h]
    simp

/-- `transProbR p q = 0` exactly when the rays are orthogonal. -/
theorem transProbR_eq_zero_iff (p q : ℙ ℝ E) :
    transProbR p q = 0 ↔ (inner ℝ p.rep q.rep : ℝ) = 0 :=
  transProbVecR_eq_zero_iff p.rep_nonzero q.rep_nonzero

/-- **Step 1 of the rigidity**: a transition-probability preserving map preserves
orthogonality of rays.  This is the input to the basis argument — an orthonormal basis
is carried to a family of pairwise-orthogonal rays. -/
theorem TransProbPreservingR.orthogonal {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) {p q : ℙ ℝ E}
    (hpq : (inner ℝ p.rep q.rep : ℝ) = 0) :
    (inner ℝ (f p).rep (f q).rep : ℝ) = 0 := by
  rw [← transProbR_eq_zero_iff, hf p q, transProbR_eq_zero_iff]
  exact hpq

/-- And conversely: orthogonality of the images forces orthogonality of the sources. -/
theorem TransProbPreservingR.orthogonal_iff {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) (p q : ℙ ℝ E) :
    (inner ℝ (f p).rep (f q).rep : ℝ) = 0 ↔ (inner ℝ p.rep q.rep : ℝ) = 0 := by
  rw [← transProbR_eq_zero_iff, ← transProbR_eq_zero_iff, hf p q]

/-! ## Step 2: an orthonormal basis goes to an orthonormal family -/

/-- Orthogonality of rays is visible on any representatives. -/
theorem inner_rep_eq_zero_iff {v w : E} (hv : v ≠ 0) (hw : w ≠ 0) :
    (inner ℝ (Projectivization.mk ℝ v hv).rep (Projectivization.mk ℝ w hw).rep : ℝ) = 0
      ↔ (inner ℝ v w : ℝ) = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℝ w hw
  have ha' : (a : ℝ) ≠ 0 := a.ne_zero
  have hb' : (b : ℝ) ≠ 0 := b.ne_zero
  rw [← ha, ← hb]
  simp only [Units.smul_def, real_inner_smul_left, real_inner_smul_right]
  simp [ha', hb', mul_eq_zero]

/-- **Step 2**: a transition-probability preserving map carries the rays of an
orthonormal family to pairwise-orthogonal rays.  Normalizing the representatives then
gives an orthonormal family — and in finite dimension, with as many members as the
dimension, an orthonormal basis, which is the candidate isometry's data. -/
theorem TransProbPreservingR.image_pairwise_orthogonal {ι : Type*}
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreservingR f) {v : ι → E}
    (hv : ∀ i, v i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℝ (v i) (v j) : ℝ) = 0)
    (i j : ι) (hij : i ≠ j) :
    (inner ℝ (f (Projectivization.mk ℝ (v i) (hv i))).rep
      (f (Projectivization.mk ℝ (v j) (hv j))).rep : ℝ) = 0 := by
  apply hf.orthogonal
  rw [inner_rep_eq_zero_iff]
  exact horth i j hij

/-- The normalized representatives of the image rays form an orthonormal family. -/
theorem TransProbPreservingR.image_orthonormal {ι : Type*}
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreservingR f) {v : ι → E}
    (hv : ∀ i, v i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℝ (v i) (v j) : ℝ) = 0) :
    Orthonormal ℝ (fun i => ‖(f (Projectivization.mk ℝ (v i) (hv i))).rep‖⁻¹ •
      (f (Projectivization.mk ℝ (v i) (hv i))).rep) := by
  constructor
  · intro i
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr
      (f (Projectivization.mk ℝ (v i) (hv i))).rep_nonzero)
  · intro i j hij
    rw [inner_smul_left, inner_smul_right,
      hf.image_pairwise_orthogonal hv horth i j hij]
    simp

/-! ## Step 3: transition probability against a unit vector is a squared coordinate -/

/-- Against a **unit** vector, the transition probability is the squared coordinate:
`transProb(ψ, φ) = ⟨ψ,φ⟩²/‖ψ‖²`.  Over ℝ there is no modulus to take — the numerator
is literally the square of the coordinate, which is why the rigidity's residual freedom
is a sign rather than a phase. -/
theorem transProbVecR_of_norm_one {φ : E} (hφ : ‖φ‖ = 1) (ψ : E) :
    transProbVecR ψ φ = (inner ℝ ψ φ : ℝ) ^ 2 / ‖ψ‖ ^ 2 := by
  unfold transProbVecR
  rw [hφ, one_pow, mul_one, Real.norm_eq_abs, sq_abs]

/-- **Step 3, the squared-coordinate transfer.**  If `f` preserves transition
probabilities and carries the unit vector `φ` to the ray of the unit vector `φ'`, then
for any ray `[ψ] ↦ [ψ']` the squared coordinates against `φ` and `φ'` agree after
normalizing by the squared norms.  This is the identity the sign-fixing step consumes:
each coordinate of the image is determined **up to sign**. -/
theorem TransProbPreservingR.coord_sq_transfer {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0)
    (hφ1 : ‖φ‖ = 1)
    {φ' : E} (hφ'1 : ‖φ'‖ = 1)
    (hfφ : f (Projectivization.mk ℝ φ hφ) = Projectivization.mk ℝ φ' (by
      intro h
      rw [h, norm_zero] at hφ'1
      exact one_ne_zero hφ'1.symm)) :
    (inner ℝ (f (Projectivization.mk ℝ ψ hψ)).rep φ' : ℝ) ^ 2
        / ‖(f (Projectivization.mk ℝ ψ hψ)).rep‖ ^ 2
      = (inner ℝ ψ φ : ℝ) ^ 2 / ‖ψ‖ ^ 2 := by
  have hφ'0 : φ' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hφ'1
    exact one_ne_zero hφ'1.symm
  -- the transition probability is preserved, and both sides are squared coordinates
  have hkey := hf (Projectivization.mk ℝ ψ hψ) (Projectivization.mk ℝ φ hφ)
  unfold transProbR at hkey
  -- rewrite each side against a unit representative
  have hR : transProbVecR (Projectivization.mk ℝ ψ hψ).rep (Projectivization.mk ℝ φ hφ).rep
      = (inner ℝ ψ φ : ℝ) ^ 2 / ‖ψ‖ ^ 2 := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ ψ hψ
    obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℝ φ hφ
    rw [← ha, ← hb]
    simp only [Units.smul_def]
    rw [transProbVecR_smul_left (a : ℝ) a.ne_zero, transProbVecR_smul_right (b : ℝ) b.ne_zero]
    exact transProbVecR_of_norm_one hφ1 ψ
  have hL : transProbVecR (f (Projectivization.mk ℝ ψ hψ)).rep
        (f (Projectivization.mk ℝ φ hφ)).rep
      = (inner ℝ (f (Projectivization.mk ℝ ψ hψ)).rep φ' : ℝ) ^ 2
        / ‖(f (Projectivization.mk ℝ ψ hψ)).rep‖ ^ 2 := by
    rw [hfφ]
    obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℝ φ' hφ'0
    rw [← hb]
    simp only [Units.smul_def]
    rw [transProbVecR_smul_right (b : ℝ) b.ne_zero]
    exact transProbVecR_of_norm_one hφ'1 _
  rw [← hL, ← hR]
  exact hkey

/-! ## Step 2b: in finite dimension the image family is an orthonormal BASIS -/

/-- **The image family spans.**  In finite dimension, an orthonormal family indexed by a
type of cardinality `finrank` is automatically a basis — so the image of an orthonormal
basis under a transition-probability preserving map is again an orthonormal basis.  This
is what lets the sign-fixing step (step 4) expand an image vector in the image basis and
conclude that its coordinates vanish outside the expected slots. -/
noncomputable def TransProbPreservingR.imageOrthonormalBasis {ι : Type*} [Fintype ι]
    [Nonempty ι]
    [FiniteDimensional ℝ E] {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreservingR f)
    {v : ι → E} (hv : ∀ i, v i ≠ 0)
    (horth : ∀ i j, i ≠ j → (inner ℝ (v i) (v j) : ℝ) = 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E) :
    OrthonormalBasis ι ℝ E := by
  classical
  refine OrthonormalBasis.mk (hf.image_orthonormal hv horth) ?_
  have hli := (hf.image_orthonormal hv horth).linearIndependent
  have hspan : Submodule.span ℝ (Set.range
      (fun i => ‖(f (Projectivization.mk ℝ (v i) (hv i))).rep‖⁻¹ •
        (f (Projectivization.mk ℝ (v i) (hv i))).rep)) = ⊤ := by
    apply LinearIndependent.span_eq_top_of_card_eq_finrank hli
    rw [hcard]
  rw [hspan]

/-! ## Step 4a: only signs remain — the image's coordinate moduli are the source's

Step 3 pinned each coordinate *squared*.  The lemmas here convert that into the statement
the sign-fixing argument actually runs on: with everything normalized, the image vector's
coordinate against the image of a unit vector has the **same absolute value** as the
source's coordinate against that unit vector.  So a transition-probability preserving map
is, coordinatewise, the identity up to a sign pattern -- and the whole remaining content
of the real rigidity is that the pattern is a single global sign.
-/

/-- Rescaling a representative by a nonzero scalar does not change the ray. -/
theorem mk_smul_eq {c : ℝ} (hc : c ≠ 0) {v : E} (hv : v ≠ 0) (h : c • v ≠ 0) :
    Projectivization.mk ℝ (c • v) h = Projectivization.mk ℝ v hv :=
  (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr ⟨Units.mk0 c hc, by simp [Units.smul_def]⟩

/-- The normalized representative represents the same ray. -/
theorem mk_normalize_rep (p : ℙ ℝ E) (h : ‖p.rep‖⁻¹ • p.rep ≠ 0) :
    Projectivization.mk ℝ (‖p.rep‖⁻¹ • p.rep) h = p :=
  (mk_smul_eq (inv_ne_zero (norm_ne_zero_iff.mpr p.rep_nonzero)) p.rep_nonzero h).trans
    (Projectivization.mk_rep p)

theorem norm_normalize {v : E} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

theorem normalize_ne_zero {v : E} (hv : v ≠ 0) : ‖v‖⁻¹ • v ≠ 0 :=
  smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hv)) hv

/-- **Step 4a.**  With both sides normalized, the coordinate transfers *in absolute
value*: the squared identity of step 3 has a unique nonnegative square root. -/
theorem TransProbPreservingR.abs_coord_transfer {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0) (hφ1 : ‖φ‖ = 1)
    {φ' : E} (hφ'0 : φ' ≠ 0) (hφ'1 : ‖φ'‖ = 1)
    (hfφ : f (Projectivization.mk ℝ φ hφ) = Projectivization.mk ℝ φ' hφ'0) :
    |(inner ℝ (‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ •
        (f (Projectivization.mk ℝ ψ hψ)).rep) φ' : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) φ : ℝ)| := by
  have hψ'0 : (f (Projectivization.mk ℝ ψ hψ)).rep ≠ 0 := (f _).rep_nonzero
  have hnψ' : ‖(f (Projectivization.mk ℝ ψ hψ)).rep‖ ≠ 0 := norm_ne_zero_iff.mpr hψ'0
  have hnψ : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hsq := hf.coord_sq_transfer hψ hφ hφ1 hφ'1 hfφ
  rw [div_eq_inv_mul, div_eq_inv_mul] at hsq
  rw [real_inner_smul_left, real_inner_smul_left, abs_mul, abs_mul, abs_inv, abs_inv,
    abs_norm, abs_norm, ← sq_eq_sq₀ (by positivity) (by positivity),
    mul_pow, mul_pow, sq_abs, sq_abs, inv_pow, inv_pow]
  exact hsq

/-- **Step 4a, the self-contained form.**  Taking `φ'` to be the *normalized image* of
`φ` removes the side hypothesis entirely: for any preserving `f` and any unit `φ`, the
normalized image of any ray has the same coordinate modulus against the normalized image
of `φ` as the source ray has against `φ`.  Applied to an orthonormal basis `b`, with
`b' = imageOrthonormalBasis`, this says **every coordinate of the image is `±` the
corresponding coordinate of the source**. -/
theorem TransProbPreservingR.abs_inner_image {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0) (hφ1 : ‖φ‖ = 1) :
    |(inner ℝ (‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ •
        (f (Projectivization.mk ℝ ψ hψ)).rep)
      (‖(f (Projectivization.mk ℝ φ hφ)).rep‖⁻¹ • (f (Projectivization.mk ℝ φ hφ)).rep) : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) φ : ℝ)| := by
  have hrep : (f (Projectivization.mk ℝ φ hφ)).rep ≠ 0 := (f _).rep_nonzero
  exact hf.abs_coord_transfer hψ hφ hφ1 (normalize_ne_zero hrep) (norm_normalize hrep)
    (mk_normalize_rep _ (normalize_ne_zero hrep)).symm

end Projectivization
