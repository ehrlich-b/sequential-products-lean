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

/-! ## Step 4b, part 1: a vector is its expansion over its support

The sign-fixing argument works with vectors supported on two basis slots: the image of
`b i + b j` has, by step 4a, coordinate modulus `1/√2` at `i` and `j` and modulus `0`
everywhere else, so it is `a • b' i + d • b' j` with `|a| = |d| = 1/√2` and the ray
depends only on the RELATIVE sign.  Turning "the other coordinates vanish" into that
finite expansion is the general lemma below.
-/

/-- **A vector equals its expansion over any set carrying all its coordinates.**  Over ℝ
the coordinates of `v` in an orthonormal basis are the inner products, so vanishing
outside `s` collapses the full expansion to a sum over `s`. -/
theorem eq_sum_over_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (v : E) (s : Finset ι)
    (h : ∀ k, k ∉ s → (inner ℝ v (b k) : ℝ) = 0) :
    v = ∑ k ∈ s, (inner ℝ v (b k) : ℝ) • b k := by
  have hfull : ∑ k, (inner ℝ v (b k) : ℝ) • b k = v :=
    (Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]).trans (b.sum_repr' v)
  refine hfull.symm.trans (Finset.sum_subset (Finset.subset_univ s) ?_).symm
  intro k _ hks
  rw [h k hks, zero_smul]

/-- The two-slot case, which is the one the sign argument uses. -/
theorem eq_pair_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (v : E) {i j : ι} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → (inner ℝ v (b k) : ℝ) = 0) :
    v = (inner ℝ v (b i) : ℝ) • b i + (inner ℝ v (b j) : ℝ) • b j := by
  have := eq_sum_over_support b v {i, j} (fun k hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact h k hk.1 hk.2)
  rwa [Finset.sum_insert (by simpa using hij), Finset.sum_singleton] at this

/-! ## Step 4b, part 2: the image of a two-slot vector is a two-slot vector

This is where "only signs remain" becomes concrete.  Take `w = b i + b j`.  Step 4a says
the image's coordinate modulus against `b' k` equals the source's against `b k`, which is
`0` for `k ∉ {i, j}` and `‖w‖⁻¹` for `k ∈ {i, j}` (no `√2` needs computing -- the value
*is* `‖w‖⁻¹`).  So by `eq_pair_expansion` the normalized image is `a • b' i + d • b' j`
with `|a| = |d| = ‖w‖⁻¹`: the ray is pinned except for the RELATIVE SIGN of `a` and `d`,
and comparing those relative signs across pairs is the whole remaining argument.
-/

section ImageBasis

variable {ι : Type*} [Fintype ι] [Nonempty ι] [FiniteDimensional ℝ E]

omit [Nonempty ι] [FiniteDimensional ℝ E] in
theorem basis_ne_zero (b : OrthonormalBasis ι ℝ E) (i : ι) : b i ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [b.orthonormal.1 i]; exact one_ne_zero)

/-- The image of an orthonormal basis, as an orthonormal basis on the same index type. -/
noncomputable def TransProbPreservingR.imgBasis {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) (b : OrthonormalBasis ι ℝ E) : OrthonormalBasis ι ℝ E :=
  hf.imageOrthonormalBasis (basis_ne_zero b) (fun _ _ hij => b.orthonormal.2 hij)
    (Module.finrank_eq_card_basis b.toBasis).symm

/-- The bridge back to the explicit normalized family, which is the form step 4a speaks
about. -/
theorem TransProbPreservingR.imgBasis_apply {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) (b : OrthonormalBasis ι ℝ E) (i : ι) :
    hf.imgBasis b i = ‖(f (Projectivization.mk ℝ (b i) (basis_ne_zero b i))).rep‖⁻¹ •
      (f (Projectivization.mk ℝ (b i) (basis_ne_zero b i))).rep :=
  congrFun (OrthonormalBasis.coe_mk
    (hf.image_orthonormal (basis_ne_zero b) (fun _ _ hij => b.orthonormal.2 hij)) _) i

/-- Step 4a, phrased against the image basis: **every coordinate of the image is `±` the
corresponding coordinate of the source.** -/
theorem TransProbPreservingR.abs_inner_imgBasis {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) (b : OrthonormalBasis ι ℝ E) {ψ : E} (hψ : ψ ≠ 0) (k : ι) :
    |(inner ℝ (‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ •
        (f (Projectivization.mk ℝ ψ hψ)).rep) (hf.imgBasis b k) : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) (b k) : ℝ)| := by
  rw [hf.imgBasis_apply b k]
  exact hf.abs_inner_image hψ (basis_ne_zero b k) (b.orthonormal.1 k)

/-- **Step 4b.**  The normalized image of `b i + b j` is supported on the two image slots
`i, j`, with both coordinate moduli equal to `‖b i + b j‖⁻¹`.  Only the relative sign of
the two coordinates is unpinned. -/
theorem TransProbPreservingR.image_two_slot {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j)
    (hw : b i + b j ≠ 0) :
    ∃ a d : ℝ, |a| = ‖b i + b j‖⁻¹ ∧ |d| = ‖b i + b j‖⁻¹ ∧
      ‖(f (Projectivization.mk ℝ (b i + b j) hw)).rep‖⁻¹ •
          (f (Projectivization.mk ℝ (b i + b j) hw)).rep
        = a • hf.imgBasis b i + d • hf.imgBasis b j := by
  classical
  have hnw : ‖b i + b j‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hinv : (0:ℝ) ≤ ‖b i + b j‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  -- the basis's own inner products
  have hb : ∀ p q : ι, (inner ℝ (b p) (b q) : ℝ) = if p = q then 1 else 0 := by
    intro p q
    rcases eq_or_ne p q with h | h
    · rw [if_pos h, h, real_inner_self_eq_norm_sq, b.orthonormal.1 q]; norm_num
    · rw [if_neg h, b.orthonormal.2 h]
  -- the source coordinates of the normalized two-slot vector
  have hsrc : ∀ k : ι, (inner ℝ (‖b i + b j‖⁻¹ • (b i + b j)) (b k) : ℝ)
      = ‖b i + b j‖⁻¹ * ((if i = k then 1 else 0) + (if j = k then 1 else 0)) := by
    intro k
    rw [real_inner_smul_left, inner_add_left, hb i k, hb j k]
  obtain ⟨u, hu⟩ : ∃ u : E, u = ‖(f (Projectivization.mk ℝ (b i + b j) hw)).rep‖⁻¹ •
      (f (Projectivization.mk ℝ (b i + b j) hw)).rep := ⟨_, rfl⟩
  rw [← hu]
  refine ⟨(inner ℝ u (hf.imgBasis b i) : ℝ), (inner ℝ u (hf.imgBasis b j) : ℝ), ?_, ?_, ?_⟩
  · rw [hu, hf.abs_inner_imgBasis b hw i, hsrc i, if_pos rfl, if_neg (Ne.symm hij), add_zero,
      mul_one, abs_of_nonneg hinv]
  · rw [hu, hf.abs_inner_imgBasis b hw j, hsrc j, if_neg hij, if_pos rfl, zero_add,
      mul_one, abs_of_nonneg hinv]
  · refine eq_pair_expansion (hf.imgBasis b) u hij ?_
    intro k hki hkj
    have habs := hf.abs_inner_imgBasis b hw k
    rw [hsrc k, if_neg (Ne.symm hki), if_neg (Ne.symm hkj), add_zero, mul_zero, abs_zero,
      ← hu] at habs
    exact abs_eq_zero.mp habs

/-! ## Step 4c, part 1: the image basis may be sign-normalized for free

The sign-fixing argument does not choose signs out of nothing -- it *absorbs* them.  Given
any pattern `σ : ι → ℝ` of units, the rescaled family `σ i • b' i` is again an orthonormal
basis, and it represents the SAME RAYS.  So replacing `b'` by a sign-normalized version
changes nothing that the classification can see, and the remaining task is only to exhibit
one pattern that works.
-/

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- Rescaling by signs preserves orthonormality. -/
theorem orthonormal_signAdjust (b : OrthonormalBasis ι ℝ E) (σ : ι → ℝ)
    (hσ : ∀ i, |σ i| = 1) : Orthonormal ℝ (fun i => σ i • b i) := by
  refine ⟨fun i => ?_, fun {i j} hij => ?_⟩
  · simp only [norm_smul, Real.norm_eq_abs, hσ i, b.orthonormal.1 i, mul_one]
  · simp only [real_inner_smul_left, real_inner_smul_right, b.orthonormal.2 hij, mul_zero]

/-- **Rescaling an orthonormal basis by signs gives an orthonormal basis.** -/
noncomputable def signAdjustBasis (b : OrthonormalBasis ι ℝ E) (σ : ι → ℝ)
    (hσ : ∀ i, |σ i| = 1) : OrthonormalBasis ι ℝ E :=
  OrthonormalBasis.mk (orthonormal_signAdjust b σ hσ) (by
    have hspan : Submodule.span ℝ (Set.range (fun i => σ i • b i)) = ⊤ := by
      apply LinearIndependent.span_eq_top_of_card_eq_finrank
        (orthonormal_signAdjust b σ hσ).linearIndependent
      exact (Module.finrank_eq_card_basis b.toBasis).symm
    rw [hspan])

omit [FiniteDimensional ℝ E] in
theorem signAdjustBasis_apply (b : OrthonormalBasis ι ℝ E) (σ : ι → ℝ)
    (hσ : ∀ i, |σ i| = 1) (i : ι) : signAdjustBasis b σ hσ i = σ i • b i :=
  congrFun (OrthonormalBasis.coe_mk (orthonormal_signAdjust b σ hσ) _) i

theorem sign_ne_zero {c : ℝ} (hc : |c| = 1) : c ≠ 0 := by
  intro h
  rw [h, abs_zero] at hc
  exact zero_ne_one hc

omit [FiniteDimensional ℝ E] in
/-- **A sign-adjusted basis represents the same rays.**  This is the precise sense in which
the residual sign freedom is invisible to the projective classification. -/
theorem mk_signAdjustBasis (b : OrthonormalBasis ι ℝ E) (σ : ι → ℝ)
    (hσ : ∀ i, |σ i| = 1) (i : ι) :
    Projectivization.mk ℝ (signAdjustBasis b σ hσ i) (basis_ne_zero _ i)
      = Projectivization.mk ℝ (b i) (basis_ne_zero b i) :=
  (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    ⟨Units.mk0 (σ i) (sign_ne_zero (hσ i)), by
      simp only [Units.smul_def, Units.val_mk0]
      exact (signAdjustBasis_apply b σ hσ i).symm⟩

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- Two distinct vectors of an orthonormal basis have nonzero sum — so the two-slot
vectors the sign argument uses never need a side hypothesis. -/
theorem basis_add_ne_zero (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j) :
    b i + b j ≠ 0 := by
  intro h
  have h1 : (inner ℝ (b i + b j) (b i) : ℝ) = 1 := by
    rw [inner_add_left, real_inner_self_eq_norm_sq, b.orthonormal.1 i,
      b.orthonormal.2 (Ne.symm hij)]
    norm_num
  rw [h, inner_zero_left] at h1
  exact zero_ne_one h1

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- **The two-slot transfer.**  The third input to `sign_pair_of_abs`: the image's
coordinate against the image of `b i + b j` reproduces the SUM of the source's two
coordinates, up to the same factor `‖b i + b j‖⁻¹` that `image_two_slot` produced.  With
`|x| = |p|` and `|y| = |q|` from step 4a, this is precisely the `|x + y| = |p + q|` that
forces a common sign. -/
theorem TransProbPreservingR.abs_inner_two_slot {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreservingR f) (b : OrthonormalBasis ι ℝ E) {ψ : E} (hψ : ψ ≠ 0)
    {i j : ι} (hij : i ≠ j) :
    |(inner ℝ (‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ • (f (Projectivization.mk ℝ ψ hψ)).rep)
        (‖(f (Projectivization.mk ℝ (b i + b j) (basis_add_ne_zero b hij))).rep‖⁻¹ •
          (f (Projectivization.mk ℝ (b i + b j) (basis_add_ne_zero b hij))).rep) : ℝ)|
      = ‖b i + b j‖⁻¹ * |(inner ℝ (‖ψ‖⁻¹ • ψ) (b i) : ℝ)
          + (inner ℝ (‖ψ‖⁻¹ • ψ) (b j) : ℝ)| := by
  have hw := basis_add_ne_zero b hij
  have hnw : ‖b i + b j‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hφ0 : ‖b i + b j‖⁻¹ • (b i + b j) ≠ 0 := normalize_ne_zero hw
  have hray : Projectivization.mk ℝ (‖b i + b j‖⁻¹ • (b i + b j)) hφ0
      = Projectivization.mk ℝ (b i + b j) hw := mk_smul_eq (inv_ne_zero hnw) hw hφ0
  have h := hf.abs_inner_image hψ hφ0 (norm_normalize hw)
  rw [hray] at h
  rw [h, real_inner_smul_right, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inner_add_right]

end ImageBasis

/-! ## Step 4c, part 2: the arithmetic that forces a COMMON sign

Here is the engine of the whole sign-fixing argument, and it is pure real arithmetic.  Step
4a gives `|x| = |p|` and `|y| = |q|` for the two coordinates; the transition probability
against the two-slot vector gives `|x + y| = |p + q|`.  Those three facts together force
`(x, y) = ±(p, q)` with **one sign for both** -- because the mixed case `x = p, y = -q`
would give `|p - q| = |p + q|`, i.e. `pq = 0`.  So a nonvanishing pair of source
coordinates transmits its relative sign, and that is what makes the global pattern
consistent rather than merely pointwise.
-/

/-- **The common-sign lemma.**  Matching moduli of the two coordinates AND of their sum
forces a single shared sign, provided neither source coordinate vanishes. -/
theorem sign_pair_of_abs {x y p q : ℝ} (hx : |x| = |p|) (hy : |y| = |q|)
    (hsum : |x + y| = |p + q|) (hpq : p * q ≠ 0) :
    (x = p ∧ y = q) ∨ (x = -p ∧ y = -q) := by
  have hsq : (x + y) ^ 2 = (p + q) ^ 2 := by
    rw [← sq_abs (x + y), ← sq_abs (p + q), hsum]
  rcases abs_eq_abs.mp hx with hx' | hx' <;> rcases abs_eq_abs.mp hy with hy' | hy'
  · exact Or.inl ⟨hx', hy'⟩
  · rw [hx', hy'] at hsq
    exact absurd (by linarith [hsq, sq_nonneg (p - q)] : p * q = 0) hpq
  · rw [hx', hy'] at hsq
    exact absurd (by linarith [hsq, sq_nonneg (p - q)] : p * q = 0) hpq
  · exact Or.inr ⟨hx', hy'⟩


end Projectivization
