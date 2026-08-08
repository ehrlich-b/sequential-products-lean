/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Wigner's theorem over the reals

For a finite-dimensional real inner product space `E`, every self-map of the projective
space `ℙ ℝ E` preserving the transition probability
`transProb p q = ⟪p.rep, q.rep⟫² / (‖p.rep‖²‖q.rep‖²)` is induced by a linear isometry.
This is the real case of Wigner's theorem, in the Uhlhorn form: only preservation of the
transition probability is assumed, not linearity, and **not bijectivity** — bijectivity is
a conclusion, since the induced isometry is invertible.

## Main definitions

* `Projectivization.transProbVec` — the transition probability of two vectors,
  `⟪ψ, φ⟫² / (‖ψ‖² ‖φ‖²)`, invariant under nonzero scaling in each slot.
* `Projectivization.transProb` — the induced function on pairs of rays.
* `Projectivization.TransProbPreserving` — the predicate that a self-map of `ℙ ℝ E`
  preserves `transProb`.
* `Projectivization.projMap` — the self-map of `ℙ ℝ E` induced by a linear isometry
  equivalence of `E`.

## Main results

* `Projectivization.projMap_transProbPreserving` — the easy inclusion: every linear
  isometry equivalence induces a transition-probability preserving map.
* `Projectivization.exists_isometry_of_transProbPreserving` — **Wigner's theorem over ℝ**:
  conversely, every transition-probability preserving self-map of `ℙ ℝ E` is `projMap e`
  for some `e : E ≃ₗᵢ[ℝ] E`. Together with the previous result this is an exact
  characterization.

## Implementation notes

The proof is elementary and self-contained: no projective topology, no measure theory, and
no functional analysis beyond the finite-dimensional inner-product API. The structure is

1. the image of an orthonormal basis is an orthonormal basis (`imageOrthonormalBasis`,
   `imgBasis`), because `transProb = 0` is orthogonality and `transProb = 1` is equality
   of rays;
2. the residual sign freedom in each image basis vector is fixed against an anchor index
   (`signPattern`, `normBasis`), using the two-slot rays `b i₀ + b i` to compare signs;
3. an arbitrary ray is matched coordinatewise, splitting on whether it meets the anchor
   (`eq_projMap_of_anchor`) or is orthogonal to it (`eq_projMap_of_anchor_zero`, handled by
   shifting the anchor); `eq_projMap` combines them and the main theorem instantiates it on
   `stdOrthonormalBasis`.

Over `ℝ` there is no phase freedom and no antiunitary alternative, so the conclusion is a
single isometry rather than a dichotomy. This is what makes the real case markedly shorter
than the complex one, and why the two are not instances of a common `RCLike` statement: the
complex conclusion carries an extra branch that has no real counterpart.

## References

* [E. P. Wigner, *Group Theory and its Application to the Quantum Mechanics of Atomic
  Spectra*][wigner1959]
* [U. Uhlhorn, *Representation of symmetry transformations in quantum mechanics*][uhlhorn1963]
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Transition probability over ℝ -/

/-- The real transition probability of two vectors. -/
def transProbVec (ψ φ : E) : ℝ :=
  ‖(inner ℝ ψ φ : ℝ)‖ ^ 2 / (‖ψ‖ ^ 2 * ‖φ‖ ^ 2)

theorem transProbVec_smul_left (c : ℝ) (hc : c ≠ 0) (ψ φ : E) :
    transProbVec (c • ψ) φ = transProbVec ψ φ := by
  unfold transProbVec
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

theorem transProbVec_smul_right (c : ℝ) (hc : c ≠ 0) (ψ φ : E) :
    transProbVec ψ (c • φ) = transProbVec ψ φ := by
  unfold transProbVec
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
def transProb (p q : ℙ ℝ E) : ℝ := transProbVec p.rep q.rep

/-! ## Orthogonal maps preserve it -/

/-- A real linear isometry preserves the vector-level transition probability. -/
theorem transProbVec_isometry (e : E ≃ₗᵢ[ℝ] E) (ψ φ : E) :
    transProbVec (e ψ) (e φ) = transProbVec ψ φ := by
  unfold transProbVec
  rw [e.inner_map_map, e.norm_map, e.norm_map]

/-- The map on `ℝP(E)` induced by a real linear isometry. -/
def projMap (e : E ≃ₗᵢ[ℝ] E) : ℙ ℝ E → ℙ ℝ E :=
  Projectivization.map e.toLinearEquiv.toLinearMap e.injective

@[simp]
theorem projMap_mk (e : E ≃ₗᵢ[ℝ] E) (v : E) (hv : v ≠ 0) :
    projMap e (Projectivization.mk ℝ v hv)
      = Projectivization.mk ℝ (e v) (by simpa using hv) :=
  Projectivization.map_mk _ _ _ _

/-- Transition-probability preservation, over ℝ. -/
def TransProbPreserving (f : ℙ ℝ E → ℙ ℝ E) : Prop :=
  ∀ p q, transProb (f p) (f q) = transProb p q

/-- **The easy inclusion `O(E) → TransProbPreserving`**: every orthogonal map induces
a transition-probability preserving self-map of `ℝP(E)`.  (The converse — Wigner's
theorem over ℝ — is `exists_isometry_of_transProbPreserving` at the end of this file,
so the two together are an exact characterization.) -/
theorem projMap_transProbPreserving (e : E ≃ₗᵢ[ℝ] E) :
    TransProbPreserving (projMap e) := by
  intro p q
  unfold transProb
  -- both `(projMap e p).rep` and `e p.rep` represent the same point, so they are
  -- proportional; `transProbVec` only sees the ray
  obtain ⟨a, ha⟩ : ∃ a : ℝˣ, (projMap e p).rep = a • e p.rep := by
    have h : projMap e p = Projectivization.mk ℝ (e p.rep) (by simpa using p.rep_nonzero) := by
      conv_lhs => rw [← p.mk_rep]
      rw [projMap_mk]
    rw [h]
    exact Projectivization.exists_smul_eq_mk_rep ℝ (e p.rep) (by simpa using p.rep_nonzero)
      |>.imp fun a ha => ha.symm
  obtain ⟨b, hb⟩ : ∃ b : ℝˣ, (projMap e q).rep = b • e q.rep := by
    have h : projMap e q = Projectivization.mk ℝ (e q.rep) (by simpa using q.rep_nonzero) := by
      conv_lhs => rw [← q.mk_rep]
      rw [projMap_mk]
    rw [h]
    exact Projectivization.exists_smul_eq_mk_rep ℝ (e q.rep) (by simpa using q.rep_nonzero)
      |>.imp fun b hb => hb.symm
  rw [ha, hb]
  simp only [Units.smul_def]
  rw [transProbVec_smul_left (a : ℝ) a.ne_zero, transProbVec_smul_right (b : ℝ) b.ne_zero,
    transProbVec_isometry]

/-! ## Step 1 of the rigidity: orthogonality is preserved -/

theorem transProbVec_eq_zero_iff {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    transProbVec ψ φ = 0 ↔ (inner ℝ ψ φ : ℝ) = 0 := by
  unfold transProbVec
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

/-- `transProb p q = 0` exactly when the rays are orthogonal. -/
theorem transProb_eq_zero_iff (p q : ℙ ℝ E) :
    transProb p q = 0 ↔ (inner ℝ p.rep q.rep : ℝ) = 0 :=
  transProbVec_eq_zero_iff p.rep_nonzero q.rep_nonzero

/-- **Step 1 of the rigidity**: a transition-probability preserving map preserves
orthogonality of rays.  This is the input to the basis argument — an orthonormal basis
is carried to a family of pairwise-orthogonal rays. -/
theorem TransProbPreserving.orthogonal {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) {p q : ℙ ℝ E}
    (hpq : (inner ℝ p.rep q.rep : ℝ) = 0) :
    (inner ℝ (f p).rep (f q).rep : ℝ) = 0 := by
  rw [← transProb_eq_zero_iff, hf p q, transProb_eq_zero_iff]
  exact hpq

/-- And conversely: orthogonality of the images forces orthogonality of the sources. -/
theorem TransProbPreserving.orthogonal_iff {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (p q : ℙ ℝ E) :
    (inner ℝ (f p).rep (f q).rep : ℝ) = 0 ↔ (inner ℝ p.rep q.rep : ℝ) = 0 := by
  rw [← transProb_eq_zero_iff, ← transProb_eq_zero_iff, hf p q]

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
theorem TransProbPreserving.image_pairwise_orthogonal {ι : Type*}
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreserving f) {v : ι → E}
    (hv : ∀ i, v i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℝ (v i) (v j) : ℝ) = 0)
    (i j : ι) (hij : i ≠ j) :
    (inner ℝ (f (Projectivization.mk ℝ (v i) (hv i))).rep
      (f (Projectivization.mk ℝ (v j) (hv j))).rep : ℝ) = 0 := by
  apply hf.orthogonal
  rw [inner_rep_eq_zero_iff]
  exact horth i j hij

/-- The normalized representatives of the image rays form an orthonormal family. -/
theorem TransProbPreserving.image_orthonormal {ι : Type*}
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreserving f) {v : ι → E}
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
theorem transProbVec_of_norm_one {φ : E} (hφ : ‖φ‖ = 1) (ψ : E) :
    transProbVec ψ φ = (inner ℝ ψ φ : ℝ) ^ 2 / ‖ψ‖ ^ 2 := by
  unfold transProbVec
  rw [hφ, one_pow, mul_one, Real.norm_eq_abs, sq_abs]

/-- **Step 3, the squared-coordinate transfer.**  If `f` preserves transition
probabilities and carries the unit vector `φ` to the ray of the unit vector `φ'`, then
for any ray `[ψ] ↦ [ψ']` the squared coordinates against `φ` and `φ'` agree after
normalizing by the squared norms.  This is the identity the sign-fixing step consumes:
each coordinate of the image is determined **up to sign**. -/
theorem TransProbPreserving.coord_sq_transfer {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0)
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
  unfold transProb at hkey
  -- rewrite each side against a unit representative
  have hR : transProbVec (Projectivization.mk ℝ ψ hψ).rep (Projectivization.mk ℝ φ hφ).rep
      = (inner ℝ ψ φ : ℝ) ^ 2 / ‖ψ‖ ^ 2 := by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℝ ψ hψ
    obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℝ φ hφ
    rw [← ha, ← hb]
    simp only [Units.smul_def]
    rw [transProbVec_smul_left (a : ℝ) a.ne_zero, transProbVec_smul_right (b : ℝ) b.ne_zero]
    exact transProbVec_of_norm_one hφ1 ψ
  have hL : transProbVec (f (Projectivization.mk ℝ ψ hψ)).rep
        (f (Projectivization.mk ℝ φ hφ)).rep
      = (inner ℝ (f (Projectivization.mk ℝ ψ hψ)).rep φ' : ℝ) ^ 2
        / ‖(f (Projectivization.mk ℝ ψ hψ)).rep‖ ^ 2 := by
    rw [hfφ]
    obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℝ φ' hφ'0
    rw [← hb]
    simp only [Units.smul_def]
    rw [transProbVec_smul_right (b : ℝ) b.ne_zero]
    exact transProbVec_of_norm_one hφ'1 _
  rw [← hL, ← hR]
  exact hkey

/-! ## Step 2b: in finite dimension the image family is an orthonormal BASIS -/

/-- **The image family spans.**  In finite dimension, an orthonormal family indexed by a
type of cardinality `finrank` is automatically a basis — so the image of an orthonormal
basis under a transition-probability preserving map is again an orthonormal basis.  This
is what lets the sign-fixing step (step 4) expand an image vector in the image basis and
conclude that its coordinates vanish outside the expected slots. -/
noncomputable def TransProbPreserving.imageOrthonormalBasis {ι : Type*} [Fintype ι]
    [Nonempty ι]
    [FiniteDimensional ℝ E] {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreserving f)
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
theorem TransProbPreserving.abs_coord_transfer {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0) (hφ1 : ‖φ‖ = 1)
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
theorem TransProbPreserving.abs_inner_image {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) {ψ φ : E} (hψ : ψ ≠ 0) (hφ : φ ≠ 0) (hφ1 : ‖φ‖ = 1) :
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
theorem eq_sum_over_support {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (v : E) (s : Finset ι)
    (h : ∀ k, k ∉ s → (inner ℝ v (b k) : ℝ) = 0) :
    v = ∑ k ∈ s, (inner ℝ v (b k) : ℝ) • b k := by
  classical
  have hfull : ∑ k, (inner ℝ v (b k) : ℝ) • b k = v :=
    (Finset.sum_congr rfl fun k _ => by rw [real_inner_comm]).trans (b.sum_repr' v)
  refine hfull.symm.trans (Finset.sum_subset (Finset.subset_univ s) ?_).symm
  intro k _ hks
  rw [h k hks, zero_smul]

/-- The two-slot case, which is the one the sign argument uses. -/
theorem eq_pair_expansion {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (v : E) {i j : ι} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → (inner ℝ v (b k) : ℝ) = 0) :
    v = (inner ℝ v (b i) : ℝ) • b i + (inner ℝ v (b j) : ℝ) • b j := by
  classical
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
noncomputable def TransProbPreserving.imgBasis {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) : OrthonormalBasis ι ℝ E :=
  hf.imageOrthonormalBasis (basis_ne_zero b) (fun _ _ hij => b.orthonormal.2 hij)
    (Module.finrank_eq_card_basis b.toBasis).symm

/-- The bridge back to the explicit normalized family, which is the form step 4a speaks
about. -/
theorem TransProbPreserving.imgBasis_apply {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i : ι) :
    hf.imgBasis b i = ‖(f (Projectivization.mk ℝ (b i) (basis_ne_zero b i))).rep‖⁻¹ •
      (f (Projectivization.mk ℝ (b i) (basis_ne_zero b i))).rep :=
  congrFun (OrthonormalBasis.coe_mk
    (hf.image_orthonormal (basis_ne_zero b) (fun _ _ hij => b.orthonormal.2 hij)) _) i

/-- Step 4a, phrased against the image basis: **every coordinate of the image is `±` the
corresponding coordinate of the source.** -/
theorem TransProbPreserving.abs_inner_imgBasis {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {ψ : E} (hψ : ψ ≠ 0) (k : ι) :
    |(inner ℝ (‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ •
        (f (Projectivization.mk ℝ ψ hψ)).rep) (hf.imgBasis b k) : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) (b k) : ℝ)| := by
  rw [hf.imgBasis_apply b k]
  exact hf.abs_inner_image hψ (basis_ne_zero b k) (b.orthonormal.1 k)

/-- **Step 4b.**  The normalized image of `b i + b j` is supported on the two image slots
`i, j`, with both coordinate moduli equal to `‖b i + b j‖⁻¹`.  Only the relative sign of
the two coordinates is unpinned. -/
theorem TransProbPreserving.image_two_slot {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j)
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
theorem TransProbPreserving.abs_inner_two_slot {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {ψ : E} (hψ : ψ ≠ 0)
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

/-! ## Step 4d, part 1: the candidate isometry

Two orthonormal bases on the same index type are related by a unique isometry matching them
slot for slot -- this is the object the rigidity produces, and it is pure Mathlib plumbing.
The classification's remaining content is not *building* it but showing that `f` agrees with
the induced projective map, which is where the sign pattern is consumed.
-/

/-- The isometry carrying one orthonormal basis to another, slot for slot. -/
noncomputable def basisIsometry (b c : OrthonormalBasis ι ℝ E) : E ≃ₗᵢ[ℝ] E :=
  b.repr.trans c.repr.symm

omit [Nonempty ι] [FiniteDimensional ℝ E] in
@[simp]
theorem basisIsometry_apply (b c : OrthonormalBasis ι ℝ E) (i : ι) :
    basisIsometry b c (b i) = c i := by
  classical
  simp only [basisIsometry, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
    OrthonormalBasis.repr_symm_single]

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- The induced projective map matches the bases as RAYS — the form the classification
statement needs. -/
theorem projMap_basisIsometry (b c : OrthonormalBasis ι ℝ E) (i : ι) :
    projMap (basisIsometry b c) (Projectivization.mk ℝ (b i) (basis_ne_zero b i))
      = Projectivization.mk ℝ (c i) (basis_ne_zero c i) := by
  rw [projMap_mk]
  exact (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    ⟨1, by simp⟩

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


/-! ## Step 4d, part 2: naming the normalized image, and the pair moduli

The assembly manipulates "the normalized representative of the image ray" constantly, so it
gets a name.  With it, the two facts the sign pattern is defined from become short: each
coordinate of the image of `b i + b j` has modulus `‖b i + b j‖⁻¹`, hence is NONZERO, so
their product has a genuine sign.
-/

/-- The normalized representative of the image ray. -/
noncomputable def normImg (f : ℙ ℝ E → ℙ ℝ E) {ψ : E} (hψ : ψ ≠ 0) : E :=
  ‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ • (f (Projectivization.mk ℝ ψ hψ)).rep

/-- `normImg` in rewritable form, for FOLDING the expanded expression that the earlier
step-4a lemmas are stated with. -/
theorem normImg_def (f : ℙ ℝ E → ℙ ℝ E) {ψ : E} (hψ : ψ ≠ 0) :
    ‖(f (Projectivization.mk ℝ ψ hψ)).rep‖⁻¹ • (f (Projectivization.mk ℝ ψ hψ)).rep
      = normImg f hψ := rfl

theorem normImg_ne_zero (f : ℙ ℝ E → ℙ ℝ E) {ψ : E} (hψ : ψ ≠ 0) : normImg f hψ ≠ 0 :=
  normalize_ne_zero (f _).rep_nonzero

theorem norm_normImg (f : ℙ ℝ E → ℙ ℝ E) {ψ : E} (hψ : ψ ≠ 0) : ‖normImg f hψ‖ = 1 :=
  norm_normalize (f _).rep_nonzero

/-- The normalized image represents the image ray — so `normImg` loses nothing. -/
theorem mk_normImg (f : ℙ ℝ E → ℙ ℝ E) {ψ : E} (hψ : ψ ≠ 0) :
    Projectivization.mk ℝ (normImg f hψ) (normImg_ne_zero f hψ) = f (Projectivization.mk ℝ ψ hψ) :=
  mk_normalize_rep _ _

/-- **The transfer in full generality**: for ANY two rays, the modulus of the inner product
of the normalized images equals that of the normalized sources.  Every specific transfer in
this development (two-slot, three-slot) is now just a computation of the right-hand side —
which is what makes the remaining pair-consistency argument mechanical rather than novel. -/
theorem TransProbPreserving.abs_inner_normImg {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) {ψ w : E} (hψ : ψ ≠ 0) (hw : w ≠ 0) :
    |(inner ℝ (normImg f hψ) (normImg f hw) : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) (‖w‖⁻¹ • w) : ℝ)| := by
  have hφ0 : ‖w‖⁻¹ • w ≠ 0 := normalize_ne_zero hw
  have hray : Projectivization.mk ℝ (‖w‖⁻¹ • w) hφ0 = Projectivization.mk ℝ w hw :=
    mk_smul_eq (inv_ne_zero (norm_ne_zero_iff.mpr hw)) hw hφ0
  have h := hf.abs_inner_image hψ hφ0 (norm_normalize hw)
  rw [hray, normImg_def, normImg_def] at h
  exact h

section PairModuli

variable {ι : Type*} [Fintype ι] [Nonempty ι] [FiniteDimensional ℝ E]

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- The inner products of an orthonormal basis, as one reusable identity. -/
theorem inner_basis_eq_ite [DecidableEq ι] (b : OrthonormalBasis ι ℝ E) (p q : ι) :
    (inner ℝ (b p) (b q) : ℝ) = if p = q then 1 else 0 := by
  rcases eq_or_ne p q with h | h
  · rw [if_pos h, h, real_inner_self_eq_norm_sq, b.orthonormal.1 q]; norm_num
  · rw [if_neg h, b.orthonormal.2 h]

/-- **Both coordinates of a two-slot image are nonzero, with modulus `‖b i + b j‖⁻¹`.**
This is what gives the sign pattern something to be the sign OF. -/
theorem TransProbPreserving.abs_inner_imgBasis_pair {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j) :
    |(inner ℝ (normImg f (basis_add_ne_zero b hij)) (hf.imgBasis b i) : ℝ)|
      = ‖b i + b j‖⁻¹ := by
  classical
  have h := hf.abs_inner_imgBasis b (basis_add_ne_zero b hij) i
  rw [show normImg f (basis_add_ne_zero b hij) = ‖(f (Projectivization.mk ℝ (b i + b j)
      (basis_add_ne_zero b hij))).rep‖⁻¹ • (f (Projectivization.mk ℝ (b i + b j)
      (basis_add_ne_zero b hij))).rep from rfl, h, real_inner_smul_left, inner_add_left,
    inner_basis_eq_ite, inner_basis_eq_ite, if_pos rfl, if_neg (Ne.symm hij), add_zero,
    mul_one, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]

theorem TransProbPreserving.inner_imgBasis_pair_ne_zero {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j) :
    (inner ℝ (normImg f (basis_add_ne_zero b hij)) (hf.imgBasis b i) : ℝ) ≠ 0 := by
  intro h
  have := hf.abs_inner_imgBasis_pair b hij
  rw [h, abs_zero] at this
  exact (inv_ne_zero (norm_ne_zero_iff.mpr (basis_add_ne_zero b hij))) this.symm

/-- The same for the second slot.  (The `(i,j)`-swapped instance of the previous lemma is
about the vector `b j + b i`, a different term, so the right slot needs its own statement.) -/
theorem TransProbPreserving.abs_inner_imgBasis_pair_right {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j) :
    |(inner ℝ (normImg f (basis_add_ne_zero b hij)) (hf.imgBasis b j) : ℝ)|
      = ‖b i + b j‖⁻¹ := by
  classical
  have h := hf.abs_inner_imgBasis b (basis_add_ne_zero b hij) j
  rw [show normImg f (basis_add_ne_zero b hij) = ‖(f (Projectivization.mk ℝ (b i + b j)
      (basis_add_ne_zero b hij))).rep‖⁻¹ • (f (Projectivization.mk ℝ (b i + b j)
      (basis_add_ne_zero b hij))).rep from rfl, h, real_inner_smul_left, inner_add_left,
    inner_basis_eq_ite, inner_basis_eq_ite, if_neg hij, if_pos rfl, zero_add,
    mul_one, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]

theorem TransProbPreserving.inner_imgBasis_pair_right_ne_zero {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i j : ι} (hij : i ≠ j) :
    (inner ℝ (normImg f (basis_add_ne_zero b hij)) (hf.imgBasis b j) : ℝ) ≠ 0 := by
  intro h
  have := hf.abs_inner_imgBasis_pair_right b hij
  rw [h, abs_zero] at this
  exact (inv_ne_zero (norm_ne_zero_iff.mpr (basis_add_ne_zero b hij))) this.symm

/-! ## Step 4d, part 2b: the sign pattern

Defined from the pairs `(i₀, i)`: the sign of the PRODUCT of the two coordinates of the
image of `b i₀ + b i`.  No choice is involved -- the coordinates are inner products, and
they are nonzero by the previous two lemmas, so the product has a genuine sign.  Adjusting
the image basis by this pattern makes each such image have two coordinates of EQUAL sign,
which is the normalization the arbitrary-ray argument runs against.
-/

/-- **The sign pattern read off the pairs `(i₀, i)`.** -/
noncomputable def TransProbPreserving.signPattern [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι) : ι → ℝ := fun i =>
  if h : i₀ = i then 1 else
    ((inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i₀) : ℝ) *
      (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i) : ℝ)) /
    |(inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i₀) : ℝ) *
      (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i) : ℝ)|

/-- The pattern consists of signs, which is all `signAdjustBasis` needs. -/
theorem TransProbPreserving.abs_signPattern [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι) (i : ι) :
    |hf.signPattern b i₀ i| = 1 := by
  unfold TransProbPreserving.signPattern
  by_cases h : i₀ = i
  · rw [dif_pos h, abs_one]
  · rw [dif_neg h]
    have hne : (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i₀) : ℝ) *
        (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i) : ℝ) ≠ 0 :=
      mul_ne_zero (hf.inner_imgBasis_pair_ne_zero b h) (hf.inner_imgBasis_pair_right_ne_zero b h)
    rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr hne)]

/-! ## Step 4d, part 2c: the normalization works

With the image basis adjusted by `signPattern`, the two coordinates of the image of
`b i₀ + b i` have the SAME sign — their product is positive.  This is the fact the
arbitrary-ray argument runs against: it means `sign_pair_of_abs` applied to a general ray
and the pair `(i₀, i)` can be read as a statement about coordinates in ONE fixed basis.
-/

/-- The arithmetic core: multiplying by `c/|c|` restores positivity. -/
theorem mul_sign_mul_pos {A B : ℝ} (hAB : A * B ≠ 0) :
    0 < A * ((A * B) / |A * B| * B) := by
  have h : A * ((A * B) / |A * B| * B) = (A * B) ^ 2 / |A * B| := by ring
  rw [h]
  exact div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hAB))) (abs_pos.mpr hAB)

/-- The sign-normalized image basis. -/
noncomputable def TransProbPreserving.normBasis [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι) :
    OrthonormalBasis ι ℝ E :=
  signAdjustBasis (hf.imgBasis b) (hf.signPattern b i₀) (hf.abs_signPattern b i₀)

theorem TransProbPreserving.normBasis_apply [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ k : ι) :
    hf.normBasis b i₀ k = hf.signPattern b i₀ k • hf.imgBasis b k :=
  signAdjustBasis_apply _ _ _ k

theorem TransProbPreserving.signPattern_self [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι) :
    hf.signPattern b i₀ i₀ = 1 := dif_pos rfl

theorem TransProbPreserving.signPattern_of_ne [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i₀ i : ι} (h : i₀ ≠ i) :
    hf.signPattern b i₀ i =
      ((inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i₀) : ℝ) *
        (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i) : ℝ)) /
      |(inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i₀) : ℝ) *
        (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.imgBasis b i) : ℝ)| := dif_neg h

/-- **The normalization works.**  Against `normBasis`, the two coordinates of the image of
`b i₀ + b i` have the same sign. -/
theorem TransProbPreserving.pair_coord_mul_pos [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i₀ i : ι} (h : i₀ ≠ i) :
    0 < (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.normBasis b i₀ i₀) : ℝ) *
        (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.normBasis b i₀ i) : ℝ) := by
  rw [hf.normBasis_apply b i₀ i₀, hf.normBasis_apply b i₀ i, real_inner_smul_right,
    real_inner_smul_right, hf.signPattern_self b i₀, one_mul, hf.signPattern_of_ne b h]
  exact mul_sign_mul_pos (mul_ne_zero (hf.inner_imgBasis_pair_ne_zero b h)
    (hf.inner_imgBasis_pair_right_ne_zero b h))

/-! ## Step 4d, part 2d: the two-slot image in the normalized basis

Equal moduli plus a positive product means EQUAL.  So in the normalized basis the image of
`b i₀ + b i` is a single scalar times `b'' i₀ + b'' i` — the two-slot image has become
symmetric, which is what lets its transition probability with an arbitrary ray be read as
`|x + y|` for the ray's own coordinates.
-/

/-- Equal moduli and a positive product force equality. -/
theorem eq_of_abs_eq_of_mul_pos {A B : ℝ} (habs : |A| = |B|) (hpos : 0 < A * B) : A = B := by
  rcases abs_eq_abs.mp habs with h | h
  · exact h
  · rw [h] at hpos
    nlinarith [hpos, sq_nonneg B]

/-- Step 4a against the normalized basis — the sign adjustment does not change moduli. -/
theorem TransProbPreserving.abs_inner_normBasis [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι) {ψ : E} (hψ : ψ ≠ 0)
    (k : ι) :
    |(inner ℝ (normImg f hψ) (hf.normBasis b i₀ k) : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) (b k) : ℝ)| := by
  rw [hf.normBasis_apply b i₀ k, real_inner_smul_right, abs_mul, hf.abs_signPattern b i₀ k,
    one_mul]
  exact hf.abs_inner_imgBasis b hψ k

/-- **The two-slot image is symmetric in the normalized basis.** -/
theorem TransProbPreserving.two_slot_normBasis [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i₀ i : ι} (h : i₀ ≠ i) :
    ∃ A : ℝ, |A| = ‖b i₀ + b i‖⁻¹ ∧
      normImg f (basis_add_ne_zero b h) = A • (hf.normBasis b i₀ i₀ + hf.normBasis b i₀ i) := by
  classical
  have hmodL : |(inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.normBasis b i₀ i₀) : ℝ)|
      = ‖b i₀ + b i‖⁻¹ := by
    rw [hf.normBasis_apply b i₀ i₀, real_inner_smul_right, abs_mul, hf.abs_signPattern b i₀ i₀,
      one_mul]
    exact hf.abs_inner_imgBasis_pair b h
  have hmodR : |(inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.normBasis b i₀ i) : ℝ)|
      = ‖b i₀ + b i‖⁻¹ := by
    rw [hf.normBasis_apply b i₀ i, real_inner_smul_right, abs_mul, hf.abs_signPattern b i₀ i,
      one_mul]
    exact hf.abs_inner_imgBasis_pair_right b h
  -- equal moduli + positive product ⟹ the two coordinates coincide
  have heq := eq_of_abs_eq_of_mul_pos (hmodL.trans hmodR.symm) (hf.pair_coord_mul_pos b h)
  have hvanish : ∀ k, k ≠ i₀ → k ≠ i →
      (inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.normBasis b i₀ k) : ℝ) = 0 := by
    intro k hki₀ hki
    have habs := hf.abs_inner_normBasis b i₀ (basis_add_ne_zero b h) k
    rw [real_inner_smul_left, inner_add_left, inner_basis_eq_ite, inner_basis_eq_ite,
      if_neg (Ne.symm hki₀), if_neg (Ne.symm hki), add_zero, mul_zero, abs_zero] at habs
    exact abs_eq_zero.mp habs
  refine ⟨(inner ℝ (normImg f (basis_add_ne_zero b h)) (hf.normBasis b i₀ i₀) : ℝ), hmodL, ?_⟩
  exact (eq_pair_expansion (hf.normBasis b i₀) (normImg f (basis_add_ne_zero b h)) h
    hvanish).trans (by rw [← heq, smul_add])

/-- **The pair transfer for an arbitrary ray.**  `sign_pair_of_abs`'s third hypothesis, in
the normalized basis: the moduli of the coordinate SUMS agree. -/
theorem TransProbPreserving.abs_add_coord_transfer [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) {i₀ i : ι} (h : i₀ ≠ i)
    {ψ : E} (hψ : ψ ≠ 0) :
    |(inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ)
        + (inner ℝ (normImg f hψ) (hf.normBasis b i₀ i) : ℝ)|
      = |(inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ) + (inner ℝ (‖ψ‖⁻¹ • ψ) (b i) : ℝ)| := by
  obtain ⟨A, hA, hAeq⟩ := hf.two_slot_normBasis b h
  have hkey := hf.abs_inner_two_slot b hψ h
  rw [normImg_def, normImg_def, hAeq, real_inner_smul_right, inner_add_right, abs_mul, hA]
    at hkey
  exact mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.mpr (basis_add_ne_zero b h))) hkey

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- Two vectors agreeing in every coordinate against an orthonormal basis are equal.  (Proved
from `sum_repr'` rather than imported: `InnerProductSpace.ext_inner_right_basis` lives in
`Analysis.InnerProductSpace.Dual`, which this development does not import.) -/
theorem eq_of_inner_basis_eq (c : OrthonormalBasis ι ℝ E) {u v : E}
    (h : ∀ k, (inner ℝ u (c k) : ℝ) = (inner ℝ v (c k) : ℝ)) : u = v :=
  (c.sum_repr' u).symm.trans ((Finset.sum_congr rfl fun k _ => by
    rw [real_inner_comm u (c k), real_inner_comm v (c k), h k]).trans (c.sum_repr' v))

/-! ## Step 4d, part 2f: THE MAIN CASE

On any ray whose anchor coordinate is nonzero, the rigidity is now complete.  The assembly
needs no sums: two vectors agreeing in every coordinate against an orthonormal basis are
equal, and `e` being an isometry turns `⟨e ψ̂, b'' k⟩` into `⟨ψ̂, b k⟩` directly.
-/

/-- **The main case of the real rigidity.**  If `⟨ψ̂, b i₀⟩ ≠ 0` then `f` agrees on `[ψ]`
with the projective map induced by the isometry carrying `b` to the sign-normalized image
basis.  The global sign is `ε = x_{i₀}/p_{i₀}`, and `sign_pair_of_abs` propagates it to
every other coordinate. -/
theorem TransProbPreserving.eq_projMap_of_anchor [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι)
    {ψ : E} (hψ : ψ ≠ 0) (hanchor : (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ) ≠ 0) :
    f (Projectivization.mk ℝ ψ hψ)
      = projMap (basisIsometry b (hf.normBasis b i₀)) (Projectivization.mk ℝ ψ hψ) := by
  classical
  have habsA := hf.abs_inner_normBasis b i₀ hψ i₀
  -- the global sign, defined outright
  have hεabs : |(inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ)
      / (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ)| = 1 := by
    rw [abs_div, habsA, div_self (abs_ne_zero.mpr hanchor)]
  have hεne : (inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ)
      / (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ) ≠ 0 := sign_ne_zero hεabs
  -- every coordinate carries that same sign
  have hcoord : ∀ k, (inner ℝ (normImg f hψ) (hf.normBasis b i₀ k) : ℝ)
      = ((inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ)
          / (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ)) * (inner ℝ (‖ψ‖⁻¹ • ψ) (b k) : ℝ) := by
    intro k
    by_cases hk : k = i₀
    · rw [hk, div_mul_cancel₀ _ hanchor]
    by_cases hpk : (inner ℝ (‖ψ‖⁻¹ • ψ) (b k) : ℝ) = 0
    · have hz := hf.abs_inner_normBasis b i₀ hψ k
      rw [hpk, abs_zero] at hz
      rw [abs_eq_zero.mp hz, hpk, mul_zero]
    rcases sign_pair_of_abs habsA (hf.abs_inner_normBasis b i₀ hψ k)
        (hf.abs_add_coord_transfer b (Ne.symm hk) hψ) (mul_ne_zero hanchor hpk) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, div_self hanchor, one_mul, h2]
    · rw [h1, neg_div, div_self hanchor, h2]
      ring
  -- the vector identity: no sums needed
  have hvec : normImg f hψ
      = ((inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ)
          / (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ)) •
        (basisIsometry b (hf.normBasis b i₀)) (‖ψ‖⁻¹ • ψ) := by
    refine eq_of_inner_basis_eq (hf.normBasis b i₀) fun k => ?_
    conv_rhs => rw [real_inner_smul_left, ← basisIsometry_apply b (hf.normBasis b i₀) k,
      LinearIsometryEquiv.inner_map_map]
    exact hcoord k
  -- and the rays agree
  have hez : (basisIsometry b (hf.normBasis b i₀)) ψ ≠ 0 := by
    intro h
    exact hψ ((basisIsometry b (hf.normBasis b i₀)).map_eq_zero_iff.mp h)
  rw [← mk_normImg f hψ, projMap_mk]
  refine (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    ⟨Units.mk0 ((inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ)
        / (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ) * ‖ψ‖⁻¹)
      (mul_ne_zero hεne (inv_ne_zero (norm_ne_zero_iff.mpr hψ))), ?_⟩
  simp only [Units.smul_def, Units.val_mk0]
  rw [← smul_smul, ← map_smul]
  exact hvec.symm

/-! ## Step 4d, part 2g: THE RESIDUAL CASE, without pair consistency

A ray orthogonal to the anchor cannot be handled by `sign_pair_of_abs` directly.  The
textbook route is a three-slot vector and a pair-consistency argument; **it is not needed.**
Shift the anchor instead: apply the main case to `ψ̂ + b i₀`, whose anchor coordinate is `1`.
Because the image of `ψ` has vanishing `i₀` coordinate, its overlap with the shifted ray is
FULL — `|⟨ψ', e ψ̂⟩| = ‖ψ'‖·‖e ψ̂‖` — and the equality case of Cauchy-Schwarz forces
proportionality.  That is the whole residual case.
-/

/-- **The residual case.**  Rays orthogonal to the anchor, by anchor-shifting. -/
theorem TransProbPreserving.eq_projMap_of_anchor_zero [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι)
    {ψ : E} (hψ : ψ ≠ 0) (hanchor : (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ) = 0) :
    f (Projectivization.mk ℝ ψ hψ)
      = projMap (basisIsometry b (hf.normBasis b i₀)) (Projectivization.mk ℝ ψ hψ) := by
  classical
  have hnψ : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hu1 : ‖‖ψ‖⁻¹ • ψ‖ = 1 := norm_normalize hψ
  have hself : (inner ℝ (‖ψ‖⁻¹ • ψ) (‖ψ‖⁻¹ • ψ) : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hu1, one_pow]
  -- the shifted vector, and its anchor coordinate
  have hinnerχ : (inner ℝ (‖ψ‖⁻¹ • ψ + b i₀) (b i₀) : ℝ) = 1 := by
    rw [inner_add_left, hanchor, real_inner_self_eq_norm_sq, b.orthonormal.1 i₀, zero_add,
      one_pow]
  have hχ : ‖ψ‖⁻¹ • ψ + b i₀ ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hinnerχ
    exact zero_ne_one hinnerχ
  have hnχ : ‖‖ψ‖⁻¹ • ψ + b i₀‖ ≠ 0 := norm_ne_zero_iff.mpr hχ
  have hanchor' : (inner ℝ (‖‖ψ‖⁻¹ • ψ + b i₀‖⁻¹ • (‖ψ‖⁻¹ • ψ + b i₀)) (b i₀) : ℝ) ≠ 0 := by
    rw [real_inner_smul_left, hinnerχ, mul_one]
    exact inv_ne_zero hnχ
  -- the main case applies to the shifted ray
  have hmain := hf.eq_projMap_of_anchor b i₀ hχ hanchor'
  rw [← mk_normImg f hχ, projMap_mk] at hmain
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mp hmain
  rw [Units.smul_def] at ha
  -- the scale of `a` is forced by both sides being unit-normalized
  have hae : |(a : ℝ)| * ‖‖ψ‖⁻¹ • ψ + b i₀‖ = 1 := by
    have h1 : ‖(a : ℝ) • (basisIsometry b (hf.normBasis b i₀)) (‖ψ‖⁻¹ • ψ + b i₀)‖ = 1 := by
      rw [ha]; exact norm_normImg f hχ
    rwa [norm_smul, Real.norm_eq_abs, LinearIsometryEquiv.norm_map] at h1
  -- the image's anchor coordinate vanishes
  have hximg : (inner ℝ (normImg f hψ) (hf.normBasis b i₀ i₀) : ℝ) = 0 := by
    have h := hf.abs_inner_normBasis b i₀ hψ i₀
    rw [hanchor, abs_zero] at h
    exact abs_eq_zero.mp h
  -- the overlap with the shifted ray is full
  have hfull : |(inner ℝ (normImg f hψ)
      ((basisIsometry b (hf.normBasis b i₀)) (‖ψ‖⁻¹ • ψ)) : ℝ)| = 1 := by
    have hkey := hf.abs_inner_normImg hψ hχ
    rw [← ha] at hkey
    rw [real_inner_smul_right] at hkey
    rw [abs_mul] at hkey
    rw [map_add] at hkey
    rw [basisIsometry_apply b (hf.normBasis b i₀) i₀] at hkey
    rw [inner_add_right] at hkey
    rw [hximg, add_zero] at hkey
    rw [real_inner_smul_right] at hkey
    rw [inner_add_right] at hkey
    rw [hself, hanchor, add_zero] at hkey
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), abs_one, mul_one] at hkey
    -- hkey : |a| * |⟨ψ', e ψ̂⟩| = ‖χ‖⁻¹, and |a| = ‖χ‖⁻¹
    have habs : |(a : ℝ)| = ‖‖ψ‖⁻¹ • ψ + b i₀‖⁻¹ := by
      have h1 : |(a : ℝ)| * ‖‖ψ‖⁻¹ • ψ + b i₀‖ * ‖‖ψ‖⁻¹ • ψ + b i₀‖⁻¹
          = 1 * ‖‖ψ‖⁻¹ • ψ + b i₀‖⁻¹ := by rw [hae]
      rwa [mul_assoc, mul_inv_cancel₀ hnχ, mul_one, one_mul] at h1
    rw [habs] at hkey
    exact mul_left_cancel₀ (inv_ne_zero hnχ) (hkey.trans (mul_one _).symm)
  -- Cauchy-Schwarz equality
  obtain ⟨r, hr0, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) (normImg_ne_zero f hψ)
      (fun h => normalize_ne_zero hψ
        ((basisIsometry b (hf.normBasis b i₀)).map_eq_zero_iff.mp h))).mp
    (by rw [Real.norm_eq_abs, hfull, norm_normImg, LinearIsometryEquiv.norm_map, hu1, one_mul])
  -- and the rays agree
  have hez : (basisIsometry b (hf.normBasis b i₀)) ψ ≠ 0 := fun h =>
    hψ ((basisIsometry b (hf.normBasis b i₀)).map_eq_zero_iff.mp h)
  rw [← mk_normImg f hψ, projMap_mk]
  refine (Projectivization.mk_eq_mk_iff ℝ _ _ _ _).mpr
    ⟨Units.mk0 (r⁻¹ * ‖ψ‖⁻¹) (mul_ne_zero (inv_ne_zero hr0) (inv_ne_zero hnψ)), ?_⟩
  simp only [Units.smul_def, Units.val_mk0]
  rw [← smul_smul, ← map_smul, hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]

/-! ## The real rigidity, assembled -/

/-- **Every ray**: combining the two cases, `f` is induced by the isometry matching `b` to
the sign-normalized image basis. -/
theorem TransProbPreserving.eq_projMap [DecidableEq ι] {f : ℙ ℝ E → ℙ ℝ E}
    (hf : TransProbPreserving f) (b : OrthonormalBasis ι ℝ E) (i₀ : ι) (p : ℙ ℝ E) :
    f p = projMap (basisIsometry b (hf.normBasis b i₀)) p := by
  induction p using Projectivization.ind with
  | h ψ hψ =>
    by_cases h : (inner ℝ (‖ψ‖⁻¹ • ψ) (b i₀) : ℝ) = 0
    · exact hf.eq_projMap_of_anchor_zero b i₀ hψ h
    · exact hf.eq_projMap_of_anchor b i₀ hψ h

end PairModuli

/-- **Wigner's theorem over `ℝ`**, in Uhlhorn's form. Every transition-probability preserving
self-map of the rays of a finite-dimensional real inner product space is induced by a linear
isometry equivalence.

Neither linearity nor bijectivity of `f` is assumed. Together with
`projMap_transProbPreserving` this characterizes the transition-probability preserving maps
exactly as the image of `E ≃ₗᵢ[ℝ] E`. -/
theorem exists_isometry_of_transProbPreserving [FiniteDimensional ℝ E] [Nontrivial E]
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreserving f) :
    ∃ e : E ≃ₗᵢ[ℝ] E, ∀ p : ℙ ℝ E, f p = projMap e p := by
  classical
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hpos⟩⟩
  exact ⟨basisIsometry (stdOrthonormalBasis ℝ E)
      (hf.normBasis (stdOrthonormalBasis ℝ E) ⟨0, hpos⟩),
    hf.eq_projMap (stdOrthonormalBasis ℝ E) ⟨0, hpos⟩⟩

end Projectivization
