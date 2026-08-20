/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockChiGen
import RadicalRelativity.Necessity.FrameBlockSpanGen
import RadicalRelativity.Necessity.ChiContinuityGen
import RadicalRelativity.Necessity.ConjTransportGen
import RadicalRelativity.Necessity.SingularExtension
import RadicalRelativity.Hermitian.CfcSqrtContinuous

set_option linter.style.longLine false

/-!
# The real type is rigid: `χ̃ = id` on `H_n(ℝ)`  (`prop:real`, M4.1 capstone)

Over ℝ the comparison character is the **identity** — there is no twist parameter at
all — and the argument needs no differentiation, only the block isometry and
continuity that the field-general layers already provide.

* `blockScalar` — the scalar by which `χ̃(r)` acts on the block `(i,j)`: over ℝ the
  Peirce block is one-dimensional, so `chiTilde_block_existsG` gives
  `χ̃(r)(blockHerm i j 1) = blockHerm i j (blockScalar …)`.
* `blockScalar_sq` — **it squares to one** (`normSq` over ℝ is `x²`), i.e. it is `±1`.
* `blockScalar_eq_one` — **it is `+1`**: `t ↦ blockScalar (t • r)` is continuous,
  squares to one, and equals `1` at `t = 0`; a continuous function into `{±1}` that
  reached `−1` would have to vanish somewhere by the intermediate value theorem,
  contradicting the square law. This is where the ℂ lane needed the phase cocycle
  and the whole differential apparatus; over ℝ connectedness does it.
* `chiTilde_eq_id` — hence `χ̃(r)` agrees with the identity on the frame and on every
  block, so it **is** the identity (`linearMap_eq_of_frame_blockG`).

Everything in *this file* takes `ThetaPreservesJordanG` as a hypothesis — but that
hypothesis is **no longer carried by the row**: real Kadison rigidity, of which we are
aware of no formalization in any other prover though we have not searched them
systematically, is proved in this development
(`Projectivization.exists_isometry_of_transProbPreservingR` in `Wigner/RealWigner.lean`
→ `Necessity.orderAutoR_preservesJordan` in `RealKadison.lean`), and
`RealRowUnconditional.thetaPreservesJordanR_of_S2` discharges it from S2 alone.  So
`RealRowUnconditional.real_classification` is hypothesis-free, and what is a located
hypothesis here is a *theorem* one file downstream.
-/

noncomputable section

open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℝ))

/-! ## The block scalar -/

/-- The scalar by which `χ̃(r)` acts on the one-dimensional block `(i,j)`. -/
def blockScalar (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    (r : n → ℝ) {i j : n} (hij : i ≠ j) : ℝ :=
  (chiTilde_block_existsG P hS2 hjord r hij (1 : ℝ)).choose

theorem blockScalar_spec (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    (chiTildeG P hS2 r).val (blockHermG i j (1 : ℝ))
      = blockHermG i j (blockScalar P hS2 hjord r hij) :=
  (chiTilde_block_existsG P hS2 hjord r hij (1 : ℝ)).choose_spec.1

/-- **The block scalar squares to one.**  `RCLike.normSq` over ℝ is `x * x`, and the
block isometry says it is preserved. -/
theorem blockScalar_sq (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij * blockScalar P hS2 hjord r hij = 1 := by
  have h := (chiTilde_block_existsG P hS2 hjord r hij (1 : ℝ)).choose_spec.2
  simpa [blockScalar, RCLike.normSq_apply] using h

theorem blockScalar_ne_zero (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij ≠ 0 := by
  intro h
  have hsq := blockScalar_sq P hS2 hjord r hij
  rw [h, mul_zero] at hsq
  exact zero_ne_one hsq

/-! ## The scalar at the origin, and its continuity -/

theorem blockScalar_zero (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord 0 hij = 1 := by
  have hspec := blockScalar_spec P hS2 hjord 0 hij
  rw [chiTilde_zeroG P hS2] at hspec
  have h1 : (blockHermG (𝕜 := ℝ) i j (1 : ℝ))
      = blockHermG i j (blockScalar P hS2 hjord 0 hij) := by
    simpa using hspec
  have hentry := congrArg (fun x : HermitianMat n ℝ => x.mat i j) h1
  simp only [blockHerm_matG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hentry
  have hij' : ¬ (j = i ∧ i = j) := fun ⟨h', _⟩ => hij h'.symm
  simp only [Matrix.single, Matrix.of_apply, hij', if_true, if_false, and_self,
    eq_self_iff_true, star_trivial] at hentry
  simpa using hentry.symm

/-- The block scalar reads off as a matrix entry of `χ̃(r)`, which is how its
continuity in `r` is obtained. -/
theorem blockScalar_eq_entry (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij
      = ((chiTildeG P hS2 r).val (blockHermG i j (1 : ℝ))).mat i j := by
  rw [blockScalar_spec P hS2 hjord r hij]
  simp only [blockHerm_matG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hij' : ¬ (j = i ∧ i = j) := fun ⟨h', _⟩ => hij h'.symm
  simp [Matrix.single, hij']

/-! ## Step 3: the sign is `+1`, by connectedness -/

/-- A continuous real function that squares to one and is `1` at the origin is
identically `1`: if it reached `−1` the intermediate value theorem would force a zero,
but a square-root-of-one never vanishes. -/
theorem eq_one_of_sq_eq_one_of_continuous {f : ℝ → ℝ} (hf : Continuous f)
    (hsq : ∀ t, f t * f t = 1) (h0 : f 0 = 1) (t : ℝ) : f t = 1 := by
  by_contra hne
  -- the value at `t` is `−1`
  have hfac : (f t - 1) * (f t + 1) = 0 := by
    have := hsq t; ring_nf; linarith [this]
  have hneg : f t = -1 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith : f t = 1) hne
    · linarith
  -- a zero of `f` between `0` and `t`, by the intermediate value theorem
  have hzero : ∃ s, f s = 0 := by
    rcases le_total 0 t with hle | hle
    · have hsub := intermediate_value_Icc' hle hf.continuousOn
      have hmem : (0 : ℝ) ∈ Set.Icc (f t) (f 0) := by
        rw [hneg, h0]; constructor <;> norm_num
      obtain ⟨s, _, hs⟩ := hsub hmem
      exact ⟨s, hs⟩
    · have hsub := intermediate_value_Icc hle hf.continuousOn
      have hmem : (0 : ℝ) ∈ Set.Icc (f t) (f 0) := by
        rw [hneg, h0]; constructor <;> norm_num
      obtain ⟨s, _, hs⟩ := hsub hmem
      exact ⟨s, hs⟩
  obtain ⟨s, hs⟩ := hzero
  have := hsq s
  rw [hs, mul_zero] at this
  exact zero_ne_one this

/-- **Step 3.** The block scalar is `1` at every parameter: it squares to one, equals
one at the origin, and is continuous along every line, so connectedness rules out
`−1`.  This is the step for which the ℂ lane needed the differential and the phase
cocycle. -/
theorem blockScalar_eq_one (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij = 1 := by
  -- the scalar along the line through `r`, as a continuous function of `t`
  set g : ℝ → ℝ := fun t =>
    ((chiTildeG P hS2 (t • r)).val (blockHermG i j (1 : ℝ))).mat i j with hg
  have hgcont : Continuous g := by
    have h1 : Continuous fun t : ℝ =>
        (chiTildeG P hS2 (t • r)).val (blockHermG (𝕜 := ℝ) i j (1 : ℝ)) :=
      (continuous_chiTilde_lineG P hS2 r).clm_apply continuous_const
    have h2 := continuous_matG h1
    exact (continuous_apply j).comp ((continuous_apply i).comp h2)
  have hgsq : ∀ t, g t * g t = 1 := by
    intro t
    rw [hg]
    have h := blockScalar_sq P hS2 hjord (t • r) hij
    rwa [blockScalar_eq_entry P hS2 hjord (t • r) hij] at h
  have hg0 : g 0 = 1 := by
    rw [hg]
    have h := blockScalar_zero P hS2 hjord (i := i) (j := j) hij
    rw [blockScalar_eq_entry P hS2 hjord 0 hij] at h
    simpa using h
  have h1 := eq_one_of_sq_eq_one_of_continuous hgcont hgsq hg0 1
  rw [blockScalar_eq_entry P hS2 hjord r hij]
  simpa [hg] using h1

/-! ## Step 4: the character is the identity, so the real type is rigid -/

/-- `χ̃(r)` fixes every frame projection (both `Θ` factors do). -/
theorem chiTilde_fixes_frameProjG (hS2 : P.FirstArgContinuous) (r : n → ℝ) (k : n) :
    (chiTildeG P hS2 r).val (frameProjG ℝ k) = frameProjG ℝ k := by
  show (((thetaUnitG P hS2 (r ⊓ 0)) * (thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val)
    (frameProjG ℝ k) = _
  rw [Units.val_mul, ContinuousLinearMap.mul_apply]
  have hinv : ((thetaUnitG P hS2 ((r ⊓ 0) - r))⁻¹).val (frameProjG ℝ k)
      = frameProjG ℝ k := by
    show LinearMap.toContinuousLinearMap
      (thetaNormG P hS2 (diagFamilyG ℝ ((r ⊓ 0) - r))).symm.toLinearMap
        (frameProjG ℝ k) = frameProjG ℝ k
    rw [LinearMap.coe_toContinuousLinearMap']
    have hfwd := thetaNorm_fixes_frameProjG P hS2 ((r ⊓ 0) - r) k
    calc (thetaNormG P hS2 (diagFamilyG ℝ ((r ⊓ 0) - r))).symm (frameProjG ℝ k)
        = (thetaNormG P hS2 (diagFamilyG ℝ ((r ⊓ 0) - r))).symm
            (thetaNormG P hS2 (diagFamilyG ℝ ((r ⊓ 0) - r)) (frameProjG ℝ k)) := by
          rw [hfwd]
      _ = frameProjG ℝ k := LinearEquiv.symm_apply_apply _ _
  rw [hinv]
  show LinearMap.toContinuousLinearMap
    (thetaNormG P hS2 (diagFamilyG ℝ (r ⊓ 0))).toLinearMap (frameProjG ℝ k) = _
  rw [LinearMap.coe_toContinuousLinearMap']
  exact thetaNorm_fixes_frameProjG P hS2 (r ⊓ 0) k

/-- Over ℝ the block is one-dimensional: `blockHerm i j z = z • blockHerm i j 1`. -/
theorem blockHermG_real_smul (i j : n) (z : ℝ) :
    blockHermG (𝕜 := ℝ) i j z = z • blockHermG i j (1 : ℝ) := by
  ext1
  rw [blockHerm_matG, HermitianMat.mat_smul, blockHerm_matG]
  rw [star_trivial, star_trivial, smul_add, smul_smul, smul_smul, mul_one]

/-- **`prop:real`, the capstone: the comparison character on `H_n(ℝ)` is the
identity.**  Hence `Θ_a = id` and the sequential product is the Lüders product — the
real type admits no twist.  Conditional only on S2 and the Jordan property, and the
latter is itself discharged one file downstream by
`RealRowUnconditional.thetaPreservesJordanR_of_S2` (real Kadison is proved in this
tree, in `RealKadison.lean`, on top of first-party real Wigner). -/
theorem chiTilde_eq_id (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) :
    ((chiTildeG P hS2 r).val : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ)
      = LinearMap.id := by
  refine linearMap_eq_of_frame_blockG _ _ ?_ ?_
  · intro k
    show (chiTildeG P hS2 r).val (frameProjG ℝ k) = _
    rw [chiTilde_fixes_frameProjG P hS2 r k]
    rfl
  · intro i j hij z
    show (chiTildeG P hS2 r).val (blockHermG i j z) = _
    rw [blockHermG_real_smul i j z, map_smul,
      blockScalar_spec P hS2 hjord r hij, blockScalar_eq_one P hS2 hjord r hij]
    rw [← blockHermG_real_smul i j z]
    rfl

/-! ## The product level: the real product IS the Lüders product -/

/-- **`prop:real` at the product level.**  On the diagonal family of `H_n(ℝ)`, an
S1–S7 sequential product with S2 (and the located Jordan property) is exactly the
Lüders product `a • b = Q_{√a} b = √a · b · √a`.  There is no twist parameter: the
comparison map is the identity by `chiTilde_eq_id`, so the structural identity
`a • b = Q_{√a}(Θ_a b)` collapses. -/
theorem sp_eq_luders_diagFamily (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) {r : n → ℝ} (hr : ∀ i, r i ≤ 0)
    {b : HermitianMat n ℝ} (hb : IsEffect b) :
    P.sp (diagFamilyG ℝ r) b
      = b.conj ((diagFamilyG ℝ r).cfc Real.sqrt).mat := by
  have ha : IsEffect (diagFamilyG ℝ r) := diagFamilyG_isEffect hr
  have hbd : (diagFamilyG ℝ r).mat.PosDef := diagFamilyG_posDef r
  -- the comparison map at this base point is the character, which is the identity
  have hθ : theta P ha hbd b = b := by
    have hcoe : ((theta P ha hbd : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ))
        = ((chiTildeG P hS2 r).val :
          HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ) := by
      rw [chiTilde_of_nonposG P hS2 hr]
      apply LinearMap.ext
      intro x
      show theta P ha hbd x = _
      rw [← thetaNorm_apply_eq_thetaG P hS2 ha hbd x]
      rfl
    have hid := chiTilde_eq_id P hS2 hjord r
    have h := congrFun (congrArg (fun L : HermitianMat n ℝ →ₗ[ℝ] HermitianMat n ℝ =>
      (L : HermitianMat n ℝ → HermitianMat n ℝ)) (hcoe.trans hid)) b
    simpa using h
  -- the structural identity, with `Θ` collapsed
  have hstruct : P.sp (diagFamilyG ℝ r) b
      = (theta P ha hbd b).conj ((diagFamilyG ℝ r).cfc Real.sqrt).mat := by
    rw [← quadRepEquiv_apply (diagFamilyG ℝ r) hbd, quadRep_theta P ha hbd b,
      seqLeftMul_apply_effect P ha hb]
  rw [hstruct, hθ]

/-! ## Every invertible effect, then every effect -/

/-- The spectral theorem in the shape the real row consumes: a positive-definite
Hermitian matrix is `Ad_U` of a diagonal family whose parameter is its log-spectrum. -/
theorem eq_adUG_diagFamilyG {a : HermitianMat n ℝ} (hbd : a.mat.PosDef) :
    a = adUG (a.H.eigenvectorUnitary : Matrix n n ℝ)
        (diagFamilyG ℝ (fun i => Real.log (a.H.eigenvalues i))) := by
  have hdiag : diagFamilyG ℝ (fun i => Real.log (a.H.eigenvalues i))
      = HermitianMat.diagonal ℝ a.H.eigenvalues := by
    rw [diagFamilyG]
    congr 1
    funext i
    exact Real.exp_log (hbd.eigenvalues_pos i)
  rw [hdiag]
  exact a.eq_conj_diagonal

/-- For an effect the log-spectrum is nonpositive, so the diagonal base point is
itself an effect. -/
theorem log_eigenvalues_nonposR {a : HermitianMat n ℝ} (ha : IsEffect a)
    (hbd : a.mat.PosDef) (i : n) : Real.log (a.H.eigenvalues i) ≤ 0 := by
  have hle : a ≤ (1 : ℝ) • (1 : HermitianMat n ℝ) := by
    rw [one_smul]
    exact le_of_le_of_eq ha.2 HermitianMat.ousUnit_eq_one
  exact Real.log_nonpos (le_of_lt (hbd.eigenvalues_pos i))
    (HermitianMat.le_smul_one_imp_eigenvalues_le a 1 hle i)

/-- **`prop:real` at every invertible effect.**  Diagonalize the base point, apply
the diagonal-family result to the conjugated product, and transport back: `Ad_U`
commutes with `Q_{√·}` because the square root is a functional calculus. -/
theorem sp_eq_luders_of_posDef (hS2 : P.FirstArgContinuous)
    (hjordAll : ∀ (U : Matrix n n ℝ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1),
      ThetaPreservesJordanG (conjProductG P hU hU'))
    {a : HermitianMat n ℝ} (ha : IsEffect a) (hbd : a.mat.PosDef)
    {b : HermitianMat n ℝ} (hb : IsEffect b) :
    P.sp a b = b.conj (a.cfc Real.sqrt).mat := by
  set U : Matrix n n ℝ := (a.H.eigenvectorUnitary : Matrix n n ℝ) with hUdef
  have hU : Uᴴ * U = 1 := by
    have h := a.H.eigenvectorUnitary.property
    rw [Matrix.mem_unitaryGroup_iff'] at h
    rwa [Matrix.star_eq_conjTranspose] at h
  have hU' : U * Uᴴ = 1 := by
    have h := a.H.eigenvectorUnitary.property
    rw [Matrix.mem_unitaryGroup_iff] at h
    rwa [Matrix.star_eq_conjTranspose] at h
  set r : n → ℝ := fun i => Real.log (a.H.eigenvalues i) with hr
  have hrle : ∀ i, r i ≤ 0 := fun i => log_eigenvalues_nonposR ha hbd i
  have hadiag : a = adUG U (diagFamilyG ℝ r) := eq_adUG_diagFamilyG hbd
  -- the conjugated product satisfies the diagonal-family conclusion
  have hQS2 : (conjProductG P hU hU').FirstArgContinuous :=
    conjProduct_firstArgContinuousG P hU hU' hS2
  have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hU'
  have hUU' : Uᴴ * (Uᴴ)ᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hU
  have hb' : IsEffect (adUG Uᴴ b) := adU_isEffectG hUU hUU' hb
  have hdiag := sp_eq_luders_diagFamily (conjProductG P hU hU') hQS2
    (hjordAll U hU hU') hrle hb'
  -- transport: `Ad_U` cancels, and `√` commutes with `Ad_U`
  rw [conjProduct_spG, adU_cancelG' hU' b] at hdiag
  rw [← hadiag] at hdiag
  have hcancel : adUG U (adUG Uᴴ (P.sp a b)) = P.sp a b := adU_cancelG' hU' _
  have hgoal := congrArg (adUG U) hdiag
  rw [hcancel] at hgoal
  rw [hgoal]
  -- unitary covariance of the square root: `Ad_U ∘ Q_{√D} = Q_{√(Ad_U D)} ∘ Ad_U`
  have hsq : (a.cfc Real.sqrt).mat
      = U * ((diagFamilyG ℝ r).cfc Real.sqrt).mat * Uᴴ := by
    conv_lhs => rw [hadiag]
    show (((diagFamilyG ℝ r).conj U).cfc Real.sqrt).mat = _
    rw [HermitianMat.cfc_conj_unitary _ _ a.H.eigenvectorUnitary,
      HermitianMat.conj_apply_mat]
  rw [adUG, adUG, HermitianMat.conj_conj, HermitianMat.conj_conj, hsq,
    Matrix.mul_assoc]

/-! ## Every effect: `prop:real` in full -/

/-- Density of the invertible effects in the effect interval of `H_n(ℝ)`
(the boundary sequence `a + (1/(k+1))(𝟙 − a) → a`), field-general twin of
`dense_posDef_effects`. -/
theorem dense_posDef_effectsR :
    Dense {x : {a : HermitianMat n ℝ // IsEffect a} | x.val.mat.PosDef} := by
  rintro ⟨a, ha⟩
  have hle : ∀ k : ℕ, (1 / ((k : ℝ) + 1)) ≤ 1 := by
    intro k
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h1a : (0 : HermitianMat n ℝ) ≤ 1 - a :=
    sub_nonneg.mpr (le_of_le_of_eq ha.2 HermitianMat.ousUnit_eq_one)
  have hseq : ∀ k : ℕ, IsEffect (a + (1 / ((k : ℝ) + 1)) • (1 - a)) := by
    intro k
    constructor
    · exact _root_.add_nonneg ha.1 (smul_nonneg (by positivity) h1a)
    · have key : (OrderUnitSpace.ousUnit : HermitianMat n ℝ)
          - (a + (1 / ((k : ℝ) + 1)) • (1 - a))
          = (1 - 1 / ((k : ℝ) + 1)) • (1 - a) := by
        rw [HermitianMat.ousUnit_eq_one, sub_smul, one_smul]
        abel
      exact sub_nonneg.mp (key ▸ smul_nonneg (by
        have := hle k; linarith) h1a)
  have hpd : ∀ k : ℕ, (a + (1 / ((k : ℝ) + 1)) • (1 - a)).mat.PosDef := by
    intro k
    have key : a + (1 / ((k : ℝ) + 1)) • (1 - a)
        = (1 / ((k : ℝ) + 1)) • (1 : HermitianMat n ℝ)
          + (1 - 1 / ((k : ℝ) + 1)) • a := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    rw [key, HermitianMat.mat_add]
    have h1 : (((1 / ((k : ℝ) + 1)) • (1 : HermitianMat n ℝ)).mat).PosDef := by
      rw [HermitianMat.mat_smul]
      exact Matrix.PosDef.one.smul (by positivity)
    have h2 : ((((1 - 1 / ((k : ℝ) + 1))) • a).mat).PosSemidef := by
      rw [HermitianMat.mat_smul]
      exact (HermitianMat.zero_le_iff.mp ha.1).smul (by have := hle k; linarith)
    exact h1.add_posSemidef h2
  have htend : Filter.Tendsto (fun k : ℕ => a + (1 / ((k : ℝ) + 1)) • (1 - a))
      Filter.atTop (nhds a) := by
    have h0 : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1))) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := tendsto_const_nhds (x := a) (f := (Filter.atTop : Filter ℕ)) |>.add
      (h0.smul_const (1 - a))
    simpa using h
  apply mem_closure_of_tendsto
    (f := fun k : ℕ => (⟨a + (1 / ((k : ℝ) + 1)) • (1 - a), hseq k⟩ :
      {a : HermitianMat n ℝ // IsEffect a}))
    (b := Filter.atTop)
  · exact tendsto_subtype_rng.mpr htend
  · filter_upwards with k
    exact hpd k

/-- **`prop:real`, THE REAL ROW: every S1–S7 sequential product with S2 on `H_n(ℝ)`
is the Lüders product on ALL effects** — singular ones included.  The real type
admits no twist parameter whatsoever.

Conditional exactly on: S2, and the Jordan property of the comparison map in each
eigenframe (we are aware of no formalization of real Kadison rigidity in any prover, though we
have not searched them systematically, so it is carried as a
located hypothesis, precisely as the manuscript cites it). -/
theorem sp_eq_luders_of_effect (hS2 : P.FirstArgContinuous)
    (hjordAll : ∀ (U : Matrix n n ℝ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1),
      ThetaPreservesJordanG (conjProductG P hU hU'))
    {b : HermitianMat n ℝ} (hb : IsEffect b)
    (a : HermitianMat n ℝ) (ha : IsEffect a) :
    P.sp a b = b.conj (a.cfc Real.sqrt).mat := by
  have hf : Continuous fun x : {a : HermitianMat n ℝ // IsEffect a} =>
      P.sp x.val b :=
    continuousOn_iff_continuous_restrict.mp (hS2 hb)
  have hg : Continuous fun x : {a : HermitianMat n ℝ // IsEffect a} =>
      b.conj ((x.val).cfc Real.sqrt).mat := by
    have hsqrt : Continuous fun x : {a : HermitianMat n ℝ // IsEffect a} =>
        (x.val).cfc Real.sqrt := by
      have := HermitianMat.continuousOn_cfc_sqrt_effects (n := n) (𝕜 := ℝ)
      exact continuousOn_iff_continuous_restrict.mp this
    have hsqrtmat : Continuous fun x : {a : HermitianMat n ℝ // IsEffect a} =>
        ((x.val).cfc Real.sqrt).mat := continuous_subtype_val.comp hsqrt
    exact (HermitianMat.continuous_conj b).comp hsqrtmat
  have hkey := MasterTheorem.prop_singular dense_posDef_effectsR
    (fun x : {a : HermitianMat n ℝ // IsEffect a} => P.sp x.val b)
    (fun x => b.conj ((x.val).cfc Real.sqrt).mat) hf hg
    (fun x hx => sp_eq_luders_of_posDef P hS2 hjordAll x.property hx hb)
  exact congrFun hkey ⟨a, ha⟩

section FrameStabilizerGen

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## The frame stabilizer, at field generality

★★ New 2026-08-09 (ARC-8 block 8.5).  `FrameConstancy.lean`'s `offdiag_eq_zero_of_fixes_frameProj`
and `normSq_diag_eq_one_of_fixes_frameProj` are ℂ-only, and `prop:stabilizers` (row 18) asks the same
question for **each of the four simple types**.  Both proofs use nothing but `adU`, `frameProj` and
matrix algebra, so they generalize to every `RCLike 𝕜` verbatim — which covers the ℝ row as well as
the ℂ row, and is the reason the ℝ row was never the work the row's status implied.

★ What this does NOT give: the article's *identity component* clauses (`{1}` for ℝ, `T^{n-1}` for ℂ).
Those are quotient/connectedness statements about the stabilizer as a group, and no connectedness
vocabulary for these groups exists in the tree (grep `identityComponent|IsConnected|ConnectedComponent`
over `RadicalRelativity/`, 2026-08-09: three hits, two docstring prose and one unrelated).  What is
proved is the stabilizer's *elementwise* description, which is what the Peirce-action computations
actually consume. -/

/-- **A unitary fixing every frame projection is diagonal** — at every `RCLike` field, so this is the
ℝ row and the ℂ row at once. -/
theorem offdiag_eq_zero_of_fixes_frameProjG {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1)
    (hfix : ∀ k, adUG U (frameProjG 𝕜 k) = frameProjG 𝕜 k) :
    ∀ i k, i ≠ k → U i k = 0 := by
  intro i k hik
  have hmat : U * (frameProjG 𝕜 k).mat = (frameProjG 𝕜 k).mat * U := by
    have h := congrArg HermitianMat.mat (hfix k)
    rw [adU_applyG, HermitianMat.conj_apply_mat] at h
    calc U * (frameProjG 𝕜 k).mat
        = (U * (frameProjG 𝕜 k).mat * Uᴴ) * U := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
      _ = (frameProjG 𝕜 k).mat * U := by rw [h]
  have hentry := congrFun (congrFun hmat i) k
  rw [frameProj_mat_eq_singleG] at hentry
  simpa [Matrix.mul_apply, Matrix.single, Ne.symm hik] using hentry

/-- **And its diagonal entries are unimodular**, so the frame stabilizer is exactly the diagonal
torus of the unitary group — at every `RCLike` field.  Over ℝ this says the entries are `±1`. -/
theorem normSq_diag_eq_one_of_fixes_frameProjG {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1)
    (hfix : ∀ k, adUG U (frameProjG 𝕜 k) = frameProjG 𝕜 k) (k : n) :
    ‖U k k‖ = 1 := by
  have hoff := offdiag_eq_zero_of_fixes_frameProjG hU hfix
  have h := congrFun (congrFun hU k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single k (fun i _ hik => by
      rw [Matrix.conjTranspose_apply, hoff i k hik, star_zero, zero_mul])
    (fun hk => absurd (Finset.mem_univ k) hk)] at h
  rw [Matrix.conjTranspose_apply] at h
  rw [RCLike.star_def, RCLike.conj_mul] at h
  have hn : ‖U k k‖ ^ 2 = 1 := by exact_mod_cast h
  nlinarith [hn, norm_nonneg (U k k)]

end FrameStabilizerGen

end Necessity
