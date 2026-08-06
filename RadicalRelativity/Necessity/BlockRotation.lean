/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.MulEmbedding

set_option linter.style.longLine false

/-!
# The block action is a rotation  (closing the ℂ lane)

Runs the one-parameter argument on the block character:

* `chiEntryCLM` — `chiEntry` packaged as a continuous linear map, with the
  character laws transported (`chiEntryCLM_zero`, `chiEntryCLM_mul`) and line
  continuity (`chiEntryCLM_continuous_line`).
* `chiEntry_eq_exp` — hence `chiEntry r i j = exp (E r)` for a **unique
  `ℝ`-linear** generator `E` (`multiParameter_eq_exp`).
* `chiEntry_generator_skew` — the generator is skew, by differentiating the
  constant `chiEntry_normSq` at `0` (the pattern of `dChi_block_skew`).
* `chiEntry_is_rotation` — **the block action is a rotation**:
  `chiEntry r i j z = e^{i c(r)} z` for an `ℝ`-linear `c`.  This is the input
  `chiTilde_eq_adU_of_block` was stated modulo.
-/

noncomputable section

open ComplexOrder NormedSpace
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℂ))

/-! ## The block character as continuous linear maps -/

/-- `chiEntry` packaged as a continuous linear map of `ℂ`. -/
def chiEntryCLM (hS2 : P.FirstArgContinuous) (r : n → ℝ) (i j : n) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (chiEntry P hS2 r i j)

@[simp]
theorem chiEntryCLM_apply (hS2 : P.FirstArgContinuous) (r : n → ℝ) (i j : n) (z : ℂ) :
    chiEntryCLM P hS2 r i j z = chiEntry P hS2 r i j z := by
  show LinearMap.toContinuousLinearMap (chiEntry P hS2 r i j) z = _
  rw [LinearMap.coe_toContinuousLinearMap']

theorem chiEntryCLM_zero (hS2 : P.FirstArgContinuous) {i j : n} (hij : i ≠ j) :
    chiEntryCLM P hS2 0 i j = 1 := by
  ext z
  rw [chiEntryCLM_apply, chiEntry_zero P hS2 hij]
  rfl

theorem chiEntryCLM_mul (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) (r r' : n → ℝ) {i j : n} (hij : i ≠ j) :
    chiEntryCLM P hS2 (r + r') i j
      = chiEntryCLM P hS2 r i j * chiEntryCLM P hS2 r' i j := by
  ext z
  rw [chiEntryCLM_apply, chiEntry_add P hS2 hjord r r' hij, LinearMap.comp_apply]
  show _ = (chiEntryCLM P hS2 r i j) ((chiEntryCLM P hS2 r' i j) z)
  rw [chiEntryCLM_apply, chiEntryCLM_apply]

/-- Line continuity: `t ↦ chiEntry (t • v)` is continuous, because
`t ↦ χ̃(t • v)` is (`continuous_chiTilde_line`) and the block coordinates are
continuous linear. -/
theorem chiEntryCLM_continuous_line (hS2 : P.FirstArgContinuous)
    (v : n → ℝ) (i j : n) :
    Continuous fun t : ℝ => chiEntryCLM P hS2 (t • v) i j := by
  have hchi := continuous_chiTilde_line P hS2 v
  -- the entry of the image of a fixed block element, as a function of `t`
  have hpt : ∀ z : ℂ, Continuous fun t : ℝ =>
      chiEntryCLM P hS2 (t • v) i j z := by
    intro z
    have h1 : Continuous fun t : ℝ =>
        ((chiTilde P hS2 (t • v)).val) (blockHerm i j z) := by
      exact hchi.clm_apply continuous_const
    have h2 : Continuous fun t : ℝ =>
        entryCLM i j (((chiTilde P hS2 (t • v)).val) (blockHerm i j z)) :=
      (entryCLM i j).continuous.comp h1
    simpa only [entryCLM_apply, chiEntryCLM_apply, chiEntry_apply] using h2
  -- reconstruct the map from its values at `1` and `I`; the reconstruction is an
  -- ℝ-linear map between finite-dimensional spaces, hence continuous
  have hlin : IsLinearMap ℝ (fun p : ℂ × ℂ =>
      Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2) := by
    constructor
    · intro p q
      ext z
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, Prod.fst_add, Prod.snd_add,
        Complex.real_smul]
      ring
    · intro c p
      ext z
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_smul', Pi.smul_apply, Complex.reCLM_apply,
        Complex.imCLM_apply, Prod.smul_fst, Prod.smul_snd, Complex.real_smul]
      ring
  have hrecon : ∀ t : ℝ, chiEntryCLM P hS2 (t • v) i j
      = Complex.reCLM.smulRight ((chiEntryCLM P hS2 (t • v) i j) 1)
        + Complex.imCLM.smulRight ((chiEntryCLM P hS2 (t • v) i j) Complex.I) := by
    intro t
    ext z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      apply Complex.ext <;> simp [Complex.real_smul]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
  rw [show (fun t : ℝ => chiEntryCLM P hS2 (t • v) i j)
      = (fun p : ℂ × ℂ =>
          Complex.reCLM.smulRight p.1 + Complex.imCLM.smulRight p.2)
        ∘ (fun t : ℝ => ((chiEntryCLM P hS2 (t • v) i j) 1,
            (chiEntryCLM P hS2 (t • v) i j) Complex.I)) from funext hrecon]
  exact (hlin.mk' _).continuous_of_finiteDimensional.comp
    ((hpt 1).prodMk (hpt Complex.I))

/-! ## A general derivative lemma -/

/-- The derivative of `t ↦ exp (t • A) x` at `0` is `A x`, on any complete real
normed space (the general form of `exp_apply_hasDerivAt`). -/
theorem exp_apply_hasDerivAt_gen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (x : E) :
    HasDerivAt (fun t : ℝ => exp (t • A) x) (A x) 0 := by
  have hc := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
  have hu : HasDerivAt (fun _ : ℝ => x) 0 (0 : ℝ) := hasDerivAt_const 0 x
  have hcomb := hc.clm_apply hu
  have h0 : exp ((0 : ℝ) • A) = (1 : E →L[ℝ] E) := by
    rw [show (0 : ℝ) • A = 0 from zero_smul ℝ A]
    exact exp_zero
  rw [h0] at hcomb
  simpa using hcomb

/-! ## The exponential form -/

/-- **The block action is an exponential**: a unique `ℝ`-linear generator `E`
with `chiEntry r i j = exp (E r)`.  This is `multiParameter_eq_exp` in the real
Banach algebra `ℂ →L[ℝ] ℂ`. -/
theorem chiEntry_eq_exp (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) :
    ∃! E : (n → ℝ) →ₗ[ℝ] (ℂ →L[ℝ] ℂ),
      ∀ r : n → ℝ, chiEntryCLM P hS2 r i j = exp (E r) :=
  multiParameter_eq_exp (fun r => chiEntryCLM P hS2 r i j)
    (fun r r' => chiEntryCLM_mul P hS2 hjord r r' hij)
    (chiEntryCLM_zero P hS2 hij)
    (fun v => chiEntryCLM_continuous_line P hS2 v i j)

/-- The generator, as data. -/
def chiEntryGen (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {i j : n} (hij : i ≠ j) : (n → ℝ) →ₗ[ℝ] (ℂ →L[ℝ] ℂ) :=
  (chiEntry_eq_exp P hS2 hjord hij).exists.choose

theorem chiEntry_eq_exp_gen (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) :
    chiEntryCLM P hS2 r i j = exp (chiEntryGen P hS2 hjord hij r) :=
  (chiEntry_eq_exp P hS2 hjord hij).exists.choose_spec r

/-! ## The generator is skew -/

/-- **The generator is skew**: differentiate the constant `chiEntry_normSq` at
`t = 0` along the line through `r` (the pattern of `dChi_block_skew`). -/
theorem chiEntryGen_skew (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) (z : ℂ) :
    z.re * ((chiEntryGen P hS2 hjord hij r) z).re
      + z.im * ((chiEntryGen P hS2 hjord hij r) z).im = 0 := by
  set A := chiEntryGen P hS2 hjord hij r with hA
  -- the curve `t ↦ exp (t • A) z` has constant norm-square
  have hconst : ∀ t : ℝ, Complex.normSq (exp (t • A) z) = Complex.normSq z := by
    intro t
    have hline : exp (t • A) = chiEntryCLM P hS2 (t • r) i j := by
      rw [chiEntry_eq_exp_gen P hS2 hjord hij (t • r), map_smul, hA]
    rw [hline, chiEntryCLM_apply]
    exact chiEntry_normSq P hS2 hjord (t • r) hij z
  -- differentiate at `0`
  have hre : HasDerivAt (fun t : ℝ => (exp (t • A) z).re) (A z).re 0 := by
    have h := (Complex.reCLM.hasFDerivAt (x := exp ((0 : ℝ) • A) z)).comp_hasDerivAt (0 : ℝ)
      (exp_apply_hasDerivAt_gen A z)
    simpa using h
  have him : HasDerivAt (fun t : ℝ => (exp (t • A) z).im) (A z).im 0 := by
    have h := (Complex.imCLM.hasFDerivAt (x := exp ((0 : ℝ) • A) z)).comp_hasDerivAt (0 : ℝ)
      (exp_apply_hasDerivAt_gen A z)
    simpa using h
  have hF : HasDerivAt (fun t : ℝ => Complex.normSq (exp (t • A) z))
      (2 * (z.re * (A z).re + z.im * (A z).im)) 0 := by
    have hz0 : exp ((0 : ℝ) • A) z = z := by
      rw [show (0 : ℝ) • A = 0 from zero_smul ℝ A, exp_zero]
      rfl
    have h := ((hre.mul hre).add (him.mul him))
    rw [hz0] at h
    have heq : (fun t : ℝ => Complex.normSq (exp (t • A) z))
        = fun t : ℝ => (exp (t • A) z).re * (exp (t • A) z).re
          + (exp (t • A) z).im * (exp (t • A) z).im := by
      funext t
      rw [Complex.normSq_apply]
    rw [heq]
    convert h using 1
    ring
  have hC : HasDerivAt (fun _ : ℝ => Complex.normSq z) 0 0 := hasDerivAt_const 0 _
  have hEq : (fun t : ℝ => Complex.normSq (exp (t • A) z))
      = fun _ : ℝ => Complex.normSq z := funext hconst
  rw [hEq] at hF
  have := hF.unique hC
  linarith

/-! ## The block action is a rotation -/

/-- **The block action of `χ̃` is a rotation.**  The generator is skew
(`chiEntryGen_skew`), hence multiplication by `i·c(r)`
(`skew_linear_eq_I_smul`), and `exp` of a multiplication is the multiplication
by `exp` (`exp_mulBy`).  So `χ̃(r)` acts on the `(i,j)` block by
`z ↦ e^{i c(r)} z`, where `c(r)` is the imaginary part of the generator at `1`.

This is exactly the input `chiTilde_eq_adU_of_block` was stated modulo, with
`c(r)` in place of `t (r_i − r_j)`; identifying `c` with that expression is the
coefficient bookkeeping of `complex_perFrame_unconditional`. -/
theorem chiEntry_is_rotation (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordan P) {i j : n} (hij : i ≠ j) (r : n → ℝ) (z : ℂ) :
    chiEntry P hS2 r i j z
      = Complex.exp ((((chiEntryGen P hS2 hjord hij r) 1).im : ℂ) * Complex.I) * z := by
  set A := chiEntryGen P hS2 hjord hij r with hA
  set c : ℝ := (A 1).im with hc
  -- the generator is multiplication by `i c`
  have hgen : (A : ℂ →ₗ[ℝ] ℂ) = mulBy ((c : ℂ) * Complex.I) := by
    apply LinearMap.ext
    intro w
    have hskew : ∀ w : ℂ, w.re * ((A : ℂ →ₗ[ℝ] ℂ) w).re
        + w.im * ((A : ℂ →ₗ[ℝ] ℂ) w).im = 0 := by
      intro w
      exact chiEntryGen_skew P hS2 hjord hij r w
    have h := skew_linear_eq_I_smul (A : ℂ →ₗ[ℝ] ℂ) hskew w
    rw [h, hc]
    show ((A : ℂ →ₗ[ℝ] ℂ) 1).im • (Complex.I * w)
      = ((((A 1).im : ℝ) : ℂ) * Complex.I) * w
    rw [Complex.real_smul, show ((A : ℂ →ₗ[ℝ] ℂ) 1) = A 1 from rfl]
    ring
  have hgenCLM : A = mulBy ((c : ℂ) * Complex.I) := by
    ext w
    have h := congrFun (congrArg (fun L : ℂ →ₗ[ℝ] ℂ => (L : ℂ → ℂ)) hgen) w
    exact h
  -- exponentiate
  have hexp : chiEntryCLM P hS2 r i j = mulByCLM (Complex.exp ((c : ℂ) * Complex.I)) := by
    rw [chiEntry_eq_exp_gen P hS2 hjord hij r, ← hA, hgenCLM,
      exp_generator_is_rotation]
  have h := congrFun (congrArg (fun L : ℂ →L[ℝ] ℂ => (L : ℂ → ℂ)) hexp) z
  simp only [chiEntryCLM_apply, mulByCLM_apply] at h
  exact h

end Necessity
