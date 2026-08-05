/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.Chi
import RadicalRelativity.MasterTheorem.Interface

set_option linter.style.longLine false

/-!
# The concrete `ComparisonSetup` on `H_n(ℂ)`  (campaign LEDGER 2.6/2.8 wiring)

This module instantiates the master-chain interface `MasterTheorem.ComparisonSetup`
on the concrete carrier `HermitianMat (Fin N) ℂ` from an S1–S7 sequential product.
Every interface field except `Θ_jordan` (Kadison/van Imhoff–Roelands rigidity,
campaign M3, taken here as the single hypothesis `ThetaPreservesJordan`) is
discharged by a machine-checked theorem of the necessity development.

* `jordanBilin` — the Jordan product `∘` as an ℝ-bilinear map.
* `opCommute_iff_commute` — **the FK/vdW compatibility bridge, PROVED on `H_n(ℂ)`**:
  Jordan-operator commutation `[L_a, L_b] = 0` is matrix commutation. Quarter
  identity `[L_a, L_b] y = ¼ [[a,b], y]`; commutation with every Hermitian matrix
  makes the commutator scalar (`Matrix.mem_range_scalar_of_commute_single`), and a
  traceless scalar vanishes. The interface docstring cites this bridge as an
  imported hypothesis; on the concrete carrier it is a theorem.
* `theta_fix_general` — the **span-extended** vdW 5.5: `Θ_a` fixes every Hermitian
  matrix commuting with `a` (not only effects), by the positive-part decomposition
  `b = b⁺ − b⁻` and positive homogeneity. Again: cited at the interface, proved here.
* `thetaNorm` — Θ made total on invertible (PosDef) base points by normalization
  `Θ_a := Θ_{(‖a‖+1)⁻¹ • a}`; the 2.3 law `theta_smul` makes the normalization
  invisible on effects, which is exactly why vdW 5.4 exists.
* `comparisonSetup` — the instance. Inputs: rank `3 ≤ N`, S2
  (`FirstArgContinuous`), and `ThetaPreservesJordan` (the M3 import).
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace
open MasterTheorem

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The Jordan product as a bilinear map -/

theorem symmMul_add_right (a b c : HermitianMat n ℂ) :
    a.symmMul (b + c) = a.symmMul b + a.symmMul c := by
  ext1
  simp only [HermitianMat.symmMul_toMat, HermitianMat.mat_add]
  rw [Matrix.mul_add, Matrix.add_mul, ← smul_add]
  congr 1
  abel

theorem symmMul_smul_right (t : ℝ) (a b : HermitianMat n ℂ) :
    a.symmMul (t • b) = t • a.symmMul b := by
  ext1
  simp only [HermitianMat.symmMul_toMat, HermitianMat.mat_smul]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_comm]

/-- The Euclidean Jordan product `x ∘ y = ½(xy + yx)` on `H_n(ℂ)` as an
ℝ-bilinear map — the `jordan` field of the comparison interface. -/
def jordanBilin : HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ →ₗ[ℝ] HermitianMat n ℂ :=
  LinearMap.mk₂ ℝ (fun a b => a.symmMul b)
    (fun a a' b => by
      show (a + a').symmMul b = a.symmMul b + a'.symmMul b
      rw [HermitianMat.symmMul_comm, symmMul_add_right]
      rw [HermitianMat.symmMul_comm (A := b) (B := a),
        HermitianMat.symmMul_comm (A := b) (B := a')])
    (fun t a b => by
      show (t • a).symmMul b = t • a.symmMul b
      rw [HermitianMat.symmMul_comm, symmMul_smul_right,
        HermitianMat.symmMul_comm (A := b) (B := a)])
    (fun a b b' => symmMul_add_right a b b')
    (fun t a b => symmMul_smul_right t a b)

@[simp]
theorem jordanBilin_apply (a b : HermitianMat n ℂ) :
    jordanBilin a b = a.symmMul b := rfl

/-! ## The compatibility bridge: operator commutation = matrix commutation

The quarter identity `[L_a, L_b] y = ¼ [[a,b], y]` reduces Jordan-operator
commutation to the matrix commutator `[a,b]` commuting with every Hermitian
matrix; Hermitians generate `M_n(ℂ)`, so `[a,b]` is scalar, and it is traceless. -/

/-- The quarter identity: `(L_a L_b − L_b L_a) y = ¼ ([a,b] y − y [a,b])`. -/
theorem symmMul_symmMul_sub_mat (a b y : HermitianMat n ℂ) :
    (a.symmMul (b.symmMul y) - b.symmMul (a.symmMul y)).mat
      = (4 : ℂ)⁻¹ • ((a.mat * b.mat - b.mat * a.mat) * y.mat
          - y.mat * (a.mat * b.mat - b.mat * a.mat)) := by
  simp only [HermitianMat.mat_sub, HermitianMat.symmMul_toMat, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub,
    smul_add, smul_sub, Matrix.mul_assoc]
  match_scalars <;> ring

/-- Operator commutation unfolds to pointwise commutation of the Jordan
multiplication operators. -/
theorem opCommute_pointwise {a b : HermitianMat n ℂ}
    (h : OpCommute (jordanBilin (n := n)) a b) (y : HermitianMat n ℂ) :
    a.symmMul (b.symmMul y) = b.symmMul (a.symmMul y) := by
  have := LinearMap.congr_fun h y
  simpa [mulOp, jordanBilin_apply] using this

theorem single_conjTranspose (i j : n) :
    (Matrix.single i j (1 : ℂ))ᴴ = Matrix.single j i (1 : ℂ) := by
  ext p q
  simp only [Matrix.conjTranspose_apply, Matrix.single, Matrix.of_apply]
  by_cases hp : j = p <;> by_cases hq : i = q <;> simp [hp, hq, and_comm]

/-- **The compatibility bridge, hard direction**: Jordan-operator commutation on
`H_n(ℂ)` forces matrix commutation. -/
theorem commute_of_opCommute {a b : HermitianMat n ℂ}
    (h : OpCommute (jordanBilin (n := n)) a b) :
    Commute a.mat b.mat := by
  set C : Matrix n n ℂ := a.mat * b.mat - b.mat * a.mat with hC
  -- step 1: the commutator commutes with every Hermitian matrix
  have hcomm : ∀ y : HermitianMat n ℂ, C * y.mat = y.mat * C := by
    intro y
    have h4 := symmMul_symmMul_sub_mat a b y
    rw [opCommute_pointwise h y, sub_self] at h4
    have hz : C * y.mat - y.mat * C = 0 := by
      have h0 : (0 : Matrix n n ℂ) = (4 : ℂ)⁻¹ • (C * y.mat - y.mat * C) := by
        rw [← h4, HermitianMat.mat_zero]
      rcases smul_eq_zero.mp h0.symm with hbad | hgood
      · exact absurd hbad (by norm_num)
      · exact hgood
    exact sub_eq_zero.mp hz
  -- step 2: hence with every `single i j 1` (Hermitians generate `M_n(ℂ)`)
  have hsingle : ∀ i j : n, Commute (Matrix.single i j (1 : ℂ)) C := by
    intro i j
    have hH1 : (Matrix.single i j (1 : ℂ) + Matrix.single j i (1 : ℂ)).IsHermitian := by
      show _ᴴ = _
      rw [Matrix.conjTranspose_add, single_conjTranspose, single_conjTranspose]
      exact add_comm _ _
    have hH2 : (Complex.I • Matrix.single i j (1 : ℂ)
        - Complex.I • Matrix.single j i (1 : ℂ)).IsHermitian := by
      show _ᴴ = _
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
        single_conjTranspose, single_conjTranspose, Complex.star_def, Complex.conj_I]
      rw [neg_smul, neg_smul, sub_neg_eq_add, ← sub_eq_neg_add]
    have h1 : Commute C (Matrix.single i j (1 : ℂ) + Matrix.single j i (1 : ℂ)) :=
      hcomm ⟨_, hH1⟩
    have h2 : Commute C (Complex.I • Matrix.single i j (1 : ℂ)
        - Complex.I • Matrix.single j i (1 : ℂ)) :=
      hcomm ⟨_, hH2⟩
    have hII : Complex.I • (Complex.I • Matrix.single i j (1 : ℂ)
        - Complex.I • Matrix.single j i (1 : ℂ))
        = Matrix.single j i (1 : ℂ) - Matrix.single i j (1 : ℂ) := by
      rw [smul_sub, smul_smul, smul_smul, Complex.I_mul_I]
      match_scalars <;> ring
    have hcombo : Commute C ((2 : ℂ)⁻¹ • ((Matrix.single i j (1 : ℂ)
        + Matrix.single j i (1 : ℂ)) - Complex.I • (Complex.I • Matrix.single i j (1 : ℂ)
        - Complex.I • Matrix.single j i (1 : ℂ)))) :=
      (h1.sub_right (h2.smul_right Complex.I)).smul_right ((2 : ℂ)⁻¹)
    have hrw : (2 : ℂ)⁻¹ • ((Matrix.single i j (1 : ℂ) + Matrix.single j i (1 : ℂ))
        - Complex.I • (Complex.I • Matrix.single i j (1 : ℂ)
        - Complex.I • Matrix.single j i (1 : ℂ)))
        = Matrix.single i j (1 : ℂ) := by
      rw [hII]
      match_scalars <;> ring
    rw [hrw] at hcombo
    exact hcombo.symm
  -- step 3: scalar and traceless ⟹ zero
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single
    (fun i j _ => hsingle i j)
  have htr : C.trace = 0 := by
    rw [hC, Matrix.trace_sub, Matrix.trace_mul_comm a.mat b.mat, sub_self]
  rcases isEmpty_or_nonempty n with he | hne
  · show a.mat * b.mat = b.mat * a.mat
    ext i _
    exact isEmptyElim i
  · have hcard : (Fintype.card n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (@Fintype.card_ne_zero n _ hne)
    have htr' : (Fintype.card n : ℂ) * r = 0 := by
      rw [← htr, ← hr, Matrix.scalar_apply, Matrix.trace_diagonal]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp htr' with hbad | hgood
      · exact absurd hbad hcard
      · exact hgood
    have hC0 : C = 0 := by
      rw [← hr, hr0, Matrix.scalar_apply]
      simp
    show a.mat * b.mat = b.mat * a.mat
    exact sub_eq_zero.mp hC0

/-- The easy direction: matrix commutation gives Jordan-operator commutation
(pointwise form proved as `symmMul_opCommute_of_commute`, LEDGER 2.5 kit). -/
theorem opCommute_of_commute {a b : HermitianMat n ℂ}
    (hab : Commute a.mat b.mat) :
    OpCommute (jordanBilin (n := n)) a b := by
  apply LinearMap.ext
  intro y
  simp only [mulOp, LinearMap.comp_apply, jordanBilin_apply]
  exact symmMul_opCommute_of_commute hab y

/-- **The FK/vdW compatibility bridge on `H_n(ℂ)`, machine-checked**: Jordan-operator
commutation is matrix commutation. The comparison interface cites this equivalence
(vdW EJA appendix / FK Lemma X.2.2) as an import; the concrete carrier proves it. -/
theorem opCommute_iff_commute {a b : HermitianMat n ℂ} :
    OpCommute (jordanBilin (n := n)) a b ↔ Commute a.mat b.mat :=
  ⟨commute_of_opCommute, opCommute_of_commute⟩

/-! ## Span-extended fixing (vdW 5.5 beyond effects) -/

variable (P : SequentialProductOn (HermitianMat n ℂ))

/-- Θ fixes every *nonnegative* matrix commuting with the base point: normalize to
an effect (`norm_smul_inv_effect`), apply the effect-level `theta_fix`, cancel the
scalar by linearity. -/
theorem theta_fix_nonneg (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) {c : HermitianMat n ℂ}
    (hc : 0 ≤ c) (hac : Commute a.mat c.mat) :
    theta P ha hbd c = c := by
  have hpos : (0 : ℝ) < (‖c‖ + 1)⁻¹ := by positivity
  have heff : IsEffect ((‖c‖ + 1)⁻¹ • c) :=
    norm_smul_inv_effect hc (by positivity) (le_norm_add_one_smul_one c)
  have hcommt : Commute a.mat (((‖c‖ + 1)⁻¹ • c)).mat := by
    rw [HermitianMat.mat_smul]
    exact hac.smul_right _
  have hfix := theta_fix P hS2 ha hbd heff hcommt
  rw [map_smul] at hfix
  exact smul_right_injective (HermitianMat n ℂ) (ne_of_gt hpos) hfix

/-- **The span-extended vdW 5.5, machine-checked**: Θ fixes *every* Hermitian matrix
commuting with the base point (not only effects), via `b = b⁺ − b⁻`. The comparison
interface carries this span-extension as part of its cited `Θ_fix` field; on the
concrete carrier it is a theorem. -/
theorem theta_fix_general (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) (b : HermitianMat n ℂ)
    (hab : Commute a.mat b.mat) :
    theta P ha hbd b = b := by
  have hplus : Commute a.mat (b⁺).mat := by
    rw [HermitianMat.posPart_eq_cfc_max]
    exact Commute.cfc_right _ hab
  have hminus : Commute a.mat (b⁻).mat := by
    rw [HermitianMat.negPart_eq_cfc_min]
    exact Commute.cfc_right _ hab
  calc theta P ha hbd b
      = theta P ha hbd (b⁺) - theta P ha hbd (b⁻) := by
        rw [← map_sub, HermitianMat.posPart_add_negPart]
    _ = b⁺ - b⁻ := by
        rw [theta_fix_nonneg P hS2 ha hbd (HermitianMat.posPart_nonneg b) hplus,
          theta_fix_nonneg P hS2 ha hbd (HermitianMat.negPart_nonneg b) hminus]
    _ = b := HermitianMat.posPart_add_negPart b

/-! ## Θ made total: `thetaNorm` -/

theorem posDef_norm_smul {a : HermitianMat n ℂ} (h : a.mat.PosDef) :
    (((‖a‖ + 1)⁻¹ • a).mat).PosDef := by
  rw [HermitianMat.mat_smul]
  exact h.smul (by positivity)

theorem isEffect_norm_smul {a : HermitianMat n ℂ} (h : a.mat.PosDef) :
    IsEffect ((‖a‖ + 1)⁻¹ • a) :=
  norm_smul_inv_effect (HermitianMat.zero_le_iff.mpr h.posSemidef) (by positivity)
    (le_norm_add_one_smul_one a)

/-- Θ as a *total* function of the base point, defined on positive-definite points
by normalization to the effect `(‖a‖+1)⁻¹ • a` (the identity elsewhere). The 2.3
law `theta_smul` (vdW 5.4) makes the normalization invisible: on effects,
`thetaNorm` agrees with `theta` (`thetaNorm_apply_eq_theta`). -/
def thetaNorm (hS2 : P.FirstArgContinuous) (a : HermitianMat n ℂ) :
    HermitianMat n ℂ ≃ₗ[ℝ] HermitianMat n ℂ :=
  letI := Classical.dec (a.mat.PosDef)
  if h : a.mat.PosDef then
    thetaEquiv P hS2 (isEffect_norm_smul h) (posDef_norm_smul h)
  else LinearEquiv.refl ℝ _

theorem thetaNorm_of_posDef (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) :
    thetaNorm P hS2 a = thetaEquiv P hS2 (isEffect_norm_smul h) (posDef_norm_smul h) := by
  unfold thetaNorm
  exact dif_pos h

/-- On effect base points the normalization is invisible (`theta_smul`). -/
theorem thetaNorm_apply_eq_theta (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (ha : IsEffect a) (hbd : a.mat.PosDef) (x : HermitianMat n ℂ) :
    thetaNorm P hS2 a x = theta P ha hbd x := by
  have ht1 : (‖a‖ + 1)⁻¹ ≤ 1 := by
    have h0 : (0 : ℝ) < ‖a‖ + 1 := by positivity
    have h1 : (1 : ℝ) / (‖a‖ + 1) ≤ 1 :=
      (div_le_one h0).mpr (by linarith [norm_nonneg a])
    simpa [one_div] using h1
  rw [thetaNorm_of_posDef P hS2 hbd, thetaEquiv_apply,
    theta_smul P hS2 ha hbd (by positivity) ht1
      (isEffect_norm_smul hbd) (posDef_norm_smul hbd)]

theorem thetaNorm_one (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) : thetaNorm P hS2 a 1 = 1 := by
  rw [thetaNorm_of_posDef P hS2 h, thetaEquiv_apply, theta_one]

theorem thetaNorm_nonneg_iff (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) (x : HermitianMat n ℂ) :
    0 ≤ x ↔ 0 ≤ thetaNorm P hS2 a x := by
  rw [thetaNorm_of_posDef P hS2 h, thetaEquiv_apply]
  exact (theta_nonneg_iff P hS2 _ _ x).symm

theorem thetaNorm_fix (hS2 : P.FirstArgContinuous) {a : HermitianMat n ℂ}
    (h : a.mat.PosDef) (b : HermitianMat n ℂ)
    (hab : OpCommute (jordanBilin (n := n)) a b) :
    thetaNorm P hS2 a b = b := by
  have hc : Commute a.mat b.mat := commute_of_opCommute hab
  rw [thetaNorm_of_posDef P hS2 h, thetaEquiv_apply]
  apply theta_fix_general P hS2 _ _ b
  rw [HermitianMat.mat_smul]
  exact hc.smul_left _

/-- **The M3 import, isolated**: every effect-level comparison map preserves the
Jordan product (van Imhoff–Roelands / Kadison rigidity; the paper's `prop:theta`).
This single hypothesis is what milestone M3 discharges. -/
def ThetaPreservesJordan : Prop :=
  ∀ {a : HermitianMat n ℂ} (ha : IsEffect a) (hbd : a.mat.PosDef),
    PreservesJordan (theta P ha hbd)

theorem thetaNorm_jordan (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {a : HermitianMat n ℂ} (h : a.mat.PosDef) (x y : HermitianMat n ℂ) :
    thetaNorm P hS2 a (jordanBilin x y)
      = jordanBilin (thetaNorm P hS2 a x) (thetaNorm P hS2 a y) := by
  rw [thetaNorm_of_posDef P hS2 h]
  simp only [thetaEquiv_apply, jordanBilin_apply]
  exact hjord (isEffect_norm_smul h) (posDef_norm_smul h) x y

/-- The χ̃ cocycle transported to `thetaNorm` (LinearEquiv form, `.trans` order). -/
theorem thetaNorm_cocycle (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P)
    {r r' : n → ℝ} (hr : ∀ i, r i ≤ 0) (hr' : ∀ i, r' i ≤ 0) :
    thetaNorm P hS2 (diagFamily (r + r'))
      = (thetaNorm P hS2 (diagFamily r)).trans (thetaNorm P hS2 (diagFamily r')) := by
  have hsum : ∀ i, (r + r') i ≤ 0 := fun i => add_nonpos (hr i) (hr' i)
  have hsum' : ∀ i, (r' + r) i ≤ 0 := fun i => add_nonpos (hr' i) (hr i)
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.trans_apply]
  rw [thetaNorm_apply_eq_theta P hS2 (diagFamily_isEffect hr) (diagFamily_posDef r) x]
  rw [thetaNorm_apply_eq_theta P hS2 (diagFamily_isEffect hr') (diagFamily_posDef r')]
  rw [thetaNorm_apply_eq_theta P hS2
    (diagFamily_isEffect hsum) (diagFamily_posDef (r + r')) x]
  have hcongr : theta P (diagFamily_isEffect hsum) (diagFamily_posDef (r + r'))
      = theta P (diagFamily_isEffect hsum') (diagFamily_posDef (r' + r)) :=
    theta_congr P (by rw [add_comm]) _ _ _ _
  have hm := thetaD_mul P hS2 hr' hr
    (hjord (diagFamily_isEffect hr') (diagFamily_posDef r'))
  rw [hcongr, hm]
  rfl

/-! ## The instance -/

theorem one_symmMul (x : HermitianMat n ℂ) :
    (1 : HermitianMat n ℂ).symmMul x = x := by
  rw [HermitianMat.symmMul_comm, HermitianMat.symmMul_one]

/-- **The concrete `ComparisonSetup` on `H_N(ℂ)`.** Every field is discharged by a
machine-checked theorem of this development, except the single cited import
`Θ_jordan`, taken as the hypothesis `hjord : ThetaPreservesJordan P` (van
Imhoff–Roelands / Kadison rigidity — campaign milestone M3). In particular the
FK/vdW facts the interface documents as imports (`frame_opCommute`, the
compatibility bridge inside `Θ_fix`, the span extension of vdW 5.5) are *proved*
here, not imported. -/
def comparisonSetup {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    ComparisonSetup (HermitianMat (Fin N) ℂ) where
  jordan := jordanBilin
  e := 1
  jordan_comm := fun x y => HermitianMat.symmMul_comm (A := x) (B := y)
  jordan_unit := fun x => one_symmMul x
  n := N
  rank_ge := hN
  p := frameProj
  nonneg := fun x => 0 ≤ x
  Inv := fun a => a.mat.PosDef
  aOf := diagFamily
  aOf_inv := diagFamily_posDef
  Θ := thetaNorm P hS2
  Θ_unital := fun _ h => thetaNorm_one P hS2 h
  Θ_orderIso := fun _ h x => thetaNorm_nonneg_iff P hS2 h x
  Θ_jordan := fun _ h x y => thetaNorm_jordan P hS2 hjord h x y
  Θ_fix := fun _ h b hb => thetaNorm_fix P hS2 h b hb
  frame_opCommute := fun r i => opCommute_of_commute (diagFamily_commute_frameProj r i)
  Θ_cocycle := fun _ _ hr hr' => thetaNorm_cocycle P hS2 hjord hr hr'

end Necessity
