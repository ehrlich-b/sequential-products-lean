/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.KadisonDischarge
import RadicalRelativity.MasterTheorem.Adapter

set_option linter.style.longLine false

/-!
# Unitary transport of a sequential product  (Globalization ingredient)

A unitary `U` acts on `H_n(ℂ)` by `Ad_U x = U x U*`, a unital linear order
isomorphism.  Conjugating an S1–S7 product by it gives another S1–S7 product
with S2:

`(P ▷ U).sp a b = Ad_{U*} (P.sp (Ad_U a) (Ad_U b))`.

Since `Ad_U` carries the standard Jordan frame to the frame of `U`'s columns,
this is what makes the **per-frame** family of `thm:complex`'s globalization
concrete: one product per unitary, hence one `t_F` per frame, all from the
single unconditional per-frame theorem.

* `adU` and the transport lemmas (`adU_unital`, `adU_cancel`, `adU_le_iff`,
  `adU_isEffect`, `adU_continuous`).
* `conjProduct` — the transported product, all nine S1–S7 fields verified.
* `conjProduct_firstArgContinuous` — S2 transports.
* `conjProduct_perFrame` — the per-frame parameter of the transported product,
  i.e. the `t` field of `ComplexGlobalizationData`, per unitary.
-/

noncomputable section

open ComplexOrder OrderUnitSpace
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## `Ad_U` as a unital order isomorphism -/

/-- Conjugation `x ↦ U x U*`. -/
def adU (U : Matrix n n ℂ) (x : HermitianMat n ℂ) : HermitianMat n ℂ := x.conj U

omit [DecidableEq n] in
@[simp]
theorem adU_apply (U : Matrix n n ℂ) (x : HermitianMat n ℂ) :
    adU U x = x.conj U := rfl

theorem adU_add (U : Matrix n n ℂ) (x y : HermitianMat n ℂ) :
    adU U (x + y) = adU U x + adU U y := map_add (HermitianMat.conj U) x y

omit [DecidableEq n] in
theorem adU_zero (U : Matrix n n ℂ) : adU U (0 : HermitianMat n ℂ) = 0 :=
  map_zero (HermitianMat.conj U)

omit [DecidableEq n] in
theorem adU_sub (U : Matrix n n ℂ) (x y : HermitianMat n ℂ) :
    adU U (x - y) = adU U x - adU U y := map_sub (HermitianMat.conj U) x y

/-- `Ad_U` is unital when `U U* = 1`. -/
theorem adU_unital {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) :
    adU U (1 : HermitianMat n ℂ) = 1 := by
  ext1
  rw [adU_apply, HermitianMat.conj_apply_mat, HermitianMat.mat_one,
    Matrix.mul_one, hU]

/-! ### `Ad_U` is a Frobenius isometry

Two elementary norm facts about conjugation, and they carry more weight than their size
suggests: together they are what makes S2 at the *single* point `𝟙` yield a scale valid at
**every** frame, which is the step `lem:n2-bounded` turns on (`FrameConstancy.lean`).

`LEDGER-ARCHIVE-M1-M7.md` recorded that Mathlib has `frobenius_norm_def` "but no congruence
invariance". That is still true of Mathlib, and it is why these are proved here — but the proof
is three lines, because on `HermitianMat` the Frobenius norm is `√⟪a,a⟫ = √(re tr(a·a))` and
trace cyclicity does all the work. No entrywise argument is needed. -/

/-- Conjugation by a unitary preserves the Frobenius norm. Proved by trace cyclicity, not
entrywise. -/
theorem norm_conj_unitary (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (a : HermitianMat n ℂ) :
    ‖a.conj U‖ = ‖a‖ := by
  rw [HermitianMat.norm_eq_sqrt_inner_self, HermitianMat.norm_eq_sqrt_inner_self]
  congr 1
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  rw [HermitianMat.conj_apply_mat]
  calc (U * a.mat * Uᴴ * (U * a.mat * Uᴴ)).trace
      = (U * (a.mat * a.mat) * Uᴴ).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [show Uᴴ * (U * (a.mat * Uᴴ)) = (Uᴴ * U) * (a.mat * Uᴴ) by
          simp only [Matrix.mul_assoc]]
        rw [hU, Matrix.one_mul]
    _ = (a.mat * a.mat).trace := by
        rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- `Ad_U` is an isometry for the Frobenius norm. -/
theorem norm_adU (U : Matrix n n ℂ) (hU : Uᴴ * U = 1) (a : HermitianMat n ℂ) :
    ‖adU U a‖ = ‖a‖ := norm_conj_unitary U hU a

omit [DecidableEq n] in
/-- Every entry is bounded by the Frobenius norm.  With `norm_adU`, this is how a *matrix
entry* of a conjugated difference gets controlled by the difference's norm. -/
theorem norm_entry_le_norm (a : HermitianMat n ℂ) (i j : n) :
    ‖a.mat i j‖ ≤ ‖a‖ := by
  rw [HermitianMat.norm_eq_frobenius, ← Real.sqrt_eq_rpow,
    show ‖a.mat i j‖ = √(‖a.mat i j‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
  refine Real.sqrt_le_sqrt ?_
  simp only [HermitianMat.mat_apply]
  have hinner : ‖a i j‖ ^ 2 ≤ ∑ j' : n, ‖a i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' : n => ‖a i j'‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have houter : (∑ j' : n, ‖a i j'‖ ^ 2) ≤ ∑ i' : n, ∑ j' : n, ‖a i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' : n => ∑ j' : n, ‖a i' j'‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  linarith

/-- `Ad_{U*}` undoes `Ad_U` when `U* U = 1`. -/
theorem adU_cancel {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (x : HermitianMat n ℂ) :
    adU Uᴴ (adU U x) = x := by
  rw [adU_apply, adU_apply, HermitianMat.conj_conj, hU, HermitianMat.conj_one]

/-- `Ad_U` undoes `Ad_{U*}` when `U U* = 1`. -/
theorem adU_cancel' {U : Matrix n n ℂ} (hU' : U * Uᴴ = 1) (x : HermitianMat n ℂ) :
    adU U (adU Uᴴ x) = x := by
  rw [adU_apply, adU_apply, HermitianMat.conj_conj, hU', HermitianMat.conj_one]

/-- `Ad_U` reflects and preserves positivity. -/
theorem adU_nonneg_iff {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (x : HermitianMat n ℂ) :
    0 ≤ adU U x ↔ 0 ≤ x := by
  constructor
  · intro h
    have h2 := HermitianMat.conj_nonneg (M := Uᴴ) h
    rwa [adU_apply, HermitianMat.conj_conj, hU, HermitianMat.conj_one] at h2
  · intro h
    exact HermitianMat.conj_nonneg (M := U) h

/-- `Ad_U` is an order isomorphism. -/
theorem adU_le_iff {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (x y : HermitianMat n ℂ) :
    x ≤ y ↔ adU U x ≤ adU U y := by
  constructor
  · intro h
    have h2 : (0 : HermitianMat n ℂ) ≤ adU U (y - x) :=
      (adU_nonneg_iff hU _).mpr (sub_nonneg.mpr h)
    rw [adU_sub] at h2
    exact sub_nonneg.mp h2
  · intro h
    have h2 : (0 : HermitianMat n ℂ) ≤ adU U y - adU U x := sub_nonneg.mpr h
    rw [← adU_sub] at h2
    exact sub_nonneg.mp ((adU_nonneg_iff hU _).mp h2)

/-- `Ad_U` preserves effects. -/
theorem adU_isEffect {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {x : HermitianMat n ℂ} (hx : IsEffect x) : IsEffect (adU U x) := by
  refine ⟨(adU_nonneg_iff hU x).mpr hx.1, ?_⟩
  have hx2 : x ≤ (1 : HermitianMat n ℂ) := by
    have h := hx.2
    rwa [HermitianMat.ousUnit_eq_one] at h
  have h1 : adU U x ≤ adU U (1 : HermitianMat n ℂ) := (adU_le_iff hU x 1).mp hx2
  rw [adU_unital hU'] at h1
  rwa [HermitianMat.ousUnit_eq_one]

/-- `Ad_U` is continuous (finite dimensions). -/
theorem adU_continuous (U : Matrix n n ℂ) : Continuous (adU U (n := n)) := by
  have h : adU U (n := n) = fun x => HermitianMat.conjLinear ℝ U x := rfl
  rw [h]
  exact (HermitianMat.conjLinear ℝ U).continuous_of_finiteDimensional

/-! ## The transported product -/

/-- **The product conjugated by a unitary.**  Every S1–S7 field transports
because `Ad_U` is a unital additive order isomorphism with inverse `Ad_{U*}`. -/
def conjProduct (P : SequentialProductOn (HermitianMat n ℂ))
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    SequentialProductOn (HermitianMat n ℂ) where
  sp a b := adU Uᴴ (P.sp (adU U a) (adU U b))
  sp_add_right := by
    intro a b c ha hb hc hsum
    have hbc : IsEffect (adU U (b + c)) := by
      refine adU_isEffect hU hU' ?_
      exact ⟨_root_.add_nonneg hb.1 hc.1, hsum⟩
    have hle : adU U b + adU U c ≤ ousUnit := by
      rw [HermitianMat.ousUnit_eq_one, ← adU_unital hU', ← adU_add]
      refine (adU_le_iff hU (b + c) 1).mp ?_
      rwa [HermitianMat.ousUnit_eq_one] at hsum
    show adU Uᴴ (P.sp (adU U a) (adU U (b + c))) = _
    rw [adU_add, P.sp_add_right (adU_isEffect hU hU' ha)
      (adU_isEffect hU hU' hb) (adU_isEffect hU hU' hc) hle, adU_add]
  sp_unit_left := by
    intro a ha
    show adU Uᴴ (P.sp (adU U ousUnit) (adU U a)) = a
    rw [HermitianMat.ousUnit_eq_one, adU_unital hU', ← HermitianMat.ousUnit_eq_one,
      P.sp_unit_left (adU_isEffect hU hU' ha), adU_cancel hU]
  sp_zero_symm := by
    intro a b ha hb h
    show adU Uᴴ (P.sp (adU U b) (adU U a)) = 0
    have h' : P.sp (adU U a) (adU U b) = 0 := by
      have := congrArg (adU U) h
      rwa [adU_cancel' hU', adU_zero] at this
    rw [P.sp_zero_symm (adU_isEffect hU hU' ha) (adU_isEffect hU hU' hb) h',
      adU_zero]
  sp_assoc_of_compatible := by
    intro a b c ha hb hc hcomm
    have hcomm' : P.sp (adU U a) (adU U b) = P.sp (adU U b) (adU U a) := by
      have := congrArg (adU U) hcomm
      rwa [adU_cancel' hU', adU_cancel' hU'] at this
    show adU Uᴴ (P.sp (adU U a) (adU U (adU Uᴴ (P.sp (adU U b) (adU U c)))))
      = adU Uᴴ (P.sp (adU U (adU Uᴴ (P.sp (adU U a) (adU U b)))) (adU U c))
    rw [adU_cancel' hU' (P.sp (adU U b) (adU U c))]
    rw [adU_cancel' hU' (P.sp (adU U a) (adU U b))]
    rw [P.sp_assoc_of_compatible (adU_isEffect hU hU' ha)
      (adU_isEffect hU hU' hb) (adU_isEffect hU hU' hc) hcomm']
  compatible_ortho := by
    intro a b ha hb hcomm
    have hcomm' : P.sp (adU U a) (adU U b) = P.sp (adU U b) (adU U a) := by
      have := congrArg (adU U) hcomm
      rwa [adU_cancel' hU', adU_cancel' hU'] at this
    show adU Uᴴ (P.sp (adU U a) (adU U (ousUnit - b)))
      = adU Uᴴ (P.sp (adU U (ousUnit - b)) (adU U a))
    rw [show adU U (ousUnit - b) = ousUnit - adU U b from by
      rw [adU_sub, HermitianMat.ousUnit_eq_one, adU_unital hU']]
    rw [P.compatible_ortho (adU_isEffect hU hU' ha) (adU_isEffect hU hU' hb) hcomm']
  compatible_add := by
    intro a b c ha hb hc hsum hab hac
    have htr : ∀ {x y : HermitianMat n ℂ}, P.sp (adU U x) (adU U y)
        = P.sp (adU U y) (adU U x) → adU Uᴴ (P.sp (adU U x) (adU U y))
          = adU Uᴴ (P.sp (adU U y) (adU U x)) := fun h => by rw [h]
    have hab' : P.sp (adU U a) (adU U b) = P.sp (adU U b) (adU U a) := by
      have := congrArg (adU U) hab
      rwa [adU_cancel' hU', adU_cancel' hU'] at this
    have hac' : P.sp (adU U a) (adU U c) = P.sp (adU U c) (adU U a) := by
      have := congrArg (adU U) hac
      rwa [adU_cancel' hU', adU_cancel' hU'] at this
    have hle : adU U b + adU U c ≤ ousUnit := by
      rw [HermitianMat.ousUnit_eq_one, ← adU_unital hU', ← adU_add]
      refine (adU_le_iff hU (b + c) 1).mp ?_
      rwa [HermitianMat.ousUnit_eq_one] at hsum
    show adU Uᴴ (P.sp (adU U a) (adU U (b + c)))
      = adU Uᴴ (P.sp (adU U (b + c)) (adU U a))
    rw [adU_add]
    rw [P.compatible_add (adU_isEffect hU hU' ha) (adU_isEffect hU hU' hb)
      (adU_isEffect hU hU' hc) hle hab' hac']
  compatible_sp := by
    intro a b c ha hb hc hab hac
    have hab' : P.sp (adU U a) (adU U b) = P.sp (adU U b) (adU U a) := by
      have := congrArg (adU U) hab
      rwa [adU_cancel' hU', adU_cancel' hU'] at this
    have hac' : P.sp (adU U a) (adU U c) = P.sp (adU U c) (adU U a) := by
      have := congrArg (adU U) hac
      rwa [adU_cancel' hU', adU_cancel' hU'] at this
    show adU Uᴴ (P.sp (adU U a) (adU U (adU Uᴴ (P.sp (adU U b) (adU U c)))))
      = adU Uᴴ (P.sp (adU U (adU Uᴴ (P.sp (adU U b) (adU U c)))) (adU U a))
    rw [adU_cancel' hU' (P.sp (adU U b) (adU U c))]
    rw [P.compatible_sp (adU_isEffect hU hU' ha) (adU_isEffect hU hU' hb)
      (adU_isEffect hU hU' hc) hab' hac']
  sp_effect := by
    intro a b ha hb
    show IsEffect (adU Uᴴ (P.sp (adU U a) (adU U b)))
    have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hU'
    have hUU' : Uᴴ * (Uᴴ)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hU
    exact adU_isEffect hUU hUU'
      (P.sp_effect (adU_isEffect hU hU' ha) (adU_isEffect hU hU' hb))

@[simp]
theorem conjProduct_sp (P : SequentialProductOn (HermitianMat n ℂ))
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (a b : HermitianMat n ℂ) :
    (conjProduct P hU hU').sp a b = adU Uᴴ (P.sp (adU U a) (adU U b)) := rfl

/-! ## S2 transports -/

/-- **S2 transports along conjugation**: `Ad` is continuous and carries effects
to effects. -/
theorem conjProduct_firstArgContinuous (P : SequentialProductOn (HermitianMat n ℂ))
    {U : Matrix n n ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hS2 : P.FirstArgContinuous) :
    (conjProduct P hU hU').FirstArgContinuous := by
  intro b hb
  have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hU'
  -- the map is `Ad_{U*} ∘ (· ∘' Ad_U b) ∘ Ad_U`
  have hmaps : Set.MapsTo (adU U (n := n)) {a : HermitianMat n ℂ | IsEffect a}
      {a : HermitianMat n ℂ | IsEffect a} := fun a ha => adU_isEffect hU hU' ha
  have hinner : ContinuousOn (fun a : HermitianMat n ℂ => P.sp a (adU U b))
      {a : HermitianMat n ℂ | IsEffect a} := hS2 (adU_isEffect hU hU' hb)
  have hcomp : ContinuousOn
      (fun a : HermitianMat n ℂ => P.sp (adU U a) (adU U b))
      {a : HermitianMat n ℂ | IsEffect a} :=
    hinner.comp (adU_continuous U).continuousOn hmaps
  exact (adU_continuous Uᴴ).comp_continuousOn hcomp

/-! ## The per-frame parameter, per unitary -/

/-- **The per-frame family of `thm:complex`, made concrete.**  For each unitary
`U` — equivalently, each Jordan frame of `H_N(ℂ)` — the product conjugated by
`U` is again an S1–S7 product with S2, so the unconditional per-frame theorem
supplies its own single parameter.  This is the `t` field of
`ComplexGlobalizationData`. -/
theorem conjProduct_perFrame {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    {U : Matrix (Fin N) (Fin N) ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    ∃ tF : ℝ, ∀ (i j : Fin N) (r : Fin N → ℝ),
      (stabilizerCoupling hN (conjProduct P hU hU')
          (conjProduct_firstArgContinuous P hU hU' hS2)
          (thetaPreservesJordan_of_S2 _
            (conjProduct_firstArgContinuous P hU hU' hS2))).ρ i j
        ((stabilizerCoupling hN (conjProduct P hU hU')
          (conjProduct_firstArgContinuous P hU hU' hS2)
          (thetaPreservesJordan_of_S2 _
            (conjProduct_firstArgContinuous P hU hU' hS2))).dχ r)
      = (tF * (r i - r j)) • rotJ :=
  complex_perFrame_unconditional hN (conjProduct P hU hU')
    (conjProduct_firstArgContinuous P hU hU' hS2)

/-! ## The frame family and the single global parameter -/

/-- The unitarity halves of a member of the unitary group, in `ᴴ` form. -/
theorem unitaryGroup_conjTranspose_mul {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) : (U.val)ᴴ * U.val = 1 := by
  have h := U.property
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rwa [Matrix.star_eq_conjTranspose] at h

theorem unitaryGroup_mul_conjTranspose {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) : U.val * (U.val)ᴴ = 1 := by
  have h := U.property
  rw [Matrix.mem_unitaryGroup_iff] at h
  rwa [Matrix.star_eq_conjTranspose] at h

/-- **The per-frame twist parameter as a function of the frame.**  A frame of
`H_N(ℂ)` is the image of the standard frame under a unitary, so the unitary
group indexes the frames; `frameTwist` is the parameter the unconditional
per-frame theorem produces at each one. -/
def frameTwist {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin N) ℂ) : ℝ :=
  (conjProduct_perFrame hN P hS2 (unitaryGroup_conjTranspose_mul U)
    (unitaryGroup_mul_conjTranspose U)).choose

/-- The defining property of `frameTwist` at each frame. -/
theorem frameTwist_spec {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ∀ (i j : Fin N) (r : Fin N → ℝ),
      (stabilizerCoupling hN
          (conjProduct P (unitaryGroup_conjTranspose_mul U)
            (unitaryGroup_mul_conjTranspose U))
          (conjProduct_firstArgContinuous P _ _ hS2)
          (thetaPreservesJordan_of_S2 _
            (conjProduct_firstArgContinuous P _ _ hS2))).ρ i j
        ((stabilizerCoupling hN
          (conjProduct P (unitaryGroup_conjTranspose_mul U)
            (unitaryGroup_mul_conjTranspose U))
          (conjProduct_firstArgContinuous P _ _ hS2)
          (thetaPreservesJordan_of_S2 _
            (conjProduct_firstArgContinuous P _ _ hS2))).dχ r)
      = (frameTwist hN P hS2 U * (r i - r j)) • rotJ :=
  (conjProduct_perFrame hN P hS2 (unitaryGroup_conjTranspose_mul U)
    (unitaryGroup_mul_conjTranspose U)).choose_spec

/-- **`thm:complex`, the global step, on `H_N(ℂ)`.**

For any S1–S7 product with S2 on `H_N(ℂ)` (`N ≥ 3`), the per-frame parameters
`frameTwist` collapse to a **single global** `t`, given the paper's two
frame-graph inputs as explicit hypotheses:

* `connected` — `lem:frame-connectivity` (paper-proved; carried as a located
  hypothesis, never an axiom);
* `overlap` — the cross-coherence agreement of adjacent frames' `U(1)`
  characters on an open interval.

The collapse itself — including the `2π`-ambiguity-free character uniqueness —
is the machine-checked `Globalization.global_t`. -/
theorem complex_global_twist_concrete {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    (Adj : Matrix.unitaryGroup (Fin N) ℂ → Matrix.unitaryGroup (Fin N) ℂ → Prop)
    (connected : ∀ F G, Relation.ReflTransGen
      (MasterTheorem.Globalization.SymmStep Adj) F G)
    (overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧ ∀ x ∈ Set.Ioo a b,
      Complex.exp ((frameTwist hN P hS2 F : ℂ) * x * Complex.I)
        = Complex.exp ((frameTwist hN P hS2 G : ℂ) * x * Complex.I)) :
    ∃ t : ℝ, ∀ U, frameTwist hN P hS2 U = t :=
  MasterTheorem.global_twist_of_perFrame (frameTwist hN P hS2) Adj connected overlap

end Necessity
