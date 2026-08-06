/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ChiExtensionGen


set_option linter.style.longLine false

/-!
# Unitary transport, over any `RCLike` field (M4.1 twin; transport half only) of a sequential product  (Globalization ingredient)

A unitary `U` acts on `H_n(𝕜)` by `Ad_U x = U x U*`, a unital linear order
isomorphism.  Conjugating an S1–S7 product by it gives another S1–S7 product
with S2:

`(P ▷ U).sp a b = Ad_{U*} (P.sp (Ad_U a) (Ad_U b))`.

Since `Ad_U` carries the standard Jordan frame to the frame of `U`'s columns,
this is what makes the **per-frame** family of `thm:complex`'s globalization
concrete: one product per unitary, hence one `t_F` per frame, all from the
single unconditional per-frame theorem.

* `adUG` and the transport lemmas (`adU_unitalG`, `adU_cancelG`, `adU_le_iffG`,
  `adU_isEffectG`, `adU_continuousG`).
* `conjProductG` — the transported product, all nine S1–S7 fields verified.
* `conjProduct_firstArgContinuousG` — S2 transports.
* `conjProduct_perFrame` — the per-frame parameter of the transported product,
  i.e. the `t` field of `ComplexGlobalizationData`, per unitary.
-/

noncomputable section

open ComplexOrder OrderUnitSpace
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## `Ad_U` as a unital order isomorphism -/

/-- Conjugation `x ↦ U x U*`. -/
def adUG (U : Matrix n n 𝕜) (x : HermitianMat n 𝕜) : HermitianMat n 𝕜 := x.conj U

omit [DecidableEq n] in
@[simp]
theorem adU_applyG (U : Matrix n n 𝕜) (x : HermitianMat n 𝕜) :
    adUG U x = x.conj U := rfl

theorem adU_addG (U : Matrix n n 𝕜) (x y : HermitianMat n 𝕜) :
    adUG U (x + y) = adUG U x + adUG U y := map_add (HermitianMat.conj U) x y

omit [DecidableEq n] in
theorem adU_zeroG (U : Matrix n n 𝕜) : adUG U (0 : HermitianMat n 𝕜) = 0 :=
  map_zero (HermitianMat.conj U)

omit [DecidableEq n] in
theorem adU_subG (U : Matrix n n 𝕜) (x y : HermitianMat n 𝕜) :
    adUG U (x - y) = adUG U x - adUG U y := map_sub (HermitianMat.conj U) x y

/-- `Ad_U` is unital when `U U* = 1`. -/
theorem adU_unitalG {U : Matrix n n 𝕜} (hU : U * Uᴴ = 1) :
    adUG U (1 : HermitianMat n 𝕜) = 1 := by
  ext1
  rw [adU_applyG, HermitianMat.conj_apply_mat, HermitianMat.mat_one,
    Matrix.mul_one, hU]

/-- `Ad_{U*}` undoes `Ad_U` when `U* U = 1`. -/
theorem adU_cancelG {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (x : HermitianMat n 𝕜) :
    adUG Uᴴ (adUG U x) = x := by
  rw [adU_applyG, adU_applyG, HermitianMat.conj_conj, hU, HermitianMat.conj_one]

/-- `Ad_U` undoes `Ad_{U*}` when `U U* = 1`. -/
theorem adU_cancelG' {U : Matrix n n 𝕜} (hU' : U * Uᴴ = 1) (x : HermitianMat n 𝕜) :
    adUG U (adUG Uᴴ x) = x := by
  rw [adU_applyG, adU_applyG, HermitianMat.conj_conj, hU', HermitianMat.conj_one]

/-- `Ad_U` reflects and preserves positivity. -/
theorem adU_nonneg_iffG {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (x : HermitianMat n 𝕜) :
    0 ≤ adUG U x ↔ 0 ≤ x := by
  constructor
  · intro h
    have h2 := HermitianMat.conj_nonneg (M := Uᴴ) h
    rwa [adU_applyG, HermitianMat.conj_conj, hU, HermitianMat.conj_one] at h2
  · intro h
    exact HermitianMat.conj_nonneg (M := U) h

/-- `Ad_U` is an order isomorphism. -/
theorem adU_le_iffG {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (x y : HermitianMat n 𝕜) :
    x ≤ y ↔ adUG U x ≤ adUG U y := by
  constructor
  · intro h
    have h2 : (0 : HermitianMat n 𝕜) ≤ adUG U (y - x) :=
      (adU_nonneg_iffG hU _).mpr (sub_nonneg.mpr h)
    rw [adU_subG] at h2
    exact sub_nonneg.mp h2
  · intro h
    have h2 : (0 : HermitianMat n 𝕜) ≤ adUG U y - adUG U x := sub_nonneg.mpr h
    rw [← adU_subG] at h2
    exact sub_nonneg.mp ((adU_nonneg_iffG hU _).mp h2)

/-- `Ad_U` preserves effects. -/
theorem adU_isEffectG {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {x : HermitianMat n 𝕜} (hx : IsEffect x) : IsEffect (adUG U x) := by
  refine ⟨(adU_nonneg_iffG hU x).mpr hx.1, ?_⟩
  have hx2 : x ≤ (1 : HermitianMat n 𝕜) := by
    have h := hx.2
    rwa [HermitianMat.ousUnit_eq_one] at h
  have h1 : adUG U x ≤ adUG U (1 : HermitianMat n 𝕜) := (adU_le_iffG hU x 1).mp hx2
  rw [adU_unitalG hU'] at h1
  rwa [HermitianMat.ousUnit_eq_one]

/-- `Ad_U` is continuous (finite dimensions). -/
theorem adU_continuousG (U : Matrix n n 𝕜) : Continuous (adUG U (n := n)) := by
  have h : adUG U (n := n) = fun x => HermitianMat.conjLinear ℝ U x := rfl
  rw [h]
  exact (HermitianMat.conjLinear ℝ U).continuous_of_finiteDimensional

/-! ## The transported product -/

/-- **The product conjugated by a unitary.**  Every S1–S7 field transports
because `Ad_U` is a unital additive order isomorphism with inverse `Ad_{U*}`. -/
def conjProductG (P : SequentialProductOn (HermitianMat n 𝕜))
    {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1) :
    SequentialProductOn (HermitianMat n 𝕜) where
  sp a b := adUG Uᴴ (P.sp (adUG U a) (adUG U b))
  sp_add_right := by
    intro a b c ha hb hc hsum
    have hbc : IsEffect (adUG U (b + c)) := by
      refine adU_isEffectG hU hU' ?_
      exact ⟨_root_.add_nonneg hb.1 hc.1, hsum⟩
    have hle : adUG U b + adUG U c ≤ ousUnit := by
      rw [HermitianMat.ousUnit_eq_one, ← adU_unitalG hU', ← adU_addG]
      refine (adU_le_iffG hU (b + c) 1).mp ?_
      rwa [HermitianMat.ousUnit_eq_one] at hsum
    show adUG Uᴴ (P.sp (adUG U a) (adUG U (b + c))) = _
    rw [adU_addG, P.sp_add_right (adU_isEffectG hU hU' ha)
      (adU_isEffectG hU hU' hb) (adU_isEffectG hU hU' hc) hle, adU_addG]
  sp_unit_left := by
    intro a ha
    show adUG Uᴴ (P.sp (adUG U ousUnit) (adUG U a)) = a
    rw [HermitianMat.ousUnit_eq_one, adU_unitalG hU', ← HermitianMat.ousUnit_eq_one,
      P.sp_unit_left (adU_isEffectG hU hU' ha), adU_cancelG hU]
  sp_zero_symm := by
    intro a b ha hb h
    show adUG Uᴴ (P.sp (adUG U b) (adUG U a)) = 0
    have h' : P.sp (adUG U a) (adUG U b) = 0 := by
      have := congrArg (adUG U) h
      rwa [adU_cancelG' hU', adU_zeroG] at this
    rw [P.sp_zero_symm (adU_isEffectG hU hU' ha) (adU_isEffectG hU hU' hb) h',
      adU_zeroG]
  sp_assoc_of_compatible := by
    intro a b c ha hb hc hcomm
    have hcomm' : P.sp (adUG U a) (adUG U b) = P.sp (adUG U b) (adUG U a) := by
      have := congrArg (adUG U) hcomm
      rwa [adU_cancelG' hU', adU_cancelG' hU'] at this
    show adUG Uᴴ (P.sp (adUG U a) (adUG U (adUG Uᴴ (P.sp (adUG U b) (adUG U c)))))
      = adUG Uᴴ (P.sp (adUG U (adUG Uᴴ (P.sp (adUG U a) (adUG U b)))) (adUG U c))
    rw [adU_cancelG' hU' (P.sp (adUG U b) (adUG U c))]
    rw [adU_cancelG' hU' (P.sp (adUG U a) (adUG U b))]
    rw [P.sp_assoc_of_compatible (adU_isEffectG hU hU' ha)
      (adU_isEffectG hU hU' hb) (adU_isEffectG hU hU' hc) hcomm']
  compatible_ortho := by
    intro a b ha hb hcomm
    have hcomm' : P.sp (adUG U a) (adUG U b) = P.sp (adUG U b) (adUG U a) := by
      have := congrArg (adUG U) hcomm
      rwa [adU_cancelG' hU', adU_cancelG' hU'] at this
    show adUG Uᴴ (P.sp (adUG U a) (adUG U (ousUnit - b)))
      = adUG Uᴴ (P.sp (adUG U (ousUnit - b)) (adUG U a))
    rw [show adUG U (ousUnit - b) = ousUnit - adUG U b from by
      rw [adU_subG, HermitianMat.ousUnit_eq_one, adU_unitalG hU']]
    rw [P.compatible_ortho (adU_isEffectG hU hU' ha) (adU_isEffectG hU hU' hb) hcomm']
  compatible_add := by
    intro a b c ha hb hc hsum hab hac
    have htr : ∀ {x y : HermitianMat n 𝕜}, P.sp (adUG U x) (adUG U y)
        = P.sp (adUG U y) (adUG U x) → adUG Uᴴ (P.sp (adUG U x) (adUG U y))
          = adUG Uᴴ (P.sp (adUG U y) (adUG U x)) := fun h => by rw [h]
    have hab' : P.sp (adUG U a) (adUG U b) = P.sp (adUG U b) (adUG U a) := by
      have := congrArg (adUG U) hab
      rwa [adU_cancelG' hU', adU_cancelG' hU'] at this
    have hac' : P.sp (adUG U a) (adUG U c) = P.sp (adUG U c) (adUG U a) := by
      have := congrArg (adUG U) hac
      rwa [adU_cancelG' hU', adU_cancelG' hU'] at this
    have hle : adUG U b + adUG U c ≤ ousUnit := by
      rw [HermitianMat.ousUnit_eq_one, ← adU_unitalG hU', ← adU_addG]
      refine (adU_le_iffG hU (b + c) 1).mp ?_
      rwa [HermitianMat.ousUnit_eq_one] at hsum
    show adUG Uᴴ (P.sp (adUG U a) (adUG U (b + c)))
      = adUG Uᴴ (P.sp (adUG U (b + c)) (adUG U a))
    rw [adU_addG]
    rw [P.compatible_add (adU_isEffectG hU hU' ha) (adU_isEffectG hU hU' hb)
      (adU_isEffectG hU hU' hc) hle hab' hac']
  compatible_sp := by
    intro a b c ha hb hc hab hac
    have hab' : P.sp (adUG U a) (adUG U b) = P.sp (adUG U b) (adUG U a) := by
      have := congrArg (adUG U) hab
      rwa [adU_cancelG' hU', adU_cancelG' hU'] at this
    have hac' : P.sp (adUG U a) (adUG U c) = P.sp (adUG U c) (adUG U a) := by
      have := congrArg (adUG U) hac
      rwa [adU_cancelG' hU', adU_cancelG' hU'] at this
    show adUG Uᴴ (P.sp (adUG U a) (adUG U (adUG Uᴴ (P.sp (adUG U b) (adUG U c)))))
      = adUG Uᴴ (P.sp (adUG U (adUG Uᴴ (P.sp (adUG U b) (adUG U c)))) (adUG U a))
    rw [adU_cancelG' hU' (P.sp (adUG U b) (adUG U c))]
    rw [P.compatible_sp (adU_isEffectG hU hU' ha) (adU_isEffectG hU hU' hb)
      (adU_isEffectG hU hU' hc) hab' hac']
  sp_effect := by
    intro a b ha hb
    show IsEffect (adUG Uᴴ (P.sp (adUG U a) (adUG U b)))
    have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hU'
    have hUU' : Uᴴ * (Uᴴ)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hU
    exact adU_isEffectG hUU hUU'
      (P.sp_effect (adU_isEffectG hU hU' ha) (adU_isEffectG hU hU' hb))

@[simp]
theorem conjProduct_spG (P : SequentialProductOn (HermitianMat n 𝕜))
    {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (a b : HermitianMat n 𝕜) :
    (conjProductG P hU hU').sp a b = adUG Uᴴ (P.sp (adUG U a) (adUG U b)) := rfl

/-! ## S2 transports -/

/-- **S2 transports along conjugation**: `Ad` is continuous and carries effects
to effects. -/
theorem conjProduct_firstArgContinuousG (P : SequentialProductOn (HermitianMat n 𝕜))
    {U : Matrix n n 𝕜} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hS2 : P.FirstArgContinuous) :
    (conjProductG P hU hU').FirstArgContinuous := by
  intro b hb
  have hUU : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact hU'
  -- the map is `Ad_{U*} ∘ (· ∘' Ad_U b) ∘ Ad_U`
  have hmaps : Set.MapsTo (adUG U (n := n)) {a : HermitianMat n 𝕜 | IsEffect a}
      {a : HermitianMat n 𝕜 | IsEffect a} := fun a ha => adU_isEffectG hU hU' ha
  have hinner : ContinuousOn (fun a : HermitianMat n 𝕜 => P.sp a (adUG U b))
      {a : HermitianMat n 𝕜 | IsEffect a} := hS2 (adU_isEffectG hU hU' hb)
  have hcomp : ContinuousOn
      (fun a : HermitianMat n 𝕜 => P.sp (adUG U a) (adUG U b))
      {a : HermitianMat n 𝕜 | IsEffect a} :=
    hinner.comp (adU_continuousG U).continuousOn hmaps
  exact (adU_continuousG Uᴴ).comp_continuousOn hcomp

end Necessity
