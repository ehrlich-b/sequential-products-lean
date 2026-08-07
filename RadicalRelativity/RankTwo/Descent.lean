/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.FrameFunction
import RadicalRelativity.RankTwo.Complementation

set_option linter.style.longLine false

/-!
# Complementation on the frame space, and the descent of `τ`  (M5.3, part 1)

`cor:qubit-classification`'s moduli object is `C(ℝP², ℝ)`, and the route there is
`ℂP¹ → ℂP¹ / complementation ≅ ℝP²`.  This file supplies the first half: the
complementation involution **on the frame space** `ℂP¹`, and the fact that the
frame function is invariant under it.

* `orthoE` — `orthoVec` at the `EuclideanSpace` level, with `orthoE_ne_zero`.
* `orthoVec_smul` — `orthoVec` is *conjugate*-linear, `orthoVec (t • v) =
  star t • orthoVec v`; a conjugate-linear map still descends to projective space,
  which is why complementation is well defined on `ℂP¹`.
* `orthoFrame` — the induced involution on `QubitFrame`, with
  `orthoFrame_involutive`.
* **`tauFrame_orthoFrame`** — the frame function is complementation invariant.
  Proved from `tauVec_eq`'s explicit formula rather than from the abstract
  `tau_swap_invariant`: complementation swaps `|v₀|²` and `|v₁|²`, which negates
  `2|v₀|²/‖v‖² − 1`, and that quantity is squared.

With this, `τ` factors through the quotient; identifying that quotient with `ℝP²`
is M5.3's remaining topological step.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace RankTwo

/-! ## Complementation at the vector level -/

/-- `orthoVec` transported to `EuclideanSpace`. -/
def orthoE (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (orthoVec (WithLp.ofLp v))

@[simp]
theorem ofLp_orthoE (v : EuclideanSpace ℂ (Fin 2)) :
    WithLp.ofLp (orthoE v) = orthoVec (WithLp.ofLp v) := rfl

theorem nsq_orthoE (v : EuclideanSpace ℂ (Fin 2)) :
    HermitianMat.nsq (WithLp.ofLp (orthoE v)) = HermitianMat.nsq (WithLp.ofLp v) := by
  rw [ofLp_orthoE, nsq_orthoVec]

theorem orthoE_ne_zero {v : EuclideanSpace ℂ (Fin 2)} (hv : v ≠ 0) : orthoE v ≠ 0 := by
  intro h
  apply hv
  have hns : HermitianMat.nsq (WithLp.ofLp v) = 0 := by
    rw [← nsq_orthoE, h]
    show HermitianMat.nsq (WithLp.ofLp (0 : EuclideanSpace ℂ (Fin 2))) = 0
    simp [HermitianMat.nsq]
  by_contra hne
  exact Necessity.nsq_ne_zero_of_ne_zero
    (v := WithLp.ofLp v) (by
      intro h0
      exact hne ((WithLp.ofLp_eq_zero (p := 2)).mp h0)) hns

/-- **`orthoVec` is conjugate-linear.**  This is what makes complementation
descend to projective space: a scaling `t` becomes `star t`, still a unit. -/
theorem orthoVec_smul (t : ℂ) (v : Fin 2 → ℂ) :
    orthoVec (t • v) = star t • orthoVec v := by
  refine funext ?_
  rw [Fin.forall_fin_two]
  constructor <;>
    simp only [orthoVec_zero, orthoVec_one, Pi.smul_apply, smul_eq_mul,
      Complex.star_def, map_mul, mul_neg]

theorem orthoE_smul (t : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    orthoE (t • v) = star t • orthoE v := by
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 2 → ℂ))
  show orthoVec (WithLp.ofLp (t • v)) = WithLp.ofLp (star t • orthoE v)
  rw [show WithLp.ofLp (t • v) = t • WithLp.ofLp v from rfl, orthoVec_smul]
  rfl

/-! ## Complementation on the frame space -/

/-- **Complementation on `ℂP¹`**: the involution sending a ray to its orthogonal
complement ray.  Well defined because `orthoVec` is conjugate-linear. -/
def orthoFrame : QubitFrame → QubitFrame :=
  Projectivization.lift
    (fun v => Projectivization.mk ℂ (orthoE v.val) (orthoE_ne_zero v.property))
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t hab
      simp only at hab
      have ht : t ≠ 0 := by
        intro h
        rw [h, zero_smul] at hab
        exact ha hab
      apply Projectivization.mk_eq_mk_iff ℂ _ _ _ _ |>.mpr
      refine ⟨Units.mk0 (star t) (star_ne_zero.mpr ht), ?_⟩
      show (star t) • orthoE b = orthoE a
      rw [hab, orthoE_smul])

@[simp]
theorem orthoFrame_mk (v : EuclideanSpace ℂ (Fin 2)) (hv : v ≠ 0) :
    orthoFrame (Projectivization.mk ℂ v hv)
      = Projectivization.mk ℂ (orthoE v) (orthoE_ne_zero hv) := rfl

/-! ## The frame function is complementation invariant -/

/-- **`τ` does not distinguish a ray from its complement.**  By `tauVec_eq`,
`τ(v) = (2|v₀|²/‖v‖² − 1)²`; complementation swaps `|v₀|²` and `|v₁|²`, which
negates the bracket, and the square kills the sign. -/
theorem tauVec_orthoE (v : {w : EuclideanSpace ℂ (Fin 2) // w ≠ 0}) :
    tauVec ⟨orthoE v.val, orthoE_ne_zero v.property⟩ = tauVec v := by
  rw [tauVec_eq, tauVec_eq]
  have hns : HermitianMat.nsq (WithLp.ofLp v.val) ≠ 0 :=
    Necessity.nsq_ne_zero_of_ne_zero (by
      intro h
      exact v.property ((WithLp.ofLp_eq_zero (p := 2)).mp h))
  have hd : HermitianMat.nsq (WithLp.ofLp (orthoE v.val))
      = HermitianMat.nsq (WithLp.ofLp v.val) := nsq_orthoE v.val
  have h0 : Complex.normSq ((WithLp.ofLp (orthoE v.val)) 0)
      = Complex.normSq ((WithLp.ofLp v.val) 1) := by
    rw [ofLp_orthoE, orthoVec_zero, Complex.normSq_neg, Complex.star_def,
      Complex.normSq_conj]
  have hsum : HermitianMat.nsq (WithLp.ofLp v.val)
      = Complex.normSq ((WithLp.ofLp v.val) 0)
        + Complex.normSq ((WithLp.ofLp v.val) 1) := by
    unfold HermitianMat.nsq
    rw [Fin.sum_univ_two]
  rw [hd, h0]
  -- `2y/(x+y) − 1 = −(2x/(x+y) − 1)`, and the square kills the sign
  have hneg : 2 * Complex.normSq ((WithLp.ofLp v.val) 1)
        / HermitianMat.nsq (WithLp.ofLp v.val) - 1
      = -(2 * Complex.normSq ((WithLp.ofLp v.val) 0)
        / HermitianMat.nsq (WithLp.ofLp v.val) - 1) := by
    field_simp
    rw [hsum]
    ring
  rw [hneg, neg_sq]

/-- **The descent input**: the frame function is invariant under complementation,
so it factors through `ℂP¹ / complementation`. -/
theorem tauFrame_orthoFrame (p : QubitFrame) : tauFrame (orthoFrame p) = tauFrame p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [orthoFrame_mk, tauFrame_mk, tauFrame_mk]
    exact tauVec_orthoE ⟨v, hv⟩

end RankTwo
