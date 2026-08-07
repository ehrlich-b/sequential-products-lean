/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.Descent
import RadicalRelativity.RankTwo.RealProjective

set_option linter.style.longLine false

/-!
# The Bloch map `ℂP¹ → ℝP²`  (M5.3, part 2)

`cor:qubit-classification` parametrizes rank-two products by `C(ℝP², ℝ)`, and the
bridge from the frame space `ℂP¹` to `ℝP²` is the **Bloch map**: a ray `[v]` in `ℂ²`
goes to the real 3-vector

`B(v) = (2 Re(v̄₀v₁), 2 Im(v̄₀v₁), |v₀|² − |v₁|²)`,

taken up to real scaling.  Two facts make it the right bridge:

* `blochVec_nsq` — `‖B(v)‖² = ‖v‖⁴`, so `B(v) ≠ 0` whenever `v ≠ 0`;
* `blochVec_orthoVec` — **complementation negates `B`**, and `ℝP²` identifies `x`
  with `−x` (`RP2.mk_neg`), so the Bloch map is *constant on complementation
  classes*.

Together with `Descent.tauFrame_orthoFrame` (the frame function is complementation
invariant) this is the pair of compatible descents that M5.3's assembly needs: both
`τ` and the Bloch map see only the unordered frame.

`blochFrame` packages the map on `ℂP¹` itself, well defined because scaling `v` by
`t` scales `B(v)` by the *positive* real `|t|²`.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace RankTwo

/-! ## The Bloch vector -/

/-- The Bloch vector of `v ∈ ℂ²`, as an element of `ℝ³`. -/
def blochVec (v : Fin 2 → ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![2 * ((starRingEnd ℂ) (v 0) * v 1).re,
    2 * ((starRingEnd ℂ) (v 0) * v 1).im,
    Complex.normSq (v 0) - Complex.normSq (v 1)]

@[simp]
theorem blochVec_apply_zero (v : Fin 2 → ℂ) :
    (WithLp.ofLp (blochVec v)) 0 = 2 * ((starRingEnd ℂ) (v 0) * v 1).re := rfl

@[simp]
theorem blochVec_apply_one (v : Fin 2 → ℂ) :
    (WithLp.ofLp (blochVec v)) 1 = 2 * ((starRingEnd ℂ) (v 0) * v 1).im := rfl

@[simp]
theorem blochVec_apply_two (v : Fin 2 → ℂ) :
    (WithLp.ofLp (blochVec v)) 2
      = Complex.normSq (v 0) - Complex.normSq (v 1) := rfl

/-- **`‖B(v)‖² = ‖v‖⁴`.**  The Bloch vector has the square of the norm, which is
what makes it nonzero on nonzero rays. -/
theorem blochVec_normSq (v : Fin 2 → ℂ) :
    (WithLp.ofLp (blochVec v)) 0 ^ 2 + (WithLp.ofLp (blochVec v)) 1 ^ 2
        + (WithLp.ofLp (blochVec v)) 2 ^ 2
      = (Complex.normSq (v 0) + Complex.normSq (v 1)) ^ 2 := by
  simp only [blochVec_apply_zero, blochVec_apply_one, blochVec_apply_two,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem blochVec_ne_zero {v : Fin 2 → ℂ} (hv : HermitianMat.nsq v ≠ 0) :
    blochVec v ≠ 0 := by
  intro h
  have hsum : HermitianMat.nsq v = Complex.normSq (v 0) + Complex.normSq (v 1) := by
    unfold HermitianMat.nsq
    rw [Fin.sum_univ_two]
  have hz : ∀ i, (WithLp.ofLp (blochVec v)) i = 0 := by
    intro i
    rw [h]
    rfl
  have hkey := blochVec_normSq v
  rw [hz 0, hz 1, hz 2] at hkey
  have : (Complex.normSq (v 0) + Complex.normSq (v 1)) ^ 2 = 0 := by linarith [hkey]
  rw [← hsum] at this
  exact hv (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/-- **Complementation negates the Bloch vector.** -/
theorem blochVec_orthoVec (v : Fin 2 → ℂ) :
    blochVec (orthoVec v) = -blochVec v := by
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;>
    simp [blochVec, orthoVec, Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;>
    ring

/-- Scaling `v` by `t` scales the Bloch vector by the **positive** real `|t|²`, so
the Bloch point is unchanged. -/
theorem blochVec_smul (t : ℂ) (v : Fin 2 → ℂ) :
    blochVec (t • v) = (Complex.normSq t) • blochVec v := by
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;>
    simp [blochVec, Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;>
    ring

/-! ## The Bloch map on the frame space -/

/-- The Bloch vector at the `EuclideanSpace` level. -/
def blochE (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  blochVec (WithLp.ofLp v)

theorem blochE_ne_zero {v : EuclideanSpace ℂ (Fin 2)} (hv : v ≠ 0) : blochE v ≠ 0 :=
  blochVec_ne_zero (Necessity.nsq_ne_zero_of_ne_zero (by
    intro h
    exact hv ((WithLp.ofLp_eq_zero (p := 2)).mp h)))

/-- **The Bloch map on the frame space** `ℂP¹ → ℝP²`.  Well defined because a
rescaling of the ray scales the Bloch vector by the positive real `|t|²`
(`blochVec_smul`), and `ℝP²` quotients by all real scalings. -/
def blochFrame : QubitFrame → RP2 :=
  Projectivization.lift
    (fun v => RP2.mk (blochE v.val) (blochE_ne_zero v.property))
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t hab
      simp only at hab
      apply (RP2.mk_eq_mk_iff _ _).mpr
      refine ⟨Complex.normSq t, ?_⟩
      show (Complex.normSq t) • blochE b = blochE a
      rw [show blochE a = blochVec (WithLp.ofLp a) from rfl,
        show blochE b = blochVec (WithLp.ofLp b) from rfl,
        show WithLp.ofLp a = t • WithLp.ofLp b from by rw [hab]; rfl,
        blochVec_smul])

@[simp]
theorem blochFrame_mk (v : EuclideanSpace ℂ (Fin 2)) (hv : v ≠ 0) :
    blochFrame (Projectivization.mk ℂ v hv) = RP2.mk (blochE v) (blochE_ne_zero hv) := rfl

/-- The Bloch vector is continuous in the vector. -/
theorem blochVec_continuous :
    Continuous (fun v : EuclideanSpace ℂ (Fin 2) => blochE v) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [blochVec] <;> fun_prop

/-- **The Bloch map is continuous** on the frame space (vendored
`continuous_lift`, the same route as `tauFrame_continuous`). -/
theorem blochFrame_continuous : Continuous blochFrame := by
  apply Projectivization.continuous_lift
  exact Projectivization.continuous_mk'.comp
    ((blochVec_continuous.comp continuous_subtype_val).subtype_mk _)

/-- **The Bloch map is complementation invariant**: complementation negates the
Bloch vector, and `ℝP²` identifies antipodes. -/
theorem blochFrame_orthoFrame (p : QubitFrame) :
    blochFrame (orthoFrame p) = blochFrame p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [orthoFrame_mk, blochFrame_mk, blochFrame_mk]
    have hneg : blochE (orthoE v) = -blochE v := by
      show blochVec (WithLp.ofLp (orthoE v)) = -blochVec (WithLp.ofLp v)
      rw [ofLp_orthoE, blochVec_orthoVec]
    rw [show RP2.mk (blochE (orthoE v)) (blochE_ne_zero (orthoE_ne_zero hv))
        = RP2.mk (-blochE v) (by rw [← hneg]; exact blochE_ne_zero (orthoE_ne_zero hv))
        from by congr 1]
    exact RP2.mk_neg _ (blochE_ne_zero hv)

end RankTwo
