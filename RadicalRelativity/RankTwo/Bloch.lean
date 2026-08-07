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

end RankTwo
