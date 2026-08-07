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

/-! ## Surjectivity: the inverse Bloch construction -/

/-- The inverse Bloch construction, generic branch: for `w = (x,y,z) ≠ 0` with
`r := z + ‖w‖ > 0`, the ray `v = (r, x + iy)` has `B(v) = 2r • w`.  The key
identity is `r² − (x²+y²) = 2zr`, which is exactly the quadratic `r` solves. -/
theorem blochVec_inverse (x y z : ℝ) (hs : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 2
      = x ^ 2 + y ^ 2 + z ^ 2) :
    blochVec ![((z + Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) : ℝ) : ℂ),
        (x : ℂ) + (y : ℂ) * Complex.I]
      = (2 * (z + Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)))
        • (WithLp.toLp 2 ![x, y, z] : EuclideanSpace ℝ (Fin 3)) := by
  set s : ℝ := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) with hsdef
  set r : ℝ := z + s with hrdef
  apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
  funext i
  fin_cases i <;>
    simp [blochVec, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, hrdef] <;>
    nlinarith [hs, sq_nonneg s, sq_nonneg z]

/-- **The Bloch map is surjective.**  Every point of `ℝP²` is the Bloch point of a
ray: solve `r² − (x²+y²) = 2zr` by `r = z + ‖w‖` on the generic branch, and take the
south pole `(0,1)` on the remaining axis. -/
theorem blochFrame_surjective : Function.Surjective blochFrame := by
  intro q
  induction q using Projectivization.ind with
  | h w hw =>
    set x : ℝ := (WithLp.ofLp w) 0 with hx
    set y : ℝ := (WithLp.ofLp w) 1 with hy
    set z : ℝ := (WithLp.ofLp w) 2 with hz
    have hwe : w = (WithLp.toLp 2 ![x, y, z] : EuclideanSpace ℝ (Fin 3)) := by
      apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
      funext i
      fin_cases i <;> simp [hx, hy, hz]
    have hs : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hne : ¬ (x = 0 ∧ y = 0 ∧ z = 0) := by
      rintro ⟨h0, h1, h2⟩
      apply hw
      rw [hwe]
      apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
      funext i
      fin_cases i <;> simp [h0, h1, h2]
    by_cases hgen : 0 < z + Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
    · -- generic branch
      set r : ℝ := z + Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) with hrdef
      set v : EuclideanSpace ℂ (Fin 2) :=
        WithLp.toLp 2 ![((r : ℝ) : ℂ), (x : ℂ) + (y : ℂ) * Complex.I] with hvdef
      have hv : v ≠ 0 := by
        intro h
        have h0 : (WithLp.ofLp v) 0 = 0 := by rw [h]; rfl
        rw [hvdef] at h0
        simp only [Matrix.cons_val_zero] at h0
        exact (ne_of_gt hgen) (by exact_mod_cast h0)
      refine ⟨Projectivization.mk ℂ v hv, ?_⟩
      rw [blochFrame_mk]
      apply (RP2.mk_eq_mk_iff _ _).mpr
      refine ⟨2 * r, ?_⟩
      show (2 * r) • w = blochE v
      rw [show blochE v = blochVec (WithLp.ofLp v) from rfl, hvdef]
      simp only [WithLp.ofLp_toLp]
      rw [blochVec_inverse x y z hs, ← hwe]
    · -- axis branch: `x = y = 0` and `z < 0`, met by the south pole `(0,1)`
      push_neg at hgen
      set v : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![(0 : ℂ), 1] with hvdef
      have hv : v ≠ 0 := by
        intro h
        have h1 : (WithLp.ofLp v) 1 = 0 := by rw [h]; rfl
        rw [hvdef] at h1
        simp at h1
      -- on this branch `√(x²+y²+z²) ≤ -z`, forcing `x = y = 0` and `z < 0`
      have hsle : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≤ -z := by linarith
      have hznn : z ≤ 0 := by
        have := Real.sqrt_nonneg (x ^ 2 + y ^ 2 + z ^ 2)
        linarith
      have hxy : x = 0 ∧ y = 0 := by
        have h1 : x ^ 2 + y ^ 2 + z ^ 2 ≤ z ^ 2 := by
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ x ^ 2 + y ^ 2 + z ^ 2 by positivity),
            Real.sqrt_nonneg (x ^ 2 + y ^ 2 + z ^ 2), hsle]
        constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
      have hzneg : z < 0 := by
        rcases lt_or_eq_of_le hznn with h | h
        · exact h
        · exact absurd ⟨hxy.1, hxy.2, h⟩ hne
      refine ⟨Projectivization.mk ℂ v hv, ?_⟩
      rw [blochFrame_mk]
      apply (RP2.mk_eq_mk_iff _ _).mpr
      refine ⟨-z⁻¹, ?_⟩
      show (-z⁻¹) • w = blochE v
      rw [show blochE v = blochVec (WithLp.ofLp v) from rfl, hvdef, hwe]
      simp only [WithLp.ofLp_toLp]
      apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
      funext i
      fin_cases i <;>
        simp [blochVec, hxy.1, hxy.2, Complex.normSq_apply] <;>
        field_simp <;>
        exact div_self (ne_of_lt hzneg)

/-! ## `τ` as a function on `ℝP²` -/

/-- `τ` in Bloch coordinates: `(w₂/‖w‖)²`, at the vector level. -/
def tauRVec (w : {u : EuclideanSpace ℝ (Fin 3) // u ≠ 0}) : ℝ :=
  ((WithLp.ofLp w.val) 2 /
    Real.sqrt ((WithLp.ofLp w.val) 0 ^ 2 + (WithLp.ofLp w.val) 1 ^ 2
      + (WithLp.ofLp w.val) 2 ^ 2)) ^ 2

theorem tauRVec_scale_invariant (a b : {u : EuclideanSpace ℝ (Fin 3) // u ≠ 0})
    (t : ℝ) (hab : (a : EuclideanSpace ℝ (Fin 3)) = t • (b : EuclideanSpace ℝ (Fin 3))) :
    tauRVec a = tauRVec b := by
  have ht : t ≠ 0 := by
    intro h
    rw [h, zero_smul] at hab
    exact a.property hab
  have hco : ∀ i, (WithLp.ofLp a.val) i = t * (WithLp.ofLp b.val) i := by
    intro i
    rw [hab]
    rfl
  unfold tauRVec
  rw [hco 0, hco 1, hco 2]
  have hfac : (t * (WithLp.ofLp b.val) 0) ^ 2 + (t * (WithLp.ofLp b.val) 1) ^ 2
        + (t * (WithLp.ofLp b.val) 2) ^ 2
      = t ^ 2 * ((WithLp.ofLp b.val) 0 ^ 2 + (WithLp.ofLp b.val) 1 ^ 2
        + (WithLp.ofLp b.val) 2 ^ 2) := by ring
  rw [hfac, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]
  rcases eq_or_ne (Real.sqrt ((WithLp.ofLp b.val) 0 ^ 2 + (WithLp.ofLp b.val) 1 ^ 2
      + (WithLp.ofLp b.val) 2 ^ 2)) 0 with h | h
  · rw [h]
    simp
  · field_simp

/-- **`τ` as a function on `ℝP²`** — the moduli object's carrier.  Well defined
because `(w₂/‖w‖)²` is invariant under all real rescalings. -/
def tauRP2 : RP2 → ℝ := Projectivization.lift tauRVec tauRVec_scale_invariant

theorem tauRVec_continuous : Continuous tauRVec := by
  apply Continuous.pow
  apply Continuous.div
  · exact (continuous_apply (2 : Fin 3)).comp
      ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  · apply Real.continuous_sqrt.comp
    fun_prop
  · intro w
    intro hzero
    apply w.property
    have hsq : (WithLp.ofLp w.val) 0 ^ 2 + (WithLp.ofLp w.val) 1 ^ 2
        + (WithLp.ofLp w.val) 2 ^ 2 = 0 := by
      have hle := Real.sqrt_eq_zero'.mp hzero
      nlinarith [sq_nonneg ((WithLp.ofLp w.val) 0), sq_nonneg ((WithLp.ofLp w.val) 1),
        sq_nonneg ((WithLp.ofLp w.val) 2), hle]
    apply (WithLp.ofLp_injective (p := 2) (V := Fin 3 → ℝ))
    have h0 : (WithLp.ofLp w.val) 0 = 0 := by
      nlinarith [sq_nonneg ((WithLp.ofLp w.val) 0), sq_nonneg ((WithLp.ofLp w.val) 1),
        sq_nonneg ((WithLp.ofLp w.val) 2), hsq]
    have h1 : (WithLp.ofLp w.val) 1 = 0 := by
      nlinarith [sq_nonneg ((WithLp.ofLp w.val) 0), sq_nonneg ((WithLp.ofLp w.val) 1),
        sq_nonneg ((WithLp.ofLp w.val) 2), hsq]
    have h2 : (WithLp.ofLp w.val) 2 = 0 := by
      nlinarith [sq_nonneg ((WithLp.ofLp w.val) 0), sq_nonneg ((WithLp.ofLp w.val) 1),
        sq_nonneg ((WithLp.ofLp w.val) 2), hsq]
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

theorem tauRP2_continuous : Continuous tauRP2 :=
  Projectivization.continuous_lift tauRVec tauRVec_scale_invariant tauRVec_continuous

/-- **The rank-two moduli element in the paper's carrier**: `τ` as a continuous
real function on `ℝP²`. -/
def tauModuliRP2 : C(RP2, ℝ) := ⟨tauRP2, tauRP2_continuous⟩

end RankTwo
