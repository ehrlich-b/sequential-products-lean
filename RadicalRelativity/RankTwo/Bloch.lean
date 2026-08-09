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

/-! ## The fibre of the Bloch map is exactly a complementary pair

★★ **New 2026-08-09 (ARC-7 block 7.1c).**  Everything above says the descent *mechanism* is
sound: complementation negates the Bloch vector, so a complementation-invariant frame function
has a chance of descending.  What was missing — and what the `ℝP²` descent for an *arbitrary*
product needs — is the converse: that `blochFrame` identifies **nothing else**.  These lemmas
supply it, so the fibres of `ℂP¹ → ℝP²` are precisely the `{ray, orthogonal ray}` pairs.

The whole content is one positive-scalar computation, and the negative case is free from
`blochVec_orthoVec`.  Note what makes it work: `blochVec_normSq` pins the *scale* of the
proportionality (`‖B(v)‖ = nsq v`), which turns "proportional" into the two equations
`|u_i|² = μ|v_i|²` plus `ū₀u₁ = μ v̄₀v₁` — and those determine the ray outright. -/

theorem fin2_funext {a b : Fin 2 → ℂ} (e0 : a 0 = b 0) (e1 : a 1 = b 1) : a = b := by
  funext i
  fin_cases i
  · exact e0
  · exact e1

/-- Coordinatewise form of a Bloch-vector proportionality. -/
theorem blochVec_coord_of_eq_smul {u v : Fin 2 → ℂ} {μ : ℝ}
    (h : blochVec u = μ • blochVec v) (i : Fin 3) :
    (WithLp.ofLp (blochVec u)) i = μ * (WithLp.ofLp (blochVec v)) i := by
  have hc := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => (WithLp.ofLp w) i) h
  simpa using hc

/-- **The positive-scalar case of the Bloch fibre**: positively proportional Bloch vectors come
from the same ray. -/
theorem exists_smul_of_blochVec_eq_pos_smul {u v : Fin 2 → ℂ} {μ : ℝ} (hμ : 0 < μ)
    (hv : HermitianMat.nsq v ≠ 0) (h : blochVec u = μ • blochVec v) :
    ∃ t : ℂ, u = t • v := by
  have hnsqv : HermitianMat.nsq v = Complex.normSq (v 0) + Complex.normSq (v 1) := by
    unfold HermitianMat.nsq; rw [Fin.sum_univ_two]
  have h0 := blochVec_coord_of_eq_smul h 0
  have h1 := blochVec_coord_of_eq_smul h 1
  have h2 := blochVec_coord_of_eq_smul h 2
  rw [blochVec_apply_zero, blochVec_apply_zero] at h0
  rw [blochVec_apply_one, blochVec_apply_one] at h1
  rw [blochVec_apply_two, blochVec_apply_two] at h2
  -- `blochVec_normSq` pins the scale, which is what makes the coordinates determine the ray
  have hsum : Complex.normSq (u 0) + Complex.normSq (u 1)
      = μ * (Complex.normSq (v 0) + Complex.normSq (v 1)) := by
    have hsq : (Complex.normSq (u 0) + Complex.normSq (u 1)) ^ 2
        = (μ * (Complex.normSq (v 0) + Complex.normSq (v 1))) ^ 2 := by
      rw [← blochVec_normSq u, blochVec_coord_of_eq_smul h 0,
        blochVec_coord_of_eq_smul h 1, blochVec_coord_of_eq_smul h 2,
        show ∀ a b c : ℝ, (μ*a)^2 + (μ*b)^2 + (μ*c)^2 = μ^2 * (a^2+b^2+c^2) from
          fun a b c => by ring, blochVec_normSq v]
      ring
    have hnn1 : 0 ≤ Complex.normSq (u 0) + Complex.normSq (u 1) :=
      add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
    have hnn2 : 0 ≤ μ * (Complex.normSq (v 0) + Complex.normSq (v 1)) :=
      mul_nonneg hμ.le (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    nlinarith [hsq, hnn1, hnn2]
  have hu0 : Complex.normSq (u 0) = μ * Complex.normSq (v 0) := by linarith
  have hu1 : Complex.normSq (u 1) = μ * Complex.normSq (v 1) := by linarith
  have hoff : (starRingEnd ℂ) (u 0) * u 1 = (μ : ℂ) * ((starRingEnd ℂ) (v 0) * v 1) := by
    refine Complex.ext ?_ ?_
    · rw [show ((μ : ℂ) * ((starRingEnd ℂ) (v 0) * v 1)).re
          = μ * ((starRingEnd ℂ) (v 0) * v 1).re from by simp]
      linarith
    · rw [show ((μ : ℂ) * ((starRingEnd ℂ) (v 0) * v 1)).im
          = μ * ((starRingEnd ℂ) (v 0) * v 1).im from by simp]
      linarith
  by_cases hv0 : v 0 = 0
  · have hu0z : u 0 = 0 := by
      refine Complex.normSq_eq_zero.mp ?_
      rw [hu0, hv0]; simp
    have hv1 : v 1 ≠ 0 := by
      intro hz
      rw [hnsqv, hv0, hz] at hv
      simp at hv
    refine ⟨u 1 / v 1, fin2_funext (by simp [hu0z, hv0]) ?_⟩
    change u 1 = u 1 / v 1 * v 1
    field_simp
  · have hnv0 : 0 < Complex.normSq (v 0) :=
      lt_of_le_of_ne (Complex.normSq_nonneg _) (fun hh =>
        hv0 (Complex.normSq_eq_zero.mp hh.symm))
    have hnu0 : 0 < Complex.normSq (u 0) := by rw [hu0]; positivity
    have hu0ne : u 0 ≠ 0 := by
      intro hz
      rw [hz] at hnu0
      simp at hnu0
    have hconjne : (starRingEnd ℂ) (u 0) ≠ 0 := by simpa using hu0ne
    have hcc : (starRingEnd ℂ) (u 0) * u 0 = (μ : ℂ) * ((starRingEnd ℂ) (v 0) * v 0) := by
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self, hu0]
      push_cast
      ring
    refine ⟨u 0 / v 0, fin2_funext ?_ ?_⟩
    · change u 0 = u 0 / v 0 * v 0
      field_simp
    change u 1 = u 0 / v 0 * v 1
    rw [div_mul_eq_mul_div, eq_div_iff hv0]
    refine mul_left_cancel₀ hconjne ?_
    rw [show (starRingEnd ℂ) (u 0) * (u 1 * v 0) = ((starRingEnd ℂ) (u 0) * u 1) * v 0 from by
        ring, hoff,
      show (starRingEnd ℂ) (u 0) * (u 0 * v 1) = ((starRingEnd ℂ) (u 0) * u 0) * v 1 from by
        ring, hcc]
    ring

/-- **The Bloch fibre, both signs.**  A negative proportionality is the positive case applied to
the complement, because complementation negates the Bloch vector. -/
theorem exists_smul_or_ortho_of_blochVec_eq_smul {u v : Fin 2 → ℂ} {μ : ℝ} (hμ : μ ≠ 0)
    (hv : HermitianMat.nsq v ≠ 0) (h : blochVec u = μ • blochVec v) :
    (∃ t : ℂ, u = t • v) ∨ (∃ t : ℂ, u = t • orthoVec v) := by
  rcases lt_or_gt_of_ne hμ with hneg | hpos
  · refine Or.inr (exists_smul_of_blochVec_eq_pos_smul (μ := -μ) (by linarith) ?_ ?_)
    · rw [nsq_orthoVec]; exact hv
    · rw [blochVec_orthoVec, h, smul_neg, neg_smul, neg_neg]
  · exact Or.inl (exists_smul_of_blochVec_eq_pos_smul hpos hv h)

theorem nsq_ofLp_ne_zero {v : EuclideanSpace ℂ (Fin 2)} (hv : v ≠ 0) :
    HermitianMat.nsq (WithLp.ofLp v) ≠ 0 :=
  Necessity.nsq_ne_zero_of_ne_zero (fun h => hv ((WithLp.ofLp_eq_zero (p := 2)).mp h))

/-- **The Bloch map on the frame space is exactly two-to-one, with complementary fibres.**

This is the converse of `blochFrame_orthoFrame` and the ingredient the `ℝP²` descent was
missing: `blochFrame` identifies a ray with its complement **and with nothing else**.  Hence any
complementation-invariant function on `ℂP¹` is constant on the fibres of `blochFrame`, which is
exactly the hypothesis a descent along it needs. -/
theorem blochFrame_eq_iff (p q : QubitFrame) :
    blochFrame p = blochFrame q ↔ (p = q ∨ p = orthoFrame q) := by
  refine ⟨?_, ?_⟩
  · induction p using Projectivization.ind with
    | h u hu =>
      induction q using Projectivization.ind with
      | h v hv =>
        intro hbf
        rw [blochFrame_mk, blochFrame_mk, RP2.mk_eq_mk_iff] at hbf
        obtain ⟨a, ha⟩ := hbf
        have hane : a ≠ 0 := by
          intro hz
          rw [hz, zero_smul] at ha
          exact blochE_ne_zero hu ha.symm
        have hcoord : blochVec (WithLp.ofLp u) = a • blochVec (WithLp.ofLp v) := by
          rw [show blochVec (WithLp.ofLp u) = blochE u from rfl,
            show blochVec (WithLp.ofLp v) = blochE v from rfl, ← ha]
        rcases exists_smul_or_ortho_of_blochVec_eq_smul hane (nsq_ofLp_ne_zero hv) hcoord with
          ⟨t, ht⟩ | ⟨t, ht⟩
        · refine Or.inl ?_
          have htne : t ≠ 0 := by
            intro hz
            rw [hz, zero_smul] at ht
            exact hu ((WithLp.ofLp_eq_zero (p := 2)).mp ht)
          refine (Projectivization.mk_eq_mk_iff ℂ _ _ hu hv).mpr ⟨Units.mk0 t htne, ?_⟩
          apply (WithLp.ofLp_injective (p := 2) (V := Fin 2 → ℂ))
          change t • WithLp.ofLp v = WithLp.ofLp u
          rw [ht]
        · refine Or.inr ?_
          rw [orthoFrame_mk]
          have htne : t ≠ 0 := by
            intro hz
            rw [hz, zero_smul] at ht
            exact hu ((WithLp.ofLp_eq_zero (p := 2)).mp ht)
          refine (Projectivization.mk_eq_mk_iff ℂ _ _ hu (orthoE_ne_zero hv)).mpr
            ⟨Units.mk0 t htne, ?_⟩
          apply (WithLp.ofLp_injective (p := 2) (V := Fin 2 → ℂ))
          change t • WithLp.ofLp (orthoE v) = WithLp.ofLp u
          rw [ofLp_orthoE, ht]
  · rintro (rfl | rfl)
    · rfl
    · exact blochFrame_orthoFrame q

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

@[simp]
theorem tauModuliRP2_apply (p : RP2) : tauModuliRP2 p = tauRP2 p := rfl

/-! ## The bridge: `τ` on `ℝP²` pulls back to `τ` on the frame space -/

/-- `‖B(v)‖ = ‖v‖²`: the Bloch norm is the squared vector norm. -/
theorem sqrt_blochVec_normSq (v : Fin 2 → ℂ) :
    Real.sqrt ((WithLp.ofLp (blochVec v)) 0 ^ 2 + (WithLp.ofLp (blochVec v)) 1 ^ 2
        + (WithLp.ofLp (blochVec v)) 2 ^ 2)
      = HermitianMat.nsq v := by
  have hsum : HermitianMat.nsq v = Complex.normSq (v 0) + Complex.normSq (v 1) := by
    unfold HermitianMat.nsq
    rw [Fin.sum_univ_two]
  rw [blochVec_normSq, ← hsum]
  refine Real.sqrt_sq ?_
  rw [hsum]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- **The bridge identity, at the vector level**: `τ` in Bloch coordinates pulls
back to `τ` on rays.  Both sides are closed forms, so this is algebra:
`2|v₀|²/‖v‖² − 1 = (|v₀|²−|v₁|²)/‖v‖² = B₂/‖B‖`. -/
theorem tauRVec_blochE (v : {w : EuclideanSpace ℂ (Fin 2) // w ≠ 0}) :
    tauRVec ⟨blochE v.val, blochE_ne_zero v.property⟩ = tauVec v := by
  have hns : HermitianMat.nsq (WithLp.ofLp v.val) ≠ 0 :=
    Necessity.nsq_ne_zero_of_ne_zero (by
      intro h
      exact v.property ((WithLp.ofLp_eq_zero (p := 2)).mp h))
  have hsum : HermitianMat.nsq (WithLp.ofLp v.val)
      = Complex.normSq ((WithLp.ofLp v.val) 0) + Complex.normSq ((WithLp.ofLp v.val) 1) := by
    unfold HermitianMat.nsq
    rw [Fin.sum_univ_two]
  rw [tauVec_eq]
  unfold tauRVec
  show (((WithLp.ofLp (blochVec (WithLp.ofLp v.val))) 2)
      / Real.sqrt ((WithLp.ofLp (blochVec (WithLp.ofLp v.val))) 0 ^ 2
        + (WithLp.ofLp (blochVec (WithLp.ofLp v.val))) 1 ^ 2
        + (WithLp.ofLp (blochVec (WithLp.ofLp v.val))) 2 ^ 2)) ^ 2 = _
  rw [sqrt_blochVec_normSq, blochVec_apply_two]
  congr 1
  field_simp
  rw [hsum]
  ring

/-- **The bridge identity**: the `ℝP²` moduli function pulls back along the Bloch
map to the frame function.  So `tauModuliRP2` really is `τ`, expressed on the
carrier `cor:qubit-classification` names. -/
theorem tauRP2_blochFrame (p : QubitFrame) : tauRP2 (blochFrame p) = tauFrame p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [blochFrame_mk, tauFrame_mk]
    show tauRVec ⟨blochE v, blochE_ne_zero hv⟩ = tauVec ⟨v, hv⟩
    exact tauRVec_blochE ⟨v, hv⟩

@[simp]
theorem tauModuliRP2_blochFrame (p : QubitFrame) :
    tauModuliRP2 (blochFrame p) = tauModuli p := tauRP2_blochFrame p

/-! ## The distinguished moduli element is nonconstant -/

/-- `τ = 1` at the standard frame `[1 : 0]`. -/
theorem tauVec_std :
    tauVec ⟨WithLp.toLp 2 ![(1 : ℂ), 0], by
      intro h
      have h0 : (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℂ), 0])) 0 = 0 := by rw [h]; rfl
      simp at h0⟩ = 1 := by
  rw [tauVec_eq]
  norm_num [HermitianMat.nsq, Fin.sum_univ_two]

/-- `τ = 0` at the Hadamard frame `[1 : 1]`. -/
theorem tauVec_had :
    tauVec ⟨WithLp.toLp 2 ![(1 : ℂ), 1], by
      intro h
      have h0 : (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℂ), 1])) 0 = 0 := by rw [h]; rfl
      simp at h0⟩ = 0 := by
  rw [tauVec_eq]
  norm_num [HermitianMat.nsq, Fin.sum_univ_two]

/-- **The moduli element is nonconstant on `ℝP²`.**  It is `1` at the Bloch point of
the standard frame and `0` at that of the Hadamard frame — so the `ℝP²` carrier of
`cor:qubit-classification` is genuinely exercised, not decorative.  (This is the
`ℝP²`-level form of the `V9` separation `tau_std_eq_one` vs `tau_had_eq_zero`.) -/
theorem tauModuliRP2_nonconstant :
    ∃ p q : RP2, tauModuliRP2 p ≠ tauModuliRP2 q := by
  refine ⟨blochFrame (Projectivization.mk ℂ (WithLp.toLp 2 ![(1 : ℂ), 0]) (by
      intro h
      have h0 : (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℂ), 0])) 0 = 0 := by rw [h]; rfl
      simp at h0)),
    blochFrame (Projectivization.mk ℂ (WithLp.toLp 2 ![(1 : ℂ), 1]) (by
      intro h
      have h0 : (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℂ), 1])) 0 = 0 := by rw [h]; rfl
      simp at h0)), ?_⟩
  have h1 : tauModuliRP2 (blochFrame (Projectivization.mk ℂ
      (WithLp.toLp 2 ![(1 : ℂ), 0]) (by
        intro h
        have h0 : (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℂ), 0])) 0 = 0 := by rw [h]; rfl
        simp at h0))) = 1 := by
    rw [tauModuliRP2_apply, tauRP2_blochFrame, tauFrame_mk]
    exact tauVec_std
  have h2 : tauModuliRP2 (blochFrame (Projectivization.mk ℂ
      (WithLp.toLp 2 ![(1 : ℂ), 1]) (by
        intro h
        have h0 : (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℂ), 1])) 0 = 0 := by rw [h]; rfl
        simp at h0))) = 0 := by
    rw [tauModuliRP2_apply, tauRP2_blochFrame, tauFrame_mk]
    exact tauVec_had
  rw [h1, h2]
  norm_num

end RankTwo
