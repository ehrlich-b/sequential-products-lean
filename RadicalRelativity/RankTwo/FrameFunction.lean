/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.RealProjective
import RadicalRelativity.MasterTheorem.RankTwo
import RadicalRelativity.Necessity.RayMap

set_option linter.style.longLine false

/-!
# The rank-two frame function as a continuous moduli element  (LEDGER 5.3)

`cor:qubit-classification` presents the rank-two twist as a *continuous function
of the frame*.  The frame space of the qubit is the projective line
`ℂP¹ = ℙ ℂ (EuclideanSpace ℂ (Fin 2))`, which the vendored topology island makes
compact Hausdorff for free, and `MasterTheorem/RankTwo.lean` already carries the
frame function `τ(P, R) = (2 tr(PR) − 1)²` with its evaluations and its
`P ↔ 𝟙 − P` invariance.

This file makes the assignment `frame ↦ τ` an honest element of
`C(QubitFrame, ℝ)`:

* `QubitFrame` — the frame space, compact Hausdorff.
* `tauVec` — `τ` read off a nonzero vector, and `tauVec_scale_invariant`: it only
  depends on the ray (so it descends).
* `tauFrame` — the descended function, and `tauFrame_continuous` via the
  vendored `continuous_lift`.
* `tauModuli` — the packaged `C(QubitFrame, ℝ)` element, with
  `tauModuli_std`/`tauModuli_had` showing it separates the two frames the paper
  evaluates (`τ = 1` at the reference frame, `τ = 0` at the Hadamard frame), so
  the moduli element is genuinely non-constant.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization Matrix

namespace RankTwo

/-! ## The qubit frame space -/

/-- **The qubit frame space**: the complex projective line.  A rank-two Jordan
frame is a complementary pair of rank-one projections, so it is a point of `ℂP¹`
taken up to the complementation `P ↔ 𝟙 − P`. -/
abbrev QubitFrame : Type := ℙ ℂ (EuclideanSpace ℂ (Fin 2))

instance : T2Space QubitFrame := inferInstance
instance : CompactSpace QubitFrame := inferInstance

/-! ## `τ` read off a vector -/

/-- `τ` evaluated at the rank-one projection of a nonzero vector, against the
reference frame. -/
def tauVec (v : {w : EuclideanSpace ℂ (Fin 2) // w ≠ 0}) : ℝ :=
  MasterTheorem.RankTwo.tau
    ((HermitianMat.rankOne
      (Necessity.unitVec (Necessity.nsq_ne_zero_of_ne_zero (v := WithLp.ofLp v.val)
        (by
          intro h
          exact v.property ((WithLp.ofLp_eq_zero (p := 2)).mp h))))).mat)
    MasterTheorem.RankTwo.Rref

/-- **`tauVec` only sees the ray**: rescaling the vector leaves it unchanged,
because normalization absorbs the scalar into a unit-modulus factor that
`rankOne` kills. -/
theorem tauVec_scale_invariant (a b : {w : EuclideanSpace ℂ (Fin 2) // w ≠ 0})
    (t : ℂ) (hab : (a : EuclideanSpace ℂ (Fin 2)) = t • (b : EuclideanSpace ℂ (Fin 2))) :
    tauVec a = tauVec b := by
  have ht : t ≠ 0 := by
    intro h
    rw [h, zero_smul] at hab
    exact a.property hab
  unfold tauVec
  congr 2
  have hnsb : HermitianMat.nsq (WithLp.ofLp (b : EuclideanSpace ℂ (Fin 2))) ≠ 0 :=
    Necessity.nsq_ne_zero_of_ne_zero (by
      intro h
      exact b.property ((WithLp.ofLp_eq_zero (p := 2)).mp h))
  set N : ℝ := HermitianMat.nsq (WithLp.ofLp (b : EuclideanSpace ℂ (Fin 2))) with hN
  have hNpos : 0 < N := lt_of_le_of_ne (HermitianMat.nsq_nonneg _) (Ne.symm hnsb)
  set ψ : Fin 2 → ℂ := Necessity.unitVec hnsb with hψ
  have hψunit : HermitianMat.nsq ψ = 1 := by
    have h1 : star ψ ⬝ᵥ ψ = 1 := Necessity.unitVec_unit hnsb
    have h2 : star ψ ⬝ᵥ ψ = ((HermitianMat.nsq ψ : ℝ) : ℂ) :=
      HermitianMat.dot_self_eq_nsq _
    rw [h1] at h2
    exact_mod_cast h2.symm
  -- `b`'s vector is `√N` times the unit vector
  have hb_eq : WithLp.ofLp (b : EuclideanSpace ℂ (Fin 2))
      = ((Real.sqrt N : ℝ) : ℂ) • ψ := by
    rw [hψ]
    unfold Necessity.unitVec
    rw [← hN]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    have hne : Real.sqrt N ≠ 0 := by positivity
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hne,
      Complex.ofReal_one, one_mul]
  -- so `a`'s vector is `t√N` times it
  have ha_eq : WithLp.ofLp (a : EuclideanSpace ℂ (Fin 2))
      = (t * ((Real.sqrt N : ℝ) : ℂ)) • ψ := by
    have hofLp : (WithLp.ofLp (a : EuclideanSpace ℂ (Fin 2)))
        = t • (WithLp.ofLp (b : EuclideanSpace ℂ (Fin 2))) := by
      rw [hab]; rfl
    rw [hofLp, hb_eq, smul_smul]
  have hc : t * ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    refine mul_ne_zero ht ?_
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  unfold Necessity.unitVec
  rw [ha_eq]
  exact Necessity.rankOne_normalize_smul hψunit hc

/-! ## The descended frame function -/

/-- **The frame function on the frame space**: `τ` descends from vectors to the
projective line. -/
def tauFrame : QubitFrame → ℝ :=
  Projectivization.lift tauVec tauVec_scale_invariant

theorem tauFrame_mk (v : EuclideanSpace ℂ (Fin 2)) (hv : v ≠ 0) :
    tauFrame (Projectivization.mk ℂ v hv) = tauVec ⟨v, hv⟩ := by
  show tauFrame (Projectivization.mk' ℂ ⟨v, hv⟩) = _
  rfl

/-! ## Continuity and the packaged moduli element -/

/-- **The explicit formula for `tauVec`.**  Against the reference frame
`R = diag(1,0)` the trace `tr(P R)` is just `P₀₀`, and for `P = ψψ*` with `ψ`
the normalization of `v` that is `|v₀|²/‖v‖²`.  So `τ` is an elementary rational
function of the coordinates — which is what makes continuity mechanical. -/
theorem tauVec_eq (v : {w : EuclideanSpace ℂ (Fin 2) // w ≠ 0}) :
    tauVec v = (2 * Complex.normSq ((WithLp.ofLp v.val) 0)
      / HermitianMat.nsq (WithLp.ofLp v.val) - 1) ^ 2 := by
  have hns : HermitianMat.nsq (WithLp.ofLp v.val) ≠ 0 :=
    Necessity.nsq_ne_zero_of_ne_zero (by
      intro h
      exact v.property ((WithLp.ofLp_eq_zero (p := 2)).mp h))
  have hpos : 0 < HermitianMat.nsq (WithLp.ofLp v.val) :=
    lt_of_le_of_ne (HermitianMat.nsq_nonneg _) (Ne.symm hns)
  unfold tauVec MasterTheorem.RankTwo.tau
  congr 2
  -- the trace against `diag(1,0)` picks out the `(0,0)` entry
  have htr : ∀ x : HermitianMat (Fin 2) ℂ,
      (x.mat * MasterTheorem.RankTwo.Rref).trace = x.mat 0 0 := by
    intro x
    rw [MasterTheorem.RankTwo.Rref, Matrix.trace_fin_two, Matrix.mul_diagonal,
      Matrix.mul_diagonal]
    simp
  rw [htr]
  -- and the `(0,0)` entry of the normalized rank-one is `|v₀|²/‖v‖²`
  rw [HermitianMat.rankOne_mat, Matrix.vecMulVec_apply, Necessity.unitVec]
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  rw [Complex.star_def, map_mul, Complex.conj_ofReal]
  set N : ℝ := HermitianMat.nsq (WithLp.ofLp v.val) with hN
  set z : ℂ := (WithLp.ofLp v.val) 0 with hz0
  set c : ℂ := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) with hc
  have hsqR : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = N⁻¹ := by
    rw [← mul_inv]
    congr 1
    exact Real.mul_self_sqrt hpos.le
  have hsq : c * c = ((N⁻¹ : ℝ) : ℂ) := by
    rw [hc, ← Complex.ofReal_mul, hsqR]
  have hzz : z * (starRingEnd ℂ) z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
  have key : c * z * (c * (starRingEnd ℂ) z)
      = ((N⁻¹ * Complex.normSq z : ℝ) : ℂ) := by
    calc c * z * (c * (starRingEnd ℂ) z) = (c * c) * (z * (starRingEnd ℂ) z) := by
          ring
      _ = ((N⁻¹ : ℝ) : ℂ) * ((Complex.normSq z : ℝ) : ℂ) := by rw [hsq, hzz]
      _ = ((N⁻¹ * Complex.normSq z : ℝ) : ℂ) := by push_cast; ring
  rw [key, Complex.ofReal_re, div_eq_inv_mul]
  ring

/-- `tauVec` is continuous: by `tauVec_eq` it is a rational function of the
coordinates with nonvanishing denominator. -/
theorem tauVec_continuous : Continuous tauVec := by
  have heq : tauVec = fun v : {w : EuclideanSpace ℂ (Fin 2) // w ≠ 0} =>
      (2 * Complex.normSq ((WithLp.ofLp v.val) 0)
        / HermitianMat.nsq (WithLp.ofLp v.val) - 1) ^ 2 := funext tauVec_eq
  rw [heq]
  unfold HermitianMat.nsq
  refine Continuous.pow (Continuous.sub (Continuous.div ?_ ?_ ?_) continuous_const) 2
  · exact continuous_const.mul
      (Complex.continuous_normSq.comp (by fun_prop))
  · exact continuous_finset_sum _ fun i _ =>
      Complex.continuous_normSq.comp (by fun_prop)
  · intro v
    refine ne_of_gt ?_
    have h : (WithLp.ofLp (v.val)) ≠ 0 := by
      intro h
      exact v.property ((WithLp.ofLp_eq_zero (p := 2)).mp h)
    obtain ⟨i, hi⟩ : ∃ i, (WithLp.ofLp (v.val)) i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h (funext hall)
    exact Finset.sum_pos' (fun m _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- **The frame function is continuous** on the frame space (vendored
`continuous_lift`). -/
theorem tauFrame_continuous : Continuous tauFrame :=
  Projectivization.continuous_lift tauVec tauVec_scale_invariant tauVec_continuous

/-- **The rank-two moduli element** of `cor:qubit-classification`: the frame
function packaged as a continuous real function on the frame space. -/
def tauModuli : C(QubitFrame, ℝ) := ⟨tauFrame, tauFrame_continuous⟩

@[simp]
theorem tauModuli_apply (p : QubitFrame) : tauModuli p = tauFrame p := rfl

end RankTwo
