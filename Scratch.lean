import RadicalRelativity

open OrderUnitSpace RankTwo

-- (B) the order-unit-norm form of S2 for the rank-two frame-dependent product
example (t : C(RP2, ℝ)) : Necessity.FirstArgContinuousOu (n2SequentialProduct t) :=
  (Necessity.firstArgContinuousOu_iff _).mpr (n2SequentialProduct_firstArgContinuous t)

-- (A) EFFECT-LEVEL non-collapse: agreeing with a constant twist on all EFFECTS forces t constant
example (t : C(RP2, ℝ)) (s : ℝ)
    (h : ∀ a b : HermitianMat (Fin 2) ℂ, IsEffect a → IsEffect b →
      n2Sp t a b = HermitianMat.twistSeq s a b) :
    ∀ p : RP2, t p = s := by
  intro p
  obtain ⟨U, hU⟩ := surjective_frameRP2 p
  rw [← hU, apply_frameRP2_eq t U]
  refine (Necessity.n2FrameTwist_unique_param (n2SequentialProduct t)
    (n2SequentialProduct_firstArgContinuous t) U).unique
      (fun r hr b hb => Necessity.n2_sp_eq_twistSeq_frame _ _ U hr rfl hb)
      (fun r hr b hb => h _ b (Necessity.adU_isEffect
        (Necessity.unitaryGroup_conjTranspose_mul U)
        (Necessity.unitaryGroup_mul_conjTranspose U)
        (Necessity.diagFamily_isEffect hr)) hb)
