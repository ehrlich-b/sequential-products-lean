import RadicalRelativity

/-! Cold-review probe: two DISTINCT S1–S7+S2 products on H_2(ℂ) with the SAME ℝP² moduli
function.  If this compiles, the map `product ↦ moduli` is not injective, so no bijection
between `C(ℝP², ℝ)` and the products (as `.sp` functions) can exist — and the row-35 residue
"the onto half at singular effects" is not the whole residue. -/

open Necessity RankTwo

/-- `badP t`'s frame parameter is the constant `t` at every frame. -/
theorem badP_frameTwist (t : ℝ) (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    Necessity.n2FrameTwist (Necessity.badP t) (Necessity.badP_S2 t) U = t := by
  refine (Necessity.n2FrameTwist_unique_param (Necessity.badP t) (Necessity.badP_S2 t) U).unique
    (fun r hr b hb => Necessity.n2_sp_eq_twistSeq_frame _ _ U hr rfl hb) ?_
  intro r hr b hb
  have ha : IsEffect (Necessity.adU (U : Matrix (Fin 2) (Fin 2) ℂ) (Necessity.diagFamily r)) :=
    Necessity.adU_isEffect (Necessity.unitaryGroup_conjTranspose_mul U)
      (Necessity.unitaryGroup_mul_conjTranspose U) (Necessity.diagFamily_isEffect hr)
  rw [Necessity.badP_sp, Necessity.badSp_eq ha hb, Necessity.twistProductOn_sp]

/-- The two products have the *same* element of the moduli object `C(ℝP², ℝ)`. -/
theorem moduli_collide (t : ℝ) :
    RankTwo.n2QubitModuli (Necessity.badP t) (Necessity.badP_S2 t)
      = RankTwo.n2QubitModuli (RankTwo.n2SequentialProduct (ContinuousMap.const RankTwo.RP2 t))
        (RankTwo.n2SequentialProduct_firstArgContinuous _) := by
  rw [RankTwo.n2QubitModuli_n2SequentialProduct]
  ext p
  obtain ⟨U, hU⟩ := RankTwo.surjective_frameRP2 p
  rw [← hU, RankTwo.n2QubitModuli_apply, badP_frameTwist]
  rfl

theorem not_isEffect_two_smul_one : ¬ IsEffect ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) := by
  intro h
  have h0 : (0 : HermitianMat (Fin 2) ℂ) ≤ 1 - (2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ) :=
    sub_nonneg.mpr (le_of_le_of_eq h.2 HermitianMat.ousUnit_eq_one)
  have hpsd := HermitianMat.zero_le_iff.mp h0
  have hd : (0 : ℂ) ≤ (1 - (2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)).mat 0 0 :=
    Matrix.PosSemidef.diag_nonneg hpsd 0
  have hval : (1 - (2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)).mat 0 0 = (-1 : ℂ) := by
    simp [Matrix.one_apply_eq]
  rw [hval] at hd
  have := (Complex.le_def.mp hd).1
  norm_num at this

/-- The two products are NOT equal as `.sp` functions: they differ at a non-effect first
argument, where the axioms say nothing. -/
theorem sp_differs (t : ℝ) :
    (Necessity.badP t).sp ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) 1
      ≠ (RankTwo.n2SequentialProduct (ContinuousMap.const RankTwo.RP2 t)).sp
          ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)) 1 := by
  rw [Necessity.badP_sp, Necessity.badSp_eq_zero (fun h => not_isEffect_two_smul_one h.1)]
  show (0 : HermitianMat (Fin 2) ℂ) ≠ RankTwo.n2Sp _ _ _
  rw [RankTwo.n2Sp_smul_one_left _ (by norm_num : (0 : ℝ) ≤ 2)]
  intro hcon
  have h00 : (0 : HermitianMat (Fin 2) ℂ).mat 0 0
      = ((2 : ℝ) • (1 : HermitianMat (Fin 2) ℂ)).mat 0 0 := by rw [hcon]
  simp [Matrix.one_apply_eq] at h00

#print axioms moduli_collide
#print axioms sp_differs
