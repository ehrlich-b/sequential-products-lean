import RadicalRelativity
open RankTwo
#print axioms RankTwo.n2QubitModuli
#print axioms RankTwo.n2QubitModuli_apply
#print axioms RankTwo.sp_eq_twistSeq_n2QubitModuli
#print axioms RankTwo.exists_unique_qubitModuli
#print axioms RankTwo.qubit_classification
#print axioms RankTwo.n2QubitModuli_n2SequentialProduct
#print axioms RankTwo.continuous_n2ModuliRP2
#print axioms RankTwo.exists_n2QubitModuli_bound
#print axioms RankTwo.isQuotientMap_frameRP2
#print axioms RankTwo.n2FrameTwist_eq_of_blochFrame_colFrame_eq
-- instance check
example : CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) := inferInstance
example : T2Space RankTwo.RP2 := inferInstance
