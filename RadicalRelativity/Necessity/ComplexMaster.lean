/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComplexClassification
import RadicalRelativity.Necessity.RateFromCoupling
import RadicalRelativity.Necessity.ConjTransport

set_option linter.style.longLine false

/-!
# `mthm:master`, the complex row  (`H_N(ℂ)`, `N ≥ 3`)

The whole ℂ lane, assembled into one statement.

* `sp_eq_twistSeq_of_frameGraph` — for an S1–S7 product with S2, the **single
  global** twist parameter (`complex_global_twist_concrete`) governs *every*
  invertible effect: diagonalize the base point into its eigenframe, read the
  per-frame rate off the coupling there (`frameTwist_spec` +
  `tvalLm_of_coupling`), apply the diagonal twist theorem
  (`sp_eq_twistSeq_diagFamily`), and transport back
  (`sp_eq_twistSeq_transport`).
* `complex_classification` — **the complex row of `mthm:master`**: there is a
  **unique** real `t` with `a • b = a^{1/2+it} b a^{1/2−it}` on **all** effects.

Hypothesis accounting, exactly: S1–S7 (the `SequentialProductOn` fields), S2
(`hS2`), `N ≥ 3`, and the paper's two frame-graph facts carried as located
hypotheses — `connected` (`lem:frame-connectivity`) and `overlap`
(cross-coherence agreement of adjacent frames' characters).  Nothing else: the
Jordan property of the comparison map is *derived* (M3,
`thetaPreservesJordan_of_S2`), not assumed, and the tree carries no custom
axioms.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace MasterTheorem

namespace Necessity

/-- **One global parameter governs every invertible effect.** -/
theorem sp_eq_twistSeq_of_frameGraph {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    (Adj : Matrix.unitaryGroup (Fin N) ℂ → Matrix.unitaryGroup (Fin N) ℂ → Prop)
    (connected : ∀ F G, Relation.ReflTransGen
      (MasterTheorem.Globalization.SymmStep Adj) F G)
    (overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧ ∀ x ∈ Set.Ioo a b,
      Complex.exp ((frameTwist hN P hS2 F : ℂ) * x * Complex.I)
        = Complex.exp ((frameTwist hN P hS2 G : ℂ) * x * Complex.I)) :
    ∃ t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ,
      IsEffect a → a.mat.PosDef → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b := by
  obtain ⟨t, hglob⟩ := complex_global_twist_concrete hN P hS2 Adj connected overlap
  refine ⟨t, ?_⟩
  intro a b ha hbd hb
  have hU := unitaryGroup_conjTranspose_mul a.H.eigenvectorUnitary
  have hU' := unitaryGroup_mul_conjTranspose a.H.eigenvectorUnitary
  have hQS2 : (conjProduct P hU hU').FirstArgContinuous :=
    conjProduct_firstArgContinuous P hU hU' hS2
  have hrle : ∀ k, Real.log (a.H.eigenvalues k) ≤ 0 := fun k =>
    log_eigenvalues_nonpos ha hbd k
  -- the per-frame rate in `a`'s eigenframe IS the global parameter
  have hcollapse : ∀ i j : Fin N, i ≠ j →
      tvalLm (conjProduct P hU hU') hQS2
          (thetaPreservesJordan_of_S2 _ hQS2) i j
          (fun k => Real.log (a.H.eigenvalues k))
        = t * (Real.log (a.H.eigenvalues i) - Real.log (a.H.eigenvalues j)) := by
    intro i j hij
    have hc := frameTwist_spec hN P hS2 a.H.eigenvectorUnitary
    rw [hglob a.H.eigenvectorUnitary] at hc
    exact tvalLm_of_coupling hN (conjProduct P hU hU') hQS2
      (thetaPreservesJordan_of_S2 _ hQS2) t hc hij _
  -- diagonal theorem in that frame, then transport back
  exact sp_eq_twistSeq_transport P hU hU' (eq_adU_diagFamily hbd) t
    (fun b' hb' => sp_eq_twistSeq_diagFamily (conjProduct P hU hU') hQS2
      (thetaPreservesJordan_of_S2 _ hQS2) t hrle hcollapse hb') hb

/-- **`mthm:master`, the complex row.**  For an S1–S7 sequential product with S2
on `H_N(ℂ)`, `N ≥ 3`, there is a **unique** real `t` with

`a • b = a^{1/2+it} · b · a^{1/2−it}`

for **every** pair of effects (singular ones included).  The paper's two
frame-graph facts are the only carried hypotheses beyond S1–S7 + S2. -/
theorem complex_classification {N : ℕ} (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous)
    (Adj : Matrix.unitaryGroup (Fin N) ℂ → Matrix.unitaryGroup (Fin N) ℂ → Prop)
    (connected : ∀ F G, Relation.ReflTransGen
      (MasterTheorem.Globalization.SymmStep Adj) F G)
    (overlap : ∀ F G, Adj F G → ∃ a b : ℝ, a < b ∧ ∀ x ∈ Set.Ioo a b,
      Complex.exp ((frameTwist hN P hS2 F : ℂ) * x * Complex.I)
        = Complex.exp ((frameTwist hN P hS2 G : ℂ) * x * Complex.I)) :
    ∃! t : ℝ, ∀ a b : HermitianMat (Fin N) ℂ, IsEffect a → IsEffect b →
      P.sp a b = HermitianMat.twistSeq t a b :=
  exists_unique_twist (by omega) P hS2
    (sp_eq_twistSeq_of_frameGraph hN P hS2 Adj connected overlap)

end Necessity
