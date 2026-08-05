/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.Twist
import RadicalRelativity.Hermitian.Resolution
import RadicalRelativity.SequentialProduct

set_option linter.style.longLine false

/-!
# The twist products satisfy S1–S7 on H_n(ℂ)  (campaign LEDGER 1.3)

This file certifies the paper's `lem:twist-sufficiency` on the concrete carrier:
for every `t : ℝ`, the twist product `a &ₜ b = a^{1/2+it} · b · a^{1/2-it}` is an
S1–S7 sequential product on the effects of `HermitianMat n ℂ`, packaged as
`twistSequentialProductCore` / `twistSequentialProduct` (the latter includes the
norm-continuity axiom S2).

The paper proves this by citing Shen–Wu's construction criterion; here every axiom
is proved directly.  The three nontrivial ingredients:

* **S4 (zero-symmetry)** rides the trace: `tr(a &ₜ b) = tr(b·a)` for `0 ≤ a`
  (`trace_twistSeq`), the trace is symmetric, and a PSD matrix with zero trace is
  zero (`eq_zero_of_nonneg_trace_zero`).

* **Compatibility ⇒ commutation** (`commute_of_twistSeq_comm`): from
  `a &ₜ b = b &ₜ a` the Frobenius certificate `C := b^{1/2+it}·a − a·b^{1/2+it}`
  satisfies `tr(C·Cᴴ) = 0`, hence `C = 0`; conjugate-transposing gives commutation
  with `b^{1/2-it}` too, and their product is `b`.  This is the Gudder–Nagy
  normality trick, run at general twist.  No spectral machinery is needed.

* **Commutation ⇒ compatibility, associativity, S6, S7**: for commuting effects the
  twist product IS the matrix product (`twistSeq_mat_of_commute`, via the vendored
  `Commute.cfc_right`), and the S5 identity reduces to the two-variable law
  `(ab)^{1/2+it} = a^{1/2+it} · b^{1/2+it}` (`twistFactor_mul_of_commute`), proved
  by presenting `ab` through the joint resolution `P_μ · Q_ν` of the two commuting
  effects and applying the resolution lemma of `Hermitian/Resolution.lean` together
  with the scalar character law `g(μν) = g(μ)g(ν)` (`twist_cos_mul`/`twist_sin_mul`,
  with `g(0) = 0` covering zero eigenvalues definitionally).
-/

noncomputable section

open ComplexOrder
-- NB: opened before `namespace HermitianMat` — see LEDGER H6.
open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The scalar character law `g(μν) = g(μ)·g(ν)` on `[0,∞)` -/

theorem twist_cos_mul {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (t : ℝ) :
    Real.sqrt (μ * ν) * Real.cos (t * Real.log (μ * ν))
      = Real.sqrt μ * Real.cos (t * Real.log μ) * (Real.sqrt ν * Real.cos (t * Real.log ν))
        - Real.sqrt μ * Real.sin (t * Real.log μ) * (Real.sqrt ν * Real.sin (t * Real.log ν)) := by
  rcases eq_or_lt_of_le hμ with rfl | hμ'
  · simp
  rcases eq_or_lt_of_le hν with rfl | hν'
  · simp
  rw [Real.sqrt_mul hμ, Real.log_mul (ne_of_gt hμ') (ne_of_gt hν'), mul_add, Real.cos_add]
  ring

theorem twist_sin_mul {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (t : ℝ) :
    Real.sqrt (μ * ν) * Real.sin (t * Real.log (μ * ν))
      = Real.sqrt μ * Real.cos (t * Real.log μ) * (Real.sqrt ν * Real.sin (t * Real.log ν))
        + Real.sqrt μ * Real.sin (t * Real.log μ) * (Real.sqrt ν * Real.cos (t * Real.log ν)) := by
  rcases eq_or_lt_of_le hμ with rfl | hμ'
  · simp
  rcases eq_or_lt_of_le hν with rfl | hν'
  · simp
  rw [Real.sqrt_mul hμ, Real.log_mul (ne_of_gt hμ') (ne_of_gt hν'), mul_add, Real.sin_add]
  ring

/-! ## Commutation transfers to the twist factor -/

/-- Anything commuting with `b` commutes with `b^{1/2+it}` (the twist factor is a
complex combination of two `cfc`s of `b`). -/
theorem commute_twistFactor {a b : HermitianMat n ℂ} (hab : Commute a.mat b.mat) (t : ℝ) :
    Commute a.mat (twistFactor b t) := by
  unfold twistFactor
  exact (hab.cfc_right _).add_right ((hab.cfc_right _).smul_right Complex.I)

/-- For a commuting pair with `0 ≤ a`, the twist product is the matrix product. -/
theorem twistSeq_mat_of_commute {a b : HermitianMat n ℂ} (ha : 0 ≤ a)
    (hab : Commute a.mat b.mat) (t : ℝ) :
    (twistSeq t a b).mat = a.mat * b.mat := by
  have h1 : Commute b.mat (twistFactor a t) := commute_twistFactor hab.symm t
  rw [twistSeq_mat, ← h1.eq, Matrix.mul_assoc, twistFactor_mul_conjTranspose ha, ← hab.eq]

/-- **Commutation ⇒ compatibility.** -/
theorem twistSeq_comm_of_commute {a b : HermitianMat n ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : Commute a.mat b.mat) (t : ℝ) :
    twistSeq t a b = twistSeq t b a := by
  ext1
  rw [twistSeq_mat_of_commute ha hab t, twistSeq_mat_of_commute hb hab.symm t, hab.eq]

/-! ## The two-variable law `(ab)^{1/2+it} = a^{1/2+it} · b^{1/2+it}` -/

set_option maxHeartbeats 800000 in
/-- **The twist factor is multiplicative on commuting positives.**  `m` is the
(Hermitian) matrix product of the commuting pair, presented by the caller.  Proved
through the joint resolution `P_μ · Q_ν` and the resolution lemma — no
simultaneous-diagonalization machinery. -/
theorem twistFactor_mul_of_commute {a b m : HermitianMat n ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : Commute a.mat b.mat) (hm : m.mat = a.mat * b.mat) (t : ℝ) :
    twistFactor m t = twistFactor a t * twistFactor b t := by
  classical
  have hPQ : ∀ μ ν : ℝ, Commute (a.specProj μ).mat (b.specProj ν).mat :=
    fun μ ν => cfc_commute _ _ hab
  -- the joint family over pairs of eigenvalues
  have hidem : ∀ q ∈ a.eigFinset ×ˢ b.eigFinset,
      ((a.specProj q.1).mat * (b.specProj q.2).mat) *
        ((a.specProj q.1).mat * (b.specProj q.2).mat)
      = (a.specProj q.1).mat * (b.specProj q.2).mat := by
    rintro ⟨μ, ν⟩ -
    rw [(hPQ μ ν).symm.mul_mul_mul_comm, specProj_mul_self, specProj_mul_self]
  have horth : ∀ q ∈ a.eigFinset ×ˢ b.eigFinset, ∀ q' ∈ a.eigFinset ×ˢ b.eigFinset, q ≠ q' →
      ((a.specProj q.1).mat * (b.specProj q.2).mat) *
        ((a.specProj q'.1).mat * (b.specProj q'.2).mat) = 0 := by
    rintro ⟨μ, ν⟩ - ⟨μ', ν'⟩ - hne
    rw [(hPQ μ' ν).symm.mul_mul_mul_comm]
    by_cases hμ : μ = μ'
    · subst hμ
      have hν : ν ≠ ν' := fun h => hne (by rw [h])
      rw [specProj_mul_orth b hν, mul_zero]
    · rw [specProj_mul_orth a hμ, zero_mul]
  have hsum : ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
      (a.specProj q.1).mat * (b.specProj q.2).mat = 1 := by
    rw [Finset.sum_product]
    calc ∑ μ ∈ a.eigFinset, ∑ ν ∈ b.eigFinset, (a.specProj μ).mat * (b.specProj ν).mat
        = ∑ μ ∈ a.eigFinset, (a.specProj μ).mat * ∑ ν ∈ b.eigFinset, (b.specProj ν).mat :=
          Finset.sum_congr rfl fun μ _ => (Finset.mul_sum _ _ _).symm
      _ = 1 := by rw [sum_specProj_mat b]; simp only [mul_one]; exact sum_specProj_mat a
  -- mixed products of component expansions land on the joint family
  have hmix : ∀ x y : ℝ → ℝ,
      (∑ μ ∈ a.eigFinset, x μ • (a.specProj μ).mat) *
        (∑ ν ∈ b.eigFinset, y ν • (b.specProj ν).mat)
      = ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
          (x q.1 * y q.2) • ((a.specProj q.1).mat * (b.specProj q.2).mat) := by
    intro x y
    rw [Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hM : m.mat = ∑ q ∈ a.eigFinset ×ˢ b.eigFinset,
      (q.1 * q.2) • ((a.specProj q.1).mat * (b.specProj q.2).mat) := by
    rw [hm, ← sum_smul_specProj_mat a, ← sum_smul_specProj_mat b]
    exact hmix _ _
  -- every cfc of m expands over the joint family, via the resolution lemma.
  -- NB: left unannotated deliberately — ascribing the (beta-reduced) type makes the
  -- unifier grind through `specProj` bodies and time out; forward inference from the
  -- hypotheses is instant.
  have hres := fun (f : ℝ → ℝ) => mat_cfc_of_resolution hidem horth hsum hM f
  -- component identities
  have hcos : (m.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat
      = (a.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat *
          (b.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat
        - (a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat *
          (b.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat := by
    rw [hres _,
      mat_cfc_eq_sum_specProj a, mat_cfc_eq_sum_specProj b,
      mat_cfc_eq_sum_specProj a, mat_cfc_eq_sum_specProj b,
      hmix _ _, hmix _ _, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    rintro ⟨μ, ν⟩ hq
    obtain ⟨hμ, hν⟩ := Finset.mem_product.mp hq
    rw [← sub_smul]
    congr 1
    exact twist_cos_mul (eigFinset_nonneg ha μ hμ) (eigFinset_nonneg hb ν hν) t
  have hsin : (m.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat
      = (a.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat *
          (b.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat
        + (a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat *
          (b.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat := by
    rw [hres _,
      mat_cfc_eq_sum_specProj a, mat_cfc_eq_sum_specProj b,
      mat_cfc_eq_sum_specProj a, mat_cfc_eq_sum_specProj b,
      hmix _ _, hmix _ _, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    rintro ⟨μ, ν⟩ hq
    obtain ⟨hμ, hν⟩ := Finset.mem_product.mp hq
    rw [← add_smul]
    congr 1
    exact twist_sin_mul (eigFinset_nonneg ha μ hμ) (eigFinset_nonneg hb ν hν) t
  -- assemble the complex factor
  show (twistRe m t).mat + Complex.I • (twistIm m t).mat
      = twistFactor a t * twistFactor b t
  unfold twistRe twistIm
  rw [hcos, hsin]
  unfold twistFactor twistRe twistIm
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [show ((a.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat) *
      (Complex.I • (b.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat)
      = Complex.I • ((a.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat *
        (b.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat) from Matrix.mul_smul _ _ _]
  rw [show (Complex.I • (a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat) *
      ((b.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat)
      = Complex.I • ((a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat *
        (b.cfc fun x => Real.sqrt x * Real.cos (t * Real.log x)).mat) from Matrix.smul_mul _ _ _]
  rw [show (Complex.I • (a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat) *
      (Complex.I • (b.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat)
      = -((a.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat *
        (b.cfc fun x => Real.sqrt x * Real.sin (t * Real.log x)).mat) from by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, neg_one_smul]]
  rw [smul_add]
  abel

/-! ## Compatibility ⇒ commutation (the Frobenius certificate) -/

/-- Trace form of the twist product against its own first argument:
`tr((a &ₜ b)·a) = tr(b·a²)`. -/
theorem trace_twistSeq_mul_left {a : HermitianMat n ℂ} (ha : 0 ≤ a) (b : HermitianMat n ℂ)
    (t : ℝ) :
    ((twistSeq t a b).mat * a.mat).trace = (b.mat * (a.mat * a.mat)).trace := by
  have hcX' : Commute a.mat ((twistFactor a t)ᴴ) := by
    rw [twistFactor_conjTranspose]; exact commute_twistFactor (Commute.refl _) (-t)
  rw [twistSeq_mat]
  calc (twistFactor a t * b.mat * (twistFactor a t)ᴴ * a.mat).trace
      = (twistFactor a t * b.mat * ((twistFactor a t)ᴴ * a.mat)).trace := by
        rw [Matrix.mul_assoc]
    _ = (twistFactor a t * b.mat * (a.mat * (twistFactor a t)ᴴ)).trace := by rw [← hcX'.eq]
    _ = ((a.mat * (twistFactor a t)ᴴ) * (twistFactor a t * b.mat)).trace :=
        Matrix.trace_mul_comm _ _
    _ = (a.mat * ((twistFactor a t)ᴴ * twistFactor a t) * b.mat).trace := by
        rw [show (a.mat * (twistFactor a t)ᴴ) * (twistFactor a t * b.mat)
          = a.mat * ((twistFactor a t)ᴴ * twistFactor a t) * b.mat from by noncomm_ring]
    _ = (a.mat * a.mat * b.mat).trace := by rw [conjTranspose_mul_twistFactor ha]
    _ = (b.mat * (a.mat * a.mat)).trace := Matrix.trace_mul_comm _ _

/-- **Compatibility ⇒ commutation** for the twist product, via the Frobenius
certificate `C = b^{1/2+it}·a − a·b^{1/2+it}` (the Gudder–Nagy normality trick at
general twist). -/
theorem commute_of_twistSeq_comm {a b : HermitianMat n ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b) {t : ℝ}
    (h : twistSeq t a b = twistSeq t b a) : Commute a.mat b.mat := by
  have hYY : twistFactor b t * (twistFactor b t)ᴴ = b.mat := twistFactor_mul_conjTranspose hb t
  have hYY' : (twistFactor b t)ᴴ * twistFactor b t = b.mat := conjTranspose_mul_twistFactor hb t
  -- the common real trace value
  have hτ : ((twistSeq t b a).mat * a.mat).trace = (b.mat * (a.mat * a.mat)).trace := by
    rw [← h]; exact trace_twistSeq_mul_left ha b t
  have hreal : star ((b.mat * (a.mat * a.mat)).trace) = (b.mat * (a.mat * a.mat)).trace := by
    rw [← Matrix.trace_conjTranspose]
    rw [show (b.mat * (a.mat * a.mat))ᴴ = (a.mat * a.mat) * b.mat from by
      simp only [Matrix.conjTranspose_mul]
      rw [a.H, b.H]]
    exact Matrix.trace_mul_comm _ _
  -- the four traces in the expansion of tr(C·Cᴴ)
  have t1 : ((twistFactor b t * a.mat) * (a.mat * (twistFactor b t)ᴴ)).trace
      = (b.mat * (a.mat * a.mat)).trace := by
    rw [Matrix.trace_mul_comm,
      show (a.mat * (twistFactor b t)ᴴ) * (twistFactor b t * a.mat)
        = a.mat * ((twistFactor b t)ᴴ * twistFactor b t) * a.mat from by noncomm_ring,
      hYY', Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have t4 : ((a.mat * twistFactor b t) * ((twistFactor b t)ᴴ * a.mat)).trace
      = (b.mat * (a.mat * a.mat)).trace := by
    rw [show (a.mat * twistFactor b t) * ((twistFactor b t)ᴴ * a.mat)
        = a.mat * (twistFactor b t * (twistFactor b t)ᴴ) * a.mat from by noncomm_ring,
      hYY, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  have t2 : ((twistFactor b t * a.mat) * ((twistFactor b t)ᴴ * a.mat)).trace
      = (b.mat * (a.mat * a.mat)).trace := by
    rw [show (twistFactor b t * a.mat) * ((twistFactor b t)ᴴ * a.mat)
        = (twistFactor b t * a.mat * (twistFactor b t)ᴴ) * a.mat from by noncomm_ring,
      ← twistSeq_mat]
    exact hτ
  have t3 : ((a.mat * twistFactor b t) * (a.mat * (twistFactor b t)ᴴ)).trace
      = (b.mat * (a.mat * a.mat)).trace := by
    rw [show (a.mat * twistFactor b t) * (a.mat * (twistFactor b t)ᴴ)
        = ((twistFactor b t * a.mat) * ((twistFactor b t)ᴴ * a.mat))ᴴ from by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [a.H]]
    rw [Matrix.trace_conjTranspose, t2]
    exact hreal
  -- the certificate vanishes
  have hCC : ((twistFactor b t * a.mat - a.mat * twistFactor b t) *
      (twistFactor b t * a.mat - a.mat * twistFactor b t)ᴴ).trace = 0 := by
    have hCH : (twistFactor b t * a.mat - a.mat * twistFactor b t)ᴴ
        = a.mat * (twistFactor b t)ᴴ - (twistFactor b t)ᴴ * a.mat := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
      rw [a.H]
    rw [hCH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_sub, t1, t2, t3, t4]
    ring
  have hC0 : twistFactor b t * a.mat - a.mat * twistFactor b t = 0 :=
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hCC
  have hcomm1 : Commute a.mat (twistFactor b t) := (sub_eq_zero.mp hC0).symm
  have hcomm2 : Commute a.mat ((twistFactor b t)ᴴ) := by
    have hh := congrArg Matrix.conjTranspose hcomm1.eq
    simp only [Matrix.conjTranspose_mul] at hh
    rw [a.H] at hh
    exact hh.symm
  have h3 : Commute a.mat ((twistFactor b t)ᴴ * twistFactor b t) := hcomm2.mul_right hcomm1
  rwa [conjTranspose_mul_twistFactor hb] at h3

/-! ## S4: zero-symmetry -/

/-- `tr(a &ₜ b) = tr(b·a)` for `0 ≤ a`. -/
theorem trace_twistSeq {a : HermitianMat n ℂ} (ha : 0 ≤ a) (b : HermitianMat n ℂ) (t : ℝ) :
    (twistSeq t a b).mat.trace = (b.mat * a.mat).trace := by
  rw [twistSeq_mat, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    conjTranspose_mul_twistFactor ha, Matrix.trace_mul_comm]

/-- A PSD Hermitian matrix with zero trace is zero. -/
theorem eq_zero_of_nonneg_trace_zero {M : HermitianMat n ℂ} (hM : 0 ≤ M)
    (h : M.mat.trace = 0) : M = 0 := by
  have htr : M.trace = 0 := (trace_eq_zero_iff M).mpr h
  have hsum : ∑ i, M.H.eigenvalues i = 0 := by rw [sum_eigenvalues_eq_trace]; exact htr
  have hzero : ∀ i, M.H.eigenvalues i = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => eigenvalues_nonneg hM j)).mp hsum i (Finset.mem_univ i)
  calc M = M.cfc id := (cfc_id M).symm
    _ = M.cfc (fun _ => 0) := by
      apply cfc_congr
      intro x hx
      rw [M.H.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      simpa using hzero i
    _ = 0 := by rw [cfc_const]; simp

/-- **S4: zero-symmetry.**  `a &ₜ b = 0 → b &ₜ a = 0`. -/
theorem twistSeq_zero_symm (t : ℝ) {a b : HermitianMat n ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : twistSeq t a b = 0) : twistSeq t b a = 0 := by
  apply eq_zero_of_nonneg_trace_zero (twistSeq_nonneg t b ha)
  rw [trace_twistSeq hb a, Matrix.trace_mul_comm]
  rw [← trace_twistSeq ha b t, h]
  simp

/-! ## S5–S7 -/

/-- **S5: associativity of compatible effects.** -/
theorem twistSeq_assoc_of_comm (t : ℝ) {a b : HermitianMat n ℂ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcomm : twistSeq t a b = twistSeq t b a) (c : HermitianMat n ℂ) :
    twistSeq t a (twistSeq t b c) = twistSeq t (twistSeq t a b) c := by
  have hab := commute_of_twistSeq_comm ha hb hcomm
  have hm : (twistSeq t a b).mat = a.mat * b.mat := twistSeq_mat_of_commute ha hab t
  have hX : twistFactor (twistSeq t a b) t = twistFactor a t * twistFactor b t :=
    twistFactor_mul_of_commute ha hb hab hm t
  ext1
  rw [twistSeq_mat, twistSeq_mat, twistSeq_mat, hX, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **S6a: compatibility with the orthocomplement.** -/
theorem twistSeq_compat_one_sub (t : ℝ) {a b : HermitianMat n ℂ} (ha : 0 ≤ a)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hcomm : twistSeq t a b = twistSeq t b a) :
    twistSeq t a (1 - b) = twistSeq t (1 - b) a := by
  have hab := commute_of_twistSeq_comm ha hb0 hcomm
  have h1b : Commute a.mat (1 - b).mat := by
    rw [mat_sub, mat_one]
    exact (Commute.one_right _).sub_right hab
  exact twistSeq_comm_of_commute ha (sub_nonneg.mpr hb1) h1b t

/-- **S6b: additivity of compatibility.** -/
theorem twistSeq_compat_add (t : ℝ) {a b c : HermitianMat n ℂ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcab : twistSeq t a b = twistSeq t b a) (hcac : twistSeq t a c = twistSeq t c a) :
    twistSeq t a (b + c) = twistSeq t (b + c) a := by
  have hab := commute_of_twistSeq_comm ha hb hcab
  have hac := commute_of_twistSeq_comm ha hc hcac
  have hbc : Commute a.mat (b + c).mat := by
    rw [mat_add]
    exact hab.add_right hac
  exact twistSeq_comm_of_commute ha (add_nonneg hb hc) hbc t

/-- **S7: multiplicativity of compatibility.** -/
theorem twistSeq_compat_sp (t : ℝ) {a b c : HermitianMat n ℂ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcab : twistSeq t a b = twistSeq t b a) (hcac : twistSeq t a c = twistSeq t c a) :
    twistSeq t a (twistSeq t b c) = twistSeq t (twistSeq t b c) a := by
  have hab := commute_of_twistSeq_comm ha hb hcab
  have hac := commute_of_twistSeq_comm ha hc hcac
  have hbc : Commute a.mat (twistSeq t b c).mat := by
    rw [twistSeq_mat]
    refine ((commute_twistFactor hab t).mul_right hac).mul_right ?_
    rw [twistFactor_conjTranspose]
    exact commute_twistFactor hab (-t)
  exact twistSeq_comm_of_commute ha (twistSeq_nonneg t b hc) hbc t

/-! ## S2: first-argument norm continuity -/

/-- Continuity of `x ↦ √x · c(t·log x)` on all of ℝ for bounded continuous `c`:
away from `0` by composition, at `0` by the squeeze `|√x · c| ≤ √x`.  (For `x < 0`
both `Real.sqrt` and hence the whole function vanish.) -/
theorem continuous_sqrt_mul_bounded {c : ℝ → ℝ} (hc : Continuous c)
    (hbd : ∀ y, |c y| ≤ 1) (t : ℝ) :
    Continuous fun x => Real.sqrt x * c (t * Real.log x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · have h0 : (fun x => Real.sqrt x * c (t * Real.log x)) 0 = 0 := by simp
    unfold ContinuousAt
    rw [h0]
    refine squeeze_zero_norm (fun x => ?_) (by simpa using Real.continuous_sqrt.tendsto 0)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg x) (hbd _)
  · exact (Real.continuous_sqrt.continuousAt).mul
      ((hc.continuousAt).comp (continuousAt_const.mul (Real.continuousAt_log hx₀)))

/-- The twist factor is (globally) norm-continuous in its matrix argument. -/
theorem continuous_twistFactor (t : ℝ) :
    Continuous fun a : HermitianMat n ℂ => twistFactor a t := by
  have h₁ : Continuous fun x => Real.sqrt x * Real.cos (t * Real.log x) :=
    continuous_sqrt_mul_bounded Real.continuous_cos (fun y => Real.abs_cos_le_one y) t
  have h₂ : Continuous fun x => Real.sqrt x * Real.sin (t * Real.log x) :=
    continuous_sqrt_mul_bounded Real.continuous_sin (fun y => Real.abs_sin_le_one y) t
  unfold twistFactor twistRe twistIm
  exact (continuous_mat.comp (HermitianMat.cfc_continuous h₁)).add
    ((continuous_mat.comp (HermitianMat.cfc_continuous h₂)).const_smul Complex.I)

/-- **S2 (global form): the twist product is norm-continuous in its first
argument**, everywhere — not only on effects. -/
theorem continuous_twistSeq_left (t : ℝ) (b : HermitianMat n ℂ) :
    Continuous fun a : HermitianMat n ℂ => twistSeq t a b := by
  have hmat : Continuous fun a : HermitianMat n ℂ => (twistSeq t a b).mat := by
    simp only [twistSeq_mat]
    have h2 : Continuous fun a : HermitianMat n ℂ => (twistFactor a t)ᴴ := by
      simp only [twistFactor_conjTranspose]
      exact continuous_twistFactor (-t)
    exact ((continuous_twistFactor t).matrix_mul continuous_const).matrix_mul h2
  exact hmat.subtype_mk _

/-- **S2 in the order-unit norm** (ε–δ form): first-argument continuity of the
twist product holds for `ouNorm` as well, via the two-sided norm comparison
(`ouNorm_le_norm`, `norm_le_sqrt_card_mul_ouNorm`).  This closes THEOREM-MAP's
(S2) literal-fidelity caveat on the concrete carrier. -/
theorem twistSeq_continuousAt_ouNorm (t : ℝ) (b a : HermitianMat n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a' : HermitianMat n ℂ, ouNorm (a' - a) < δ →
      ouNorm (twistSeq t a' b - twistSeq t a b) < ε := by
  have hc := (continuous_twistSeq_left t b).continuousAt (x := a)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ₀, hδ₀, hball⟩ := hc ε hε
  refine ⟨δ₀ / (Real.sqrt (Fintype.card n) + 1), by positivity, fun a' h => ?_⟩
  have hin : dist a' a < δ₀ := by
    rw [dist_eq_norm]
    calc ‖a' - a‖ ≤ Real.sqrt (Fintype.card n) * ouNorm (a' - a) :=
          norm_le_sqrt_card_mul_ouNorm _
      _ ≤ (Real.sqrt (Fintype.card n) + 1) * ouNorm (a' - a) := by
          have := ouNorm_nonneg (a' - a)
          nlinarith [Real.sqrt_nonneg (Fintype.card n : ℝ)]
      _ < (Real.sqrt (Fintype.card n) + 1) * (δ₀ / (Real.sqrt (Fintype.card n) + 1)) := by
          have hpos : (0 : ℝ) < Real.sqrt (Fintype.card n) + 1 := by positivity
          exact mul_lt_mul_of_pos_left h hpos
      _ = δ₀ := by field_simp
  have hout := hball hin
  rw [dist_eq_norm] at hout
  calc ouNorm (twistSeq t a' b - twistSeq t a b)
      ≤ ‖twistSeq t a' b - twistSeq t a b‖ := ouNorm_le_norm _
    _ < ε := hout

/-! ## Packaging: the S1–S7 interface -/

/-- **The twist product is an S1–S7 sequential product on `H_n(ℂ)`** (paper
`lem:twist-sufficiency`, algebraic core S1, S3–S7): the `SequentialProductCore`
structure with `sp := twistSeq t`, for every twist parameter `t : ℝ`. -/
def twistSequentialProductCore (t : ℝ) : SequentialProductCore (HermitianMat n ℂ) where
  toOrderUnitSpace := inferInstance
  sp := twistSeq t
  sp_add_right := fun _ _ _ _ => twistSeq_add_right t _ _ _
  sp_unit_left := fun _ => twistSeq_one_left t _
  sp_zero_symm := fun ha hb h => twistSeq_zero_symm t ha.1 hb.1 h
  sp_assoc_of_compatible := fun ha hb _ hcomm => twistSeq_assoc_of_comm t ha.1 hb.1 hcomm _
  compatible_ortho := fun ha hb hcomm => twistSeq_compat_one_sub t ha.1 hb.1 hb.2 hcomm
  compatible_add := fun ha hb hc _ hcab hcac => twistSeq_compat_add t ha.1 hb.1 hc.1 hcab hcac
  compatible_sp := fun ha hb hc hcab hcac => twistSeq_compat_sp t ha.1 hb.1 hc.1 hcab hcac
  sp_effect := fun ha hb => twistSeq_isEffect t ha.1 ha.2 hb.1 hb.2

/-- **The twist product is a `SequentialProduct`** (paper `lem:twist-sufficiency`,
all seven axioms including the norm-continuity S2), for every `t : ℝ`.  S2 holds in
the carried (Frobenius) norm; the order-unit norm comparison is LEDGER 1.4. -/
def twistSequentialProduct (t : ℝ) : SequentialProduct (HermitianMat n ℂ) where
  toSequentialProductCore := twistSequentialProductCore t
  sp_continuous_left := fun b _ => (continuous_twistSeq_left t b).continuousOn

end HermitianMat
