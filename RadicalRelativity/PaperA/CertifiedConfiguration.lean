/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ComplexRowUnconditional
import RadicalRelativity.Necessity.RealRowUnconditional
import RadicalRelativity.PaperA.Statement

set_option linter.style.longLine false

/-!
# The certified configuration: the frozen conclusion shapes, met by the proved rows

`PaperA/Statement.lean` freezes the *shapes* a completed formalization must prove, with the
Lüders and twist reference maps left as **parameters** — its docstring says "the concrete EJA
reference maps do not yet exist in this development."  That is no longer true: both exist, and
both flagship rows are proved.  This module closes the gap.

* `ludersRefR`, `twistRefC` — the two reference maps as genuine `EffectProduct`s, i.e. with
  effect closure *proved*, not assumed.  The real one needs `cfcSqrt_mul_self` (`√a·√a = a`,
  field-general, proved here in the pattern of `twistRe_sq_add_twistIm_sq`).
* `SequentialProductOn.toSequentialProduct` — the bridge from the carrier-pinned product plus
  S2 to the `SequentialProduct` class the statement layer quantifies over.
* `real_meets_ludersConclusion`, `complex_meets_uniqueTwistConclusion` — **the two frozen
  shapes, discharged.**

What this buys, exactly: the audited statement shape and the proved theorem are now the *same
statement*, so the capstones cannot be described as theorems about the paper's sequential
product while actually concluding something weaker (the failure mode `Statement.lean` was built
to make impossible).  It buys nothing about `H_n(ℍ)` or `H₃(𝕆)`, whose rows are not proved.
-/

noncomputable section

open ComplexOrder
open scoped Matrix
open OrderUnitSpace

/-! ## `√a · √a = a`, field-general -/

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- **The square root squares back**: for `0 ≤ a`, `√a · √a = a`.  On the nonnegative
spectrum `√x · √x = x`, so the product of the two functional calculi is the calculus of the
identity. -/
theorem cfcSqrt_mul_self {a : HermitianMat n 𝕜} (ha : 0 ≤ a) :
    (a.cfc Real.sqrt).mat * (a.cfc Real.sqrt).mat = a.mat := by
  rw [← HermitianMat.mat_cfc_mul_apply]
  have key : a.cfc (fun x => Real.sqrt x * Real.sqrt x) = a := by
    have heq : Set.EqOn (fun x => Real.sqrt x * Real.sqrt x) (fun x => x) (Set.Ici 0) :=
      fun _ hx => Real.mul_self_sqrt hx
    calc a.cfc _ = a.cfc (fun x => x) := HermitianMat.cfc_congr_of_nonneg ha heq
      _ = a := HermitianMat.cfc_id' a
  rw [key]

/-- **The Lüders product of effects is an effect.**  Positivity is `conj_nonneg`; the upper
bound is monotonicity of `conj` against `b ≤ 𝟙` followed by `√a · √a = a ≤ 𝟙`. -/
theorem luders_isEffect {a b : HermitianMat n 𝕜} (ha : IsEffect a) (hb : IsEffect b) :
    IsEffect (b.conj (a.cfc Real.sqrt).mat) := by
  refine ⟨b.conj_nonneg _ hb.1, ?_⟩
  have hb1 : b ≤ (1 : HermitianMat n 𝕜) := by
    have h := hb.2
    rwa [HermitianMat.ousUnit_eq_one] at h
  have hstep : b.conj (a.cfc Real.sqrt).mat
      ≤ (1 : HermitianMat n 𝕜).conj (a.cfc Real.sqrt).mat := HermitianMat.conj_mono hb1
  have hunit : (1 : HermitianMat n 𝕜).conj (a.cfc Real.sqrt).mat = a := by
    ext1
    rw [HermitianMat.conj_apply_mat, HermitianMat.mat_one, Matrix.mul_one,
      (a.cfc Real.sqrt).H, cfcSqrt_mul_self ha.1]
  rw [hunit] at hstep
  have ha1 : a ≤ (1 : HermitianMat n 𝕜) := by
    have h := ha.2
    rwa [HermitianMat.ousUnit_eq_one] at h
  rw [HermitianMat.ousUnit_eq_one]
  exact hstep.trans ha1

end HermitianMat

/-! ## From a pinned product plus S2 to the statement layer's class -/

namespace SequentialProductOn

variable {V : Type*} [OrderUnitSpace V]

/-- **The bridge.**  A carrier-pinned S1, S3–S7 product together with S2 is exactly a
`SequentialProduct` instance, with the order-unit parent definitionally the carrier's own. -/
def toSequentialProduct (P : SequentialProductOn V) (hS2 : P.FirstArgContinuous) :
    SequentialProduct V :=
  { P.toCore with sp_continuous_left := hS2 }

end SequentialProductOn

/-! ## The two reference maps, concretely -/

namespace PaperA

variable {N : ℕ}

/-- The Lüders reference on `H_N(ℝ)`, as a genuine effect-to-effect product. -/
def ludersRefR (N : ℕ) : EffectProduct (HermitianMat (Fin N) ℝ) :=
  fun a b => ⟨b.1.conj (a.1.cfc Real.sqrt).mat, HermitianMat.luders_isEffect a.2 b.2⟩

/-- The twist reference on `H_N(ℂ)`, as a genuine effect-to-effect product. -/
def twistRefC (N : ℕ) (t : ℝ) : EffectProduct (HermitianMat (Fin N) ℂ) :=
  fun a b => ⟨HermitianMat.twistSeq t a.1 b.1,
    ⟨(HermitianMat.twistSeq_isEffect t a.2.1 a.2.2 b.2.1 b.2.2).1,
      (HermitianMat.twistSeq_isEffect t a.2.1 a.2.2 b.2.1 b.2.2).2⟩⟩

@[simp] theorem ludersRefR_val (a b : Effect (HermitianMat (Fin N) ℝ)) :
    (ludersRefR N a b : HermitianMat (Fin N) ℝ) = b.1.conj (a.1.cfc Real.sqrt).mat := rfl

@[simp] theorem twistRefC_val (t : ℝ) (a b : Effect (HermitianMat (Fin N) ℂ)) :
    (twistRefC N t a b : HermitianMat (Fin N) ℂ) = HermitianMat.twistSeq t a.1 b.1 := rfl

/-! ## The frozen shapes, discharged -/

/-- **`prop:real` meets the frozen Lüders shape.**  The real row's conclusion *is*
`LudersConclusion` with the reference instantiated by the concrete conj-Lüders map — no
parameter left open, and the product being classified is the paper's own effect-level
operation. -/
theorem real_meets_ludersConclusion (hN : 0 < N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℝ)) (hS2 : P.FirstArgContinuous) :
    @LudersConclusion (HermitianMat (Fin N) ℝ) (P.toSequentialProduct hS2) (ludersRefR N) := by
  intro a b
  apply Subtype.ext
  change P.sp a.1 b.1 = b.1.conj (a.1.cfc Real.sqrt).mat
  exact Necessity.real_classification hN P hS2 b.2 a.1 a.2

/-- **`mthm:master`'s complex row meets the frozen unique-twist shape.**  The `∃!` proved by
`complex_classification_unconditional` is the *same* `∃!` the statement layer froze, with the
reference instantiated by `twistSeq`. -/
theorem complex_meets_uniqueTwistConclusion (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ)) (hS2 : P.FirstArgContinuous) :
    @UniqueTwistConclusion (HermitianMat (Fin N) ℂ) (P.toSequentialProduct hS2)
      (twistRefC N) := by
  obtain ⟨t, ht, huniq⟩ := Necessity.complex_classification_unconditional hN P hS2
  refine ⟨t, fun a b => Subtype.ext (ht a.1 b.1 a.2 b.2), fun t' ht' => ?_⟩
  refine huniq t' fun a b ha hb => ?_
  exact congrArg Subtype.val (ht' ⟨a, ha⟩ ⟨b, hb⟩)

end PaperA
