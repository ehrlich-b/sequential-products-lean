/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.RankTwo.Lifting
import RadicalRelativity.Vendor.Wigner.Topology

set_option linter.style.longLine false

/-!
# The real projective plane as the rank-two parameter carrier  (LEDGER 5.2)

`cor:qubit-classification` describes the rank-two moduli space as the continuous
real functions on `ℝP²`.  LEDGER 5.2 had budgeted for building `ℝP²` by hand
(`S²/±` through orbit-quotient machinery, plus an evenness/descent bridge),
since Mathlib has no real projective space in any form.

**That construction is unnecessary.**  The vendored `Projectivization` topology
island — already in the tree and inside the audited Wigner closure — is stated
for `[RCLike K]`, which covers `K = ℝ`.  So

`ℝP² := ℙ ℝ (EuclideanSpace ℝ (Fin 3))`

is a compact Hausdorff space *for free*, with the quotient topology, and needs
no sphere quotient and no evenness bridge.

* `RP2` — the carrier, with `T2Space` and `CompactSpace` recorded.
* `RP2.mk` — the point of a nonzero vector, and `RP2.mk_eq_mk_iff`: two vectors
  give the same point exactly when they are proportional (this *is* the
  antipodal identification, obtained from the projective quotient rather than
  built).
* `QubitModuli` — the moduli object of `cor:qubit-classification`, `C(ℝP², ℝ)`,
  with its ring structure inherited.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace RankTwo

/-! ## The carrier -/

/-- **The real projective plane**, as the projectivization of `ℝ³`. -/
abbrev RP2 : Type := ℙ ℝ (EuclideanSpace ℝ (Fin 3))

/-- `ℝP²` is Hausdorff (vendored `Projectivization.instT2Space` at `K = ℝ`). -/
instance : T2Space RP2 := inferInstance

/-- `ℝP²` is compact (vendored `Projectivization.instCompactSpace` at `K = ℝ`). -/
instance : CompactSpace RP2 := inferInstance

/-- The point of `ℝP²` determined by a nonzero vector. -/
def RP2.mk (v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) : RP2 :=
  Projectivization.mk ℝ v hv

/-- **The antipodal identification, for free**: two nonzero vectors give the same
point of `ℝP²` exactly when they are proportional.  In particular `v` and `-v`
agree, which is the `S²/±` description — obtained from the projective quotient
rather than constructed. -/
theorem RP2.mk_eq_mk_iff {v w : EuclideanSpace ℝ (Fin 3)} (hv : v ≠ 0) (hw : w ≠ 0) :
    RP2.mk v hv = RP2.mk w hw ↔ ∃ a : ℝ, a • w = v :=
  Projectivization.mk_eq_mk_iff' ℝ v w hv hw

/-- Antipodal points coincide. -/
theorem RP2.mk_neg (v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
    RP2.mk (-v) (neg_ne_zero.mpr hv) = RP2.mk v hv := by
  rw [RP2.mk_eq_mk_iff]
  exact ⟨-1, by simp⟩

/-! ## The moduli object -/

/-- **The rank-two moduli object** of `cor:qubit-classification`: the continuous
real functions on `ℝP²`.  A rank-two sequential product is (the paper's claim)
exactly such a function — the frame-dependent twist parameter `τ(F)`, with the
frame space being `ℝP²`. -/
abbrev QubitModuli : Type := C(RP2, ℝ)

/-- The moduli object is a commutative ring (pointwise operations), and in
particular nontrivial: the constants `0` and `1` are distinct because `ℝP²` is
nonempty. -/
example : CommRing QubitModuli := inferInstance

/-- `ℝP²` is nonempty (the first standard basis vector is nonzero). -/
instance : Nonempty RP2 :=
  ⟨RP2.mk (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) (by
    intro h
    have h1 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 0 = 0 := by
      rw [h]; rfl
    rw [EuclideanSpace.single_apply] at h1
    simp at h1)⟩

/-- The constant-`0` and constant-`1` moduli differ: the Lüders product and the
unit twist are distinct rank-two products.  (The nontriviality that makes
`cor:qubit-classification`'s parameter space more than a point.) -/
theorem QubitModuli_nontrivial :
    (0 : QubitModuli) ≠ (1 : QubitModuli) := by
  intro h
  obtain ⟨p⟩ := (inferInstance : Nonempty RP2)
  have h0 : (0 : QubitModuli) p = (1 : QubitModuli) p := by rw [h]
  simp only [ContinuousMap.zero_apply, ContinuousMap.one_apply] at h0
  exact zero_ne_one h0

end RankTwo
