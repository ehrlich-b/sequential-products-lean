/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Vendor.HermitianMat.Inner
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The normed ring of continuous endomorphisms of `HermitianMat`

`HermitianMat n 𝕜` carries two topologies that are definitionally equal but not syntactically
equal:

* `HermitianMat.instTopologicalSpace` (`Vendor/HermitianMat/Basic.lean`), the subtype topology
  inherited from `selfAdjoint`; and
* the metric topology induced by `HermitianMat.instNormedGroup`
  (`Vendor/HermitianMat/Inner.lean`), i.e. `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`.

Instance synthesis picks the first. Mathlib's normed structures on continuous linear maps are
phrased against the second. Every normed structure on
`HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜` therefore becomes unreachable — `Norm`,
`NonUnitalSeminormedRing`, `NormedRing`, `NormedAlgebra` alike.

The precise mechanism is the Lean v4.33 flip of `backward.isDefEq.respectTransparency`:
`isDefEq` at `.instances` transparency no longer unfolds non-reducible instance definitions, so
`HermitianMat.instTopologicalSpace` is no longer *seen* to be defeq to the metric topology. The
diamond itself is old and harmless — the two remain defeq, and `rfl` still proves them equal at
default transparency. Only the visibility changed. (Upstream physlib hit the same wall: the
vendored `Basic.lean` carries six `set_option backward.isDefEq.respectTransparency false in`
lines for exactly this reason.)

A `trace.Meta.synthInstance` on the failure shows `ContinuousLinearMap.hasOpNorm` is the only
candidate tried, every subgoal succeeds, and the failure is the final `tryResolve` unifying the
two continuous-linear-map type terms. Under `pp.explicit` **two** slots mismatch, not one: the
topology, and the additive structure (the `ℂ` shortcut `HermitianMat.instAddCommMonoidComplex`
against `SeminormedAddCommGroup.toAddCommGroup.toAddCommMonoid`). Pinning one horn with `letI`
therefore does not help — the type has both baked in by the time synthesis runs.

We deliberately do NOT set `backward.isDefEq.respectTransparency false` in first-party code: it
is a compatibility knob slated for removal, and relying on it would have to be redone at the bump
that drops it. The bridges below are permanent.

The diamond is genuine but harmless: `rfl` proves the two topologies equal at default
transparency. So it is enough to declare the instance *once* with its carrier arguments given
explicitly, which elaborates the Mathlib instance on the metric horn, and let the definitional
unifier bridge to the stated type. A single `NormedRing` suffices — `Norm`,
`NormedAddCommGroup` and `NonUnitalSeminormedRing` all follow from it, so no competing `Norm`
instance is introduced.

The resulting norm is the operator norm on the nose:
`‖f‖ = ContinuousLinearMap.opNorm f` holds by `rfl` (checked below).

This lives in first-party space rather than as a patch to the vendored island, so that the
island stays byte-verbatim against upstream physlib and survives future bumps unedited.
-/

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- The normed ring structure on continuous endomorphisms of `HermitianMat n 𝕜`.

Stated with `E` and `𝕜` explicit so that Mathlib's instance elaborates against the metric
topology; the assignment to the declared type is then discharged by the definitional unifier.
See the module docstring for why this cannot be found automatically. -/
noncomputable instance instNormedRingCLM :
    NormedRing (HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜) :=
  ContinuousLinearMap.toNormedRing (E := HermitianMat n 𝕜) (𝕜 := ℝ)

/-- The normed `ℝ`-algebra structure, blocked by the same diamond. -/
noncomputable instance instNormedAlgebraCLM :
    NormedAlgebra ℝ (HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜) :=
  ContinuousLinearMap.toNormedAlgebra (E := HermitianMat n 𝕜) (𝕜 := ℝ)

/-- `HermitianMat` is a sequential space. The metric topology gives this, but synthesis stalls
on the subtype horn; the type ascription forces the search to run at the metric topology and the
definitional unifier bridges the result back. Needed as a side condition of
`ContinuousLinearMap.instCompleteSpace`. -/
instance instSequentialSpace : SequentialSpace (HermitianMat n 𝕜) :=
  (inferInstance : @SequentialSpace (HermitianMat n 𝕜)
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace)

/-- Completeness, blocked by the same diamond. With this and `instNormedRingCLM` in place,
`HasSummableGeomSeries` (needed for the Neumann-series inversion arguments in
`Necessity.ChiContinuity`) derives from Mathlib's generic
`[NormedRing R] [CompleteSpace R]` instance without further help. -/
instance instCompleteSpaceCLM :
    CompleteSpace (HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜) :=
  ContinuousLinearMap.instCompleteSpace (E := HermitianMat n 𝕜) (F := HermitianMat n 𝕜)
    (𝕜₁ := ℝ) (𝕜₂ := ℝ)

/-- The norm supplied by `instNormedRingCLM` is the operator norm, definitionally. -/
theorem norm_clm_eq_opNorm (f : HermitianMat n 𝕜 →L[ℝ] HermitianMat n 𝕜) :
    ‖f‖ = ContinuousLinearMap.opNorm f := rfl

end HermitianMat
