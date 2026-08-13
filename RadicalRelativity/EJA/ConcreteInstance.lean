/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.EJA.InterfaceInstance
import RadicalRelativity.Necessity.ComparisonInstance

set_option linter.style.longLine false

/-!
# The concrete `EJAComparison` on `H_N(ℂ)`

**ARC-9 block 9.23, 2026-08-13.**

`EJA/InterfaceInstance.lean` shows that an interface *told its frame is a frame* produces a
`CoalescenceSetup` with the three Faraut–Korányi fields proved. This file supplies that
telling for **the paper's own comparison setup**: `ejaComparison` is
`Necessity.comparisonSetup` together with the five equations, so

```
(ejaComparison hN P hS2 hjord).toCoalescenceSetup
```

is a `CoalescenceSetup` on `HermitianMat (Fin N) ℂ` in which `simDiag_opCommute`,
`aOf_scalarOn` and `block_mem_J2` are **theorems rather than citations**.

★ **Every ingredient was already in the tree.** `frameProj_isProjection`, `frameProj_orth`,
`sum_frameProj` and `diagFamily_eq_sum_frameProj` have been in
`Necessity/DiagonalFamily.lean` throughout, and the Jordan identity is the vendored
`IsCommJordan (HermitianMat d 𝕜)`. What this file adds is three short bridges from the
`.mat`-level statements to `jordanBilin`, and the assembly. **The fourth time this arc that a
residue's ingredients turned out to be in-tree** — after row 35, the FK fields, and formal
reality.

## What this does and does not do for manifest row 16

★★ **It does NOT close row 16, and the status word does not move.** `lem:coalescence` is proved
over `CoalescenceSetup` from **four** hypotheses. Three are now discharged on this carrier. The
fourth, `Θ_fix` (van de Wetering Prop 5.5, in span-extended form), is a `ComparisonSetup` field
and remains cited — as does `Θ_jordan`, which enters through the `ThetaPreservesJordan P`
argument and is campaign milestone M3.

★ What *has* changed is the **shape of the residue**: before this file, row 16's Faraut–Korányi
content was an unexaminable field on an abstract structure; it is now a theorem about the
paper's own carrier. The EJA-GATED terminal state stands, but its (E2) half is discharged here
and only the (E3)/vIR half remains.
-/

namespace RadicalRelativity.EJA

open Necessity HermMul

variable {N : ℕ}

theorem jordanBilin_apply (a b : HermitianMat (Fin N) ℂ) :
    jordanBilin a b = a.symmMul b := rfl

/-- The concrete frame is idempotent for the Jordan product. -/
theorem frameProj_jordan_self (i : Fin N) :
    jordanBilin (frameProj i) (frameProj i) = frameProj i := by
  apply HermitianMat.ext
  rw [jordanBilin_apply, HermitianMat.symmMul_toMat]
  have hp : (frameProj i).mat * (frameProj i).mat = (frameProj i).mat := by
    have := frameProj_isProjection (n := Fin N) i
    rwa [HermitianMat.isProjection_iff_mat_mul_self] at this
  rw [hp]
  module

/-- Distinct frame projections are Jordan-orthogonal. -/
theorem frameProj_jordan_orth {i j : Fin N} (hij : i ≠ j) :
    jordanBilin (frameProj i) (frameProj j) = 0 := by
  apply HermitianMat.ext
  rw [jordanBilin_apply, HermitianMat.symmMul_toMat, frameProj_orth hij,
    frameProj_orth (Ne.symm hij)]
  simp

/-- The Jordan identity for the concrete bilinear product — the vendored `IsCommJordan`
instance on `HermitianMat`, restated for `jordanBilin`. -/
theorem jordanBilin_jordan_id (a b : HermitianMat (Fin N) ℂ) :
    jordanBilin (jordanBilin a b) (jordanBilin a a)
      = jordanBilin a (jordanBilin b (jordanBilin a a)) :=
  IsCommJordan.lmul_comm_rmul_rmul a b

/-- ★★★ **The concrete `EJAComparison`**: the paper's own comparison setup, told that its
frame is a frame. -/
noncomputable def ejaComparison (hN : 3 ≤ N)
    (P : SequentialProductOn (HermitianMat (Fin N) ℂ))
    (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordan P) :
    EJAComparison (HermitianMat (Fin N) ℂ) :=
  { comparisonSetup hN P hS2 hjord with
    jordan_id := jordanBilin_jordan_id
    p_idem := frameProj_jordan_self
    p_orth := fun _ _ hij => frameProj_jordan_orth hij
    p_sum := sum_frameProj
    aOf_eq := diagFamily_eq_sum_frameProj }

end RadicalRelativity.EJA
