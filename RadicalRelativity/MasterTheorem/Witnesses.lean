/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.DiagonalHom
import RadicalRelativity.MasterTheorem.Branches.Albert
import Mathlib.Algebra.Module.PUnit

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Interface witnesses — inhabitedness guards (degenerate instances)

One concrete instance of each of the five interface structures the master-theorem
chain quantifies over (`ComparisonSetup`, `CoalescenceSetup`, `DiagonalHomSetup`,
`StabilizerCoupling`, `IsAlbertModel`), plus a live run of the producer capstone
`DiagonalHomSetup.toStabilizerCoupling`.

## What this module certifies — and what it does not

**Certifies (the vacuity guard).** `THEOREM-MAP.md` §2 documented an escape class:
because the tree constructed no witness of any interface structure, a hostile edit
could redefine a helper *body* (e.g. `MasterTheorem.OpCommute` to `False`) so that a
field became unsatisfiable — making the whole skeleton vacuous — while every frozen
constructor type, the module manifest, and every axiom closure stayed green. The
instances below consume the helper bodies through real proofs (e.g.
`opCommute_mul_real` proves an actual `OpCommute`, and the `IsAlbertModel` witness
proves an actual `Function.Injective`), so that edit class now **fails the build**
here. Inhabitedness of each structure is established constructively.

**Does not certify (read this before quoting).** Every witness below is
**degenerate**: the carrier is `ℝ` (or `PUnit`), the "frame" is the zero family, the
"rank" field is `3` with no rank semantics behind it, the comparison maps are the
identity, and the block representations are zero. These witnesses model **no**
Euclidean Jordan algebra of rank `≥ 3`, carry **no** sequential product, and
instantiate **none** of the cited van de Wetering / van Imhoff–Roelands /
Faraut–Korányi / Yokota content. Inhabitedness removes the vacuity *failure mode*;
it does **not** shrink the conditionality of the skeleton: the distance between
these degenerate instances and the intended EJA instances is exactly the remaining
formalization campaign (`LEDGER.md`). Nothing downstream may cite this module as
evidence that the interface hypotheses hold on the paper's algebras.

`#print axioms` on every declaration here is Lean core only.
-/

noncomputable section

open scoped InnerProductSpace

namespace MasterTheorem

/-! ## Operator commutation on the degenerate carrier `ℝ` -/

/-- On the commutative associative algebra `ℝ`, any two elements operator-commute
for the multiplication bilinear map. This proves a genuine `OpCommute` (consuming
its body — the vacuity guard for the `OpCommute`-redefinition escape). -/
theorem opCommute_mul_real (x y : ℝ) : OpCommute (LinearMap.mul ℝ ℝ) x y := by
  unfold OpCommute mulOp
  ext z
  simp only [LinearMap.comp_apply, LinearMap.mul_apply']
  ring

/-! ## The comparison-face witnesses -/

/-- **Degenerate witness** for `ComparisonSetup` (the inhabitant sketched in the
structure's own vacuity-honesty docstring): carrier `ℝ`, Jordan product = ordinary
multiplication, zero frame, full cone, `Θ = id`. Establishes inhabitedness only —
models no rank-`3` EJA. -/
noncomputable def trivialComparison : ComparisonSetup ℝ where
  jordan := LinearMap.mul ℝ ℝ
  e := 1
  jordan_comm := fun x y => by
    simp only [LinearMap.mul_apply']; exact mul_comm x y
  jordan_unit := fun x => by
    simp only [LinearMap.mul_apply']; exact one_mul x
  n := 3
  rank_ge := le_refl 3
  p := fun _ => 0
  nonneg := fun _ => True
  Inv := fun _ => True
  aOf := fun _ => 1
  aOf_inv := fun _ => trivial
  Θ := fun _ => LinearEquiv.refl ℝ ℝ
  Θ_unital := fun _ _ => rfl
  Θ_orderIso := fun _ _ _ => Iff.rfl
  Θ_jordan := fun _ _ _ _ => rfl
  Θ_fix := fun _ _ _ _ => rfl
  frame_opCommute := fun _ _ => opCommute_mul_real _ _
  Θ_cocycle := fun _ _ _ _ => by ext x; rfl

/-- **Degenerate witness** for `CoalescenceSetup`: `trivialComparison` with the
trivially-true Peirce predicates. The `simDiag_opCommute` field is discharged by a
real `OpCommute` proof (not by vacuous hypotheses), keeping the guard live. -/
noncomputable def trivialCoalescence : CoalescenceSetup ℝ where
  toComparisonSetup := trivialComparison
  J2 := fun _ _ _ => True
  ScalarOn := fun _ _ _ => True
  simDiag_opCommute := fun _ _ a b _ _ => opCommute_mul_real a b
  aOf_scalarOn := fun _ _ _ _ => trivial
  block_mem_J2 := fun _ _ _ _ => trivial

/-- **Degenerate witness** for `DiagonalHomSetup` (`J = Stab = V = ℝ`): zero block
representations, zero additive differential (continuous), vanishing differentiated
coalescence. Establishes inhabitedness only — none of the differential-face fields
carry their intended Lie-theoretic semantics here. -/
noncomputable def trivialDiagonalHom : DiagonalHomSetup ℝ ℝ ℝ where
  toCoalescenceSetup := trivialCoalescence
  ρ := fun _ _ => 0
  ρ_skew := fun _ _ _ x => by simp
  dχAdd :=
    { toFun := fun _ => 0
      map_zero' := rfl
      map_add' := fun _ _ => (add_zero (0 : ℝ)).symm }
  dχAdd_cont := continuous_const
  coalescence_diff := fun _ _ _ _ => by simp

/-- **Live run of the producer capstone**: `toStabilizerCoupling` applied to the
degenerate `DiagonalHomSetup` witness. Type-checks the packaging path
(`lieHom_smooth` + `hyperplane_factorization`) on an actual instance. -/
noncomputable def trivialProducedCoupling : StabilizerCoupling 3 ℝ ℝ :=
  trivialDiagonalHom.toStabilizerCoupling

/-! ## The differential-face witnesses -/

/-- **Degenerate witness** for `StabilizerCoupling` at rank `3` with the
`PUnit` stabilizer: zero representations, zero differential, zero twists. The
`PUnit` stabilizer makes the zero representation *injective*, which is what the
`IsAlbertModel` witness below needs. Models no frame-stabilizer Lie algebra. -/
noncomputable def trivialCoupling : StabilizerCoupling 3 PUnit ℝ where
  ρ := fun _ _ => 0
  ρ_skew := fun _ _ _ x => by simp
  dχ := 0
  T := fun _ _ => 0
  coupling := fun _ _ r => by simp
  rank_ge := le_refl 3

/-- **Degenerate witness** for `IsAlbertModel`: over the `PUnit` stabilizer the zero
block representations are injective (any map out of a subsingleton is), so the
marker is inhabited. This consumes `Function.Injective` through a real proof — the
guard companion to `opCommute_mul_real` — while modelling nothing about `H₃(𝕆)`:
the intended `Spin(8)`-triality content is untouched (see `LEDGER.md`). -/
theorem trivialCoupling_isAlbertModel : IsAlbertModel trivialCoupling :=
  ⟨fun _ _ _ a b _ => Subsingleton.elim a b⟩

end MasterTheorem
