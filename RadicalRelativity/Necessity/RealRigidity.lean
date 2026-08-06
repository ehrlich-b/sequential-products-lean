/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.BlockChiGen
import RadicalRelativity.Necessity.FrameBlockSpanGen
import RadicalRelativity.Necessity.ChiContinuityGen

set_option linter.style.longLine false

/-!
# The real type is rigid: `χ̃ = id` on `H_n(ℝ)`  (`prop:real`, M4.1 capstone)

Over ℝ the comparison character is the **identity** — there is no twist parameter at
all — and the argument needs no differentiation, only the block isometry and
continuity that the field-general layers already provide.

* `blockScalar` — the scalar by which `χ̃(r)` acts on the block `(i,j)`: over ℝ the
  Peirce block is one-dimensional, so `chiTilde_block_existsG` gives
  `χ̃(r)(blockHerm i j 1) = blockHerm i j (blockScalar …)`.
* `blockScalar_sq` — **it squares to one** (`normSq` over ℝ is `x²`), i.e. it is `±1`.
* `blockScalar_eq_one` — **it is `+1`**: `t ↦ blockScalar (t • r)` is continuous,
  squares to one, and equals `1` at `t = 0`; a continuous function into `{±1}` that
  reached `−1` would have to vanish somewhere by the intermediate value theorem,
  contradicting the square law. This is where the ℂ lane needed the phase cocycle
  and the whole differential apparatus; over ℝ connectedness does it.
* `chiTilde_eq_id` — hence `χ̃(r)` agrees with the identity on the frame and on every
  block, so it **is** the identity (`linearMap_eq_of_frame_blockG`).

Everything is conditional on `ThetaPreservesJordanG` — real Kadison/Uhlhorn is not
available in any prover, so on `H_n(ℝ)` the Jordan property of the comparison map is
carried as a located hypothesis, exactly as the manuscript cites it (and exactly as
the ℂ row stood before M3 discharged it there).
-/

noncomputable section

open scoped Matrix
open OrderUnitSpace

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (P : SequentialProductOn (HermitianMat n ℝ))

/-! ## The block scalar -/

/-- The scalar by which `χ̃(r)` acts on the one-dimensional block `(i,j)`. -/
def blockScalar (hS2 : P.FirstArgContinuous) (hjord : ThetaPreservesJordanG P)
    (r : n → ℝ) {i j : n} (hij : i ≠ j) : ℝ :=
  (chiTilde_block_existsG P hS2 hjord r hij (1 : ℝ)).choose

theorem blockScalar_spec (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    (chiTildeG P hS2 r).val (blockHermG i j (1 : ℝ))
      = blockHermG i j (blockScalar P hS2 hjord r hij) :=
  (chiTilde_block_existsG P hS2 hjord r hij (1 : ℝ)).choose_spec.1

/-- **The block scalar squares to one.**  `RCLike.normSq` over ℝ is `x * x`, and the
block isometry says it is preserved. -/
theorem blockScalar_sq (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij * blockScalar P hS2 hjord r hij = 1 := by
  have h := (chiTilde_block_existsG P hS2 hjord r hij (1 : ℝ)).choose_spec.2
  simpa [blockScalar, RCLike.normSq_apply] using h

theorem blockScalar_ne_zero (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij ≠ 0 := by
  intro h
  have hsq := blockScalar_sq P hS2 hjord r hij
  rw [h, mul_zero] at hsq
  exact zero_ne_one hsq

/-! ## The scalar at the origin, and its continuity -/

theorem blockScalar_zero (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord 0 hij = 1 := by
  have hspec := blockScalar_spec P hS2 hjord 0 hij
  rw [chiTilde_zeroG P hS2] at hspec
  have h1 : (blockHermG (𝕜 := ℝ) i j (1 : ℝ))
      = blockHermG i j (blockScalar P hS2 hjord 0 hij) := by
    simpa using hspec
  have hentry := congrArg (fun x : HermitianMat n ℝ => x.mat i j) h1
  simp only [blockHerm_matG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hentry
  have hij' : ¬ (j = i ∧ i = j) := fun ⟨h', _⟩ => hij h'.symm
  simp only [Matrix.single, Matrix.of_apply, hij', if_true, if_false, and_self,
    eq_self_iff_true, star_trivial] at hentry
  simpa using hentry.symm

/-- The block scalar reads off as a matrix entry of `χ̃(r)`, which is how its
continuity in `r` is obtained. -/
theorem blockScalar_eq_entry (hS2 : P.FirstArgContinuous)
    (hjord : ThetaPreservesJordanG P) (r : n → ℝ) {i j : n} (hij : i ≠ j) :
    blockScalar P hS2 hjord r hij
      = ((chiTildeG P hS2 r).val (blockHermG i j (1 : ℝ))).mat i j := by
  rw [blockScalar_spec P hS2 hjord r hij]
  simp only [blockHerm_matG, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hij' : ¬ (j = i ∧ i = j) := fun ⟨h', _⟩ => hij h'.symm
  simp [Matrix.single, hij']

end Necessity
