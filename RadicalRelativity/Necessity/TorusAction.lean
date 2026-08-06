/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Necessity.ConjTransport

set_option linter.style.longLine false

/-!
# The torus action: the target of the `Ad_{a^{it}}` identification

The complex lane's remaining paper-analytic step is to identify the comparison
map `Θ_{a(r)}` with the twist conjugation `Ad_{a(r)^{it}}`.  On the spectral
frame of `a(r)`, that conjugation is by the **diagonal torus unitary**
`U_t(r) = diag(e^{i t r_k})`.  This file computes its action exactly:

* `torusU` — the unitary, with `torusU_unitary` (both `ᴴ`-products are `1`).
* `torusU_fixes_frameProj` — it fixes every frame projection.
* `torusU_block` — **the block action**: `Ad_{U_t(r)} (blockHerm i j z)
  = blockHerm i j (e^{i t (r_i − r_j)} · z)`, i.e. rotation of the `(i,j)` block
  by the angle `t(r_i − r_j)`.

That angle is exactly the one `complex_perFrame_unconditional` produces for the
comparison map's block generator, which is what makes the two maps candidates
for equality; closing the identification then needs only that the frame
projections together with the blocks span.
-/

noncomputable section

open ComplexOrder
open scoped Matrix

namespace Necessity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The torus unitary -/

/-- The diagonal torus unitary `diag(e^{i t r_k})`. -/
def torusU (t : ℝ) (r : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal (fun k => Complex.exp ((↑(t * r k) : ℂ) * Complex.I))

theorem torusU_conjTranspose (t : ℝ) (r : n → ℝ) :
    (torusU t r)ᴴ
      = Matrix.diagonal (fun k => Complex.exp ((↑(-(t * r k)) : ℂ) * Complex.I)) := by
  rw [torusU, Matrix.diagonal_conjTranspose]
  congr 1
  funext k
  show star (Complex.exp ((↑(t * r k) : ℂ) * Complex.I)) = _
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

omit [Fintype n] [DecidableEq n] in
/-- The pointwise cancellation `e^{i t r_k} · e^{-i t r_k} = 1`. -/
theorem torusU_diag_cancel (t : ℝ) (r : n → ℝ) (k : n) :
    Complex.exp ((↑(t * r k) : ℂ) * Complex.I)
      * Complex.exp ((↑(-(t * r k)) : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_add]
  rw [show ((↑(t * r k) : ℂ) * Complex.I + (↑(-(t * r k)) : ℂ) * Complex.I) = 0 by
    push_cast; ring]
  exact Complex.exp_zero

/-- `U_t(r)` is unitary in both `ᴴ`-orders. -/
theorem torusU_unitary (t : ℝ) (r : n → ℝ) :
    (torusU t r)ᴴ * torusU t r = 1 ∧ torusU t r * (torusU t r)ᴴ = 1 := by
  constructor
  · rw [torusU_conjTranspose, torusU, Matrix.diagonal_mul_diagonal]
    rw [show (fun k => Complex.exp ((↑(-(t * r k)) : ℂ) * Complex.I)
        * Complex.exp ((↑(t * r k) : ℂ) * Complex.I)) = fun _ : n => (1 : ℂ) from
      funext (fun k => by rw [mul_comm]; exact torusU_diag_cancel t r k)]
    exact Matrix.diagonal_one
  · rw [torusU_conjTranspose, torusU, Matrix.diagonal_mul_diagonal]
    rw [show (fun k => Complex.exp ((↑(t * r k) : ℂ) * Complex.I)
        * Complex.exp ((↑(-(t * r k)) : ℂ) * Complex.I)) = fun _ : n => (1 : ℂ) from
      funext (torusU_diag_cancel t r)]
    exact Matrix.diagonal_one

/-! ## The entry formula for conjugation by a diagonal -/

/-- Conjugation by the torus unitary, entrywise: it multiplies the `(a,b)` entry
by `e^{i t (r_a − r_b)}`. -/
theorem adU_torusU_entry (t : ℝ) (r : n → ℝ) (x : HermitianMat n ℂ) (a b : n) :
    (adU (torusU t r) x).mat a b
      = Complex.exp ((↑(t * r a) : ℂ) * Complex.I) * x.mat a b
        * Complex.exp ((↑(-(t * r b)) : ℂ) * Complex.I) := by
  rw [adU_apply, HermitianMat.conj_apply_mat, torusU_conjTranspose, torusU,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

/-! ## The action on the frame -/

/-- The torus unitary fixes every frame projection: conjugation by a diagonal
matrix multiplies the `(a,b)` entry by `e^{i t (r_a − r_b)}`, which is `1` on the
diagonal, and the frame projection is supported there. -/
theorem torusU_fixes_frameProj (t : ℝ) (r : n → ℝ) (i : n) :
    adU (torusU t r) (frameProj i) = frameProj i := by
  ext1
  ext a b
  rw [adU_torusU_entry, frameProj_mat_eq_single]
  by_cases hab : a = b
  · subst hab
    rw [mul_comm (Complex.exp ((↑(t * r a) : ℂ) * Complex.I)), mul_assoc,
      torusU_diag_cancel, mul_one]
  · have hz : Matrix.single i i (1 : ℂ) a b = 0 := by
      have : ¬(i = a ∧ i = b) := fun ⟨h1, h2⟩ => hab (h1 ▸ h2)
      simp [Matrix.single, this]
    rw [hz, mul_zero, zero_mul]

/-! ## The action on the blocks -/

/-- **The block action of the torus unitary**: `Ad_{U_t(r)}` rotates the `(i,j)`
block by the angle `t(r_i − r_j)`.  This is exactly the angle
`complex_perFrame_unconditional` produces for the comparison map's block
generator, which is what makes the two maps candidates for equality. -/
theorem torusU_block (t : ℝ) (r : n → ℝ) {i j : n} (hij : i ≠ j) (z : ℂ) :
    adU (torusU t r) (blockHerm i j z)
      = blockHerm i j (Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z) := by
  ext1
  ext a b
  rw [adU_torusU_entry, blockHerm_mat, blockHerm_mat]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  -- the four cases of `(a,b)` against `{(i,j), (j,i)}`
  by_cases hai : a = i
  · by_cases hbj : b = j
    · rw [hai, hbj]
      have c1 : Matrix.single i j (1:ℂ) i j = 1 := by simp [Matrix.single]
      have c2 : Matrix.single j i (1:ℂ) i j = 0 := by
        have : ¬(j = i ∧ i = j) := fun ⟨h1, _⟩ => hij h1.symm
        simp [Matrix.single, this]
      rw [c1, c2, mul_zero, add_zero, mul_one, mul_one]
      have hcomb : Complex.exp ((↑(t * r i) : ℂ) * Complex.I)
          * Complex.exp ((↑(-(t * r j)) : ℂ) * Complex.I)
          = Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc Complex.exp ((↑(t * r i) : ℂ) * Complex.I) * z
              * Complex.exp ((↑(-(t * r j)) : ℂ) * Complex.I)
          = (Complex.exp ((↑(t * r i) : ℂ) * Complex.I)
              * Complex.exp ((↑(-(t * r j)) : ℂ) * Complex.I)) * z := by ring
        _ = Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z := by rw [hcomb]
        _ = Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z
              + star (Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z) * 0 := by
              ring
    · have hz : ∀ w : ℂ, w * Matrix.single i j (1:ℂ) a b
          + star w * Matrix.single j i (1:ℂ) a b = 0 := by
        intro w
        have d1 : Matrix.single i j (1:ℂ) a b = 0 := by
          have : ¬(i = a ∧ j = b) := fun ⟨_, h2⟩ => hbj h2.symm
          simp [Matrix.single, this]
        have d2 : Matrix.single j i (1:ℂ) a b = 0 := by
          have : ¬(j = a ∧ i = b) := fun ⟨h1, _⟩ => hij (h1.trans hai).symm
          simp [Matrix.single, this]
        rw [d1, d2, mul_zero, mul_zero, add_zero]
      rw [hz, hz, mul_zero, zero_mul]
  · by_cases haj : a = j
    · by_cases hbi : b = i
      · rw [haj, hbi]
        have c1 : Matrix.single i j (1:ℂ) j i = 0 := by
          have : ¬(i = j ∧ j = i) := fun ⟨h1, _⟩ => hij h1
          simp [Matrix.single, this]
        have c2 : Matrix.single j i (1:ℂ) j i = 1 := by simp [Matrix.single]
        rw [c1, c2, mul_zero, zero_add, mul_one, mul_one]
        have hconj : star (Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I))
            = Complex.exp ((↑(-(t * (r i - r j))) : ℂ) * Complex.I) := by
          rw [Complex.star_def, ← Complex.exp_conj]
          congr 1
          simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
          push_cast
          ring
        have hcomb : Complex.exp ((↑(t * r j) : ℂ) * Complex.I)
            * Complex.exp ((↑(-(t * r i)) : ℂ) * Complex.I)
            = Complex.exp ((↑(-(t * (r i - r j))) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        rw [star_mul', hconj]
        calc Complex.exp ((↑(t * r j) : ℂ) * Complex.I) * star z
                * Complex.exp ((↑(-(t * r i)) : ℂ) * Complex.I)
            = (Complex.exp ((↑(t * r j) : ℂ) * Complex.I)
                * Complex.exp ((↑(-(t * r i)) : ℂ) * Complex.I)) * star z := by ring
          _ = Complex.exp ((↑(-(t * (r i - r j))) : ℂ) * Complex.I) * star z := by
                rw [hcomb]
          _ = Complex.exp ((↑(t * (r i - r j)) : ℂ) * Complex.I) * z * 0
                + Complex.exp ((↑(-(t * (r i - r j))) : ℂ) * Complex.I) * star z := by
                ring
      · have hz : ∀ w : ℂ, w * Matrix.single i j (1:ℂ) a b
            + star w * Matrix.single j i (1:ℂ) a b = 0 := by
          intro w
          have d1 : Matrix.single i j (1:ℂ) a b = 0 := by
            have : ¬(i = a ∧ j = b) := fun ⟨h1, _⟩ => hai h1.symm
            simp [Matrix.single, this]
          have d2 : Matrix.single j i (1:ℂ) a b = 0 := by
            have : ¬(j = a ∧ i = b) := fun ⟨_, h2⟩ => hbi h2.symm
            simp [Matrix.single, this]
          rw [d1, d2, mul_zero, mul_zero, add_zero]
        rw [hz, hz, mul_zero, zero_mul]
    · have hz : ∀ w : ℂ, w * Matrix.single i j (1:ℂ) a b
          + star w * Matrix.single j i (1:ℂ) a b = 0 := by
        intro w
        have d1 : Matrix.single i j (1:ℂ) a b = 0 := by
          have : ¬(i = a ∧ j = b) := fun ⟨h1, _⟩ => hai h1.symm
          simp [Matrix.single, this]
        have d2 : Matrix.single j i (1:ℂ) a b = 0 := by
          have : ¬(j = a ∧ i = b) := fun ⟨h1, _⟩ => haj h1.symm
          simp [Matrix.single, this]
        rw [d1, d2, mul_zero, mul_zero, add_zero]
      rw [hz, hz, mul_zero, zero_mul]

end Necessity
