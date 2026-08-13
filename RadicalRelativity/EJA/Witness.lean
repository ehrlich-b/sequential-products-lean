/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.EJA.PeirceMul
import RadicalRelativity.Vendor.HermitianMat.Jordan

set_option linter.style.longLine false

/-!
# Non-vacuity of the Peirce layer, on the paper's own carrier

**ARC-9 block 9.5, 2026-08-12.**

`EJA/Peirce.lean` and `EJA/PeirceMul.lean` are stated over an abstract real commutative
Jordan algebra and are *conditional* throughout: every theorem assumes `c ∘ c = c`, and the
sharper ones assume an element with `c ∘ y = ½ y`. Conditional theorems are worth exactly
as much as their hypotheses are satisfiable, and **this project has already shipped an
abstract tier whose hypothesis no carrier satisfied** — ARC-6's abstract rows, fixed only
when `HermitianMat.isArchimedean` was proved (`LEDGER.md`). This file is the check that was
missing then.

Two things are verified, and they are different claims.

**1. The instance stack resolves on `H₂(ℂ)`.** The four typeclass hypotheses of the Peirce
layer — `NonUnitalNonAssocCommRing`, `IsCommJordan`, `Module ℝ`, `IsScalarTower ℝ` — are all
satisfied by `HermitianMat (Fin 2) ℂ` under the tree's own scoped Jordan instances
(`Vendor/HermitianMat/Jordan.lean`, namespace `HermMul`). Nothing had to be built for this:
the vendored file has carried `IsCommJordan (HermitianMat d 𝕜)` all along, and **the EJA
layer is its first consumer** — `grep -rn HermMul` over the tree returns no other user.
★ This is also why the layer assumes `IsScalarTower ℝ J J` rather than `SMulCommClass`:
they are interchangeable for a commutative product, and `IsScalarTower` is the one the
carrier supplies.

**2. The `1/2`-eigenspace is not zero.** This is the part that could have gone wrong
silently. Every rule in `EJA/PeirceMul.lean` mentioning `J_{1/2}` would be *vacuously true*
on a carrier where the half-space is trivial — and the half-space **is** trivial for the two
idempotents one reaches for first, `0` and `1`. So a witness is exhibited: `cWit` is the
rank-one projection `diag(1,0)`, `xWit` is the off-diagonal `[[0,1],[1,0]]`, and
`cWit_mul_xWit` proves `cWit ∘ xWit = ½ · xWit` with `xWit ≠ 0`.

★ **Scope.** This is non-vacuity, not coverage: it shows the Peirce hypotheses have a model
with all three components nonzero. It does **not** connect the EJA layer to any manifest
row, and no row moves on it. The rank-two carrier is used because it is the smallest place
where a `1/2`-eigenvector exists, not because rank two matters here.
-/

open HermMul RadicalRelativity.EJA

namespace RadicalRelativity.EJA.Witness

/-- The paper's rank-two carrier. -/
abbrev H2 := HermitianMat (Fin 2) ℂ

/-! ### 1. The instance stack -/

noncomputable example : NonUnitalNonAssocCommRing H2 := inferInstance
noncomputable example : IsCommJordan H2 := inferInstance
noncomputable example : Module ℝ H2 := inferInstance
noncomputable example : IsScalarTower ℝ H2 H2 := inferInstance

/-! ### 2. An idempotent with a nonzero `1/2`-eigenspace -/

/-- The rank-one projection `diag(1,0)`. -/
noncomputable def cWit : H2 := HermitianMat.diagonal ℂ ![1, 0]

/-- The off-diagonal Hermitian matrix `[[0,1],[1,0]]`. -/
def xWit : H2 :=
  ⟨!![0, 1; 1, 0], by
    simp only [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

theorem cWit_mat : cWit.mat = Matrix.diagonal (fun i => ((![1, 0] : Fin 2 → ℝ) i : ℂ)) := rfl

theorem xWit_mat : xWit.mat = !![0, 1; 1, 0] := rfl

theorem xWit_ne_zero : xWit ≠ 0 := by
  intro h
  have h2 : xWit.mat 0 1 = (0 : H2).mat 0 1 := by rw [h]
  rw [xWit_mat] at h2
  simp at h2

/-- `cWit` is an idempotent for the Jordan product. -/
theorem cWit_idem : cWit * cWit = cWit := by
  apply HermitianMat.ext
  rw [mul_eq_symmMul, HermitianMat.symmMul_toMat, cWit_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- **The half-space is inhabited by a nonzero element**, so every `J_{1/2}` rule in
`EJA/PeirceMul.lean` has content on this carrier. -/
theorem cWit_mul_xWit : cWit * xWit = (2 : ℝ)⁻¹ • xWit := by
  apply HermitianMat.ext
  rw [mul_eq_symmMul, HermitianMat.symmMul_toMat, cWit_mat, xWit_mat]
  show _ = (2 : ℝ)⁻¹ • xWit.mat
  rw [xWit_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMul_diagonal]

/-! ### 3. The layer, exercised

Three theorems of the abstract layer instantiated at the witness. They are corollaries with
no new content — the point is that the hypotheses discharge against a real carrier rather
than remaining hypothetical. -/

/-- `eigen_half_mul_half` at the witness: `xWit ∘ xWit` has no `1/2`-component. -/
theorem witness_half_mul_half : cWit * (cWit * (xWit * xWit)) = cWit * (xWit * xWit) :=
  eigen_half_mul_half cWit_idem cWit_mul_xWit cWit_mul_xWit

/-- `peirceHalf_mul_half_eq_zero` at the witness. -/
theorem witness_peirceHalf_eq_zero : peirceHalf cWit (xWit * xWit) = 0 :=
  peirceHalf_mul_half_eq_zero cWit_idem cWit_mul_xWit cWit_mul_xWit

/-- `exists_peirce_decomposition` at the witness: `xWit` itself splits. -/
theorem witness_decomposition :
    ∃ y₁ yₕ y₀ : H2, cWit * y₁ = y₁ ∧ cWit * yₕ = (2 : ℝ)⁻¹ • yₕ ∧ cWit * y₀ = 0
      ∧ xWit = y₁ + yₕ + y₀ :=
  exists_peirce_decomposition cWit_idem xWit

/-- **The middle branch of `eigenvalue_trichotomy` is attained.**  Without this the
trichotomy would still be true with an empty `1/2` case, and every `J_{1/2}` rule with it.

★ This statement replaced a genuinely vacuous one, and the replacement is the finding.  The
first version here read `(2:ℝ)⁻¹ = 0 ∨ (2:ℝ)⁻¹ = (2:ℝ)⁻¹ ∨ (2:ℝ)⁻¹ = 1`, discharged by
`eigenvalue_trichotomy` at the witness — a disjunction whose middle disjunct is `rfl`, so it
is provable with no witness, no carrier and no Jordan identity.  It is the VACUOUS defect
kind from ARC-8's three-way taxonomy, reproduced inside the file written to rule out
vacuity, within an hour of that file being written. -/
theorem witness_half_attained : ∃ y : H2, y ≠ 0 ∧ cWit * y = (2 : ℝ)⁻¹ • y :=
  ⟨xWit, xWit_ne_zero, cWit_mul_xWit⟩

end RadicalRelativity.EJA.Witness
