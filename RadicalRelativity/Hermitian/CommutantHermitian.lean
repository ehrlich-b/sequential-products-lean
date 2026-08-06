/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.OrderUnit

set_option linter.style.longLine false

/-!
# The commutant of the Hermitian matrices, over any `RCLike` field

A matrix commuting with every Hermitian matrix is a scalar; if it is additionally
traceless it is zero.

This replaces the one field-dependent step of `Necessity/ComparisonInstance.lean`'s
`commute_of_opCommute` (Jordan-operator commutation ⟺ matrix commutation). That
proof kills the commutator `C = [a,b]` using the **anti-Hermitian** generators
`i·E_ij − i·E_ji`, which do not exist over ℝ. The generators used here are
Hermitian over *every* `RCLike` field:

* real diagonals with distinct entries force `C` to be diagonal
  (`eq_diagonal_of_commute_hermitian`);
* the symmetric off-diagonals `E_ij + E_ji` then equate all its diagonal entries,
  so `C = λ • 1` (`exists_smul_one_of_commute_hermitian`);
* `λ • 1` has trace `card • λ`, so a traceless such `C` vanishes
  (`eq_zero_of_commute_hermitian_of_trace_zero`).

The traceless hypothesis is exactly what the caller has: `C = [a,b]` is a
commutator, and commutators are traceless. Note that anti-Hermitian-ness alone
would **not** suffice over ℂ (`i • 1` is anti-Hermitian and nonzero) — it is the
trace that closes the argument uniformly, which is why it appears here.
-/

noncomputable section

open scoped Matrix

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- A real diagonal matrix with pairwise-distinct entries, Hermitian over any
`RCLike` field: the entry at `i` is the index of `i` under a fixed enumeration. -/
def indexDiag (𝕜 : Type*) [RCLike 𝕜] (n : Type*) [Fintype n] [DecidableEq n] :
    HermitianMat n 𝕜 :=
  HermitianMat.diagonal 𝕜 (fun i => ((Fintype.equivFin n i : ℕ) : ℝ))

theorem indexDiag_entries_injective :
    Function.Injective (fun i : n => ((Fintype.equivFin n i : ℕ) : ℝ)) := by
  intro i j hij
  simp only at hij
  have : ((Fintype.equivFin n i : ℕ)) = ((Fintype.equivFin n j : ℕ)) := by
    exact_mod_cast hij
  exact (Fintype.equivFin n).injective (Fin.val_injective this)

/-- The symmetric off-diagonal generator `E_ij + E_ji`, Hermitian over any
`RCLike` field. -/
def symGen (i j : n) : HermitianMat n 𝕜 :=
  ⟨Matrix.single i j (1 : 𝕜) + Matrix.single j i (1 : 𝕜), by
    show _ᴴ = _
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, star_one]
    exact add_comm _ _⟩

@[simp]
theorem symGen_mat (i j : n) :
    (symGen (𝕜 := 𝕜) i j).mat
      = Matrix.single i j (1 : 𝕜) + Matrix.single j i (1 : 𝕜) := rfl

/-- **Step 1**: commuting with a diagonal of distinct entries forces diagonality. -/
theorem eq_diagonal_of_commute_hermitian {C : Matrix n n 𝕜}
    (h : ∀ y : HermitianMat n 𝕜, Commute C y.mat) {i j : n} (hij : i ≠ j) :
    C i j = 0 := by
  have hc := h (indexDiag 𝕜 n)
  have hentry := congrFun (congrFun hc i) j
  rw [indexDiag, HermitianMat.diagonal_mat] at hentry
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  -- `C i j * d j = d i * C i j`, and `d i ≠ d j`
  have hne : ((Fintype.equivFin n i : ℕ) : 𝕜) ≠ ((Fintype.equivFin n j : ℕ) : 𝕜) := by
    intro hEq
    have h1 : ((Fintype.equivFin n i : ℕ) : ℝ) = ((Fintype.equivFin n j : ℕ) : ℝ) := by
      have := hEq
      exact_mod_cast (by exact_mod_cast this : ((Fintype.equivFin n i : ℕ) : ℝ)
        = ((Fintype.equivFin n j : ℕ) : ℝ))
    exact hij (indexDiag_entries_injective h1)
  have hcast : ∀ k : n, ((((Fintype.equivFin n k : ℕ) : ℝ)) : 𝕜)
      = (((Fintype.equivFin n k : ℕ)) : 𝕜) := by
    intro k; push_cast; ring
  rw [hcast i, hcast j] at hentry
  rcases mul_eq_zero.mp (by linear_combination hentry :
      C i j * (((Fintype.equivFin n j : ℕ) : 𝕜) - ((Fintype.equivFin n i : ℕ) : 𝕜)) = 0) with h' | h'
  · exact h'
  · exact absurd (sub_eq_zero.mp h').symm hne

/-- **Steps 1–2**: a matrix commuting with every Hermitian matrix is a scalar. -/
theorem exists_smul_one_of_commute_hermitian {C : Matrix n n 𝕜}
    (h : ∀ y : HermitianMat n 𝕜, Commute C y.mat) :
    ∀ i j : n, C i j = if i = j then C i i else 0 := by
  intro i j
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl]
  · rw [if_neg hij]
    exact eq_diagonal_of_commute_hermitian h hij

/-- **Step 2**: the diagonal entries agree, via the symmetric generators. -/
theorem diag_eq_of_commute_hermitian {C : Matrix n n 𝕜}
    (h : ∀ y : HermitianMat n 𝕜, Commute C y.mat) (i j : n) :
    C i i = C j j := by
  by_cases hij : i = j
  · rw [hij]
  · have hoff : ∀ k l : n, k ≠ l → C k l = 0 := fun k l hkl =>
      eq_diagonal_of_commute_hermitian h hkl
    have hc := h (symGen (𝕜 := 𝕜) i j)
    have hentry := congrFun (congrFun hc i) j
    rw [symGen_mat] at hentry
    -- `(C · (E_ij+E_ji))_{ij} = C i i` and `((E_ij+E_ji) · C)_{ij} = C j j`
    have hL : ((C * (Matrix.single i j (1 : 𝕜) + Matrix.single j i 1) : Matrix n n 𝕜)) i j
        = C i i := by
      rw [Matrix.mul_add, Matrix.add_apply]
      rw [Matrix.mul_single_apply_same]
      rw [Matrix.mul_single_apply_of_ne (c := (1 : 𝕜)) j i i j (Ne.symm hij) C]
      rw [mul_one, add_zero]
    have hR : ((Matrix.single i j (1 : 𝕜) + Matrix.single j i 1) * C : Matrix n n 𝕜) i j
        = C j j := by
      rw [Matrix.add_mul, Matrix.add_apply]
      rw [Matrix.single_mul_apply_same]
      rw [Matrix.single_mul_apply_of_ne (c := (1 : 𝕜)) j i i j hij C]
      rw [one_mul, add_zero]
    rw [hL, hR] at hentry
    exact hentry

/-- **The uniform kill (steps 1–3)**: a traceless matrix commuting with every
Hermitian matrix is zero, over any `RCLike` field.  The caller's `C` is a
commutator `[a,b]`, hence traceless; the trace — not anti-Hermitian-ness — is what
closes the argument uniformly, since `i • 1` is anti-Hermitian and nonzero. -/
theorem eq_zero_of_commute_hermitian_of_trace_zero [Nonempty n] {C : Matrix n n 𝕜}
    (h : ∀ y : HermitianMat n 𝕜, Commute C y.mat) (htr : C.trace = 0) : C = 0 := by
  obtain ⟨i₀⟩ := ‹Nonempty n›
  -- every diagonal entry equals the one at `i₀`, off-diagonals vanish
  have hdiag : ∀ i : n, C i i = C i₀ i₀ := fun i => diag_eq_of_commute_hermitian h i i₀
  have htrace : C.trace = (Fintype.card n : 𝕜) * C i₀ i₀ := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Finset.sum_congr rfl fun i _ => hdiag i, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [htrace] at htr
  have hcard : (Fintype.card n : 𝕜) ≠ 0 := by
    have hpos : 0 < Fintype.card n := Fintype.card_pos
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hzero : C i₀ i₀ = 0 := (mul_eq_zero.mp htr).resolve_left hcard
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [hdiag i, hzero, Matrix.zero_apply]
  · rw [eq_diagonal_of_commute_hermitian h hij, Matrix.zero_apply]

end HermitianMat
