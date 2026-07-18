/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The rank-two boundary (`sec:qubit`)

Machine-checked core of Section 6 of

> Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*
> (`landing/papers/twist-normal-form/main.tex`), `prop:n2-necessity`,
> `thm:qubit-boundary`, `rem:n2-selection`.

At rank two the complex qubit escapes the rigidity of `mthm:master`: the twist
parameter is a *frame function* `τ(F)` rather than a single global constant, and
there is an explicit continuous frame-dependent product satisfying all seven
sequential axioms and conjugate to no constant-twist product. This module
formalizes the algebraic core on the concrete self-adjoint qubit algebra
`M₂(ℂ)ˢᵃ`, modelled inside `Matrix (Fin 2) (Fin 2) ℂ`.

The paper's Section 6 proofs (`thm:qubit-boundary`, Steps 0–7) are the source of
truth; the SymPy script `verify_n2.py` (labels V1–V10) is corroboration. This
file reproduces the load-bearing identities as concrete `2×2` matrix / complex
arithmetic — no functional calculus, no continuity axiom, no new `axiom`s.

## What is formalized

* **`n2_necessity`** (`prop:n2-necessity`): the block rotation of the comparison
  map is `e^{i·t_F·(r₀−r₁)}` for a single real `t_F` per frame (`r_i = log λ_i`),
  with no cross-frame constraint. Modelled at the differential/generator level:
  a real-linear block angle vanishing on the coalescence line `{r₀=r₁}`
  factors through `r₀−r₁`. Realized as a genuine `SO(2)` rotation (`blockRot`).
* **`n2_exchange_selects_luders`** (`rem:n2-selection`, the paper's new Remark 6.2,
  Bryan-sanctioned, consumed by Paper B): if the block generator is exchange
  covariant then `t_F = 0` for every frame, i.e. the product is Lüders.
* **`sp_blockForm`** (`thm:qubit-boundary(i)`, V1): the family `a·b = F_a b F_aᴴ`,
  `F_a = a^{1/2+iτ}` in the spectral frame, has the displayed block form.
  **`sp_luders_of_twist_zero`** (V3): at `τ = 0` it *is* the Lüders product
  `√a · b · √a`. Degenerations `sp_scalar` (V2) and `sp_rankOne` (V3, `λ₂=0`).
* **`sp_maps_effects`** (`thm:qubit-boundary(i)`, cone preservation): effects to
  effects — `F_a b F_aᴴ` is positive semidefinite and `≤ a ≤ 1`.
* **`tau_std_eq_one`, `tau_had_eq_zero`** (`eq:tau-def`, V9): `τ(F)=(2tr(PR)−1)²`
  takes value `1` on the reference frame and `0` on the Hadamard frame — the
  frame-dependence witness. **`tau_swap_invariant`** (V9c).
* **`phase_cocycle`** (V5a): `F_a F_b = F_{ab}` on a shared frame (`ζ=1`).
* **`compat_backward`** (V7): commuting effects are compatible (`a·b = b·a`).

## Faithfulness / scope

Everything here is `necessity-only` in the paper's sense: no exhaustive rank-two
classification is claimed. `n2_necessity` and `n2_exchange_selects_luders` are
stated for an *arbitrary* real-linear block angle vanishing on the coalescence
line (the differential shadow the paper derives from the comparison map of an
S1–S7 product; that derivation is the paper's), so they are necessity statements
at the generator level; `sp_*` formalize the explicit family's block algebra.
The seven-axiom verification and the non-conjugacy argument that establish
*sharpness* are the paper's Section 6 (+ `verify_n2.py` corroboration) — they
are **not** in this file. The comparison-map inputs (`Θ_a` a Jordan
automorphism fixing the frame, its `SO(2)` block action, the cocycle) are the
`Interface`/paper imports; here we consume only their differential shadow (a real
linear angle vanishing on the coalescence line). No `axiom`s are introduced and
none from the ledger are consumed: `#print axioms` on every result shows only the
Lean core.
-/

noncomputable section

open Matrix
open scoped ComplexOrder

namespace MasterTheorem.RankTwo

/-! ## The single-eigenvalue power `λ^{1/2+it}` and its off-diagonal coefficient

For a diagonal effect `a = diag(λ₁,λ₂)` in its own spectral frame, the paper's
`F_a = a^{1/2+it}` is the diagonal matrix with entries `gEntry λ_i t = λ_i^{1/2+it}`.
Because `√0 = 0`, the paper's convention `0^z := 0` is automatic. -/

/-- `gEntry lam t = lam^{1/2+it} = √lam · e^{i t log lam}` for a single nonnegative
eigenvalue (`0^z := 0` automatic via `√0 = 0`). -/
def gEntry (lam t : ℝ) : ℂ :=
  (Real.sqrt lam : ℂ) * Complex.exp ((↑(t * Real.log lam) : ℂ) * Complex.I)

/-- The off-diagonal coherence coefficient `√(λ₁λ₂) · e^{i t (log λ₁ − log λ₂)}`
(the entry of `E(λ₁,λ₂)` on the coherence `1`-space; V1). -/
def offCoeff (l1 l2 t : ℝ) : ℂ :=
  (Real.sqrt (l1 * l2) : ℂ) * Complex.exp ((↑(t * (Real.log l1 - Real.log l2)) : ℂ) * Complex.I)

@[simp] theorem gEntry_zero_left (t : ℝ) : gEntry 0 t = 0 := by
  simp [gEntry]

/-- `gEntry lam 0 = √lam`: at zero twist the entry is the real square root, so the
family reduces to the Lüders square root (V3). -/
theorem gEntry_twist_zero (lam : ℝ) : gEntry lam 0 = (Real.sqrt lam : ℂ) := by
  simp [gEntry]

theorem conj_gEntry (lam t : ℝ) :
    star (gEntry lam t)
      = (Real.sqrt lam : ℂ) * Complex.exp (-((↑(t * Real.log lam) : ℂ) * Complex.I)) := by
  rw [← starRingEnd_apply, gEntry, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `λ^{1/2+it} · conj(λ^{1/2+it}) = λ` for `λ ≥ 0`: the diagonal entry preserves the
eigenvalue (unimodular twist). -/
theorem gEntry_mul_conj (lam t : ℝ) (h : 0 ≤ lam) :
    gEntry lam t * star (gEntry lam t) = (lam : ℂ) := by
  rw [conj_gEntry, gEntry]
  have hexp : Complex.exp ((↑(t * Real.log lam) : ℂ) * Complex.I)
      * Complex.exp (-((↑(t * Real.log lam) : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hsqrt : (Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]
  calc (↑(Real.sqrt lam) * Complex.exp ((↑(t * Real.log lam) : ℂ) * Complex.I))
        * (↑(Real.sqrt lam) * Complex.exp (-((↑(t * Real.log lam) : ℂ) * Complex.I)))
      = (↑(Real.sqrt lam) * ↑(Real.sqrt lam))
        * (Complex.exp ((↑(t * Real.log lam) : ℂ) * Complex.I)
            * Complex.exp (-((↑(t * Real.log lam) : ℂ) * Complex.I))) := by ring
    _ = (lam : ℂ) := by rw [hexp, hsqrt, mul_one]

/-- `λ₁^{1/2+it} · conj(λ₂^{1/2+it}) = offCoeff λ₁ λ₂ t` (V1, off-diagonal). -/
theorem gEntry_mul_conj_off (l1 l2 t : ℝ) (h1 : 0 ≤ l1) :
    gEntry l1 t * star (gEntry l2 t) = offCoeff l1 l2 t := by
  rw [conj_gEntry, gEntry, offCoeff]
  have hsqrt : (Real.sqrt l1 : ℂ) * (Real.sqrt l2 : ℂ) = (Real.sqrt (l1 * l2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul h1]
  have harg : (↑(t * Real.log l1) : ℂ) * Complex.I + -((↑(t * Real.log l2) : ℂ) * Complex.I)
      = (↑(t * (Real.log l1 - Real.log l2)) : ℂ) * Complex.I := by
    push_cast; ring
  calc (↑(Real.sqrt l1) * Complex.exp ((↑(t * Real.log l1) : ℂ) * Complex.I))
        * (↑(Real.sqrt l2) * Complex.exp (-((↑(t * Real.log l2) : ℂ) * Complex.I)))
      = (↑(Real.sqrt l1) * ↑(Real.sqrt l2))
        * (Complex.exp ((↑(t * Real.log l1) : ℂ) * Complex.I)
            * Complex.exp (-((↑(t * Real.log l2) : ℂ) * Complex.I))) := by ring
    _ = (Real.sqrt (l1 * l2) : ℂ) * Complex.exp ((↑(t * (Real.log l1 - Real.log l2)) : ℂ) * Complex.I) := by
        rw [hsqrt, ← Complex.exp_add, harg]

/-- `offCoeff λ λ t = λ` for `λ ≥ 0` (V2, scalar): a scalar effect is twist-invisible. -/
theorem offCoeff_scalar (lam t : ℝ) (h : 0 ≤ lam) : offCoeff lam lam t = (lam : ℂ) := by
  rw [offCoeff, sub_self, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Real.sqrt_mul_self h]

/-- `offCoeff λ 0 t = 0` (V3): a rank-deficient first argument kills the coherence. -/
theorem offCoeff_zero_right (l1 t : ℝ) : offCoeff l1 0 t = 0 := by
  simp [offCoeff]

/-- `offCoeff λ₁ λ₂ 0 = √(λ₁λ₂)` (V3): at zero twist the coefficient is the Lüders
value `√(λ₁λ₂)`. -/
theorem offCoeff_twist_zero (l1 l2 : ℝ) : offCoeff l1 l2 0 = (Real.sqrt (l1 * l2) : ℂ) := by
  simp [offCoeff]

/-- `offCoeff λ₂ λ₁ t = conj(offCoeff λ₁ λ₂ t)`: the `(2,1)` coefficient is the
conjugate of the `(1,2)` coefficient. -/
theorem offCoeff_swap (l1 l2 t : ℝ) :
    offCoeff l2 l1 t = star (offCoeff l1 l2 t) := by
  rw [← starRingEnd_apply, offCoeff, offCoeff, map_mul, Complex.conj_ofReal, mul_comm l2 l1,
    ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-! ## The frame-dependent family on `M₂(ℂ)ˢᵃ` (`eq:qubit-family`) -/

/-- `F_a = a^{1/2+it}` for a diagonal `a = diag(λ₁,λ₂)` in its spectral frame. -/
def Fdiag (l1 l2 t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![gEntry l1 t, gEntry l2 t]

/-- The frame-dependent product in the spectral frame of `a`: `a·b = F_a b F_aᴴ`
(`eq:qubit-family`, `F_a = a^{1/2+iτ(a)}`). -/
def sp (l1 l2 t : ℝ) (b : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Fdiag l1 l2 t * b * (Fdiag l1 l2 t)ᴴ

/-- Entrywise action: `(a·b)_{ij} = λ_i^{1/2+it} · b_{ij} · conj(λ_j^{1/2+it})`. -/
theorem sp_apply (l1 l2 t : ℝ) (b : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    sp l1 l2 t b i j
      = ![gEntry l1 t, gEntry l2 t] i * b i j
          * star (![gEntry l1 t, gEntry l2 t] j) := by
  simp only [sp, Fdiag, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply]

/-- **Block normal form** (`thm:qubit-boundary(i)`, V1). In the spectral frame of
`a = diag(λ₁,λ₂)`, `a·b` has diagonal blocks `λ_i b_{ii}` and off-diagonal
coefficient `√(λ₁λ₂) e^{±i t log(λ₁/λ₂)}`. -/
theorem sp_blockForm (l1 l2 t : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2)
    (b : Matrix (Fin 2) (Fin 2) ℂ) :
    sp l1 l2 t b =
      !![ (l1 : ℂ) * b 0 0, offCoeff l1 l2 t * b 0 1;
          star (offCoeff l1 l2 t) * b 1 0, (l2 : ℂ) * b 1 1 ] := by
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  constructor <;> rw [Fin.forall_fin_two] <;> constructor <;>
    simp only [sp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Fin.isValue]
  · -- (0,0)
    rw [mul_right_comm, gEntry_mul_conj l1 t h1]
  · -- (0,1)
    rw [mul_right_comm, gEntry_mul_conj_off l1 l2 t h1]
  · -- (1,0)
    rw [mul_right_comm, gEntry_mul_conj_off l2 l1 t h2, offCoeff_swap]
  · -- (1,1)
    rw [mul_right_comm, gEntry_mul_conj l2 t h2]

/-- **Scalar invisibility** (V2): `(λ·Id)·b = λ·b` for every twist — the value of
`τ` on scalar effects is immaterial. -/
theorem sp_scalar (lam t : ℝ) (h : 0 ≤ lam) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    sp lam lam t b = (lam : ℂ) • b := by
  rw [sp_blockForm lam lam t h h, offCoeff_scalar lam t h]
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  constructor <;> rw [Fin.forall_fin_two] <;> constructor <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, Matrix.smul_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]

/-- **Rank-deficient first argument** (V3): `diag(λ,0)·b = λ·(P b P)`, twist-independent
(`P = E₁₁`). -/
theorem sp_rankOne (x t : ℝ) (h : 0 ≤ x) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    sp x 0 t b = !![ (x : ℂ) * b 0 0, 0; 0, 0 ] := by
  rw [sp_blockForm x 0 t h le_rfl, offCoeff_zero_right]
  refine Matrix.ext ?_
  rw [Fin.forall_fin_two]
  constructor <;> rw [Fin.forall_fin_two] <;> constructor <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, star_zero, zero_mul, Complex.ofReal_zero]

/-- **Reduction to Lüders at `τ = 0`** (V3). At zero twist the family is exactly the
standard Lüders product `√a · b · √a` (`√a = diag(√λ₁,√λ₂)`). -/
theorem sp_luders_of_twist_zero (l1 l2 : ℝ) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    sp l1 l2 0 b
      = Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)] * b
          * Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)] := by
  have hF : Fdiag l1 l2 0 = Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)] := by
    rw [Fdiag, gEntry_twist_zero, gEntry_twist_zero]
  have hH : (Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)])ᴴ
      = Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)] := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    refine funext ?_
    rw [Fin.forall_fin_two]
    constructor <;> simp [Pi.star_apply]
  rw [sp, hF, hH]

/-! ## Cone preservation: effects to effects (`thm:qubit-boundary(i)`)

`b ↦ F_a b F_aᴴ` is a congruence, hence positivity preserving, and takes `[0,a]`
into `[0,a]`. Combined with `a ≤ 1` this maps effects to effects. -/

/-- `F_a F_aᴴ = a`: the congruence sends the unit to `a` (`√(λ₁λ₂)` unimodularity). -/
theorem Fdiag_mul_conjTranspose (l1 l2 t : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) :
    Fdiag l1 l2 t * (Fdiag l1 l2 t)ᴴ = Matrix.diagonal ![(l1 : ℂ), (l2 : ℂ)] := by
  rw [Fdiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  refine funext ?_
  rw [Fin.forall_fin_two]
  constructor <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Pi.star_apply]
  · exact gEntry_mul_conj l1 t h1
  · exact gEntry_mul_conj l2 t h2

/-- **Positivity preservation**: `a·b` is positive semidefinite when `b` is (congruence). -/
theorem sp_posSemidef (l1 l2 t : ℝ) {b : Matrix (Fin 2) (Fin 2) ℂ} (hb : b.PosSemidef) :
    (sp l1 l2 t b).PosSemidef :=
  hb.mul_mul_conjTranspose_same (Fdiag l1 l2 t)

/-- **Effects to effects** (`thm:qubit-boundary(i)`). If `b` is an effect
(`0 ≤ b ≤ 1`) and `a = diag(λ₁,λ₂)` is an effect (`0 ≤ a ≤ 1`, encoded as
`0 ≤ λ_i` and `1 - a` PSD), then `a·b` is an effect: `0 ≤ a·b ≤ 1`. -/
theorem sp_maps_effects (l1 l2 t : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2)
    {b : Matrix (Fin 2) (Fin 2) ℂ} (hb0 : b.PosSemidef)
    (hb1 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - b).PosSemidef)
    (ha1 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - Matrix.diagonal ![(l1 : ℂ), (l2 : ℂ)]).PosSemidef) :
    (sp l1 l2 t b).PosSemidef ∧
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) - sp l1 l2 t b).PosSemidef := by
  refine ⟨sp_posSemidef l1 l2 t hb0, ?_⟩
  have hFbF : Fdiag l1 l2 t * ((1 : Matrix (Fin 2) (Fin 2) ℂ) - b) * (Fdiag l1 l2 t)ᴴ
      = Matrix.diagonal ![(l1 : ℂ), (l2 : ℂ)] - sp l1 l2 t b := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Fdiag_mul_conjTranspose l1 l2 t h1 h2, sp]
  have key : (1 : Matrix (Fin 2) (Fin 2) ℂ) - sp l1 l2 t b
      = ((1 : Matrix (Fin 2) (Fin 2) ℂ) - Matrix.diagonal ![(l1 : ℂ), (l2 : ℂ)])
          + Fdiag l1 l2 t * ((1 : Matrix (Fin 2) (Fin 2) ℂ) - b) * (Fdiag l1 l2 t)ᴴ := by
    rw [hFbF]; abel
  rw [key]
  exact ha1.add (hb1.mul_mul_conjTranspose_same (Fdiag l1 l2 t))

/-! ## The frame function `τ(F) = (2 tr(PR) − 1)²` (`eq:tau-def`, V9) -/

/-- The reference rank-one projection `R = E₁₁`. -/
def Rref : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), 0]

/-- The standard-frame projection `P = E₁₁` (shares `R`'s frame). -/
def Pstd : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![(1 : ℂ), 0]

/-- The Hadamard-frame projection `P = |+⟩⟨+| = ½[[1,1],[1,1]]`. -/
def Phad : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of ![![(1/2 : ℂ), 1/2], ![1/2, 1/2]]

/-- The twist frame function `τ(F) = (2 tr(PR) − 1)²` (`eq:tau-def`). -/
def tau (P R : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (2 * (P * R).trace.re - 1) ^ 2

/-- **V9a**: `τ = 1` on the reference frame (`P = R = E₁₁`, `tr(PR) = 1`). -/
theorem tau_std_eq_one : tau Pstd Rref = 1 := by
  have h : (Pstd * Rref).trace = 1 := by
    simp only [Pstd, Rref, Matrix.diagonal_mul_diagonal, Matrix.trace_fin_two,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [tau, h]
  norm_num

/-- **V9b**: `τ = 0` on the Hadamard frame (`tr(PR) = ½`). -/
theorem tau_had_eq_zero : tau Phad Rref = 0 := by
  have h : (Phad * Rref).trace = 1 / 2 := by
    simp only [Phad, Rref, Matrix.trace_fin_two, Matrix.mul_diagonal, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [tau, h]
  norm_num

/-- **V9c**: `τ` is invariant under `P ↔ Id − P` (it depends only on the unordered
frame), for a projection `R` with `tr(R) = 1`. -/
theorem tau_swap_invariant (P R : Matrix (Fin 2) (Fin 2) ℂ) (hR : (R.trace).re = 1) :
    tau (1 - P) R = tau P R := by
  have h : ((1 - P) * R).trace.re = (R.trace).re - (P * R).trace.re := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
  rw [tau, tau, h, hR]
  ring

/-! ## The frame function wired into the family

Adversarial-review addition (2026-07-15): the reviewers observed that `tau` was
evaluated (V9) but never *fed into* `sp`, so the frame-dependence of the product
itself was asserted only in prose. The two theorems below wire them: on the Hadamard
frame the dial reads `0` and the product **is** the Lüders product; on the reference
frame the dial reads `1` and the product is the unit-twist member of the family. -/

/-- **`τ` wired into `sp`, equator witness.** In the Hadamard frame the dial reads
`τ = 0`, so the frame-dependent product on that frame is exactly the Lüders product
`√a · b · √a`. -/
theorem sp_tau_had_is_luders (l1 l2 : ℝ) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    sp l1 l2 (tau Phad Rref) b
      = Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)] * b
          * Matrix.diagonal ![(Real.sqrt l1 : ℂ), (Real.sqrt l2 : ℂ)] := by
  rw [tau_had_eq_zero, sp_luders_of_twist_zero]

/-- **`τ` wired into `sp`, pole witness.** In the reference frame the dial reads
`τ = 1`: the product is the unit-twist member of the family. Together with
`sp_tau_had_is_luders` this is the frame-dependence pair (V9) acting on the product
itself, not just on the dial. -/
theorem sp_tau_std_is_unit_twist (l1 l2 : ℝ) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    sp l1 l2 (tau Pstd Rref) b = sp l1 l2 1 b := by
  rw [tau_std_eq_one]

/-! ## The phase cocycle (V5) and backward compatibility (V7) -/

/-- `λ₁^{1/2+it} · λ₂^{1/2+it} = (λ₁λ₂)^{1/2+it}` for `λᵢ > 0`: the exponent adds
multiplicatively (the diagonal shadow of the phase cocycle). -/
theorem gEntry_mul (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gEntry a t * gEntry b t = gEntry (a * b) t := by
  rw [gEntry, gEntry, gEntry]
  have hs : (Real.sqrt a : ℂ) * (Real.sqrt b : ℂ) = (Real.sqrt (a * b) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul ha.le]
  have hl : Real.log (a * b) = Real.log a + Real.log b := Real.log_mul (ne_of_gt ha) (ne_of_gt hb)
  calc (↑(Real.sqrt a) * Complex.exp ((↑(t * Real.log a) : ℂ) * Complex.I))
        * (↑(Real.sqrt b) * Complex.exp ((↑(t * Real.log b) : ℂ) * Complex.I))
      = (↑(Real.sqrt a) * ↑(Real.sqrt b))
        * (Complex.exp ((↑(t * Real.log a) : ℂ) * Complex.I)
            * Complex.exp ((↑(t * Real.log b) : ℂ) * Complex.I)) := by ring
    _ = (Real.sqrt (a * b) : ℂ) * Complex.exp ((↑(t * Real.log (a * b)) : ℂ) * Complex.I) := by
        rw [hs, ← Complex.exp_add]
        congr 2
        rw [hl]; push_cast; ring

/-- **Phase cocycle** (V5a): on a shared frame with equal twist, `F_a F_b = F_{ab}`
(`ζ = 1`), from which `S5` follows in the compatible case. -/
theorem phase_cocycle (a1 a2 b1 b2 t : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    Fdiag a1 a2 t * Fdiag b1 b2 t = Fdiag (a1 * b1) (a2 * b2) t := by
  rw [Fdiag, Fdiag, Fdiag, Matrix.diagonal_mul_diagonal]
  congr 1
  refine funext ?_
  rw [Fin.forall_fin_two]
  constructor <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue]
  · exact gEntry_mul a1 b1 t ha1 hb1
  · exact gEntry_mul a2 b2 t ha2 hb2

/-- `a·b` on a diagonal `b` (shared frame) is the diagonal `diag(λ_i μ_i)`. -/
theorem sp_diagonal (l1 l2 t : ℝ) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (c1 c2 : ℝ) :
    sp l1 l2 t (Matrix.diagonal ![(c1 : ℂ), (c2 : ℂ)])
      = Matrix.diagonal ![((l1 * c1 : ℝ) : ℂ), ((l2 * c2 : ℝ) : ℂ)] := by
  rw [sp, Fdiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  refine funext ?_
  rw [Fin.forall_fin_two]
  constructor <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Pi.star_apply]
  · rw [mul_right_comm, gEntry_mul_conj l1 t h1, ← Complex.ofReal_mul]
  · rw [mul_right_comm, gEntry_mul_conj l2 t h2, ← Complex.ofReal_mul]

/-- **Backward compatibility** (V7): commuting (simultaneously diagonal) effects are
compatible, `a·b = b·a`, both equal to the diagonal `diag(λ_i μ_i)`. -/
theorem compat_backward (a1 a2 b1 b2 t : ℝ)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    sp a1 a2 t (Matrix.diagonal ![(b1 : ℂ), (b2 : ℂ)])
      = sp b1 b2 t (Matrix.diagonal ![(a1 : ℂ), (a2 : ℂ)]) := by
  rw [sp_diagonal a1 a2 t ha1 ha2 b1 b2, sp_diagonal b1 b2 t hb1 hb2 a1 a2]
  congr 1
  refine funext ?_
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩ <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] <;>
    push_cast <;> ring

/-! ## Necessity and the exchange selector (`prop:n2-necessity`, `rem:n2-selection`)

The block rotation of the comparison map, as a function of the log-eigenvalue
vector `r` (`r_i = log λ_i`), is a real-linear angle vanishing on the coalescence
line `{r₀ = r₁}` (that vanishing is `lem:coalescence`, valid at any rank). We show
it factors through `r₀ − r₁ = log(λ₁/λ₂)` with a single real coefficient `t_F` per
frame, realized as a genuine `SO(2)` rotation. -/

/-- The `SO(2)` block rotation by angle `θ`: `w ↦ e^{iθ} w` on the coherence line
`W ≅ ℂ`. -/
def blockRot (θ : ℝ) (w : ℂ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I) * w

@[simp] theorem blockRot_zero (w : ℂ) : blockRot 0 w = w := by
  simp [blockRot]

/-- The block rotations compose: `R(θ+θ') = R(θ)∘R(θ')` — the `SO(2)` homomorphism
underlying the diagonal homomorphism `lem:homomorphism`. -/
theorem blockRot_add (θ θ' : ℝ) (w : ℂ) :
    blockRot (θ + θ') w = blockRot θ (blockRot θ' w) := by
  simp only [blockRot, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- **Hyperplane factorization** (the `n = 2` case of `lem:homomorphism`). A real
linear angle `Fin 2 → ℝ` (the differential of the block rotation) vanishing on the
coalescence line `{r₀ = r₁}` equals `t_F · (r₀ − r₁)` for a single real `t_F`. -/
theorem angle_factor (angle : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hcoal : ∀ r : Fin 2 → ℝ, r 0 = r 1 → angle r = 0) :
    ∃ tF : ℝ, ∀ r, angle r = tF * (r 0 - r 1) := by
  refine ⟨angle (Pi.single 0 (1 : ℝ)), fun r => ?_⟩
  have hconst : angle (fun _ : Fin 2 => (1 : ℝ)) = 0 := hcoal _ rfl
  have hdecomp : r = (r 1) • (fun _ : Fin 2 => (1 : ℝ))
      + (r 0 - r 1) • (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ) := by
    refine funext ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.isValue] <;>
      norm_num
  have key : angle r
      = r 1 * angle (fun _ : Fin 2 => (1 : ℝ)) + (r 0 - r 1) * angle (Pi.single 0 (1 : ℝ)) := by
    conv_lhs => rw [hdecomp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [key, hconst, mul_zero, zero_add, mul_comm]

/-- **Necessity at rank two** (`prop:n2-necessity`). The comparison map's block
action on the coherence line `W` is the rotation `e^{i·t_F·(r₀−r₁)}` for a single
real `t_F` per frame (`r_i = log λ_i`, so `r₀ − r₁ = log(λ₁/λ₂)`). One real
parameter per frame; there is no cross-frame constraint (`t_F` is an existential
attached to each frame's block angle). -/
theorem n2_necessity (angle : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hcoal : ∀ r : Fin 2 → ℝ, r 0 = r 1 → angle r = 0) :
    ∃ tF : ℝ, ∀ (r : Fin 2 → ℝ) (w : ℂ),
      blockRot (angle r) w = blockRot (tF * (r 0 - r 1)) w := by
  obtain ⟨tF, hfac⟩ := angle_factor angle hcoal
  exact ⟨tF, fun r w => by rw [hfac r]⟩

/-- **Rank-two selection: exchange covariance forces Lüders** (`rem:n2-selection`,
the paper's new Remark 6.2). If the block generator is exchange covariant — its
angle is invariant under interchanging the two atoms (`r ↦ r∘swap`) — then, because
the same generator is antisymmetric in `r₀ − r₁` by `n2_necessity`, the twist
`t_F = 0` on every frame and the product is Lüders (`angle ≡ 0`). This is the
generator-level form of the paper's interval / character-uniqueness kill: the
scalar factor `√(λ₁λ₂)` is swap-symmetric, so exchange covariance forces the
rotation part to equal its inverse, killing `t_F`. Consumed by Paper B. -/
theorem n2_exchange_selects_luders (angle : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hcoal : ∀ r : Fin 2 → ℝ, r 0 = r 1 → angle r = 0)
    (hexch : ∀ r : Fin 2 → ℝ, angle (fun i => r (Equiv.swap 0 1 i)) = angle r) :
    ∀ r, angle r = 0 := by
  obtain ⟨tF, hfac⟩ := angle_factor angle hcoal
  have htf : tF = 0 := by
    have hswap : (fun i => (![(1 : ℝ), 0] : Fin 2 → ℝ) (Equiv.swap 0 1 i)) = ![(0 : ℝ), 1] := by
      refine funext ?_
      rw [Fin.forall_fin_two]
      constructor <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
    have h := hexch ![(1 : ℝ), 0]
    rw [hswap, hfac, hfac] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at h
    linear_combination (-1 / 2 : ℝ) * h
  intro r
  rw [hfac, htf, zero_mul]

end MasterTheorem.RankTwo
