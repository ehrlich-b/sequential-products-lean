/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.LocalTomography
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic.Module

set_option linter.style.longLine false

/-!
# Twist normal form: retained legacy scaffold

This file and `Selection/NormalFormExistence.lean` are the **separate earlier
Lean development** described in the shipped paper's appendix (the pair-local
ansatz route). Their internal labels (`thm:normal-form`, `prop:coherence`,
`prop:closure`, `def:canonical-composite`, `def:paths`) come from an earlier
manuscript and are **not** section labels of the shipped Paper A ("A
Classification of Sequential Products on Simple Euclidean Jordan Algebras of
Rank ≥ 3").

Live content in the standalone release:

* the operator-level normal form as the interface `NormalForm` (endomorphisms
  `A, B` with `A + B = Id`, `[A,B] = 0`, action `E(x,y) = x^A y^B`), with
  `coherence_forces_luders`: reciprocity `E(x,y) = E(y,x)` forces `T = 0` and the
  Lüders value `E(x,y) = √(xy)·Id`;
* the Peirce multiplicity / local twist group facts (`SO(d)`) and the scalar
  Lüders-mixing identities;
* the `EJAType` composite-closure / self-defect facts (`rfl` on the label type);
* the Barnum–Graydon–Wilce composite table, carried as the **definition**
  `bgwComposite` with `rfl`-proved rows (`bgwComposite_table`). The former
  packaging as this file's one `axiom` (`bgw_canonical_composite`) was
  eliminated 2026-08-04 (`LEDGER.md` 2.8): it asserted only a constructible
  existence, so it recorded no falsifiable import. This file now declares
  **no custom axiom**; the BGW attribution is prose provenance (see the
  `prop:closure` section docstring).

## References

* Barnum–Graydon–Wilce 2020 (composite closure table, Table 3);
  Faraut–Korányi 1994 (Peirce multiplicities).
-/

noncomputable section

namespace TwistNormalForm

open LocalTomography

/-! ## `prop:type-table` — Peirce multiplicity and local twist group

For a simple Euclidean Jordan algebra, `d = dim V₁(p,q)` is the Peirce
off-diagonal multiplicity, and the local sequential-twist group is `SO(d)`
(Proposition, twist isotropy). The classification content — that these are the
multiplicities of the simple EJAs — is imported (Faraut–Korányi). -/

/-- Peirce off-diagonal multiplicity `d = dim V₁(p,q)` of a simple EJA type.
    Matrix families over ℝ/ℂ/ℍ give `d = 1,2,4`; the Albert algebra `d = 8`;
    a rank-two spin factor of dimension `n = k+1` gives `d = k-1 = n-2`. -/
def peirceMultiplicity : EJAType → ℕ
  | .real _    => 1
  | .complex _ => 2
  | .quatern _ => 4
  | .albert    => 8
  | .spin n    => n - 2

/-- Dimension of the local twist group `SO(d)`, namely `d(d-1)/2`.
    Real: `0` (trivial); complex: `1` (`SO(2)`); quaternionic: `6` (`SO(4)`);
    Albert: `28` (`SO(8)`). -/
def localTwistGroupDim (t : EJAType) : ℕ :=
  let d := peirceMultiplicity t
  d * (d - 1) / 2

/-- The real matrix family admits no continuous twist: `SO(1)` is trivial. -/
theorem localTwistGroupDim_real (n : ℕ) : localTwistGroupDim (.real n) = 0 := by
  simp [localTwistGroupDim, peirceMultiplicity]

/-- The complex matrix family admits exactly the one-parameter twist `SO(2)`. -/
theorem localTwistGroupDim_complex (n : ℕ) : localTwistGroupDim (.complex n) = 1 := by
  simp [localTwistGroupDim, peirceMultiplicity]

/-- The quaternionic family carries an `SO(4)` twist (dimension 6). -/
theorem localTwistGroupDim_quatern (n : ℕ) : localTwistGroupDim (.quatern n) = 6 := by
  simp [localTwistGroupDim, peirceMultiplicity]

/-- The Albert algebra carries an `SO(8)` twist (dimension 28). -/
theorem localTwistGroupDim_albert : localTwistGroupDim .albert = 28 := rfl

/-! ## Scalar shadow of `thm:normal-form` / `prop:coherence`

On the complex block the off-diagonal action is `E(x,y) = √(xy)·exp(t log(x/y) J)`;
its scalar part is the Lüders mixing `f(x,y) = √(xy)`. Two facts drive the normal
form and its reciprocity selection at the scalar level:

* multiplicativity `f(x₁x₂, y₁y₂) = f(x₁,y₁) f(x₂,y₂)` — the scalar form of
  eq. (endo-compose), `E(α₁,α₂) ∘ E(β₁,β₂) = E(α₁β₁, α₂β₂)`, which S5 imposes;
* symmetry `f(x,y) = f(y,x)` — the scalar form of the reciprocity premise
  eq. (recognition-symmetry), `E(x,y) = E(y,x)`, which forces the twist to zero.

The operator-level statements (with `E` valued in `End(W)` and twist
`T ∈ so(W)`) are Wave 2. -/

/-- The Lüders mixing scalar `f(x,y) = √(x·y)` (Paper, corrected product). -/
def mixingLuders (x y : ℝ) : ℝ := Real.sqrt (x * y)

/-- **Scalar multiplicativity** (shadow of eq. endo-compose, imposed by S5):
    `f(x₁x₂, y₁y₂) = f(x₁,y₁)·f(x₂,y₂)` for nonnegative arguments. -/
theorem mixingLuders_multiplicative {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁) :
    mixingLuders (x₁ * x₂) (y₁ * y₂) = mixingLuders x₁ y₁ * mixingLuders x₂ y₂ := by
  unfold mixingLuders
  rw [show x₁ * x₂ * (y₁ * y₂) = (x₁ * y₁) * (x₂ * y₂) by ring,
      Real.sqrt_mul (mul_nonneg hx₁ hy₁)]

/-- **Scalar reciprocity** (shadow of eq. recognition-symmetry): the Lüders
    mixing is symmetric, `f(x,y) = f(y,x)`. At the scalar level the twist is
    already absent; the operator twist `T` is what reciprocity kills in general. -/
theorem mixingLuders_symm (x y : ℝ) : mixingLuders x y = mixingLuders y x := by
  unfold mixingLuders; rw [mul_comm]

/-- **Scalar unitality** (shadow of S3): `f(1,1) = 1`. -/
theorem mixingLuders_unit : mixingLuders 1 1 = 1 := by
  unfold mixingLuders; simp

/-! ## `thm:normal-form` / `prop:coherence` — operator-level twist normal form

The operator-level interface promised above (the scalar-shadow section deferred
it to "Wave 2").  On a non-classical Peirce `1`-space `W` — the manuscript's
"arbitrary real vector space", encoded here as a finite-dimensional real normed
space with endomorphism algebra `W →L[ℝ] W = End(W)` — the block normal form of
Theorem `thm:normal-form` presents the off-diagonal action as `E(x,y) = x^A y^B`
with commuting `A, B ∈ End(W)`, `A + B = Id`, equivalently
`E(x,y) = √(xy)·exp((log x − log y)·T)` with twist `T = A − ½·Id`.

`NormalForm` is an *interface* (a `structure`): it posits the endomorphisms
`A, B`, their commuting, and the coalescence identity `A + B = Id` that
Theorem `thm:normal-form` *derives* from S2/S3/S5 and the decomposition-independent
ansatz.  Reproducing that existence derivation — the operator one-parameter-group
argument (standard theory; the underlying scalar functional equation is Aczél 1966)
together with the coalescence limit — is not formalized here.  Carrying the normal
form as a structure rather than an existence theorem is what keeps the operator
normal-form material free of any *custom* axiom; since the 2026-08-04 elimination
of the former `bgw_canonical_composite` axiom (now the proved-table definition
`bgwComposite` below), this file declares no custom axiom at all.

`coherence_forces_luders` is the reciprocity elimination of Proposition
`prop:coherence`.  The read/write reciprocity premise eq. (recognition-symmetry),
`E(x,y) = E(y,x)`, forces `A = B`, hence `T = 0`, hence the Lüders value
`E(x,y) = √(xy)·Id`.  The manuscript's own five-line algebra is reproduced: set
the second argument to the unit, obtain `x^A = x^B` for every `x`, and read off
`A = B` by differentiating the one-parameter subgroup `s ↦ exp(s·A)` at the
identity.  The single analytic input is Mathlib's `hasDerivAt_exp_smul_const`,
which gives `A` as that derivative at `0`; equal subgroups have equal generators.

Faithfulness caveats.  (i) The *existence* half of `thm:normal-form` (that
S2/S3/S5 force this shape) is assumed by taking `NormalForm` as a structure, not
proved.  (ii) The `commute` field records `[A,B]=0` for faithfulness to
`thm:normal-form`; the reciprocity elimination does not consume it, since it
collapses the block action already at `y = 1`.  (iii) The `E_normalForm` lemma
below certifies that the defining `x^A y^B` form equals the manuscript's primary
display `√(xy)·exp((log x − log y)·T)`. -/

section OperatorNormalForm

open NormedSpace

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [CompleteSpace W]

/-- `W →L[ℝ] W` is a normed ℚ-algebra by restriction of scalars from ℝ; supplied
because Mathlib's `NormedSpace.exp_add_of_commute` is stated over ℚ. -/
local instance : NormedAlgebra ℚ (W →L[ℝ] W) :=
  NormedAlgebra.restrictScalars ℚ ℝ (W →L[ℝ] W)

omit [FiniteDimensional ℝ W] [CompleteSpace W] in
/-- Operator identity `exp(c·Id) = eᶜ·Id` on `End(W)`: the exponential of a scalar
multiple of the identity is the scalar exponential.  Bridges the operator normal
form to the scalar Lüders value of `prop:coherence`. -/
theorem exp_smul_one (c : ℝ) :
    exp (c • (1 : W →L[ℝ] W)) = Real.exp c • (1 : W →L[ℝ] W) := by
  rw [(Algebra.algebraMap_eq_smul_one c).symm, ← algebraMap_exp_comm c,
      ← Real.exp_eq_exp_ℝ]
  exact Algebra.algebraMap_eq_smul_one _

/-- **`thm:normal-form` (interface).**  The block twist normal form on a
non-classical Peirce `1`-space `W`, at operator level: two commuting
endomorphisms `A, B ∈ End(W) = W →L[ℝ] W` with `A + B = Id`, the coalescence
identity eq. (coalescence).  Theorem `thm:normal-form` *derives* this shape from
S2, S3, S5 and the decomposition-independent ansatz; here it is the posited
interface whose reciprocity elimination is Proposition `prop:coherence`.  The
off-diagonal action `E` is defined below. -/
structure NormalForm (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] where
  /-- The `x`-exponent endomorphism `A = ½·Id + T` of `E(x,y) = x^A y^B`. -/
  A : W →L[ℝ] W
  /-- The `y`-exponent endomorphism `B = ½·Id − T`. -/
  B : W →L[ℝ] W
  /-- Coalescence identity `A + B = Id` (eq. (coalescence)). -/
  sum_eq_one : A + B = 1
  /-- `[A, B] = 0`: the two generators commute (`thm:normal-form`). -/
  commute : Commute A B

namespace NormalForm

variable (nf : NormalForm W)

/-- The block **twist** `T = A − ½·Id ∈ End(W)` (`thm:normal-form`).  Reciprocity
forces it to vanish (`prop:coherence`). -/
def T : W →L[ℝ] W := nf.A - (2⁻¹ : ℝ) • 1

/-- Off-diagonal action, `x^A y^B` presentation of the normal form:
`E(x,y) = exp(log x · A) · exp(log y · B)` (`thm:normal-form`, eq. (normal-form)). -/
noncomputable def E (x y : ℝ) : W →L[ℝ] W :=
  exp (Real.log x • nf.A) * exp (Real.log y • nf.B)

/-- Read/write **reciprocity** premise eq. (recognition-symmetry): the block
action is symmetric under interchange of the two atoms, `E(x,y) = E(y,x)` for all
positive eigenvalues. -/
def Reciprocity : Prop := ∀ x y : ℝ, 0 < x → 0 < y → nf.E x y = nf.E y x

omit [CompleteSpace W] in
@[simp] theorem E_right_one (x : ℝ) : nf.E x 1 = exp (Real.log x • nf.A) := by
  simp [E, exp_zero]

omit [CompleteSpace W] in
@[simp] theorem E_left_one (x : ℝ) : nf.E 1 x = exp (Real.log x • nf.B) := by
  simp [E, exp_zero]

/-- Factor the `x`-exponent around the twist: `x^A = exp(r·A) = eʳ⸍²·exp(r·T)`
with `r = log x`, using `A = ½·Id + T` (`thm:normal-form`). -/
theorem exp_smul_A (r : ℝ) :
    exp (r • nf.A) = Real.exp (r / 2) • exp (r • nf.T) := by
  have hsplit : r • nf.A = (r / 2) • (1 : W →L[ℝ] W) + r • nf.T := by
    simp only [T]; module
  rw [hsplit, exp_add_of_commute ((Commute.one_left (r • nf.T)).smul_left (r / 2)),
      exp_smul_one, smul_mul_assoc, one_mul]

/-- Factor the `y`-exponent around the twist: `y^B = exp(r·B) = eʳ⸍²·exp((−r)·T)`
with `r = log y`, using `B = ½·Id − T` (`thm:normal-form`). -/
theorem exp_smul_B (r : ℝ) :
    exp (r • nf.B) = Real.exp (r / 2) • exp ((-r) • nf.T) := by
  have hsplit : r • nf.B = (r / 2) • (1 : W →L[ℝ] W) + (-r) • nf.T := by
    have hb : nf.B = 1 - nf.A := by rw [← nf.sum_eq_one]; abel
    rw [hb]; simp only [T]; module
  rw [hsplit, exp_add_of_commute ((Commute.one_left ((-r) • nf.T)).smul_left (r / 2)),
      exp_smul_one, smul_mul_assoc, one_mul]

/-- **`thm:normal-form`, equivalence of presentations (eq. (normal-form)).**  The
defining `x^A y^B` action equals the manuscript's primary display
`E(x,y) = √(xy)·exp((log x − log y)·T)` with twist `T = A − ½·Id`.  This certifies
that the Lean encoding of `E` and the boxed normal form of `thm:normal-form`
coincide. -/
theorem E_normalForm {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    nf.E x y = Real.sqrt (x * y) • exp ((Real.log x - Real.log y) • nf.T) := by
  have hsqrt : Real.exp (Real.log x / 2) * Real.exp (Real.log y / 2)
      = Real.sqrt (x * y) := by
    rw [← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (mul_pos hx hy),
        Real.log_mul hx.ne' hy.ne']
    congr 1; ring
  have htwist : exp (Real.log x • nf.T) * exp ((-Real.log y) • nf.T)
      = exp ((Real.log x - Real.log y) • nf.T) := by
    rw [← exp_add_of_commute
      (((Commute.refl nf.T).smul_left (Real.log x)).smul_right (-Real.log y))]
    congr 1; module
  simp only [E]
  rw [nf.exp_smul_A, nf.exp_smul_B, smul_mul_smul_comm, htwist, hsqrt]

omit [CompleteSpace W] in
/-- Reciprocity, read at `y = 1` over all `x > 0`, equates the two one-parameter
subgroups `s ↦ exp(s·A)` and `s ↦ exp(s·B)` — the manuscript's `x^A = x^B`. -/
theorem exp_smul_eq_of_reciprocity (h : nf.Reciprocity) (s : ℝ) :
    exp (s • nf.A) = exp (s • nf.B) := by
  have hx : (0 : ℝ) < Real.exp s := Real.exp_pos s
  have hrec := h (Real.exp s) 1 hx one_pos
  rwa [E_right_one, E_left_one, Real.log_exp] at hrec

/-- **`prop:coherence`, generator step.**  Reciprocity forces `A = B`: the two
one-parameter subgroups agree, so their generators — their derivatives at `0`,
computed by `hasDerivAt_exp_smul_const` — agree. -/
theorem A_eq_B (h : nf.Reciprocity) : nf.A = nf.B := by
  have key : (fun s : ℝ => exp (s • nf.A)) = fun s : ℝ => exp (s • nf.B) :=
    funext (nf.exp_smul_eq_of_reciprocity h)
  have hA : HasDerivAt (fun s : ℝ => exp (s • nf.A)) nf.A 0 := by
    simpa [exp_zero] using hasDerivAt_exp_smul_const nf.A (0 : ℝ)
  have hB : HasDerivAt (fun s : ℝ => exp (s • nf.A)) nf.B 0 := by
    rw [key]; simpa [exp_zero] using hasDerivAt_exp_smul_const nf.B (0 : ℝ)
  exact hA.unique hB

/-- With reciprocity's `A = B` and coalescence `A + B = Id`, the exponent equals
`½·Id` (`prop:coherence`). -/
theorem A_eq_half (h : nf.Reciprocity) :
    nf.A = (2⁻¹ : ℝ) • (1 : W →L[ℝ] W) := by
  have h2 : (2 : ℝ) • nf.A = 1 := by
    have hsum := nf.sum_eq_one
    rw [← nf.A_eq_B h, ← two_smul ℝ] at hsum
    exact hsum
  have e : nf.A = (2⁻¹ : ℝ) • ((2 : ℝ) • nf.A) := by
    rw [smul_smul, show (2⁻¹ * 2 : ℝ) = 1 by norm_num, one_smul]
  rw [e, h2]

theorem B_eq_half (h : nf.Reciprocity) :
    nf.B = (2⁻¹ : ℝ) • (1 : W →L[ℝ] W) := by
  rw [← nf.A_eq_B h]; exact nf.A_eq_half h

/-- **`prop:coherence`, twist step.**  The twist `T = A − ½·Id` vanishes. -/
theorem T_eq_zero (h : nf.Reciprocity) : nf.T = 0 := by
  rw [T, nf.A_eq_half h, sub_self]

/-- **`prop:coherence`, Lüders value (`eq:faithful-f`).**  Under reciprocity the
off-diagonal action is scalar multiplication by `√(xy)`: `E(x,y) = √(xy)·Id`. -/
theorem E_luders (h : nf.Reciprocity) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    nf.E x y = Real.sqrt (x * y) • (1 : W →L[ℝ] W) := by
  have hx2 : Real.exp (Real.log x * 2⁻¹) = Real.sqrt x := by
    rw [← Real.rpow_def_of_pos hx, Real.sqrt_eq_rpow]; congr 1; norm_num
  have hy2 : Real.exp (Real.log y * 2⁻¹) = Real.sqrt y := by
    rw [← Real.rpow_def_of_pos hy, Real.sqrt_eq_rpow]; congr 1; norm_num
  simp only [E]
  rw [nf.A_eq_half h, nf.B_eq_half h, smul_smul, smul_smul, exp_smul_one,
      exp_smul_one, hx2, hy2, smul_mul_smul_comm, one_mul, ← Real.sqrt_mul hx.le]

/-- **`prop:coherence` (reciprocity elimination).**  On a non-classical block the
reciprocity premise eq. (recognition-symmetry) forces the twist to vanish and
pins the Lüders value: `T = 0` and `E(x,y) = √(xy)·Id`. -/
theorem coherence_forces_luders (h : nf.Reciprocity) :
    nf.T = 0 ∧ ∀ x y : ℝ, 0 < x → 0 < y →
      nf.E x y = Real.sqrt (x * y) • (1 : W →L[ℝ] W) :=
  ⟨nf.T_eq_zero h, fun _ _ hx hy => nf.E_luders h hx hy⟩

end NormalForm

end OperatorNormalForm

/-! ## `prop:closure` — the Barnum–Graydon–Wilce composition table

`prop:closure` records, within the canonical standard-embedding category
(`def:canonical-composite`, the composite `⊙c` of Barnum–Graydon–Wilce 2020),
the pairwise composites of the three simple matrix families
`R_n = Mₙ(ℝ)ˢᵃ`, `C_n = Mₙ(ℂ)ˢᵃ`, `H_n = Mₙ(ℍ)ˢᵃ`:

```
  ⊙c │ R_n     C_n      H_n
  ───┼───────────────────────
  R_m│ R_{mn}  C_{mn}   H_{mn}
  C_m│ C_{mn}  C_{mn}   C_{2mn}
  H_m│ H_{mn}  C_{2mn}  R_{4mn}
```

Every entry is a Barnum–Graydon–Wilce 2020 result at matrix ranks `m, n ≥ 2`
(Table 3 there) — the division-ring tensor law (`ℝ⊗D = D`, `ℂ⊗ℂ = ℂ` on the
connected/canonical column rather than the universal `ℂ⊕ℂ`, `ℂ⊗ℍ = M₂(ℂ)`,
`ℍ⊗ℍ = M₄(ℝ)`). At the degenerate indices `m` or `n ∈ {0,1}` the row is a
formal label value, not a BGW result; those instances are consumed nowhere and
lie outside the `master_chain` closure. The table is carried as the
**definition** `bgwComposite`, with the nine matrix rows proved by `rfl`
(`bgwComposite_table`). The former packaging as a single `axiom`
(`bgw_canonical_composite`, eliminated 2026-08-04, campaign `LEDGER.md` 2.8)
asserted only the *existence* of an operation with these nine values — a
constructible statement that cannot be false — so it padded the axiom ledger
without recording any falsifiable import. What IS imported from
Barnum–Graydon–Wilce 2020 is the **interpretation**: that this table is the
composition table of their canonical standard-embedding composite `⊙c`
(`def:canonical-composite`). That identification lives here and in
`THEOREM-MAP.md` as prose provenance — exactly where it lived before, since
`#print axioms` never checked fidelity to the source either. Non-matrix rows
(spin, Albert) carry the junk-total convention `.real 0`, consumed nowhere,
mirroring the manuscript's partial/undefined composite — the same epistemic
status as the former axiom's opaque unpinned values, but visibly junk rather
than opaquely junk.

The diagonal self-square flow `τ ↦ τ⋆τ` (`def:paths`) then reads off the
table as `ℝ↦ℝ`, `ℂ↦ℂ`, `ℍ↦ℝ`: the real and complex families are closed under
strict self-composition, and a quaternionic system defects to the real family
(`R_{4n²}`, since `ℍ⊗ℍ = M₄(ℝ)`) at its first self-square, so no homogeneous
quaternionic tower of depth ≥ 1 exists. -/

/-- **`prop:closure` (table definition; interpretation cited to
Barnum–Graydon–Wilce 2020).** The canonical standard-embedding composite `⊙c`
on `EJAType` (`def:canonical-composite`), as an explicit table. The nine
matrix-row values are the content of `prop:closure`; their agreement with the
BGW canonical composite is a cited *interpretation* (see the section
docstring), not a Lean-checked fact — exactly as when this was carried by the
(eliminated) `bgw_canonical_composite` axiom. Non-matrix rows are the
junk-total convention `.real 0`, consumed nowhere. -/
def bgwComposite : EJAType → EJAType → EJAType
  | .real m,    .real n    => .real (m * n)
  | .real m,    .complex n => .complex (m * n)
  | .real m,    .quatern n => .quatern (m * n)
  | .complex m, .real n    => .complex (m * n)
  | .complex m, .complex n => .complex (m * n)
  | .complex m, .quatern n => .complex (2 * m * n)
  | .quatern m, .real n    => .quatern (m * n)
  | .quatern m, .complex n => .complex (2 * m * n)
  | .quatern m, .quatern n => .real (4 * m * n)
  | _,          _          => .real 0

/-- **`prop:closure`, full table (PROVED, `rfl` per row, no axiom).** The nine
    R/C/H entries of the canonical composition table. Formerly the `.property`
    of the eliminated `bgw_canonical_composite` axiom; the BGW-2020 citation
    now attaches to the table's interpretation, not to a Lean assumption. -/
theorem bgwComposite_table :
    (∀ m n : ℕ, bgwComposite (.real m)    (.real n)    = .real (m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.real m)    (.complex n) = .complex (m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.real m)    (.quatern n) = .quatern (m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.complex m) (.real n)    = .complex (m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.complex m) (.complex n) = .complex (m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.complex m) (.quatern n) = .complex (2 * m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.quatern m) (.real n)    = .quatern (m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.quatern m) (.complex n) = .complex (2 * m * n)) ∧
    (∀ m n : ℕ, bgwComposite (.quatern m) (.quatern n) = .real (4 * m * n)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Table row `R_m ⊙ R_n = R_{mn}` (Barnum–Graydon–Wilce 2020). -/
theorem bgwComposite_real_real (m n : ℕ) :
    bgwComposite (.real m) (.real n) = .real (m * n) := bgwComposite_table.1 m n

/-- Table row `R_m ⊙ C_n = C_{mn}` (Barnum–Graydon–Wilce 2020). -/
theorem bgwComposite_real_complex (m n : ℕ) :
    bgwComposite (.real m) (.complex n) = .complex (m * n) := bgwComposite_table.2.1 m n

/-- Table row `R_m ⊙ H_n = H_{mn}` (Barnum–Graydon–Wilce 2020). -/
theorem bgwComposite_real_quatern (m n : ℕ) :
    bgwComposite (.real m) (.quatern n) = .quatern (m * n) := bgwComposite_table.2.2.1 m n

/-- Table row `C_m ⊙ R_n = C_{mn}` (Barnum–Graydon–Wilce 2020). -/
theorem bgwComposite_complex_real (m n : ℕ) :
    bgwComposite (.complex m) (.real n) = .complex (m * n) := bgwComposite_table.2.2.2.1 m n

/-- Table row `C_m ⊙ C_n = C_{mn}` on the canonical column (Barnum–Graydon–Wilce
    2020); the universal composite `C_{mn} ⊕ C_{mn}` is a separate convention. -/
theorem bgwComposite_complex_complex (m n : ℕ) :
    bgwComposite (.complex m) (.complex n) = .complex (m * n) := bgwComposite_table.2.2.2.2.1 m n

/-- Table row `C_m ⊙ H_n = C_{2mn}` (Barnum–Graydon–Wilce 2020; `ℂ⊗ℍ = M₂(ℂ)`). -/
theorem bgwComposite_complex_quatern (m n : ℕ) :
    bgwComposite (.complex m) (.quatern n) = .complex (2 * m * n) :=
  bgwComposite_table.2.2.2.2.2.1 m n

/-- Table row `H_m ⊙ R_n = H_{mn}` (Barnum–Graydon–Wilce 2020). -/
theorem bgwComposite_quatern_real (m n : ℕ) :
    bgwComposite (.quatern m) (.real n) = .quatern (m * n) := bgwComposite_table.2.2.2.2.2.2.1 m n

/-- Table row `H_m ⊙ C_n = C_{2mn}` (Barnum–Graydon–Wilce 2020; `ℍ⊗ℂ = M₂(ℂ)`). -/
theorem bgwComposite_quatern_complex (m n : ℕ) :
    bgwComposite (.quatern m) (.complex n) = .complex (2 * m * n) :=
  bgwComposite_table.2.2.2.2.2.2.2.1 m n

/-- Table row `H_m ⊙ H_n = R_{4mn}` (Barnum–Graydon–Wilce 2020; `ℍ⊗ℍ = M₄(ℝ)`).
    This is the quaternionic self-defect: the composite is real, not
    quaternionic. -/
theorem bgwComposite_quatern_quatern (m n : ℕ) :
    bgwComposite (.quatern m) (.quatern n) = .real (4 * m * n) :=
  bgwComposite_table.2.2.2.2.2.2.2.2 m n

/-! ### Self-square flow (`prop:closure` diagonal, `def:paths`) -/

/-- **Self-square, real (`ℝ↦ℝ`).** `R_n ⊙ R_n = R_{n²}`: the real family is
    closed under strict self-composition. -/
theorem bgwComposite_self_square_real (n : ℕ) :
    bgwComposite (.real n) (.real n) = .real (n * n) := bgwComposite_real_real n n

/-- **Self-square, complex (`ℂ↦ℂ`).** `C_n ⊙ C_n = C_{n²}`: the complex family
    is closed under strict self-composition. -/
theorem bgwComposite_self_square_complex (n : ℕ) :
    bgwComposite (.complex n) (.complex n) = .complex (n * n) := bgwComposite_complex_complex n n

/-- **Self-square, quaternionic (`ℍ↦ℝ`).** `H_n ⊙ H_n = R_{4n²}`: the
    quaternionic family defects to the real family at its first self-square, so
    no homogeneous quaternionic tower of depth ≥ 1 exists. -/
theorem bgwComposite_self_square_quatern (n : ℕ) :
    bgwComposite (.quatern n) (.quatern n) = .real (4 * n * n) := bgwComposite_quatern_quatern n n

/-- **`prop:closure`, self-square flow.** The diagonal of the table:
    `ℝ↦ℝ`, `ℂ↦ℂ`, `ℍ↦ℝ`. -/
theorem self_square_flow (n : ℕ) :
    bgwComposite (.real n) (.real n) = .real (n * n) ∧
    bgwComposite (.complex n) (.complex n) = .complex (n * n) ∧
    bgwComposite (.quatern n) (.quatern n) = .real (4 * n * n) :=
  ⟨bgwComposite_self_square_real n, bgwComposite_self_square_complex n,
   bgwComposite_self_square_quatern n⟩

/-- The canonical self-square type `τ ↦ τ⋆τ` (`def:paths`) for the matrix
    families, read off the `bgwComposite` diagonal: `ℝ↦ℝ`, `ℂ↦ℂ`, `ℍ↦ℝ`.
    Non-matrix rows are left fixed here. -/
def selfSquareType : EJAType → EJAType
  | .real n    => .real (n * n)
  | .complex n => .complex (n * n)
  | .quatern n => .real (4 * n * n)
  | t          => t

/-- The real matrix family is closed under strict self-composition. -/
theorem real_self_square (n : ℕ) : selfSquareType (.real n) = .real (n * n) := rfl

/-- The complex matrix family is closed under strict self-composition. -/
theorem complex_self_square (n : ℕ) : selfSquareType (.complex n) = .complex (n * n) := rfl

/-- The quaternionic family defects to the real family (`R_{4n²}`) at its first
    self-square. -/
theorem quatern_self_defects (n : ℕ) : selfSquareType (.quatern n) = .real (4 * n * n) := rfl

/-- The concrete self-square function `selfSquareType` agrees with the imported
    Barnum–Graydon–Wilce diagonal on all three matrix families: a consistency
    check tying the definitional shadow to the imported table. -/
theorem selfSquareType_eq_bgwComposite (t : EJAType)
    (h : ∃ n, t = .real n ∨ t = .complex n ∨ t = .quatern n) :
    selfSquareType t = bgwComposite t t := by
  obtain ⟨n, hr | hc | hq⟩ := h
  · subst hr; exact (bgwComposite_self_square_real n).symm
  · subst hc; exact (bgwComposite_self_square_complex n).symm
  · subst hq; exact (bgwComposite_self_square_quatern n).symm

end TwistNormalForm
