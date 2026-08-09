/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.OrderUnitSpace
import RadicalRelativity.Vendor.HermitianMat.Order
import RadicalRelativity.Vendor.HermitianMat.Inner
import RadicalRelativity.Vendor.HermitianMat.CFC

set_option linter.style.longLine false

/-!
# H_n(𝕜) as an order unit space  (campaign LEDGER 1.1)

This file puts the concrete carrier `HermitianMat n 𝕜` (vendored physlib island,
`RadicalRelativity/Vendor/`) underneath the abstract `OrderUnitSpace` interface of
the master chain, and defines the order-unit norm.

## Main results

* `HermitianMat.le_norm_smul_one` / `neg_norm_smul_one_le` — order-unit boundedness
  with the explicit witness `r = ‖a‖` (Frobenius), both sides.
* `HermitianMat.le_zero_of_forall_le_smul_one` — the **full Archimedean property**
  over ℂ (the abstract class's `archimedean` field is only order-unit boundedness;
  this is the genuinely stronger statement, recorded here concretely).
* `instance : OrderUnitSpace (HermitianMat n 𝕜)` — unit `1`, Loewner order,
  Frobenius norm.  Under this instance `OrderUnitSpace.IsEffect a` is
  *definitionally* `0 ≤ a ∧ a ≤ 1` (`isEffect_iff`), so the vendored effect-interval
  facts (`unitInterval_IsCompact`) apply to the abstract effect space verbatim.
* `HermitianMat.ouNorm` — the order-unit norm `inf {t ≥ 0 | -t•1 ≤ a ≤ t•1}` as an
  **unbundled def**.  The `Norm` instance slot is deliberately left to the vendored
  Frobenius norm; introducing a second bundled norm would create an instance clash
  (LEDGER 1.1).  Attainment of the infimum (`neg_ouNorm_smul_one_le`,
  `le_ouNorm_smul_one`) comes from closedness of the PSD cone
  (`HermitianMat.isClosed_nonneg`, vendored), not from eigenvalue bookkeeping,
  so everything except the Archimedean statement and the eigenvalue bounds is
  uniform in `RCLike 𝕜`.
* `HermitianMat.eigenvalues_mem_Icc_of_effect` — effects have spectrum in `[0,1]` (ℂ).

The norm-equivalence discharge `ouNorm ≍ ‖·‖` (THEOREM-MAP's S2 literal-fidelity
caveat, LEDGER 1.4) is the final section: `ouNorm_le_norm` and
`norm_le_sqrt_card_mul_ouNorm` give the two-sided comparison
`ouNorm ≤ ‖·‖ ≤ √(card n) · ouNorm`.
-/

noncomputable section

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Order-unit boundedness -/

/-- Every Hermitian matrix is dominated by its (Frobenius) norm times the identity. -/
theorem le_norm_smul_one (a : HermitianMat n 𝕜) : a ≤ ‖a‖ • 1 :=
  lt_smul_of_norm_lt le_rfl

/-- Lower order-unit bound: `-(‖a‖ • 1) ≤ a`. -/
theorem neg_norm_smul_one_le (a : HermitianMat n 𝕜) : -(‖a‖ • 1) ≤ a :=
  neg_le.mp (lt_smul_of_norm_lt (norm_neg a).le)

/-- The order-unit property of `1` in `H_n(𝕜)`: every element is dominated by a
nonnegative multiple of the unit. -/
theorem exists_nonneg_le_smul_one (a : HermitianMat n 𝕜) :
    ∃ r : ℝ, 0 ≤ r ∧ a ≤ r • 1 :=
  ⟨‖a‖, norm_nonneg a, le_norm_smul_one a⟩

/-- **The full Archimedean property** of the Loewner order on `H_n(ℂ)`: an element
below every positive multiple of the unit is nonpositive.  (The `archimedean` field
of `OrderUnitSpace` is only order-unit boundedness; this is the stronger condition,
proved here via the eigenvalue characterization of `a ≤ ε • 1`.) -/
theorem le_zero_of_forall_le_smul_one {a : HermitianMat n 𝕜}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ε • 1) : a ≤ 0 := by
  have hev : ∀ i, a.H.eigenvalues i ≤ 0 := by
    intro i
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := le_smul_one_imp_eigenvalues_le (A := a) ε (h ε hε) i
    linarith
  have h0 := eigenvalues_le_imp_le_smul_one (A := a) 0 hev
  rwa [show (0 : ℝ) • (1 : HermitianMat n 𝕜) = 0 from zero_smul ℝ 1] at h0

/-! ### The `OrderUnitSpace` instance

The parent structures (`NormedAddCommGroup`, `NormedSpace ℝ`, `PartialOrder`) are
filled by the existing vendored instances, so no second normed or order structure
is created. -/

instance : OrderUnitSpace (HermitianMat n 𝕜) where
  add_le_add_left _ _ h _ := add_le_add le_rfl h
  ousUnit := 1
  smul_nonneg_mono _ hr := fun h => smul_le_smul_of_nonneg_left h hr
  ousUnit_nonneg := zero_le_one
  archimedean := exists_nonneg_le_smul_one

@[simp]
theorem ousUnit_eq_one : (OrderUnitSpace.ousUnit : HermitianMat n 𝕜) = 1 := rfl

/-- On the concrete carrier, the abstract effect predicate is definitionally the
unit interval of the Loewner order. -/
theorem isEffect_iff {a : HermitianMat n 𝕜} :
    OrderUnitSpace.IsEffect a ↔ 0 ≤ a ∧ a ≤ 1 :=
  Iff.rfl

/-- The effect space of `H_n(𝕜)` is compact (vendored
`HermitianMat.unitInterval_IsCompact`, restated through the abstract predicate). -/
theorem isCompact_setOf_isEffect :
    IsCompact {a : HermitianMat n 𝕜 | OrderUnitSpace.IsEffect a} :=
  unitInterval_IsCompact

/-- Effects have eigenvalues in `[0,1]` (ℂ). -/
theorem eigenvalues_mem_Icc_of_effect {a : HermitianMat n 𝕜}
    (h0 : 0 ≤ a) (h1 : a ≤ 1) (i : n) :
    a.H.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨eigenvalues_nonneg h0 i,
    le_smul_one_imp_eigenvalues_le (A := a) 1
      (by rw [one_smul]; exact h1) i⟩

/-! ### The order-unit norm (unbundled) -/

/-- The **order-unit norm** on `H_n(𝕜)`:
`ouNorm a = inf {t | 0 ≤ t ∧ -(t • 1) ≤ a ∧ a ≤ t • 1}`.

Deliberately an unbundled `def`, not a `Norm` instance: the carrier's `Norm` slot
is occupied by the Frobenius norm (which feeds the inner-product and `CompleteSpace`
structure), and a competing bundled norm would make instance resolution ambiguous.
The two-sided comparison with the carried norm (`ouNorm_le_norm`,
`norm_le_sqrt_card_mul_ouNorm`) is proved below. -/
def ouNorm (a : HermitianMat n 𝕜) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ -(t • 1) ≤ a ∧ a ≤ t • 1}

theorem norm_mem_ouNorm_set (a : HermitianMat n 𝕜) :
    ‖a‖ ∈ {t : ℝ | 0 ≤ t ∧ -(t • 1) ≤ a ∧ a ≤ t • 1} :=
  ⟨norm_nonneg a, neg_norm_smul_one_le a, le_norm_smul_one a⟩

theorem bddBelow_ouNorm_set (a : HermitianMat n 𝕜) :
    BddBelow {t : ℝ | 0 ≤ t ∧ -(t • 1) ≤ a ∧ a ≤ t • 1} :=
  ⟨0, fun _ ht => ht.1⟩

/-- The defining set of the order-unit norm is closed, via closedness of the PSD
cone (`isClosed_nonneg`) — no eigenvalue machinery, uniform in `𝕜`. -/
theorem isClosed_ouNorm_set (a : HermitianMat n 𝕜) :
    IsClosed {t : ℝ | 0 ≤ t ∧ -(t • 1) ≤ a ∧ a ≤ t • 1} := by
  have h2 : IsClosed {t : ℝ | -(t • (1 : HermitianMat n 𝕜)) ≤ a} :=
    IsClosed.preimage (f := fun t : ℝ => -(t • (1 : HermitianMat n 𝕜)))
      (by fun_prop) (isClosed_Iic (a := a))
  have h3 : IsClosed {t : ℝ | a ≤ t • (1 : HermitianMat n 𝕜)} :=
    IsClosed.preimage (f := fun t : ℝ => t • (1 : HermitianMat n 𝕜))
      (by fun_prop) (isClosed_Ici (a := a))
  exact isClosed_Ici.inter (h2.inter h3)

/-- The infimum defining the order-unit norm is attained. -/
theorem ouNorm_mem (a : HermitianMat n 𝕜) :
    ouNorm a ∈ {t : ℝ | 0 ≤ t ∧ -(t • 1) ≤ a ∧ a ≤ t • 1} :=
  (isClosed_ouNorm_set a).csInf_mem ⟨‖a‖, norm_mem_ouNorm_set a⟩ (bddBelow_ouNorm_set a)

theorem ouNorm_nonneg (a : HermitianMat n 𝕜) : 0 ≤ ouNorm a :=
  (ouNorm_mem a).1

/-- Attained lower bound: `-(ouNorm a • 1) ≤ a`. -/
theorem neg_ouNorm_smul_one_le (a : HermitianMat n 𝕜) : -(ouNorm a • 1) ≤ a :=
  (ouNorm_mem a).2.1

/-- Attained upper bound: `a ≤ ouNorm a • 1`. -/
theorem le_ouNorm_smul_one (a : HermitianMat n 𝕜) : a ≤ ouNorm a • 1 :=
  (ouNorm_mem a).2.2

/-- Minimality: the order-unit norm is below any nonnegative two-sided bound. -/
theorem ouNorm_le {a : HermitianMat n 𝕜} {t : ℝ}
    (ht : 0 ≤ t) (h₁ : -(t • 1) ≤ a) (h₂ : a ≤ t • 1) : ouNorm a ≤ t :=
  csInf_le (bddBelow_ouNorm_set a) ⟨ht, h₁, h₂⟩

/-- The order-unit norm is dominated by the Frobenius norm.  (The reverse
comparison is `norm_le_sqrt_card_mul_ouNorm` below.) -/
theorem ouNorm_le_norm (a : HermitianMat n 𝕜) : ouNorm a ≤ ‖a‖ :=
  ouNorm_le (norm_nonneg a) (neg_norm_smul_one_le a) (le_norm_smul_one a)

@[simp]
theorem ouNorm_zero : ouNorm (0 : HermitianMat n 𝕜) = 0 :=
  le_antisymm (ouNorm_le le_rfl (by simp) (by simp)) (ouNorm_nonneg 0)

theorem ouNorm_eq_zero_iff {a : HermitianMat n 𝕜} : ouNorm a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h₁ := le_ouNorm_smul_one a
    have h₂ := neg_ouNorm_smul_one_le a
    rw [h, zero_smul] at h₁ h₂
    rw [neg_zero] at h₂
    exact le_antisymm h₁ h₂
  · rintro rfl
    exact ouNorm_zero

theorem ouNorm_neg (a : HermitianMat n 𝕜) : ouNorm (-a) = ouNorm a := by
  have key : ∀ b : HermitianMat n 𝕜, ouNorm (-b) ≤ ouNorm b := fun b =>
    ouNorm_le (ouNorm_nonneg b)
      (neg_le_neg (le_ouNorm_smul_one b))
      (neg_le.mpr (neg_ouNorm_smul_one_le b))
  exact le_antisymm (key a) (by simpa using key (-a))

/-- Triangle inequality for the order-unit norm. -/
theorem ouNorm_add_le (a b : HermitianMat n 𝕜) :
    ouNorm (a + b) ≤ ouNorm a + ouNorm b := by
  refine ouNorm_le (add_nonneg (ouNorm_nonneg a) (ouNorm_nonneg b)) ?_ ?_
  · rw [add_smul, neg_add]
    exact add_le_add (neg_ouNorm_smul_one_le a) (neg_ouNorm_smul_one_le b)
  · rw [add_smul]
    exact add_le_add (le_ouNorm_smul_one a) (le_ouNorm_smul_one b)

/-- Effects have order-unit norm at most one. -/
theorem ouNorm_le_one_of_effect {a : HermitianMat n 𝕜}
    (h0 : 0 ≤ a) (h1 : a ≤ 1) : ouNorm a ≤ 1 :=
  ouNorm_le zero_le_one
    (le_trans (by simpa using neg_nonpos.mpr (zero_le_one (α := HermitianMat n 𝕜))) h0)
    (by simpa using h1)

/-! ### Norm comparison (LEDGER 1.4): `ouNorm ≤ ‖·‖ ≤ √(card n) · ouNorm`

Together with `ouNorm_le_norm` this identifies the order-unit and carried
(Frobenius) topologies on the finite-dimensional carrier — the content of
THEOREM-MAP's (S2) literal-fidelity caveat. -/

/-- Every eigenvalue is bounded by the order-unit norm in absolute value.  The
lower bound goes through `-a` and the eigenvalue permutation of `cfc_eigenvalues`. -/
theorem abs_eigenvalues_le_ouNorm (a : HermitianMat n 𝕜) (i : n) :
    |a.H.eigenvalues i| ≤ ouNorm a := by
  rw [abs_le]
  constructor
  · have hneg : -a ≤ ouNorm a • 1 := neg_le.mpr (neg_ouNorm_smul_one_le a)
    have hcfc : a.cfc (fun x => -x) = -a := by
      have h := cfc_neg_apply (A := a) (f := id)
      simpa using h
    obtain ⟨e, he⟩ := cfc_eigenvalues (fun x => -x) a
    rw [hcfc] at he
    have h2 := le_smul_one_imp_eigenvalues_le (-a) (ouNorm a) hneg (e.symm i)
    rw [he] at h2
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h2
    linarith
  · exact le_smul_one_imp_eigenvalues_le a (ouNorm a) (le_ouNorm_smul_one a) i

/-- **The reverse norm comparison**: the carried (Frobenius) norm is at most
`√(card n)` times the order-unit norm. -/
theorem norm_le_sqrt_card_mul_ouNorm (a : HermitianMat n 𝕜) :
    ‖a‖ ≤ Real.sqrt (Fintype.card n) * ouNorm a := by
  have hsq : ‖a‖ ^ 2 ≤ (Fintype.card n : ℝ) * ouNorm a ^ 2 := by
    rw [norm_eq_sum_eigenvalues_sq]
    calc ∑ i, (a.H.eigenvalues i) ^ 2
        ≤ ∑ _i : n, ouNorm a ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_eigenvalues_le_ouNorm a i) 2
      _ = (Fintype.card n : ℝ) * ouNorm a ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  calc ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
    _ ≤ Real.sqrt ((Fintype.card n : ℝ) * ouNorm a ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (Fintype.card n) * ouNorm a := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (ouNorm_nonneg a)]

/-! ## The carrier is Archimedean

★★ **New 2026-08-09 (ARC-7 block 7.3), and it retires a real caveat.**

`OrderUnitSpace`'s own `archimedean` field is order-unit *boundedness* only.  The genuine
Archimedean squeeze — `(∀ ε > 0, x ≤ ε•𝟙) ⟹ x ≤ 0` — is supplied separately as the `Prop`
`OrderUnitSpace.IsArchimedean`, because putting it in the class would change
`SequentialProductCore.mk`'s printed constructor type, which `AxiomAudit.lean` Layer 5 freezes.

ARC-6 proved `lem:homog`(ii) and `lem:cone-ext` at abstract order-unit-space generality **carrying
that `Prop` as a hypothesis**, and defended the FORMALIZED labels on the ground that the squeeze is
part of the *definition* of the article's order unit space rather than a located stand-in for a
cited result.  That defense is sound but it left an unpleasant gap: nothing in the tree exhibited a
*single* carrier satisfying it, so those results applied, as far as the machine knew, to nothing.

This closes that.  `H_n(𝕜)` — the paper's own carrier for the real and complex rows — satisfies
`IsArchimedean`, so the abstract tier is instantiated where the paper uses it and the hypothesis is
**discharged rather than assumed**.  The proof is the quadratic-form characterization
(`le_iff_mulVec_le`) plus one real ε-argument: no spectral theorem, no topology, no closedness of
the positive cone. -/

section Archimedean

open ComplexOrder
open scoped _root_.Matrix

omit [DecidableEq n] in
theorem quadForm_zero (v : n → 𝕜) :
    star v ⬝ᵥ ((0 : HermitianMat n 𝕜).mat) *ᵥ v = 0 := by simp

theorem quadForm_smul_one (v : n → 𝕜) (ε : ℝ) :
    star v ⬝ᵥ ((ε • (1 : HermitianMat n 𝕜)).mat) *ᵥ v = (ε : 𝕜) * (star v ⬝ᵥ v) := by
  rw [HermitianMat.mat_smul, HermitianMat.mat_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, RCLike.real_smul_eq_coe_mul]

omit [DecidableEq n] in
theorem quadForm_nonneg (v : n → 𝕜) : (0 : 𝕜) ≤ star v ⬝ᵥ v := by
  rw [dotProduct]
  refine Finset.sum_nonneg (fun i _ => ?_)
  simpa [Pi.star_apply] using star_mul_self_nonneg (v i)

/-- **`H_n(𝕜)` is Archimedean.**  If `x ≤ ε•𝟙` for every `ε > 0` then `x ≤ 0`.

Read through `le_iff_mulVec_le` this is a statement about one real number per vector: the
quadratic form `⟪v, xv⟫` is below `ε⟪v,v⟫` for every `ε > 0`, hence below `0`.  The imaginary part
is pinned by the same inequality at `ε = 1`. -/
theorem isArchimedean : OrderUnitSpace.IsArchimedean (HermitianMat n 𝕜) := by
  intro x hx
  simp only [HermitianMat.ousUnit_eq_one] at hx
  rw [HermitianMat.le_iff_mulVec_le]
  intro v
  rw [quadForm_zero]
  have hs := quadForm_nonneg (𝕜 := 𝕜) v
  have hkey : ∀ ε : ℝ, 0 < ε →
      star v ⬝ᵥ x.mat *ᵥ v ≤ (ε : 𝕜) * (star v ⬝ᵥ v) := by
    intro ε hε
    have h := (HermitianMat.le_iff_mulVec_le).mp (hx ε hε) v
    rwa [quadForm_smul_one] at h
  have hsim : RCLike.im (star v ⬝ᵥ v) = 0 := by
    have h := (RCLike.le_iff_re_im.mp hs).2
    simpa using h.symm
  have hsre : (0 : ℝ) ≤ RCLike.re (star v ⬝ᵥ v) := by
    have h := (RCLike.le_iff_re_im.mp hs).1
    simpa using h
  have hre : ∀ ε : ℝ, 0 < ε →
      RCLike.re (star v ⬝ᵥ x.mat *ᵥ v) ≤ ε * RCLike.re (star v ⬝ᵥ v) := by
    intro ε hε
    have h := (RCLike.le_iff_re_im.mp (hkey ε hε)).1
    rwa [show RCLike.re ((ε : 𝕜) * (star v ⬝ᵥ v)) = ε * RCLike.re (star v ⬝ᵥ v) from by
      simp [RCLike.mul_re]] at h
  have him : RCLike.im (star v ⬝ᵥ x.mat *ᵥ v) = 0 := by
    have h := (RCLike.le_iff_re_im.mp (hkey 1 one_pos)).2
    rw [show RCLike.im (((1 : ℝ) : 𝕜) * (star v ⬝ᵥ v))
        = RCLike.im (star v ⬝ᵥ v) from by simp] at h
    rw [h, hsim]
  rw [RCLike.le_iff_re_im]
  refine ⟨?_, ?_⟩
  · simp only [map_zero]
    rcases eq_or_lt_of_le hsre with hs0 | hspos
    · have h := hre 1 one_pos
      rw [← hs0] at h
      linarith
    · by_contra hcon
      push_neg at hcon
      have hεpos : 0 < RCLike.re (star v ⬝ᵥ x.mat *ᵥ v) / (2 * RCLike.re (star v ⬝ᵥ v)) := by
        positivity
      have h := hre _ hεpos
      rw [show RCLike.re (star v ⬝ᵥ x.mat *ᵥ v) / (2 * RCLike.re (star v ⬝ᵥ v))
            * RCLike.re (star v ⬝ᵥ v) = RCLike.re (star v ⬝ᵥ x.mat *ᵥ v) / 2 from by
          field_simp] at h
      linarith
  · simp only [map_zero, him]

/-- The textbook ℕ-form of the Archimedean property also holds on the carrier, via
`OrderUnitSpace.arch_iff`. -/
theorem isArchNat : OrderUnitSpace.IsArchNat (HermitianMat n 𝕜) :=
  OrderUnitSpace.arch_iff.mp isArchimedean

end Archimedean

end HermitianMat
