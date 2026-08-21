/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.MasterTheorem.Interface
import Mathlib.Analysis.Quaternion

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Master Theorem chain — the quaternionic branch (`thm:quaternionic`)

The quaternionic typewise branch of the master theorem
(`landing/papers/twist-normal-form/main.tex`, `thm:quaternionic`).

On `Hₙ(ℍ)` with `n ≥ 3` the frame-stabilizer Lie algebra is `(Im ℍ)ⁿ`, and a
stabilizer element `ξ = (ξ₁, …, ξₙ)` acts on the coherence block
`V_{ij} ≅ ℍ` by the **two-slot map**
`ρ_{ij}(ξ) : x ↦ ξ_i · x − x · ξ_j`.
Unlike the exceptional branch, the individual block representation `ρ_{ij}` is
**not** faithful — a spectator coordinate `ξ_l` (`l ≠ i, j`) lies in its kernel.
What is decisive is that the *two-slot* assignment `(ξ_i, ξ_j) ↦ ρ_{ij}(ξ)` is
injective, together with the third-index coefficient kill supplied by coalescence
(`ρ_{ij}(dχ(r)) = (r_i − r_j)·T_{ij}`, `StabilizerCoupling.coupling`).

The kill (run step-for-step along the paper's `thm:quaternionic`): with
`ξ_i(r) = Σ_l r_l a_{il}`, matching the `r_l` coefficient for `l ≠ i, j` (which
exists because `n ≥ 3`) gives `a_{il} x = x a_{jl}` for all `x`; setting `x = 1`
gives `a_{il} = a_{jl}`, and then `a_{il}` commutes with every quaternion, so
`a_{il} ∈ Z(ℍ) ∩ Im ℍ = {0}`. Matching the `r_i` and `r_j` coefficients gives
`T_{ij}(x) = a_{ii} x = x a_{jj}`, forcing `a_{ii} = a_{jj} ∈ Z(ℍ) ∩ Im ℍ = {0}`,
whence `T_{ij} = 0` — in the paper's normal-form reading, the update is Lüders.

## Design (how the concrete model binds to the abstract interface)

`V := Quaternion ℝ` is the single block space (it carries Mathlib's inner product
space instance, `Mathlib/Analysis/Quaternion.lean`). We do **not** construct a
`StabilizerCoupling` from scratch; instead the capstone `quaternionic_luders` takes
*any* `StabilizerCoupling n Stab (Quaternion ℝ)` whose block representation has the
two-slot form (an explicit named hypothesis `hρ`, with `im : Stab → Fin n → ℍ`
extracting the imaginary quaternion coordinates, imaginary by `himag`) and derives
`T_{ij} = 0`. This is honest relative mathematics: the content is that the *only*
coupling of the two-slot form is Lüders.

The two concrete facts underpinning the model are proved here directly:

* `central_im_zero` — `Z(ℍ) ∩ Im ℍ = {0}` (a purely imaginary quaternion commuting
  with every quaternion is `0`);
* `twoSlot_injective` — the decisive two-slot injectivity of the block action;
* `twoSlot_skew` — the two-slot map is skew for the quaternion inner product
  (`prop:isotropy`), i.e. the abstract `ρ_skew` field is realized by the model, so
  the `hρ` hypothesis is not vacuous.

**No new axioms** — the quaternionic branch is pure proof. It consumes only
`StabilizerCoupling` (never `ComparisonSetup`), so `#print axioms
quaternionic_luders` records only the three core Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`). In particular the van Imhoff–Roelands
order-isomorphism input — now carried as the cited `ComparisonSetup` field
`Θ_jordan` rather than a global axiom — does not enter this branch's proof term.

## References
* Ehrlich 2026, *Sequential-Product Moduli on Simple Euclidean Jordan Algebras*,
  `thm:quaternionic`.
* Faraut–Korányi, *Analysis on Symmetric Cones*, 1994 (Peirce theory, Ch. IV).
-/

noncomputable section

open scoped InnerProductSpace
open Quaternion

namespace MasterTheorem
namespace Quaternionic

/-! ## Concrete quaternionic facts -/

/-- **`Z(ℍ) ∩ Im ℍ = {0}`.** A purely imaginary quaternion (`q.re = 0`) that
commutes with every quaternion is zero. This is the finite computation the paper
invokes twice in `thm:quaternionic`. -/
theorem central_im_zero {q : Quaternion ℝ} (hre : q.re = 0)
    (h : ∀ x : Quaternion ℝ, q * x = x * q) : q = 0 := by
  -- Expand the commutation identity against a *variable* quaternion `y` first.
  -- `imK_mul`/`imJ_mul` are stated over `ℍ[ℝ] = Quaternion ℝ`, while a raw
  -- structure literal `⟨0,0,1,0⟩` carries the inferred type `ℍ[ℝ,-1,0,-1]`;
  -- unifying the two unfolds the semireducible `Quaternion`, which `simp` no
  -- longer does. Instantiating at the literals *after* the rewrite avoids it.
  have hKgen : ∀ y : Quaternion ℝ,
      q.re * y.imK + q.imI * y.imJ - q.imJ * y.imI + q.imK * y.re
        = y.re * q.imK + y.imI * q.imJ - y.imJ * q.imI + y.imK * q.re := by
    intro y
    have hK := congrArg QuaternionAlgebra.imK (h y)
    simp only [imK_mul] at hK
    exact hK
  have hJgen : ∀ y : Quaternion ℝ,
      q.re * y.imJ - q.imI * y.imK + q.imJ * y.re + q.imK * y.imI
        = y.re * q.imJ - y.imI * q.imK + y.imJ * q.re + y.imK * q.imI := by
    intro y
    have hJ := congrArg QuaternionAlgebra.imJ (h y)
    simp only [imJ_mul] at hJ
    exact hJ
  -- q.imI: commute with j = ⟨0,0,1,0⟩ (imK component); q.imJ: commute with
  -- i = ⟨0,1,0,0⟩ (imK component); q.imK: commute with i (imJ component).
  have hI := hKgen ⟨0, 0, 1, 0⟩
  have hJ := hKgen ⟨0, 1, 0, 0⟩
  have hK := hJgen ⟨0, 1, 0, 0⟩
  norm_num at hI hJ hK
  refine QuaternionAlgebra.ext hre ?_ ?_ ?_
  · change q.imI = 0
    linarith
  · change q.imJ = 0
    linarith
  · change q.imK = 0
    linarith

/-- **Two-slot injectivity** (the decisive quaternionic fact, paper §4 remark). The
map on pairs of imaginary quaternions `(ξ_i, ξ_j) ↦ (x ↦ ξ_i x − x ξ_j)` is
injective — even though the single-slot representation is not. -/
theorem twoSlot_injective {ξi ξj ηi ηj : Quaternion ℝ}
    (hξi : ξi.re = 0) (_hξj : ξj.re = 0) (hηi : ηi.re = 0) (_hηj : ηj.re = 0)
    (h : ∀ x : Quaternion ℝ, ξi * x - x * ξj = ηi * x - x * ηj) :
    ξi = ηi ∧ ξj = ηj := by
  have hcomm : ∀ x : Quaternion ℝ, (ξi - ηi) * x = x * (ξj - ηj) := by
    intro x
    have hkey : (ξi - ηi) * x - x * (ξj - ηj)
        = (ξi * x - x * ξj) - (ηi * x - x * ηj) := by
      rw [sub_mul, mul_sub]; abel
    rw [h x, sub_self] at hkey
    exact sub_eq_zero.mp hkey
  have hd : ξi - ηi = ξj - ηj := by
    have h1 := hcomm 1
    simpa using h1
  have hre : (ξi - ηi).re = 0 := by rw [re_sub, hξi, hηi, sub_zero]
  have hcentral : ξi - ηi = 0 :=
    central_im_zero hre (fun x => by rw [hcomm x, hd])
  refine ⟨sub_eq_zero.mp hcentral, sub_eq_zero.mp ?_⟩
  rw [← hd]; exact hcentral

/-- **`prop:isotropy` for the quaternionic block.** The two-slot map with imaginary
coordinates is skew for the quaternion inner product, `⟪ξ_i x − x ξ_j, x⟫ = 0`.
This certifies that the abstract `StabilizerCoupling.ρ_skew` field is realized by
the two-slot model, so the capstone's `hρ` hypothesis is not vacuous. -/
theorem twoSlot_skew {ξi ξj x : Quaternion ℝ} (hξi : ξi.re = 0) (hξj : ξj.re = 0) :
    ⟪ξi * x - x * ξj, x⟫_ℝ = 0 := by
  simp only [Quaternion.inner_def, sub_mul, re_sub, re_mul, re_star, imI_star, imJ_star,
    imK_star, imI_mul, imJ_mul, imK_mul, hξi, hξj]
  ring

/-! ## The capstone: the two-slot coupling is Lüders -/

/-- A third frame index distinct from any two given ones, available because
`n ≥ 3`. Supplies the spectator coordinate whose coalescence coefficient kills the
off-diagonal quaternion generators. -/
theorem exists_third {n : ℕ} (hn : 3 ≤ n) (p q : Fin n) :
    ∃ m : Fin n, m ≠ p ∧ m ≠ q := by
  have hne : ({p, q} : Finset (Fin n))ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    have h2 : ({p, q} : Finset (Fin n)).card ≤ 2 := by
      refine (Finset.card_insert_le _ _).trans ?_
      simp
    simp only [Fintype.card_fin]
    omega
  obtain ⟨m, hm⟩ := hne
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at hm
  push_neg at hm
  exact ⟨m, hm.1, hm.2⟩

/-- **`thm:quaternionic` (differential form).** Let `S` be any frame-stabilizer
coupling on `V = Quaternion ℝ` of rank `n ≥ 3` whose block representation has the
two-slot quaternionic form `S.ρ i j ξ x = (im ξ i) · x − x · (im ξ j)` with
imaginary coordinates `im ξ k ∈ Im ℍ`. Then every off-diagonal twist generator
vanishes, `T_{ij} = 0` (`i ≠ j`) — the Lüders conclusion in the paper's normal-form
reading; the Lean statement is exactly `T i j = 0`.

The proof is the paper's `thm:quaternionic`, run against the abstract coupling
identity `S.coupling` (`ρ_{ij}(dχ r) = (r_i − r_j)·T_{ij}`): the `n ≥ 3` spectator
index (`exists_third`) kills the off-diagonal coordinates via `central_im_zero`, and
the diagonal coordinates are killed the same way, leaving `T_{ij} = 0`. -/
theorem quaternionic_luders {n : ℕ} {Stab : Type*} [AddCommGroup Stab] [Module ℝ Stab]
    (S : StabilizerCoupling n Stab (Quaternion ℝ))
    (im : Stab → Fin n → Quaternion ℝ)
    (himag : ∀ (ξ : Stab) (k : Fin n), (im ξ k).re = 0)
    (hρ : ∀ (i j : Fin n) (ξ : Stab) (x : Quaternion ℝ),
      S.ρ i j ξ x = im ξ i * x - x * im ξ j)
    {i j : Fin n} (hij : i ≠ j) : S.T i j = 0 := by
  -- The coupling identity, applied to a vector `x`, in two-slot form.
  have key : ∀ (a b : Fin n) (r : Fin n → ℝ) (x : Quaternion ℝ),
      im (S.dχ r) a * x - x * im (S.dχ r) b = (r a - r b) • (S.T a b x) := by
    intro a b r x
    have hc := LinearMap.congr_fun (S.coupling a b r) x
    rw [LinearMap.smul_apply, hρ a b (S.dχ r) x] at hc
    exact hc
  -- Off-diagonal coordinate kill: `a_{pq} = im (dχ e_q) p = 0` for `p ≠ q`.
  have offdiag : ∀ (p q : Fin n), p ≠ q → im (S.dχ (Pi.single q 1)) p = 0 := by
    intro p q hpq
    obtain ⟨m, hmp, hmq⟩ := exists_third S.rank_ge p q
    -- block `(p, m)`, coefficient of `r_q` (both `p ≠ q` and `m ≠ q` give RHS = 0).
    have hcomm : ∀ x, im (S.dχ (Pi.single q 1)) p * x
        = x * im (S.dχ (Pi.single q 1)) m := by
      intro x
      have hk := key p m (Pi.single q 1) x
      rw [Pi.single_eq_of_ne hpq, Pi.single_eq_of_ne hmq, sub_self,
        zero_smul, sub_eq_zero] at hk
      exact hk
    have hAB : im (S.dχ (Pi.single q 1)) p = im (S.dχ (Pi.single q 1)) m := by
      have h1 := hcomm 1
      simpa using h1
    exact central_im_zero (himag _ p) (fun x => by rw [hcomm x, hAB])
  -- Diagonal kill: `T_{ij}(x) = a_{ii} x` and `= x a_{jj}`, with off-diagonals gone.
  have eqI : ∀ x, im (S.dχ (Pi.single i 1)) i * x = S.T i j x := by
    intro x
    have hk := key i j (Pi.single i 1) x
    rw [offdiag j i (Ne.symm hij)] at hk
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, sub_zero,
      one_smul] at hk
    exact hk
  have eqII : ∀ x, x * im (S.dχ (Pi.single j 1)) j = S.T i j x := by
    intro x
    have hk := key i j (Pi.single j 1) x
    rw [offdiag i j hij] at hk
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, zero_mul, zero_sub,
      neg_one_smul, neg_inj] at hk
    exact hk
  -- `a_{ii} = a_{jj}` and both central ⟹ `a_{ii} = 0`.
  have hAB : im (S.dχ (Pi.single i 1)) i = im (S.dχ (Pi.single j 1)) j := by
    have h1 := (eqI 1).trans (eqII 1).symm
    simpa using h1
  have haii : im (S.dχ (Pi.single i 1)) i = 0 := by
    refine central_im_zero (himag _ i) (fun x => ?_)
    rw [eqI x, ← eqII x, hAB]
  -- Conclude `T_{ij} = 0`.
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply, ← eqI x, haii, zero_mul]

end Quaternionic
end MasterTheorem
