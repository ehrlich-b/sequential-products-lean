/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.Symplectic
import RadicalRelativity.Necessity.Theta
import RadicalRelativity.Hermitian.Sequential

set_option linter.style.longLine false

/-!
# The quadratic representation is quaternionic  (`H_n(ℍ)` row, Θ-chain step 1)

`Q_{√a} x = √a · x · √a` is the map the whole Θ construction is built on.  This file shows it
restricts to the quaternionic subspace, in both directions — which is what lets `theta` exist
on `QuatCarrier n`.

**The load-bearing lemma is the intertwining**, `quatConjH_conj`: for quaternionic `A`,
`Φ (x.conj A) = (Φ x).conj A` for **every** `x`, quaternionic or not.  Stating it that way is
what makes the inverse branch free.  Conjugation by `√a` is handled by
`IsQuaternionic.cfc_of_effect` directly, but the inverse branch conjugates by
`(√a)⁻¹ = a.cfc (fun x => (√x)⁻¹)`, and **that function is not continuous at `0`**, so
`cfc_of_effect` does not apply to it.  With the intertwining in hand the inverse branch needs
no functional calculus at all: `Q` is injective, and `Q (Φ x) = Φ (Q x) = Φ y = y = Q x`
forces `Φ x = x`.

* `quatConjH_conj` — the intertwining.
* `IsQuaternionic.conj`, `IsQuaternionic.sqrt` — closure under conjugation and under `√`.
* `IsQuaternionic.quadRep`, `IsQuaternionic.quadRepInv` — both branches restrict.
-/

noncomputable section

open scoped Matrix
open ComplexOrder

namespace HermitianMat

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The intertwining.**  Conjugation by a quaternionic Hermitian matrix commutes with `Φ`,
for every argument.  `A` being Hermitian collapses `Aᴴ` to `A`, and `Φ` is multiplicative. -/
theorem quatConjH_conj (x : HermitianMat (n ⊕ n) ℂ) {A : HermitianMat (n ⊕ n) ℂ}
    (hA : IsQuaternionic A) :
    quatConjH (x.conj A.mat) = (quatConjH x).conj A.mat := by
  ext1
  rw [quatConjH_mat, HermitianMat.conj_apply_mat, HermitianMat.conj_apply_mat, quatConjH_mat]
  have hAH : A.matᴴ = A.mat := A.H
  rw [hAH, quatConj_mul, quatConj_mul, hA]

/-- Conjugation by a quaternionic Hermitian matrix keeps the quaternionic set invariant. -/
theorem IsQuaternionic.conj {x A : HermitianMat (n ⊕ n) ℂ}
    (hx : IsQuaternionic x) (hA : IsQuaternionic A) :
    IsQuaternionic (x.conj A.mat) := by
  have hxx : quatConjH x = x := by ext1; exact hx
  have h := quatConjH_conj x hA
  rw [hxx] at h
  exact congrArg HermitianMat.mat h

/-- **`√a` is quaternionic** for a quaternionic effect `a`: `√` is continuous on `[0,1]`, so
the functional-calculus closure applies. -/
theorem IsQuaternionic.sqrt {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) : IsQuaternionic (a.cfc Real.sqrt) :=
  congrArg HermitianMat.mat
    (ha.cfc_of_effect hae (Real.continuous_sqrt.continuousOn))

/-- **The forward branch restricts**: `Q_{√a}` maps quaternionic to quaternionic. -/
theorem IsQuaternionic.quadRep {a x : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (hx : IsQuaternionic x) :
    IsQuaternionic (Necessity.quadRep a x) :=
  hx.conj (ha.sqrt hae)

/-- `Φ` intertwines the quadratic representation itself. -/
theorem quatConjH_quadRep {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (x : HermitianMat (n ⊕ n) ℂ) :
    quatConjH (Necessity.quadRep a x) = Necessity.quadRep a (quatConjH x) :=
  quatConjH_conj x (ha.sqrt hae)

/-- **The inverse branch restricts too** — and note it needs no functional calculus.  The
function `(√x)⁻¹` is not continuous at `0`, so `cfc_of_effect` cannot see it; instead the
intertwining plus injectivity of `Q_{√a}` forces the answer. -/
theorem IsQuaternionic.quadRepInv {a y : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (hbd : a.mat.PosDef) (hy : IsQuaternionic y) :
    IsQuaternionic (Necessity.quadRepInv a y) := by
  have hinj : Function.Injective (Necessity.quadRep a) :=
    (Necessity.quadRepEquiv a hbd).injective
  have hround : Necessity.quadRep a (Necessity.quadRepInv a y) = y := by
    show (y.conj _).conj _ = y
    rw [Necessity.conj_conj_mat, Necessity.sqrt_mul_invSqrt hbd, Necessity.conj_one_mat]
  have hyy : quatConjH y = y := by ext1; exact hy
  have key : Necessity.quadRep a (quatConjH (Necessity.quadRepInv a y))
      = Necessity.quadRep a (Necessity.quadRepInv a y) := by
    rw [← quatConjH_quadRep ha hae, hround, hyy]
  exact congrArg HermitianMat.mat (hinj key)


/-! ## `Q_{√a}` as an automorphism of the quaternionic carrier

With both branches shown to restrict, `Q_{√a}` is an `ℝ`-linear automorphism of
`QuatCarrier n` outright.  This is the object the `H_n(ℍ)` row's `theta` would be built from.
-/

/-- `Q_{√a}` restricted to the quaternionic carrier. -/
def quatQuadRep {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) : QuatCarrier n →ₗ[ℝ] QuatCarrier n where
  toFun x := ⟨Necessity.quadRep a x.val,
    mem_quatSubmodule.mpr (IsQuaternionic.quadRep ha hae (mem_quatSubmodule.mp x.property))⟩
  map_add' x y := by
    ext1
    exact map_add (Necessity.quadRep a) _ _
  map_smul' c x := by
    ext1
    exact map_smul (Necessity.quadRep a) _ _

@[simp]
theorem quatQuadRep_coe {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (x : QuatCarrier n) :
    ((quatQuadRep ha hae x : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ)
      = Necessity.quadRep a x.val := rfl

/-- The inverse branch, restricted. -/
def quatQuadRepInv {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (hbd : a.mat.PosDef) :
    QuatCarrier n →ₗ[ℝ] QuatCarrier n where
  toFun y := ⟨Necessity.quadRepInv a y.val,
    mem_quatSubmodule.mpr
      (IsQuaternionic.quadRepInv ha hae hbd (mem_quatSubmodule.mp y.property))⟩
  map_add' x y := by
    ext1
    exact map_add (Necessity.quadRepInv a) _ _
  map_smul' c x := by
    ext1
    exact map_smul (Necessity.quadRepInv a) _ _

@[simp]
theorem quatQuadRepInv_coe {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (hbd : a.mat.PosDef) (y : QuatCarrier n) :
    ((quatQuadRepInv ha hae hbd y : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ)
      = Necessity.quadRepInv a y.val := rfl

/-- **`Q_{√a}` is an `ℝ`-linear automorphism of `H_n(ℍ)`.**  Both round trips are the ambient
ones, read through `Subtype.ext`. -/
def quatQuadRepEquiv {a : HermitianMat (n ⊕ n) ℂ} (ha : IsQuaternionic a)
    (hae : OrderUnitSpace.IsEffect a) (hbd : a.mat.PosDef) :
    QuatCarrier n ≃ₗ[ℝ] QuatCarrier n :=
  LinearEquiv.ofLinear (quatQuadRep ha hae) (quatQuadRepInv ha hae hbd)
    (by
      apply LinearMap.ext
      intro y
      ext1
      show Necessity.quadRep a (Necessity.quadRepInv a y.val) = y.val
      show (y.val.conj _).conj _ = y.val
      rw [Necessity.conj_conj_mat, Necessity.sqrt_mul_invSqrt hbd, Necessity.conj_one_mat])
    (by
      apply LinearMap.ext
      intro x
      ext1
      show Necessity.quadRepInv a (Necessity.quadRep a x.val) = x.val
      show (x.val.conj _).conj _ = x.val
      rw [Necessity.conj_conj_mat, Necessity.invSqrt_mul_sqrt hbd, Necessity.conj_one_mat])


/-! ## The Lüders product ON the quaternionic carrier

★★★ New 2026-08-09 (ARC-8 block 8.3).  `WallCertificates/thm-quaternionic.lean` records the honest
state of row 20 as: the carrier `QuatCarrier n` exists, `quatQuadRep` exists, and **no product is
defined on the carrier at all** (its absence claim, with grep scope, is
`SequentialProductOn (QuatCarrier …)` → no hits).  This closes that half.

★ **Nothing here is a new S1–S7 verification.**  Every axiom is the ambient one at `t = 0`, read
through the subtype coercion: the quaternionic set is closed under `Q_{√a}` (`IsQuaternionic.quadRep`,
which is `IsQuaternionic.cfc_of_effect` plus `IsQuaternionic.conj`), the order and unit on the carrier
are the restrictions, and the axioms are pointwise identities or implications between them.  So the
content is the closure, and the closure was already in the tree.

★★ **What this does NOT do, stated plainly, because it is the row's actual statement.**
`thm:quaternionic` says an *arbitrary* S1–S7 product on `H_n(ℍ)`, `n ≥ 3`, **must** be this one
(`Θ_r = id`).  That is the transfer, it is what the certificate names as the row's only honest
residue, and it is untouched here.  What lands is the *sufficiency* direction: this product exists.
The row stays PARTIAL. -/

section LudersProduct

/-- Being an effect of the quaternionic carrier is being an effect of the ambient algebra. -/
theorem quatCarrier_isEffect_iff {a : QuatCarrier n} :
    OrderUnitSpace.IsEffect a ↔ OrderUnitSpace.IsEffect (a : HermitianMat (n ⊕ n) ℂ) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [HermitianMat.ousUnit_eq_one]
    exact h2
  · intro h
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [HermitianMat.ousUnit_eq_one] at h2
    exact h2

/-- The Lüders product of quaternionic elements is quaternionic. -/
theorem isQuaternionic_twistSeq_zero {a b : HermitianMat (n ⊕ n) ℂ}
    (ha : IsQuaternionic a) (hae : OrderUnitSpace.IsEffect a) (hb : IsQuaternionic b) :
    IsQuaternionic (twistSeq 0 a b) := by
  rw [twistSeq_zero]
  exact hb.conj (ha.sqrt hae)

/-- **The Lüders product on `H_n(ℍ)`.**  Total, as the interface requires; off the effects of the
first argument it is `0`, exactly as `badP` is in the rank-two lane. -/
noncomputable def quatSp (a b : QuatCarrier n) : QuatCarrier n :=
  letI := Classical.dec (OrderUnitSpace.IsEffect (a : HermitianMat (n ⊕ n) ℂ))
  if h : OrderUnitSpace.IsEffect (a : HermitianMat (n ⊕ n) ℂ) then
    ⟨twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (b : HermitianMat (n ⊕ n) ℂ),
      mem_quatSubmodule.mpr (isQuaternionic_twistSeq_zero
        (mem_quatSubmodule.mp a.property) h (mem_quatSubmodule.mp b.property))⟩
  else 0

theorem quatSp_coe {a b : QuatCarrier n}
    (ha : OrderUnitSpace.IsEffect (a : HermitianMat (n ⊕ n) ℂ)) :
    ((quatSp a b : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ)
      = twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (b : HermitianMat (n ⊕ n) ℂ) := by
  rw [quatSp, dif_pos ha]

/-- **The product IS `Q_{√a}`**, i.e. the article's `a·b = Q_{√a} b` — stated against the tree's
own `quatQuadRep`, so the operation is the article's and not a lookalike. -/
theorem quatSp_eq_quatQuadRep {a b : QuatCarrier n}
    (ha : OrderUnitSpace.IsEffect (a : HermitianMat (n ⊕ n) ℂ)) :
    quatSp a b = quatQuadRep (mem_quatSubmodule.mp a.property) ha b := by
  apply Subtype.ext
  rw [quatSp_coe ha, quatQuadRep_coe, twistSeq_zero]
  rfl

/-- **`H_n(ℍ)` carries the Lüders product as an S1, S3–S7 sequential product.** -/
noncomputable def quatLuders : SequentialProductOn (QuatCarrier n) where
  sp := quatSp
  sp_add_right := fun {a b c} ha hb hc _ => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    apply Subtype.ext
    rw [quatSp_coe ha']
    push_cast
    rw [twistSeq_add_right, ← quatSp_coe (a := a) (b := b) ha',
      ← quatSp_coe (a := a) (b := c) ha']
  sp_unit_left := fun {a} _ => by
    have h1 : OrderUnitSpace.IsEffect
        ((OrderUnitSpace.ousUnit : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ) := by
      rw [quatCarrier_ousUnit_coe, ← HermitianMat.ousUnit_eq_one]
      exact OrderUnitSpace.isEffect_unit
    apply Subtype.ext
    rw [quatSp_coe h1, quatCarrier_ousUnit_coe, twistSeq_one_left]
  sp_zero_symm := fun {a b} ha hb h => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    have hb' := quatCarrier_isEffect_iff.mp hb
    apply Subtype.ext
    rw [quatSp_coe hb']
    refine twistSeq_zero_symm 0 ha'.1 hb'.1 ?_
    rw [← quatSp_coe ha', congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) h]
    rfl
  sp_assoc_of_compatible := fun {a b c} ha hb _ hcomm => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    have hb' := quatCarrier_isEffect_iff.mp hb
    have hab : OrderUnitSpace.IsEffect
        ((quatSp a b : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ) := by
      rw [quatSp_coe ha']
      exact twistSeq_isEffect 0 ha'.1 ha'.2 hb'.1 hb'.2
    have hcomm' : twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (b : HermitianMat (n ⊕ n) ℂ)
        = twistSeq 0 (b : HermitianMat (n ⊕ n) ℂ) (a : HermitianMat (n ⊕ n) ℂ) := by
      rw [← quatSp_coe ha', ← quatSp_coe hb',
        congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) hcomm]
    apply Subtype.ext
    rw [quatSp_coe ha', quatSp_coe hab, quatSp_coe ha', quatSp_coe hb']
    exact twistSeq_assoc_of_comm 0 ha'.1 hb'.1 hcomm' _
  compatible_ortho := fun {a b} ha hb hcomm => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    have hb' := quatCarrier_isEffect_iff.mp hb
    have hb1 : (b : HermitianMat (n ⊕ n) ℂ) ≤ 1 := by
      have := hb'.2; rwa [HermitianMat.ousUnit_eq_one] at this
    have hsub : OrderUnitSpace.IsEffect
        (((OrderUnitSpace.ousUnit - b : QuatCarrier n)) : HermitianMat (n ⊕ n) ℂ) := by
      push_cast
      rw [quatCarrier_ousUnit_coe]
      refine ⟨sub_nonneg.mpr hb1, ?_⟩
      rw [HermitianMat.ousUnit_eq_one]
      exact sub_le_self _ hb'.1
    have hcomm' : twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (b : HermitianMat (n ⊕ n) ℂ)
        = twistSeq 0 (b : HermitianMat (n ⊕ n) ℂ) (a : HermitianMat (n ⊕ n) ℂ) := by
      rw [← quatSp_coe ha', ← quatSp_coe hb',
        congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) hcomm]
    apply Subtype.ext
    rw [quatSp_coe ha', quatSp_coe hsub]
    push_cast
    rw [quatCarrier_ousUnit_coe]
    exact twistSeq_compat_one_sub 0 ha'.1 hb'.1 hb1 hcomm'
  compatible_add := fun {a b c} ha hb hc hbcle h1 h2 => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    have hb' := quatCarrier_isEffect_iff.mp hb
    have hc' := quatCarrier_isEffect_iff.mp hc
    have hbc' : OrderUnitSpace.IsEffect (((b + c : QuatCarrier n)) : HermitianMat (n ⊕ n) ℂ) :=
      quatCarrier_isEffect_iff.mp ⟨OrderUnitSpace.add_nonneg hb.1 hc.1, hbcle⟩
    have e1 : twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (b : HermitianMat (n ⊕ n) ℂ)
        = twistSeq 0 (b : HermitianMat (n ⊕ n) ℂ) (a : HermitianMat (n ⊕ n) ℂ) := by
      rw [← quatSp_coe ha', ← quatSp_coe hb',
        congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) h1]
    have e2 : twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (c : HermitianMat (n ⊕ n) ℂ)
        = twistSeq 0 (c : HermitianMat (n ⊕ n) ℂ) (a : HermitianMat (n ⊕ n) ℂ) := by
      rw [← quatSp_coe ha', ← quatSp_coe hc',
        congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) h2]
    apply Subtype.ext
    rw [quatSp_coe ha', quatSp_coe hbc']
    push_cast
    exact twistSeq_compat_add 0 ha'.1 hb'.1 hc'.1 e1 e2
  compatible_sp := fun {a b c} ha hb hc h1 h2 => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    have hb' := quatCarrier_isEffect_iff.mp hb
    have hc' := quatCarrier_isEffect_iff.mp hc
    have hbcE : OrderUnitSpace.IsEffect
        ((quatSp b c : QuatCarrier n) : HermitianMat (n ⊕ n) ℂ) := by
      rw [quatSp_coe hb']
      exact twistSeq_isEffect 0 hb'.1 hb'.2 hc'.1 hc'.2
    have e1 : twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (b : HermitianMat (n ⊕ n) ℂ)
        = twistSeq 0 (b : HermitianMat (n ⊕ n) ℂ) (a : HermitianMat (n ⊕ n) ℂ) := by
      rw [← quatSp_coe ha', ← quatSp_coe hb',
        congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) h1]
    have e2 : twistSeq 0 (a : HermitianMat (n ⊕ n) ℂ) (c : HermitianMat (n ⊕ n) ℂ)
        = twistSeq 0 (c : HermitianMat (n ⊕ n) ℂ) (a : HermitianMat (n ⊕ n) ℂ) := by
      rw [← quatSp_coe ha', ← quatSp_coe hc',
        congrArg (fun x : QuatCarrier n => (x : HermitianMat (n ⊕ n) ℂ)) h2]
    apply Subtype.ext
    rw [quatSp_coe ha', quatSp_coe hbcE, quatSp_coe hb']
    exact twistSeq_compat_sp 0 ha'.1 hb'.1 hc'.1 e1 e2
  sp_effect := fun {a b} ha hb => by
    have ha' := quatCarrier_isEffect_iff.mp ha
    have hb' := quatCarrier_isEffect_iff.mp hb
    refine quatCarrier_isEffect_iff.mpr ?_
    rw [quatSp_coe ha']
    exact twistSeq_isEffect 0 ha'.1 ha'.2 hb'.1 hb'.2

end LudersProduct

end HermitianMat
