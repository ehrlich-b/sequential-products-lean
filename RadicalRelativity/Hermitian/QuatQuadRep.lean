/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.Hermitian.Symplectic
import RadicalRelativity.Necessity.Theta

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

end HermitianMat
