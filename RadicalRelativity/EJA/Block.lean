/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import RadicalRelativity.EJA.Frame

set_option linter.style.longLine false

/-!
# The rank-two block, split into its three Peirce pieces

**ARC-9 block 9.14, 2026-08-12.**

For orthogonal idempotents `p, q`, the Peirce-1 space of the rank-two block `q' = p + q`
decomposes:

  `J₁(p + q) = J₁(p) ⊕ (J_{1/2}(p) ∩ J_{1/2}(q)) ⊕ J₁(q)`.

`exists_block_split` is the forward half and `block_mul_eq_self` the converse, so together
they characterise `J₁(p+q)` exactly. This is the Faraut–Korányi coherence-block structure at
the smallest interesting size, and it is what `MasterTheorem/Coalescence.lean`'s `J2` and
`IsBlockElt` predicates are *about*.

## The argument

`L_p` commutes with `L_q` (`opCommute_of_orthogonal`), hence with `L_{p+q}`, hence with every
polynomial in `L_p` — so the three Peirce projections of `p` all preserve `J₁(p+q)`. Apply
them to `x ∈ J₁(p+q)`: the pieces have `p`-eigenvalues `1`, `1/2`, `0`, and since
`q ∘ z = (p+q) ∘ z − p ∘ z = z − p ∘ z` on `J₁(p+q)`, their `q`-eigenvalues are the
complements `0`, `1/2`, `1`. **The three admissible patterns are exactly the three ways
`μ + ν = 1` can happen with `μ, ν ∈ {0, 1/2, 1}`** — which is why the block has three pieces
and not nine.

★ **The eigenvalue trichotomy is what makes this finite**, but note it is not *invoked*: the
projections do the work directly. The trichotomy explains the shape of the answer rather than
appearing in the proof.

## `q` is not assumed idempotent, and that is not an oversight

`exists_block_split` needs only **`p ∘ p = p` and `p ∘ q = 0`**. Lean's unused-variable linter
caught the `hq` hypothesis being dead and it was removed rather than silenced. The reason is
visible in the argument above: every claim about `q` is derived from
`q ∘ z = (p+q) ∘ z − p ∘ z`, which never asks what `q ∘ q` is.

★ What `hq` buys is the *interpretation*: without it `p + q` need not be idempotent, so
"`J₁(p+q)`" is not a Peirce space and "`J₁(q)`" is not either — the conclusions are still true,
they just stop being a Peirce decomposition. Callers wanting the FK reading should have `hq`
in hand from `IsOrthIdemFamily`; the theorem simply does not need to be told.
-/

namespace RadicalRelativity.EJA

section Block

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

omit [IsCommJordan J] in
/-- If `L_c` commutes with `L_p` then it commutes with the Peirce-1 projection of `p`. -/
theorem mul_peirceOne_comm {c p : J} (h : ∀ w : J, c * (p * w) = p * (c * w)) (x : J) :
    c * peirceOne p x = peirceOne p (c * x) := by
  simp only [peirceOne_apply, mul_sub, mul_smul_comm', h]

omit [IsCommJordan J] in
/-- The same for the Peirce-`1/2` projection. -/
theorem mul_peirceHalf_comm {c p : J} (h : ∀ w : J, c * (p * w) = p * (c * w)) (x : J) :
    c * peirceHalf p x = peirceHalf p (c * x) := by
  simp only [peirceHalf_apply, mul_sub, mul_smul_comm', h]

omit [IsCommJordan J] in
/-- The same for the Peirce-`0` projection. -/
theorem mul_peirceZero_comm {c p : J} (h : ∀ w : J, c * (p * w) = p * (c * w)) (x : J) :
    c * peirceZero p x = peirceZero p (c * x) := by
  simp only [peirceZero_apply, mul_add, mul_sub, mul_smul_comm', h]

variable {p q : J}

omit [IsScalarTower ℝ J J] in
/-- `L_{p+q}` commutes with `L_p`, for `p` idempotent and orthogonal to `q`. -/
theorem add_mul_comm_left (hp : p * p = p) (hpq : p * q = 0) (w : J) :
    (p + q) * (p * w) = p * ((p + q) * w) := by
  rw [add_mul, add_mul, mul_add, opCommute_of_orthogonal hp hpq w]

/-- **The rank-two block splits.** Every element of `J₁(p+q)` is the sum of an element of
`J₁(p)`, an element of the coherence space `J_{1/2}(p) ∩ J_{1/2}(q)`, and an element of
`J₁(q)` — and the `q`-eigenvalues come out as the complements of the `p`-eigenvalues.

★ Needs only `p ∘ p = p` and `p ∘ q = 0`; see the module docstring on why `q ∘ q = q` is not
required. -/
theorem exists_block_split (hp : p * p = p) (hpq : p * q = 0) {x : J} (hx : (p + q) * x = x) :
    ∃ a b c : J, (p * a = a ∧ q * a = 0) ∧ (p * b = (2 : ℝ)⁻¹ • b ∧ q * b = (2 : ℝ)⁻¹ • b)
      ∧ (p * c = 0 ∧ q * c = c) ∧ x = a + b + c := by
  have hcomm := add_mul_comm_left hp hpq
  refine ⟨peirceOne p x, peirceHalf p x, peirceZero p x, ⟨mul_peirceOne hp x, ?_⟩,
    ⟨mul_peirceHalf hp x, ?_⟩, ⟨mul_peirceZero hp x, ?_⟩, (peirce_add_add p x).symm⟩
  · have h1 : p * peirceOne p x + q * peirceOne p x = peirceOne p x := by
      rw [← add_mul, mul_peirceOne_comm hcomm x, hx]
    rw [mul_peirceOne hp x] at h1
    refine add_left_cancel (a := peirceOne p x) ?_
    rw [add_zero]
    exact h1
  · have h2 : p * peirceHalf p x + q * peirceHalf p x = peirceHalf p x := by
      rw [← add_mul, mul_peirceHalf_comm hcomm x, hx]
    rw [mul_peirceHalf hp x] at h2
    have hstep : q * peirceHalf p x = peirceHalf p x - (2 : ℝ)⁻¹ • peirceHalf p x :=
      eq_sub_of_add_eq (by rw [add_comm]; exact h2)
    rw [hstep]
    module
  · have h3 : p * peirceZero p x + q * peirceZero p x = peirceZero p x := by
      rw [← add_mul, mul_peirceZero_comm hcomm x, hx]
    rw [mul_peirceZero hp x, zero_add] at h3
    exact h3

omit [IsCommJordan J] [IsScalarTower ℝ J J] in
/-- **The converse.** Each of the three admissible eigenvalue patterns lands in `J₁(p+q)`, so
together with `exists_block_split` this characterises the block exactly.

The three cases are `1 + 0`, `1/2 + 1/2` and `0 + 1` — the only ways two elements of
`{0, 1/2, 1}` sum to `1`. -/
theorem block_mul_eq_self {z : J} (h : (p * z = z ∧ q * z = 0)
    ∨ (p * z = (2 : ℝ)⁻¹ • z ∧ q * z = (2 : ℝ)⁻¹ • z) ∨ (p * z = 0 ∧ q * z = z)) :
    (p + q) * z = z := by
  rw [add_mul]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, add_zero]
  · rw [h1, h2]; module
  · rw [h1, h2, zero_add]

end Block

end RadicalRelativity.EJA
