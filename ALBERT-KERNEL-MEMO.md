# Albert branch: discharging `block_injective` without Spin(8) — M0(b) feasibility memo

**Date:** 2026-08-04 (campaign M0 design pass; see `LEDGER.md` and
`research/PAPER-A-LEAN-ROUTE.md` in the blog repo).

**Question posed by the route (M0(b)).** Can `IsAlbertModel.block_injective` — the
one Yokota/triality import of the exceptional branch — be reduced to a
kernel-rank computation on the explicit frame-stabilizing derivation algebra
acting on ℝ²⁷, bypassing the Spin(8)/triality identification entirely?

**Answer: better than asked.** The import falls to an **elementary two-step
algebraic proof** (the "unit-slot argument") that needs no Spin(8), no triality,
no 28-dimensional anything, and no large rank certificate. The only computational
ingredient is `nucleus(𝕆) = ℝ`, a finite check against the Cayley table. The
729-unknown kernel-rank certificate contemplated by the route is demoted to
**fallback #2**; the disclosed-axiom exit remains fallback #3.

Confidence: high at proof-sketch level, verified below in the standard matrix-unit
convention; one named caveat (§4) about conventions in whichever concrete `H₃(𝕆)`
model M6 builds.

---

## 1. What the field asserts on the intended instance

For the intended model: `Stab` = the frame-stabilizing derivation algebra
`𝔡 = {D ∈ Der(H₃(𝕆)) : D(E_ii) = 0, i = 1,2,3}`, and `ρ_ij(D) = D|_{V_ij}`
under isometric identifications `V_ij ≅ 𝕆 ≅ ℝ⁸`. Note two cheap generic lemmas
make this well-typed:

- **(P1) Peirce preservation.** `D(E_ii) = 0` ⟹ `D` commutes with each
  multiplication operator `L_{E_ii}` (Leibniz), hence preserves every
  eigenspace of the `L_{E_ii}`, i.e. every Peirce space `V_ij`. Generic, easy.
- **(P2) Diagonal kill.** `D` vanishes on `span{E_11, E_22, E_33}` (linearity).

`block_injective` for the instance is then exactly:

> (★) Every derivation of `H₃(𝕆)` that kills the three diagonal frame
> idempotents and vanishes on **one** off-diagonal Peirce block is zero.

This quantifies over the *actual* `Stab`, whatever its dimension — nothing needs
`dim 𝔡 = 28`, the simplicity of 𝔰𝔭𝔦𝔫(8), or the identification of the three
block actions with `8_v, 8_s, 8_c`.

## 2. The unit-slot argument (kills the import elementarily)

Work in the standard matrix-unit presentation: `F_ij(x) = x E_ij + x̄ E_ji`
(`x ∈ 𝕆`, `i < j`), Jordan product `X ∘ Y = ½(XY + YX)`. Two product identities,
verified by direct matrix-unit computation:

- (I) `F_12(x) ∘ F_23(y) = ½ F_13(x·y)`
- (II) `F_13(z) ∘ F_23(y) = ½ F_12(z·ȳ)`

Let `D ∈ 𝔡` with `D|_{V_12} = 0`. Write `D F_13(z) = F_13(C₁₃ z)` and
`D F_23(y) = F_23(C₂₃ y)` (P1 gives block preservation; `C_ij ∈ End_ℝ(𝕆)`).

**Step 1 (unit slot).** Apply `D` to (I) with Leibniz and `D|_{V_12} = 0`:

  `C₁₃(x·y) = x · (C₂₃ y)` for all `x, y ∈ 𝕆`.

Put `x = 1`: `C₁₃ = C₂₃ =: C`. Put `y = 1`, `c := C(1)`: `C(x) = x·c`. Substitute
back: `(x·y)·c = x·(y·c)` for all `x, y`, i.e. the associator `[x, y, c]`
vanishes identically, i.e. `c ∈ nucleus(𝕆) = ℝ·1`. So `C = (scalar c)·id`.

**Step 2 (second identity kills the scalar).** Apply `D` to (II): the right side
lies in `V_12`, where `D` vanishes, so

  `0 = (C z)·ȳ + z·conj(C y) = c·(z·ȳ) + c·(z·ȳ) = 2c·(z·ȳ)` for all `z, y`

(using `c` real, so `conj(cy) = c·ȳ`). Take `z = y = 1`: `c = 0`. Hence
`C = 0`, i.e. `D|_{V_13} = D|_{V_23} = 0`, and with (P2) `D = 0`. ∎

Injectivity of `ρ_13` and `ρ_23` follow by the same argument with indices
permuted (mechanical; no symmetry apparatus needed — just redo twice).

**Inputs consumed, in full:** octonion algebra basics (unit, conjugation
anti-automorphism, bilinearity), the two matrix-unit identities (I)/(II)
(finite computations in the concrete model), Peirce bookkeeping (P1)/(P2), and

- **(N) `nucleus(𝕆) = ℝ`**: `[x, y, c] = 0 for all x, y ⟹ c ∈ ℝ·1`. Finite
  check: expand `c` in the standard basis; for each imaginary unit `e_k` exhibit
  a basis pair with `[e_i, e_j, e_k] ≠ 0` from the Cayley table; linear
  independence forces each imaginary coefficient to zero. `decide`-scale over
  exact scalars; no `native_decide` (which the audit census rejects).

Notably NOT consumed: skew-adjointness of the block actions, alternativity
beyond what (N)'s table check uses, any Lie theory, any dimension count.

## 3. What M6 looks like under this route

1. Build `H₃(𝕆)` over the existing octonion formalization
   (`~/repos/research/lean/` `Octonions.lean`, all sorries proved; coordinate
   with Nuccio's Mathlib WIP per LEDGER before duplicating). 27-dim ℝ-module
   with the symmetrized product; frame `E_11, E_22, E_33`; Peirce blocks as
   `F_ij` images.
2. Prove (I), (II) in the model (finite bilinear computations), (P1), (P2)
   generically, and (N) by table check.
3. The unit-slot argument above — a page of equational Lean.
4. Package: `Stab := 𝔡` (the derivation subalgebra as a `Submodule`-carried
   type), `ρ_ij` := block restriction, `IsAlbertModel.mk` from (★).

Estimated as weeks of mechanical work, not months, and **the Yokota citation
leaves the import ledger entirely** (it remains a historical pointer in prose).
The heavy remaining Albert work is then shared with every branch: producing the
`DiagonalHomSetup` data (`Θ`, `dχ`, `ρ` from the actual sequential product) —
that is M2-machinery specialized to the Albert model, not part of this memo's
question.

## 4. Caveat and fallbacks

**Convention caveat.** (I)/(II) were verified here in the `F_ij`/matrix-unit
convention with `X∘Y = ½(XY+YX)`. If M6's concrete model places conjugations
differently (e.g. Freudenthal's `x̄` on the other triangle), the identities pick
up conjugates/signs but the argument's shape (unit slot → nucleus → second
identity kills the scalar) is convention-independent. Re-derive (I)/(II) in the
chosen model before quoting this memo as discharged.

**Fallback ladder** (pre-registered):
1. Unit-slot argument (this memo) — mainline.
2. Kernel-rank certificate: with (P1)/(P2), (★) is a linear system in the three
   block components (≤ 192 unknowns; with `D|_{V_12} = 0` imposed, 128);
   kernel-zero certified by an explicit invertible square minor over ℚ —
   kernel-`decide` scale (~10⁶ rational ops), still no `native_decide`. The
   729-unknown full-`End(ℝ²⁷)` version in the route file is superseded by this
   block-reduced form.
3. Disclosed axiom: keep `block_injective` as a cited hypothesis field exactly
   as today, stated in THEOREM-MAP §2 — the honest exit if 1 and 2 both slip.

## 5. Verdict for the route file

M6's risk class changes from "1–3 months of heavy mechanical exact linear
algebra, validity of the reduction uncertain" to "weeks of equational algebra
with a finite-check lemma; validity verified at sketch level in the standard
convention." The campaign's expected import count at M7: **one** (Jordan–von
Neumann–Wigner, by per-type scoping) — the Albert import is expected to
discharge, and Kadison (M3) remains the only other candidate for a disclosed
axiom if it stalls.
