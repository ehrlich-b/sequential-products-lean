# feat(Analysis/InnerProductSpace): Wigner's theorem over the reals

**DRAFT — not submitted.** See `upstream/README.md` for status and the pre-submission
checklist.

---

Adds Wigner's theorem over `ℝ`, in Uhlhorn's form: for a finite-dimensional real inner
product space `E`, every self-map of `ℙ ℝ E` that preserves the transition probability is
induced by a linear isometry equivalence of `E`.

```lean
theorem Projectivization.exists_isometry_of_transProbPreserving
    [FiniteDimensional ℝ E] [Nontrivial E]
    {f : ℙ ℝ E → ℙ ℝ E} (hf : TransProbPreserving f) :
    ∃ e : E ≃ₗᵢ[ℝ] E, ∀ p : ℙ ℝ E, f p = projMap e p
```

Together with the easy inclusion `projMap_transProbPreserving` this is an exact
characterization: the transition-probability preserving self-maps of `ℙ ℝ E` are precisely
the ones induced by `E ≃ₗᵢ[ℝ] E`.

## Why this form of the hypothesis

`TransProbPreserving f` is *only*

```lean
∀ p q, transProb (f p) (f q) = transProb p q
```

— no linearity, no continuity, and in particular **no bijectivity**. This is Uhlhorn's
strengthening of Wigner's original statement; injectivity is derived inside the proof
(`transProb = 1` forces equality of rays) and surjectivity falls out with the isometry. A
version that assumed a bijection would be strictly weaker and, in the applications this
theorem has (symmetry arguments in quantum foundations), the bijectivity is exactly what one
does not get for free.

## Contents

Definitions (all in `namespace Projectivization`):

- `transProbVec ψ φ = ⟪ψ, φ⟫² / (‖ψ‖² ‖φ‖²)`, with invariance under nonzero scaling in each
  slot;
- `transProb`, the induced function on rays;
- `TransProbPreserving`, the predicate above;
- `projMap e`, the self-map of `ℙ ℝ E` induced by an isometry equivalence — by definition
  `Projectivization.map e.toLinearEquiv.toLinearMap e.injective`.

Results:

- `projMap_transProbPreserving` — isometries preserve transition probabilities;
- `exists_isometry_of_transProbPreserving` — the converse, i.e. the theorem.

## Proof sketch

Elementary and self-contained. No projective topology, no measure theory, no functional
analysis beyond the finite-dimensional inner-product API.

1. **The image of an orthonormal basis is an orthonormal basis.** `transProb = 0` is
   orthogonality of rays and `transProb = 1` is equality of rays, so a preserving map sends
   an orthonormal frame to a pairwise-orthogonal family of rays of full cardinality
   (`imageOrthonormalBasis`, `imgBasis`).
2. **Fix the sign freedom.** Each image basis vector is determined only up to sign. Choosing
   an anchor index `i₀` and testing against the two-slot rays `[b i₀ + b i]` pins the
   relative signs, giving a normalized image basis (`signPattern`, `normBasis`).
3. **Match an arbitrary ray coordinatewise.** For a ray meeting the anchor
   (`⟪ψ̂, b i₀⟫ ≠ 0`) the coordinate moduli transfer from step 1 and the signs from step 2,
   and Cauchy–Schwarz in the equality case identifies the image
   (`eq_projMap_of_anchor`). Rays orthogonal to the anchor are handled by shifting the anchor
   (`eq_projMap_of_anchor_zero`). `eq_projMap` combines the cases and the main theorem
   instantiates it at `stdOrthonormalBasis`.

## Notes for reviewers

**Why not state this over `RCLike`?** The four definitions would generalize mechanically. The
theorem does not: over `ℂ` the conclusion acquires a second, antiunitary branch with no real
counterpart, so a single `RCLike` statement would either weaken the real conclusion or become
a disjunction that is vacuous over `ℝ`. I am happy to generalize the definitions if
maintainers prefer that shape; I have kept them at `ℝ` so that this PR does not fix an API
for a complex case it does not prove. (A complex development exists independently outside
Mathlib; its author should be looped in before the shared API is settled.)

**`projMap`.** It is a definitional abbreviation for `Projectivization.map` applied to an
isometry's underlying linear map. If you would rather have no abbreviation, it can be deleted
and every use rewritten.

**Bibliography.** The module docstring cites Wigner (1959) and Uhlhorn (1963); neither is
currently in `docs/references.bib`, so this PR adds both entries.

## Checklist

- [ ] rebased on current master and re-verified (the file was developed against an older
      pinned Mathlib)
- [ ] `docs/references.bib` entries for `wigner1959`, `uhlhorn1963`
- [ ] file path confirmed with maintainers
- [x] no `sorry`, no custom axioms; closure is `propext`, `Classical.choice`, `Quot.sound`
- [x] zero warnings under `linter.mathlibStandardSet`
