---
id: boolean-coefficient-cone
title: Set functions with nonnegative Möbius coefficients form a closed cone
difficulty: medium
kind: interface
labels: []
---

# Set functions with nonnegative Möbius coefficients form a closed cone

## Goal
Prove wiki assertion **CUE4** (article `adaptive-three-point`) and tag it. It is pure
combinatorics on a finite Boolean lattice: the cone of set functions whose Möbius coefficients
are nonnegative is closed under sums, products, restriction and coordinate differences. Three
further assertions of the article build on it.

## Target
Fix a finite set `E` (a `Finset α`). Let `𝒞_E` be the set of `f` on subsets of `E` of the form
`f(S) = Σ_{T ⊆ S} a_T` with all `a_T ≥ 0`.
1. The coefficients are unique, and `a_T = Σ_{U ⊆ T} (−1)^{|T \ U|} f(U)` for `T ⊆ E`.
2. `𝒞_E` is closed under nonnegative linear combinations and under pointwise products.
3. For `e ∈ E`, the two restrictions `f⁻(S) = f(S)` and `f⁺(S) = f(S ∪ {e})`, for
   `S ⊆ E \ {e}`, and the difference `f⁺ − f⁻` all lie in `𝒞_{E \ {e}}`.

Write membership in `𝒞_E` inline (no new `def`), for example:
```lean
∃ a : Finset α → ℝ, (∀ T ⊆ E, 0 ≤ a T) ∧ ∀ S ⊆ E, f S = ∑ T ∈ S.powerset, a T
```
Sketch of one area lemma:
```lean
theorem mem_cone_mul {E : Finset α} {f g : Finset α → ℝ}
    (hf : ∃ a : Finset α → ℝ, (∀ T ⊆ E, 0 ≤ a T) ∧ ∀ S ⊆ E, f S = ∑ T ∈ S.powerset, a T)
    (hg : ∃ b : Finset α → ℝ, (∀ T ⊆ E, 0 ≤ b T) ∧ ∀ S ⊆ E, g S = ∑ T ∈ S.powerset, b T) :
    ∃ c : Finset α → ℝ, (∀ T ⊆ E, 0 ≤ c T) ∧ ∀ S ⊆ E, f S * g S = ∑ T ∈ S.powerset, c T
```
Search first: mathlib's incidence algebra and Möbius inversion
(`Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean`), `Finset.sum_powerset_neg_one_pow_card`
(`Mathlib/Data/Nat/Choose/Sum.lean`), and the inclusion–exclusion files. Use what exists. If a
definition of the cone would be used a third time, propose it in the pull request instead of
adding it.

## Owned files
- New `PercLib/Combinatorics/BooleanCoefficients.lean` (area lemmas).
- New `PercLib/Combinatorics/Tags/BooleanCoefficients.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
mathlib; wiki assertion CUE4 (its proof uses no other assertion).

## Stop condition
CUE4 tagged and proved, modules built with `--wfail`; or the statement is found false as
written (report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
