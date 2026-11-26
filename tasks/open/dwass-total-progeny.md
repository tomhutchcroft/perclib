---
id: dwass-total-progeny
title: Dwass's formula for the total progeny of a forest with m ancestors
difficulty: hard
kind: interface
labels: []
---

# Dwass's formula for the total progeny of a forest with m ancestors

## Goal
Prove wiki assertion **UPOZ** (article `regular-tree-percolation`) and tag it: the hitting-time
(Dwass) formula `P(T^{(m)} = k) = (m/k) P(ξ₁ + ⋯ + ξ_k = k − m)` for the total progeny of a
Galton–Watson forest with `m ≥ 1` ancestors, for an arbitrary almost surely finite offspring law
(no mean assumption; the total progeny may be infinite). Note the target `k − m`, not `k − 1`.

## Target
Let `ξ₁, ξ₂, …` be independent copies of an `ℕ`-valued offspring variable and `m ≥ 1`. For
every integer `k ≥ m`,
`P(T^{(m)} = k) = (m/k) · P(ξ₁ + ⋯ + ξ_k = k − m)`,
and `P(T^{(m)} = k) = 0` for `k < m`.

**How to state `T^{(m)}`.** The library has no Galton–Watson process. Use the queue
(breadth-first) encoding, which the article's proof gives as an equivalent description: start
with `m` individuals and explore one per step, appending its `ξ_i` children; after `k` steps the
queue has `m + Σ_{i ≤ k} (ξ_i − 1)` individuals, and `T^{(m)}` is the first `k ≥ 1` at which it
is empty (`⊤` if never). Write this inline as an `ℕ∞`-valued hitting time of the integer walk
(no new `def`), and say in the pull request, and in the tagged statement's docstring, that the
forest is represented by this encoding. Sketch (spelling free):
```lean
theorem measure_hittingTime_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ) (hξm : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ P) (hid : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m k : ℕ} (hm : 1 ≤ m) (hk : m ≤ k) :
    (P {ω | IsLeast {j : ℕ | 1 ≤ j ∧
        (m : ℤ) + ∑ i ∈ Finset.range j, ((ξ i ω : ℤ) - 1) = 0} k}).toReal =
      (m / k : ℝ) * (P {ω | ∑ i ∈ Finset.range k, ξ i ω = k - m}).toReal
```
plus the `k < m` case. Two proofs are known: the cycle lemma (Dvoretzky–Motzkin, Kemperman:
if integers `x_i ≥ −1` satisfy `x₁ + ⋯ + x_k = −m`, exactly `m` of the `k` cyclic shifts of
`(x₁, …, x_k)` have partial sums that first reach `−m` at time `k`), applied to `x_i = ξ_i − 1`
and the exchangeability of `(ξ₁, …, ξ_k)`; or the Lagrange inversion argument given in the
article. The cycle-lemma route needs only finite sums and exchangeability and is probably
shorter in Lean. The pinned mathlib has no cycle lemma or ballot theorem under `Mathlib/`
(search again before writing one; a ballot proof exists only in mathlib's `Archive`, which is
not a dependency).

Tagged statement: both cases, for every offspring law.

## Owned files
- New `PercLib/Probability/TotalProgeny.lean` (area lemmas, including any cycle lemma).
- New `PercLib/Probability/Tags/TotalProgeny.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
mathlib (independence, `IdentDistrib`, finite sums); `PercLib/Probability/OffspringTransform.lean`
for context; wiki assertion UPOZ (its proof uses no other assertion). Published source:
M. Dwass, *J. Appl. Probab.* 6 (1969) 682–686.

## Stop condition
UPOZ tagged and proved, modules built with `--wfail`. If the queue encoding is judged not to be a
faithful statement of the assertion, stop and say so in the pull request before proving.

## Hand-off
Pull request description: the tagged statement in full, the encoding of `T^{(m)}` and why it is
the total progeny, the area lemmas, what was searched, build result.
