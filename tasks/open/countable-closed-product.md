---
id: countable-closed-product
title: Coordinate sampling, independence of disjoint blocks and the countable closed product
difficulty: medium
kind: interface
labels: []
---

# Coordinate sampling, independence of disjoint blocks and the countable closed product

## Goal
Prove wiki assertion **QH7Q** (article `finite-transcripts`) in full and tag it. The library has
the law of an injectively sampled configuration in `infinitePi` form and independence of one
fixed block from its complement (DYU8), but no statement for arbitrary disjoint families and no
infinite-product formula for the event that a countable set of coordinates is closed.

## Target
Let `I, J` be arbitrary types, `q : I → [0,1]`, `P_q = prodBernoulli q`.
1. **Sampling.** For injective `e : J → I`, the map `ω ↦ {j | e j ∈ ω}` is measurable and pushes
   `P_q` forward to `P_{q ∘ e}`:
   `(prodBernoulli q).map (fun ω => {j | e j ∈ ω}) = prodBernoulli (q ∘ e)`.
2. **Block families.** For any pairwise disjoint family `(S_b)_{b∈B}` of subsets of `I`, the
   restrictions `ω ↦ ω ∩ S_b` (or the maps to `Set S_b`) are mutually independent under `P_q`
   (`ProbabilityTheory.iIndepFun`), hence so are measurable observables of the blocks.
3. **Countable closed product.** For countable `T ⊆ I`,
   `P_q(ω ∩ T = ∅) = ∏_{i∈T} (1 − q_i)`, the product being the limit of finite products along
   any increasing finite exhaustion (state it with `∏'` in `ℝ≥0∞`, or as `⨅` over finite subsets,
   whichever matches mathlib's API best; give both if cheap).
4. **Exponential case.** If moreover `q_i = 1 − e^{−β J_i}` on `T` with finite `β ≥ 0`,
   `J_i ≥ 0` and `Σ_{i∈T} J_i < ∞`, then `P_q(ω ∩ T = ∅) = exp(−β Σ_{i∈T} J_i)`.

Tagged statement: the conjunction of 1-4. Each part is a named area lemma.

Inputs: `prodBernoulli_map_query` (`PercLib/Probability/Exploration/Transcript.lean`) and
`prodBernoulli_map_preimage` (`PercLib/Probability/Transport/Pullback.lean`) for 1 (check whether
1 is already stated there in this form); `disjoint_block_independence` (DYU8)
and the area lemmas behind it for 2, by induction over finite subfamilies; continuity from
above (`MeasureTheory.tendsto_measure_iInter_atTop` or similar) and finite independence for 3.

## Owned files
- `PercLib/Probability/Exploration/Transcript.lean` (append only).
- New `PercLib/Probability/Tags/ClosedProduct.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/{ProdBernoulli,ProdBernoulliIndependence,DeterminedIndependence}.lean`,
`PercLib/Probability/Exploration/*`, `PercLib/Probability/Transport/*`, the area lemmas behind `PercLib/Probability/Tags/Symmetries.lean`,
mathlib; wiki assertions QH7Q, DYU8.

## Stop condition
QH7Q tagged and proved, modules built with `--wfail`; or part of the statement is found false as
written (report it, finish the rest untagged).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
