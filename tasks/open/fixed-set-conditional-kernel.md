---
id: fixed-set-conditional-kernel
title: Explicit conditional kernel given a fixed set of observed coordinates
difficulty: medium
kind: interface
labels: []
---

# Explicit conditional kernel given a fixed set of observed coordinates

## Goal
Prove and tag wiki assertion **D9KI** (article `finite-transcripts`): for a product Bernoulli law
on a countable index set and a deterministic set `S` of observed coordinates, keeping the
observed coordinates and resampling the complement with its original product law is a version
of the conditional law of the full configuration given its restriction to `S`, for finite or
infinite `S`. This complements the finite-transcript results of
`PercLib/Probability/Exploration/Transcript.lean`, which divide by positive probabilities.

## Target
Let `ι` be countable, `q : ι → unitInterval`, `S : Set ι`. Write `μ_S = prodBernoulli (q ∘ (↑) : S → _)`,
`μ_{Sᶜ} = prodBernoulli (q ∘ (↑) : ↥Sᶜ → _)`, `ω|_S = (↑) ⁻¹' ω : Set S`, and for `η : Set S`,
`ξ : Set ↥Sᶜ` the combined configuration `η ⊕ ξ = (↑) '' η ∪ (↑) '' ξ : Set ι`.
1. `K η = μ_{Sᶜ}.map (η ⊕ ·)` defines a Markov kernel from `Set S` to `Set ι`;
2. for all measurable `A ⊆ Set ι` and `B ⊆ Set S`,
   `prodBernoulli q (A ∩ {ω | ω|_S ∈ B}) = ∫⁻ η in B, K η A ∂μ_S`.

Sketch (spelling free):
```lean
theorem prodBernoulli_inter_restrict_preimage [Countable ι] (q : ι → unitInterval) (S : Set ι)
    {A : Set (Set ι)} (hA : MeasurableSet A) {B : Set (Set S)} (hB : MeasurableSet B) :
    prodBernoulli q (A ∩ {ω | ((↑) ⁻¹' ω : Set S) ∈ B}) =
      ∫⁻ η in B, observedKernel q S η A ∂prodBernoulli (fun i : S => q i)
```
together with `IsMarkovKernel (observedKernel q S)`. The kernel and the assembly map are new
definitions (D-24: in the `Defs.lean` file) with their basic API: measurability of assembly and
restriction, `restrict (η ⊕ ξ) = η`, and the two edge cases the article records (`S = ∅` gives the
original law, `S = univ` gives the point mass at the observed configuration). Route, as in the
article: `prodBernoulli q` is the pushforward of `μ_S ⊗ μ_{Sᶜ}` under assembly (compare on
finite cylinders, or through `Measure.infinitePi` and a measurable equivalence
`(ι → Prop) ≃ (S → Prop) × (Sᶜ → Prop)`), then Fubini. Search mathlib for an existing
`infinitePi` splitting lemma before proving one.

## Owned files
- New `PercLib/Probability/ObservedKernel/Defs.lean` (assembly map, kernel, basic API).
- New `PercLib/Probability/ObservedKernel.lean` (area lemmas).
- New `PercLib/Probability/Tags/ObservedKernel.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/ProdBernoulli.lean`, `PercLib/Probability/Exploration/Transcript.lean`,
mathlib (`ProbabilityTheory.Kernel`, `Measure.infinitePi`, `MeasurableEquiv`); wiki assertion
D9KI.

## Stop condition
D9KI tagged, built with `--wfail`; or the statement is found false as written (report it).

## Hand-off
Pull request description: the definitions and the tagged statement in full, the lemmas it
restates, build result.
