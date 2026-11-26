/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the comparison of predictable sampling trees with product laws.
Mathematical reference: N. Gladkov, Percolation inequalities and decision trees,
arXiv:2408.08457v1, Main Lemma 8.1. Every statement is assembled from lemmas proved in the
imported module; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.SectionComparison

/-!
# Section comparison for predictable sampling trees: statement form

The theorem restates, as one conjunction, the lower and upper bounds proved under their own
names in `PercLib.Probability.SectionComparison`.

## Main results

* `measure_pi_le_samplingTree_law_le_measure_pi`
-/

@[expose] public section

open MeasureTheory Finset Function
open scoped ENNReal

namespace PercLib.Probability

/-- Let `E` be finite and, for every `e`, let `μ e, ν e` be probability laws on a finite
alphabet `Ω e`. If `A` satisfies `∑ u, μ e u 1_A(z, u) ≤ ∑ u, ν e u 1_A(z, u)` for every `e`
and every assignment `z` off `e` (here `z[e ↦ u]`), then for every predictable sampling tree,
chosen by an independent seed `i ∼ σ`, the resulting configuration `Z` satisfies
`(⊗ μ)(A) ≤ P(Z ∈ A) ≤ (⊗ ν)(A)`. The tree assigns every coordinate exactly once, each from the
law (`μ e` or `ν e`) it chooses; the starting configuration `x` is overwritten everywhere. -/
@[tag "9GXY"]
theorem measure_pi_le_samplingTree_law_le_measure_pi {E : Type*} [Fintype E] [DecidableEq E]
    {Ω : E → Type*} [∀ e, Fintype (Ω e)] [∀ e, MeasurableSpace (Ω e)]
    [∀ e, MeasurableSingletonClass (Ω e)] (μ ν : ∀ e, PMF (Ω e)) (A : Set (∀ e, Ω e))
    (hsec : ∀ (e : E) (z : ∀ e, Ω e),
      ∑ u, μ e u * A.indicator 1 (update z e u) ≤ ∑ u, ν e u * A.indicator 1 (update z e u))
    {ι : Type*} (σ : PMF ι) (t : ι → SamplingTree Ω (univ : Finset E)) (x : ∀ e, Ω e) :
    Measure.pi (fun e => (μ e).toMeasure) A ≤ (σ.bind fun i => (t i).law μ ν x).toMeasure A ∧
      (σ.bind fun i => (t i).law μ ν x).toMeasure A ≤ Measure.pi (fun e => (ν e).toMeasure) A :=
  ⟨SamplingTree.measure_pi_le_toMeasure_bind_law μ ν σ t x A hsec,
    SamplingTree.toMeasure_bind_law_le_measure_pi μ ν σ t x A hsec⟩

end PercLib.Probability
