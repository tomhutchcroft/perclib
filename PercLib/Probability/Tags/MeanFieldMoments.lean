/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the band bound and moment comparison of a cluster volume with a
cubic second moment and tree-graph moment bounds. The statement is proved in the imported
module; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.MeanFieldMoments

/-!
# Mean-field cluster moments: statement form

The theorem restates `measureReal_band_ge_of_tree_graph` and
`exists_moment_comparison_of_tree_graph` from `PercLib.Probability.MeanFieldMoments`.

## Main results

* `band_and_moment_comparison_of_tree_graph`
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal Nat

namespace PercLib.Probability

universe u

/-- Let `T` be positive integer-valued with `χ = E T < ∞`, and suppose `0 < α ≤ 1`,
`E T² ≥ α χ³` and `E T^k ≤ (2k-3)!! χ^{2k-1}` for `k = 1, 2, …`. With `a = E T² / χ` and
`B = 24/α²`, `P(a/2 ≤ T ≤ B χ²) ≥ α⁴ / (576 χ)`. For every fixed real `r ≥ 1`,
`E T^r ≍_{α,r} χ^{2r-1}` and `E T^{r+1} / E T^r ≍_{α,r} χ²`: there are constants `0 < c, C`
depending only on `α` and `r` such that every such `T` satisfies
`c χ^{2r-1} ≤ E T^r ≤ C χ^{2r-1}` and `c χ² ≤ E T^{r+1} / E T^r ≤ C χ²`. -/
@[tag "2DZD"]
theorem band_and_moment_comparison_of_tree_graph :
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℕ),
      Measurable T → (∀ ω, 1 ≤ T ω) → Integrable (fun ω => (T ω : ℝ)) μ →
      ∀ α : ℝ, 0 < α → α ≤ 1 →
      α * (∫ ω, (T ω : ℝ) ∂μ) ^ 3 ≤ ∫ ω, (T ω : ℝ) ^ 2 ∂μ →
      (∀ k : ℕ, 1 ≤ k → ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤
        ENNReal.ofReal ((2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1))) →
      α ^ 4 / (576 * ∫ ω, (T ω : ℝ) ∂μ) ≤
        μ.real {ω | (∫ ω, (T ω : ℝ) ^ 2 ∂μ) / (∫ ω, (T ω : ℝ) ∂μ) / 2 ≤ T ω ∧
          (T ω : ℝ) ≤ 24 / α ^ 2 * (∫ ω, (T ω : ℝ) ∂μ) ^ 2}) ∧
    (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ r : ℝ, 1 ≤ r →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (T : Ω → ℕ), Measurable T → (∀ ω, 1 ≤ T ω) →
        Integrable (fun ω => (T ω : ℝ)) μ →
        α * (∫ ω, (T ω : ℝ) ∂μ) ^ 3 ≤ ∫ ω, (T ω : ℝ) ^ 2 ∂μ →
        (∀ k : ℕ, 1 ≤ k → ∫⁻ ω, (T ω : ℝ≥0∞) ^ k ∂μ ≤
          ENNReal.ofReal ((2 * k - 3)‼ * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * k - 1))) →
        c * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * r - 1) ≤ ∫ ω, (T ω : ℝ) ^ r ∂μ ∧
        ∫ ω, (T ω : ℝ) ^ r ∂μ ≤ C * (∫ ω, (T ω : ℝ) ∂μ) ^ (2 * r - 1) ∧
        c * (∫ ω, (T ω : ℝ) ∂μ) ^ 2 ≤
          (∫ ω, (T ω : ℝ) ^ (r + 1) ∂μ) / ∫ ω, (T ω : ℝ) ^ r ∂μ ∧
        (∫ ω, (T ω : ℝ) ^ (r + 1) ∂μ) / ∫ ω, (T ω : ℝ) ^ r ∂μ ≤
          C * (∫ ω, (T ω : ℝ) ∂μ) ^ 2) :=
  ⟨fun μ _ _T hT hT1 hint _α hα0 _ h2 hk =>
      measureReal_band_ge_of_tree_graph (μ := μ) hT hT1 hint hα0 h2 hk,
    fun _α hα0 _ _r hr => exists_moment_comparison_of_tree_graph hα0 hr⟩

end PercLib.Probability
