/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for convex comparison under negative quadrant dependence with
preceding sums. All mathematical inputs come from the imported modules; no source proof is
copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.ConvexComparison

/-!
# Convex comparison for integrable increments: correspondence

Wiki correspondence for the convex comparison of a sum whose increments are negatively
quadrant dependent with their preceding sums against the sum of independent copies.

## Main results

* `convex_comparison_and_hinge_and_central_moment_of_tail_le`
* `ae_summable_and_convex_comparison_tsum_of_tail_le`
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set Filter
open scoped NNReal Topology

namespace PercLib.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Let `Z₀, …, Z_{n-1}` be integrable real random variables with
`P(S_i ≥ u, Z_i ≥ v) ≤ P(S_i ≥ u) P(Z_i ≥ v)` for `1 ≤ i < n` and all real `u, v`, where
`S_i = Z₀ + ⋯ + Z_{i-1}`, and let `Z'_i` be independent with the same respective laws. Then
for every convex `φ : ℝ → ℝ`, `E φ(S_n) ≤ E φ(S'_n)` with both expectations well defined in
`(-∞, ∞]` (negative parts integrable; if the right side is finite so is the left, and the
inequality holds). In particular `E (S_n - a)₊ ≤ E (S'_n - a)₊` for real `a`, and
`E |S_n - E S_n|^r ≤ E |S'_n - E S'_n|^r` for `r ≥ 1`. -/
@[tag "3NBK"]
theorem convex_comparison_and_hinge_and_central_moment_of_tail_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ}
    {Z' : ℕ → Ω' → ℝ} {n : ℕ} (hZm : ∀ i < n, Measurable (Z i))
    (hZ : ∀ i < n, Integrable (Z i) μ) (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i)) :
    (∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ →
      Integrable (fun ω => (φ (∑ i ∈ range n, Z i ω))⁻) μ ∧
        Integrable (fun ω => (φ (∑ i ∈ range n, Z' i ω))⁻) μ' ∧
        (Integrable (fun ω => φ (∑ i ∈ range n, Z' i ω)) μ' →
          Integrable (fun ω => φ (∑ i ∈ range n, Z i ω)) μ ∧
            ∫ ω, φ (∑ i ∈ range n, Z i ω) ∂μ ≤ ∫ ω, φ (∑ i ∈ range n, Z' i ω) ∂μ')) ∧
      (∀ a : ℝ, ∫ ω, max (∑ i ∈ range n, Z i ω - a) 0 ∂μ ≤
        ∫ ω, max (∑ i ∈ range n, Z' i ω - a) 0 ∂μ') ∧
      ∀ r : ℝ, 1 ≤ r →
        ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range n, Z i ω - ∫ ω', ∑ i ∈ range n, Z i ω' ∂μ| ^ r)
            ∂μ ≤
          ∫⁻ ω, ENNReal.ofReal
            (|∑ i ∈ range n, Z' i ω - ∫ ω', ∑ i ∈ range n, Z' i ω' ∂μ'| ^ r) ∂μ' :=
  ⟨fun _ hφ => convex_comparison_sum_of_tail_le hZm hZ hZ'm htail hind hlaw hφ,
    integral_max_sub_le_of_tail_le hZm hZ hZ'm htail hind hlaw,
    fun _ hr => lintegral_abs_sub_integral_rpow_le_of_tail_le hZm hZ hZ'm htail hind hlaw hr⟩

/-- Let `(Z_i)_{i ≥ 0}` satisfy the negative quadrant dependence with preceding sums at every
finite index, with `∑ E |Z_i| < ∞`, and let `Z'_i` be independent with the same respective
laws. Then both series converge absolutely almost surely and in `L¹`, their sums `S` and `S'`
are integrable with the same mean, `E φ(S) ≤ E φ(S')` in `(-∞, ∞]` for every convex `φ`, and
for every real `t` and `r ≥ 1`, `E e^{t(S - E S)} ≤ E e^{t(S' - E S')}` and
`E |S - E S|^r ≤ E |S' - E S'|^r`. -/
@[tag "OCZT"]
theorem ae_summable_and_convex_comparison_tsum_of_tail_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, Integrable (Z i) μ) (hZ'm : ∀ i, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ) (hind : iIndepFun Z' μ')
    (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i)) :
    ((∀ᵐ ω ∂μ, Summable fun i => |Z i ω|) ∧ Integrable (fun ω => ∑' i, Z i ω) μ ∧
      Tendsto (fun n => ∫ ω, |∑ i ∈ range n, Z i ω - ∑' i, Z i ω| ∂μ) atTop (𝓝 0)) ∧
    ((∀ᵐ ω ∂μ', Summable fun i => |Z' i ω|) ∧ Integrable (fun ω => ∑' i, Z' i ω) μ' ∧
      Tendsto (fun n => ∫ ω, |∑ i ∈ range n, Z' i ω - ∑' i, Z' i ω| ∂μ') atTop (𝓝 0)) ∧
    ∫ ω, ∑' i, Z i ω ∂μ = ∫ ω, ∑' i, Z' i ω ∂μ' ∧
    (∀ φ : ℝ → ℝ, ConvexOn ℝ univ φ →
      Integrable (fun ω => (φ (∑' i, Z i ω))⁻) μ ∧
        Integrable (fun ω => (φ (∑' i, Z' i ω))⁻) μ' ∧
        (Integrable (fun ω => φ (∑' i, Z' i ω)) μ' →
          Integrable (fun ω => φ (∑' i, Z i ω)) μ ∧
            ∫ ω, φ (∑' i, Z i ω) ∂μ ≤ ∫ ω, φ (∑' i, Z' i ω) ∂μ')) ∧
    (∀ t : ℝ,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (∑' i, Z i ω - ∫ ω', ∑' i, Z i ω' ∂μ))) ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (∑' i, Z' i ω - ∫ ω', ∑' i, Z' i ω' ∂μ'))) ∂μ') ∧
    ∀ r : ℝ, 1 ≤ r →
      ∫⁻ ω, ENNReal.ofReal (|∑' i, Z i ω - ∫ ω', ∑' i, Z i ω' ∂μ| ^ r) ∂μ ≤
        ∫⁻ ω, ENNReal.ofReal (|∑' i, Z' i ω - ∫ ω', ∑' i, Z' i ω' ∂μ'| ^ r) ∂μ' :=
  ⟨ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ hsum,
    ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum
      (fun i => integrable_of_map_eq (hZm i) (hZ'm i) (hZ i) (hlaw i))
      (summable_integral_abs_of_map_eq hZm hZ'm hsum hlaw),
    integral_tsum_eq_of_map_eq hZm hZ hZ'm hsum hlaw,
    fun _ hφ => convex_comparison_tsum_of_tail_le hZm hZ hZ'm htail hsum hind hlaw hφ,
    lintegral_exp_mul_sub_integral_le_of_tail_le hZm hZ hZ'm htail hsum hind hlaw,
    fun _ hr =>
      lintegral_abs_sub_integral_tsum_rpow_le_of_tail_le hZm hZ hZ'm htail hsum hind hlaw hr⟩

end PercLib.Probability
