/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for sampled-root window moments and for the product and covariance
chains of two cluster functionals. All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterCorrelation.FunctionalChain
public import PercLib.Percolation.Bond.Tightness.Hyperscaling

/-!
# Sampled-root window moments and cluster functional chains: correspondence

Wiki correspondence for the moments of the window intersection at a uniformly sampled root
(any measure on configurations, real exponent) and for the product and covariance bounds of
functionals of two clusters in the countable product model.

## Main results

* `lintegral_avg_rpow_clusterIntersection_and_window_bounds`
* `cluster_functional_product_and_covariance_chains`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

open Classical in
/-- **Finite-window cluster moments under uniform root sampling.** For any measure `μ` on
configurations, a finite `Λ`, and `U` uniform on `Λ` independent of the graph (the average
over `u ∈ Λ` inside the expectation), `X = |K_U ∩ Λ|` and the traces `D` of the clusters
on `Λ` (full-graph connectivity): for real `m ≥ 0`, `E X^m = |Λ|⁻¹ E ∑_D |D|^(m+1)`, and,
with `N` the number of traces with `a v ≤ |D| ≤ b v`,
`(a v)^(m+1) / |Λ| · E N ≤ E[X^m 1{a v ≤ X ≤ b v}] ≤ (b v)^(m+1) / |Λ| · E N`. -/
@[tag "OB0A"]
theorem lintegral_avg_rpow_clusterIntersection_and_window_bounds [Countable V]
    (μ : Measure (Config V)) (Λ : Finset V) {m : ℝ} (hm : 0 ≤ m) (a b v : ℝ) :
    ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ, (clusterIntersection Λ ω u : ℝ≥0∞) ^ m ∂μ =
        (Λ.card : ℝ≥0∞)⁻¹ * ∫⁻ ω, ∑ D ∈ Λ.image (fun x => Λ.filter (· ∈ cluster ω x)),
          (D.card : ℝ≥0∞) ^ (m + 1) ∂μ ∧
      ENNReal.ofReal (a * v) ^ (m + 1) / Λ.card *
          ∫⁻ ω, (((Λ.image fun x => Λ.filter (· ∈ cluster ω x)).filter
            fun D => a * v ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ b * v).card : ℝ≥0∞) ∂μ ≤
        ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ,
          (if a * v ≤ (clusterIntersection Λ ω u : ℝ) ∧
              (clusterIntersection Λ ω u : ℝ) ≤ b * v
            then (clusterIntersection Λ ω u : ℝ≥0∞) ^ m else 0) ∂μ ∧
      ∫⁻ ω, (Λ.card : ℝ≥0∞)⁻¹ * ∑ u ∈ Λ,
          (if a * v ≤ (clusterIntersection Λ ω u : ℝ) ∧
              (clusterIntersection Λ ω u : ℝ) ≤ b * v
            then (clusterIntersection Λ ω u : ℝ≥0∞) ^ m else 0) ∂μ ≤
        ENNReal.ofReal (b * v) ^ (m + 1) / Λ.card *
          ∫⁻ ω, (((Λ.image fun x => Λ.filter (· ∈ cluster ω x)).filter
            fun D => a * v ≤ (D.card : ℝ) ∧ (D.card : ℝ) ≤ b * v).card : ℝ≥0∞) ∂μ :=
  ⟨lintegral_avg_rpow_clusterIntersection μ Λ hm,
    rpow_div_mul_lintegral_card_le_window μ Λ hm a b v,
    window_le_rpow_div_mul_lintegral_card μ Λ hm a b v⟩

/-- **Distinct-cluster product and covariance bounds without finite clusters or finite
susceptibility.** In the countable product model, for `F G : Set V → ℝ≥0∞` with measurable
cluster evaluations and `G` increasing:
`E[F(K_x) G(K_y) 1{x ↮ y}] ≤ E[F(K_x) 1{x ↮ y}] E G(K_y) ≤ E F(K_x) E G(K_y)`
(infinite values allowed). If also `F` is increasing,
`E F E G ≤ E[F G] ≤ E F E G + E[F G 1{x ↔ y}]`, and when `E[F G]`, `E F`, `E G` are finite,
`0 ≤ Cov(F(K_x), G(K_y)) ≤ E[F G 1{x ↔ y}]`. -/
@[tag "UXBN"]
theorem cluster_functional_product_and_covariance_chains [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (F G : Set V → ℝ≥0∞) (hG : Monotone G)
    (hFm : Measurable fun ω : Config V => F (cluster ω x))
    (hGm : Measurable fun ω : Config V => G (cluster ω y)) :
    (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q ≤
        (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
          ∫⁻ ω, G (cluster ω y) ∂law q ∧
      (∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x)) ω ∂law q) *
          ∫⁻ ω, G (cluster ω y) ∂law q ≤
        (∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q) ∧
    (Monotone F →
      ((∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) ≤
          ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ∧
        ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≤
          (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) +
            ∫⁻ ω, (conn x y).indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω
              ∂law q) ∧
      (∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≠ ⊤ →
        ∫⁻ ω, F (cluster ω x) ∂law q ≠ ⊤ → ∫⁻ ω, G (cluster ω y) ∂law q ≠ ⊤ →
        0 ≤ cov[fun ω => (F (cluster ω x)).toReal, fun ω => (G (cluster ω y)).toReal;
            law q] ∧
          cov[fun ω => (F (cluster ω x)).toReal, fun ω => (G (cluster ω y)).toReal;
              law q] ≤
            (∫⁻ ω, (conn x y).indicator
              (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q).toReal)) :=
  ⟨lintegral_indicator_compl_conn_mul_le_mul_le q x y F G hG hFm hGm, fun hF =>
    ⟨lintegral_mul_lintegral_le_lintegral_mul_le_add q x y F G hF hG hFm hGm,
      covariance_cluster_nonneg_and_le q x y F G hF hG hFm hGm⟩⟩

end PercLib.Percolation.Bond
