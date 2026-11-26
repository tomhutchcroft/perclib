/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs of Lemma I.2.1 (i)–(iii) of T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, the targets `DisjointClusterBK`, `ClusterFunctionalHarris` and
`ClusterCovarianceUpper` of `PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean`. The statements
come from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files `PercLib/CriticalLRP/BK/FunctionalIndicator.lean`,
`PercLib/CriticalLRP/BK/FunctionalFromBelow.lean`,
`PercLib/CriticalLRP/BK/FunctionalInterface.lean`, `PercLib/CriticalLRP/BK/BorelReduction.lean` and
`PercLib/CriticalLRP/Correlation/Hrest.lean`; licence Apache-2.0 as declared in those file headers
and `third_party/critical-lrp/NOTICE.md`; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified). Contributor: yujinhkim. The
proofs are new: (i) uses the restoration map (`map_restoreMap`) instead of the source's BK route, so
neither the source's continuity-from-below hypothesis nor `p < 1` is needed; (ii) is Harris for
increasing `ℝ≥0∞`-valued functions, `prodBernoulli_lintegral_mul_le`.
-/
module

public import PercLib.Percolation.Bond.ClusterCorrelation.Restoration
public import PercLib.Probability.HarrisDecreasing

/-! # Lemma I.2.1: BK, Harris and the covariance bound for cluster functionals

* `disjointClusterBK` (I.2.1(i)): for `ω̃ = restoreMap x (ω, ω')` (law `μ`), the cluster of
  `x` is that of `ω`, and on `{x ↮ y}` the cluster of `y` is inside the cluster of `y` in
  the independent `ω'`; monotonicity of `G` gives the bound.
* `clusterFunctionalHarris` (I.2.1(ii)), `clusterCovarianceUpper` (I.2.1(iii)).

No hypothesis beyond monotonicity and measurability of `F` and `G` is used; in particular
the continuity from below assumed by the source formalisation is not needed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal
open PercLib.Probability

namespace PercLib.Percolation.Bond

/-! ### Lemma I.2.1 -/

variable {V : Type*}

/-- **Lemma I.2.1(i).** -/
theorem disjointClusterBK [Countable V] : DisjointClusterBK V := by
  intro q x y F G hF hG hFm hGm
  have hm : Measurable fun ω : Config V =>
      (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω :=
    (hFm.mul hGm).indicator (measurableSet_conn x y).compl
  calc ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q
      = ∫⁻ p, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y))
          (restoreMap x p) ∂((law q).prod (law q)) := by
        conv_lhs => rw [← map_restoreMap q x]
        exact lintegral_map hm (measurable_restoreMap x)
    _ ≤ ∫⁻ p, F (cluster p.1 x) * G (cluster p.2 y) ∂((law q).prod (law q)) := by
        refine lintegral_mono fun p => ?_
        by_cases hc : restoreMap x p ∈ conn x y
        · rw [indicator_of_notMem (Set.notMem_compl_iff.2 hc)]
          exact zero_le
        · rw [indicator_of_mem hc, cluster_restoreMap]
          have hy : y ∉ cluster p.1 x := by
            rw [← cluster_restoreMap x p]; exact hc
          exact mul_le_mul' le_rfl (hG fun w hw => (cluster_restoreMap_subset_snd hy hw).1)
    _ = (∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q :=
        lintegral_prod_mul hFm.aemeasurable hGm.aemeasurable

/-- **Lemma I.2.1(ii).** -/
theorem clusterFunctionalHarris [Countable V] : ClusterFunctionalHarris V := by
  intro q x y F G hF hG hFm hGm
  exact prodBernoulli_lintegral_mul_le q (fun ω ω' h => hF (cluster_mono h x))
    (fun ω ω' h => hG (cluster_mono h y)) hFm hGm

/-- **Lemma I.2.1(iii).** -/
theorem clusterCovarianceUpper [Countable V] : ClusterCovarianceUpper V := by
  intro q x y F G hF hG hFm hGm
  have hc := measurableSet_conn (V := V) x y
  have hsplit : ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q =
      ∫⁻ ω, (conn x y).indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q +
        ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q := by
    rw [lintegral_indicator hc, lintegral_indicator hc.compl, lintegral_add_compl _ hc]
  rw [hsplit, add_comm]
  exact add_le_add (disjointClusterBK q x y F G hF hG hFm hGm) le_rfl

/-! ### Witnesses -/

/-- `F = G = |·|` (the cluster volume) on `Bool`: the three inequalities hold. -/
example (q : Sym2 Bool → unitInterval) :
    ∫⁻ ω, (conn false true)ᶜ.indicator (fun ω => ((cluster ω false).encard : ℝ≥0∞) *
        (cluster ω true).encard) ω ∂law q ≤
      (∫⁻ ω, ((cluster ω false).encard : ℝ≥0∞) ∂law q) *
        ∫⁻ ω, ((cluster ω true).encard : ℝ≥0∞) ∂law q :=
  disjointClusterBK q false true (fun S => (S.encard : ℝ≥0∞)) (fun S => (S.encard : ℝ≥0∞))
    (fun _ _ h => ENat.toENNReal_le.2 (Set.encard_le_encard h))
    (fun _ _ h => ENat.toENNReal_le.2 (Set.encard_le_encard h))
    (measurable_from_top.comp (measurable_encard_cluster false))
    (measurable_from_top.comp (measurable_encard_cluster true))

example (q : Sym2 Bool → unitInterval) :=
  clusterCovarianceUpper q false true (fun _ => (1 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞))
    monotone_const monotone_const measurable_const measurable_const

end PercLib.Percolation.Bond
