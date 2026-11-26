/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The restoration map and the targets of Lemmas I.2.1 and I.4.12 of T. Hutchcroft, *Critical
long-range percolation I*, arXiv:2508.18807v1, on the bond interface.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Correlation/TwoClusterGap.lean` (`restoreMap`, and the statement of
`longRange_twoCluster_gap_le`) and `PercLib/CriticalLRP/Correlation/Hrest.lean` (the statements of
`twoCluster_ennreal`, `fkg_functional_ennreal`, `hrest_generic`); licence Apache-2.0 as declared in
those file headers; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Modified: the edge-labelled `BondGraph`/`edgeLaw` model
and the hypothesis `∀ e, p e < 1` are replaced by `law q` on `Set (Sym2 V)` with an arbitrary
profile; the restoration map reads the cluster from its first argument; the three-point tree-graph
hypothesis of Lemma I.4.12 is dropped from the target, since it is itself the target
`TreeGraphInequality`. The witnesses below are new.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Correlation inequalities for clusters: interface

The restoration map of the proof of Lemma I.4.12 and four propositions to prove
(`def … : Prop`, asserting nothing): the BK inequality for functionals of disjoint
clusters, the Harris inequality and the covariance upper bound for cluster functionals
(Lemma I.2.1), and the two-cluster gap inequality (Lemma I.4.12).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The **restoration map** of the proof of Lemma I.4.12: from a pair `(ω, ω')`, keep `ω`
on the pairs with an endpoint in the cluster `cluster ω o`, and `ω'` on all other pairs. -/
def restoreMap (o : V) (p : Config V × Config V) : Config V :=
  {e | e ∈ p.1 ∧ ∃ v ∈ e, v ∈ cluster p.1 o} ∪ {e | e ∈ p.2 ∧ ¬∃ v ∈ e, v ∈ cluster p.1 o}

/-- **Lemma I.2.1(i)**, BK for disjoint clusters: for increasing functionals `F, G` of
the clusters of `x` and `y`,
`∫ 1{x ↮ y} F(K_x) G(K_y) ≤ (∫ F(K_x)) (∫ G(K_y))`. A proposition to prove. -/
def DisjointClusterBK (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (x y : V) (F G : Set V → ℝ≥0∞), Monotone F → Monotone G →
    Measurable (fun ω : Config V => F (cluster ω x)) →
    Measurable (fun ω : Config V => G (cluster ω y)) →
    ∫⁻ ω, (conn x y)ᶜ.indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q ≤
      (∫⁻ ω, F (cluster ω x) ∂law q) * ∫⁻ ω, G (cluster ω y) ∂law q

/-- **Lemma I.2.1(ii)**, the lower covariance comparison (Harris): for increasing
functionals, `(∫ F(K_x)) (∫ G(K_y)) ≤ ∫ F(K_x) G(K_y)`. A proposition to prove. -/
def ClusterFunctionalHarris (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (x y : V) (F G : Set V → ℝ≥0∞), Monotone F → Monotone G →
    Measurable (fun ω : Config V => F (cluster ω x)) →
    Measurable (fun ω : Config V => G (cluster ω y)) →
    (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) ≤
      ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q

/-- **Lemma I.2.1(iii)**, the upper covariance comparison: for increasing functionals,
`∫ F(K_x) G(K_y) ≤ (∫ F(K_x)) (∫ G(K_y)) + ∫ 1{x ↔ y} F(K_x) G(K_y)`, the `ℝ≥0∞` form of
`Cov(F(K_x), G(K_y)) ≤ E[F(K_x) G(K_y) 1{x ↔ y}]`. A proposition to prove. -/
def ClusterCovarianceUpper (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (x y : V) (F G : Set V → ℝ≥0∞), Monotone F → Monotone G →
    Measurable (fun ω : Config V => F (cluster ω x)) →
    Measurable (fun ω : Config V => G (cluster ω y)) →
    ∫⁻ ω, F (cluster ω x) * G (cluster ω y) ∂law q ≤
      (∫⁻ ω, F (cluster ω x) ∂law q) * (∫⁻ ω, G (cluster ω y) ∂law q) +
        ∫⁻ ω, (conn x y).indicator (fun ω => F (cluster ω x) * G (cluster ω y)) ω ∂law q

/-- **Lemma I.4.12**, the two-cluster gap inequality, for every profile:
`τ(o,x) τ(y,z) ≤ P(o ↔ x, y ↔ z, o ↮ y) + ∑_{a,b} τ(o,a) τ(a,x) τ(a,b) τ(y,b) τ(b,z)`.
A proposition to prove. -/
def TwoClusterGap (V : Type*) [Countable V] : Prop :=
  ∀ (q : Sym2 V → unitInterval) (o x y z : V),
    tau q o x * tau q y z ≤ law q (conn o x ∩ conn y z ∩ (conn o y)ᶜ) +
      ∑' a, ∑' b, tau q o a * tau q a x * tau q a b * tau q y b * tau q b z

/-! ### API -/

theorem mem_restoreMap {o : V} {p : Config V × Config V} {e : Sym2 V} :
    e ∈ restoreMap o p ↔ (e ∈ p.1 ∧ ∃ v ∈ e, v ∈ cluster p.1 o) ∨
      (e ∈ p.2 ∧ ¬∃ v ∈ e, v ∈ cluster p.1 o) := Iff.rfl

/-- The restoration map is measurable. -/
theorem measurable_restoreMap [Countable V] (o : V) :
    Measurable (restoreMap (V := V) o) := by
  refine Measurable.of_mem fun e => measurableSet_setOfPred.1 ?_
  have hT : MeasurableSet {p : Config V × Config V | ∃ v ∈ e, v ∈ cluster p.1 o} := by
    have : {p : Config V × Config V | ∃ v ∈ e, v ∈ cluster p.1 o} =
        ⋃ v ∈ {v | v ∈ e}, Prod.fst ⁻¹' conn o v := by
      ext p; simp [cluster, conn]
    rw [this]
    exact MeasurableSet.biUnion (to_countable _) fun v _ =>
      measurable_fst (measurableSet_conn o v)
  have h1 : MeasurableSet {p : Config V × Config V | e ∈ p.1} :=
    measurable_fst (measurableSet_setOfPred.2 (measurable_set_mem e))
  have h2 : MeasurableSet {p : Config V × Config V | e ∈ p.2} :=
    measurable_snd (measurableSet_setOfPred.2 (measurable_set_mem e))
  exact (h1.inter hT).union (h2.inter hT.compl)

/-- The restoration map agrees with its first argument on the pairs touching the cluster. -/
theorem mem_restoreMap_of_touch {o : V} {p : Config V × Config V} {e : Sym2 V}
    (h : ∃ v ∈ e, v ∈ cluster p.1 o) : e ∈ restoreMap o p ↔ e ∈ p.1 := by
  simp only [mem_restoreMap, h, not_true_eq_false, and_false, or_false, and_true]

/-- The restoration map agrees with its second argument off the pairs touching the cluster. -/
theorem mem_restoreMap_of_not_touch {o : V} {p : Config V × Config V} {e : Sym2 V}
    (h : ¬∃ v ∈ e, v ∈ cluster p.1 o) : e ∈ restoreMap o p ↔ e ∈ p.2 := by
  simp only [mem_restoreMap, h, not_false_eq_true, and_false, false_or, and_true]

/-- The restoration map does not change a configuration paired with itself. -/
theorem restoreMap_self (o : V) (ω : Config V) : restoreMap o (ω, ω) = ω := by
  ext e
  by_cases h : ∃ v ∈ e, v ∈ cluster ω o
  · exact mem_restoreMap_of_touch h
  · exact mem_restoreMap_of_not_touch h

/-! ### Witnesses

The targets have no hypotheses beyond the monotonicity and measurability of `F` and `G`;
the witnesses check the constant functionals and, for Lemma I.4.12, the case `y = o`. -/

/-- Lemma I.2.1(i) at `F = G = 1`. -/
example [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    ∫⁻ ω, (conn x y)ᶜ.indicator (fun _ => (1 : ℝ≥0∞) * 1) ω ∂law q ≤
      (∫⁻ _ω, (1 : ℝ≥0∞) ∂law q) * ∫⁻ _ω, (1 : ℝ≥0∞) ∂law q := by
  calc _ ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂law q := lintegral_mono fun ω => by
          by_cases h : ω ∈ (conn x y)ᶜ <;> simp [h]
    _ = _ := by simp

/-- Lemma I.2.1(ii) and (iii) at `F = G = 1`. -/
example [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    (∫⁻ _ω, (1 : ℝ≥0∞) ∂law q) * (∫⁻ _ω, (1 : ℝ≥0∞) ∂law q) ≤ ∫⁻ _ω, 1 * 1 ∂law q ∧
      ∫⁻ _ω, (1 : ℝ≥0∞) * 1 ∂law q ≤ (∫⁻ _ω, (1 : ℝ≥0∞) ∂law q) * (∫⁻ _ω, 1 ∂law q) +
        ∫⁻ ω, (conn x y).indicator (fun _ => (1 : ℝ≥0∞) * 1) ω ∂law q := by
  simp

/-- Lemma I.4.12 holds when `y = o`: the summand `a = b = o` already bounds the left side. -/
theorem twoClusterGap_of_eq (q : Sym2 V → unitInterval) (o x z : V) :
    tau q o x * tau q o z ≤ law q (conn o x ∩ conn o z ∩ (conn o o)ᶜ) +
      ∑' a, ∑' b, tau q o a * tau q a x * tau q a b * tau q o b * tau q b z := by
  refine le_add_left (le_trans ?_ (ENNReal.le_tsum o))
  refine le_trans ?_ (ENNReal.le_tsum (f := fun b =>
    tau q o o * tau q o x * tau q o b * tau q o b * tau q b z) o)
  simp [tau_self]

example [Countable V] (q : Sym2 V → unitInterval) (o x z : V) :
    tau q o x * tau q o z ≤ law q (conn o x ∩ conn o z ∩ (conn o o)ᶜ) +
      ∑' a, ∑' b, tau q o a * tau q a x * tau q a b * tau q o b * tau q b z :=
  twoClusterGap_of_eq q o x z

end PercLib.Percolation.Bond
