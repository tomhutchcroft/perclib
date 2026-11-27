/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs using the existing finite-volume spatial-moment derivative and finite-cluster
domain Markov property. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Percolation.Bond.SpatialMoments.Derivative

/-!
# Finite-volume Russo identity as a boundary expectation

The finite susceptibility derivative equals the expected boundary susceptibility of the
root cluster. The proof retains the closed-boundary indicator in the existing exact Russo
formula, then uses the domain Markov property on each possible root cluster.

## Main results

* `law_cluster_eq_inter_conn`: conditioned on a specified finite root cluster, connections
  outside it have their unconditioned complementary-domain probability.
* `integral_boundarySusceptibility_eq_sum_cluster`: the boundary expectation equals the
  directed cluster increment in the finite-volume Russo formula.
* `hasDerivAt_toReal_chi_eq_integral_boundarySusceptibility`: the actual canonical intensity
  law satisfies the finite-volume derivative identity, with coefficient one.

Finite vertex domains are covered by applying the theorem to the domain subtype and its
restricted intensity kernel. The boundary susceptibility is then computed in that subtype;
it does not include exits outside the finite domain. No infinite-volume limit is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A connection starting outside a specified root cluster stays in its complement. -/
theorem mem_conn_iff_mem_localConn_compl_of_cluster_eq {ω : Config V} {o y z : V}
    {C : Set V} (hC : cluster ω o = C) (hy : y ∉ C) :
    ω ∈ conn y z ↔ ω ∈ localConn Cᶜ y z := by
  classical
  constructor
  · rintro ⟨w⟩
    have hw : ∀ a ∈ w.support, a ∈ Cᶜ := by
      intro a ha hCa
      have hoa : ω ∈ conn o a := by
        change a ∈ cluster ω o
        rwa [hC]
      have hya : ω ∈ conn y a := ⟨w.takeUntil a ha⟩
      apply hy
      rw [← hC]
      exact conn_trans hoa (by rw [conn_symm]; exact hya)
    exact ⟨hy, hw z w.end_mem_support, ⟨w.induce Cᶜ hw⟩⟩
  · exact fun h => localConn_subset_conn Cᶜ y z h

/-- The finite-cluster domain Markov property, written using a full connection outside
the prescribed cluster. No division by the probability of that cluster is needed. -/
theorem law_cluster_eq_inter_conn [Countable V] (q : Sym2 V → unitInterval) (o : V)
    {C : Set V} (hC : C.Finite) (ho : o ∈ C) (y : V) (hy : y ∉ C) (z : V) :
    law q ({ω : Config V | cluster ω o = C} ∩ conn y z) =
      law q {ω : Config V | cluster ω o = C} * law q (localConn Cᶜ y z) := by
  classical
  have heq : {ω : Config V | cluster ω o = C} ∩ conn y z =
      {ω : Config V | cluster ω o = C} ∩ localConn Cᶜ y z := by
    ext ω
    exact and_congr_right fun h => mem_conn_iff_mem_localConn_compl_of_cluster_eq h hy
  rw [heq]
  have hdet : ∀ ω ω' : Config V,
      (∀ a ∉ hC.toFinset, ∀ b ∉ hC.toFinset,
        (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) →
      (ω ∈ localConn Cᶜ y z ↔ ω' ∈ localConn Cᶜ y z) := by
    intro ω ω' hagree
    by_cases hz : z ∈ C
    · simp only [localConn_of_notMem_right (show z ∉ Cᶜ from fun h => h hz),
        Set.mem_empty_iff_false]
    · rw [mem_localConn_iff_reachable hy hz, mem_localConn_iff_reachable hy hz]
      exact localConn_iff_of_agree Cᶜ ⟨y, hy⟩ ⟨z, hz⟩ fun a ha b hb =>
        hagree a (by simpa using ha) b (by simpa using hb)
  simpa only [hC.coe_toFinset] using law_cluster_eq_inter q o hC.toFinset
    (by simpa using ho) (measurableSet_localConn Cᶜ y z) hdet

section Finite

variable [Fintype V]

open Classical in
/-- Partitioning a finite configuration integral according to the root cluster. -/
theorem integral_eq_sum_cluster (q : Sym2 V → unitInterval) (o : V)
    (f : Config V → ℝ) :
    (∫ ω, f ω ∂law q) = ∑ C : Set V,
      ∫ ω, {ω : Config V | cluster ω o = C}.indicator f ω ∂law q := by
  rw [← integral_finsetSum _ fun _ _ => Integrable.of_finite]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [Finset.sum_eq_single (cluster ω o)]
  · simp
  · intro C _ hC
    simp [Ne.symm hC]
  · simp

open Classical in
/-- The law of the root cluster integrates any finite-volume cluster functional. -/
theorem integral_cluster_functional_eq_sum (q : Sym2 V → unitInterval) (o : V)
    (F : Set V → ℝ) :
    (∫ ω, F (cluster ω o) ∂law q) =
      ∑ C : Set V, (law q).real {ω : Config V | cluster ω o = C} * F C := by
  rw [integral_eq_sum_cluster q o]
  refine Finset.sum_congr rfl fun C _ => ?_
  have heq : {ω : Config V | cluster ω o = C}.indicator (fun ω => F (cluster ω o)) =
      {ω : Config V | cluster ω o = C}.indicator (fun _ => F C) := by
    funext ω
    by_cases h : cluster ω o = C <;> simp [Set.indicator, h]
  rw [heq, integral_indicator_const _ (measurableSet_setOf_cluster_eq o C), smul_eq_mul]

open Classical in
/-- The outside cluster volume on a specified root-cluster event factors through the
complementary connection probabilities. The statement is unnormalized, including null events. -/
theorem integral_indicator_cluster_eq_sum_cluster (q : Sym2 V → unitInterval)
    (o : V) (C : Set V) (ho : o ∈ C) (y : V) (hy : y ∉ C) :
    (∫ ω, {ω : Config V | cluster ω o = C}.indicator
        (fun ω => ∑ z, (cluster ω y).indicator (fun _ => (1 : ℝ)) z) ω ∂law q) =
      (law q).real {ω : Config V | cluster ω o = C} *
        ∑ z, (law q).real (localConn Cᶜ y z) := by
  have heq : (fun ω => {ω : Config V | cluster ω o = C}.indicator
      (fun ω => ∑ z, (cluster ω y).indicator (fun _ => (1 : ℝ)) z) ω) =
      fun ω => ∑ z, ({ω : Config V | cluster ω o = C} ∩ conn y z).indicator
        (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases h : cluster ω o = C <;> simp [Set.indicator, h, mem_cluster_iff]
  rw [heq, integral_finsetSum _ fun _ _ => Integrable.of_finite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_indicator_const _ ((measurableSet_setOf_cluster_eq o C).inter
    (measurableSet_conn y z)), smul_eq_mul, mul_one, measureReal_def,
    law_cluster_eq_inter_conn q o C.toFinite ho y hy z, ENNReal.toReal_mul]
  rfl

open Classical in
/-- The boundary susceptibility averaged over the root cluster is exactly the directed
cluster increment in the finite-volume Russo identity. -/
theorem integral_boundarySusceptibility_eq_sum_cluster (J : Sym2 V → ℝ≥0) (β : ℝ≥0)
    (o : V) :
    (∫ ω, boundarySusceptibility J β (Set.toFinite (cluster ω o)).toFinset
      ∂law (intensityProfile J β)) =
      ∑ x, ∑ y, (J s(x, y) : ℝ) * ∫ ω,
        (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
          ∑ z, (cluster ω y).indicator (fun _ => (1 : ℝ)) z else 0)
        ∂law (intensityProfile J β) := by
  let q := intensityProfile J β
  have hterm (x y : V) :
      (∫ ω, (if x ∈ cluster ω o ∧ y ∉ cluster ω o then
          ∑ z, (cluster ω y).indicator (fun _ => (1 : ℝ)) z else 0) ∂law q) =
        ∑ C : Set V, (law q).real {ω : Config V | cluster ω o = C} *
          (if x ∈ C ∧ y ∉ C then ∑ z, (law q).real (localConn Cᶜ y z) else 0) := by
    rw [integral_eq_sum_cluster q o]
    refine Finset.sum_congr rfl fun C _ => ?_
    by_cases ho : o ∈ C
    · by_cases hxy : x ∈ C ∧ y ∉ C
      · rw [ite_eq_left hxy]
        rw [← integral_indicator_cluster_eq_sum_cluster q o C ho y hxy.2]
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases h : cluster ω o = C <;> simp [Set.indicator, h, hxy]
      · rw [ite_eq_right hxy, mul_zero]
        have heq : (fun ω => {ω : Config V | cluster ω o = C}.indicator
            (fun ω => if x ∈ cluster ω o ∧ y ∉ cluster ω o then
              ∑ z, (cluster ω y).indicator (fun _ => (1 : ℝ)) z else 0) ω) = 0 := by
          funext ω
          by_cases h : cluster ω o = C <;> simp [Set.indicator, h, hxy]
        simp [heq]
    · have he : {ω : Config V | cluster ω o = C} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro ω h
        exact ho (h ▸ (SimpleGraph.Reachable.refl o : o ∈ cluster ω o))
      simp [he]
  have hboundary (C : Set V) : boundarySusceptibility J β C.toFinite.toFinset =
      ∑ x, ∑ y, (J s(x, y) : ℝ) *
        (if x ∈ C ∧ y ∉ C then ∑ z, (law q).real (localConn Cᶜ y z) else 0) := by
    rw [boundarySusceptibility_eq]
    simp only [tsum_fintype, Set.Finite.mem_toFinset, Set.Finite.coe_toFinset]
    have hs : (∑ x, ∑ y, (J s(x, y) : ℝ) *
        (if x ∈ C ∧ y ∉ C then ∑ z, (law q).real (localConn Cᶜ y z) else 0)) =
        ∑ x ∈ C.toFinite.toFinset, ∑ y, (J s(x, y) : ℝ) *
          (if x ∈ C ∧ y ∉ C then ∑ z, (law q).real (localConn Cᶜ y z) else 0) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
      have hx' : x ∉ C := by simpa using hx
      simp [hx']
    rw [hs]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x ∈ C := by simpa using hx
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ C <;> simp [hx', hy, q]
  rw [integral_cluster_functional_eq_sum (intensityProfile J β) o
    (fun C => boundarySusceptibility J β C.toFinite.toFinset)]
  simp_rw [hboundary, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Set V) (α := V)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hterm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  ring

open Classical in
/-- For the actual canonical intensity law on a finite vertex type, the susceptibility
derivative is the expected boundary susceptibility of the root cluster. -/
theorem hasDerivAt_toReal_chi_eq_integral_boundarySusceptibility
    (J : Sym2 V → ℝ≥0) (o : V) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun b : ℝ => (chi (intensityProfile J b.toNNReal) o).toReal)
      (∫ ω, boundarySusceptibility J β.toNNReal
          (Set.toFinite (cluster ω o)).toFinset
        ∂law (intensityProfile J β.toNNReal)) β := by
  have hderiv (e : Sym2 V) :
      HasDerivAt (fun b : ℝ => ((b.toNNReal * J e : ℝ≥0) : ℝ)) (J e : ℝ) β := by
    have hb : HasDerivAt (fun b : ℝ => (b.toNNReal : ℝ)) 1 β := by
      refine (hasDerivAt_id β).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds hβ] with b hb
      simp [Real.coe_toNNReal _ hb.le]
    simpa only [NNReal.coe_mul, one_mul] using hb.mul_const (J e : ℝ)
  have hprofile (b : ℝ) : intensityProfile (fun e => b.toNNReal * J e) 1 =
      intensityProfile J b.toNNReal := by
    simpa only [Pi.smul_def, smul_eq_mul, mul_one] using intensityProfile_smul J b.toNNReal 1
  have hchi (b : ℝ) : (chi (intensityProfile J b.toNNReal) o).toReal =
      ∫ ω, ∑ z, (cluster ω o).indicator (fun _ => (1 : ℝ)) z
        ∂law (intensityProfile J b.toNNReal) := by
    rw [chi_eq_tsum_tau, tsum_fintype,
      ENNReal.toReal_sum (f := fun z => tau (intensityProfile J b.toNNReal) o z)
        (fun _ _ => measure_ne_top _ _),
      integral_finsetSum _ fun _ _ => Integrable.of_finite]
    refine Finset.sum_congr rfl fun z _ => ?_
    change (law (intensityProfile J b.toNNReal)).real (conn o z) =
      ∫ ω, (conn o z).indicator (fun _ => (1 : ℝ)) ω
        ∂law (intensityProfile J b.toNNReal)
    rw [integral_indicator_const _ (measurableSet_conn o z), smul_eq_mul, mul_one]
  have h := hasDerivAt_integral_sum_cluster (fun b e => b.toNNReal * J e)
    (fun e => (J e : ℝ)) β hderiv o (fun _ => 1)
  simp_rw [hprofile, ← hchi] at h
  rw [← integral_boundarySusceptibility_eq_sum_cluster] at h
  exact h

end Finite

end PercLib.Percolation.Bond
