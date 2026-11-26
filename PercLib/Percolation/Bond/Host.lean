/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs for the host-graph specialization of the bond interface, using the canonical cylinder
marginal, countable almost-everywhere conjunction and mathlib's fromEdgeSet API.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Cylinder

/-!
# Host graphs as supported bond profiles

The hypothesis is zero probability on every pair outside the host edge set,
including diagonal pairs. This yields configuration containment as well as graph
containment. The general bond law continues to allow arbitrary diagonal values.

* `ae_config_subset_host_iff`, `law_config_subset_host_eq_one_iff`: configuration
  containment holds almost surely exactly when every pair outside the host edge set,
  diagonal pairs included, has probability zero.
* `ae_openGraph_le_host_iff`, `law_openGraph_le_host_eq_one_iff`: graph containment holds
  almost surely exactly when every non-diagonal pair outside the host has probability zero.
-/

@[expose] public section

open MeasureTheory

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- Almost surely no pair outside the host edge set is open. -/
theorem ae_config_subset_host (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hq : ∀ e, e ∉ G.edgeSet → q e = 0) :
    ∀ᵐ ω ∂law q, ω ⊆ G.edgeSet := by
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ ω → e ∈ G.edgeSet := by
    by_cases h : e ∈ G.edgeSet
    · exact Filter.Eventually.of_forall (fun _ _ => h)
    · have hz : law q {ω | e ∈ ω} = 0 := by
        simpa [law, hq e h] using PercLib.Probability.prodBernoulli_setOf_mem q e
      rw [ae_iff]
      simpa [h] using hz
  filter_upwards [ae_all_iff.mpr he] with ω hω
  exact fun e he => hω e he

/-- Almost surely the graph of open edges is a subgraph of the host graph. -/
theorem ae_openGraph_le_host (G : SimpleGraph V) (q : Sym2 V → unitInterval)
    (hq : ∀ e, e ∉ G.edgeSet → q e = 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ G := by
  filter_upwards [ae_config_subset_host G q hq] with ω hω
  simpa [openGraph] using SimpleGraph.fromEdgeSet_mono hω

omit [Countable V] in
/-- A pair is open with probability zero exactly when its profile value is zero. -/
theorem law_setOf_mem_eq_zero_iff (q : Sym2 V → unitInterval) (e : Sym2 V) :
    law q {ω | e ∈ ω} = 0 ↔ q e = 0 := by
  change PercLib.Probability.prodBernoulli q {ω | e ∈ ω} = 0 ↔ q e = 0
  rw [PercLib.Probability.prodBernoulli_setOf_mem, ENNReal.coe_eq_zero,
    ← NNReal.coe_eq_zero, unitInterval.coe_toNNReal]
  exact Set.Icc.coe_eq_zero

/-- Configuration containment in a host is a measurable event. -/
theorem measurableSet_config_subset_host (G : SimpleGraph V) :
    MeasurableSet {ω : Config V | ω ⊆ G.edgeSet} := by
  have h : {ω : Config V | ω ⊆ G.edgeSet} = ⋂ e ∈ G.edgeSetᶜ, {ω : Config V | e ∉ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun h e he hω => he (h hω), fun h e hω => by_contra fun he => h e he hω⟩
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _) fun e _ => (measurableSet_mem e).compl

/-- Graph containment in a host is a measurable event. -/
theorem measurableSet_openGraph_le_host (G : SimpleGraph V) :
    MeasurableSet {ω : Config V | openGraph ω ≤ G} := by
  have h : {ω : Config V | openGraph ω ≤ G} =
      ⋂ x, ⋂ y, ⋂ (_ : x ≠ y ∧ ¬ G.Adj x y), {ω : Config V | s(x, y) ∉ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h x y hxy hω
      exact hxy.2 (h ((openGraph_adj_iff ω x y).2 ⟨hω, hxy.1⟩))
    · intro h x y hadj
      rw [openGraph_adj_iff] at hadj
      by_contra hG
      exact h x y ⟨hadj.2, hG⟩ hadj.1
  rw [h]
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    MeasurableSet.iInter fun _ => (measurableSet_mem _).compl

/-- **Configuration containment criterion.** Almost surely every open pair is a host edge
exactly when every pair outside the host edge set, diagonal pairs included, has probability
zero. -/
theorem ae_config_subset_host_iff (G : SimpleGraph V) (q : Sym2 V → unitInterval) :
    (∀ᵐ ω ∂law q, ω ⊆ G.edgeSet) ↔ ∀ e ∉ G.edgeSet, q e = 0 := by
  refine ⟨fun h e he => ?_, ae_config_subset_host G q⟩
  rw [← law_setOf_mem_eq_zero_iff]
  exact measure_mono_null (t := {ω : Config V | ¬ ω ⊆ G.edgeSet})
    (fun ω (hω : e ∈ ω) hsub => he (hsub hω)) (ae_iff.1 h)

/-- **Graph containment criterion.** Almost surely the open graph is a subgraph of the host
exactly when every non-diagonal pair outside the host has probability zero; diagonal pairs
are unrestricted. -/
theorem ae_openGraph_le_host_iff (G : SimpleGraph V) (q : Sym2 V → unitInterval) :
    (∀ᵐ ω ∂law q, openGraph ω ≤ G) ↔ ∀ x y, x ≠ y → ¬ G.Adj x y → q s(x, y) = 0 := by
  constructor
  · intro h x y hxy hG
    rw [← law_setOf_mem_eq_zero_iff]
    refine measure_mono_null (t := {ω : Config V | ¬ openGraph ω ≤ G})
      (fun ω (hω : s(x, y) ∈ ω) hle => hG (hle ?_)) (ae_iff.1 h)
    exact (openGraph_adj_iff ω x y).2 ⟨hω, hxy⟩
  · intro hq
    have hxy (x y : V) : ∀ᵐ ω ∂law q, x ≠ y → ¬ G.Adj x y → s(x, y) ∉ ω := by
      by_cases h : x ≠ y ∧ ¬ G.Adj x y
      · have hz : law q {ω | s(x, y) ∈ ω} = 0 :=
          (law_setOf_mem_eq_zero_iff q _).2 (hq x y h.1 h.2)
        rw [ae_iff]
        refine measure_mono_null (fun ω hω => ?_) hz
        simp only [Set.mem_ofPred_eq, not_imp, not_not] at hω
        exact hω.2.2
      · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ h
    filter_upwards [ae_all_iff.2 fun x => ae_all_iff.2 (hxy x)] with ω hω x y hadj
    rw [openGraph_adj_iff] at hadj
    by_contra hG
    exact hω x y hadj.2 hG hadj.1

/-- Configuration containment has probability one exactly when every pair outside the host
edge set has probability zero. -/
theorem law_config_subset_host_eq_one_iff (G : SimpleGraph V) (q : Sym2 V → unitInterval) :
    law q {ω | ω ⊆ G.edgeSet} = 1 ↔ ∀ e ∉ G.edgeSet, q e = 0 := by
  rw [← ae_config_subset_host_iff,
    ae_iff_measure_eq (measurableSet_config_subset_host G).nullMeasurableSet, measure_univ]

/-- Graph containment has probability one exactly when every non-diagonal pair outside the
host has probability zero. -/
theorem law_openGraph_le_host_eq_one_iff (G : SimpleGraph V) (q : Sym2 V → unitInterval) :
    law q {ω | openGraph ω ≤ G} = 1 ↔ ∀ x y, x ≠ y → ¬ G.Adj x y → q s(x, y) = 0 := by
  rw [← ae_openGraph_le_host_iff,
    ae_iff_measure_eq (measurableSet_openGraph_le_host G).nullMeasurableSet, measure_univ]

/-- Both configuration and graph containment form the host-specialization target. -/
def HostContainment (G : SimpleGraph V) (q : Sym2 V → unitInterval) : Prop :=
  (∀ e, e ∉ G.edgeSet → q e = 0) →
    ∀ᵐ ω ∂law q, ω ⊆ G.edgeSet ∧ openGraph ω ≤ G

theorem hostContainment (G : SimpleGraph V) (q : Sym2 V → unitInterval) :
    HostContainment G q := by
  intro hq
  exact (ae_config_subset_host G q hq).and (ae_openGraph_le_host G q hq)

example (G : SimpleGraph V) : ∀ᵐ ω ∂law (fun _ : Sym2 V => 0),
    ω ⊆ G.edgeSet ∧ openGraph ω ≤ G :=
  hostContainment G _ (fun _ _ => rfl)

-- Inhomogeneous host profiles, including probability one on host edges.
open Classical in
example (G : SimpleGraph Bool) (p : Sym2 Bool → unitInterval) :
    let q := fun e => if e ∈ G.edgeSet then p e else 0
    ∀ᵐ ω ∂law q, ω ⊆ G.edgeSet ∧ openGraph ω ≤ G := by
  classical
  exact hostContainment G _ (fun e he => by simp [he])

end PercLib.Percolation.Bond
