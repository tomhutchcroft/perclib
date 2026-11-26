/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.GlobalConnectivity
public import PercLib.Percolation.Bond.LocalFiniteness

/-! Correspondence wrappers for local finiteness and global connection events.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Finite neighbour sets give finite walk-length sets, finite closed and open intrinsic
balls (the open ball of radius zero is empty and the closed one is `{v}`); for Bernoulli
bonds on countable `V` with finite off-diagonal rows there is one almost sure event on which
all open neighbour sets and all finite-radius intrinsic balls are finite. -/
@[tag "7R5Q"]
theorem finite_neighbors_finite_balls :
    (∀ G : SimpleGraph V, (∀ v, (G.neighborSet v).Finite) → ∀ (v : V) (r : ℕ),
      {w | ∃ p : G.Walk v w, p.length ≤ r}.Finite ∧
      {w | G.edist v w ≤ r}.Finite ∧ (G.ball v r).Finite) ∧
    (∀ (G : SimpleGraph V) (v : V), G.ball v 0 = ∅ ∧ {w | G.edist v w ≤ 0} = {v}) ∧
    (∀ [Countable V] (q : Sym2 V → unitInterval),
      (∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞) →
      ∀ᵐ ω ∂law q, (∀ v, ((openGraph ω).neighborSet v).Finite) ∧
        ∀ (v : V) (r : ℕ), {w | (openGraph ω).edist v w ≤ r}.Finite ∧
          ((openGraph ω).ball v r).Finite) := by
  have hclosed : ∀ (G : SimpleGraph V) (v : V) (r : ℕ),
      {w | G.edist v w ≤ r} ⊆ G.ball v ((r + 1 : ℕ) : ℕ∞) := by
    intro G v r w hw
    rw [SimpleGraph.mem_ball, SimpleGraph.edist_comm]
    have hw' : G.edist v w ≤ r := hw
    exact lt_of_le_of_lt hw' (by exact_mod_cast Nat.lt_succ_self r)
  refine ⟨fun G hG v r => ⟨SimpleGraph.finite_setOf_exists_walk_length_le G hG r v,
      (SimpleGraph.finite_ball_of_finite_neighborSet G hG (r + 1) v).subset (hclosed G v r),
      SimpleGraph.finite_ball_of_finite_neighborSet G hG r v⟩,
    fun G v => ⟨SimpleGraph.ball_zero, ?_⟩, fun q hrow => ?_⟩
  · ext w
    simp only [Set.mem_ofPred_eq, nonpos_iff_eq_zero, Set.mem_singleton_iff]
    rw [SimpleGraph.edist_eq_zero_iff, eq_comm]
  · filter_upwards [ae_all_finite_neighbors_of_rowSum_lt_top q hrow,
      ae_finite_balls_of_rowSum_lt_top q hrow] with ω h1 h2
    exact ⟨h1, fun v r => ⟨(h2 v (r + 1)).subset (by exact_mod_cast hclosed _ v r), h2 v r⟩⟩

/-- The all-pairs connection event and its nonempty version are increasing; on countable
`V` they are measurable, as are the events that every cluster is finite and that every
cluster has at most `n` vertices, and the latter two are decreasing. -/
@[tag "POEO"]
theorem global_connection_events :
    IsUpperSet {ω : Config V | (openGraph ω).Preconnected} ∧
    IsUpperSet {ω : Config V | (openGraph ω).Connected} ∧
    IsLowerSet {ω : Config V | ∀ x, (cluster ω x).Finite} ∧
    (∀ n : ℕ∞, IsLowerSet {ω : Config V | ∀ x, (cluster ω x).encard ≤ n}) ∧
    (Countable V →
      MeasurableSet {ω : Config V | (openGraph ω).Preconnected} ∧
      MeasurableSet {ω : Config V | (openGraph ω).Connected} ∧
      MeasurableSet {ω : Config V | ∀ x, (cluster ω x).Finite} ∧
      ∀ n : ℕ∞, MeasurableSet {ω : Config V | ∀ x, (cluster ω x).encard ≤ n}) :=
  ⟨isUpperSet_preconnected, isUpperSet_connected,
    fun _ _ hle hω x => (hω x).subset (cluster_mono hle x),
    fun _ _ _ hle hω x => le_trans (Set.encard_le_encard (cluster_mono hle x)) (hω x),
    fun _ => ⟨measurableSet_preconnected, measurableSet_connected,
      measurableSet_forall_cluster_finite, measurableSet_forall_encard_cluster_le⟩⟩

open Classical in
/-- Spanning, Harris and isolation bounds for the all-pairs connection event; the
isolation bounds need a second vertex. -/
@[tag "JSS9"]
theorem global_connection_bounds (q : Sym2 V → unitInterval) (x : V) :
    (∀ T : Finset (Sym2 V), (SimpleGraph.fromEdgeSet (T : Set (Sym2 V))).Preconnected →
      (∏ e ∈ T, (unitInterval.toNNReal (q e) : ℝ≥0∞)) ≤
        law q {ω | (openGraph ω).Preconnected}) ∧
    (∀ [Fintype V],
      (∏ y ∈ Finset.univ.erase x, tau q x y) ≤ law q {ω | (openGraph ω).Preconnected}) ∧
    (∀ [Countable V], (∃ y, y ≠ x) →
      law q {ω : Config V | (openGraph ω).Preconnected} ≤
        1 - law q {ω : Config V | ∀ y, ¬ (openGraph ω).Adj x y}) ∧
    (∀ [Fintype V], (∃ y, y ≠ x) →
      law q {ω : Config V | (openGraph ω).Preconnected} ≤
        1 - ∏ y ∈ Finset.univ.erase x, (1 - (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞))) := by
  refine ⟨fun T hT => prod_le_law_preconnected q T hT,
    prod_tau_le_law_preconnected q x,
    fun hV => law_preconnected_le_one_sub_isolated q x hV, fun hV => by
      rw [← law_isolated q x]
      exact law_preconnected_le_one_sub_isolated q x hV⟩

end PercLib.Percolation.Bond
