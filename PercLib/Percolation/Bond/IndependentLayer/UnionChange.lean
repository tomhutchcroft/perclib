/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof-only results, derived here; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 (the change event used in the softened-edge coupling). The results below are
measurability statements only; they assert no continuity or probability estimate.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.UnionChange.Defs

/-!
# The union-change event of a cluster, as a measurable crossing event

Let `ω, D` be two bond configurations on a vertex type `V`, and let `o` be a root vertex.  Adding
`D` to `ω` can only enlarge the cluster of `o` (`cluster_mono`).  This file identifies the event

  `unionChange o = {z : Config V × Config V | cluster (z.1 ∪ z.2) o ≠ cluster z.1 o}`

exactly with the countable union, over ordered pairs `p = (u, v)` of vertices, of the *boundary*
events

  `crossingPair o p = {z | u ∈ cluster z.1 o} ∩ {z | v ∉ cluster z.1 o} ∩ {z | s(u, v) ∈ z.2}`,

i.e. `u` is in the old cluster of `o`, `v` is not, and the pair `u—v` is opened by the added
configuration `D = z.2`.  Two consequences are recorded:

* `unionChange o = ⋃ p, crossingPair o p` (`unionChange_eq_iUnion_crossingPair`); neither
  inclusion needs countability of `V`.
* `MeasurableSet (unionChange o)` when `V` is countable
  (`measurableSet_unionChange`), together with the measurability of each boundary event
  (`measurableSet_crossingPair`) and of arbitrary unions of them
  (`measurableSet_iUnion_crossingPair`).

This is the measurability certificate that the softened-edge coupling bound needs: with it the
indicator of the change event is measurable, so an integral of the form
`∫⁻ z, (change).indicator (fun _ => (1 : ℝ≥0∞)) z ∂γ` is `γ change` by
`lintegral_indicator_const` (see `UnionChangeIntegral.lean`).

The forward inclusion `unionChange o ⊆ ⋃ p, crossingPair o p` is exactly the exploration
inclusion `cluster_union_subset`: a vertex newly reached from `o` is reached either inside the old
cluster or through an added pair from the old cluster to its complement.  The reverse inclusion is
direct: such a pair joins its outside endpoint to `o` in `ω ∪ D`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The boundary (ordered-pair) events -/

/-- Membership in a boundary event, in the unfolded form used everywhere below. -/
@[simp]
theorem mem_crossingPair {o : V} {p : V × V} {z : Config V × Config V} :
    z ∈ crossingPair o p ↔
      p.1 ∈ cluster z.1 o ∧ p.2 ∉ cluster z.1 o ∧ s(p.1, p.2) ∈ z.2 := by
  simp [crossingPair, and_assoc]

theorem exists_crossingPair_of_mem_cluster_union {o : V} {z : Config V × Config V} {y : V}
    (hy : y ∈ cluster (z.1 ∪ z.2) o) (hyo : y ∉ cluster z.1 o) :
    ∃ p : V × V, p.1 ∈ cluster z.1 o ∧ p.2 ∉ cluster z.1 o ∧ s(p.1, p.2) ∈ z.2 := by
  have hC : y ∈ cluster z.1 o ∪ ⋃ u ∈ cluster z.1 o, ⋃ v ∈ (cluster z.1 o)ᶜ,
      ⋃ (_ : s(u, v) ∈ z.2), cluster ((z.1 ∪ z.2) ∩ {e | ∀ x ∈ e, x ∉ cluster z.1 o}) v :=
    cluster_union_subset z.1 z.2 o hy
  rcases hC with hC | hC
  · exact absurd hC hyo
  simp only [mem_iUnion, exists_prop] at hC
  obtain ⟨u, hu, v, hv, huv, -⟩ := hC
  exact ⟨(u, v), hu, hv, huv⟩

/-- **The change event is the union of the boundary events.**  The cluster of `o` changes when `D`
is added to `ω` exactly when some added pair joins a vertex of the old cluster of `o` to a vertex
outside it.  No countability of `V` is used. -/
theorem unionChange_eq_iUnion_crossingPair (o : V) :
    unionChange o = ⋃ p : V × V, crossingPair o p := by
  ext z
  constructor
  · intro hz
    have hsub : cluster z.1 o ⊆ cluster (z.1 ∪ z.2) o := cluster_mono subset_union_left o
    have hns : ¬ (cluster (z.1 ∪ z.2) o ⊆ cluster z.1 o) := fun h =>
      hz (Subset.antisymm hsub h).symm
    obtain ⟨y, hy, hyo⟩ := not_subset.1 hns
    obtain ⟨p, hp, hp', hpd⟩ := exists_crossingPair_of_mem_cluster_union hy hyo
    exact mem_iUnion.2 ⟨p, mem_crossingPair.2 ⟨hp, hp', hpd⟩⟩
  · intro hz
    obtain ⟨p, hp⟩ := mem_iUnion.1 hz
    obtain ⟨hu, hv, huv⟩ := mem_crossingPair.1 hp
    have hup : p.1 ∈ cluster (z.1 ∪ z.2) o := cluster_mono subset_union_left o hu
    have hne : p.1 ≠ p.2 := fun h => hv (h ▸ hu)
    have hmem : s(p.1, p.2) ∈ z.1 ∪ z.2 := mem_union_right _ huv
    have hvp : p.2 ∈ cluster (z.1 ∪ z.2) o := conn_trans hup (mem_conn_of_mem hne hmem)
    exact fun hEq => hv (hEq ▸ hvp)

/-! ### Measurability -/

/-- Being in the old cluster of `o` is a measurable property of the configuration pair. -/
theorem measurableSet_cluster_mem_fst [Countable V] (o y : V) :
    MeasurableSet {z : Config V × Config V | y ∈ cluster z.1 o} :=
  (measurableSet_conn o y).preimage measurable_fst

/-- Each boundary event is measurable: it is the intersection of a measurable cluster event in the
first coordinate, its complement, and a one-pair cylinder in the second coordinate. -/
theorem measurableSet_crossingPair [Countable V] (o : V) (p : V × V) :
    MeasurableSet (crossingPair o p) := by
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact (measurableSet_conn o p.1).preimage measurable_fst
  · exact ((measurableSet_conn o p.2).preimage measurable_fst).compl
  · exact (measurableSet_mem (s(p.1, p.2))).preimage measurable_snd

/-- Any union of boundary events over any set of ordered pairs is measurable; only the
countability of the index type is used. -/
theorem measurableSet_iUnion_crossingPair [Countable V] (o : V) (T : Set (V × V)) :
    MeasurableSet (⋃ p ∈ T, crossingPair o p) :=
  MeasurableSet.biUnion (T.to_countable) fun p _ => measurableSet_crossingPair o p

/-- **The change event is measurable.**  This is the measurability certificate for the
softened-edge coupling: `V` countable is the only hypothesis. -/
theorem measurableSet_unionChange [Countable V] (o : V) : MeasurableSet (unionChange o) := by
  rw [unionChange_eq_iUnion_crossingPair]
  exact MeasurableSet.iUnion fun p => measurableSet_crossingPair o p

/-- The same event with the two configurations in the other order, in the form used by
`PercLib.Models.LongRange.measure_change_le`. -/
theorem measurableSet_unionChange' [Countable V] (o : V) :
    MeasurableSet {z : Config V × Config V | cluster z.1 o ≠ cluster (z.1 ∪ z.2) o} := by
  have h : {z : Config V × Config V | cluster z.1 o ≠ cluster (z.1 ∪ z.2) o} = unionChange o :=
    Set.ext fun z => ne_comm
  rw [h]
  exact measurableSet_unionChange o

/-- The indicator of the change event is a measurable function: this is what the integration step
of the coupling estimate uses. -/
theorem measurable_indicator_unionChange [Countable V] (o : V) :
    Measurable fun z : Config V × Config V => (unionChange o).indicator (fun _ => (1 : ℝ≥0∞)) z :=
  measurable_const.indicator (measurableSet_unionChange o)

end PercLib.Percolation.Bond
