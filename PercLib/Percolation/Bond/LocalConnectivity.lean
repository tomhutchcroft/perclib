/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Generalises the internal-connectivity helpers identified in
Percolation/Literature/SharpnessDCTProofs.lean at tomhutchcroft/near-critical-diffusivity, revision
c820fea91a7482c1755de0ec94ecb9f59ccfcacc (under Tom Hutchcroft's reuse permission recorded in
`docs/DECISIONS.md`). Licence status: that file lies in the source's `Percolation/Literature/`
tree, which holds code vendored from the `percolation/` project of `anthropics/formal-math`
(Apache-2.0; see the source's `third_party/formal-math/`). For any vendored part, the Apache-2.0
licence and its notices are those retained in `third_party/percolation/`; no other upstream licence
is asserted. Uses pinned mathlib induced graphs and walks directly; no PathIn or second
connection-event definition is introduced. No nearest-neighbour assumption.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.MeasureTheory.Measure.Continuity

/-! # Internal connectivity in the canonical bond configuration

Restricting the open graph to a vertex domain is exactly the canonical open graph
of the restricted pair configuration. Countability is needed only for the domain
in measurability statements, never for the ambient type in the deterministic API.
-/

@[expose] public section
open MeasureTheory Set
namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Restriction commutes with the canonical open-graph construction. -/
theorem openGraph_induce (ω : Config V) (S : Set V) :
    (openGraph ω).induce S = openGraph (Sym2.map (Subtype.val : S → V) ⁻¹' ω) := by
  ext x y
  simp [SimpleGraph.induce, SimpleGraph.comap_adj, openGraph_adj_iff, Subtype.coe_inj]

/-- The restricted unordered-pair configuration is measurable for any vertex domain. -/
theorem measurable_restrict_pairs (S : Set V) :
    Measurable (fun ω : Config V => Sym2.map (Subtype.val : S → V) ⁻¹' ω) :=
  measurable_set_iff.mpr (fun e => measurable_set_mem (Sym2.map Subtype.val e))

/-- Internal connectivity is measurable on every countable domain, even when the
ambient vertex type is uncountable. Finite domains need no extra assumption. -/
theorem measurableSet_setOf_reachable_induce (S : Set V) [Countable S] (x y : S) :
    MeasurableSet {ω : Config V | ((openGraph ω).induce S).Reachable x y} := by
  simpa only [openGraph_induce, conn, Set.preimage_ofPred_eq] using
    (measurableSet_conn x y).preimage (measurable_restrict_pairs S)

/-- Only pairs having both endpoints in the domain affect its induced open graph. -/
theorem openGraph_induce_eq_of_agree (S : Set V) {ω ω' : Config V}
    (h : ∀ x ∈ S, ∀ y ∈ S, (s(x, y) ∈ ω ↔ s(x, y) ∈ ω')) :
    (openGraph ω).induce S = (openGraph ω').induce S := by
  ext x y
  simp only [SimpleGraph.induce, SimpleGraph.comap_adj, Function.Embedding.coe_subtype,
    openGraph_adj_iff, h x x.property y y.property]

/-- Internal connection events depend only on internal pairs. -/
theorem localConn_iff_of_agree (S : Set V) (x y : S) {ω ω' : Config V}
    (h : ∀ a ∈ S, ∀ b ∈ S, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω')) :
    ((openGraph ω).induce S).Reachable x y ↔
      ((openGraph ω').induce S).Reachable x y := by
  rw [openGraph_induce_eq_of_agree S h]

/-- Increasing the open configuration preserves internal connections. -/
theorem localConn_mono_config (S : Set V) (x y : S) {ω ω' : Config V}
    (h : ω ⊆ ω') (hxy : ((openGraph ω).induce S).Reachable x y) :
    ((openGraph ω').induce S).Reachable x y := by
  exact hxy.mono (fun _ _ hadj => openGraph_mono h hadj)

/-- Increasing the vertex domain preserves internal connections. -/
theorem localConn_mono_domain (ω : Config V) {S T : Set V} (h : S ⊆ T) (x y : S)
    (hxy : ((openGraph ω).induce S).Reachable x y) :
    ((openGraph ω).induce T).Reachable (Set.inclusion h x) (Set.inclusion h y) :=
  hxy.map ((openGraph ω).induceHomOfLE h).toHom

/-- An internal connection is a connection in the full model. -/
theorem conn_of_localConn (ω : Config V) (S : Set V) (x y : S)
    (hxy : ((openGraph ω).induce S).Reachable x y) : ω ∈ conn (x : V) (y : V) :=
  hxy.map (SimpleGraph.Embedding.induce S).toHom

/-- Every global connection is witnessed in a finite vertex domain. No ambient
countability, interaction-range, or degree assumption is needed. -/
theorem conn_iff_exists_finset_localConn (ω : Config V) (x y : V) :
    ω ∈ conn x y ↔ ∃ S : Finset V, ω ∈ localConn (S : Set V) x y := by
  classical
  constructor
  · rintro ⟨w⟩
    have hw : ∀ z ∈ w.support, z ∈ (w.support.toFinset : Set V) := by
      intro z hz
      simpa using hz
    exact ⟨w.support.toFinset, hw x w.start_mem_support, hw y w.end_mem_support,
      ⟨w.induce _ hw⟩⟩
  · rintro ⟨S, hx, hy, h⟩
    exact conn_of_localConn ω S ⟨x, hx⟩ ⟨y, hy⟩ h

/-- A singleton domain retains the reflexive connection, even with no open bonds. -/
example (x : V) :
    ((openGraph (∅ : Config V)).induce ({x} : Set V)).Reachable
      ⟨x, by simp⟩ ⟨x, by simp⟩ := .refl _

/-- Finite-domain events are measurable without ambient countability. -/
example (S : Finset V) (x y : S) :
    MeasurableSet {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable x y} :=
  measurableSet_setOf_reachable_induce (S : Set V) x y

/-- Internal connection events increase with an increasing family of domains. -/
theorem monotone_localConn {S : ℕ → Set V} (hS : Monotone S) (x y : V) :
    Monotone (fun n => localConn (S n) x y) := by
  intro n m hnm ω hω
  rcases hω with ⟨hx, hy, hxy⟩
  exact ⟨hS hnm hx, hS hnm hy,
    localConn_mono_domain ω (hS hnm) ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩

/-- Exhaustion identity for connections. Every finite path eventually lies inside one
domain; this does not bound the length of an edge or the number of potential neighbours. -/
theorem conn_eq_iUnion_localConn {S : ℕ → Set V} (hS : Monotone S)
    (hcover : ∀ v, ∃ n, v ∈ S n) (x y : V) :
    (conn x y : Set (Config V)) = ⋃ n, localConn (S n) x y := by
  ext ω
  simp only [Set.mem_iUnion]
  constructor
  · intro h
    obtain ⟨F, hx, hy, hxy⟩ := (conn_iff_exists_finset_localConn ω x y).mp h
    have hf : (F : Set V) ⊆ ⋃ n, S n := by
      intro v _
      exact Set.mem_iUnion.mpr (hcover v)
    obtain ⟨n, hn⟩ := hS.directed_le.exists_mem_subset_of_finset_subset_biUnion hf
    exact ⟨n, hn hx, hn hy, localConn_mono_domain ω hn ⟨x, hx⟩ ⟨y, hy⟩ hxy⟩
  · rintro ⟨n, hx, hy, hxy⟩
    exact conn_of_localConn ω (S n) ⟨x, hx⟩ ⟨y, hy⟩ hxy

/-- Two-point probabilities are the increasing supremum of their domain restrictions.
This uses continuity from below, without subtracting an infinite susceptibility. -/
theorem tau_eq_iSup_localConn (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (x y : V) :
    tau q x y = ⨆ n, law q (localConn (S n) x y) := by
  rw [tau, conn_eq_iUnion_localConn hS hcover]
  exact (monotone_localConn hS x y).measure_iUnion

/-- Probability convergence along any increasing domain exhaustion. -/
theorem tendsto_localConn_probability (q : Sym2 V → unitInterval)
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n) (x y : V) :
    Filter.Tendsto (fun n => law q (localConn (S n) x y))
      Filter.atTop (nhds (tau q x y)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law q) (monotone_localConn hS x y)
  simpa only [← conn_eq_iUnion_localConn hS hcover, tau, Function.comp_def] using h

/-- A nontrivial internal connection uses the existing unordered open edge. -/
example : ((openGraph ({s(false, true)} : Config Bool)).induce Set.univ).Reachable
    ⟨false, Set.mem_univ _⟩ ⟨true, Set.mem_univ _⟩ := by
  apply SimpleGraph.Adj.reachable
  simp [SimpleGraph.induce, SimpleGraph.comap_adj, openGraph_adj_iff]

/-! ### Restricted clusters versus cluster intersections -/

/-- Inside a two-point set, `w` is joined to `v ≠ w` exactly when the pair `s(v, w)` is
open. -/
theorem mem_localCluster_pair_iff {ω : Config V} {v w : V} (hvw : v ≠ w) :
    w ∈ localCluster ω {v, w} v ↔ s(v, w) ∈ ω := by
  constructor
  · rintro ⟨hv, hw, hr⟩
    by_contra h
    have hbot : (openGraph ω).induce ({v, w} : Set V) = ⊥ := by
      ext a b
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj_iff,
        SimpleGraph.bot_adj, iff_false, not_and]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact fun _ hne => hne rfl
      · exact fun h' _ => h h'
      · exact fun h' _ => h (Sym2.eq_swap ▸ h')
      · exact fun _ hne => hne rfl
    rw [hbot, SimpleGraph.reachable_bot] at hr
    exact hvw (congrArg Subtype.val hr)
  · intro h
    refine ⟨Set.mem_insert v {w}, Set.mem_insert_of_mem v rfl, SimpleGraph.Adj.reachable ?_⟩
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj_iff]
    exact ⟨h, hvw⟩

/-- **The restricted cluster can be strictly smaller.** If `v - a - w` is an open path and
the pair `s(v, w)` is closed, then `w` lies in the cluster of `v` and in `{v, w}`, but not
in the restricted cluster of `v` in `{v, w}`. -/
theorem localCluster_ssubset_cluster_inter_of_path {ω : Config V} {v a w : V} (hvw : v ≠ w)
    (hva : s(v, a) ∈ ω) (haw : s(a, w) ∈ ω) (hvw' : s(v, w) ∉ ω) :
    localCluster ω {v, w} v ⊂ cluster ω v ∩ {v, w} := by
  refine (localCluster_subset ω _ v).ssubset_of_mem_notMem (a := w) ⟨?_, ?_⟩ ?_
  · have hav : v ≠ a := by rintro rfl; exact hvw' haw
    have haw' : a ≠ w := by rintro rfl; exact hvw' hva
    exact conn_trans (mem_conn_of_mem hav hva) (mem_conn_of_mem haw' haw)
  · exact Set.mem_insert_of_mem v rfl
  · rw [mem_localCluster_pair_iff hvw]
    exact hvw'

/-- On the path `0 - 1 - 2` with both edges open, the restricted cluster of `0` in `{0, 2}`
is strictly smaller than the intersection of the cluster of `0` with `{0, 2}`. -/
theorem localCluster_ssubset_cluster_inter_fin_three :
    localCluster ({s(0, 1), s(1, 2)} : Config (Fin 3)) {0, 2} 0 ⊂
      cluster ({s(0, 1), s(1, 2)} : Config (Fin 3)) 0 ∩ {0, 2} :=
  localCluster_ssubset_cluster_inter_of_path (a := 1) (by decide) (by simp) (by simp)
    (by simp)

end PercLib.Percolation.Bond
