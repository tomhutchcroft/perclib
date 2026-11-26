/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original proofs for the canonical lace events; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.PivotalPartition
public import PercLib.Percolation.Bond.LocalConnectivity

/-!
# Localization of lace events to a containing vertex set

## Main results

When two root clusters lie in a common vertex set and their configurations
agree on pairs internal to that set, root connections and through-set events
are unchanged. The forbidden vertex sets need only agree inside the containing
set. The same hypotheses preserve the actual `E'` event.

Directed pivotal pairs are compared only in the presence of the actual root
connection. This makes both endpoints of a relevant pivotal pair belong to
the root cluster, including when the ambient vertex set is infinite.
The statements are deterministic and require no finiteness or countability.
-/

@[expose] public section
noncomputable section

open Set

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- A connection restricted to a prescribed vertex set can be transferred using
only the pairs and vertex memberships inside a set containing its root cluster. -/
theorem mem_localConn_of_cluster_subset_of_agree
    {ω η : Config V} {A B S : Set V} {x y : V}
    (hω : cluster ω x ⊆ S)
    (hconfig : ∀ u ∈ S, ∀ v ∈ S, (s(u, v) ∈ ω ↔ s(u, v) ∈ η))
    (hsets : ∀ u ∈ S, u ∈ A ↔ u ∈ B)
    (h : ω ∈ localConn A x y) : η ∈ localConn B x y := by
  classical
  obtain ⟨hx, hy, ⟨p⟩⟩ := h
  let p' := p.map (SimpleGraph.Embedding.induce A).toHom
  have hpS : ∀ z ∈ p'.support, z ∈ S := by
    intro z hz
    exact hω ⟨p'.takeUntil z hz⟩
  have hpA : ∀ z ∈ p'.support, z ∈ A := by
    intro z hz
    dsimp only [p'] at hz
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
    obtain ⟨a, -, ha⟩ := hz
    exact ha ▸ a.property
  let φ : (openGraph ω).induce (S ∩ A) →g (openGraph η).induce B :=
    { toFun := fun u => ⟨u.1, (hsets u.1 u.2.1).mp u.2.2⟩
      map_rel' := by
        intro u v huv
        change (openGraph η).Adj u.1 v.1
        change (openGraph ω).Adj u.1 v.1 at huv
        rw [openGraph_adj_iff] at huv ⊢
        exact ⟨(hconfig u.1 u.2.1 v.1 v.2.1).mp huv.1, huv.2⟩ }
  refine ⟨(hsets x (hω (mem_cluster_self ω x))).mp hx,
    (hsets y (hpS y p'.end_mem_support)).mp hy, ⟨?_⟩⟩
  exact (p'.induce (S ∩ A) (fun z hz => ⟨hpS z hz, hpA z hz⟩)).map φ

/-- Root connections depend only on the common containing set and its internal
pairs, provided neither root cluster leaves that set. -/
theorem mem_conn_iff_of_cluster_subset_of_agree
    {ω η : Config V} {S : Set V} {x y : V}
    (hω : cluster ω x ⊆ S) (hη : cluster η x ⊆ S)
    (hconfig : ∀ u ∈ S, ∀ v ∈ S, (s(u, v) ∈ ω ↔ s(u, v) ∈ η)) :
    (ω ∈ conn x y ↔ η ∈ conn x y) := by
  have hsets : ∀ u ∈ S, u ∈ (univ : Set V) ↔ u ∈ (univ : Set V) :=
    fun _ _ => Iff.rfl
  constructor
  · intro h
    have ht := mem_localConn_of_cluster_subset_of_agree hω hconfig hsets
      (show ω ∈ localConn univ x y by simpa only [localConn_univ] using h)
    simpa only [localConn_univ] using ht
  · intro h
    have ht := mem_localConn_of_cluster_subset_of_agree hη
      (fun u hu v hv => (hconfig u hu v hv).symm) hsets
      (show η ∈ localConn univ x y by simpa only [localConn_univ] using h)
    simpa only [localConn_univ] using ht

/-- The root clusters themselves agree under localization of their internal
configurations. -/
theorem cluster_eq_of_cluster_subset_of_agree
    {ω η : Config V} {S : Set V} {x : V}
    (hω : cluster ω x ⊆ S) (hη : cluster η x ⊆ S)
    (hconfig : ∀ u ∈ S, ∀ v ∈ S, (s(u, v) ∈ ω ↔ s(u, v) ∈ η)) :
    cluster ω x = cluster η x := by
  ext y
  exact mem_conn_iff_of_cluster_subset_of_agree hω hη hconfig

/-- Through-set connections are unchanged when both the configuration and the
prescribed vertex set agree on a common set containing the root clusters. -/
theorem mem_throughSet_iff_of_cluster_subset_of_agree
    {ω η : Config V} {A B S : Set V} {x y : V}
    (hω : cluster ω x ⊆ S) (hη : cluster η x ⊆ S)
    (hconfig : ∀ u ∈ S, ∀ v ∈ S, (s(u, v) ∈ ω ↔ s(u, v) ∈ η))
    (hsets : ∀ u ∈ S, u ∈ A ↔ u ∈ B) :
    (ω ∈ throughSet A x y ↔ η ∈ throughSet B x y) := by
  have hc := mem_conn_iff_of_cluster_subset_of_agree (y := y) hω hη hconfig
  have hcomp : ∀ u ∈ S, u ∈ Aᶜ ↔ u ∈ Bᶜ :=
    fun u hu => not_congr (hsets u hu)
  have ha : ω ∈ localConn Aᶜ x y ↔ η ∈ localConn Bᶜ x y :=
    ⟨mem_localConn_of_cluster_subset_of_agree hω hconfig hcomp,
      mem_localConn_of_cluster_subset_of_agree hη
        (fun u hu v hv => (hconfig u hu v hv).symm)
        (fun u hu => (hcomp u hu).symm)⟩
  change (ω ∈ conn x y ∧ ω ∉ localConn Aᶜ x y) ↔
    (η ∈ conn x y ∧ η ∉ localConn Bᶜ x y)
  rw [hc, ha]

/-- On an actual root connection, a directed pivotal pair and its orientation
are determined by the internal pairs of a set containing the root clusters. -/
theorem mem_orientedPivotal_of_conn_of_cluster_subset_of_agree
    {ω η : Config V} {S : Set V} {x y u v : V}
    (hω : cluster ω x ⊆ S) (hη : cluster η x ⊆ S)
    (hconfig : ∀ a ∈ S, ∀ b ∈ S, (s(a, b) ∈ ω ↔ s(a, b) ∈ η))
    (hxy : ω ∈ conn x y) (hp : ω ∈ orientedPivotal x y u v) :
    η ∈ orientedPivotal x y u v := by
  have hxyη := (mem_conn_iff_of_cluster_subset_of_agree hω hη hconfig).mp hxy
  have hxv : ω ∈ conn x v :=
    conn_trans hxy (conn_mono sdiff_subset hp.2.2.2).symm
  have hxvη := (mem_conn_iff_of_cluster_subset_of_agree hω hη hconfig).mp hxv
  have hωdel : cluster (ω \ {s(u, v)}) x ⊆ S :=
    fun _ hz => hω (conn_mono sdiff_subset hz)
  have hηdel : cluster (η \ {s(u, v)}) x ⊆ S :=
    fun _ hz => hη (conn_mono sdiff_subset hz)
  have hωv : cluster (ω \ {s(u, v)}) v ⊆ S :=
    fun _ hz => hω (conn_trans hxv (conn_mono sdiff_subset hz))
  have hηv : cluster (η \ {s(u, v)}) v ⊆ S :=
    fun _ hz => hη (conn_trans hxvη (conn_mono sdiff_subset hz))
  have hdel : ∀ a ∈ S, ∀ b ∈ S,
      (s(a, b) ∈ ω \ {s(u, v)} ↔ s(a, b) ∈ η \ {s(u, v)}) := by
    intro a ha b hb
    simp only [mem_sdiff, mem_singleton_iff, hconfig a ha b hb]
  refine ⟨conn_mono (subset_insert _ _) hxyη, ?_, ?_, ?_⟩
  · exact fun h => hp.2.1
      ((mem_conn_iff_of_cluster_subset_of_agree hωdel hηdel hdel).mpr h)
  · exact (mem_conn_iff_of_cluster_subset_of_agree hωdel hηdel hdel).mp hp.2.2.1
  · exact (mem_conn_iff_of_cluster_subset_of_agree hωv hηv hdel).mp hp.2.2.2

/-- The lace event `E'` is determined by the internal configuration and vertex
memberships on any common set containing the two root clusters. -/
theorem mem_laceEPrime_iff_of_cluster_subset_of_agree
    {ω η : Config V} {A B S : Set V} {x y : V}
    (hω : cluster ω x ⊆ S) (hη : cluster η x ⊆ S)
    (hconfig : ∀ u ∈ S, ∀ v ∈ S, (s(u, v) ∈ ω ↔ s(u, v) ∈ η))
    (hsets : ∀ u ∈ S, u ∈ A ↔ u ∈ B) :
    (ω ∈ laceEPrime A x y ↔ η ∈ laceEPrime B x y) := by
  have ht (z : V) :=
    mem_throughSet_iff_of_cluster_subset_of_agree (y := z) hω hη hconfig hsets
  by_cases hxy : ω ∈ conn x y
  · have hxyη := (mem_conn_iff_of_cluster_subset_of_agree hω hη hconfig).mp hxy
    have hp (u v : V) :
        ω ∈ orientedPivotal x y u v ↔ η ∈ orientedPivotal x y u v :=
      ⟨mem_orientedPivotal_of_conn_of_cluster_subset_of_agree hω hη hconfig hxy,
        mem_orientedPivotal_of_conn_of_cluster_subset_of_agree hη hω
          (fun a ha b hb => (hconfig a ha b hb).symm) hxyη⟩
    simp only [laceEPrime, mem_sdiff, mem_iUnion, mem_inter_iff, ht, hp]
  · have hxyη : η ∉ conn x y := fun h => hxy
      ((mem_conn_iff_of_cluster_subset_of_agree hω hη hconfig).mpr h)
    exact ⟨fun h => (hxy h.1.1).elim, fun h => (hxyη h.1.1).elim⟩

end PercLib.Percolation.Bond.Lace
