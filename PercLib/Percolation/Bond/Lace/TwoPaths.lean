/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original constructive proofs; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.DoubleConnection
public import PercLib.Percolation.Bond.BoundarySusceptibility

/-!
# Two disjoint connections and absence of pivotal pairs

Double connection is transitive. To join two pairs of disjoint paths, stop the
second pair at its first contacts with the first pair and route to those contacts
along opposite sides. This uncrossing argument also proves the order-two
edge-Menger equivalence on the canonical bond interface, without finiteness or
countability assumptions on the ambient vertex type.
-/

@[expose] public section
noncomputable section
open Set
open scoped Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*} {G : SimpleGraph V}

/-- Stop a walk at its first visit to a set. Every edge of the prefix has an
endpoint outside the set. -/
private theorem exists_first_contact {z y : V} (r : G.Walk z y)
    (S : Set V) (hy : y ∈ S) :
    ∃ a ∈ S, ∃ t : G.Walk z a,
      t.edges ⊆ r.edges ∧ ∀ e ∈ t.edges, ∃ v ∈ e, v ∉ S := by
  induction r with
  | nil => exact ⟨_, hy, .nil, by simp, by simp⟩
  | @cons z w y hzw r ih =>
    by_cases hz : z ∈ S
    · exact ⟨z, hz, .nil, by simp, by simp⟩
    obtain ⟨a, ha, t, ht, hout⟩ := ih hy
    refine ⟨a, ha, .cons hzw t, ?_, ?_⟩
    · intro e he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he ⊢
      exact he.elim Or.inl (fun h => Or.inr (ht h))
    · intro e he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨z, by simp, hz⟩
      · exact hout e he

/-- Two disjoint trails give disjoint routes from their common start to any
two vertices on the first trail. -/
private theorem route_two_on_same {x y a b : V} (p q : G.Walk x y)
    (hp : p.IsTrail) (hd : p.edges.Disjoint q.edges)
    (ha : a ∈ p.support) (hb : b ∈ p.support) :
    ∃ f : G.Walk x a, ∃ g : G.Walk x b,
      f.edges.Disjoint g.edges ∧
      (∀ e ∈ f.edges, e ∈ p.edges ∨ e ∈ q.edges) ∧
      (∀ e ∈ g.edges, e ∈ p.edges ∨ e ∈ q.edges) := by
  let l := p.takeUntil a ha
  let r := p.dropUntil a ha
  have hl : l.edges ⊆ p.edges := p.edges_takeUntil_subset_edges ha
  have hr : r.edges ⊆ p.edges := p.edges_dropUntil_subset_edges ha
  have hlr : l.edges.Disjoint r.edges := hp.disjoint_edges_takeUntil_dropUntil ha
  by_cases hbr : b ∈ r.support
  · let t := r.dropUntil b hbr
    have ht : t.edges ⊆ r.edges := r.edges_dropUntil_subset_edges hbr
    refine ⟨l, q.append t.reverse, ?_, ?_, ?_⟩
    · intro e he he'
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
        List.mem_append, List.mem_reverse] at he'
      exact he'.elim (hd (hl he)) (fun h => hlr he (ht h))
    · exact fun e he => Or.inl (hl he)
    · intro e he
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
        List.mem_append, List.mem_reverse] at he
      exact he.elim Or.inr (fun h => Or.inl (hr (ht h)))
  · have hbl : b ∈ l.support := by
      have hs : l.append r = p := p.take_spec ha
      rw [← hs, SimpleGraph.Walk.mem_support_append_iff] at hb
      exact hb.resolve_right hbr
    let t := l.takeUntil b hbl
    have ht : t.edges ⊆ l.edges := l.edges_takeUntil_subset_edges hbl
    refine ⟨q.append r.reverse, t, ?_, ?_, ?_⟩
    · intro e he he'
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
        List.mem_append, List.mem_reverse] at he
      exact he.elim (fun h => hd (hl (ht he')) h) (fun h => hlr (ht he') h)
    · intro e he
      simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
        List.mem_append, List.mem_reverse] at he
      exact he.elim Or.inr (fun h => Or.inl (hr h))
    · exact fun e he => Or.inl (hl (ht he))

/-- Two disjoint trails route to any two vertices of their combined support. -/
private theorem route_two_contacts {x y a b : V} (p q : G.Walk x y)
    (hp : p.IsTrail) (hq : q.IsTrail) (hd : p.edges.Disjoint q.edges)
    (ha : a ∈ p.support ∨ a ∈ q.support) (hb : b ∈ p.support ∨ b ∈ q.support) :
    ∃ f : G.Walk x a, ∃ g : G.Walk x b,
      f.edges.Disjoint g.edges ∧
      (∀ e ∈ f.edges, e ∈ p.edges ∨ e ∈ q.edges) ∧
      (∀ e ∈ g.edges, e ∈ p.edges ∨ e ∈ q.edges) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact route_two_on_same p q hp hd ha hb
  · refine ⟨p.takeUntil a ha, q.takeUntil b hb, ?_, ?_, ?_⟩
    · exact fun _ he hf => hd (p.edges_takeUntil_subset_edges ha he)
        (q.edges_takeUntil_subset_edges hb hf)
    · exact fun _ he => Or.inl (p.edges_takeUntil_subset_edges ha he)
    · exact fun _ he => Or.inr (q.edges_takeUntil_subset_edges hb he)
  · refine ⟨q.takeUntil a ha, p.takeUntil b hb, ?_, ?_, ?_⟩
    · exact fun _ he hf => hd (p.edges_takeUntil_subset_edges hb hf)
        (q.edges_takeUntil_subset_edges ha he)
    · exact fun _ he => Or.inr (q.edges_takeUntil_subset_edges ha he)
    · exact fun _ he => Or.inl (p.edges_takeUntil_subset_edges hb he)
  · obtain ⟨f, g, hfg, hf, hg⟩ := route_two_on_same q p hq hd.symm ha hb
    exact ⟨f, g, hfg, fun e he => (hf e he).symm, fun e he => (hg e he).symm⟩

/-- Realize double connection by paths in the original open graph. -/
theorem exists_disjoint_paths_of_mem_doubleConn {ω : Config V} {x y : V}
    (h : ω ∈ doubleConn x y) :
    ∃ p q : (openGraph ω).Walk x y,
      p.IsPath ∧ q.IsPath ∧ p.edges.Disjoint q.edges := by
  obtain ⟨F, H, _, _, hd, hFω, hHω, hF, hH⟩ := (mem_doubleConn_iff ω x y).mp h
  obtain ⟨p, hp⟩ := (show (openGraph F).Reachable x y from hF).exists_isPath
  obtain ⟨q, hq⟩ := (show (openGraph H).Reachable x y from hH).exists_isPath
  have hpt : ∀ e ∈ p.edges, e ∈ (openGraph ω).edgeSet :=
    fun _ he => SimpleGraph.edgeSet_mono (openGraph_mono hFω) (p.edges_subset_edgeSet he)
  have hqt : ∀ e ∈ q.edges, e ∈ (openGraph ω).edgeSet :=
    fun _ he => SimpleGraph.edgeSet_mono (openGraph_mono hHω) (q.edges_subset_edgeSet he)
  refine ⟨p.transfer (openGraph ω) hpt, q.transfer (openGraph ω) hqt,
    hp.transfer hpt, hq.transfer hqt, ?_⟩
  simp only [SimpleGraph.Walk.edges_transfer]
  exact fun _ he hf => Set.disjoint_left.mp hd
    (mem_of_mem_edges_openGraph p he) (mem_of_mem_edges_openGraph q hf)

/-- Disjoint open walks supply the two finite certificates. -/
theorem mem_doubleConn_of_disjoint_walks {ω : Config V} {x y : V}
    (p q : (openGraph ω).Walk x y) (hd : p.edges.Disjoint q.edges) :
    ω ∈ doubleConn x y := by
  apply (mem_doubleConn_iff ω x y).mpr
  refine ⟨{e | e ∈ p.edges}, {e | e ∈ q.edges}, List.finite_toSet _,
    List.finite_toSet _, ?_, fun _ he => mem_of_mem_edges_openGraph p he,
    fun _ he => mem_of_mem_edges_openGraph q he, edges_mem_conn p, edges_mem_conn q⟩
  exact Set.disjoint_left.mpr (fun _ he hf => hd he hf)

/-- Double connection is transitive, even when the pairs of witnesses overlap. -/
theorem doubleConn_trans {ω : Config V} {x y z : V}
    (hxy : ω ∈ doubleConn x y) (hyz : ω ∈ doubleConn y z) :
    ω ∈ doubleConn x z := by
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn hxy
  have hzy : ω ∈ doubleConn z y := by rwa [doubleConn_comm]
  obtain ⟨r, s, _, _, hrs⟩ := exists_disjoint_paths_of_mem_doubleConn hzy
  let S : Set V := {v | v ∈ p.support ∨ v ∈ q.support}
  have hy : y ∈ S := Or.inl p.end_mem_support
  obtain ⟨a, ha, r', hr', hrout⟩ := exists_first_contact r S hy
  obtain ⟨b, hb, s', hs', hsout⟩ := exists_first_contact s S hy
  obtain ⟨f, g, hfg, hf, hg⟩ := route_two_contacts p q hp.isTrail hq.isTrail hpq ha hb
  have hout {u v : V} (t : (openGraph ω).Walk u v)
      (ht : ∀ e ∈ t.edges, ∃ w ∈ e, w ∉ S) {e : Sym2 V} (he : e ∈ t.edges) :
      ¬ (e ∈ p.edges ∨ e ∈ q.edges) := by
    obtain ⟨w, hwe, hw⟩ := ht e he
    intro he'
    apply hw
    exact he'.elim
      (fun h => Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges h hwe))
      (fun h => Or.inr (SimpleGraph.Walk.mem_support_of_mem_edges h hwe))
  apply mem_doubleConn_of_disjoint_walks (f.append r'.reverse) (g.append s'.reverse)
  intro e he he'
  simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
    List.mem_append, List.mem_reverse] at he he'
  rcases he with he | he <;> rcases he' with he' | he'
  · exact hfg he he'
  · exact hout s' hsout he' (hf e he)
  · exact hout r' hrout he (hg e he')
  · exact hrs (hr' he) (hs' he')

/-- If every step of a walk is doubly connected, so are its endpoints. -/
private theorem mem_doubleConn_of_walk_steps {ω : Config V} {x y : V}
    (p : (openGraph ω).Walk x y)
    (h : ∀ u v, s(u, v) ∈ p.edges → ω ∈ doubleConn u v) :
    ω ∈ doubleConn x y := by
  induction p with
  | nil => simp
  | @cons x u y hxu p ih =>
    apply doubleConn_trans (h x u (by simp))
    apply ih
    exact fun a b hab => h a b (by simp [hab])

/-- The order-two edge-Menger theorem for bond configurations. Deletion of
every single pair preserves connection exactly when two disjoint paths exist. -/
theorem mem_doubleConn_iff_isEdgeReachable_two {ω : Config V} {x y : V} :
    ω ∈ doubleConn x y ↔ (openGraph ω).IsEdgeReachable 2 x y := by
  refine ⟨isEdgeReachable_two_of_mem_doubleConn, fun h => ?_⟩
  obtain ⟨p, hp⟩ := (h.reachable (by simp)).exists_isPath
  apply mem_doubleConn_of_walk_steps p
  intro u v huv
  have hadj := p.adj_of_mem_edges huv
  have huv2 := hp.isTrail.isEdgeReachable_two_of_isEdgeReachable_two h
    (p.fst_mem_support_of_mem_edges huv) (p.snd_mem_support_of_mem_edges huv)
  apply mem_doubleConn_of_direct_of_deleted hadj.ne
    (mem_of_mem_edges_openGraph p huv)
  have hd := SimpleGraph.isEdgeReachable_two.mp huv2 s(u, v)
  change ((SimpleGraph.fromEdgeSet ω).deleteEdges {s(u, v)}).Reachable u v at hd
  rw [SimpleGraph.deleteEdges_fromEdgeSet] at hd
  exact hd

/-- A realized connection is double exactly when it has no pivotal pair. -/
@[tag "DLF1"]
theorem mem_doubleConn_iff_conn_and_no_pivotal {ω : Config V} {x y : V} :
    ω ∈ doubleConn x y ↔ ω ∈ conn x y ∧
      ∀ e : Sym2 V, ¬ (insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y) := by
  refine ⟨fun h => ⟨doubleConn_subset_conn x y h,
    not_pivotal_of_mem_doubleConn h⟩, fun ⟨hc, hn⟩ => ?_⟩
  rw [mem_doubleConn_iff_isEdgeReachable_two, SimpleGraph.isEdgeReachable_two]
  intro e
  have hd : ω \ {e} ∈ conn x y := by
    by_contra hnot
    exact hn e ⟨conn_mono (subset_insert _ _) hc, hnot⟩
  change ((SimpleGraph.fromEdgeSet ω).deleteEdges {e}).Reachable x y
  rw [SimpleGraph.deleteEdges_fromEdgeSet]
  exact hd

end PercLib.Percolation.Bond.Lace
