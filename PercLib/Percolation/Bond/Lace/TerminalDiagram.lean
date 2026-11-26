/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original proofs; no upstream code is copied.
The terminal diagram is the general-profile form of Heydenreich and van der
Hofstad (2017), Section 7.3, equation (7.3.8).
-/
module

public import PercLib.Percolation.Bond.Lace.FirstPivotal
public import PercLib.Percolation.Bond.Lace.CuttingFactorization
public import PercLib.Probability.DisjointOccurrenceAlgebra

/-!
# The terminal four-arm lace diagram

## Main results

The last doubly connected block of an `E'` connection must meet the required
vertex set. Splitting one of its two paths at such a vertex gives two arms to
the terminal endpoint, as well as a disjoint connection from the source.
The geometric inclusion does not require a countable or finite vertex set.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem path_meets_of_throughSet {A : Set V} {ω : Config V} {x y : V}
    (p : (openGraph ω).Walk x y) (h : ω ∈ throughSet A x y) :
    ∃ z ∈ p.support, z ∈ A := by
  classical
  by_contra hn
  push Not at hn
  exact h.2 ⟨hn x p.start_mem_support, hn y p.end_mem_support,
    ⟨p.induce Aᶜ hn⟩⟩

private theorem disjoint_edges_of_not_conn {ω : Config V} {a b c d : V}
    (p : (openGraph ω).Walk a b) (r : (openGraph ω).Walk c d)
    (h : ω ∉ conn a c) : p.edges.Disjoint r.edges := by
  classical
  intro e he hf
  induction e using Sym2.ind with
  | _ s t =>
    exact h (conn_trans
      ⟨p.takeUntil s (p.fst_mem_support_of_mem_edges he)⟩
      (show ω ∈ conn c s from
        ⟨r.takeUntil s (r.fst_mem_support_of_mem_edges hf)⟩).symm)

private theorem throughSet_tail_of_adj {A : Set V} {ω : Config V} {v y t s : V}
    (h : ω ∈ throughSet A v y) (hnt : ω ∉ throughSet A v t)
    (hvt : ω ∈ conn v t) (hts : (openGraph ω).Adj t s) (hsy : ω ∈ conn s y) :
    ω ∈ throughSet A s y := by
  classical
  have hav : ∃ hv : v ∈ Aᶜ, ∃ ht : t ∈ Aᶜ,
      ((openGraph ω).induce Aᶜ).Reachable ⟨v, hv⟩ ⟨t, ht⟩ := by
    by_contra hn
    exact hnt ⟨hvt, hn⟩
  obtain ⟨hv, ht, hvt'⟩ := hav
  refine ⟨hsy, ?_⟩
  rintro ⟨hs, hy, hsy'⟩
  have hadj : ((openGraph ω).induce Aᶜ).Adj ⟨t, ht⟩ ⟨s, hs⟩ := hts
  exact h.2 ⟨hv, hy, hvt'.trans (hadj.reachable.trans hsy')⟩

private theorem four_arms_of_prefix_paths {ω η : Config V} (hηω : η ⊆ ω)
    {v t z y : V} (p q : (openGraph η).Walk t y) (r : (openGraph ω).Walk v t)
    (hp : p.IsPath) (hpq : p.edges.Disjoint q.edges)
    (hpr : p.edges.Disjoint r.edges) (hqr : q.edges.Disjoint r.edges)
    (hz : z ∈ p.support) :
    ω ∈ disjointOccurrence
      (disjointOccurrence (disjointOccurrence (conn t z) (conn z y)) (conn t y))
      (conn v t) := by
  classical
  apply (mem_disjointOccurrence_three_iff
    (isUpperSet_disjointOccurrence (isUpperSet_conn t z) (isUpperSet_conn z y))
    (isUpperSet_conn t y) (isUpperSet_conn v t) ω).mpr
  refine ⟨{e | e ∈ p.edges}, {e | e ∈ q.edges}, {e | e ∈ r.edges},
    List.finite_toSet _, List.finite_toSet _, List.finite_toSet _,
    Set.disjoint_left.mpr (fun _ he hf => hpq he hf),
    Set.disjoint_left.mpr (fun _ he hf => hpr he hf),
    Set.disjoint_left.mpr (fun _ he hf => hqr he hf),
    fun _ he => hηω (mem_of_mem_edges_openGraph p he),
    fun _ he => hηω (mem_of_mem_edges_openGraph q he),
    fun _ he => mem_of_mem_edges_openGraph r he, ?_, edges_mem_conn q, edges_mem_conn r⟩
  apply (mem_disjointOccurrence_iff_open (isUpperSet_conn t z) (isUpperSet_conn z y) _).mpr
  refine ⟨{e | e ∈ (p.takeUntil z hz).edges}, {e | e ∈ (p.dropUntil z hz).edges},
    List.finite_toSet _, List.finite_toSet _, ?_,
    p.edges_takeUntil_subset_edges hz, p.edges_dropUntil_subset_edges hz,
    edges_mem_conn _, edges_mem_conn _⟩
  exact Set.disjoint_left.mpr
    (fun _ he hf => hp.isTrail.disjoint_edges_takeUntil_dropUntil hz he hf)

/-- The last doubly connected block of an `E'` connection meets the required
set. The resulting four connection witnesses are pairwise edge-disjoint. -/
theorem laceEPrime_subset_iUnion_terminal (A : Set V) (v y : V) :
    laceEPrime A v y ⊆ ⋃ z : A, ⋃ t : V,
      disjointOccurrence
        (disjointOccurrence (disjointOccurrence (conn t (z : V)) (conn (z : V) y))
          (conn t y)) (conn v t) := by
  classical
  intro ω h
  have hrev : ω ∈ conn y v := h.1.1.symm
  rw [conn_eq_doubleConn_union_firstPivotal y v] at hrev
  rcases hrev with hd | hc
  · rw [doubleConn_comm y v] at hd
    obtain ⟨p, q, hp, _, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn hd
    obtain ⟨z, hzp, hzA⟩ := path_meets_of_throughSet p h.1
    refine mem_iUnion.mpr ⟨⟨z, hzA⟩, mem_iUnion.mpr ⟨v, ?_⟩⟩
    exact four_arms_of_prefix_paths Subset.rfl p q .nil hp hpq (by simp) (by simp) hzp
  · obtain ⟨s, t, hc⟩ := by simpa only [mem_iUnion] using hc
    have hp := hc.1.2
    have hyt : ω \ {s(s, t)} ∉ conn y t := by
      intro hyt
      exact hp.2.1 (conn_trans hyt hp.2.2.2)
    have hdouble : ω \ {s(s, t)} ∈ doubleConn s y := by
      have hd := (laceEPrime_sdiff_iff_of_same_deleted_cluster univ hp.2.2.1 hyt).mp hc.1.1
      simpa only [laceEPrime_univ, doubleConn_comm y s] using hd
    have heq : s(t, s) = s(s, t) := Sym2.eq_swap
    have hpforward : ω ∈ orientedPivotal v y t s := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [heq]
        exact hp.1.symm
      · rw [heq]
        exact fun hh => hp.2.1 hh.symm
      · rw [heq]
        exact hp.2.2.2.symm
      · rw [heq]
        exact hp.2.2.1.symm
    have hnt : ω ∉ throughSet A v t := fun ht =>
      h.2 (mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨s, hpforward, ht⟩⟩)
    have hadj : (openGraph ω).Adj t s := (openGraph_adj_iff ω t s).mpr
      ⟨heq.symm ▸ hc.2, Ne.symm (orientedPivotal_ne hp)⟩
    have hthrough : ω ∈ throughSet A s y := throughSet_tail_of_adj h.1 hnt
      (conn_mono sdiff_subset hp.2.2.2.symm) hadj (conn_mono sdiff_subset hp.2.2.1.symm)
    have hthrough' : ω \ {s(s, t)} ∈ throughSet A s y :=
      (throughSet_sdiff_iff_of_same_deleted_cluster A Subset.rfl hp.2.2.1
        (SimpleGraph.Reachable.refl y) hyt).mp hthrough
    obtain ⟨p, q, hpath, _, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn hdouble
    obtain ⟨z, hzp, hzA⟩ := path_meets_of_throughSet p hthrough'
    obtain ⟨r₀⟩ := hp.2.2.2.symm
    let r' := r₀.transfer (openGraph ω) fun e he =>
      SimpleGraph.edgeSet_mono (openGraph_mono sdiff_subset) (r₀.edges_subset_edgeSet he)
    let r := r'.append (.cons hadj .nil)
    have hnvs : ω \ {s(s, t)} ∉ conn v s := by
      intro hvs
      exact hp.2.1 (conn_trans hp.2.2.1 hvs.symm)
    have hdisj (l : (openGraph (ω \ {s(s, t)})).Walk s y) :
        r.edges.Disjoint l.edges := by
      intro e he hl
      simp only [r, r', SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_transfer,
        SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | rfl
      · exact disjoint_edges_of_not_conn r₀ l hnvs he hl
      · have hf : s(s, t) ∈ l.edges := (congrArg (fun e => e ∈ l.edges) heq).mp hl
        exact (mem_of_mem_edges_openGraph l hf).2 (mem_singleton _)
    refine mem_iUnion.mpr ⟨⟨z, hzA⟩, mem_iUnion.mpr ⟨s, ?_⟩⟩
    exact four_arms_of_prefix_paths sdiff_subset p q r hpath hpq
      (hdisj p).symm (hdisj q).symm hzp

/-- The terminal lace bound has constant one and retains two connection
factors at the terminal endpoint, avoiding a susceptibility factor. -/
theorem law_laceEPrime_le_terminal [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (v y : V) :
    law q (laceEPrime A v y) ≤ ∑' z : A, ∑' t : V,
      tau q v t * tau q t (z : V) * tau q t y * tau q (z : V) y := by
  classical
  refine (measure_mono (laceEPrime_subset_iUnion_terminal A v y)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun z =>
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun t => ?_)))
  have h1 := countable_profile_bk q (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) y)
  have h2 := countable_profile_bk q
    (isUpperSet_disjointOccurrence (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) y))
    (isUpperSet_conn t y)
  have h3 := countable_profile_bk q
    (isUpperSet_disjointOccurrence
      (isUpperSet_disjointOccurrence (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) y))
      (isUpperSet_conn t y)) (isUpperSet_conn v t)
  refine h3.trans ((mul_le_mul' (h2.trans (mul_le_mul' h1 le_rfl)) le_rfl).trans_eq ?_)
  change ((tau q t (z : V) * tau q (z : V) y) * tau q t y) * tau q v t = _
  ac_rfl

example (x : V) : (∅ : Config V) ∈ laceEPrime {x} x x := by
  classical
  simp

end PercLib.Percolation.Bond.Lace
