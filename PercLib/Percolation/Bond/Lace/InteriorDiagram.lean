/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Original proofs; no upstream code is copied.
The two interior diagrams follow Heydenreich and van der Hofstad (2017),
Section 7.3, equation (7.3.9), retaining bond deletion and removing the
duplicate case where the attachment and terminal-block roots coincide.
-/
module

public import PercLib.Percolation.Bond.Lace.TerminalDiagram

/-! # The interior six-arm lace diagrams -/

@[expose] public section
noncomputable section
open Set MeasureTheory PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem path_meets_of_throughSet {A : Set V} {ω : Config V} {x y : V}
    (p : (openGraph ω).Walk x y) (h : ω ∈ throughSet A x y) :
    ∃ z ∈ p.support, z ∈ A := by
  by_contra hn
  push Not at hn
  exact h.2 ⟨hn x p.start_mem_support, hn y p.end_mem_support, ⟨p.induce Aᶜ hn⟩⟩

private theorem disjoint_edges_of_not_conn {ω : Config V} {a b c d : V}
    (p : (openGraph ω).Walk a b) (r : (openGraph ω).Walk c d)
    (h : ω ∉ conn a c) : p.edges.Disjoint r.edges := by
  intro e he hf
  induction e using Sym2.ind with
  | _ s t =>
    exact h (conn_trans ⟨p.takeUntil s (p.fst_mem_support_of_mem_edges he)⟩
      (show ω ∈ conn c s from ⟨r.takeUntil s (r.fst_mem_support_of_mem_edges hf)⟩).symm)

private theorem throughSet_tail_of_adj {A : Set V} {ω : Config V} {v y t s : V}
    (h : ω ∈ throughSet A v y) (hnt : ω ∉ throughSet A v t)
    (hvt : ω ∈ conn v t) (hts : (openGraph ω).Adj t s) (hsy : ω ∈ conn s y) :
    ω ∈ throughSet A s y := by
  have hav : ∃ hv : v ∈ Aᶜ, ∃ ht : t ∈ Aᶜ,
      ((openGraph ω).induce Aᶜ).Reachable ⟨v, hv⟩ ⟨t, ht⟩ := by
    by_contra hn
    exact hnt ⟨hvt, hn⟩
  obtain ⟨hv, ht, hvt'⟩ := hav
  refine ⟨hsy, ?_⟩
  rintro ⟨hs, hy, hsy'⟩
  have hadj : ((openGraph ω).induce Aᶜ).Adj ⟨t, ht⟩ ⟨s, hs⟩ := hts
  exact h.2 ⟨hv, hy, hvt'.trans (hadj.reachable.trans hsy')⟩

/-- An `E'` connection has a simple stem and two disjoint terminal paths,
each meeting the required set. All three paths are edge-disjoint. -/
theorem exists_terminal_paths_of_mem_laceEPrime {A : Set V} {ω : Config V} {v u : V}
    (h : ω ∈ laceEPrime A v u) :
    ∃ t : V, ∃ p q : (openGraph ω).Walk t u, ∃ r : (openGraph ω).Walk v t,
      p.IsPath ∧ q.IsPath ∧ r.IsPath ∧ p.edges.Disjoint q.edges ∧
      p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges ∧
      (∃ z ∈ p.support, z ∈ A) ∧ (∃ z ∈ q.support, z ∈ A) := by
  have hrev : ω ∈ conn u v := h.1.1.symm
  rw [conn_eq_doubleConn_union_firstPivotal u v] at hrev
  rcases hrev with hd | hc
  · rw [doubleConn_comm u v] at hd
    obtain ⟨p, q, hp, hq, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn hd
    exact ⟨v, p, q, .nil, hp, hq, .nil, hpq, by simp, by simp,
      path_meets_of_throughSet p h.1, path_meets_of_throughSet q h.1⟩
  · obtain ⟨s, t, hc⟩ := by simpa only [mem_iUnion] using hc
    have hp := hc.1.2
    have hut : ω \ {s(s, t)} ∉ conn u t := by
      intro hut
      exact hp.2.1 (conn_trans hut hp.2.2.2)
    have hdouble : ω \ {s(s, t)} ∈ doubleConn s u := by
      have hd := (laceEPrime_sdiff_iff_of_same_deleted_cluster univ hp.2.2.1 hut).mp hc.1.1
      simpa only [laceEPrime_univ, doubleConn_comm u s] using hd
    have heq : s(t, s) = s(s, t) := Sym2.eq_swap
    have hpforward : ω ∈ orientedPivotal v u t s := by
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
    have hthrough : ω ∈ throughSet A s u := throughSet_tail_of_adj h.1 hnt
      (conn_mono sdiff_subset hp.2.2.2.symm) hadj (conn_mono sdiff_subset hp.2.2.1.symm)
    have hthrough' : ω \ {s(s, t)} ∈ throughSet A s u :=
      (throughSet_sdiff_iff_of_same_deleted_cluster A Subset.rfl hp.2.2.1
        (SimpleGraph.Reachable.refl u) hut).mp hthrough
    obtain ⟨p, q, hpath, hqpath, hpq⟩ := exists_disjoint_paths_of_mem_doubleConn hdouble
    obtain ⟨r₀⟩ := hp.2.2.2.symm
    let r' := r₀.transfer (openGraph ω) fun e he =>
      SimpleGraph.edgeSet_mono (openGraph_mono sdiff_subset) (r₀.edges_subset_edgeSet he)
    let r := r'.append (.cons hadj .nil)
    have hnvs : ω \ {s(s, t)} ∉ conn v s := by
      intro hvs
      exact hp.2.1 (conn_trans hp.2.2.1 hvs.symm)
    have hdisj (l : (openGraph (ω \ {s(s, t)})).Walk s u) :
        r.edges.Disjoint l.edges := by
      intro e he hl
      simp only [r, r', SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_transfer,
        SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | rfl
      · exact disjoint_edges_of_not_conn r₀ l hnvs he hl
      · have hf : s(s, t) ∈ l.edges := (congrArg (fun e => e ∈ l.edges) heq).mp hl
        exact (mem_of_mem_edges_openGraph l hf).2 (mem_singleton _)
    have htransfer (l : (openGraph (ω \ {s(s, t)})).Walk s u) :
        ∀ e ∈ l.edges, e ∈ (openGraph ω).edgeSet :=
      fun _ he => SimpleGraph.edgeSet_mono (openGraph_mono sdiff_subset) (l.edges_subset_edgeSet he)
    refine ⟨s, p.transfer (openGraph ω) (htransfer p),
      q.transfer (openGraph ω) (htransfer q), r.bypass,
      hpath.transfer (htransfer p), hqpath.transfer (htransfer q), r.bypass_isPath,
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.edges_transfer] using hpq
    · simpa only [SimpleGraph.Walk.edges_transfer] using
        (show p.edges.Disjoint r.bypass.edges from
          fun _ he hf => hdisj p (r.edges_bypass_subset_edges hf) he)
    · simpa only [SimpleGraph.Walk.edges_transfer] using
        (show q.edges.Disjoint r.bypass.edges from
          fun _ he hf => hdisj q (r.edges_bypass_subset_edges hf) he)
    · simpa only [SimpleGraph.Walk.support_transfer] using path_meets_of_throughSet p hthrough'
    · simpa only [SimpleGraph.Walk.support_transfer] using path_meets_of_throughSet q hthrough'

private theorem first_contact {G : SimpleGraph V} {a v : V} (r : G.Walk a v)
    (S : Set V) (hv : v ∈ S) :
    ∃ w ∈ S, ∃ b : G.Walk a w, ∀ e ∈ b.edges, ∃ z ∈ e, z ∉ S := by
  induction r with
  | nil => exact ⟨_, hv, .nil, by simp⟩
  | @cons a c v hac r ih =>
    by_cases ha : a ∈ S
    · exact ⟨a, ha, .nil, by simp⟩
    obtain ⟨w, hw, b, hb⟩ := ih hv
    refine ⟨w, hw, .cons hac b, ?_⟩
    intro e he
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨a, by simp, ha⟩
    · exact hb e he

private theorem split_edges_mem {ω : Config V} {x y z : V}
    (p : (openGraph ω).Walk x y) (hp : p.IsPath) (hz : z ∈ p.support) :
    {e | e ∈ p.edges} ∈ disjointOccurrence (conn x z) (conn z y) := by
  apply (mem_disjointOccurrence_iff_open (isUpperSet_conn x z) (isUpperSet_conn z y) _).mpr
  refine ⟨{e | e ∈ (p.takeUntil z hz).edges}, {e | e ∈ (p.dropUntil z hz).edges},
    List.finite_toSet _, List.finite_toSet _, ?_,
    p.edges_takeUntil_subset_edges hz, p.edges_dropUntil_subset_edges hz,
    edges_mem_conn _, edges_mem_conn _⟩
  exact Set.disjoint_left.mpr
    (fun _ he hf => hp.isTrail.disjoint_edges_takeUntil_dropUntil hz he hf)

private theorem four_disjoint_certificates
    {A B C D : Set (Config V)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hC : IsUpperSet C) (hD : IsUpperSet D) {ω F H K L : Config V}
    (hF : F.Finite) (hH : H.Finite) (hK : K.Finite) (hL : L.Finite)
    (hFH : Disjoint F H) (hFK : Disjoint F K) (hFL : Disjoint F L)
    (hHK : Disjoint H K) (hHL : Disjoint H L) (hKL : Disjoint K L)
    (hFω : F ⊆ ω) (hHω : H ⊆ ω) (hKω : K ⊆ ω) (hLω : L ⊆ ω)
    (hFA : F ∈ A) (hHB : H ∈ B) (hKC : K ∈ C) (hLD : L ∈ D) :
    ω ∈ disjointOccurrence (disjointOccurrence (disjointOccurrence A B) C) D := by
  apply (mem_disjointOccurrence_three_iff (isUpperSet_disjointOccurrence hA hB) hC hD ω).mpr
  refine ⟨F ∪ H, K, L, hF.union hH, hK, hL,
    disjoint_union_left.mpr ⟨hFK, hHK⟩, disjoint_union_left.mpr ⟨hFL, hHL⟩, hKL,
    union_subset hFω hHω, hKω, hLω, ?_, hKC, hLD⟩
  exact (mem_disjointOccurrence_iff_open hA hB (F ∪ H)).mpr
    ⟨F, H, hF, hH, hFH, subset_union_left, subset_union_right, hFA, hHB⟩

private theorem four_walk_certificates {ω : Config V} (e : Sym2 V)
    {x₁ y₁ x₂ y₂ x₃ y₃ a w : V}
    (p : (openGraph ω).Walk x₁ y₁) (q : (openGraph ω).Walk x₂ y₂)
    (r : (openGraph ω).Walk x₃ y₃) (b : (openGraph (ω \ {e})).Walk a w)
    {A B C : Set (Config V)} (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C)
    (hpq : p.edges.Disjoint q.edges) (hpr : p.edges.Disjoint r.edges)
    (hpb : p.edges.Disjoint b.edges) (hqr : q.edges.Disjoint r.edges)
    (hqb : q.edges.Disjoint b.edges) (hrb : r.edges.Disjoint b.edges)
    (hpA : {f | f ∈ p.edges} ∈ A) (hqB : {f | f ∈ q.edges} ∈ B)
    (hrC : {f | f ∈ r.edges} ∈ C) :
    ω ∈ disjointOccurrence (disjointOccurrence (disjointOccurrence A B) C)
      {η : Config V | η \ {e} ∈ conn w a} := by
  apply four_disjoint_certificates hA hB hC
    (fun _ _ h hη => conn_mono (sdiff_subset_sdiff_left h) hη)
    (List.finite_toSet _) (List.finite_toSet _) (List.finite_toSet _) (List.finite_toSet _)
    (Set.disjoint_left.mpr (fun _ hf hg => hpq hf hg))
    (Set.disjoint_left.mpr (fun _ hf hg => hpr hf hg))
    (Set.disjoint_left.mpr (fun _ hf hg => hpb hf hg))
    (Set.disjoint_left.mpr (fun _ hf hg => hqr hf hg))
    (Set.disjoint_left.mpr (fun _ hf hg => hqb hf hg))
    (Set.disjoint_left.mpr (fun _ hf hg => hrb hf hg))
    (fun _ hf => mem_of_mem_edges_openGraph p hf)
    (fun _ hf => mem_of_mem_edges_openGraph q hf)
    (fun _ hf => mem_of_mem_edges_openGraph r hf)
    (fun _ hf => (mem_of_mem_edges_openGraph b hf).1) hpA hqB hrC
  have he : e ∉ {f | f ∈ b.edges} := by
    intro he
    exact (mem_of_mem_edges_openGraph b he).2 (mem_singleton _)
  change {f | f ∈ b.edges} \ {e} ∈ conn w a
  rw [sdiff_singleton_eq_self he, conn_symm w a]
  exact edges_mem_conn b

/-- An interior lace layer has one of two six-arm diagrams. The outgoing arm
retains the deleted pair. In the second diagram the stem-attachment vertex
differs from the terminal-block root, removing their common degenerate case. -/
theorem laceEPrime_inter_deleted_subset_iUnion_interior
    (A : Set V) (v u a : V) (e : Sym2 V) :
    laceEPrime A v u ∩ {ω : Config V | ω \ {e} ∈ conn v a} ⊆
      ⋃ z : A, ⋃ t : V, ⋃ w : V,
        disjointOccurrence
          (disjointOccurrence
            (disjointOccurrence (disjointOccurrence (conn t w) (conn w u))
              (disjointOccurrence (conn t (z : V)) (conn (z : V) u))) (conn v t))
          {ω : Config V | ω \ {e} ∈ conn w a} ∪
        (if w = t then ∅ else
          disjointOccurrence
            (disjointOccurrence
              (disjointOccurrence (disjointOccurrence (conn v w) (conn w t))
                (disjointOccurrence (conn t (z : V)) (conn (z : V) u))) (conn t u))
            {ω : Config V | ω \ {e} ∈ conn w a}) := by
  intro ω h
  obtain ⟨t, p, q, r, hp, hq, hr, hpq, hpr, hqr,
    ⟨zp, hzp, hzpA⟩, ⟨zq, hzq, hzqA⟩⟩ :=
    exists_terminal_paths_of_mem_laceEPrime h.1
  obtain ⟨r₀⟩ := (show (openGraph (ω \ {e})).Reachable v a from h.2).symm
  let S : Set V := {z | z ∈ p.support ∨ z ∈ q.support ∨ z ∈ r.support}
  obtain ⟨w, hw, b, hb⟩ := first_contact r₀ S (Or.inr (Or.inr r.start_mem_support))
  have hout {f : Sym2 V} (hf : f ∈ b.edges) :
      ¬ (f ∈ p.edges ∨ f ∈ q.edges ∨ f ∈ r.edges) := by
    obtain ⟨z, hzf, hz⟩ := hb f hf
    rintro (h | h | h)
    · exact hz (Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges h hzf))
    · exact hz (Or.inr (Or.inl (SimpleGraph.Walk.mem_support_of_mem_edges h hzf)))
    · exact hz (Or.inr (Or.inr (SimpleGraph.Walk.mem_support_of_mem_edges h hzf)))
  have hpb : p.edges.Disjoint b.edges := fun _ hf hg => hout hg (Or.inl hf)
  have hqb : q.edges.Disjoint b.edges := fun _ hf hg => hout hg (Or.inr (Or.inl hf))
  have hrb : r.edges.Disjoint b.edges := fun _ hf hg => hout hg (Or.inr (Or.inr hf))
  by_cases hwcycle : w ∈ p.support ∨ w ∈ q.support
  · rcases hwcycle with hwp | hwq
    · refine mem_iUnion.mpr ⟨⟨zq, hzqA⟩, mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨w, Or.inl ?_⟩⟩⟩
      exact four_walk_certificates e p q r b
        (isUpperSet_disjointOccurrence (isUpperSet_conn t w) (isUpperSet_conn w u))
        (isUpperSet_disjointOccurrence (isUpperSet_conn t zq) (isUpperSet_conn zq u))
        (isUpperSet_conn v t) hpq hpr hpb hqr hqb hrb
        (split_edges_mem p hp hwp) (split_edges_mem q hq hzq) (edges_mem_conn r)
    · refine mem_iUnion.mpr ⟨⟨zp, hzpA⟩, mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨w, Or.inl ?_⟩⟩⟩
      exact four_walk_certificates e q p r b
        (isUpperSet_disjointOccurrence (isUpperSet_conn t w) (isUpperSet_conn w u))
        (isUpperSet_disjointOccurrence (isUpperSet_conn t zp) (isUpperSet_conn zp u))
        (isUpperSet_conn v t) hpq.symm hqr hqb hpr hpb hrb
        (split_edges_mem q hq hwq) (split_edges_mem p hp hzp) (edges_mem_conn r)
  · have hwr : w ∈ r.support := by
      rcases hw with hwp | hwq | hwr
      · exact (hwcycle (Or.inl hwp)).elim
      · exact (hwcycle (Or.inr hwq)).elim
      · exact hwr
    have hwt : w ≠ t := by
      intro hwt
      exact hwcycle (Or.inl
        ((congrArg (fun z : V => z ∈ p.support) hwt.symm).mp p.start_mem_support))
    refine mem_iUnion.mpr ⟨⟨zp, hzpA⟩, mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨w, Or.inr ?_⟩⟩⟩
    rw [ite_eq_right hwt]
    exact four_walk_certificates e r p q b
      (isUpperSet_disjointOccurrence (isUpperSet_conn v w) (isUpperSet_conn w t))
      (isUpperSet_disjointOccurrence (isUpperSet_conn t zp) (isUpperSet_conn zp u))
      (isUpperSet_conn t u) hpr.symm hqr.symm hrb hpq hpb hqb
      (split_edges_mem r hr hwr) (split_edges_mem p hp hzp) (edges_mem_conn q)

private theorem law_four_le [Countable V] (q : Sym2 V → unitInterval)
    {A B C D : Set (Config V)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hC : IsUpperSet C) (hD : IsUpperSet D) {a b c d : ℝ≥0∞}
    (ha : law q A ≤ a) (hb : law q B ≤ b) (hc : law q C ≤ c) (hd : law q D ≤ d) :
    law q (disjointOccurrence (disjointOccurrence (disjointOccurrence A B) C) D) ≤
      a * b * c * d := by
  have h1 := (countable_profile_bk q hA hB).trans (mul_le_mul' ha hb)
  have h2 := (countable_profile_bk q (isUpperSet_disjointOccurrence hA hB) hC).trans
    (mul_le_mul' h1 hc)
  exact (countable_profile_bk q
    (isUpperSet_disjointOccurrence (isUpperSet_disjointOccurrence hA hB) hC) hD).trans
    (mul_le_mul' h2 hd)

/-- BK bounds the two interior diagrams separately, retaining the deleted
outgoing arm and omitting the duplicate `w=t` term of the second diagram. -/
theorem law_laceEPrime_inter_deleted_le_interior [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (v u a : V) (e : Sym2 V) :
    law q (laceEPrime A v u ∩ {ω : Config V | ω \ {e} ∈ conn v a}) ≤
      ∑' z : A, ∑' t : V, ∑' w : V,
        ((tau q t w * tau q w u) * (tau q t (z : V) * tau q (z : V) u) * tau q v t +
          if w = t then 0 else
            (tau q v w * tau q w t) * (tau q t (z : V) * tau q (z : V) u) * tau q t u) *
          law q {ω : Config V | ω \ {e} ∈ conn w a} := by
  refine (measure_mono (laceEPrime_inter_deleted_subset_iUnion_interior A v u a e)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun z =>
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun t =>
        (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun w => ?_))))
  refine (measure_union_le _ _).trans ?_
  rw [add_mul]
  have hD : IsUpperSet {ω : Config V | ω \ {e} ∈ conn w a} :=
    fun _ _ h hω => conn_mono (sdiff_subset_sdiff_left h) hω
  apply add_le_add
  · exact law_four_le q
      (isUpperSet_disjointOccurrence (isUpperSet_conn t w) (isUpperSet_conn w u))
      (isUpperSet_disjointOccurrence (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) u))
      (isUpperSet_conn v t) hD
      (countable_profile_bk q (isUpperSet_conn t w) (isUpperSet_conn w u))
      (countable_profile_bk q (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) u))
      le_rfl le_rfl
  · by_cases hwt : w = t
    · simp [hwt]
    · simp only [ite_eq_right hwt]
      exact law_four_le q
        (isUpperSet_disjointOccurrence (isUpperSet_conn v w) (isUpperSet_conn w t))
        (isUpperSet_disjointOccurrence (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) u))
        (isUpperSet_conn t u) hD
        (countable_profile_bk q (isUpperSet_conn v w) (isUpperSet_conn w t))
        (countable_profile_bk q (isUpperSet_conn t (z : V)) (isUpperSet_conn (z : V) u))
        le_rfl le_rfl

example (x : V) (e : Sym2 V) : (∅ : Config V) ∈
    laceEPrime {x} x x ∩ {ω : Config V | ω \ {e} ∈ conn x x} := by simp [conn_self]

end PercLib.Percolation.Bond.Lace
