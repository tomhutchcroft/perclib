/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond interface. Source motivation: M. Aizenman and C. M. Newman, "Tree
graph inequalities and critical behavior in percolation models", J. Stat. Phys. 36 (1984), and the
wiki proof of L82Q. No source text or code is copied.
-/
module

public import PercLib.Percolation.Bond.TreeGraph.Defs
public import PercLib.Probability.CountableBK
public import PercLib.Probability.OpenEventHarris
public import PercLib.Combinatorics.TreeSplitting

/-! # Branch points and the tree-graph inequality

* `exists_branch_finset`: in the graph of a finite edge set `F`, if `o` is joined to every
  `x i`, `i ∈ I`, `|I| ≥ 2`, then there are a vertex `z`, a split `I = A ⊔ (I \ A)` into
  nonempty parts and three pairwise disjoint subsets of `F` joining `o` to `z`, `z` to every
  `x i` with `i ∈ A`, and `z` to every `x i` with `i ∈ I \ A`. Empty paths are allowed.
* `exists_branch_mem`: the same for an open configuration, as a disjoint occurrence
  `{o ↔ z} ∘ ({z ↔ x_A} ∘ {z ↔ x_(I∖A)})`, with a prescribed index in `A`.
* `law_forall_conn_le`: the union bound and BK twice.
* `treeGraphInequality : TreeGraphInequality V` (L82Q) for every countable `V`.

The proof of `exists_branch_finset` is by strong induction on `|F|`. If some `x i` equals
`o`, split off `{i}` at `z = o`. Otherwise delete the edges at `o`; every `x i` is then
joined to a neighbour of `o`. If every `x i` is joined to the same neighbour `c`, move the
root to `c`; if not, split at `z = o` along the component of `c`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set SimpleGraph
open scoped ENNReal

namespace PercLib.Percolation.Bond

open PercLib.Probability PercLib

variable {V : Type*} {ι : Type*}

/-! ### Deleting the edges at a vertex -/

/-- If `v ≠ o` is reachable from `o` in the graph of `F`, then `v` is reachable from a
neighbour `c` of `o` without the edges at `o`. -/
theorem exists_nbr_reachable_avoid [DecidableEq V] {F : Finset (Sym2 V)} {o v : V}
    (h : (fromEdgeSet (F : Set (Sym2 V))).Reachable o v) (hne : o ≠ v) :
    ∃ c, s(o, c) ∈ F ∧ o ≠ c ∧
      (fromEdgeSet ((F.filter fun e => o ∉ e : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
        c v := by
  obtain ⟨p, hp⟩ := h.exists_isPath
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ c _ hadj p' =>
    obtain ⟨h1, h2⟩ := (fromEdgeSet_adj _).1 hadj
    have hnot : o ∉ p'.support := ((Walk.cons_isPath_iff hadj p').1 hp).2
    refine ⟨c, h1, h2, ⟨p'.transfer _ fun e he => ?_⟩⟩
    have heF := p'.edges_subset_edgeSet he
    rw [edgeSet_fromEdgeSet] at heF ⊢
    refine ⟨?_, heF.2⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨heF.1, fun ho => hnot ?_⟩
    induction e using Sym2.ind with
    | h a b =>
      rcases Sym2.mem_iff.1 ho with rfl | rfl
      · exact p'.fst_mem_support_of_mem_edges he
      · exact p'.snd_mem_support_of_mem_edges he

/-! ### The finite branch point -/

/-- **Branch point in a finite edge set.** If `o` is joined to every `x i`, `i ∈ I`, in the
graph of a finite edge set `F` and `|I| ≥ 2`, then there are `z`, a split of `I` into
nonempty parts `A` and `I \ A`, and pairwise disjoint `F₀, F_A, F_B ⊆ F` with `o ↔ z` in
`F₀`, `z ↔ x i` in `F_A` for `i ∈ A` and `z ↔ x i` in `F_B` for `i ∈ I \ A`. -/
theorem exists_branch_finset [DecidableEq V] [DecidableEq ι] (x : ι → V) (I : Finset ι)
    (hI : 1 < I.card)
    (F : Finset (Sym2 V)) (o : V)
    (ho : ∀ i ∈ I, (fromEdgeSet (F : Set (Sym2 V))).Reachable o (x i)) :
    ∃ z : V, ∃ A ⊆ I, A.Nonempty ∧ (I \ A).Nonempty ∧
      ∃ F₀ FA FB : Finset (Sym2 V), F₀ ⊆ F ∧ FA ⊆ F ∧ FB ⊆ F ∧
        Disjoint F₀ FA ∧ Disjoint F₀ FB ∧ Disjoint FA FB ∧
        (fromEdgeSet (F₀ : Set (Sym2 V))).Reachable o z ∧
        (∀ i ∈ A, (fromEdgeSet (FA : Set (Sym2 V))).Reachable z (x i)) ∧
        (∀ i ∈ I \ A, (fromEdgeSet (FB : Set (Sym2 V))).Reachable z (x i)) := by
  classical
  induction F using Finset.strongInduction generalizing o with
  | H F ih =>
  -- some target is the root itself
  by_cases hox : ∃ i ∈ I, x i = o
  · obtain ⟨i, hi, hio⟩ := hox
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hI i
    refine ⟨o, {i}, Finset.singleton_subset_iff.2 hi, Finset.singleton_nonempty i,
      ⟨j, Finset.mem_sdiff.2 ⟨hj, by simpa using hji⟩⟩, ∅, ∅, F, Finset.empty_subset _,
      Finset.empty_subset _, subset_rfl, Finset.disjoint_empty_left _,
      Finset.disjoint_empty_left _, Finset.disjoint_empty_left _, Reachable.rfl, ?_,
      fun k hk => ho k (Finset.mem_sdiff.1 hk).1⟩
    intro k hk
    rw [Finset.mem_singleton.1 hk, hio]
  push Not at hox
  obtain ⟨i₀, hi₀⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  set F' : Finset (Sym2 V) := F.filter fun e => o ∉ e with hF'
  obtain ⟨c, hcF, hoc, hc₀⟩ := exists_nbr_reachable_avoid (ho i₀ hi₀) (hox i₀ hi₀).symm
  have hocF' : s(o, c) ∉ F' := fun h => (Finset.mem_filter.1 h).2 (Sym2.mem_mk_left o c)
  have hF'F : F' ⊆ F := Finset.filter_subset _ _
  by_cases hall : ∀ i ∈ I, (fromEdgeSet (F' : Set (Sym2 V))).Reachable c (x i)
  · -- move the root to `c`
    have hss : F' ⊂ F := Finset.ssubset_iff_subset_ne.2 ⟨hF'F, fun h => hocF' (h ▸ hcF)⟩
    obtain ⟨z, A, hAI, hA, hB, F₀, FA, FB, h0, hA', hB', d1, d2, d3, r0, rA, rB⟩ :=
      ih F' hss c hall
    refine ⟨z, A, hAI, hA, hB, insert s(o, c) F₀, FA, FB,
      Finset.insert_subset hcF (h0.trans hF'F), hA'.trans hF'F, hB'.trans hF'F,
      Finset.disjoint_insert_left.2 ⟨fun h => hocF' (hA' h), d1⟩,
      Finset.disjoint_insert_left.2 ⟨fun h => hocF' (hB' h), d2⟩, d3, ?_, rA, rB⟩
    have hadj : (fromEdgeSet ((insert s(o, c) F₀ : Finset (Sym2 V)) : Set (Sym2 V))).Adj o c :=
      (fromEdgeSet_adj _).2 ⟨by simp, hoc⟩
    exact hadj.reachable.trans (r0.mono (fromEdgeSet_mono (by simp)))
  · -- split at `o` along the component of `c`
    push Not at hall
    obtain ⟨j₀, hj₀, hj₀c⟩ := hall
    set A : Finset ι :=
      I.filter fun i => (fromEdgeSet (F' : Set (Sym2 V))).Reachable c (x i) with hAdef
    set FA : Finset (Sym2 V) := insert s(o, c)
      (F'.filter fun e => ∃ w ∈ e, (fromEdgeSet (F' : Set (Sym2 V))).Reachable c w) with hFA
    have hFAF : FA ⊆ F :=
      Finset.insert_subset hcF ((Finset.filter_subset _ _).trans hF'F)
    refine ⟨o, A, Finset.filter_subset _ _, ⟨i₀, Finset.mem_filter.2 ⟨hi₀, hc₀⟩⟩,
      ⟨j₀, Finset.mem_sdiff.2 ⟨hj₀, fun h => hj₀c (Finset.mem_filter.1 h).2⟩⟩, ∅, FA, F \ FA,
      Finset.empty_subset _, hFAF, Finset.sdiff_subset, Finset.disjoint_empty_left _,
      Finset.disjoint_empty_left _, Finset.disjoint_sdiff, Reachable.rfl, ?_, ?_⟩
    · -- the part through `c`
      intro i hi
      have hci := (Finset.mem_filter.1 hi).2
      have hadj : (fromEdgeSet (FA : Set (Sym2 V))).Adj o c :=
        (fromEdgeSet_adj _).2 ⟨by simp [hFA], hoc⟩
      refine hadj.reachable.trans ?_
      by_cases hxc : x i = c
      · rw [hxc]
      obtain ⟨e, he, hxe⟩ := exists_mem_of_reachable_ne hci.symm hxc
      have h := reachable_filter_reachable F' c
        ⟨e, Finset.mem_filter.2 ⟨Finset.mem_coe.1 he, x i, hxe, hci⟩, hxe⟩
      exact h.mono (fromEdgeSet_mono (by simp [hFA]))
    · -- the rest avoids the component of `c`
      intro j hj
      obtain ⟨hjI, hjA⟩ := Finset.mem_sdiff.1 hj
      have hjc : ¬ (fromEdgeSet (F' : Set (Sym2 V))).Reachable c (x j) :=
        fun h => hjA (Finset.mem_filter.2 ⟨hjI, h⟩)
      obtain ⟨d, hdF, hod, hdj⟩ := exists_nbr_reachable_avoid (ho j hjI) (hox j hjI).symm
      have hcd : ¬ (fromEdgeSet (F' : Set (Sym2 V))).Reachable c d :=
        fun h => hjc (h.trans hdj)
      have hnotFA : ∀ e ∈ F', ∀ w ∈ e,
          (fromEdgeSet (F' : Set (Sym2 V))).Reachable d w → e ∉ FA := by
        intro e he w hwe hdw heFA
        rcases Finset.mem_insert.1 heFA with rfl | heFA
        · exact (Finset.mem_filter.1 he).2 (Sym2.mem_mk_left o c)
        · obtain ⟨-, w', hw'e, hcw'⟩ := Finset.mem_filter.1 heFA
          exact hcd (hcw'.trans ((reachable_fromEdgeSet_of_mem (Finset.mem_coe.2 he)
            hw'e hwe).trans hdw.symm))
      have hodFB : s(o, d) ∈ F \ FA := by
        refine Finset.mem_sdiff.2 ⟨hdF, fun h => ?_⟩
        rcases Finset.mem_insert.1 h with h | h
        · exact hcd (by rw [Sym2.congr_right.1 h])
        · exact (Finset.mem_filter.1 (Finset.mem_of_mem_filter _ h)).2 (Sym2.mem_mk_left o d)
      have hadj : (fromEdgeSet ((F \ FA : Finset (Sym2 V)) : Set (Sym2 V))).Adj o d :=
        (fromEdgeSet_adj _).2 ⟨Finset.mem_coe.2 hodFB, hod⟩
      refine hadj.reachable.trans (reachable_of_closed (F := (F' : Set (Sym2 V))) ?_
        Reachable.rfl Reachable.rfl hdj)
      intro e he w hwe hdw
      exact Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hF'F (Finset.mem_coe.1 he),
        hnotFA e (Finset.mem_coe.1 he) w hwe hdw⟩)

/-! ### Branch points of open configurations -/

/-- The event that `z` is joined to every `x i`, `i ∈ A`, is increasing. -/
theorem isUpperSet_forall_conn (z : V) (x : ι → V) (A : Finset ι) :
    IsUpperSet {ω : Config V | ∀ i ∈ A, ω ∈ conn z (x i)} :=
  fun _ _ h hω i hi => conn_mono h (hω i hi)

/-- **Branch point of an open configuration.** If `o` is joined to every `x i`, `i ∈ I`,
with `|I| ≥ 2` and `i₀ ∈ I`, then for some `z` and some `A ⊆ I` with `i₀ ∈ A` and
`I \ A` nonempty, `{o ↔ z} ∘ ({z ↔ x_A} ∘ {z ↔ x_(I∖A)})` occurs. -/
theorem exists_branch_mem [DecidableEq ι] (x : ι → V) (I : Finset ι) (hI : 1 < I.card) {i₀ : ι}
    (hi₀ : i₀ ∈ I) {o : V} {ω : Config V} (h : ∀ i ∈ I, ω ∈ conn o (x i)) :
    ∃ z : V, ∃ A ⊆ I, i₀ ∈ A ∧ (I \ A).Nonempty ∧
      ω ∈ disjointOccurrence (conn o z)
        (disjointOccurrence {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}
          {η : Config V | ∀ i ∈ I \ A, η ∈ conn z (x i)}) := by
  classical
  -- a finite open edge set carrying all the connections
  have hfin : ∀ i, ∃ G : Finset (Sym2 V), (G : Config V) ⊆ ω ∧
      (i ∈ I → (G : Config V) ∈ conn o (x i)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨G, hG, hGc⟩ := exists_finset_of_mem_conn (h i hi)
      exact ⟨G, hG, fun _ => hGc⟩
    · exact ⟨∅, by simp, fun h => absurd h hi⟩
  choose G hGω hGc using hfin
  set F : Finset (Sym2 V) := I.biUnion G with hF
  have hFω : (F : Config V) ⊆ ω := by
    intro e he
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 he)
    exact hGω i hi
  have hoF : ∀ i ∈ I, (fromEdgeSet (F : Set (Sym2 V))).Reachable o (x i) := fun i hi =>
    conn_mono (Finset.coe_subset.2 (Finset.subset_biUnion_of_mem G hi)) (hGc i hi)
  obtain ⟨z, A, hAI, hA, hB, F₀, FA, FB, h0, hA', hB', d1, d2, d3, r0, rA, rB⟩ :=
    exists_branch_finset x I hI F o hoF
  have hcert : ∀ (A' B' : Finset ι) (GA GB : Finset (Sym2 V)), GA ⊆ F → GB ⊆ F →
      Disjoint F₀ GA → Disjoint F₀ GB → Disjoint GA GB →
      (∀ i ∈ A', (fromEdgeSet (GA : Set (Sym2 V))).Reachable z (x i)) →
      (∀ i ∈ B', (fromEdgeSet (GB : Set (Sym2 V))).Reachable z (x i)) →
      ω ∈ disjointOccurrence (conn o z)
        (disjointOccurrence {η : Config V | ∀ i ∈ A', η ∈ conn z (x i)}
          {η : Config V | ∀ i ∈ B', η ∈ conn z (x i)}) := by
    intro A' B' GA GB hGA hGB e1 e2 e3 rA' rB'
    have hup := isUpperSet_disjointOccurrence (isUpperSet_forall_conn z x A')
      (isUpperSet_forall_conn z x B')
    refine (mem_disjointOccurrence_iff_open (isUpperSet_conn o z) hup ω).2
      ⟨(F₀ : Set (Sym2 V)), ((GA ∪ GB : Finset (Sym2 V)) : Set (Sym2 V)),
        Finset.finite_toSet _, Finset.finite_toSet _, ?_,
        (Finset.coe_subset.2 h0).trans hFω,
        (Finset.coe_subset.2 (Finset.union_subset hGA hGB)).trans hFω, r0, ?_⟩
    · rw [Finset.disjoint_coe]
      exact Finset.disjoint_union_right.2 ⟨e1, e2⟩
    · refine (mem_disjointOccurrence_iff_open (isUpperSet_forall_conn z x A')
        (isUpperSet_forall_conn z x B') _).2
        ⟨(GA : Set (Sym2 V)), (GB : Set (Sym2 V)), Finset.finite_toSet _,
          Finset.finite_toSet _, Finset.disjoint_coe.2 e3, by simp, by simp, rA', rB'⟩
  by_cases hi₀A : i₀ ∈ A
  · exact ⟨z, A, hAI, hi₀A, hB, hcert A (I \ A) FA FB hA' hB' d1 d2 d3 rA rB⟩
  · refine ⟨z, I \ A, Finset.sdiff_subset, Finset.mem_sdiff.2 ⟨hi₀, hi₀A⟩, ?_, ?_⟩
    · rwa [Finset.sdiff_sdiff_eq_self hAI]
    · rw [Finset.sdiff_sdiff_eq_self hAI]
      exact hcert (I \ A) A FB FA hB' hA' d2 d1 d3.symm rB rA

/-! ### The probability bound -/

/-- **Union bound over branch points.** For `|I| ≥ 2` and `i₀ ∈ I`,
`P(o ↔ x_i ∀ i ∈ I) ≤ ∑_z ∑_{A ∋ i₀, A ⊊ I} τ(o, z) P(z ↔ x_A) P(z ↔ x_(I∖A))`. -/
theorem law_forall_conn_le [Countable V] [DecidableEq ι] (q : Sym2 V → unitInterval) (x : ι → V)
    (I : Finset ι) (hI : 1 < I.card) {i₀ : ι} (hi₀ : i₀ ∈ I) (o : V) :
    law q {ω | ∀ i ∈ I, ω ∈ conn o (x i)} ≤
      ∑' z, ∑ A ∈ I.powerset.filter (fun A => i₀ ∈ A ∧ (I \ A).Nonempty),
        tau q o z * (law q {ω | ∀ i ∈ A, ω ∈ conn z (x i)} *
          law q {ω | ∀ i ∈ I \ A, ω ∈ conn z (x i)}) := by
  classical
  have hsub : {ω : Config V | ∀ i ∈ I, ω ∈ conn o (x i)} ⊆
      ⋃ z, ⋃ A ∈ I.powerset.filter (fun A => i₀ ∈ A ∧ (I \ A).Nonempty),
        disjointOccurrence (conn o z)
          (disjointOccurrence {η : Config V | ∀ i ∈ A, η ∈ conn z (x i)}
            {η : Config V | ∀ i ∈ I \ A, η ∈ conn z (x i)}) := by
    intro ω hω
    obtain ⟨z, A, hAI, hiA, hB, hmem⟩ := exists_branch_mem x I hI hi₀ hω
    exact Set.mem_iUnion.2 ⟨z, Set.mem_biUnion
      (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hAI, hiA, hB⟩)) hmem⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum
    fun z => (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun A _ => ?_)))
  refine (countable_profile_bk q (isUpperSet_conn o z) (isUpperSet_disjointOccurrence
    (isUpperSet_forall_conn z x A) (isUpperSet_forall_conn z x _))).trans ?_
  exact mul_le_mul' le_rfl (countable_profile_bk q (isUpperSet_forall_conn z x A)
    (isUpperSet_forall_conn z x _))

/-! ### The tree-graph inequality (L82Q) -/

/-- **The tree-graph inequality** (L82Q): for every countable vertex type and every
profile, `P(x ↔ y, x ↔ z) ≤ ∑_w τ(x, w) τ(w, y) τ(w, z)`. -/
@[tag "L82Q"]
theorem treeGraphInequality (V : Type*) [Countable V] : TreeGraphInequality V := by
  classical
  intro q x y z
  set D : V → Set (Config V) := fun w =>
    disjointOccurrence (conn x w) (disjointOccurrence (conn w y) (conn w z)) with hD
  have hsub : conn x y ∩ conn x z ⊆ ⋃ w, D w := by
    intro ω hω
    have h : ∀ i ∈ (Finset.univ : Finset (Fin 2)), ω ∈ conn x (![y, z] i) := by
      intro i _
      fin_cases i
      · exact hω.1
      · exact hω.2
    obtain ⟨w, A, -, h0A, hB, hmem⟩ :=
      exists_branch_mem ![y, z] Finset.univ (by simp) (Finset.mem_univ 0) h
    have h1A : (1 : Fin 2) ∉ A := by
      intro h1
      obtain ⟨i, hi⟩ := hB
      have hiA := (Finset.mem_sdiff.1 hi).2
      fin_cases i
      · exact hiA h0A
      · exact hiA h1
    refine Set.mem_iUnion.2 ⟨w, disjointOccurrence_mono subset_rfl
      (disjointOccurrence_mono (fun η (hη : ∀ i ∈ A, η ∈ conn w (![y, z] i)) => hη 0 h0A)
        (fun η (hη : ∀ i ∈ Finset.univ \ A, η ∈ conn w (![y, z] i)) => hη 1 ?_)) hmem⟩
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h1A⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum
    fun w => ?_))
  refine (countable_profile_bk q (isUpperSet_conn x w) (isUpperSet_disjointOccurrence
    (isUpperSet_conn w y) (isUpperSet_conn w z))).trans ?_
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (countable_profile_bk q (isUpperSet_conn w y)
    (isUpperSet_conn w z))

/-! ### Non-vacuity -/

example : TreeGraphInequality Bool := treeGraphInequality Bool

example : TreeGraphInequality ℤ := treeGraphInequality ℤ

/-- Three points on `Fin 3`, joined at a branch point. -/
example (q : Sym2 (Fin 3) → unitInterval) :
    law q {ω | ∀ i ∈ (Finset.univ : Finset (Fin 3)), ω ∈ conn 0 ((![0, 1, 2] : Fin 3 → Fin 3) i)} ≤
      ∑' z, ∑ A ∈ (Finset.univ : Finset (Fin 3)).powerset.filter
          (fun A => 0 ∈ A ∧ (Finset.univ \ A).Nonempty),
        tau q 0 z * (law q {ω | ∀ i ∈ A, ω ∈ conn z ((![0, 1, 2] : Fin 3 → Fin 3) i)} *
          law q {ω | ∀ i ∈ Finset.univ \ A, ω ∈ conn z ((![0, 1, 2] : Fin 3 → Fin 3) i)}) :=
  law_forall_conn_le q _ _ (by simp) (Finset.mem_univ 0) 0

end PercLib.Percolation.Bond
