/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Basic properties of the priority exploration stopped at a cluster-size threshold. New for
this project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream
code is copied. Mathematical reference: the standard edge-by-edge exploration of a
percolation cluster, e.g. Grimmett, *Percolation*, 2nd ed., Springer, 1999.
-/
module

public import PercLib.Probability.Exploration.PriorityStopped.Defs
public import PercLib.Percolation.Bond.FiniteVolume

/-!
# Priority exploration: basic properties

Properties of `priorityExploration G ι o n ω` that hold for every configuration `ω`, with no
finiteness of degrees, geometry or transitivity assumed.

## Main results

* `priorityExploration_discovered_mono`: the discovered sets increase.
* `priorityExploration_discovered_subset_cluster`: `D_t ⊆ K_o`, the open cluster of `o` in `G`.
* `encard_priorityExploration_discovered_le`: `|D_t| ≤ n` for `n ≥ 1`.
* `encard_priorityExploration_discovered_succ_le`: each query adds at most one vertex.
* `priorityQuery_eq_none_iff`, `priorityExploration_eq_of_priorityQuery_eq_none`: the halting
  rule, and a halted exploration stays halted.
* `priorityQuery_injective`: no edge is queried twice.
* `priorityExploration_eq_of_priorityAnswer_eq`: the state, hence the next query and the
  stopping decision, depends only on the preceding answers.
* `exists_priorityQuery_eq_some_of_mem_eligible`: fairness; on a run that never halts, every
  eligible edge is eventually queried.
* `encard_iUnion_priorityExploration_discovered`: `|D_∞| = min (|K_o|, n)`.
* `setOf_le_encard_cluster_eq`: `{|K_o| ≥ n}` is the event that `n` vertices are discovered at
  a finite time.
* `exists_setOf_le_encard_cluster_eq_iUnion_cylinder`: that event is a countable union of
  cylinders on finite prefixes of the answer transcript.
-/

@[expose] public section

noncomputable section

open Set

namespace PercLib.Percolation.Bond

variable {V : Type*} {G : SimpleGraph V} {ι : G.edgeSet ↪ ℕ} {n : ℕ} {ω : Config V}

namespace PriorityExploration.State

theorem discovered_subset_step (s : State G) :
    s.discovered ⊆ (s.step ι n ω).discovered := by
  rcases h : s.nextQuery ι n with _ | e
  · rw [step_of_nextQuery_eq_none h]
  · rw [step_of_nextQuery_eq_some h]
    split_ifs
    · exact subset_union_left
    · exact subset_rfl

theorem queried_subset_step (s : State G) : s.queried ⊆ (s.step ι n ω).queried := by
  rcases h : s.nextQuery ι n with _ | e
  · rw [step_of_nextQuery_eq_none h]
  · rw [step_of_nextQuery_eq_some h]
    exact subset_insert _ _

theorem mem_queried_step_of_nextQuery_eq_some {s : State G} {e : G.edgeSet}
    (h : s.nextQuery ι n = some e) : e ∈ (s.step ι n ω).queried := by
  rw [step_of_nextQuery_eq_some h]
  exact mem_insert _ _

theorem mem_eligible_of_nextQuery_eq_some {s : State G} {e : G.edgeSet}
    (h : s.nextQuery ι n = some e) : e ∈ s.eligible :=
  ((nextQuery_eq_some_iff ι n s e).1 h).2.1

/-- A query with a discovered endpoint adds at most its other endpoint. -/
theorem encard_step_discovered_le (s : State G) :
    (s.step ι n ω).discovered.encard ≤ s.discovered.encard + 1 := by
  rcases h : s.nextQuery ι n with _ | e
  · rw [step_of_nextQuery_eq_none h]
    exact le_self_add
  · obtain ⟨-, v, hv, hvD⟩ := mem_eligible_of_nextQuery_eq_some h
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hv
    refine le_trans (encard_le_encard ?_) (encard_insert_le s.discovered w)
    rw [step_of_nextQuery_eq_some h]
    split_ifs
    · rintro x (hx | hx)
      · exact mem_insert_of_mem _ hx
      · rw [mem_ofPred_eq, hw, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact mem_insert_of_mem _ hvD
        · exact mem_insert _ _
    · exact subset_insert _ _

/-- Every vertex discovered by an open answer is joined to an already discovered vertex by
an open edge of `G`. -/
theorem step_discovered_subset_cluster {s : State G} {o : V}
    (hs : s.discovered ⊆ cluster (ω ∩ G.edgeSet) o) :
    (s.step ι n ω).discovered ⊆ cluster (ω ∩ G.edgeSet) o := by
  rcases h : s.nextQuery ι n with _ | e
  · rwa [step_of_nextQuery_eq_none h]
  · obtain ⟨-, v, hv, hvD⟩ := mem_eligible_of_nextQuery_eq_some h
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.1 hv
    rw [step_of_nextQuery_eq_some h]
    split_ifs with hω
    · rintro x (hx | hx)
      · exact hs hx
      · rw [mem_ofPred_eq, hw, Sym2.mem_iff] at hx
        have hG : G.Adj v w := by
          have := e.2
          rwa [hw, SimpleGraph.mem_edgeSet] at this
        have hadj : (openGraph (ω ∩ G.edgeSet)).Adj v w := by
          rw [openGraph_adj_iff]
          refine ⟨⟨hw ▸ hω, ?_⟩, hG.ne⟩
          rw [SimpleGraph.mem_edgeSet]
          exact hG
        rcases hx with rfl | rfl
        · exact hs hvD
        · exact (hs hvD).trans hadj.reachable
    · exact hs

theorem mem_eligible_step {s : State G} {e : G.edgeSet} (he : e ∈ s.eligible)
    (hq : s.nextQuery ι n ≠ some e) : e ∈ (s.step ι n ω).eligible := by
  rcases h : s.nextQuery ι n with _ | f
  · rwa [step_of_nextQuery_eq_none h]
  · have hfe : e ≠ f := fun hef => hq (hef ▸ h)
    obtain ⟨heQ, v, hv, hvD⟩ := he
    refine ⟨?_, v, hv, discovered_subset_step s hvD⟩
    rw [step_of_nextQuery_eq_some h]
    rintro (h' | h')
    · exact hfe h'
    · exact heQ h'

/-- Open queried edges have both endpoints discovered. -/
theorem step_open_queried_subset {s : State G}
    (hs : ∀ e ∈ s.queried, (e : Sym2 V) ∈ ω → ∀ v ∈ (e : Sym2 V), v ∈ s.discovered) :
    ∀ e ∈ (s.step ι n ω).queried, (e : Sym2 V) ∈ ω →
      ∀ v ∈ (e : Sym2 V), v ∈ (s.step ι n ω).discovered := by
  rcases h : s.nextQuery ι n with _ | f
  · rwa [step_of_nextQuery_eq_none h]
  · rw [step_of_nextQuery_eq_some h]
    rintro e (rfl | he) heω v hv
    · simp only [heω, ↓reduceIte]
      exact Or.inr hv
    · split_ifs
      · exact Or.inl (hs e he heω v hv)
      · exact hs e he heω v hv

end PriorityExploration.State

open PriorityExploration

variable {o : V}

theorem priorityExploration_discovered_mono :
    Monotone fun t => (priorityExploration G ι o n ω t).discovered :=
  monotone_nat_of_le_succ fun t => by
    simp only [priorityExploration_succ]
    exact State.discovered_subset_step _

theorem priorityExploration_queried_mono :
    Monotone fun t => (priorityExploration G ι o n ω t).queried :=
  monotone_nat_of_le_succ fun t => by
    simp only [priorityExploration_succ]
    exact State.queried_subset_step _

/-- `D_t ⊆ K_o`: every discovered vertex is joined to `o` by open edges of `G`. -/
theorem priorityExploration_discovered_subset_cluster (t : ℕ) :
    (priorityExploration G ι o n ω t).discovered ⊆ cluster (ω ∩ G.edgeSet) o := by
  induction t with
  | zero =>
    simp only [priorityExploration_zero, State.init_discovered, singleton_subset_iff]
    exact mem_cluster_self _ _
  | succ t ih =>
    rw [priorityExploration_succ]
    exact State.step_discovered_subset_cluster ih

/-- Each query adds at most one vertex. -/
theorem encard_priorityExploration_discovered_succ_le (t : ℕ) :
    (priorityExploration G ι o n ω (t + 1)).discovered.encard ≤
      (priorityExploration G ι o n ω t).discovered.encard + 1 := by
  rw [priorityExploration_succ]
  exact State.encard_step_discovered_le _

theorem encard_priorityExploration_discovered_le_add_one (t : ℕ) :
    (priorityExploration G ι o n ω t).discovered.encard ≤ ((t + 1 : ℕ) : ℕ∞) := by
  induction t with
  | zero => simp
  | succ t ih =>
    refine (encard_priorityExploration_discovered_succ_le t).trans ?_
    push_cast at ih ⊢
    gcongr

theorem priorityExploration_discovered_finite (t : ℕ) :
    (priorityExploration G ι o n ω t).discovered.Finite :=
  finite_of_encard_le_coe (encard_priorityExploration_discovered_le_add_one t)

/-- The halting rule: the exploration halts exactly when the discovered set has size `n` or
no unqueried edge of `G` meets it. -/
theorem priorityQuery_eq_none_iff (t : ℕ) :
    priorityQuery G ι o n ω t = none ↔
      (priorityExploration G ι o n ω t).discovered.encard = n ∨
        (priorityExploration G ι o n ω t).eligible = ∅ :=
  State.nextQuery_eq_none_iff ι n _

/-- The query rule: the queried edge is the eligible edge of least `ι`-value. -/
theorem priorityQuery_eq_some_iff (t : ℕ) (e : G.edgeSet) :
    priorityQuery G ι o n ω t = some e ↔
      (priorityExploration G ι o n ω t).discovered.encard ≠ n ∧
        e ∈ (priorityExploration G ι o n ω t).eligible ∧
          ∀ f ∈ (priorityExploration G ι o n ω t).eligible, ι e ≤ ι f :=
  State.nextQuery_eq_some_iff ι n _ e

theorem priorityExploration_succ_of_priorityQuery_eq_none {t : ℕ}
    (h : priorityQuery G ι o n ω t = none) :
    priorityExploration G ι o n ω (t + 1) = priorityExploration G ι o n ω t := by
  rw [priorityExploration_succ]
  exact State.step_of_nextQuery_eq_none h ω

/-- A halted exploration stays halted, with a constant state. -/
theorem priorityExploration_eq_of_priorityQuery_eq_none {t u : ℕ}
    (h : priorityQuery G ι o n ω t = none) (htu : t ≤ u) :
    priorityExploration G ι o n ω u = priorityExploration G ι o n ω t := by
  induction u, htu using Nat.le_induction with
  | base => rfl
  | succ u _ ih =>
    rw [priorityExploration_succ, ih]
    exact State.step_of_nextQuery_eq_none h ω

theorem priorityQuery_eq_none_of_le {t u : ℕ} (h : priorityQuery G ι o n ω t = none)
    (htu : t ≤ u) : priorityQuery G ι o n ω u = none := by
  rw [priorityQuery_def, priorityExploration_eq_of_priorityQuery_eq_none h htu]
  exact h

/-- `|D_t| ≤ n` for a threshold `n ≥ 1`. -/
theorem encard_priorityExploration_discovered_le (hn : 1 ≤ n) (t : ℕ) :
    (priorityExploration G ι o n ω t).discovered.encard ≤ n := by
  induction t with
  | zero => simpa using hn
  | succ t ih =>
    by_cases hD : (priorityExploration G ι o n ω t).discovered.encard = n
    · rwa [priorityExploration_succ_of_priorityQuery_eq_none
        ((priorityQuery_eq_none_iff t).2 (Or.inl hD))]
    · exact (encard_priorityExploration_discovered_succ_le t).trans
        (Order.add_one_le_of_lt (lt_of_le_of_ne ih hD))

theorem priorityQuery_mem_eligible {t : ℕ} {e : G.edgeSet}
    (h : priorityQuery G ι o n ω t = some e) :
    e ∈ (priorityExploration G ι o n ω t).eligible :=
  State.mem_eligible_of_nextQuery_eq_some h

theorem mem_priorityExploration_queried_of_lt {s t : ℕ} {e : G.edgeSet}
    (h : priorityQuery G ι o n ω s = some e) (hst : s < t) :
    e ∈ (priorityExploration G ι o n ω t).queried := by
  refine priorityExploration_queried_mono hst ?_
  simp only [priorityExploration_succ]
  exact State.mem_queried_step_of_nextQuery_eq_some h

/-- No edge is queried twice. -/
theorem priorityQuery_injective {s t : ℕ} {e : G.edgeSet}
    (hs : priorityQuery G ι o n ω s = some e) (ht : priorityQuery G ι o n ω t = some e) :
    s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (priorityQuery_mem_eligible ht).1 (mem_priorityExploration_queried_of_lt hs hst)
  · exact (priorityQuery_mem_eligible hs).1 (mem_priorityExploration_queried_of_lt ht hts)

/-- The state after `t` steps, hence the next query and the stopping decision, depends only
on the answers recorded before time `t`. -/
theorem priorityExploration_eq_of_priorityAnswer_eq {ω' : Config V} {t : ℕ}
    (h : ∀ s < t, priorityAnswer G ι o n ω s = priorityAnswer G ι o n ω' s) :
    priorityExploration G ι o n ω t = priorityExploration G ι o n ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hS := ih fun s hs => h s (by omega)
    have ht := h t (by omega)
    simp only [priorityAnswer, priorityQuery, hS] at ht
    rw [priorityExploration_succ, priorityExploration_succ, hS]
    rcases hq : (priorityExploration G ι o n ω' t).nextQuery ι n with _ | e
    · rw [State.step_of_nextQuery_eq_none hq, State.step_of_nextQuery_eq_none hq]
    · rw [hq] at ht
      have ht' : (e : Sym2 V) ∈ ω ↔ (e : Sym2 V) ∈ ω' := by simpa using ht
      rw [State.step_of_nextQuery_eq_some hq, State.step_of_nextQuery_eq_some hq]
      congr 1
      classical
      exact if_congr ht' rfl rfl

theorem priorityQuery_eq_of_priorityAnswer_eq {ω' : Config V} {t : ℕ}
    (h : ∀ s < t, priorityAnswer G ι o n ω s = priorityAnswer G ι o n ω' s) :
    priorityQuery G ι o n ω t = priorityQuery G ι o n ω' t := by
  rw [priorityQuery_def, priorityQuery_def, priorityExploration_eq_of_priorityAnswer_eq h]

/-- An eligible edge stays eligible until it is queried. -/
theorem mem_priorityExploration_succ_eligible {t : ℕ} {e : G.edgeSet}
    (he : e ∈ (priorityExploration G ι o n ω t).eligible)
    (hq : priorityQuery G ι o n ω t ≠ some e) :
    e ∈ (priorityExploration G ι o n ω (t + 1)).eligible := by
  rw [priorityExploration_succ]
  exact State.mem_eligible_step he hq

/-- Fairness: on a run that never halts, every eligible edge is eventually queried. Only
finitely many edges have smaller priority, and none is queried twice. -/
theorem exists_priorityQuery_eq_some_of_mem_eligible {t : ℕ} {e : G.edgeSet}
    (he : e ∈ (priorityExploration G ι o n ω t).eligible)
    (hrun : ∀ u, priorityQuery G ι o n ω u ≠ none) :
    ∃ u, t ≤ u ∧ priorityQuery G ι o n ω u = some e := by
  by_contra hne
  push Not at hne
  have helig : ∀ k, e ∈ (priorityExploration G ι o n ω (t + k)).eligible := by
    intro k
    induction k with
    | zero => simpa using he
    | succ k ih =>
      rw [← add_assoc]
      exact mem_priorityExploration_succ_eligible ih (hne _ (by omega))
  have hf : ∀ k, ∃ f, priorityQuery G ι o n ω (t + k) = some f :=
    fun k => Option.ne_none_iff_exists'.1 (hrun _)
  choose f hf using hf
  have hlt : ∀ k, ι (f k) < ι e := by
    intro k
    have hle := ((priorityQuery_eq_some_iff _ _).1 (hf k)).2.2 e (helig k)
    refine lt_of_le_of_ne hle fun h' => hne (t + k) (by omega) ?_
    rw [hf k, ι.injective h']
  let g : ℕ → Fin (ι e) := fun k => ⟨ι (f k), hlt k⟩
  refine not_injective_infinite_finite g fun k k' hkk' => ?_
  have hff : f k = f k' := ι.injective (Fin.mk.inj_iff.1 hkk')
  have := priorityQuery_injective (hf k) (hff ▸ hf k')
  omega

/-- Open queried edges have both endpoints discovered. -/
theorem mem_priorityExploration_discovered_of_mem_queried {t : ℕ} {e : G.edgeSet}
    (he : e ∈ (priorityExploration G ι o n ω t).queried) (heω : (e : Sym2 V) ∈ ω) {v : V}
    (hv : v ∈ (e : Sym2 V)) : v ∈ (priorityExploration G ι o n ω t).discovered := by
  induction t generalizing e v with
  | zero => simp at he
  | succ t ih =>
    rw [priorityExploration_succ] at he ⊢
    exact State.step_open_queried_subset (fun f hf hfω w hw => ih hf hfω hw) e he heω v hv

theorem iUnion_priorityExploration_discovered_subset_cluster :
    (⋃ t, (priorityExploration G ι o n ω t).discovered) ⊆ cluster (ω ∩ G.edgeSet) o :=
  iUnion_subset priorityExploration_discovered_subset_cluster

/-- If the threshold is never reached, the union of the discovered sets is closed under open
edges of `G`: by the halting rule if the exploration halts, and by fairness otherwise. -/
theorem exists_mem_priorityExploration_discovered_of_adj
    (hthr : ∀ t, (priorityExploration G ι o n ω t).discovered.encard ≠ n) {t : ℕ} {v w : V}
    (hv : v ∈ (priorityExploration G ι o n ω t).discovered)
    (hadj : (openGraph (ω ∩ G.edgeSet)).Adj v w) :
    ∃ u, w ∈ (priorityExploration G ι o n ω u).discovered := by
  rw [openGraph_adj_iff] at hadj
  obtain ⟨⟨hω, hG⟩, -⟩ := hadj
  let e : G.edgeSet := ⟨s(v, w), hG⟩
  have hw : w ∈ (e : Sym2 V) := Sym2.mem_mk_right v w
  have hve : v ∈ (e : Sym2 V) := Sym2.mem_mk_left v w
  -- At any time `T ≥ t`, the edge `e` is queried or eligible.
  have hQE : ∀ T, t ≤ T → e ∈ (priorityExploration G ι o n ω T).queried ∨
      e ∈ (priorityExploration G ι o n ω T).eligible := by
    intro T hT
    by_cases hQ : e ∈ (priorityExploration G ι o n ω T).queried
    · exact Or.inl hQ
    · exact Or.inr ⟨hQ, v, hve, priorityExploration_discovered_mono hT hv⟩
  by_cases hhalt : ∃ u, priorityQuery G ι o n ω u = none
  · obtain ⟨u, hu⟩ := hhalt
    have hT : priorityQuery G ι o n ω (max t u) = none :=
      priorityQuery_eq_none_of_le hu (le_max_right t u)
    rw [priorityQuery_eq_none_iff] at hT
    have hempty := hT.resolve_left (hthr _)
    rcases hQE (max t u) (le_max_left t u) with hQ | hE
    · exact ⟨_, mem_priorityExploration_discovered_of_mem_queried hQ hω hw⟩
    · rw [hempty] at hE
      exact hE.elim
  · push Not at hhalt
    rcases hQE t le_rfl with hQ | hE
    · exact ⟨t, mem_priorityExploration_discovered_of_mem_queried hQ hω hw⟩
    · obtain ⟨u, -, hu⟩ := exists_priorityQuery_eq_some_of_mem_eligible hE hhalt
      refine ⟨u + 1, mem_priorityExploration_discovered_of_mem_queried ?_ hω hw⟩
      exact mem_priorityExploration_queried_of_lt hu (Nat.lt_succ_self u)

/-- If the threshold is never reached, the exploration discovers the whole root cluster. -/
theorem iUnion_priorityExploration_discovered_eq_cluster
    (hthr : ∀ t, (priorityExploration G ι o n ω t).discovered.encard ≠ n) :
    (⋃ t, (priorityExploration G ι o n ω t).discovered) = cluster (ω ∩ G.edgeSet) o := by
  refine subset_antisymm iUnion_priorityExploration_discovered_subset_cluster ?_
  rintro y ⟨p⟩
  suffices h : ∀ {a b : V} (q : (openGraph (ω ∩ G.edgeSet)).Walk a b),
      a ∈ ⋃ t, (priorityExploration G ι o n ω t).discovered →
        b ∈ ⋃ t, (priorityExploration G ι o n ω t).discovered from
    h p (mem_iUnion.2 ⟨0, by simp⟩)
  intro a b q
  induction q with
  | nil => exact id
  | cons hadj _ ih =>
    intro ha
    obtain ⟨t, ht⟩ := mem_iUnion.1 ha
    exact ih (mem_iUnion.2 (exists_mem_priorityExploration_discovered_of_adj hthr ht hadj))

theorem encard_iUnion_priorityExploration_discovered_eq_iSup :
    (⋃ t, (priorityExploration G ι o n ω t).discovered).encard =
      ⨆ t, (priorityExploration G ι o n ω t).discovered.encard :=
  encard_iUnion_of_monotone priorityExploration_discovered_mono

/-- An increasing union of sets of size less than `n` has size less than `n`. -/
theorem encard_iUnion_priorityExploration_discovered_lt (hn : 1 ≤ n)
    (hthr : ∀ t, (priorityExploration G ι o n ω t).discovered.encard ≠ n) :
    (⋃ t, (priorityExploration G ι o n ω t).discovered).encard < n := by
  rw [encard_iUnion_priorityExploration_discovered_eq_iSup]
  have hle : ∀ t, (priorityExploration G ι o n ω t).discovered.encard ≤ ((n - 1 : ℕ) : ℕ∞) := by
    intro t
    have hlt := lt_of_le_of_ne (encard_priorityExploration_discovered_le hn t) (hthr t)
    have h1 := Order.add_one_le_of_lt hlt
    have : ((n - 1 : ℕ) : ℕ∞) + 1 = n := by
      rw [← ENat.natCast_one, ← ENat.natCast_add, Nat.sub_add_cancel hn]
    rw [← this] at h1
    exact (WithTop.add_le_add_iff_right ENat.one_ne_top).1 h1
  refine lt_of_le_of_lt (iSup_le hle) ?_
  exact_mod_cast Nat.sub_lt hn Nat.one_pos

/-- `|D_∞| = min (|K_o|, n)`. -/
theorem encard_iUnion_priorityExploration_discovered (hn : 1 ≤ n) :
    (⋃ t, (priorityExploration G ι o n ω t).discovered).encard =
      min (cluster (ω ∩ G.edgeSet) o).encard n := by
  by_cases hreach : ∃ t, (priorityExploration G ι o n ω t).discovered.encard = n
  · obtain ⟨t, ht⟩ := hreach
    have hK : (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard :=
      ht ▸ encard_le_encard (priorityExploration_discovered_subset_cluster t)
    rw [min_eq_right hK]
    refine le_antisymm ?_ (ht ▸ encard_le_encard
      (subset_iUnion (fun t => (priorityExploration G ι o n ω t).discovered) t))
    rw [encard_iUnion_priorityExploration_discovered_eq_iSup]
    exact iSup_le (encard_priorityExploration_discovered_le hn)
  · push Not at hreach
    have hlt := encard_iUnion_priorityExploration_discovered_lt hn hreach
    rw [iUnion_priorityExploration_discovered_eq_cluster hreach] at hlt ⊢
    exact (min_eq_left hlt.le).symm

/-- `{|K_o| ≥ n}` is the event that the exploration discovers `n` vertices at a finite time. -/
theorem setOf_le_encard_cluster_eq (hn : 1 ≤ n) :
    {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} =
      {ω | ∃ t, (priorityExploration G ι o n ω t).discovered.encard = n} := by
  ext ω
  simp only [mem_ofPred_eq]
  constructor
  · intro hK
    by_contra hreach
    push Not at hreach
    have hlt := encard_iUnion_priorityExploration_discovered_lt hn hreach
    rw [iUnion_priorityExploration_discovered_eq_cluster hreach] at hlt
    exact absurd hK (not_le.2 hlt)
  · rintro ⟨t, ht⟩
    exact ht ▸ encard_le_encard (priorityExploration_discovered_subset_cluster t)

/-- The cluster-tail event is a countable union of cylinders on finite prefixes of the
answer transcript, so a single output rule on the full transcript decides it for every
configuration, even when the exploration never halts. -/
theorem exists_setOf_le_encard_cluster_eq_iUnion_cylinder (hn : 1 ≤ n) :
    ∃ T : (t : ℕ) → Set (Fin t → Option Bool),
      {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} =
        ⋃ t, {ω | (fun s : Fin t => priorityAnswer G ι o n ω s) ∈ T t} := by
  refine ⟨fun t => {a | ∃ ω' : Config V, (fun s : Fin t => priorityAnswer G ι o n ω' s) = a ∧
    (priorityExploration G ι o n ω' t).discovered.encard = n}, ?_⟩
  rw [setOf_le_encard_cluster_eq (ι := ι) hn]
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, ω, rfl, ht⟩
  · rintro ⟨t, ω', hω', ht⟩
    refine ⟨t, ?_⟩
    rw [← ht]
    refine (priorityExploration_eq_of_priorityAnswer_eq fun s hs => ?_) ▸ rfl
    exact congrFun hω' ⟨s, hs⟩

end PercLib.Percolation.Bond
