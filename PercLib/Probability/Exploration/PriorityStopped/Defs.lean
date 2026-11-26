/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Priority exploration of a bond cluster, stopped at a cluster-size threshold. New for this
project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is
copied. The least eligible edge is mathlib's `Function.argminOn`. Mathematical reference: the
standard edge-by-edge exploration of a percolation cluster, e.g. Grimmett, *Percolation*,
2nd ed., Springer, 1999.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Basic
public import Mathlib.Order.WellFounded

/-!
# Priority exploration stopped at a cluster-size threshold

A countable graph `G : SimpleGraph V` with an injection `ι : G.edgeSet ↪ ℕ` ordering its edges,
a root `o` and a threshold `n`. The exploration starts with discovered set `{o}` and no queried
edges. While the discovered set does not have size `n` and some unqueried edge of `G` has an
endpoint in it, it queries the eligible edge of least `ι`-value in the configuration `ω`; an
open answer adds both endpoints to the discovered set. Once it halts, its state no longer
changes and every later step records the cemetery value `none`.

## Main definitions

* `PriorityExploration.State G`: discovered vertices and queried edges.
* `PriorityExploration.State.eligible`: unqueried edges with a discovered endpoint.
* `PriorityExploration.State.nextQuery ι n s`: the next queried edge, or `none` on halting.
* `PriorityExploration.State.step ι n ω s`: one step of the exploration.
* `priorityExploration G ι o n ω t`: the state after `t` steps.
* `priorityQuery G ι o n ω t`, `priorityAnswer G ι o n ω t`: the edge queried and the answer
  recorded at step `t` (`none` is the cemetery symbol).
-/

@[expose] public section

noncomputable section

open Set

namespace PercLib.Percolation.Bond

variable {V : Type*} {G : SimpleGraph V}

namespace PriorityExploration

/-- A state of the priority exploration: the discovered vertices and the queried edges. -/
@[ext]
structure State (G : SimpleGraph V) where
  /-- The discovered vertices. -/
  discovered : Set V
  /-- The edges queried so far. -/
  queried : Set G.edgeSet

namespace State

/-- The initial state: discovered set `{o}` and no queried edges. -/
def init (G : SimpleGraph V) (o : V) : State G := ⟨{o}, ∅⟩

/-- The eligible edges: unqueried edges of `G` with an endpoint in the discovered set. -/
def eligible (s : State G) : Set G.edgeSet :=
  {e | e ∉ s.queried ∧ ∃ v ∈ (e : Sym2 V), v ∈ s.discovered}

open Classical in
/-- The next query: `none` (halt) if the discovered set has size `n` or no edge is eligible,
and otherwise the eligible edge of least `ι`-value. -/
def nextQuery (ι : G.edgeSet ↪ ℕ) (n : ℕ) (s : State G) : Option G.edgeSet :=
  if h : s.discovered.encard ≠ n ∧ s.eligible.Nonempty then
    some (Function.argminOn ι s.eligible h.2)
  else none

open Classical in
/-- One step: a halted state is fixed; otherwise the next edge is queried, and an open answer
adds both its endpoints to the discovered set. -/
def step (ι : G.edgeSet ↪ ℕ) (n : ℕ) (ω : Config V) (s : State G) : State G :=
  match s.nextQuery ι n with
  | none => s
  | some e =>
    ⟨if (e : Sym2 V) ∈ ω then s.discovered ∪ {v | v ∈ (e : Sym2 V)} else s.discovered,
      insert e s.queried⟩

@[simp] theorem init_discovered (o : V) : (init G o).discovered = {o} := rfl

@[simp] theorem init_queried (o : V) : (init G o).queried = ∅ := rfl

theorem mem_eligible_iff (s : State G) (e : G.edgeSet) :
    e ∈ s.eligible ↔ e ∉ s.queried ∧ ∃ v ∈ (e : Sym2 V), v ∈ s.discovered := Iff.rfl

theorem nextQuery_eq_none_iff (ι : G.edgeSet ↪ ℕ) (n : ℕ) (s : State G) :
    s.nextQuery ι n = none ↔ s.discovered.encard = n ∨ s.eligible = ∅ := by
  unfold nextQuery
  split_ifs with h
  · simp only [false_iff, not_or]
    exact ⟨h.1, h.2.ne_empty⟩
  · simp only [true_iff]
    by_contra h'
    simp only [not_or] at h'
    exact h ⟨h'.1, Set.nonempty_iff_ne_empty.2 h'.2⟩

theorem nextQuery_eq_some_iff (ι : G.edgeSet ↪ ℕ) (n : ℕ) (s : State G) (e : G.edgeSet) :
    s.nextQuery ι n = some e ↔
      s.discovered.encard ≠ n ∧ e ∈ s.eligible ∧ ∀ f ∈ s.eligible, ι e ≤ ι f := by
  unfold nextQuery
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h.1, Function.argminOn_mem _ _ _, fun f hf => Function.argminOn_le _ _ hf⟩
    · rintro ⟨-, he, hmin⟩
      apply ι.injective
      exact le_antisymm (Function.argminOn_le _ _ he)
        (hmin _ (Function.argminOn_mem _ _ _))
  · simp only [false_iff]
    rintro ⟨h1, he, -⟩
    exact h ⟨h1, e, he⟩

theorem step_of_nextQuery_eq_none {ι : G.edgeSet ↪ ℕ} {n : ℕ} {s : State G}
    (h : s.nextQuery ι n = none) (ω : Config V) : s.step ι n ω = s := by
  simp [step, h]

open Classical in
theorem step_of_nextQuery_eq_some {ι : G.edgeSet ↪ ℕ} {n : ℕ} {s : State G} {e : G.edgeSet}
    (h : s.nextQuery ι n = some e) (ω : Config V) :
    s.step ι n ω =
      ⟨if (e : Sym2 V) ∈ ω then s.discovered ∪ {v | v ∈ (e : Sym2 V)} else s.discovered,
        insert e s.queried⟩ := by
  simp [step, h]

end State

end PriorityExploration

open PriorityExploration

/-- The priority exploration of the cluster of `o` in the open subgraph of `G`, with edge order
`ι` and halted when `n` vertices are discovered: its state after `t` steps. -/
@[tag "28UY"]
def priorityExploration (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ)
    (ω : Config V) (t : ℕ) : State G :=
  (State.step ι n ω)^[t] (State.init G o)

/-- The edge queried at step `t`, or `none` once the exploration has halted. -/
def priorityQuery (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ)
    (ω : Config V) (t : ℕ) : Option G.edgeSet :=
  (priorityExploration G ι o n ω t).nextQuery ι n

open Classical in
/-- The answer recorded at step `t`: `some true` (open), `some false` (closed), or the
cemetery value `none` once the exploration has halted. -/
def priorityAnswer (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ)
    (ω : Config V) (t : ℕ) : Option Bool :=
  (priorityQuery G ι o n ω t).map fun e => decide ((e : Sym2 V) ∈ ω)

variable (G) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ) (ω : Config V)

@[simp] theorem priorityExploration_zero :
    priorityExploration G ι o n ω 0 = State.init G o := rfl

theorem priorityExploration_succ (t : ℕ) :
    priorityExploration G ι o n ω (t + 1) =
      (priorityExploration G ι o n ω t).step ι n ω :=
  Function.iterate_succ_apply' _ _ _

theorem priorityQuery_def (t : ℕ) :
    priorityQuery G ι o n ω t = (priorityExploration G ι o n ω t).nextQuery ι n := rfl

theorem priorityAnswer_eq_none_iff (t : ℕ) :
    priorityAnswer G ι o n ω t = none ↔ priorityQuery G ι o n ω t = none := by
  simp [priorityAnswer]

theorem priorityAnswer_eq_some_iff (t : ℕ) (b : Bool) :
    priorityAnswer G ι o n ω t = some b ↔
      ∃ e, priorityQuery G ι o n ω t = some e ∧ ((e : Sym2 V) ∈ ω ↔ b = true) := by
  unfold priorityAnswer
  rcases priorityQuery G ι o n ω t with _ | e
  · simp
  · cases b <;> simp

end PercLib.Percolation.Bond
