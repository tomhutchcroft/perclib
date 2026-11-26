/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.Exploration.PriorityStopped

/-!
# Correspondence wrappers for the stopped priority exploration

Tagged restatements for the priority exploration `priorityExploration G ι o n ω` of the
cluster of `o` in the open subgraph of `G`, halted when `n` vertices are discovered. The
exploration itself is defined in `PercLib.Probability.Exploration.PriorityStopped.Defs`, and
every conjunct below is proved under its own name in
`PercLib.Probability.Exploration.PriorityStopped`.

## Main results

* `encard_iUnion_priorityExploration_discovered_and_setOf_le_encard_cluster_eq`: for every
  configuration `|D_∞| = min (|K_o|, n)`; the event `{|K_o| ≥ n}` is the event that `n`
  vertices are discovered at a finite time; and that event is a countable union of cylinders
  on finite prefixes of the answer transcript.
-/

@[expose] public section

noncomputable section

open Set

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- For a threshold `n ≥ 1` and every configuration, the union `D_∞` of the discovered sets
has size `min (|K_o|, n)`; the event `{|K_o| ≥ n}` is the event that the exploration
discovers `n` vertices at a finite time; and this event is a countable union of cylinders on
finite prefixes of the answer transcript in `{0, 1, †}^ℕ`. -/
@[tag "PWBU"]
theorem encard_iUnion_priorityExploration_discovered_and_setOf_le_encard_cluster_eq
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) {n : ℕ} (hn : 1 ≤ n) :
    (∀ ω : Config V, (⋃ t, (priorityExploration G ι o n ω t).discovered).encard =
      min (cluster (ω ∩ G.edgeSet) o).encard n) ∧
    {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} =
      {ω | ∃ t, (priorityExploration G ι o n ω t).discovered.encard = n} ∧
    ∃ T : (t : ℕ) → Set (Fin t → Option Bool),
      {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} =
        ⋃ t, {ω | (fun s : Fin t => priorityAnswer G ι o n ω s) ∈ T t} :=
  ⟨fun _ => encard_iUnion_priorityExploration_discovered hn, setOf_le_encard_cluster_eq hn,
    exists_setOf_le_encard_cluster_eq_iUnion_cylinder hn⟩

end PercLib.Percolation.Bond
