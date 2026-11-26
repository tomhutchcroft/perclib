/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project, written on 2026-11-21. A restatement of library lemmas; no upstream
code is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.RootGlobalPercolation

/-! # Correspondence wrapper: root and global percolation

## Main results

* `root_global_percolation_of_transitive`: on a countable vertex set, almost-sure existence of
  an infinite cluster is equivalent to positive root percolation at some vertex, and under a
  transitive law at any given root; for a family of transitive laws the parameter sets of
  positive root percolation, positive global percolation and almost-sure global percolation
  coincide, and so do their infima.

All mathematical inputs are proved in `PercLib.Percolation.Bond.RootGlobalPercolation`.
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Percolation.Bond

/-- On a countable vertex set: an infinite cluster exists almost surely iff some root
percolates with positive probability; under a transitive law, iff a given root does; for a
family of transitive laws the three parameter sets agree, and so do their infima. -/
@[tag "0YH8"]
theorem root_global_percolation_of_transitive {V ι : Type*} [Countable V] :
    (∀ q : Sym2 V → unitInterval,
      law q {ω | ∃ x, (cluster ω x).Infinite} = 1 ↔
        ∃ x, 0 < law q {ω | (cluster ω x).Infinite}) ∧
    (∀ q : Sym2 V → unitInterval,
      (∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ (law q).map (fun ω => Sym2.map σ '' ω) = law q) →
      ∀ o : V,
        (law q {ω | ∃ x, (cluster ω x).Infinite} = 1 ↔
          0 < law q {ω | (cluster ω o).Infinite})) ∧
    (∀ p : ι → Sym2 V → unitInterval,
      (∀ i, ∀ x y : V, ∃ σ : V ≃ V,
        σ x = y ∧ (law (p i)).map (fun ω => Sym2.map σ '' ω) = law (p i)) →
      ∀ o : V,
        {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
            {i | 0 < law (p i) {ω | ∃ x, (cluster ω x).Infinite}} ∧
          {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
            {i | law (p i) {ω | ∃ x, (cluster ω x).Infinite} = 1}) ∧
    (∀ [InfSet ι] (p : ι → Sym2 V → unitInterval),
      (∀ i, ∀ x y : V, ∃ σ : V ≃ V,
        σ x = y ∧ (law (p i)).map (fun ω => Sym2.map σ '' ω) = law (p i)) →
      ∀ o : V,
        sInf {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
            sInf {i | 0 < law (p i) {ω | ∃ x, (cluster ω x).Infinite}} ∧
          sInf {i | 0 < law (p i) {ω | (cluster ω o).Infinite}} =
            sInf {i | law (p i) {ω | ∃ x, (cluster ω x).Infinite} = 1}) :=
  ⟨law_exists_cluster_infinite_eq_one_iff,
    law_exists_cluster_infinite_eq_one_iff_of_transitive_law,
    fun p hT o => ⟨setOf_law_cluster_infinite_pos_eq_of_transitive_law p hT o,
      setOf_law_cluster_infinite_pos_eq_setOf_eq_one_of_transitive_law p hT o⟩,
    fun p hT o => ⟨sInf_setOf_law_cluster_infinite_pos_eq_of_transitive_law p hT o,
      sInf_setOf_law_cluster_infinite_pos_eq_setOf_eq_one_of_transitive_law p hT o⟩⟩

end PercLib.Percolation.Bond
