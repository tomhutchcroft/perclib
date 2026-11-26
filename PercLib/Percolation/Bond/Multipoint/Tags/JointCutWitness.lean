/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the joint-cut witness lemma used in the critical joint-cut estimate
of T. Hutchcroft, *Critical long-range percolation III* (Lemma III.6.16). All mathematical
inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Multipoint.JointCutWitness

/-!
# Joint vertex cuts and disjoint three-point witnesses: correspondence

Wiki correspondence for the statement that a connection destroyed only by deleting two
disjoint vertex sets together supplies two finite connected witnesses through the three
points `y, b, c` and `a, b, c`, meeting exactly in `{b, c}` and sharing no edge.

## Main results

* `exists_subgraphs_of_joint_cut_of_disjoint`
-/

@[expose] public section

namespace PercLib.Percolation.Bond

open SimpleGraph

/-- Let `G` be any graph and `A, B` disjoint vertex sets. If `y` is connected to `a` in
`G \ A` and in `G \ B` but not in `G \ (A ∪ B)`, then there are `b ∈ A`, `c ∈ B` and finite
connected subgraphs `H_y, H_a` of `G` containing `{y, b, c}` and `{a, b, c}` with
`V(H_y) ∩ V(H_a) = {b, c}` and `E(H_y) ∩ E(H_a) = ∅`. Connection in `G \ S` is a walk of `G`
whose support avoids `S`. -/
@[tag "RIH3"]
theorem exists_subgraphs_of_joint_cut_of_disjoint {V : Type*} (G : SimpleGraph V)
    {A B : Set V} (_hdisj : Disjoint A B) {y a : V}
    (hA : ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ A)
    (hB : ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ B)
    (hAB : ¬ ∃ p : G.Walk y a, ∀ x ∈ p.support, x ∉ A ∪ B) :
    ∃ b ∈ A, ∃ c ∈ B, ∃ Hy Ha : G.Subgraph,
      Hy.Connected ∧ Ha.Connected ∧ Hy.verts.Finite ∧ Ha.verts.Finite ∧
      {y, b, c} ⊆ Hy.verts ∧ {a, b, c} ⊆ Ha.verts ∧
      Hy.verts ∩ Ha.verts = {b, c} ∧ Disjoint Hy.edgeSet Ha.edgeSet :=
  exists_subgraphs_of_joint_cut hA hB fun p =>
    by_contra fun h => hAB ⟨p, fun x hx hx' => h ⟨x, hx, hx'⟩⟩

end PercLib.Percolation.Bond
