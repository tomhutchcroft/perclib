/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the fair order of two exits of the randomised depth-first search,
proved from `DFSPivot.lean`. Mathematical reference: I. Gladkov and I. Pak, *Exploring mazes at
random*. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.DFSPivot

/-!
# The DFS pivot involution

Restates `PercLib.card_filter_idxOf_lt_div`, `PercLib.exists_involutive_coinRun_pivot` and
`PercLib.card_filter_coinRun_eq_of_branching` in the form of the wiki assertion.

## Main results

* `PercLib.dfs_pivot_fair_exits`: for the randomised depth-first search from a leaf `A` of a
  finite connected graph of maximum degree three, with leaf targets `B, C`, the probability that
  `B` is discovered before `C` is `1/2`; an involution of the coin space keeps the rooted discovery
  tree and exchanges the two discovery orders; and given the tree, the coins at its branching
  vertices are uniform.
-/

@[expose] public section

namespace PercLib

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Fair order of two exits.** Let `G` be a finite connected graph of maximum degree three with
distinct leaves `A, B, C`, and let `ρ u p` list the neighbours of `u` other than `p` (in any fixed
order). Run the recursive depth-first search from `A` to completion, where on first entering a
vertex of degree three a fair coin decides which of its two other edges is examined first
(`coinRun G ρ A b` is the list of discoveries `(child, parent)` in order, for the coin assignment
`b`). Then

* `B` is discovered before `C` for exactly half of the coin assignments;
* there is an involution of the coin space (hence a bijection, preserving the uniform law) that
  keeps the rooted discovery tree and exchanges the discovery orders of `B` and `C`;
* conditional on the discovery tree `T`, the coins at any set `W` of branching vertices of `T`
  (vertices with two children), which fix the order of their two child branches, are independent
  and fair: every prescription of their values is met by equally many assignments with tree `T`. -/
@[tag "KRU2"]
theorem dfs_pivot_fair_exits {ρ : V → V → List V}
    (hρ : ∀ u p, (ρ u p).Nodup ∧ ∀ w, w ∈ ρ u p ↔ G.Adj u w ∧ w ≠ p) (hconn : G.Connected)
    {A B C : V} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hA : G.degree A = 1)
    (hB : G.degree B = 1) (hC : G.degree C = 1) (hdeg : ∀ u, G.degree u ≤ 3) :
    ((Finset.univ.filter fun b : {u // G.degree u = 3} → Bool =>
      ((coinRun G ρ A b).map Prod.fst).idxOf B <
        ((coinRun G ρ A b).map Prod.fst).idxOf C).card : ℚ) /
      Fintype.card ({u // G.degree u = 3} → Bool) = 1 / 2 ∧
    (∃ φ : ({u // G.degree u = 3} → Bool) → ({u // G.degree u = 3} → Bool),
      Function.Involutive φ ∧ ∀ b, (coinRun G ρ A (φ b)).toFinset = (coinRun G ρ A b).toFinset ∧
        (((coinRun G ρ A (φ b)).map Prod.fst).idxOf B <
            ((coinRun G ρ A (φ b)).map Prod.fst).idxOf C ↔
          ((coinRun G ρ A b).map Prod.fst).idxOf C <
            ((coinRun G ρ A b).map Prod.fst).idxOf B)) ∧
    (∀ (T : Finset (V × V)) (W : Finset {u // G.degree u = 3}),
      (∀ w ∈ W, ∃ x y, x ≠ y ∧ (x, w.1) ∈ T ∧ (y, w.1) ∈ T) →
      ∀ a a' : {u // G.degree u = 3} → Bool,
        (Finset.univ.filter fun b =>
          (coinRun G ρ A b).toFinset = T ∧ ∀ s ∈ W, b s = a s).card =
        (Finset.univ.filter fun b =>
          (coinRun G ρ A b).toFinset = T ∧ ∀ s ∈ W, b s = a' s).card) :=
  ⟨card_filter_idxOf_lt_div hρ hconn hAB hAC hBC hA hB hC hdeg,
    exists_involutive_coinRun_pivot hρ hconn hAB hAC hBC hA hB hC hdeg,
    fun T W hW a a' => card_filter_coinRun_eq_of_branching hρ hA hdeg T W hW a a'⟩

end PercLib
