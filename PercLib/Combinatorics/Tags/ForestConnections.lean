/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the finite-forest branch-vertex assertion 4K33, proved from
`ForestBranching.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.ForestBranching

/-!
# Branch vertices and leaves of a finite forest

Restates results of `PercLib.Combinatorics.ForestBranching` as one tagged conjunction.

## Main results

* `PercLib.forest_degree_excess_and_branch_bounds`: the signed degree-excess identity of a finite
  forest, the bound `|B| ≤ |L| - 2(c - i) ≤ |L|`, and the two finite-tree bounds.
-/

@[expose] public section
noncomputable section

open Finset

namespace PercLib

variable {W : Type*} [Fintype W]

/-- **4K33.** Let `T` be a finite forest with `c` connected components and `i` isolated vertices,
let `L` be its set of degree-one vertices and `B` its set of vertices of degree at least three.
Then `∑_v (deg v - 2) = -2c` (signed subtraction) and `|B| ≤ |L| - 2(c - i) ≤ |L|`. A finite tree
with at least two vertices has `|B| + 2 ≤ |L|`, and if a set `A` of at least two vertices contains
every leaf of a finite tree, then `|B| ≤ |A| - 2`. -/
@[tag "4K33"]
theorem forest_degree_excess_and_branch_bounds (T : SimpleGraph W) [DecidableRel T.Adj] :
    (T.IsAcyclic →
      ∑ v : W, ((T.degree v : ℤ) - 2) = -2 * Nat.card T.ConnectedComponent ∧
      ((univ.filter fun v => 3 ≤ T.degree v).card : ℤ) ≤
        (univ.filter fun v => T.degree v = 1).card -
          2 * ((Nat.card T.ConnectedComponent : ℤ) - (univ.filter fun v => T.degree v = 0).card) ∧
      ((univ.filter fun v => T.degree v = 1).card : ℤ) -
          2 * ((Nat.card T.ConnectedComponent : ℤ) - (univ.filter fun v => T.degree v = 0).card) ≤
        (univ.filter fun v => T.degree v = 1).card) ∧
    (T.IsTree → 2 ≤ Fintype.card W →
      (univ.filter fun v => 3 ≤ T.degree v).card + 2 ≤
        (univ.filter fun v => T.degree v = 1).card) ∧
    (T.IsTree → ∀ A : Finset W, (∀ v, T.degree v = 1 → v ∈ A) → 2 ≤ A.card →
      (univ.filter fun v => 3 ≤ T.degree v).card ≤ A.card - 2) :=
  ⟨fun hT => ⟨forest_sum_degree_sub_two T hT, forest_card_branch_le_leaves_sub_two_mul T hT,
      by have := card_degree_eq_zero_le_card_connectedComponent T; omega⟩,
    fun hT hW =>
      have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      tree_card_branch_add_two_le_leaves T hT,
    fun hT A hA hcard => tree_card_branch_le_card_sub_two T hT A hA hcard⟩

end PercLib
