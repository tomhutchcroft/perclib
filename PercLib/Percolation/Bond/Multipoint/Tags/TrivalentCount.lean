/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the count of leaf-labelled trivalent tree shapes. Mathematical
reference: the leaf-removal bijection for leaf-labelled trivalent (unrooted binary) trees, e.g.
C. Semple and M. Steel, *Phylogenetics* (Oxford University Press, 2003), Section 2.1. All
mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Multipoint.TrivalentCount

/-!
# Counting leaf-labelled trivalent tree shapes: correspondence

For `k ≥ 2`, the leaf-labelled trivalent tree shapes `𝒯_k = TreeShape k` number `(2k - 5)!!`
(with `(-1)!! = 1`; in `ℕ`, `2 * 2 - 5 = 0` and `0‼ = 1`). Every representative lives on
`Fin k ⊕ Fin (k - 2)`; that `k - 2` is the right number of internal vertices is the degree-sum
count `card_internal_and_card_edgeFinset_of_isTree`: any finite tree with `k` distinctly labelled
leaves and all other vertices of degree three has `k - 2` internal vertices and `2k - 3` edges.

## Main results

* `card_treeShape_and_card_vertices_and_card_edgeFinset`
-/

@[expose] public section

namespace PercLib.Percolation.Bond

/-- For `k ≥ 2`: (i) `|𝒯_k| = (2k - 5)!!`, with `(-1)!! = 1`; (ii) any finite tree whose
leaves carry the distinct labels `0, …, k - 1` and whose other vertices have degree three has
`k - 2` internal vertices and `2k - 3` edges; (iii) in particular every representative
trivalent tree on `Fin k ⊕ Fin (k - 2)` has `2k - 3` edges. -/
@[tag "SO5J"]
theorem card_treeShape_and_card_vertices_and_card_edgeFinset {k : ℕ} (hk : 2 ≤ k) :
    Nat.card (TreeShape k) = Nat.doubleFactorial (2 * k - 5) ∧
    (∀ {α : Type} [Fintype α] [DecidableEq α] (H : SimpleGraph α) [DecidableRel H.Adj],
      H.IsTree → ∀ ℓ : Fin k ↪ α, (∀ i, H.degree (ℓ i) = 1) →
        (∀ v, (∀ i, ℓ i ≠ v) → H.degree v = 3) →
        (Finset.univ.filter fun v => ∀ i, ℓ i ≠ v).card = k - 2 ∧
          H.edgeFinset.card = 2 * k - 3) ∧
    ∀ (G : SimpleGraph (Fin k ⊕ Fin (k - 2))) [Fintype G.edgeSet],
      IsTrivalentTree k G → G.edgeFinset.card = 2 * k - 3 :=
  ⟨card_treeShape hk,
    fun _ _ hH ℓ h1 h3 => card_internal_and_card_edgeFinset_of_isTree hH ℓ h1 h3,
    fun _ _ hG => card_edgeFinset_trivalentTree hG⟩

end PercLib.Percolation.Bond
