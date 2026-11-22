/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for moment determinacy of the block-size law of a random finite
partition, proved from `PartitionSizeMoments.lean`. Mathematical reference: T. Hutchcroft,
*On the volume of clusters in hierarchical percolation* (2022), Section 2. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.PartitionSizeMoments

/-!
# Mixed mass moments and the block-size law: correspondence

Restates `Finpartition.map_parts_card_eq_of_sum_prod_pow_eq` and
`Finpartition.exists_pmf_ne_of_sum_prod_pow_eq` in the form of the wiki assertion.

## Main results

* `Finpartition.map_parts_card_eq_of_sum_prod_pow_eq_and_exists_pmf_ne`
-/

@[expose] public section
noncomputable section

open Finset

namespace Finpartition

universe u

/-- **W8PB.** For a random partition of a set with `N` points, the expectations of all products
of `S_p = ∑_b |b|^p`, `2 ≤ p ≤ N`, determine the law of the multiset of block sizes; they need
not determine the law of the labelled partition (two different laws on partitions of `Fin 3`
have the same mixed moments). -/
@[tag "W8PB"]
theorem map_parts_card_eq_of_sum_prod_pow_eq_and_exists_pmf_ne :
    (∀ (α : Type u) [Fintype α] [DecidableEq α] (μ ν : PMF (Finpartition (univ : Finset α))),
      (∀ k : ℕ → ℕ,
        ∑ P, (μ P).toReal *
            ∏ p ∈ Icc 2 (Fintype.card α), ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p =
          ∑ P, (ν P).toReal *
            ∏ p ∈ Icc 2 (Fintype.card α), ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p) →
      μ.map (fun P => P.parts.val.map Finset.card) =
        ν.map (fun P => P.parts.val.map Finset.card)) ∧
    ∃ μ ν : PMF (Finpartition (univ : Finset (Fin 3))), μ ≠ ν ∧ ∀ k : ℕ → ℕ,
      ∑ P, (μ P).toReal * ∏ p ∈ Icc 2 3, ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p =
        ∑ P, (ν P).toReal * ∏ p ∈ Icc 2 3, ((∑ b ∈ P.parts, b.card ^ p : ℕ) : ℝ) ^ k p :=
  ⟨fun _ _ _ μ ν h => map_parts_card_eq_of_sum_prod_pow_eq μ ν h,
    exists_pmf_ne_of_sum_prod_pow_eq⟩

end Finpartition
