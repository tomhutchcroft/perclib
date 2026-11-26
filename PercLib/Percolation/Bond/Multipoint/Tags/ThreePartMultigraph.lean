/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the regular multigraph bound obtained from three-part product
inequalities (T. Hutchcroft, *Critical long-range percolation II*, arXiv:2508.18808v1, (II.3.3)).
All mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Multipoint.ThreePartMultigraph

/-!
# Three-part product inequalities yield the regular multigraph bound: correspondence

Wiki correspondence for the bound `t(A) ^ 2 ^ (n - 2) ≤ C ∑_Q ∏ t({x, y}) ^ q_{xy}` over the
connected loopless `2 ^ (n - 2)`-regular multigraphs `Q` on an `n`-point set `A`, under the
three-part product inequalities, together with its root form.

## Main results

* `pow_le_mul_finsum_regularMultigraph_and_root`
-/

@[expose] public section
noncomputable section
open Finset

universe u

namespace PercLib.Percolation.Bond

/-- Let `|A| = n ≥ 2` and `t ≥ 0` on the subsets of `A` with at least two elements. Suppose every
`B ⊆ A` with `|B| ≥ 3` has a partition `B = B₁ ⊔ B₂ ⊔ B₃` into nonempty parts with
`t(B)² ≤ K_{|B|} t(B₁ ∪ B₂) t(B₁ ∪ B₃) t(B₂ ∪ B₃)` (equivalently, `t(B)²` is at most `K_{|B|}`
times the maximum over such partitions). Then, with constants depending only on `n` and `K`:
(i) `t(A) ^ 2 ^ (n - 2) ≤ C ∑_Q ∏_{x ≠ y} t({x, y}) ^ q_{xy}`, the sum over the connected
loopless multigraphs `Q` on `A` of degree `2 ^ (n - 2)` at every vertex (parallel edges allowed);
(ii) `t(A) ≤ C ∑_Q ∏_{x ≠ y} t({x, y}) ^ (q_{xy} / 2 ^ (n - 2))`. -/
@[tag "L3HA"]
theorem pow_le_mul_finsum_regularMultigraph_and_root (n : ℕ) (hn : 2 ≤ n) (K : ℕ → ℝ) :
    (∃ C : ℝ, ∀ {α : Type u} [DecidableEq α] (A : Finset α) (t : Finset α → ℝ), A.card = n →
      (∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) →
      (∀ B ⊆ A, 3 ≤ B.card → ∃ B₁ B₂ B₃ : Finset α, B₁.Nonempty ∧ B₂.Nonempty ∧ B₃.Nonempty ∧
        Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧ B₁ ∪ B₂ ∪ B₃ = B ∧
        t B ^ 2 ≤ K B.card * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) →
      t A ^ 2 ^ (n - 2) ≤ C * ∑ᶠ q ∈ {q : Sym2 α →₀ ℕ |
          (∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ A) ∧
          (∀ x ∈ A, ∑ y ∈ A, q s(x, y) = 2 ^ (n - 2)) ∧
          ∀ x ∈ A, ∀ y ∈ A, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y},
        ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ q e) ∧
    (∃ C : ℝ, ∀ {α : Type u} [DecidableEq α] (A : Finset α) (t : Finset α → ℝ), A.card = n →
      (∀ B ⊆ A, 2 ≤ B.card → 0 ≤ t B) →
      (∀ B ⊆ A, 3 ≤ B.card → ∃ B₁ B₂ B₃ : Finset α, B₁.Nonempty ∧ B₂.Nonempty ∧ B₃.Nonempty ∧
        Disjoint B₁ B₂ ∧ Disjoint B₁ B₃ ∧ Disjoint B₂ B₃ ∧ B₁ ∪ B₂ ∪ B₃ = B ∧
        t B ^ 2 ≤ K B.card * (t (B₁ ∪ B₂) * t (B₁ ∪ B₃) * t (B₂ ∪ B₃))) →
      t A ≤ C * ∑ᶠ q ∈ {q : Sym2 α →₀ ℕ |
          (∀ e ∈ q.support, ¬e.IsDiag ∧ ∀ x ∈ e, x ∈ A) ∧
          (∀ x ∈ A, ∑ y ∈ A, q s(x, y) = 2 ^ (n - 2)) ∧
          ∀ x ∈ A, ∀ y ∈ A, (SimpleGraph.fromRel fun u v => q s(u, v) ≠ 0).Reachable x y},
        ∏ e ∈ A.sym2.filter (fun e => ¬e.IsDiag), t e.toFinset ^ ((q e : ℝ) / 2 ^ (n - 2))) :=
  ⟨pow_le_mul_finsum_regularMultigraph.{u} n hn K,
    le_mul_finsum_prod_rpow_regularMultigraph.{u} n hn K⟩

end PercLib.Percolation.Bond
