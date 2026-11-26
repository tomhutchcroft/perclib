/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for predictable coordinate swaps. The statement is the library lemma
`prodBernoulli_prod_map_predictableSwap`; no new definition is introduced. Mathematical
reference: N. Gladkov, "Percolation Inequalities and Decision Trees", arXiv:2408.08457 (2024).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.PredictableSwap

/-!
# Predictable coordinate swaps: statement form

## Main results

* `predictable_swap_preserves_pair_law`
-/

@[expose] public section

open MeasureTheory

namespace PercLib.Probability

variable {E : Type*}

/-- Let `E` be finite and `μ = prodBernoulli p`, and let `ω = (X, Y)` have law `μ ⊗ μ`. A
decision tree of common depth `n` queries `next k h` at step `k`, where `h` records the
previously revealed pairs `(X e, Y e)`, and decides by `share k h`, before revealing the pair,
whether the coordinate enters the shared set `S`; a coordinate is shared only at its first query
(`hfresh`), and unqueried coordinates lie outside `S` (`hS`). `answers ω` is the revealed
history (`hrun`). Then `(H, H') = (X ∩ S ∪ Y \ S, Y ∩ S ∪ X \ S)` has law `μ ⊗ μ`. -/
@[tag "Q3MP"]
theorem predictable_swap_preserves_pair_law [Fintype E] (p : E → unitInterval)
    {n : ℕ}
    (next : (k : Fin n) → (Fin k.val → Bool × Bool) → E)
    (share : (k : Fin n) → (Fin k.val → Bool × Bool) → Bool)
    (answers : Set E × Set E → Fin n → Bool × Bool)
    (hrun : ∀ ω k,
      ((answers ω k).1 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.1) ∧
      ((answers ω k).2 = true ↔
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) ∈ ω.2))
    (hfresh : ∀ (h : Fin n → Bool × Bool) (k : Fin n),
      share k (fun j => h ⟨j.val, j.isLt.trans k.isLt⟩) = true → ∀ j : Fin n, j < k →
        next j (fun i => h ⟨i.val, i.isLt.trans j.isLt⟩) ≠
          next k (fun i => h ⟨i.val, i.isLt.trans k.isLt⟩))
    (S : Set E × Set E → Set E)
    (hS : ∀ ω e, e ∈ S ω ↔ ∃ k,
      share k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = true ∧
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e) :
    ((prodBernoulli p).prod (prodBernoulli p)).map
        (fun ω => (ω.1 ∩ S ω ∪ ω.2 \ S ω, ω.2 ∩ S ω ∪ ω.1 \ S ω)) =
      (prodBernoulli p).prod (prodBernoulli p) :=
  prodBernoulli_prod_map_predictableSwap p next share answers hrun hfresh S hS

end PercLib.Probability
