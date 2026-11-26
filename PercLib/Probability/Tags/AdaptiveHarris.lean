/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the adaptive Harris and adaptive BK inequalities. The statements
are the library lemmas `prodBernoulli_mul_le_prod_hybrid` and
`prodBernoulli_prod_sharedWitness_le_mul`; no new definition is introduced. Mathematical reference:
N. Gladkov, "Percolation Inequalities and Decision Trees", arXiv:2408.08457 (2024).
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.AdaptiveHarris

/-!
# Adaptive Harris and BK inequalities: statement form

## Main results

* `adaptive_harris_of_same_monotonicity`
* `adaptive_bk_of_overlap_off_shared`
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
history (`hrun`). With the hybrid `H = X ∩ S ∪ Y \ S`, if `A, B ⊆ Set E` are both increasing or
both decreasing, then `P(X ∈ A, H ∈ B) ≥ μ(A) μ(B)`. -/
@[tag "26TT"]
theorem adaptive_harris_of_same_monotonicity [Fintype E] (p : E → unitInterval)
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
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e)
    (A B : Set (Set E))
    (hAB : (IsUpperSet A ∧ IsUpperSet B) ∨ (IsLowerSet A ∧ IsLowerSet B)) :
    prodBernoulli p A * prodBernoulli p B ≤
      (prodBernoulli p).prod (prodBernoulli p) {ω | ω.1 ∈ A ∧ ω.1 ∩ S ω ∪ ω.2 \ S ω ∈ B} :=
  prodBernoulli_mul_le_prod_hybrid next share answers p hrun hfresh S hS hAB

/-- Let `E` be finite and `μ = prodBernoulli p`, and let `ω = (X, Y)` have law `μ ⊗ μ`, read by
a predictable sharing tree as in `adaptive_harris_of_same_monotonicity`, with shared set `S` and
hybrid `H = X ∩ S ∪ Y \ S`. An open witness for `A` in `x` is a set `I ⊆ x` such that every
configuration containing `I` lies in `A`. Write `A □_S B` for the event that there are open
witnesses `I` for `A` in `X` and `J` for `B` in `H` with `I ∩ J ⊆ E \ S`. For increasing events
`A, B`, `P(A □_S B) ≤ μ(A) μ(B)`. -/
@[tag "7LLO"]
theorem adaptive_bk_of_overlap_off_shared [Fintype E] (p : E → unitInterval)
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
        next k (fun j => answers ω ⟨j.val, j.isLt.trans k.isLt⟩) = e)
    (A B : Set (Set E)) (_hA : IsUpperSet A) (_hB : IsUpperSet B) :
    (prodBernoulli p).prod (prodBernoulli p)
        {ω | ∃ I₁ J : Set E, I₁ ⊆ ω.1 ∧ (∀ z, I₁ ⊆ z → z ∈ A) ∧
          J ⊆ ω.1 ∩ S ω ∪ ω.2 \ S ω ∧ (∀ z, J ⊆ z → z ∈ B) ∧ I₁ ∩ J ⊆ (S ω)ᶜ} ≤
      prodBernoulli p A * prodBernoulli p B :=
  prodBernoulli_prod_sharedWitness_le_mul next share answers p hrun hfresh S hS A B

end PercLib.Probability
