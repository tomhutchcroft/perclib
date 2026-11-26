/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the effect of splitting one coordinate on a disjoint occurrence.
Every statement is assembled from lemmas proved in the imported modules; no new definition
is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.SplitCoordinate

/-!
# Splitting a coordinate in a disjoint occurrence: statement form

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `prodBernoulli_split_coordinate`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set

namespace PercLib.Probability
variable {I : Type*}

/-- Splitting coordinate `e` into two independent copies, one read by `A` and one by `B`,
increases `P(A □ B)` by `p² μ(C₁₁ \ U) + p(1-p) μ(V \ C₀₀)` with `p = q e`; both terms are
nonnegative, and the second vanishes exactly when `p ∈ {0, 1}` or `μ(V \ C₀₀) = 0`. -/
@[tag "XWH4"]
theorem prodBernoulli_split_coordinate [Finite I] (q : I → unitInterval) (e : I)
    {A B : Set (Set I)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (prodBernoulli (Sum.elim q fun _ : Unit => q e)).real
        (disjointOccurrence {ω : Set (I ⊕ Unit) | Sum.inl ⁻¹' ω ∈ A}
          {ω : Set (I ⊕ Unit) | {i | (i ≠ e ∧ Sum.inl i ∈ ω) ∨ (i = e ∧ Sum.inr () ∈ ω)} ∈ B}) -
      (prodBernoulli q).real (disjointOccurrence A B) =
      (q e : ℝ) ^ 2 * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
              {η | insert e (Subtype.val '' η) ∈ B} \
            (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∪
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B})) +
        (q e : ℝ) * (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          ((disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∩
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B}) \
            disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B}) ∧
    0 ≤ (q e : ℝ) ^ 2 * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
              {η | insert e (Subtype.val '' η) ∈ B} \
            (disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∪
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B})) ∧
    0 ≤ (q e : ℝ) * (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          ((disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∩
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B}) \
            disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B}) ∧
    ((q e : ℝ) * (1 - (q e : ℝ)) * (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          ((disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∩
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B}) \
            disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B}) = 0 ↔
      (q e : ℝ) = 0 ∨ (q e : ℝ) = 1 ∨
        (prodBernoulli (fun i : ({e}ᶜ : Set I) => q i)).real
          ((disjointOccurrence {η | insert e (Subtype.val '' η) ∈ A}
                {η | Subtype.val '' η ∈ B} ∩
              disjointOccurrence {η | Subtype.val '' η ∈ A}
                {η | insert e (Subtype.val '' η) ∈ B}) \
            disjointOccurrence {η | Subtype.val '' η ∈ A} {η | Subtype.val '' η ∈ B}) = 0) := by
  refine ⟨prodBernoulli_real_split_sub q hA hB, ?_, ?_, split_second_term_eq_zero_iff (q e) _⟩
  · exact (split_terms_nonneg (q e) _ 0 measureReal_nonneg le_rfl).1
  · exact (split_terms_nonneg (q e) 0 _ le_rfl measureReal_nonneg).2

end PercLib.Probability
