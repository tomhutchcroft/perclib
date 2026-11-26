/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous bootstrap across a strict gap

A continuous quantity on a preconnected parameter set stays below a lower threshold
if it starts below an upper threshold and every upper bound improves to the lower one.
The strict gap prevents the quantity from reaching the upper threshold. No monotonicity
in the parameter is required.

## Main results

* `le_of_continuousOn_of_improves_le`: the bootstrap principle on a preconnected set.
* `le_on_Icc_of_improves_le`: the closed-interval form.
* `le_on_Ico_of_improves_le`: the half-open form, without continuity at the right endpoint.
-/

@[expose] public section

open Set

namespace PercLib.Analysis

variable {X α : Type*} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α]

/-- An improvement from an upper threshold to a strictly smaller lower threshold propagates
through a preconnected set. The starting value need only satisfy the upper bound. -/
theorem le_of_continuousOn_of_improves_le {s : Set X} {f : X → α} {a : X}
    {lower upper : α} (hs : IsPreconnected s) (hf : ContinuousOn f s) (ha : a ∈ s)
    (hstart : f a ≤ upper) (hgap : lower < upper)
    (himprove : ∀ x ∈ s, f x ≤ upper → f x ≤ lower) :
    ∀ x ∈ s, f x ≤ lower := by
  intro x hx
  rcases le_total (f x) upper with hxu | hux
  · exact himprove x hx hxu
  obtain ⟨z, hzs, hfz⟩ := hs.intermediate_value ha hx hf ⟨hstart, hux⟩
  have hz := himprove z hzs hfz.le
  exact (not_le_of_gt hgap (hfz ▸ hz)).elim

section Intervals

variable {β : Type*} [ConditionallyCompleteLinearOrder β] [DenselyOrdered β]
  [TopologicalSpace β] [OrderTopology β]

/-- The continuous bootstrap principle on a closed interval. It also covers an empty
interval, so no separate ordering assumption on the endpoints is needed. -/
theorem le_on_Icc_of_improves_le {f : β → α} {a b : β} {lower upper : α}
    (hf : ContinuousOn f (Icc a b)) (hstart : f a ≤ upper) (hgap : lower < upper)
    (himprove : ∀ x ∈ Icc a b, f x ≤ upper → f x ≤ lower) :
    ∀ x ∈ Icc a b, f x ≤ lower := by
  intro x hx
  exact le_of_continuousOn_of_improves_le isPreconnected_Icc hf
    ⟨le_rfl, hx.1.trans hx.2⟩ hstart hgap himprove x hx

/-- The continuous bootstrap principle below an excluded right endpoint. In particular,
this requires no value or continuity assumption at a critical endpoint. -/
theorem le_on_Ico_of_improves_le {f : β → α} {a b : β} {lower upper : α}
    (hf : ContinuousOn f (Ico a b)) (hstart : f a ≤ upper) (hgap : lower < upper)
    (himprove : ∀ x ∈ Ico a b, f x ≤ upper → f x ≤ lower) :
    ∀ x ∈ Ico a b, f x ≤ lower := by
  intro x hx
  exact le_of_continuousOn_of_improves_le isPreconnected_Ico hf
    ⟨le_rfl, hx.1.trans_lt hx.2⟩ hstart hgap himprove x hx

end Intervals

/-- The bootstrap hypotheses admit a nonconstant continuous function on a nontrivial interval. -/
example : ∃ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) ∧ f 0 ≤ 2 ∧
    (∀ x ∈ Icc 0 1, f x ≤ 2 → f x ≤ 1) ∧ f 0 < f 1 := by
  refine ⟨id, continuousOn_id, ?_, ?_, zero_lt_one⟩
  · exact zero_le_one.trans (by exact_mod_cast Nat.le_succ 1)
  · intro x hx _
    exact hx.2

end PercLib.Analysis
