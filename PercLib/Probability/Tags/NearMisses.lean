/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the observable form of Holley's inequality (from `FKG.lean`) and the
capped total-variation bound between Bernoulli product laws (from `TotalVariation.lean`).
No upstream proof is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.FKG
public import PercLib.Probability.TotalVariation

/-!
# Holley's observable form and profile perturbations: correspondence

Wiki correspondence for Holley's comparison of increasing expectations on a finite Boolean
lattice, and for the bound `min {1, ∑ |q i - r i|}` on events and bounded observables under a
change of the Bernoulli profile.

## Main results

* `integral_le_and_measure_le_of_holley`
* `abs_prodBernoulli_real_sub_le_min_and_abs_integral_sub_le`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

/-- **KB49.** Let `E` be finite and `μ, ν` probability measures on the subsets of `E` whose point
masses satisfy Holley's condition `μ{S} ν{T} ≤ μ{S ∩ T} ν{S ∪ T}`. Then every increasing real
function has a smaller `μ`-expectation than `ν`-expectation, and in particular every increasing
event has smaller `μ`-probability. Neither measure needs full support. -/
@[tag "KB49"]
theorem integral_le_and_measure_le_of_holley {E : Type*} [Fintype E] (μ ν : Measure (Set E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ S T : Set E, μ {S} * ν {T} ≤ μ {S ∩ T} * ν {S ∪ T}) :
    (∀ f : Set E → ℝ, Monotone f → ∫ ω, f ω ∂μ ≤ ∫ ω, f ω ∂ν) ∧
      (∀ A : Set (Set E), IsUpperSet A → μ A ≤ ν A) :=
  ⟨fun _ hf => integral_le_of_holley μ ν h hf, fun _ hA => measure_le_of_holley μ ν h hA⟩

/-- **W90W.** Let `I` be countable, `q, r` profiles in `[0,1]^I` and `d₁ = ∑' i, |q i - r i|`
in `[0, ∞]`. Every measurable event has `|P_q(A) - P_r(A)| ≤ min {1, d₁}` (so the
total-variation distance, normalized as a supremum over events, is at most `min {1, d₁}`), and
every bounded measurable real `f` has `|E_q f - E_r f| ≤ (sup f - inf f) · min {1, d₁}`. -/
@[tag "W90W"]
theorem abs_prodBernoulli_real_sub_le_min_and_abs_integral_sub_le {I : Type*} [Countable I]
    (q r : I → unitInterval) :
    (∀ A : Set (Set I), MeasurableSet A →
      |(prodBernoulli q).real A - (prodBernoulli r).real A| ≤
        (min 1 (∑' i, ENNReal.ofReal |(q i : ℝ) - r i|)).toReal) ∧
      (∀ f : Set I → ℝ, Measurable f → BddAbove (range f) → BddBelow (range f) →
        |∫ ω, f ω ∂prodBernoulli q - ∫ ω, f ω ∂prodBernoulli r| ≤
          ((⨆ ω, f ω) - ⨅ ω, f ω) * (min 1 (∑' i, ENNReal.ofReal |(q i : ℝ) - r i|)).toReal) :=
  ⟨fun _ hA => abs_prodBernoulli_real_sub_le_min q r hA,
    fun _ hf hfa hfb => abs_integral_prodBernoulli_sub_le q r hf hfa hfb⟩

end PercLib.Probability

end
