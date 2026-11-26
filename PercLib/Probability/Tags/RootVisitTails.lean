/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the tails of the root visit count of a Markov chain. All
mathematical inputs are proved in the imported module.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.RootVisitTails

/-!
# Root visit counts of a Markov chain: correspondence

Wiki correspondence for the exponential upper tail, the linear lower tail and the fractional
moments of the number of visits of a Markov chain to its starting point.

## Main results

* `root_visit_count_tails`
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal Nat

universe u v

namespace PercLib.Probability

/-- **Root visit counts.** Let `Z` be a time-homogeneous Markov chain on a countable state
space `S` with transition kernel `P`, started at `o`, given by its finite-dimensional
distributions. With `ℓ_n = ∑_{k ≤ n} 1_{Z k = o}` and `U_n = E ℓ_n`: for every `n ≥ 0`,
`0 ≤ θ < 1` and integer `m ≥ 1`, `E exp (θ ℓ_n / U_n) ≤ 1/(1 - θ)` and
`P(ℓ_n ≤ m) ≤ min {1, e/(1 - e⁻¹) · m/U_n}`; and for each `p > -1` there are positive
constants depending only on `p` with `c_p U_n^p ≤ E ℓ_n^p ≤ C_p U_n^p`. No recurrence
assumption is made. -/
@[tag "Y2C3"]
theorem root_visit_count_tails :
    (∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
      [DiscreteMeasurableSpace S] [Countable S] [DecidableEq S] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (P : Kernel S S) [IsMarkovKernel P] (Z : ℕ → Ω → S) (o : S),
      (∀ k, Measurable (Z k)) →
      (∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) →
      (∀ (n : ℕ) (θ : ℝ), 0 ≤ θ → θ < 1 →
        ∫ ω, Real.exp (θ * (((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ) /
          ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o})) ∂μ ≤ 1 / (1 - θ)) ∧
      (∀ n m : ℕ, 1 ≤ m →
        μ.real {ω | (∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0) ≤ m} ≤
          min 1 (Real.exp 1 / (1 - Real.exp (-1)) *
            (m / ∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o})))) ∧
    (∀ p : ℝ, -1 < p → ∃ c > 0, ∃ C > 0,
      ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
      [DiscreteMeasurableSpace S] [Countable S] [DecidableEq S] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (P : Kernel S S) [IsMarkovKernel P] (Z : ℕ → Ω → S) (o : S),
      (∀ k, Measurable (Z k)) →
      (∀ (n : ℕ) (x : Fin (n + 1) → S), μ {ω | ∀ i : Fin (n + 1), Z i ω = x i} =
        (if x 0 = o then 1 else 0) * ∏ i : Fin n, P (x i.castSucc) {x i.succ}) →
      ∀ n : ℕ,
        c * (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ p ≤
          ∫ ω, ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ) ^ p ∂μ ∧
        ∫ ω, ((∑ k ∈ range (n + 1), if Z k ω = o then 1 else 0 : ℕ) : ℝ) ^ p ∂μ ≤
          C * (∑ k ∈ range (n + 1), μ.real {ω | Z k ω = o}) ^ p) := by
  refine ⟨fun μ _ P _ Z o hm hZ => integral_exp_and_measureReal_visitCount_le hm hZ, ?_⟩
  intro p hp
  obtain ⟨c, hc, C, hC, h⟩ := exists_integral_visitCount_rpow_bounds.{u, v} hp
  exact ⟨c, hc, C, hC, fun μ _ P _ Z o hm hZ n => h μ P Z o hm hZ n⟩

end PercLib.Probability
