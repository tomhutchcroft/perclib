/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the survival probability, the total-progeny generating function
and the total-progeny tail of a critical Galton–Watson process. All mathematical inputs are
proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GaltonWatsonCriticalSurvival
public import PercLib.Probability.GaltonWatsonTotalProgenyTail

/-!
# Critical Galton–Watson processes: statement forms

## Main results

* `galtonWatson_survival_isEquivalent`: for mean one and finite positive variance `σ²`,
  `P(Zₙ > 0) ~ 2/(σ² n)`.
* `galtonWatson_one_sub_totalProgeny_genFun_isEquivalent`: for mean one and finite positive
  variance `σ²`, `F(s) = E[s^T]` satisfies `1 - F(s) ~ √(2(1-s)/σ²)` as `s ↑ 1`.
* `galtonWatson_totalProgeny_tail_bounds`: for mean one and finite positive variance,
  `c/√n ≤ P(T ≥ n) ≤ C/√n` for all large `n`.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics Topology
open scoped ENNReal

namespace PercLib.Probability

/-- For an offspring law `p` with mean `m = ∑ k p(k) = 1` and variance
`σ² = ∑ (k - 1)² p(k)` finite and positive, the Galton–Watson process satisfies
`P(Zₙ > 0) ~ 2/(σ² n)` as `n → ∞`. -/
@[tag "8WO7"]
theorem galtonWatson_survival_isEquivalent (p : PMF ℕ) (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1)
    {σ2 : ℝ} (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    (fun n : ℕ => (galtonWatsonMeasure p {ω | 0 < generationSize n ω}).toReal) ~[atTop]
      fun n : ℕ => 2 / (σ2 * n) :=
  isEquivalent_measureReal_generationSize_pos p hm hσ hσ0

/-- For an offspring law `p` with mean `m = ∑ k p(k) = 1` and variance
`σ² = ∑ (k - 1)² p(k)` finite and positive, the generating function
`F(s) = E[s^T] = ∑ₖ P(T = k) sᵏ` of the total progeny `T` satisfies
`1 - F(s) ~ √(2(1-s)/σ²)` as `s ↑ 1`. -/
@[tag "OVG9"]
theorem galtonWatson_one_sub_totalProgeny_genFun_isEquivalent (p : PMF ℕ)
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    (fun s => 1 - ∑' k : ℕ, (galtonWatsonMeasure p {ω | totalProgeny ω = k}).toReal * s ^ k)
      ~[𝓝[<] 1] fun s => Real.sqrt (2 * (1 - s) / σ2) :=
  isEquivalent_one_sub_tsum_measureReal_totalProgeny p hm hσ hσ0

/-- For an offspring law `p` with mean `m = ∑ k p(k) = 1` and variance
`σ² = ∑ (k - 1)² p(k)` finite and positive, there are constants `c, C > 0` such that the
total progeny satisfies `c n^{-1/2} ≤ P(T ≥ n) ≤ C n^{-1/2}` for all sufficiently large `n`. -/
@[tag "MIFH"]
theorem galtonWatson_totalProgeny_tail_bounds (p : PMF ℕ)
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    ∃ c > 0, ∃ C > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c / Real.sqrt n ≤ (galtonWatsonMeasure p {ω | (n : ℝ≥0∞) ≤ totalProgeny ω}).toReal ∧
        (galtonWatsonMeasure p {ω | (n : ℝ≥0∞) ≤ totalProgeny ω}).toReal ≤
          C / Real.sqrt n :=
  exists_measure_totalProgeny_ge_bounds p hm hσ hσ0

end PercLib.Probability
