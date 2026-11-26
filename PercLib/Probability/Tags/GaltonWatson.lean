/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the extinction probability and the generation means of the
Galton–Watson process, proved in `PercLib.Probability.GaltonWatson`. Mathematical reference:
K. B. Athreya and P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I. No new
definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.GaltonWatson

/-!
# Galton–Watson process: extinction and expected total progeny

## Main results

* `PercLib.Probability.isLeast_extinction_genFun`: the extinction probability is the least
  fixed point of the offspring generating function in `[0, 1]`.
* `PercLib.Probability.extinction_criterion`: extinction is almost sure for `m < 1` and for
  `m = 1` unless `p(1) = 1`, never occurs if `p(1) = 1`, and fails with positive probability
  for `m > 1`.
* `PercLib.Probability.lintegral_generationSize_and_totalProgeny`: `E Zₙ = mⁿ`, and
  `E T = (1 - m)⁻¹` for `m < 1`, `E T = ∞` for `m ≥ 1`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

/-- **Extinction probability is the least generating-function fixed point.** For an offspring
law `p`, with `φ(s) = ∑ₖ p(k) sᵏ`, the extinction probability `q = P(∃ n, Zₙ = 0)` is the least
solution of `φ(s) = s` in `[0, 1]`. -/
@[tag "8TFY"]
theorem isLeast_extinction_genFun (p : PMF ℕ) :
    IsLeast {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r}
      (galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0}).toReal :=
  isLeast_galtonWatsonMeasure_extinction p

/-- **Mean generation sizes and expected total progeny.** With `m = ∑ₖ k p(k) ∈ [0, ∞]`,
`E Zₙ = mⁿ` for every `n`, and `E T = (1 - m)⁻¹` if `m < 1`, `E T = ∞` if `m ≥ 1`. -/
@[tag "UKY4"]
theorem lintegral_generationSize_and_totalProgeny (p : PMF ℕ) :
    (∀ n, ∫⁻ ω, (generationSize n ω : ℝ≥0∞) ∂galtonWatsonMeasure p =
      (∑' k : ℕ, (k : ℝ≥0∞) * p k) ^ n) ∧
    ∫⁻ ω, totalProgeny ω ∂galtonWatsonMeasure p =
      if ∑' k : ℕ, (k : ℝ≥0∞) * p k < 1 then (1 - ∑' k : ℕ, (k : ℝ≥0∞) * p k)⁻¹ else ⊤ :=
  ⟨lintegral_generationSize p, lintegral_totalProgeny_eq_ite p⟩

/-- **Extinction criterion with the deterministic critical exception.** With
`m = ∑ₖ k p(k) ∈ [0, ∞]` and extinction event `{∃ n, Zₙ = 0}`: if `m < 1`, extinction is almost
sure; if `m = 1`, extinction is almost sure unless `p(1) = 1` (that is, `ξ = 1` almost surely),
and in that exceptional case `Zₙ = 1` for every `n` almost surely and extinction has
probability zero; if `m > 1`, survival `{∀ n, Zₙ ≠ 0}` has positive probability. -/
@[tag "BFM4"]
theorem extinction_criterion (p : PMF ℕ) :
    (∑' k : ℕ, (k : ℝ≥0∞) * p k < 1 →
      galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 1) ∧
    (∑' k : ℕ, (k : ℝ≥0∞) * p k = 1 → p 1 ≠ 1 →
      galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 1) ∧
    (∑' k : ℕ, (k : ℝ≥0∞) * p k = 1 → p 1 = 1 →
      (∀ᵐ ω ∂galtonWatsonMeasure p, ∀ n, generationSize n ω = 1) ∧
        galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 0) ∧
    (1 < ∑' k : ℕ, (k : ℝ≥0∞) * p k →
      0 < galtonWatsonMeasure p {ω | ∀ n, generationSize n ω ≠ 0}) :=
  ⟨galtonWatsonMeasure_extinction_eq_one_of_mean_lt_one p,
    galtonWatsonMeasure_extinction_eq_one_of_mean_eq_one p,
    fun _ h => ⟨ae_forall_generationSize_eq_one p h,
      galtonWatsonMeasure_extinction_eq_zero_of_apply_one p h⟩,
    galtonWatsonMeasure_survival_pos_of_one_lt_mean p⟩

end PercLib.Probability
