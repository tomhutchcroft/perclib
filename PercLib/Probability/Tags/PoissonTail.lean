/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the Poisson tail and its extended parameter, proved from
`PoissonTail.lean`. Mathematical reference: W. Feller, *An Introduction to Probability Theory
and Its Applications*, Vol. 1, Chapter VI. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.PoissonTail

/-!
# Poisson tails and the extended path parameter

Restates the properties of the Poisson tail `Q_j` in the form of the wiki assertion.

## Main results

* `PercLib.poissonTail_bijOn_and_tendsto_binomial`: for `j ≥ 1`, `Q_j` is continuous, strictly
  increasing and a bijection from `[0, ∞)` onto `[0, 1)`; every `p ∈ [0, 1]` has a unique
  extended parameter `λ ∈ [0, ∞]` with `p = Q_j(λ)` (`Q_j(∞) = 1`); and the tails of the
  number of successes among `N` independent routes of success probability `λ / N` tend to
  `Q_j(λ)`.
-/

@[expose] public section

open Filter Topology MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal

namespace PercLib

/-- **Poisson tails give a well-defined extended parameter for every positive path-count
threshold.** For an integer `j ≥ 1`, `Q_j(λ) = 1 - e^{-λ} ∑_{i < j} λ^i / i!` is continuous,
strictly increasing on `[0, ∞)`, and a bijection from `[0, ∞)` onto `[0, 1)`. With
`Q_j(∞) = 1`, every `p ∈ [0, 1]` equals `Q_j(λ)` for a unique `λ ∈ [0, ∞]`. If `N`
independent routes each succeed with probability `λ / N` (for all large `N`), the number of
successful routes, of law `Bin(N, λ / N)`, satisfies `P(· ≥ j) → Q_j(λ)` as `N → ∞`.

Continuity holds on all of `ℝ`; the limit statement needs no sign condition on `λ`, since
`λ / N ∈ [0, 1]` forces `λ ≥ 0`. -/
@[tag "TIKW"]
theorem poissonTail_bijOn_and_tendsto_binomial {j : ℕ} (hj : 1 ≤ j) :
    Continuous (poissonTail j) ∧ StrictMonoOn (poissonTail j) (Set.Ici 0) ∧
    Set.BijOn (poissonTail j) (Set.Ici 0) (Set.Ico 0 1) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, ∃! l : ℝ≥0∞, p = if l = ⊤ then 1 else poissonTail j l.toReal) ∧
    (∀ (lam : ℝ) (q : ℕ → I), (∀ᶠ N in atTop, (q N : ℝ) = lam / N) →
      Tendsto (fun N ↦ (binomial N (q N)).real (Set.Ici j)) atTop (𝓝 (poissonTail j lam))) :=
  ⟨continuous_poissonTail j, strictMonoOn_poissonTail hj, bijOn_poissonTail hj,
    fun _ hp ↦ existsUnique_eq_poissonTail_ennreal hj hp,
    fun _ _ hq ↦ tendsto_binomial_real_Ici_poissonTail_of_eventually_eq_div hq j⟩

end PercLib
