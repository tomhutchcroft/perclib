/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the branching random walk model and the first moments of its
occupation counts. All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.BranchingRandomWalkMoment

/-!
# Branching random walk occupation: correspondence

Wiki correspondence for the generation process of branching random walk and the first moments
of its generation and occupation counts.

## Main results

* `brwMeasure_spec`
* `brw_occupation_first_moments`
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace PercLib.Probability.BranchingRandomWalk

/-- **Branching random walk.** On a discrete state space `S` with Markov kernel `P` and
offspring law `ξ` on `ℕ`, the generation process `brwMeasure ξ P x` starts from the single
particle at `x`, and, given the generations up to `n`, generation `n + 1` has law
`stepLaw ξ P (ω n)`: every particle at `z` independently has a `ξ`-distributed number of
children, placed independently according to `P z`. `(ω n).count y` is `N_n(y)` and
`∑' n, (ω n).count y` is the occupation count `L_y`. -/
@[tag "CYYG"]
theorem brwMeasure_spec {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Countable S] (ξ : Measure ℕ) [IsProbabilityMeasure ξ] (P : Kernel S S) [IsMarkovKernel P]
    (x : S) :
    (∀ g : Config S → ℝ≥0∞, ∫⁻ ω, g (ω 0) ∂brwMeasure ξ P x = g (Config.ofList [x])) ∧
    (∀ (n : ℕ) (G : (Π _ : Iic n, Config S) → Config S → ℝ≥0∞),
      ∫⁻ ω, G (frestrictLe n ω) (ω (n + 1)) ∂brwMeasure ξ P x =
        ∫⁻ ω, ∫⁻ c, G (frestrictLe n ω) c ∂stepLaw ξ P (ω n).toList ∂brwMeasure ξ P x) :=
  ⟨lintegral_brwMeasure_zero x, lintegral_brwMeasure_succ x⟩

/-- **First moments of branching-random-walk occupation.** With `m = ∫⁻ k, k ∂ξ`,
`E_x N_n(y) = mⁿ Pⁿ(x, y)` for every `n ≥ 0` (with `P⁰(x, y) = 1_{x = y}` and `m⁰ = 1`, also
for `m = 0`), `E_x L_y = ∑ₙ mⁿ Pⁿ(x, y)`, and at criticality `m = 1` the expected occupation is
the Green function `∑ₙ Pⁿ(x, y)`. The finiteness `m < ∞` of the source is not needed. -/
@[tag "94E7"]
theorem brw_occupation_first_moments {S : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [Countable S] [DecidableEq S] (ξ : Measure ℕ)
    [IsProbabilityMeasure ξ] (P : Kernel S S) [IsMarkovKernel P] (x y : S) :
    (∀ n : ℕ, ∫⁻ ω, ((ω n).count y : ℝ≥0∞) ∂brwMeasure ξ P x =
      (∫⁻ k, (k : ℝ≥0∞) ∂ξ) ^ n * (P ^ n) x {y}) ∧
    ∫⁻ ω, ∑' n, ((ω n).count y : ℝ≥0∞) ∂brwMeasure ξ P x =
      ∑' n, (∫⁻ k, (k : ℝ≥0∞) ∂ξ) ^ n * (P ^ n) x {y} ∧
    (∫⁻ k, (k : ℝ≥0∞) ∂ξ = 1 →
      ∫⁻ ω, ∑' n, ((ω n).count y : ℝ≥0∞) ∂brwMeasure ξ P x = ∑' n, (P ^ n) x {y}) :=
  ⟨lintegral_count_brwMeasure x y, lintegral_occupation_brwMeasure x y,
    fun hm => lintegral_occupation_brwMeasure_of_mean_eq_one hm x y⟩

end PercLib.Probability.BranchingRandomWalk
