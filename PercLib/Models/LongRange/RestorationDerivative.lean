/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1. The high-temperature small-tail input is supplied by the restoration-map bounds.
-/
module

public import PercLib.Models.LongRange.PowerLawBinomialDerivative
public import PercLib.Percolation.Bond.RestorationWindow
public import PercLib.Models.LongRange.CutoffExhaustion.Moments

/-!
# A high-temperature instance of the cut-off binomial derivative

At the sup-norm power law with `β M < 1`, the restoration-majorant window supplies a finite
pair window locally in the cutoff scale. Combining it with the existing uncapped derivative
interfaces proves the binomial derivative at `r₀ = 3/2`, without gap factorization.
This is a corner-free interacting instance, not a critical or arbitrary-subcritical result.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

theorem hasDerivAt_powerLaw_three_halves_of_restoration {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal (∑' z : Fin d → ℤ,
      (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) (3 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (3 / 2)) β)))
      (3 / 2) := by
  refine hasDerivAt_powerLaw_three_halves_of_small_tail (d := d) hd hα hβ p hp ?_
  intro r₀ hr₀ ε hε
  exact exists_nhds_htail_powerLaw_of_restoration hd hα
    (CutoffExhaustion.lt_globalCriticalIntensity_of_BFS hd hα hβ) p hp 0 r₀ hr₀ ε hε

end PercLib.Models.LongRange
