/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the spatial-cutoff-moments assertion GAF9, proved from
`LinearODEAsymptotics.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.LinearODEAsymptotics

/-!
# Spatial cutoff moments: correspondence

Wiki correspondence for the asymptotics of the linear spatial-moment ODE of
`PercLib/Analysis/LinearODEAsymptotics.lean`.

## Main results

* `linearODE_asymptotics`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- **GAF9.** Let `r₀ ≥ 1`, `α, c > 0`, `S ≥ 0` absolutely continuous on every `[r₀, R]` with
`S' = (2α/r + e) S + g` a.e. on `[r₀, ∞)`, `e` integrable on `[r₀, ∞)`, `g ≥ 0` and
`g ~ c r^{α+1}`. Then `S ~ c r^{α+2}/(2-α)` if `α < 2`, `S ~ c r⁴ log r` if `α = 2`, and
`S ~ K r^{2α}` for some `K > 0` if `α > 2`. If moreover `m ~ m₀ r^α` with `m₀ > 0`, then
`√(S/m) ≍ r`, `r √(log r)` and `r^{α/2}` in the three cases. -/
@[tag "GAF9"]
theorem linearODE_asymptotics {α c r₀ : ℝ} {S e g : ℝ → ℝ} (hr₀ : 1 ≤ r₀) (_hα : 0 < α)
    (hc : 0 < c) (hS0 : ∀ r, r₀ ≤ r → 0 ≤ S r)
    (hSac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval S r₀ R)
    (hder : ∀ᵐ r, r₀ ≤ r → deriv S r = (2 * α / r + e r) * S r + g r)
    (he : IntegrableOn e (Ici r₀)) (hg0 : ∀ r, r₀ ≤ r → 0 ≤ g r)
    (hg : g ~[atTop] fun r => c * r ^ (α + 1)) :
    ((α < 2 → S ~[atTop] fun r => c * r ^ (α + 2) / (2 - α)) ∧
     (α = 2 → S ~[atTop] fun r => c * r ^ (4 : ℝ) * Real.log r) ∧
     (2 < α → ∃ K > 0, S ~[atTop] fun r => K * r ^ (2 * α))) ∧
    ∀ {m : ℝ → ℝ} {m₀ : ℝ}, 0 < m₀ → (m ~[atTop] fun r => m₀ * r ^ α) →
     ((α < 2 → (fun r => √(S r / m r)) =Θ[atTop] fun r => r) ∧
      (α = 2 → (fun r => √(S r / m r)) =Θ[atTop] fun r => r * √(Real.log r)) ∧
      (2 < α → (fun r => √(S r / m r)) =Θ[atTop] fun r => r ^ (α / 2))) :=
  ⟨⟨fun h => isEquivalent_linearODE_lt hr₀ h hc hSac hder he hg0 hg,
    fun h => isEquivalent_linearODE_eq hr₀ h hc hSac hder he hg0 hg,
    fun h => exists_isEquivalent_linearODE_gt hr₀ h hc hS0 hSac hder he hg0 hg⟩,
   fun hm₀ hm => ⟨fun h => isTheta_sqrt_linearODE_lt hr₀ h hc hSac hder he hg0 hg hm₀ hm,
    fun h => isTheta_sqrt_linearODE_eq hr₀ h hc hSac hder he hg0 hg hm₀ hm,
    fun h => isTheta_sqrt_linearODE_gt hr₀ h hc hS0 hSac hder he hg0 hg hm₀ hm⟩⟩

end PercLib.Analysis
