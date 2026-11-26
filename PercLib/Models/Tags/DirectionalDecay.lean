/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the directional-correlation-length article. New proofs, no
upstream code; every statement is assembled from lemmas proved in
`PercLib.Models.DirectionalDecay`, and no definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.DirectionalDecay

/-!
# Directional decay rates on `ℤ^d`: statement forms

Each theorem restates results proved under their own names in
`PercLib.Models.DirectionalDecay`.

## Main results

* `zdGraph_directional_rate_bounds`: below the inverse connective constant, the
  nearest-neighbour directional rate exists, lies between `‖v‖₁ log(1/(p μ_d))` and
  `‖v‖₁ log(1/p)`, and is positive for `v ≠ 0`.
* `powerLaw_directional_rate_zero_and_chi_le`: the power-law intensities have zero
  directional rate for every `β > 0`, while `M < ∞` and `χ(0) ≤ (1 - βM)⁻¹` when `βM < 1`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Topology PercLib.Percolation.Bond PercLib.Models.LongRange
open scoped ENNReal

namespace PercLib.Models.Site

variable {d : ℕ}

open Classical in
/-- For homogeneous nearest-neighbour bond percolation on `ℤ^d`, `d ≥ 1`, with `μ_d` the
connective constant and `0 < p < μ_d⁻¹`: for every `v`, the directional rate
`m_p(v) = lim -(1/n) log τ_p(0, n v)` exists, satisfies
`‖v‖₁ log(1/(p μ_d)) ≤ m_p(v) ≤ ‖v‖₁ log(1/p)`, and is positive for `v ≠ 0`. -/
@[tag "I8WP"]
theorem zdGraph_directional_rate_bounds (hd : 1 ≤ d) {μ : ℝ}
    (hμ : Tendsto (fun n : ℕ => (Nat.card {p : Σ y, (zdGraph d).Path 0 y //
      p.2.1.length = n} : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ))
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hpμ : (p : ℝ) < μ⁻¹) (v : Fin d → ℤ) :
    ∃ m : ℝ, Tendsto (fun n : ℕ => -Real.log (tau (fun e => if e ∈ (zdGraph d).edgeSet then p
        else 0) 0 (n • v)).toReal / n) atTop (𝓝 m) ∧
      (∑ i, (v i).natAbs : ℕ) * Real.log (1 / ((p : ℝ) * μ)) ≤ m ∧
      m ≤ (∑ i, (v i).natAbs : ℕ) * Real.log (1 / (p : ℝ)) ∧
      (v ≠ 0 → 0 < m) :=
  exists_tendsto_neg_log_tau_div_nearestNeighbour_of_lt_inv hd hμ p hp0 hpμ v

/-- On `ℤ^d`, `d ≥ 1`, `α > 0`, with each non-loop bond `{x, y}` open with probability
`q_β(x, y) = 1 - exp(-β ‖y - x‖_∞^{-d-α})`: for every `β > 0` the directional rate is `0` in
every direction; `M = ∑_{z ≠ 0} ‖z‖_∞^{-d-α}` is finite; and `β M < 1` gives
`χ_β(0) ≤ (1 - βM)⁻¹`. -/
@[tag "23RT"]
theorem powerLaw_directional_rate_zero_and_chi_le (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    (∀ β : NNReal, 0 < β → ∀ v : Fin d → ℤ,
      Tendsto (fun n : ℕ => -Real.log (tau (intensityProfile (radialKernel
        (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) 0
          (n • v)).toReal / n) atTop (𝓝 0)) ∧
    Summable (fun z : Fin d → ℤ => if z = 0 then (0 : ℝ) else ‖z‖ ^ (-((d : ℝ) + α))) ∧
    (∀ β : NNReal,
      (β : ℝ) * ∑' z : Fin d → ℤ, (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) < 1 →
      chi (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α))) β) 0 ≤
        ENNReal.ofReal (1 - (β : ℝ) * ∑' z : Fin d → ℤ,
          (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))))⁻¹) :=
  ⟨fun _ hβ v => tendsto_neg_log_tau_div_powerLaw_zero hα hβ v, summable_powerLaw hd hα,
    fun β hβ => chi_intensity_powerLaw_le hd hα β hβ 0⟩

end PercLib.Models.Site
