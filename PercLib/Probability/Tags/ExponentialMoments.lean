/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for exponential moments and tails from double-factorial moment
bounds, and for the divergence bound between intensity-parametrised Bernoulli laws. Every
statement is assembled from lemmas proved in the imported modules; no new definition is
introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.ExponentialMoments
public import PercLib.Probability.BernoulliDivergence

/-!
# Exponential moments and divergence bounds: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `exponential_moments_of_moment_bounds`
* `tail_bounds_of_moment_bounds`
* `bernoulliDivergence_intensity_bound`
-/

@[expose] public section
noncomputable section
open Real Filter MeasureTheory Set
open scoped Nat ENNReal Topology

namespace PercLib.Probability

section Moments
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {χ : ℝ}

/-- Moment bounds `E X^m ≤ (2m-3)!! χ^{2m-1}` give the size-biased and plain exponential
moment bounds below the critical exponent. -/
@[tag "0BQB"]
theorem exponential_moments_of_moment_bounds [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1))) :
    (∀ r : ℝ, 0 ≤ r → r < (2 * χ ^ 2)⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (X ω * exp (r * X ω)) ∂P ≤
        ENNReal.ofReal (χ / sqrt (1 - 2 * r * χ ^ 2))) ∧
    (∀ r : ℝ, 0 ≤ r → r ≤ (2 * χ ^ 2)⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (exp (r * X ω)) ∂P ≤
        ENNReal.ofReal (1 + (1 - sqrt (1 - 2 * r * χ ^ 2)) / χ)) :=
  ⟨fun _ hr hr1 => lintegral_mul_exp_le hX hX0 hχ hmom hr hr1,
    fun _ hr hr1 => lintegral_exp_le hX hX0 hχ hmom hr hr1⟩

/-- Tail bounds from the same moment bounds: a bound valid for every `n > 0`, and a pure
exponential bound for `n ≥ 4χ² log(1 + χ⁻¹)`. -/
@[tag "SNB3"]
theorem tail_bounds_of_moment_bounds [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1))) :
    (∀ n : ℝ, 0 < n → P {ω | n ≤ X ω} ≤
      ENNReal.ofReal (min 1 (min (sqrt 2 * χ / n * exp (-(n / (4 * χ ^ 2))))
        ((1 + χ⁻¹) * exp (-(n / (2 * χ ^ 2))))))) ∧
    (∀ n : ℝ, 4 * χ ^ 2 * log (1 + χ⁻¹) ≤ n →
      P {ω | n ≤ X ω} ≤ ENNReal.ofReal (exp (-(n / (4 * χ ^ 2))))) :=
  ⟨fun _ hn => measure_le_le_min hX hX0 hχ hmom hn,
    fun _ hn => measure_le_le_exp hX hX0 hχ hmom hn⟩

end Moments

/-- The divergence between the Bernoulli laws with parameters `1 - e^{-β₁J}` and
`1 - e^{-β₂J}` is at most `J(β₁ log(β₁/β₂) - β₁ + β₂)`, which is at most
`J(β₁ - β₂)²/(2 min(β₁, β₂))`; at `J = 0` both sides vanish. -/
@[tag "KHB7"]
theorem bernoulliDivergence_intensity_bound {J β₁ β₂ : ℝ} (hJ : 0 ≤ J) (h₁ : 0 < β₁)
    (h₂ : 0 < β₂) :
    (1 - exp (-(β₁ * J))) * log ((1 - exp (-(β₁ * J))) / (1 - exp (-(β₂ * J)))) +
        (1 - (1 - exp (-(β₁ * J)))) *
          log ((1 - (1 - exp (-(β₁ * J)))) / (1 - (1 - exp (-(β₂ * J))))) ≤
      J * (β₁ * log (β₁ / β₂) - β₁ + β₂) ∧
    J * (β₁ * log (β₁ / β₂) - β₁ + β₂) ≤ J * (β₁ - β₂) ^ 2 / (2 * min β₁ β₂) :=
  ⟨bernoulliDivergence_exp_le_of_nonneg hJ h₁ h₂, mul_poissonDivergence_le hJ h₁ h₂⟩

end PercLib.Probability
