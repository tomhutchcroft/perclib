/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, Lemma I.4.1. Cap (bounded truncation) approximation of the power-law cut-off
cluster moments at the nondegenerate scale `r₀ = 5/2`, with a quantitative uniform-in-scale error
bound in the high-temperature region `β M < 1`. No derivative-level cap removal is claimed.
-/
module

public import PercLib.Models.LongRange.ExplicitHighTemperature
public import PercLib.Models.LongRange.HighTemperatureDerivative
public import PercLib.Probability.CapMoment

/-!
# Cap approximation of the power-law cut-off cluster moments

The capped `p`-th cluster moment at cut-off scale `ρ` is

`B ↦ ∫ ω, (((cluster ω o).encard ⊓ B : ℕ∞).toNat : ℝ) ^ p ∂law (cutoffProfile ρ)`.

This file instantiates the generic cap-approximation results of
`PercLib.Probability.CapMoment` for the sup-norm power law on `ℤ^d`:

* `tendsto_integral_capCluster_powerLaw`: at every positive cut-off scale, in the
  high-temperature region `β M < 1`, the capped moments converge as `B → ∞` to the honest real
  moment `(∫⁻ ω, |K_o(ω)| ^ p).toReal`. The `ℝ≥0∞` monotone convergence statement itself needs
  no high-temperature hypothesis and keeps infinite clusters as `⊤`.
* `exists_integral_capCluster_uniform_error_powerLaw`: a single finite `(p+1)`-st root moment
  bound `M` controls the cap error *uniformly* over the whole corner/scale window, with the
  explicit rate `(∫⁻ |K_o| ^ p).toReal - ∫ cap ^ p ≤ B⁻¹ M.toReal` for every `B ≥ 1`.
* `tendsto_integral_capCluster_powerLaw_five_halves`,
  `exists_integral_capCluster_uniform_error_powerLaw_five_halves`: the same statements at the
  nondegenerate scale `r₀ = 5/2`, where production already has the *capped* derivative
  (`hasDerivAt_integral_cutoff_powerLaw_d2_capped_five_halves`), and on the interval
  `(2, 3) ∪ {3}` containing it.
* `exists_integral_capCluster_uniform_error_d2_beta_one_hundredth`: the fully explicit
  dimension-two witness `d = 2`, `α = 1`, `β = 1/100`, with no remaining hypotheses.

What is *not* claimed: the cap error bound is a bound on the *values* of the moment map. It does
not differentiate, and in particular it does not show that the derivative of the capped moment
converges to the derivative of the uncapped moment. That derivative-level cap removal is exactly
where the local small-tail estimate (`htail` of
`hasDerivAt_powerLaw_three_halves_of_root_moment_of_small_tail`, respectively the `hfac`-type
factorization behind it) is still needed: the value-level estimate gives no control on the pivotal
flux, which is the quantity that must be summed uniformly in `B`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### The high-temperature region and the cut-off law -/

/-! ### Pointwise-in-scale cap approximation -/

/-- **Unconditional cap convergence of the power-law cluster moments.** At every positive cut-off
scale and for every `β ≥ 0`, the capped `p`-th cluster moments increase to the full extended
`p`-th moment in `ℝ≥0∞`. No positivity, finiteness or high-temperature hypothesis is used here,
and an infinite cluster (`⊤`) is preserved in the limit rather than truncated to `0`. -/
theorem iSup_lintegral_capCluster_powerLaw {α : ℝ} (β : ℝ≥0) (o : Fin d → ℤ) (p : ℕ)
    (ρ : ℝ) :
    (⨆ B : ℕ, ∫⁻ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) ρ) β) :=
  PercLib.Probability.iSup_lintegral_capToNat_pow _ (measurable_encard_cluster o) p

/-- **Cap approximation of the power-law cluster moment at a fixed positive scale.** In the
high-temperature region `β M < 1`, at every cut-off scale `ρ > 0` the real capped `p`-th moments
converge, as the cap `B → ∞`, to the honest real moment of the (possibly infinite) cluster size.
The latter is finite here, so `toReal` is legitimate. -/
theorem tendsto_integral_capCluster_powerLaw {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun B : ℕ => ∫ ω,
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) atTop
      (𝓝 ((∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)).toReal)) :=
  PercLib.Probability.tendsto_integral_capToNat_pow _
    (measurable_encard_cluster o) p
    (lintegral_cutoffKernel_powerLaw_pow_ne_top hd hα hβ hρ o p)

/-- **Cap approximation at the nondegenerate scale `r₀ = 5/2`.** `5/2` is not a value of the
sup norm on `ℤ^d`, so this is the scale at which production has a non-trivial capped derivative
(`hasDerivAt_integral_cutoff_powerLaw_d2_capped_five_halves`); here the value-level cap limit at
the same scale is unconditional apart from `β M < 1` and `α > 0`. -/
theorem tendsto_integral_capCluster_powerLaw_five_halves {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    Tendsto (fun B : ℕ => ∫ ω,
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (5 / 2)) β)) atTop
      (𝓝 ((∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) (5 / 2)) β)).toReal)) :=
  tendsto_integral_capCluster_powerLaw hd hα hβ o p (by norm_num)

/-! ### The quantitative uniform-in-scale error bound -/

/-- **Uniform-in-scale cap error bound, high temperature.** There is a single finite
`(p+1)`-st root moment bound `M`, uniform over the corner/scale window `Ioo u v ∪ {R}`, such that
for every scale in that window and every cap `B ≥ 1` the cap error of the `p`-th moment is at most
`B⁻¹ M.toReal`. This is the value-level quantitative form of cap approximation; it is exactly
`capMoment_error_le` with the higher moment estimated by the production uniform root moment bound
`exists_powerLaw_root_succ_moment_bound`. -/
theorem exists_integral_capCluster_uniform_error_powerLaw {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) {u v R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ ρ ∈ (Ioo u v ∪ {R} : Set ℝ), ∀ B : ℕ, 1 ≤ B →
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)).toReal -
        ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)
        ≤ (B : ℝ)⁻¹ * M.toReal := by
  obtain ⟨M, hM, hroot⟩ :=
    exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ o p hu hR
  refine ⟨M, hM, fun ρ hρ B hB => ?_⟩
  have hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1)
      ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) ≠ ⊤ :=
    ne_top_of_le_ne_top hM (hroot ρ hρ)
  refine (PercLib.Probability.capMoment_error_le _ (measurable_encard_cluster o) p hB hfin).trans ?_
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hM (hroot ρ hρ)) (by positivity)

/-- **Uniform-in-scale cap error bound near `r₀ = 5/2`.** The window `(2, 3) ∪ {3}` contains the
nondegenerate scale `5/2`; on it the cap error of every `p`-th cluster moment is `O(1/B)` with a
single constant. -/
theorem exists_integral_capCluster_uniform_error_powerLaw_five_halves {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ ρ ∈ (Ioo (2 : ℝ) 3 ∪ {3} : Set ℝ), ∀ B : ℕ, 1 ≤ B →
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)).toReal -
        ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)
        ≤ (B : ℝ)⁻¹ * M.toReal :=
  exists_integral_capCluster_uniform_error_powerLaw hd hα hβ o p (by norm_num) (by norm_num)
    (u := 2) (v := 3) (R := 3)

/-- **Uniform cap error bound on the window of the `r₀ = 3/2` derivative.** On the exact
corner-free window `(5/4, 8/5) ∪ {8/5}` consumed by the `hroot` premise of
`hasDerivAt_powerLaw_three_halves_of_root_moment_of_small_tail`, the cap error of every `p`-th
cluster moment is `O(1/B)` with the same uniform constant that dominates the `(p+1)`-st moment.
This is the value-level half of cap removal at the scale where production has the uncapped
derivative; the derivative-level half is not claimed. -/
theorem exists_integral_capCluster_uniform_error_powerLaw_three_halves {α : ℝ} (hd : 1 ≤ d)
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ ρ ∈ (Ioo (5 / 4 : ℝ) (8 / 5) ∪ {8 / 5} : Set ℝ), ∀ B : ℕ, 1 ≤ B →
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)).toReal -
        ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)
        ≤ (B : ℝ)⁻¹ * M.toReal :=
  exists_integral_capCluster_uniform_error_powerLaw hd hα hβ o p (by norm_num) (by norm_num)
    (u := 5 / 4) (v := 8 / 5) (R := 8 / 5)

/-! ### The explicit dimension-two witness -/

/-- **Fully explicit quantitative cap approximation in dimension two.** At `d = 2`, `α = 1`,
`β = 1/100` every hypothesis is discharged: there is a finite `M` such that on the window
`(2, 3) ∪ {3}`, which contains `r₀ = 5/2`, the cap error of the `p`-th cluster moment is at most
`B⁻¹ M.toReal` for all `B ≥ 1`. -/
theorem exists_integral_capCluster_uniform_error_d2_beta_one_hundredth
    (o : Fin 2 → ℤ) (p : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ ρ ∈ (Ioo (2 : ℝ) 3 ∪ {3} : Set ℝ), ∀ B : ℕ, 1 ≤ B →
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
            (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) ρ) (1 / 100))).toReal -
        ∫ ω, (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
          ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
            (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) ρ) (1 / 100))
        ≤ (B : ℝ)⁻¹ * M.toReal :=
  exists_integral_capCluster_uniform_error_powerLaw (d := 2) (by norm_num) (α := 1) one_pos
    d2_beta_rowSum_lt_one o p (by norm_num) (by norm_num) (u := 2) (v := 3) (R := 3)

/-- **Fully explicit cap approximation at `r₀ = 5/2`, `d = 2`, `α = 1`, `β = 1/100`.** This is
the value-level counterpart at the scale of the production capped derivative
`hasDerivAt_integral_cutoff_powerLaw_d2_capped_five_halves`. -/
theorem tendsto_integral_capCluster_d2_beta_one_hundredth_five_halves
    (o : Fin 2 → ℤ) (p : ℕ) :
    Tendsto (fun B : ℕ => ∫ ω,
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
          (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) (5 / 2)) (1 / 100))) atTop
      (𝓝 ((∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin 2 → ℝ))
          (powerLawProfile 1 (((2 : ℕ) : ℝ) + 1)) (5 / 2)) (1 / 100))).toReal)) :=
  tendsto_integral_capCluster_powerLaw_five_halves (d := 2) (by norm_num) (α := 1) one_pos
    d2_beta_rowSum_lt_one o p

end PercLib.Models.LongRange
