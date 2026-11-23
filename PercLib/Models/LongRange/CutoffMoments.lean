/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the canonical bond interface; no old-source code is copied. The source results
`PowerLawHighTemp/Moments.lean` implies for the paper's law are recovered here for the
production radial cutoff and `law (intensityProfile _ β)`, using
`lintegral_prodBernoulli_mono` for the central domination step.
This is a proof-only composition module, with no definition and no critical
parameter, limit, or sharpness claim.
-/
module

public import PercLib.Percolation.Bond.MomentTransport
public import PercLib.Percolation.Bond.Exploration.BFS.IntensityRpowMoments
public import PercLib.Models.LongRange.Defs

/-!
# Equal-parameter cutoff cluster moments

A nonnegative profile has `cutoffProfile K r ≤ K` for every positive `r`, so stochastic
monotonicity gives every natural or real cluster moment of the cutoff at the same parameter as an
upper bound for that of the uncut law. Finiteness transfers in the same direction. At the concrete
power-law profile this yields all natural and all nonnegative real moments of the cutoff law in
the explicit high-temperature region `β M < 1`, at every positive scale and every root.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Analysis
open PercLib.Percolation.Bond.Exploration
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ} {r : ℝ}

/-- At the same parameter, every natural cluster moment of the cutoff is bounded by that of the
uncut law. Both integrals are extended and may be infinite. -/
theorem lintegral_cutoffKernel_encard_cluster_pow_le (hK : ∀ t, 0 < t → 0 ≤ K t)
    (hr : 0 < r) (β : ℝ≥0) (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile (cutoffKernel N K r) β)) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile (radialKernel N K) β) :=
  lintegral_encard_cluster_pow_mono_intensity
    (fun e => cutoffKernel_le_radialKernel hK hr e) β o k

/-- Finiteness of an uncut natural moment transfers to every cutoff radius. -/
theorem lintegral_cutoffKernel_encard_cluster_pow_ne_top_of_le
    (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r) (β : ℝ≥0) (o : Fin d → ℤ) (k : ℕ)
    (hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law
        (intensityProfile (radialKernel N K) β)) ≠ ⊤) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile (cutoffKernel N K r) β)) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (lintegral_cutoffKernel_encard_cluster_pow_le hK hr β o k)

/-- At the same parameter, every real cluster moment of nonnegative order of the cutoff is
bounded by that of the uncut law. -/
theorem lintegral_cutoffKernel_encard_cluster_rpow_le (hK : ∀ t, 0 < t → 0 ≤ K t)
    (hr : 0 < r) (β : ℝ≥0) (o : Fin d → ℤ) {q : ℝ} (hq : 0 ≤ q) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂law (intensityProfile (cutoffKernel N K r) β)) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂law (intensityProfile (radialKernel N K) β) :=
  lintegral_encard_cluster_rpow_mono (intensityProfile_le_of_le
    (fun e => cutoffKernel_le_radialKernel hK hr e) β) o hq

/-- Finiteness of an uncut real cluster moment transfers to every cutoff radius. -/
theorem lintegral_cutoffKernel_encard_cluster_rpow_ne_top_of_le
    (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r) (β : ℝ≥0) (o : Fin d → ℤ)
    {q : ℝ} (hq : 0 ≤ q)
    (hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂law
        (intensityProfile (radialKernel N K) β)) ≠ ⊤) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂law (intensityProfile (cutoffKernel N K r) β)) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (lintegral_cutoffKernel_encard_cluster_rpow_le hK hr β o hq)

/-- All natural cluster moments of the concrete power-law cutoff are finite at high temperature,
at every root and every positive scale, with no reduced parameter. -/
theorem lintegral_cutoffKernel_powerLaw_pow_ne_top (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hr : 0 < r) (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law
          (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ :=
  lintegral_cutoffKernel_encard_cluster_pow_ne_top_of_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hr β o k
    (BFS.power_lintegral_encard_cluster_pow_ne_top hd hα hβ o k)

/-- Simultaneous all-radius, all-root form of the power-law cutoff moments. -/
theorem forall_lintegral_cutoffKernel_powerLaw_pow_ne_top (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) :
    ∀ (r : ℝ), 0 < r → ∀ (o : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law
          (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ :=
  fun r hr o k => lintegral_cutoffKernel_powerLaw_pow_ne_top hd hα hβ (r := r) hr o k

/-- Every nonnegative real moment of the concrete power-law cutoff is finite at high temperature,
at every root and every positive scale. -/
theorem lintegral_cutoffKernel_powerLaw_rpow_ne_top (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (hr : 0 < r) (o : Fin d → ℤ) {q : ℝ} (hq : 0 ≤ q) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂law
          (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ :=
  lintegral_cutoffKernel_encard_cluster_rpow_ne_top_of_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hr β o hq
    (BFS.power_lintegral_encard_cluster_rpow_ne_top hd hα hβ o hq)

/-- A positive interval on which every natural cutoff moment is finite at every positive radius
and every root. -/
theorem exists_beta_interval_cutoffKernel_powerLaw_pow_ne_top (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (r : ℝ), 0 < r → ∀ (o : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law
          (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ := by
  obtain ⟨β₀, hβ₀, hfin⟩ := BFS.exists_beta_interval_powerLaw_encard_cluster_pow_ne_top hd hα
  exact ⟨β₀, hβ₀, fun β hβ r hr o k =>
    lintegral_cutoffKernel_encard_cluster_pow_ne_top_of_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hr β o k
    (hfin β hβ o k)⟩

/-- A positive interval on which every nonnegative real cutoff moment is finite at every positive
radius and every root. -/
theorem exists_beta_interval_cutoffKernel_powerLaw_rpow_ne_top (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (r : ℝ), 0 < r →
      ∀ (o : Fin d → ℤ) (q : ℝ), 0 ≤ q →
        (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ q ∂law
          (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≠ ⊤ := by
  obtain ⟨β₀, hβ₀, hfin⟩ := BFS.exists_beta_interval_powerLaw_encard_cluster_rpow_ne_top hd hα
  exact ⟨β₀, hβ₀, fun β hβ r hr o q hq =>
    lintegral_cutoffKernel_encard_cluster_rpow_ne_top_of_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hr β o hq
    (hfin β hβ o q hq)⟩

end PercLib.Models.LongRange
