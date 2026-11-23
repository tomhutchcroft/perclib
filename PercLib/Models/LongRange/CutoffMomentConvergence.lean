/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical model: the radial cut-off and uncut long-range percolation laws on `ℤ^d`.
No assertion at criticality, no sharpness theorem, and no derivative formula is claimed.
-/
module

public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Models.LongRange.TwoPointCutoffConvergence
public import PercLib.Percolation.Bond.MomentConvergence

/-!
# Convergence of cut-off cluster moments

For nonnegative decreasing profiles tending to zero, every natural moment of the infinite-lattice
rooted cluster at cut-off radius `r` converges to the uncut moment. At the concrete power law and
in the high-temperature region `β M < 1`, this also yields convergence after `ENNReal.toReal`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PercLib.Probability
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis
open PercLib.Percolation.Bond

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ}

/-- **Convergence of every natural cut-off cluster moment to the uncut moment.** -/
theorem tendsto_lintegral_cutoffKernel_encard_cluster_pow
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hKanti : AntitoneOn K (Ioi 0)) (hK : Tendsto K atTop (𝓝 0))
    (β : ℝ≥0) (o : Fin d → ℤ) (p : ℕ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel N.toSeminorm K r) β)) atTop
      (𝓝 (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (radialKernel N.toSeminorm K) β))) := by
  refine PercLib.Percolation.Bond.tendsto_lintegral_encard_cluster_pow_of_tendsto_profile
    (q := fun r => intensityProfile (cutoffKernel N.toSeminorm K r) β)
    (qinf := intensityProfile (radialKernel N.toSeminorm K) β) ?_ ?_ ?_ o p
  · exact fun r ρ hrρ =>
      intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKanti e hrρ) β
  · intro r
    rcases le_or_gt r 1 with hr | hr
    · exact (intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKanti e hr) β).trans
        (intensityProfile_le_of_le
          (fun e => cutoffKernel_le_radialKernel hKnn one_pos e) β)
    · exact intensityProfile_le_of_le
        (fun e => cutoffKernel_le_radialKernel hKnn (one_pos.trans hr) e) β
  · exact fun e => PercLib.Percolation.Bond.tendsto_intensityProfile_cutoffKernel hK β e

/-- **Concrete power law: natural cut-off moments converge to the uncut moment.** -/
theorem tendsto_lintegral_cutoffKernel_powerLaw_pow {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (β : ℝ≥0) (o : Fin d → ℤ) (p : ℕ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law
        (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile c ((d : ℝ) + α)) r) β)) atTop
      (𝓝 (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law
        (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile c ((d : ℝ) + α))) β))) :=
  tendsto_lintegral_cutoffKernel_encard_cluster_pow
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun t ht => mul_nonneg hc (Real.rpow_nonneg ht.le _))
    (PercLib.Models.LongRange.antitoneOn_powerLawProfile hc (by positivity))
    (PercLib.Models.LongRange.tendsto_powerLawProfile_atTop (by positivity)) β o p

/-- **Monotone convergence in the cluster volume along the cut-off scale.**  The supremum of the
cut-off moments over the scale is the uncut moment. -/
theorem iSup_lintegral_cutoffKernel_encard_cluster_pow_eq
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hKanti : AntitoneOn K (Ioi 0)) (hK : Tendsto K atTop (𝓝 0))
    (β : ℝ≥0) (o : Fin d → ℤ) (p : ℕ) :
    (⨆ r : ℝ, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (cutoffKernel N.toSeminorm K r) β)) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂law (intensityProfile (radialKernel N.toSeminorm K) β) := by
  refine PercLib.Percolation.Bond.iSup_lintegral_encard_cluster_pow_eq_of_tendsto_profile
    (q := fun r => intensityProfile (cutoffKernel N.toSeminorm K r) β)
    (qinf := intensityProfile (radialKernel N.toSeminorm K) β) ?_ ?_ ?_ o p
  · exact fun r ρ hrρ =>
      intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKanti e hrρ) β
  · intro r
    rcases le_or_gt r 1 with hr | hr
    · exact (intensityProfile_le_of_le (fun e => monotone_cutoffKernel hKanti e hr) β).trans
        (intensityProfile_le_of_le
          (fun e => cutoffKernel_le_radialKernel hKnn one_pos e) β)
    · exact intensityProfile_le_of_le
        (fun e => cutoffKernel_le_radialKernel hKnn (one_pos.trans hr) e) β
  · exact fun e => PercLib.Percolation.Bond.tendsto_intensityProfile_cutoffKernel hK β e

/-- **Real-valued high-temperature form at the concrete power law.**  In the region `β M < 1` the
uncut `p`-th moment is finite, so the convergence of the cut-off moments is a convergence of
ordinary nonnegative real numbers. -/
theorem tendsto_lintegral_cutoffKernel_powerLaw_pow_toReal {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) :
    Tendsto (fun r : ℝ => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law
        (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)).toReal) atTop
      (𝓝 ((∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law
        (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α))) β)).toReal)) :=
  (ENNReal.tendsto_toReal
      (PercLib.Percolation.Bond.Exploration.BFS.power_lintegral_encard_cluster_pow_ne_top
        hd hα hβ o p)).comp
    (tendsto_lintegral_cutoffKernel_powerLaw_pow (d := d) hα zero_le_one β o p)

end PercLib.Models.LongRange
