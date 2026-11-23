/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived hypotheses for cutoff moment derivatives, with no old-source code copied.
This supplies a uniform bound matching the `hroot` premise of the uncapped derivative interfaces:
at the concrete power law with β*M<1, every cutoff cluster moment up to order p+1 is bounded by
its uncut value at the same β. The bound is independent of radius and no criticality assertion
is made. No small-tail or uncapped-flux-continuity claim is included.
-/
module

public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Models.LongRange.CutoffPowerLawAnalytic

/-!
# Uniform moment bounds for the uncapped derivative interfaces

At a summable power-law profile and β*M<1, the uncut `(p+1)`-st root moment at the origin is a
finite uniform majorant for every positive-radius cutoff law at the same parameter. All moments
remain extended nonnegative real valued, and no ordinary real number is assigned to an infinite
cluster.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration
open PercLib.Analysis
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- A finite uniform bound for the power-law cutoff `(p+1)`-st root moment throughout the
corner/scale hypotheses of `hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment`.
Only the positive scales and `β M < 1` are used; selection of the actual corner-free interval and
of the remaining local-tail input is left to the derivative consumer. -/
theorem exists_powerLaw_root_succ_moment_bound {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (o : Fin d → ℤ) (p : ℕ) {u v R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      ∀ ρ ∈ (Ioo u v ∪ {R} : Set ℝ),
        (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂
          law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) ≤ M := by
  refine ⟨(∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂
    law (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α))) β)),
    BFS.power_lintegral_encard_cluster_pow_ne_top hd hα hβ o (p + 1), ?_⟩
  intro ρ hρ
  have hρpos : 0 < ρ := by
    rcases hρ with hρ | hρ
    · exact lt_trans hu hρ.1
    · simp only [Set.mem_singleton_iff] at hρ
      linarith [hu, hR]
  exact lintegral_cutoffKernel_encard_cluster_pow_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hρpos β o (p + 1)

end PercLib.Models.LongRange
