/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Adapted from the uncommitted, project-generated PercLib candidates `M1/Defs.lean` and
`M1/Main.lean`, under the same Apache 2.0 licence. The duplicate `rootMoment` and
`rootMomentReal` definitions from that candidate are not retained: the statements below use
`PercLib.Percolation.Bond.rootMoment` directly.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 and the proof of Lemma I.4.1. The latter is used here only for the one-sided
high-temperature treatment, not a two-sided claim at lattice corners.
-/
module

public import PercLib.Models.LongRange.CornerCoupling.Defs
public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Models.LongRange.HighTemperatureDerivative
public import PercLib.Percolation.Bond.RestorationWindow.Defs

/-!
# The softened-change factor and canonical cutoff root-moment properties

`chiFactor` is the non-radius-dependent coefficient of the softened-change term. It is the
number `(2n+1)^d` of sup-norm lattice points in the ball of radius `n`, multiplied by the real
susceptibility at radius `n`. The root moments themselves use
`PercLib.Percolation.Bond.rootMoment`, at the actual infinite-lattice cutoff law, rather than a
second meaning-preserving alias for the same integral.

This file also records the monotonicity of that canonical root moment in the cutoff scale and
power, and the power-law uniform higher-moment bound used for right-continuity at a corner.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open PercLib.Models.LongRange
open scoped ENNReal NNReal unitInterval Topology

namespace PercLib.Models.LongRange.CornerMoment

variable {d : ℕ}

/-- The real change-probability factor of the softened union coupling: the number `(2n+1)^d` of
lattice points of the sup-norm ball of radius `n` times the real susceptibility at scale `n`. -/
noncomputable def chiFactor (β : ℝ≥0) (K : ℝ → ℝ) (n : ℕ) (o : Fin d → ℤ) : ℝ :=
  (((2 * n + 1) ^ d : ℕ) : ℝ) *
    (chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o).toReal

theorem chiFactor_def (β : ℝ≥0) (K : ℝ → ℝ) (n : ℕ) (o : Fin d → ℤ) :
    chiFactor (d := d) β K n o = (((2 * n + 1) ^ d : ℕ) : ℝ) *
      (chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o).toReal :=
  rfl

theorem chiFactor_nonneg (β : ℝ≥0) (K : ℝ → ℝ) (n : ℕ) (o : Fin d → ℤ) :
    0 ≤ chiFactor (d := d) β K n o :=
  mul_nonneg (by positivity) ENNReal.toReal_nonneg

/-- The canonical root moment increases with the cutoff scale for an antitone profile. -/
theorem rootMoment_mono_radius {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {r ρ : ℝ}
    (hrρ : r ≤ ρ) (o : Fin d → ℤ) (p : ℕ) :
    PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o p ≤
    PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K ρ) β)) o p := by
  have h := lintegral_cutoffKernel_mono (N := supModelNorm d) (β := β) hK hrρ
    (φ := fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) ^ p)
    ((measurable_encard_cluster_toENNReal o).pow_const p) ?_
  · exact h
  · intro ω ω' hω
    exact pow_le_pow_left' (ENat.toENNReal_mono (Set.encard_mono (cluster_mono hω o))) p

/-- The canonical root moment increases with the power. -/
theorem rootMoment_mono_pow {K : ℝ → ℝ} {β : ℝ≥0} (o : Fin d → ℤ) {k l : ℕ} (hkl : k ≤ l)
    (r : ℝ) :
    PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o k ≤
    PercLib.Percolation.Bond.rootMoment
      (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) o l := by
  refine lintegral_mono fun ω => ?_
  exact pow_le_pow_right'
    (by simpa using ENat.toENNReal_mono (one_le_encard_cluster ω o)) hkl

/-- The published uniform `(p+1)`-st root-moment bound, written with the canonical bond
root moment and the cutoff law. -/
theorem exists_uniform_rootMoment_bound {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    (o : Fin d → ℤ) (p : ℕ) {u v R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ r, r ∈ (Ioo u v ∪ {R} : Set ℝ) →
      PercLib.Percolation.Bond.rootMoment
        (law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) o (p + 1) ≤ M := by
  obtain ⟨M, hM, hb⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα hβ o p hu hR
  refine ⟨M, hM, fun r hr => ?_⟩
  simpa only [PercLib.Percolation.Bond.rootMoment,
    PercLib.Analysis.ModelNorm.toSeminorm_ofNorm] using hb r hr

end PercLib.Models.LongRange.CornerMoment
