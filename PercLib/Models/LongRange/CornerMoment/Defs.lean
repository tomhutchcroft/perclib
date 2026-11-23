/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/

module

public import PercLib.Models.LongRange.CornerContinuity
public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Models.LongRange.HighTemperatureDerivative

/-!
# The actual infinite-lattice cutoff root moment: definition and monotonicities

`rootMoment β K o p r` is the uncapped `p`-th moment of the cluster volume of the lattice
vertex `o` under the bond-percolation law at cut-off scale `r`, written in extended nonnegative
reals; `rootMomentReal` is its `toReal` value. Both are the *actual* infinite-lattice objects of
`PercLib.Percolation.Bond` (`law`, `cluster`), not a finite-torus substitute.

The file records the two monotonicities used in the integer-radius right-continuity argument:
the moment increases with the cut-off scale (for a profile antitone on `(0,∞)`) and with the
power. It also restates the published uniform `(p+1)`-st moment bound in terms of `rootMoment`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open PercLib.Models.LongRange
open scoped ENNReal NNReal unitInterval Topology

namespace PercLib.Models.LongRange.CornerMoment

variable {d : ℕ}

/-- The uncapped `p`-th cutoff cluster moment of the vertex `o` at cut-off scale `r`, as an
extended nonnegative real. -/
noncomputable def rootMoment (β : ℝ≥0) (K : ℝ → ℝ) (o : Fin d → ℤ) (p : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂
    law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)

/-- The real-valued, uncapped cutoff root moment. -/
noncomputable def rootMomentReal (β : ℝ≥0) (K : ℝ → ℝ) (o : Fin d → ℤ) (p : ℕ)
    (r : ℝ) : ℝ :=
  (rootMoment (d := d) β K o p r).toReal

theorem rootMoment_def (β : ℝ≥0) (K : ℝ → ℝ) (o : Fin d → ℤ) (p : ℕ) (r : ℝ) :
    rootMoment (d := d) β K o p r =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile
          (cutoffKernel (supModelNorm d).toSeminorm K r) β) := rfl

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

/-- A cluster contains its base vertex, so its volume is at least one, also in `ℝ≥0∞`. -/
theorem one_le_encard_cluster_toENNReal (ω : Config (Fin d → ℤ)) (o : Fin d → ℤ) :
    1 ≤ ((cluster ω o).encard : ℝ≥0∞) := by
  simpa using ENat.toENNReal_mono (one_le_encard_cluster ω o)

/-- **The root moment increases with the cut-off scale**, for a profile antitone on `(0,∞)`. -/
theorem rootMoment_mono_radius {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {r ρ : ℝ}
    (hrρ : r ≤ ρ) (o : Fin d → ℤ) (p : ℕ) :
    rootMoment (d := d) β K o p r ≤ rootMoment (d := d) β K o p ρ := by
  have h := lintegral_cutoffKernel_mono (N := supModelNorm d) (β := β) hK hrρ
    (φ := fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) ^ p)
    ((measurable_encard_cluster_toENNReal o).pow_const p) ?_
  · simpa only [rootMoment] using h
  · intro ω ω' hω
    exact pow_le_pow_left' (ENat.toENNReal_mono (Set.encard_mono (cluster_mono hω o))) p

/-- **The root moment increases with the power.** -/
theorem rootMoment_mono_pow {K : ℝ → ℝ} {β : ℝ≥0} (o : Fin d → ℤ) {k l : ℕ} (hkl : k ≤ l)
    (r : ℝ) : rootMoment (d := d) β K o k r ≤ rootMoment (d := d) β K o l r := by
  refine lintegral_mono fun ω => ?_
  exact pow_le_pow_right' (by simpa using one_le_encard_cluster_toENNReal ω o) hkl

/-- The published uniform `(p+1)`-st root-moment bound, in terms of `rootMoment`: on every
positive scale of `Ioo u v ∪ {R}` the power-law cutoff `(p+1)`-st moment is dominated by a
single finite constant. -/
theorem exists_uniform_rootMoment_bound {α : ℝ} (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ↑(Real.toNNReal (∑' (z : Fin d → ℤ), (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) < 1)
    (o : Fin d → ℤ) (p : ℕ) {u v R : ℝ} (hu : 0 < u) (hR : 0 < R) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ r, r ∈ (Ioo u v ∪ {R} : Set ℝ) →
      rootMoment (d := d) β (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α)) o (p + 1)
        r ≤ M := by
  obtain ⟨M, hM, hb⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα hβ o p hu hR
  refine ⟨M, hM, fun r hr => ?_⟩
  simpa only [rootMoment, PercLib.Analysis.ModelNorm.toSeminorm_ofNorm] using hb r hr

end PercLib.Models.LongRange.CornerMoment
