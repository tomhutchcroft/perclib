/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Concrete power-law instantiation of the single-pair uncapped pivotal continuity interfaces.
New proofs; no old-source code is copied and no definition is added.
-/
module

public import PercLib.Models.LongRange.CutoffPowerLawAnalytic
public import PercLib.Models.LongRange.InfiniteVolumeRusso
public import PercLib.Models.LongRange.TruncatedMoments
public import PercLib.Models.LongRange.HighTemperatureDerivative

/-!
# Power-law continuity of one inserted pivotal moment

The recovered interfaces `continuousOn_pivotal_cutoff_uncapped_of_root_succ_moment` and
`continuousOn_cutoff_weight_mul_pivotal_uncapped_of_root_succ_moment` take an abstract profile
`K`, an abstract derivative `K'` and an abstract uniform root moment bound `M`. This file removes
those abstract inputs at the concrete profile `powerLawProfile 1 (d + α)`:

* the profile is antitone on `(0, ∞)`;
* its derivative `t ↦ 1 * (-(d + α) * t ^ (-(d + α) - 1))` exists and is continuous on `(0, ∞)`;
* the uniform `(p + 1)`-st root moment bound is `exists_powerLaw_root_succ_moment_bound`, valid at
  every positive scale of the window and at the outer scale `R`, at high temperature `β M < 1`.

What is *not* proved here: absolute summability of the pair series over `e`, the small-tail
estimate, and the derivative formula of the cutoff moment itself. Those remain inputs of
`continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail` and
`hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_local_tail`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-- **Single-pair uncapped pivotal continuity at the concrete power law.** With `1 ≤ d`, `0 < α`
and the high-temperature hypothesis `β M < 1` of the summability region, the inserted pivotal
moment of one pair is continuous in the cutoff radius on every window `(u, R)` of positive radii.
No norm-corner hypothesis is needed for this unweighted statement. -/
theorem continuousOn_pivotal_cutoff_uncapped_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {u R : ℝ} (hu : 0 < u) (huR : u < R)
    (e : Sym2 (Fin d → ℤ)) :
    ContinuousOn (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u R) := by
  obtain ⟨M, hM, hroot⟩ :=
    exists_powerLaw_root_succ_moment_bound hd hα hβ 0 p hu (lt_trans hu huR)
  exact continuousOn_pivotal_cutoff_uncapped_of_root_succ_moment
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by
      have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith))
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add (d := d) 1 α)
    β p hp o hu e M hM hroot

/-- **The derivative weight of one pair at the concrete power law.** This is
`(radialKernel 1{s < r} e) * β (-K') exp (-β K_r(e))` with `K = powerLawProfile 1 (d + α)`, the
single summand of the flux in `hasDerivAt_integral_cutoff_pow_binomial`; the derivative factor is
written out as `(d + α) r ^ (-(d + α) - 1)`, which is `-K'(r)`. -/
theorem continuousOn_cutoff_weight_mul_pivotal_uncapped_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {u v R : ℝ} (hu : 0 < u) (huv : u < v) (hvR : v ≤ R)
    (hI : ∀ z : Fin d → ℤ,
      (normSeminorm ℝ (Fin d → ℝ)) (Int.cast ∘ z) ∉ Ioo u v)
    (e : Sym2 (Fin d → ℤ)) :
    ContinuousOn (fun r =>
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v) := by
  have hcoef : ∀ r : ℝ, -(1 * (-((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1))) =
      ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := fun r => by ring
  obtain ⟨M, hM, hroot⟩ :=
    exists_powerLaw_root_succ_moment_bound hd hα hβ 0 p hu (lt_of_lt_of_le (lt_trans hu huv) hvR)
  refine (continuousOn_cutoff_weight_mul_pivotal_uncapped_of_root_succ_moment
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by
      have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith))
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add (d := d) 1 α)
    β p hp o hu hvR hI e M hM hroot).congr ?_
  intro r _
  simp only [hcoef r, ModelNorm.toSeminorm_ofNorm]

/-- **The right-hand limit of one inserted pivotal moment at the concrete power law.** At a scale
`n` that lies inside a window `(u, R)` of positive radii, the pair's pivotal moment converges from
the right to its value at `n`; no norm-corner hypothesis is needed. This is the per-pair
convergence input `hPiv` of
`tendsto_tsum_cutoff_pivotal_flux_nhdsGT_of_root_succ_moment`, discharged at the power law. -/
theorem tendsto_pivotal_cutoff_uncapped_powerLaw_nhdsGT {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {u R n : ℝ} (hu : 0 < u) (hun : u < n) (hnR : n < R)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (𝓝[>] n)
      (𝓝 (∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) n) β)))) := by
  obtain ⟨M, hM, hroot⟩ :=
    exists_powerLaw_root_succ_moment_bound hd hα hβ 0 p hu (lt_trans (lt_trans hu hun) hnR)
  exact continuousAt_pivotal_cutoff_uncapped_of_root_succ_moment
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by
      have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith))
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add (d := d) 1 α)
    β p hp o hu hun hnR M hM hroot e

/-- **A corner-free window can be read off from the integers.** Since every value of the sup norm
on `ℤ^d` is a natural number, an interval containing no natural number contains no norm corner;
this discharges the corner-freeness hypothesis of the weighted statement from an arithmetic
condition on the window. -/
theorem corner_free_of_forall_nat_notMem {d : ℕ} {u v : ℝ} (h : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) :
    ∀ z : Fin d → ℤ, (normSeminorm ℝ (Fin d → ℝ)) (Int.cast ∘ z) ∉ Ioo u v := by
  intro z
  obtain ⟨n, hn⟩ := exists_nat_eq_norm z
  rw [normSeminorm_intCast, hn]
  exact h n

/-- **Weighted pair continuity at the concrete power law on an arithmetically corner-free
window**, the usable form of `continuousOn_cutoff_weight_mul_pivotal_uncapped_powerLaw`: the
corner-freeness hypothesis is discharged by excluding natural numbers from `(u, v)`. -/
theorem continuousOn_cutoff_weight_mul_pivotal_uncapped_powerLaw_of_nat {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {u v R : ℝ} (hu : 0 < u) (huv : u < v) (hvR : v ≤ R)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (e : Sym2 (Fin d → ℤ)) :
    ContinuousOn (fun r =>
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v) :=
  continuousOn_cutoff_weight_mul_pivotal_uncapped_powerLaw hd hα hβ p hp o hu huv hvR
    (corner_free_of_forall_nat_notMem (d := d) hI) e

/-- **Two-sided continuity of one weighted pivotality at a corner-free scale.** At a scale `r₀` in
`(0, R)` that is not the norm of a lattice point, a corner-free neighbourhood of `r₀` exists and the
weighted single-pair summand
`r ↦ (radial weight) * β (-K'(r)) exp (-β K_r(e)) * pivotal_r(e)` is continuous there in the
ordinary two-sided topology. This is the one-scale regularity the pair series is assembled from; it
does not assert that the series over `e` is summable or continuous. -/
theorem continuousAt_cutoff_weight_mul_pivotal_uncapped_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {r₀ R : ℝ} (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (hcorner : ∀ z : Fin d → ℤ, (normSeminorm ℝ (Fin d → ℝ)) (Int.cast ∘ z) ≠ r₀)
    (e : Sym2 (Fin d → ℤ)) :
    ContinuousAt (fun r =>
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) r₀ := by
  obtain ⟨δ, hδ, hu, hvR, hI⟩ :=
    exists_corner_free (N := ModelNorm.ofNorm (Fin d → ℝ)) hr₀ hr₀R hcorner
  exact (continuousOn_cutoff_weight_mul_pivotal_uncapped_powerLaw hd hα hβ p hp o hu
      (by linarith) hvR hI e).continuousAt
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)

/-- **Two-sided continuity of one unweighted pivotality at an arbitrary scale of the power law.**
No norm-corner hypothesis appears: the cutoff kernel itself is continuous in the scale, and the
corner isolated in `PercLib.Models.LongRange.hasDerivAt_cutoffProfile` (module `CutoffCorner`) is a
corner of the *derivative* in the scale, not of the value.
The corner-free hypothesis in `continuousAt_cutoff_weight_mul_pivotal_uncapped_powerLaw` is needed
only for the radial indicator weight `1{s < r}`. -/
theorem continuousAt_pivotal_cutoff_uncapped_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {r₀ R : ℝ} (hr₀ : 0 < r₀) (hr₀R : r₀ < R)
    (e : Sym2 (Fin d → ℤ)) :
    ContinuousAt (fun r => ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) r₀ := by
  exact (continuousOn_pivotal_cutoff_uncapped_powerLaw hd hα hβ p hp o
      (by linarith : (0 : ℝ) < r₀ / 2) (by linarith : r₀ / 2 < R) e).continuousAt
    (isOpen_Ioo.mem_nhds ⟨by linarith, hr₀R⟩)

end PercLib.Models.LongRange
