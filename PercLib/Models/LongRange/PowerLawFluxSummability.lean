/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1,
for the cut-off derivative consumer. No old proof text is migrated here.
-/
module

public import PercLib.Models.LongRange.HighTemperatureDerivative
public import PercLib.Models.LongRange.CutoffExhaustion.Moments
public import PercLib.Models.LongRange.PowerLawPivotalContinuity
public import PercLib.Models.LongRange.TruncatedMoments

/-!
# Summability of the power-law weighted pivotal flux

At `K s = s ^ (-(d + α))` in the sup norm and strictly below the uncut global critical intensity.
The moment majorant comes from `CutoffExhaustion.Moments`; older high-temperature inputs can be
converted by `lt_globalCriticalIntensity_of_BFS`.
The weighted inserted-pivotal series of the uncapped cut-off derivative is absolutely summable
on every corner-free positive-radius window. A uniform bound on its total mass is also proved.

These are pointwise-in-radius summability and total-mass results. They do not establish
continuity of the whole series, an arbitrarily small cofinite tail, or a derivative formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-! ### Norm summability of the weighted inserted-pivotal series -/

/-- **The weighted inserted-pivotal flux of the high-temperature power law is absolutely
summable**, at every radius of every corner-free window (no natural number strictly inside
`Ioo u v`), for every order `p ≥ 1`, with the uncut `(p+1)`-st moment as the uniform
radius-independent root-moment majorant.

The weight is the derivative of the cut-off edge probability at the power-law derivative
`K'(t) = -((d + α) t ^ (-(d + α) - 1))`, evaluated at the cut-off kernel; `-K'(r)` is displayed
evaluated as `(d + α) r ^ (-(d + α) - 1)`. -/
theorem summable_norm_cutoffKernel_powerLaw_flux_of_high_temp {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∀ r ∈ Ioo u v, Summable fun e : Sym2 (Fin d → ℤ) =>
      ‖(radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂
          (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖ := by
  obtain ⟨M, hM, hroot⟩ :=
  CutoffExhaustion.exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ (0 : Fin d → ℤ) p (u := u) (v := v) (R := 1)
    hu zero_lt_one
  refine summable_norm_cutoff_flux_of_root_succ_moment
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => -(((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    β p hp _
    hM
    (fun r e => (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
        Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))))
    (fun r e => by simp only [neg_neg, ModelNorm.toSeminorm_ofNorm])
    (corner_free_of_forall_nat_notMem hcorner)
    (fun r hr => hroot r (Or.inl hr))

/-- The same series is summable as a real-valued series (not only in norm) on any corner-free
window: the pointwise summability a derivative consumer needs. -/
theorem summable_cutoffKernel_powerLaw_flux_of_high_temp {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    {p : ℕ} (hp : 1 ≤ p) {u v r : ℝ} (hu : 0 < u)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) (hr : r ∈ Ioo u v) :
    Summable fun e : Sym2 (Fin d → ℤ) =>
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂
          (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β)) :=
  (summable_norm_cutoffKernel_powerLaw_flux_of_high_temp hd hα hβ hp hu hcorner r
    hr).of_norm

/-! ### Uniform total mass on a corner-free window -/

/-- **One radius-independent constant dominates the whole weighted inserted-pivotal flux.** On a
corner-free window (no natural number strictly inside `Ioo u v`; the window may be empty), the total
absolute weighted pivotal mass of the high-temperature power law is at most
`β * (d + α) * u ^ (-(d + α) - 1) * C`,
where `C ≥ 0` depends only on `d, α, β` and the order `p`: the radius enters only through the
monotone rate `r ↦ (d + α) r ^ (-(d + α) - 1) ≤ (d + α) u ^ (-(d + α) - 1)`.

Nothing uniform in a *tolerance* is claimed, and no tail over the complement of a finite edge set is
bounded: the constant dominates the sum over all edges, so it gives no small-tail input. -/
theorem exists_uniform_norm_tsum_cutoffKernel_powerLaw_flux_le_of_high_temp {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    {p : ℕ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u)
    (hcorner : ∀ n : ℕ, (n : ℝ) ∉ Ioo u v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioo u v,
      Summable (fun e : Sym2 (Fin d → ℤ) =>
        ‖(radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂
            (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖) ∧
      (∑' e : Sym2 (Fin d → ℤ),
        ‖(radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) 0).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) 0).encard : ℝ≥0∞) ^ p).toReal ∂
            (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖) ≤
        (β : ℝ) * (((d : ℝ) + α) * u ^ (-((d : ℝ) + α) - 1)) * C := by
  obtain ⟨M, hM, hroot⟩ :=
  CutoffExhaustion.exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ (0 : Fin d → ℤ) p (u := u) (v := v) (R := 1)
    hu zero_lt_one
  obtain ⟨C, hC0, hC⟩ := exists_uniform_tsum_norm_cutoff_flux_le_of_root_succ_moment
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => -(((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    β p hp _
    hM
    (fun r e => (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
        Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))))
    (fun r e => by simp only [neg_neg, ModelNorm.toSeminorm_ofNorm])
    (corner_free_of_forall_nat_notMem hcorner)
    (fun r hr => hroot r (Or.inl hr))
  refine ⟨C, hC0, fun r hr => ⟨(hC r hr).1, ?_⟩⟩
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hda : (0 : ℝ) < (d : ℝ) + α := by linarith
  have hz : -((d : ℝ) + α) - 1 ≤ 0 := by linarith
  have hrpow : r ^ (-((d : ℝ) + α) - 1) ≤ u ^ (-((d : ℝ) + α) - 1) :=
    Real.rpow_le_rpow_of_nonpos hu hr.1.le hz
  have hnn : (0 : ℝ) ≤ (β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) := by
    have h : (0 : ℝ) ≤ r ^ (-((d : ℝ) + α) - 1) :=
      Real.rpow_nonneg (le_of_lt (lt_trans hu hr.1)) _
    have hb : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
    positivity
  have hrate : |(β : ℝ) * -(-(((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)))| ≤
      (β : ℝ) * (((d : ℝ) + α) * u ^ (-((d : ℝ) + α) - 1)) := by
    rw [neg_neg, abs_of_nonneg hnn]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hda.le) β.coe_nonneg
  exact ((hC r hr).2).trans (mul_le_mul_of_nonneg_right hrate hC0)

end PercLib.Models.LongRange
