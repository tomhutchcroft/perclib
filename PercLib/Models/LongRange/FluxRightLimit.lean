/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 and the right-rate reading of Lemma I.4.1. No two-sided differentiability at a
norm corner is asserted.
-/
module

public import PercLib.Analysis.UniformTail
public import PercLib.Models.LongRange.RestorationDerivativeGeneral
public import PercLib.Models.LongRange.CutoffExhaustion.Moments

/-!
# The right limit of the uncapped pivotal flux at an integer scale

Uniform small tails replace a uniform summable edge dominator. At every positive integer radius
strictly below the uncut global critical intensity, restoration supplies the local tail and the
uncapped flux sums have absolute summability there. Their right limit carries the closed-ball
radial weight. Moment continuity is a separate input and is not assumed here.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-- **The aggregate right limit of the cut-off pivotal flux from a uniform small tail.**

This is `tendsto_tsum_flux_nhdsGT_of_dominated` with the summable dominator `bound` replaced by the
uniform small-tail estimate `htail`.  The uniform tail, not a pointwise bound, is what the
restoration estimates give, and it is enough: see
`PercLib.Analysis.tendsto_tsum_of_tendsto_of_uniform_tail`.  The limit carries the closed-ball
radial factor `1 (N z ≤ n)`, i.e. the length classes sitting exactly at the corner scale enter with
their full derivative weight. -/
theorem tendsto_tsum_cutoff_pivotal_flux_nhdsGT_of_uniform_tail {d : ℕ}
    {N : ModelNorm (Fin d → ℝ)} {K K' : ℝ → ℝ}
    (hKa : AntitoneOn K (Ioi 0)) (hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t)
    (hK'c : ContinuousOn K' (Ioi 0)) (β : ℝ≥0) {n : ℝ} (hn : 0 < n)
    (Piv : ℝ → Sym2 (Fin d → ℤ) → ℝ)
    (hPiv : ∀ e, Tendsto (fun r => Piv r e) (𝓝[>] n) (𝓝 (Piv n e)))
    (htail : ∀ ε > 0, ∃ F : Finset (Sym2 (Fin d → ℤ)), ∀ᶠ r in 𝓝[>] n,
      Summable (fun e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ =>
        ‖(radialKernel N (fun s => if s < r then 1 else 0) e.1 : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e.1 : ℝ))) *
          Piv r e.1‖) ∧
      ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖(radialKernel N (fun s => if s < r then 1 else 0) e.1 : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e.1 : ℝ))) *
          Piv r e.1‖ ≤ ε) :
    Tendsto (fun r => ∑' e, (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))) *
        Piv r e) (𝓝[>] n)
      (𝓝 (∑' e, (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))) *
        Piv n e)) := by
  refine tendsto_tsum_of_tendsto_of_uniform_tail (𝓕 := 𝓝[>] n)
    (f := fun r e => (radialKernel N (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e : ℝ))) * Piv r e)
    (g := fun e => (radialKernel N (fun s => if s ≤ n then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' n * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K n e : ℝ))) * Piv n e) ?_ ?_
  · intro e
    exact (tendsto_cutoff_coeff_nhdsGT hKa hK' hK'c β hn e).mul (hPiv e)
  · exact htail

/-- **The right limit of the actual uncapped power-law pivotal flux at a positive integer scale.**

At every positive integer scale `n`, strictly below the uncut global critical intensity, the whole
weighted pivotal flux series of the uncapped `p`-th root moment has a right limit at `n`.
That limit uses the **closed-ball** radial weight `1 (‖z‖ ≤ n)`, so the entire cutoff support
carries its full derivative weight in the right limit.

Every hypothesis of `tendsto_tsum_cutoff_pivotal_flux_nhdsGT_of_root_succ_moment` is discharged:
the uniform one-sided dominator `hbd` — which does not exist on the infinite lattice — is replaced
by the uniform small-tail estimate
`exists_nhds_htail_powerLaw_of_restoration_general`, the per-pair limit by
`continuousAt_pivotal_cutoff_uncapped_of_root_succ_moment`, and the pointwise absolute summability
by `summable_norm_cutoffKernel_powerLaw_flux_of_high_temp` on the corner-free window
`(n, n+1)`. -/
theorem tendsto_tsum_cutoffKernel_powerLaw_pivotal_flux_nhdsGT_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    {p : ℕ} (hp : 1 ≤ p) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal ∂
            (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      (𝓝[>] (n : ℝ))
      (𝓝 (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s ≤ (n : ℝ) then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * (n : ℝ) ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ) e : ℝ))) *
          ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal ∂
            (law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (n : ℝ)) β)))) := by
  set N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ) with hN
  set K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α) with hK
  set K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)) with hK'
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hda : (0 : ℝ) ≤ (d : ℝ) + α := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    linarith
  set u : ℝ := (n : ℝ) / 2 with hu_def
  set R : ℝ := 2 * (n : ℝ) + 1 with hR_def
  have hu : 0 < u := by rw [hu_def]; linarith
  have hR : 0 < R := by rw [hR_def]; linarith
  have hun : u < (n : ℝ) := by rw [hu_def]; linarith
  have hnR : (n : ℝ) < R := by rw [hR_def]; linarith
  have huR : u < R := lt_trans hun hnR
  have hKa : AntitoneOn K (Ioi 0) := by
    rw [hK]; exact antitoneOn_powerLawProfile_add (c := 1) zero_le_one hda
  have hK'deriv : ∀ t, 0 < t → HasDerivAt K (K' t) t := by
    intro t ht
    rw [hK, hK']
    exact hasDerivAt_powerLawProfile_add 1 α ht
  have hK'cont : ContinuousOn K' (Ioi 0) := by
    rw [hK']; exact continuousOn_powerLawProfile_deriv_add (d := d) 1 α
  obtain ⟨M, hM, hroot⟩ :=
    CutoffExhaustion.exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := u) (v := R) (R := R) hu hR
  have hroot' : ∀ r ∈ (Ioo u R ∪ {R} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
    intro r hr
    simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot r hr
  have hPiv : ∀ e : Sym2 (Fin d → ℤ),
      Tendsto (fun r : ℝ => ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) (𝓝[>] (n : ℝ))
        (𝓝 (∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
          ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
          ∂(law (intensityProfile (cutoffKernel (d := d) N K (n : ℝ)) β)))) :=
    fun e => continuousAt_pivotal_cutoff_uncapped_of_root_succ_moment
      (N := N) (K := K) (K' := K') hKa hK'deriv hK'cont β p hp (0 : Fin d → ℤ)
      (u := u) (R := R) (n := (n : ℝ)) hu hun hnR M hM hroot' e
  have hcorner : ∀ k : ℕ, (k : ℝ) ∉ Ioo (n : ℝ) ((n : ℝ) + 1) := by
    intro k hk
    have h1 : n < k := by exact_mod_cast hk.1
    have h2 : k < n + 1 := by exact_mod_cast hk.2
    omega
  have htail : ∀ ε > 0, ∃ F : Finset (Sym2 (Fin d → ℤ)), ∀ᶠ r in 𝓝[>] (n : ℝ),
      Summable (fun e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ =>
        ‖(radialKernel N (fun s => if s < r then 1 else 0) e.1 : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e.1 : ℝ))) *
          (∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))‖) ∧
      ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖(radialKernel N (fun s => if s < r then 1 else 0) e.1 : ℝ) *
          ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e.1 : ℝ))) *
          (∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))‖ ≤ ε := by
    intro ε hε
    obtain ⟨U, hU, F, hF⟩ := exists_nhds_htail_powerLaw_of_restoration_general (d := d) hd hα
      hβ p hp (0 : Fin d → ℤ) hu huR (n : ℝ) ⟨hun, hnR⟩ ε hε
    refine ⟨F, ?_⟩
    have hU' : ∀ᶠ r in 𝓝[>] (n : ℝ), r ∈ U := nhdsWithin_le_nhds (s := Ioi (n : ℝ)) hU
    have hmid : ∀ᶠ r in 𝓝[>] (n : ℝ), r ∈ Ioo u R := by
      have h1 : Ioi u ∈ 𝓝 (n : ℝ) := isOpen_Ioi.mem_nhds hun
      have h2 : Iio R ∈ 𝓝 (n : ℝ) := isOpen_Iio.mem_nhds hnR
      have := nhdsWithin_le_nhds (s := Ioi (n : ℝ)) (inter_mem h1 h2)
      filter_upwards [this] with r hr
      exact hr
    have hev : ∀ᶠ r in 𝓝[>] (n : ℝ), r ∈ Ioo (n : ℝ) ((n : ℝ) + 1) := by
      have h1 : Ioi (n : ℝ) ∈ 𝓝[>] (n : ℝ) := self_mem_nhdsWithin
      have h2 : Iio ((n : ℝ) + 1) ∈ 𝓝[>] (n : ℝ) :=
        nhdsWithin_le_nhds (s := Ioi (n : ℝ)) (isOpen_Iio.mem_nhds (by
          change (n : ℝ) < (n : ℝ) + 1
          linarith))
      filter_upwards [h1, h2] with r hr1 hr2
      exact ⟨hr1, hr2⟩
    have hsumm : ∀ᶠ r in 𝓝[>] (n : ℝ),
        Summable (fun e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ =>
          ‖(radialKernel N (fun s => if s < r then 1 else 0) e.1 : ℝ) *
            ((β : ℝ) * -K' r * Real.exp (-(β : ℝ) * (cutoffKernel (d := d) N K r e.1 : ℝ))) *
            (∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
              ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β)))‖) := by
      filter_upwards [hev] with r hr
      have h0 := summable_norm_cutoffKernel_powerLaw_flux_of_high_temp (d := d) hd hα hβ
        (p := p) hp (u := (n : ℝ)) (v := (n : ℝ) + 1) hnn hcorner r hr
      simpa only [hN, hK, hK', ModelNorm.toSeminorm_ofNorm, one_mul, neg_mul, neg_neg,
        Function.comp_def] using h0.subtype (fun e => e ∈ (F : Set (Sym2 (Fin d → ℤ)))ᶜ)
    filter_upwards [hU', hmid, hsumm] with r hrU hrIoo hrsum
    refine ⟨hrsum, ?_⟩
    have h := hF r ⟨hrU, hrIoo⟩
    simpa only [hN, hK, hK', ModelNorm.toSeminorm_ofNorm, one_mul, neg_mul, neg_neg] using h
  have hmain := tendsto_tsum_cutoff_pivotal_flux_nhdsGT_of_uniform_tail (N := N) (K := K) (K' := K')
    hKa hK'deriv hK'cont β hnn
    (Piv := fun r e => ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
      ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
      ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) hPiv htail
  simpa only [hN, hK, hK', ModelNorm.toSeminorm_ofNorm, one_mul, neg_mul, neg_neg] using hmain

end PercLib.Models.LongRange
