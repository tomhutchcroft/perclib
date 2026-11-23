/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5. This is a quantitative coupling estimate for continuity analysis; it is not
itself a global differentiability claim.
-/
module

public import PercLib.Models.LongRange.CornerCoupling
public import PercLib.Models.LongRange.RestorationDerivativeGeneral
public import PercLib.Models.LongRange.CornerChangeMeasurable

/-!
# A capped change estimate from the softened-edge coupling

The softening coupling bounds how much a cluster-moment expectation can increase near an integer
cut-off scale. Its change probability is bounded using the base susceptibility, while the
higher-order remainder is controlled by the uncapped `(p+1)`-st moment.
-/

@[expose] public section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open scoped ENNReal NNReal unitInterval Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-- **The cluster moment at scale `r` is at most the scale-`n` moment plus a capped change term
and a tail term.** This is the quantitative right-continuity estimate at an integer scale: the
`p`-th moment grows by at most `B^p` times the probability that the cluster cardinality changes,
plus `B⁻¹` times the `(p+1)`-st moment. -/
theorem moment_le_soften {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) {β : ℝ≥0} {n : ℕ}
    {r : ℝ} (hnr : (n : ℝ) ≤ r) (hrn : r < (n : ℝ) + 1) {ρ : unitInterval}
    (hρ : (ρ : ℝ) = 1 - Real.exp (-(β : ℝ) * (K (n : ℝ) - K r)))
    (o : Fin d → ℤ) (p : ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hχ : chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K (n : ℝ)) β) o ≠ ⊤)
    (hn_fin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law
      (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β)) ≠ ⊤)
    (hr_fin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂law
      (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)) ≠ ⊤) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)).toReal
      ≤ (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂
        law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β)).toReal
        + (B : ℝ) ^ p *
          (((↑(unitInterval.toNNReal ρ) : ℝ≥0∞) * (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) *
            chi (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β) o).toReal)
        + (B : ℝ)⁻¹ * (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂
            law (intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β)).toReal := by
  classical
  set q_r := intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K r) β with hq_r
  set q_n := intensityProfile (cutoffKernel (supModelNorm d).toSeminorm K n) β with hq_n
  set P_n : Measure (Config (Fin d → ℤ)) := law q_n with hP_n
  set P_ρ : Measure (Config (Fin d → ℤ)) := law (reopenProfile (d := d) n ρ) with hP_ρ
  set γ : Measure (Config (Fin d → ℤ) × Config (Fin d → ℤ)) := P_n.prod P_ρ with hγ
  set fr : Config (Fin d → ℤ) → ℝ≥0∞ := fun ω => ((cluster ω o).encard : ℝ≥0∞) ^ p with hfr
  set fr1 : Config (Fin d → ℤ) → ℝ≥0∞ := fun ω => ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) with hfr1
  have hbase : Measurable fun ω : Config (Fin d → ℤ) => ((cluster ω o).encard : ℝ≥0∞) :=
    measurable_encard_cluster_toENNReal o
  have hmeasr : Measurable fr := by
    rw [hfr]; exact hbase.pow_const p
  have hmeasr1 : Measurable fr1 := by
    rw [hfr1]; exact hbase.pow_const (p + 1)
  have hmap : law q_r = Measure.map (fun z : Config (Fin d → ℤ) × Config (Fin d → ℤ) =>
      z.1 ∪ z.2) γ := by
    rw [hγ, hP_n, hP_ρ, hq_r, hq_n]
    exact (prodBernoulli_cutoff_eq_soften hK hnr hrn hρ).symm
  have e1 : (∫⁻ ω, fr ω ∂law q_r) = ∫⁻ z, fr (z.1 ∪ z.2) ∂γ := by
    rw [hmap, lintegral_map hmeasr (by fun_prop)]
  have e2 : (∫⁻ ω, fr ω ∂law q_n) = ∫⁻ z, fr z.1 ∂γ := by
    rw [hγ, hP_n, ← lintegral_map hmeasr measurable_fst, Measure.map_fst_prod]
    simp [hP_ρ]
  have hInt := lintegral_capped_change_bound o γ p hB
  have hchange : γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
        cluster (z.1 ∪ z.2) o ≠ cluster z.1 o}
      ≤ (↑(unitInterval.toNNReal ρ) : ℝ≥0∞) * (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) * chi q_n o := by
    simpa only [ne_comm, hγ, hP_n, hP_ρ, hq_n] using
      measure_change_le (K := K) (β := β) (n := n) (ρ := ρ) o
  have hold : (∫⁻ z, fr z.1 ∂γ) ≠ ⊤ := by
    rw [e2.symm]
    exact hn_fin
  have he1p : (∫⁻ ω, fr1 ω ∂law q_r) = ∫⁻ z, fr1 (z.1 ∪ z.2) ∂γ := by
    rw [hmap, lintegral_map hmeasr1 (by fun_prop)]
  have hnew : (∫⁻ z, fr1 (z.1 ∪ z.2) ∂γ) ≠ ⊤ := he1p ▸ hr_fin
  have H := toReal_lintegral_capped_change_bound o γ p hB (measure_ne_top _ _) hold hnew
  rw [← e1, ← e2, ← he1p] at H
  calc (∫⁻ ω, fr ω ∂law q_r).toReal
      ≤ (∫⁻ ω, fr ω ∂law q_n).toReal + (B : ℝ) ^ p *
          (γ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
            cluster (z.1 ∪ z.2) o ≠ cluster z.1 o}).toReal +
        (B : ℝ)⁻¹ * (∫⁻ ω, fr1 ω ∂law q_r).toReal := H
    _ ≤ _ := by
        have hfinite : ((↑(unitInterval.toNNReal ρ) : ℝ≥0∞) *
            (((2 * n + 1) ^ d : ℕ) : ℝ≥0∞) * chi q_n o) ≠ ⊤ := by
          refine ENNReal.mul_ne_top
            (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top _)) hχ
        gcongr

end PercLib.Models.LongRange
