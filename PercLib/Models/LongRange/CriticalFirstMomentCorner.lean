/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 and Lemma I.4.1. This proves a failure of the literal two-sided-differentiability
reading at radius one for the full infinite-lattice first moment; it does not adjudicate a
one-sided interpretation of the source formula or its exponential edge-weight convention.
-/
module

public import PercLib.Models.LongRange.MomentCorner
public import PercLib.Models.LongRange.CutoffSubcritical

/-!
# The first root moment at radius one

Reduced-parameter domination supplies finiteness of the cut-off first moment at every intensity
at most the uncut global critical intensity. This permits the same honest infinite-lattice
one-edge lower bound at radius one: the left derivative is zero while right difference quotients
are eventually bounded away from zero. Hence no two-sided derivative exists at positive
subcritical intensity or at the uncut global critical intensity. No higher-moment analogue and no
right-derivative formula is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond PercLib.Probability PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange.Corner

variable {d : ℕ}

/-- The cut-off first root moment is finite for every scale at least one and every intensity at
most the uncut global critical intensity. -/
theorem lintegral_first_moment_ne_top_of_le_globalCritical (hd : 1 ≤ d) {α r : ℝ}
    (hα : 0 < α) (hr : 1 ≤ r) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) ≤ globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)))) :
    (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (1 : ℕ) ∂(mu d α β r)) ≠ ⊤ := by
  simpa only [mu, snorm, prof, chi, pow_one] using
    (chi_cutoffKernel_powerLaw_lt_top_of_le_globalCritical hd hα hr β hβ (0 : Fin d → ℤ)).ne

/-- The first cut-off moment grows at least linearly in a unit-pair edge probability beyond one,
without a high-temperature hypothesis. -/
theorem moment_sub_one_ge_p_one_of_le_globalCritical (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) ≤ globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    {r : ℝ} (hr : 1 < r) (i : Fin d) :
    ((2 : ℝ) ^ (1 : ℕ) - 1) *
        (1 - Real.exp (-(β : ℝ) * (1 - r ^ (-((d : ℝ) + α))))) ≤
      moment d α β 1 r - moment d α β 1 1 := by
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (1 : ℕ) - 1 := by norm_num
  have hfin := lintegral_first_moment_ne_top_of_le_globalCritical hd hα hr.le β hβ
  have h1 : 1 + ((2 : ℝ) ^ (1 : ℕ) - 1) *
      (mu d α β r {ω : Config (Fin d → ℤ) | s(0, Pi.single i (1 : ℤ)) ∈ ω}).toReal
      ≤ (∫⁻ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (1 : ℕ))
        ∂(mu d α β r)).toReal :=
    one_add_mul_toReal_le (x := Pi.single i (1 : ℤ)) (ne_zero_single i).symm hfin
  have h2 := one_sub_exp_le_measure_pair (d := d) hα (β := β) hr i
  have hm := moment_eq_lintegral_toReal (d := d) (α := α) (β := β) (p := 1) (r := r) hfin
  have h0 := moment_eq_one_of_le_one (d := d) (α := α) (β := β)
    (p := 1) (r := (1 : ℝ)) le_rfl
  rw [h0, hm]
  have := mul_le_mul_of_nonneg_left h2 hc
  linarith

/-- Positive right-slope lower bound at the first radius for the first moment, throughout the
subcritical and critical intensity range. -/
theorem eventually_le_slope_moment_p_one_of_le_globalCritical (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0} (hβpos : 0 < β)
    (hβ : (β : ℝ≥0∞) ≤ globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (i : Fin d) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ((2 : ℝ) ^ (1 : ℕ) - 1) * ((β : ℝ) * ((d : ℝ) + α)) / 2
        ≤ (moment d α β 1 (1 + δ) - moment d α β 1 1) / δ := by
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (1 : ℕ) - 1 := by norm_num
  have hfac := eventually_le_cornerFactor_slope (d := d) hα hβpos
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 := by
    have : Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
    exact this
  filter_upwards [hfac, hsmall, self_mem_nhdsWithin] with δ hδ hδ1 hδpos
  have hδ0 : (0 : ℝ) < δ := hδpos
  have hr : (1 : ℝ) < 1 + δ := by linarith
  have hmain := moment_sub_one_ge_p_one_of_le_globalCritical (d := d) hd hα hβ hr i
  have hge : ((2 : ℝ) ^ (1 : ℕ) - 1) *
      (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α)))))
      ≤ moment d α β 1 (1 + δ) - moment d α β 1 1 := hmain
  have hdiv : ((2 : ℝ) ^ (1 : ℕ) - 1) *
        (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ
      ≤ (moment d α β 1 (1 + δ) - moment d α β 1 1) / δ :=
    div_le_div_of_nonneg_right hge hδ0.le
  have hsplit : ((2 : ℝ) ^ (1 : ℕ) - 1) *
        (1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ
      = ((2 : ℝ) ^ (1 : ℕ) - 1) *
        ((1 - Real.exp (-(β : ℝ) * (1 - (1 + δ) ^ (-((d : ℝ) + α))))) / δ) := by
    ring
  rw [hsplit] at hdiv
  have := mul_le_mul_of_nonneg_left hδ hc
  linarith [hdiv, this]

/-- The full infinite-lattice first moment has no two-sided derivative at radius one, including
at the uncut global critical intensity. -/
theorem not_hasDerivAt_first_moment_one_of_le_globalCritical (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0} (hβpos : 0 < β)
    (hβ : (β : ℝ≥0∞) ≤ globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (i : Fin d) (L : ℝ) :
    ¬ HasDerivAt (moment d α β 1) L 1 := by
  intro h
  have hleft : HasDerivWithinAt (moment d α β 1) L (Iic (1 : ℝ)) 1 := h.hasDerivWithinAt
  have e1 : derivWithin (moment d α β 1) (Iic (1 : ℝ)) 1 = L :=
    hleft.derivWithin (uniqueDiffWithinAt_Iic 1)
  have e0 : derivWithin (moment d α β 1) (Iic (1 : ℝ)) 1 = 0 :=
    (hasDerivWithinAt_moment_zero_Iic_one (d := d) (α := α) (β := β)
      (p := 1)).derivWithin (uniqueDiffWithinAt_Iic 1)
  have hL : L = 0 := by rw [← e1, e0]
  subst hL
  have hslope1 : Tendsto (slope (moment d α β 1) (1 : ℝ)) (𝓝[≠] (1 : ℝ)) (𝓝 0) :=
    h.tendsto_slope
  have hin : Tendsto (fun δ : ℝ => 1 + δ) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hbase : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using hbase.const_add 1
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ' : (0 : ℝ) < δ := hδ
      intro hcon
      rw [Set.mem_singleton_iff] at hcon
      linarith
  have hcomp := hslope1.comp hin
  have hpt : ∀ δ : ℝ, slope (moment d α β 1) (1 : ℝ) (1 + δ)
      = (moment d α β 1 (1 + δ) - moment d α β 1 1) / δ := by
    intro δ
    have hd : (1 + δ) - 1 = δ := by ring
    simp only [slope, vsub_eq_sub, hd, smul_eq_mul, div_eq_inv_mul]
  have hslope : Tendsto (fun δ : ℝ => (moment d α β 1 (1 + δ) - moment d α β 1 1) / δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := Tendsto.congr hpt hcomp
  have hev := eventually_le_slope_moment_p_one_of_le_globalCritical (d := d) hd hα hβpos hβ i
  have hβ' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβpos
  have ha : (0 : ℝ) < (d : ℝ) + α := by positivity
  have hmul : (0 : ℝ) < ((2 : ℝ) ^ (1 : ℕ) - 1) * ((β : ℝ) * ((d : ℝ) + α)) := by
    norm_num
    positivity
  have hbound := le_of_tendsto_of_tendsto tendsto_const_nhds hslope hev
  linarith

/-- Differentiability form of the radius-one obstruction at arbitrary subcritical or critical
intensity for the first root moment. -/
theorem not_differentiableAt_first_moment_one_of_le_globalCritical (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0} (hβpos : 0 < β)
    (hβ : (β : ℝ≥0∞) ≤ globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (i : Fin d) :
    ¬ DifferentiableAt ℝ (moment d α β 1) 1 := by
  intro hd'
  exact not_hasDerivAt_first_moment_one_of_le_globalCritical hd hα hβpos hβ i
    (deriv (moment d α β 1) 1) (DifferentiableAt.hasDerivAt hd')

end PercLib.Models.LongRange.Corner
