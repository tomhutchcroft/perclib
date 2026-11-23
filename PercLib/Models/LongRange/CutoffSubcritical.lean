/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 and the subsequent cut-off subcriticality discussion.
-/
module

public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Models.LongRange.FiniteSusceptibility
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Percolation.Bond.ZeroIntensityGap

/-!
# Reduced-parameter domination of the cutoff power-law model

For radii at least one, the cutoff power-law kernel is dominated pointwise by a strictly smaller
positive multiple of the original kernel. This compares cut-off natural cluster
moments at parameter `β` with uncut moments at a strictly smaller parameter, and proves finite
cut-off susceptibility at every parameter at most the uncut global critical intensity. It does
not supply the higher uncut moments needed by the subcritical uncapped derivative interfaces.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

open PercLib.Analysis PercLib.Percolation.Bond

variable {d : ℕ}

/-! ### The sup norm of a nonzero integer vector -/

/-- A nonzero integer vector has sup norm at least `1`.  This is the only place where the sup
norm (rather than an arbitrary norm) enters. -/
theorem one_le_norm_intCast {z : Fin d → ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ ‖z‖ := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    exact hz (funext fun i => by simpa using not_not.1 (not_exists.1 h i))
  have h4 : (1 : ℝ) ≤ ‖z i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h4.trans (norm_le_pi_norm z i)

/-! ### Reduced-parameter domination of the cut-off kernel -/

/-- Pointwise domination `J_r ≤ (1 - r ^ (-(d+α))) • J` of Definition I.1.5 at a profile value
`s ≥ 1`.  For `s ≤ r` the deficit is `r ^ (-(d+α))` and `s ^ (-(d+α)) ≤ 1`; for `s > r` the
cut-off value is `0` and the factor is nonnegative because `r ≥ 1`. -/
theorem powerLaw_cutoffProfile_le_smul {α r s : ℝ} (hα : 0 < α) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    cutoffProfile (powerLawProfile 1 ((d : ℝ) + α)) r s ≤
      (1 - r ^ (-((d : ℝ) + α))) * powerLawProfile 1 ((d : ℝ) + α) s := by
  have ha : (0 : ℝ) < (d : ℝ) + α := by positivity
  have hspos : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hsa : s ^ (-((d : ℝ) + α)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs (by linarith)
  have hra : r ^ (-((d : ℝ) + α)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith)
  have hra0 : (0 : ℝ) ≤ r ^ (-((d : ℝ) + α)) := Real.rpow_nonneg hrpos.le _
  have hspos' : (0 : ℝ) ≤ s ^ (-((d : ℝ) + α)) := Real.rpow_nonneg hspos.le _
  unfold cutoffProfile powerLawProfile
  simp only [one_mul]
  split_ifs with h
  · nlinarith [hra0, hsa]
  · have h1 : (0 : ℝ) ≤ 1 - r ^ (-((d : ℝ) + α)) := by linarith
    have h2 : (0 : ℝ) ≤ (1 - r ^ (-((d : ℝ) + α))) * s ^ (-((d : ℝ) + α)) :=
      mul_nonneg h1 hspos'
    linarith

/-- Kernel-level form: the cut-off kernel is dominated by a multiple of the uncut radial kernel. -/
theorem cutoffKernel_powerLaw_le_smul_radialKernel {α r : ℝ} (hα : 0 < α) (hr : 1 ≤ r)
    (e : Sym2 (Fin d → ℤ)) :
    (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ) ≤
      (1 - r ^ (-((d : ℝ) + α))) *
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) e : ℝ) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp
    · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have hs : (1 : ℝ) ≤ normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) := by
        rw [normSeminorm_intCast]
        exact one_le_norm_intCast hz
      have hs' : (0 : ℝ) < normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y)) := by linarith
      have hcut : (0 : ℝ) ≤ cutoffProfile (powerLawProfile 1 ((d : ℝ) + α)) r
          (normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y))) := by
        unfold cutoffProfile powerLawProfile
        simp only [one_mul]
        split_ifs with h
        · have h1 : r ^ (-((d : ℝ) + α)) ≤
              (normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y))) ^ (-((d : ℝ) + α)) :=
            Real.rpow_le_rpow_of_nonpos hs' h (by linarith)
          linarith
        · exact le_rfl
      have hrad : (0 : ℝ) ≤ powerLawProfile 1 ((d : ℝ) + α)
          (normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ (x - y))) := by
        unfold powerLawProfile
        have := Real.rpow_nonneg hs'.le (-((d : ℝ) + α))
        linarith
      rw [cutoffKernel,
        coe_radialKernel_of_ne (N := normSeminorm ℝ (Fin d → ℝ))
          (K := cutoffProfile (powerLawProfile 1 ((d : ℝ) + α)) r) hxy hcut,
        coe_radialKernel_of_ne (N := normSeminorm ℝ (Fin d → ℝ))
          (K := powerLawProfile 1 ((d : ℝ) + α)) hxy hrad]
      exact powerLaw_cutoffProfile_le_smul (d := d) hα hr hs

/-- A general profile comparison: a pointwise domination of the integrated intensities gives
domination of the edge probabilities at possibly different parameters. -/
theorem intensityProfile_le_of_smul_le {V : Type*} {J J' : Sym2 V → ℝ≥0} {β β' : ℝ≥0}
    (h : ∀ e, (β : ℝ) * (J e : ℝ) ≤ (β' : ℝ) * (J' e : ℝ)) :
    intensityProfile J β ≤ intensityProfile J' β' := by
  intro e
  change 1 - Real.exp (-(β : ℝ) * (J e : ℝ)) ≤ 1 - Real.exp (-(β' : ℝ) * (J' e : ℝ))
  have h2 := Real.exp_le_exp.2 (show -(β' : ℝ) * (J' e : ℝ) ≤ -(β : ℝ) * (J e : ℝ) by
    linarith [h e])
  linarith

/-- At the reduced parameter `β * (1 - r ^ (-(d+α)))` the cut-off edge probabilities are dominated
by the uncut ones. -/
theorem intensityProfile_cutoffKernel_powerLaw_le {α r : ℝ} (hα : 0 < α) (hr : 1 ≤ r)
    (β : ℝ≥0) :
    intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β ≤
      intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))) (β * (1 - r ^ (-((d : ℝ) + α))).toNNReal) := by
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hra : r ^ (-((d : ℝ) + α)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr (by
      have : (0 : ℝ) ≤ (d : ℝ) + α := by positivity
      linarith)
  have hc : (0 : ℝ) ≤ 1 - r ^ (-((d : ℝ) + α)) := by linarith
  refine intensityProfile_le_of_smul_le (J' := radialKernel (normSeminorm ℝ (Fin d → ℝ))
    (powerLawProfile 1 ((d : ℝ) + α))) fun e => ?_
  have hker := cutoffKernel_powerLaw_le_smul_radialKernel (d := d) hα hr e
  have hcoe : ((β * (1 - r ^ (-((d : ℝ) + α))).toNNReal : ℝ≥0) : ℝ) =
      (β : ℝ) * (1 - r ^ (-((d : ℝ) + α))) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hc]
  have hker' : (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ) ≤
      (1 - r ^ (-((d : ℝ) + α))) *
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) e : ℝ) :=
    hker
  rw [hcoe]
  calc (β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)
      ≤ (β : ℝ) * ((1 - r ^ (-((d : ℝ) + α))) *
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) e : ℝ)) :=
        mul_le_mul_of_nonneg_left hker' β.coe_nonneg
    _ = ((β : ℝ) * (1 - r ^ (-((d : ℝ) + α)))) *
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) e : ℝ) := by ring

/-! ### Moment and susceptibility consequences -/

/-- **Reduced-parameter moment domination.**  Every natural cut-off cluster moment at parameter
`β` is bounded by the uncut moment at `β * (1 - r ^ (-(d+α)))`. -/
theorem lintegral_cutoffKernel_powerLaw_pow_le_uncut_smul {α r : ℝ} (hα : 0 < α) (hr : 1 ≤ r)
    (β : ℝ≥0) (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂
        law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂
        law (intensityProfile (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α))) (β * (1 - r ^ (-((d : ℝ) + α))).toNNReal)) :=
  lintegral_encard_cluster_pow_mono
    (intensityProfile_cutoffKernel_powerLaw_le (d := d) hα hr β) o k

/-- The uncut power-law radial kernel is a translation-invariant kernel in the sense of the
sharpness theorem. -/
theorem radialKernel_powerLaw_eq_translate {α : ℝ} (x y : Fin d → ℤ) :
    radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) s(x, y) =
      Real.toNNReal (if y - x = 0 then 0 else ‖y - x‖ ^ (-((d : ℝ) + α))) := by
  by_cases h : x = y
  · subst h
    rw [radialKernel_diag]
    simp
  · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [radialKernel_mk]
    simp only [powerLawProfile, one_mul, normSeminorm_intCast, norm_sub_rev]
    simp [h, hne]

/-- **The cut-off susceptibility is finite at every intensity at most the uncut global critical
intensity**, for every radius at least one. The strict decrease in intensity, rather than the
high-temperature condition `β M < 1`, supplies finiteness of this first moment. This is not a
higher-moment bound or an uncapped derivative theorem at subcritical intensity. -/
theorem chi_cutoffKernel_powerLaw_lt_top_of_le_globalCritical (hd : 1 ≤ d) {α r : ℝ}
    (hα : 0 < α) (hr : 1 ≤ r) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) ≤ globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (o : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
      (powerLawProfile 1 ((d : ℝ) + α)) r) β) o < ⊤ := by
  by_cases hβ0 : β = 0
  · rw [hβ0, chi_zero_intensity]
    exact ENNReal.one_lt_top
  · have hβpos : (0 : ℝ≥0) < β := pos_iff_ne_zero.2 hβ0
    have ha : (0 : ℝ) < (d : ℝ) + α := by positivity
    have hrpos : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
    have hra0 : (0 : ℝ) < r ^ (-((d : ℝ) + α)) := Real.rpow_pos_of_pos hrpos _
    have hcoe_lt : (1 - r ^ (-((d : ℝ) + α))).toNNReal < 1 := by
      rw [Real.toNNReal_lt_one]
      linarith
    have hβ'lt : β * (1 - r ^ (-((d : ℝ) + α))).toNNReal < β := by
      calc β * (1 - r ^ (-((d : ℝ) + α))).toNNReal < β * 1 :=
            mul_lt_mul_of_pos_left hcoe_lt hβpos
        _ = β := mul_one β
    have hlt : ((β * (1 - r ^ (-((d : ℝ) + α))).toNNReal : ℝ≥0) : ℝ≥0∞) <
        globalCriticalIntensity (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α))) :=
      lt_of_lt_of_le (by exact_mod_cast hβ'lt) hβ
    have hpl := chi_lt_top_of_lt_globalCriticalIntensity_powerLaw (d := d) hd hα
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)))
      (fun x y => radialKernel_powerLaw_eq_translate (d := d) x y)
    refine lt_of_le_of_lt ?_ ((hpl.1 _ hlt) o)
    have hmom := lintegral_cutoffKernel_powerLaw_pow_le_uncut_smul (d := d) hα hr β o 1
    simpa only [chi, pow_one] using hmom

end PercLib.Models.LongRange
