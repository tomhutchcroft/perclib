/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Adapted from the uncommitted, project-generated candidate `CutoffExhaustion.lean`, under the same
Apache 2.0 licence. Its source digest is retained in the verification log and integration commit
message. This is a proof-only migration.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5, Corollary I.2.5 and the proof of Lemma I.4.1. The parameter range here is
strictly below the uncut global critical intensity; no endpoint result is claimed.
-/
module

public import PercLib.Models.LongRange.CutoffExhaustion.Moments
public import PercLib.Models.LongRange.CornerDerivative.Defs

/-!
# Strict-subcritical cutoff exhaustion and corner selectors

The imported `CutoffExhaustion.Moments` module supplies uniform higher moments independently of the
corner derivative interfaces. This module adds its real-valued monotonicity and the selector
algebra, keeping those lower-level moment bounds usable by the derivative stack. Nothing is
asserted at `β = β_c`; no flux-level selector inequality is proved here.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open PercLib.Analysis
open PercLib.Percolation.Bond
open PercLib.Models.LongRange
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange.CutoffExhaustion

variable {d : ℕ} {α : ℝ}

/-! ### The real-valued corner object and the two selectors

`momToReal d α β p ρ` (from `PercLib/Models/LongRange/CornerDerivative/Defs.lean`) is the real
`p`-th cut-off root moment that the corner derivative differentiates. Below we record that at
`β < β_c` it is monotone and uniformly bounded, and we compare the strict and closed radial
selectors `kernelSelStrict` / `kernelSelClosed` used in the pivotal flux. -/

/-- Monotonicity of a radial kernel in its profile. -/
theorem radialKernel_mono_profile {N : Seminorm ℝ (Fin d → ℝ)} {K₁ K₂ : ℝ → ℝ}
    (hK : ∀ s, K₁ s ≤ K₂ s) (e : Sym2 (Fin d → ℤ)) :
    radialKernel N K₁ e ≤ radialKernel N K₂ e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [radialKernel_mk, radialKernel_mk]
    split_ifs with h
    · exact le_rfl
    · exact Real.toNNReal_le_toNNReal (hK _)

/-- The strict-ball radial selector is pointwise dominated by the closed-ball selector. -/
theorem radialKernel_kernelSelStrict_le_closed (N : Seminorm ℝ (Fin d → ℝ)) {n : ℝ}
    (e : Sym2 (Fin d → ℤ)) :
    radialKernel N (kernelSelStrict n) e ≤ radialKernel N (kernelSelClosed n) e := by
  refine radialKernel_mono_profile (fun s => ?_) e
  simp only [kernelSelStrict, kernelSelClosed]
  split_ifs with h1 h2
  · norm_num
  · linarith
  · norm_num
  · norm_num

/-- **The selector discrepancy is exactly the shell.**  For every bond, the closed-ball weight is
the strict-ball weight plus the indicator of the shell at distance exactly `n`: this is the only
term by which the two corner selectors differ. -/
theorem radialKernel_kernelSelClosed_eq_strict_add_shell (N : Seminorm ℝ (Fin d → ℝ)) {n : ℝ}
    (hn : 0 ≤ n) (e : Sym2 (Fin d → ℤ)) :
    (radialKernel N (kernelSelClosed n) e : ℝ) =
      (radialKernel N (kernelSelStrict n) e : ℝ) +
        (radialKernel N (fun s => if s = n then 1 else 0) e : ℝ) := by
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      simp [radialKernel_diag]
    · rw [coe_radialKernel_of_ne hxy (by
          simp only [kernelSelClosed]; split_ifs <;> norm_num),
        coe_radialKernel_of_ne hxy (by
          simp only [kernelSelStrict]; split_ifs <;> norm_num),
        coe_radialKernel_of_ne hxy (by split_ifs <;> norm_num)]
      simp only [kernelSelClosed, kernelSelStrict]
      rcases lt_trichotomy (N (Int.cast ∘ (x - y))) n with hlt | heq | hgt
      · simp [hlt, le_of_lt hlt, ne_of_lt hlt]
      · subst heq
        norm_num
      · have h2 : ¬ (N (Int.cast ∘ (x - y)) < n) := not_lt.mpr (le_of_lt hgt)
        have h3 : ¬ (N (Int.cast ∘ (x - y)) = n) := ne_of_gt hgt
        have h4 : ¬ (N (Int.cast ∘ (x - y)) ≤ n) := not_le.mpr hgt
        simp [h2, h3, h4]

/-- **The real cut-off root moment is bounded by the raw moment** at strict subcriticality, at
every positive scale. -/
theorem momToReal_le_raw (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    momToReal d α β p ρ ≤
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p ∂law (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β)).toReal :=
  ENNReal.toReal_mono
    (lintegral_encard_pow_raw_ne_top hd hα hβ 0 p)
    (cutoff_pow_le_raw β 0 p hρ)

/-- **The real cut-off root moment is monotone in the scale** at strict subcriticality. -/
theorem monotoneOn_momToReal (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) : MonotoneOn (momToReal d α β p) (Ioi 0) := by
  intro r hr ρ hρ hrρ
  have hle : (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p ∂law (intensityProfile
      (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤
      ∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p ∂law (intensityProfile
        (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) ρ) β) :=
    lintegral_encard_cluster_pow_mono_intensity
      (J := cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) r)
      (J' := cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) ρ)
      (fun e => monotone_cutoffKernel
        (N := ModelNorm.ofNorm (Fin d → ℝ))
        (PercLib.Models.LongRange.antitoneOn_powerLawProfile zero_le_one (by positivity))
        e hrρ) β 0 p
  refine ENNReal.toReal_mono ?_ hle
  exact PercLib.Models.LongRange.lintegral_cutoffKernel_encard_cluster_pow_ne_top_of_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (hK := fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hρ β 0 p
    (lintegral_encard_pow_raw_ne_top hd hα hβ 0 p)

end PercLib.Models.LongRange.CutoffExhaustion
