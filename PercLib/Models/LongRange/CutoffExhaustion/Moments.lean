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

public import PercLib.Models.LongRange.FiniteSusceptibility
public import PercLib.Percolation.Bond.UniformVolumeTail
public import PercLib.Models.LongRange.CutoffMoments
public import PercLib.Models.LongRange.CutoffMomentConvergence
public import PercLib.Models.LongRange.CutoffMonotone
public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail

/-!
# Strict-subcritical cutoff exhaustion for the raw power-law law

This proof-only module gives the **boundary/exhaustion** interface of the raw full-lattice
power-law law: uniform higher moments and exact cutoff limits.

Content, all on the raw law `radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 (d+α))`
and at `(β : ℝ≥0∞) < globalCriticalIntensity` of that very kernel:

* `rawKernel_displacement`: the raw kernel is the displacement profile
  `z ↦ (if z = 0 then 0 else ‖z‖ ^ (-(d+α)))`, so the landed transitive-sharpness results apply.
* `chi_lt_top_of_lt_globalCriticalIntensity_raw`, `iSup_chi_ne_top_raw`: finite susceptibility at
  **every** vertex and finite `⨆ x, χ(x)` — the uniform susceptibility hypothesis, in the raw law,
  with `β < β_c` only.
* `lintegral_encard_pow_raw_ne_top`, `lintegral_ofReal_encard_toNat_cluster_pow_le_raw`: every
  natural and real cluster moment of the uncut law is finite.
* `cutoff_pow_le_raw`, `exists_uniform_cutoff_pow_bound_raw`: the cut-off moments at **every**
  positive scale are dominated by the raw moment of the same order — the exhaustion is uniformly
  bounded, no per-scale hypothesis.
* `iSup_cutoff_pow_eq_raw`: the raw moment is exactly the supremum of the cut-off moments over the
  scale (the boundary error along the exhaustion vanishes).
* `lintegral_exp_encard_cluster_le_raw`: finite exponential cluster moments near `0`.

No definition is introduced, no hypothesis `hM` is assumed, and nothing is asserted at `β = β_c`.
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

/-- The raw power-law kernel on `ℤ^d` is the even displacement profile
`z ↦ (if z = 0 then 0 else ‖z‖ ^ (-(d+α)))`: this is the form in which the transitive sharpness
theorem of `PercLib.Models.chi_lt_top_of_lt_globalCriticalIntensity_powerLaw` is stated. -/
theorem rawKernel_displacement (hα : 0 < α) (x y : Fin d → ℤ) :
    radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) s(x, y) =
      Real.toNNReal (if y - x = 0 then 0 else ‖y - x‖ ^ (-((d : ℝ) + α))) := by
  rw [PercLib.Percolation.Bond.Exploration.BFS.radialKernel_powerLaw_mk hα]
  split_ifs with h
  · have hne : -((d : ℝ) + α) ≠ 0 := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    rw [h, norm_zero, Real.zero_rpow hne, Real.toNNReal_zero]
  · rfl

/-- **Sharpness at strict subcriticality, raw law.** Below the global critical intensity of the
power-law kernel the raw full-lattice susceptibility is finite at every vertex. -/
theorem chi_lt_top_of_lt_globalCriticalIntensity_raw (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)))) :
    ∀ x : Fin d → ℤ, chi (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) x < ⊤ :=
  (PercLib.Models.chi_lt_top_of_lt_globalCriticalIntensity_powerLaw hd hα _
    (rawKernel_displacement (d := d) (α := α) hα)).1 β hβ

/-- **The uniform susceptibility hypothesis, discharged on the raw law.** The raw power-law kernel
is translation invariant, so its susceptibility does not depend on the root; by
`chi_lt_top_of_lt_globalCriticalIntensity_raw` each value is finite, hence the supremum is. -/
theorem iSup_chi_ne_top_raw (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)))) :
    (⨆ x : Fin d → ℤ, chi (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) x) ≠ ⊤ := by
  have hT := PercLib.Models.transitive_of_translationInvariant
    (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)))
    (fun z => Real.toNNReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))))
    (rawKernel_displacement (d := d) (α := α) hα)
  have hconst : ∀ x : Fin d → ℤ, chi (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) x =
      chi (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) 0 :=
    fun x => chi_eq_of_transitive _ hT β x 0
  have hfun : (fun x : Fin d → ℤ => chi (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) x) =
      fun _ => chi (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) 0 :=
    funext hconst
  rw [hfun, iSup_const]
  exact ne_of_lt (chi_lt_top_of_lt_globalCriticalIntensity_raw hd hα hβ 0)

/-- **Uncut natural moments at strict subcriticality.** Every positive order moment of the cluster
of any vertex is finite on the raw full-lattice power-law law, for every `β < β_c`. -/
theorem lintegral_encard_pow_raw_ne_top (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (o : Fin d → ℤ) (k : ℕ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β)) ≠ ⊤ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  refine ne_top_of_le_ne_top ?_
    (lintegral_encard_pow_le_iSup (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) k hk o)
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ne_of_lt (chi_lt_top_of_lt_globalCriticalIntensity_raw hd hα hβ o)))
    (ENNReal.pow_ne_top (iSup_chi_ne_top_raw hd hα hβ))

/-- **Uncut real moments at strict subcriticality**, with the tree-graph constant of
`PercLib.Percolation.Bond.lintegral_ofReal_encard_toNat_cluster_pow_le`. -/
theorem lintegral_ofReal_encard_toNat_cluster_pow_le_raw (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (o : Fin d → ℤ) (m : ℕ) (hm : 1 ≤ m) :
    ∫⁻ ω, ENNReal.ofReal (((cluster ω o).encard.toNat : ℝ) ^ m) ∂law (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * (chi (intensityProfile
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α))) β) o).toReal *
        (⨆ x : Fin d → ℤ, chi (intensityProfile
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α))) β) x).toReal ^ (2 * m - 2)) :=
  PercLib.Percolation.Bond.lintegral_ofReal_encard_toNat_cluster_pow_le _ o
    (iSup_chi_ne_top_raw hd hα hβ) m hm

/-- **Finite exponential cluster moments at strict subcriticality.** -/
theorem lintegral_exp_encard_cluster_le_raw (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (o : Fin d → ℤ) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s ≤ (2 * (⨆ x : Fin d → ℤ, chi (intensityProfile
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))) β) x).toReal ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * ((cluster ω o).encard.toNat : ℝ))) ∂law (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) ≤
      ENNReal.ofReal (1 + (chi (intensityProfile
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α))) β) o).toReal /
        (⨆ x : Fin d → ℤ, chi (intensityProfile
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α))) β) x).toReal ^ 2 *
        (1 - Real.sqrt (1 - 2 * s * (⨆ x : Fin d → ℤ, chi (intensityProfile
          (radialKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α))) β) x).toReal ^ 2))) :=
  PercLib.Percolation.Bond.lintegral_exp_encard_cluster_le _ o
    (iSup_chi_ne_top_raw hd hα hβ) hs hs1

/-! ### The cut-off exhaustion: uniform bound and exact supremum

The cut-off kernel `cutoffKernel N K ρ = radialKernel N (cutoffProfile K ρ)` is the closed-ball
selector `s ≤ ρ` of the profile.  Its moments are monotone in `ρ` and dominated by the raw moment
of the same order at every scale; the supremum over the scale is the raw moment. -/

/-- **Uniform cut-off domination at every scale** (no hypothesis on the size of the scale). -/
theorem cutoff_pow_le_raw (β : ℝ≥0) (o : Fin d → ℤ) (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile
        (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) ≤
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂law (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) :=
  PercLib.Models.LongRange.lintegral_cutoffKernel_encard_cluster_pow_le
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (hK := fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le) hρ β o k

/-- **A single finite constant bounds every cut-off moment at strict subcriticality.** -/
theorem exists_uniform_cutoff_pow_bound_raw (hd : 1 ≤ d) (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))))
    (o : Fin d → ℤ) (p : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂law (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β)) ≤ M ∧
      ∀ ρ : ℝ, 0 < ρ →
        (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ (p + 1) ∂law (intensityProfile
          (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) ≤ M := by
  refine ⟨_, lintegral_encard_pow_raw_ne_top hd hα hβ o (p + 1), le_rfl,
    fun ρ hρ => (cutoff_pow_le_raw β o (p + 1) hρ).trans le_rfl⟩

/-- **The exhaustion has no boundary error in the limit**: the raw moment is the supremum of the
cut-off moments over the scale, for every parameter and every order. -/
theorem iSup_cutoff_pow_eq_raw (hα : 0 < α) (β : ℝ≥0) (o : Fin d → ℤ) (p : ℕ) :
    (⨆ ρ : ℝ, ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (intensityProfile
        (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α)) ρ) β)) =
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p ∂law (intensityProfile
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) β) :=
  PercLib.Models.LongRange.iSup_lintegral_cutoffKernel_encard_cluster_pow_eq
    (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (fun _ ht => (powerLawProfile_pos (c := 1) one_pos ht).le)
    (PercLib.Models.LongRange.antitoneOn_powerLawProfile zero_le_one
      (by positivity))
    (PercLib.Models.LongRange.tendsto_powerLawProfile_atTop (by positivity)) β o p


end PercLib.Models.LongRange.CutoffExhaustion
