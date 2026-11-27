/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Analysis.ContinuousBootstrap
public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.NearestNeighbor
public import PercLib.Percolation.Bond.Lace.Bootstrap.NNImprovement
public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Percolation.Bond.SusceptibilityEndpoint

/-!
# Closing the actual subcritical nearest-neighbour bootstrap

## Main results

Continuity and the proved model-specific improvement bound the actual bootstrap
at every finite-susceptibility intensity. No weak-bootstrap assumption remains
in the resulting theorem. The actual step mass then bounds normalized intensity,
proving a finite critical intensity with an explicit dimension-dependent upper
bound. Sharpness identifies that endpoint and its infinite susceptibility.
-/

@[expose] public section
noncomputable section

open Set PercLib.Analysis PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

/-- The actual nearest-neighbour bootstrap is uniformly bounded throughout the
finite-susceptibility regime; the weak bootstrap has been discharged by continuity. -/
@[tag "JN6H"]
theorem fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0)
    (hchi : chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤) :
    fourierBootstrap (intensityProfile (nearestNeighborIntensity d) β) ≤ 17 / 10 := by
  have hdpos : 0 < d := by omega
  have hfin (t : ℝ≥0) (ht : t ∈ Icc 0 β) :
      chi (intensityProfile (nearestNeighborIntensity d) t) 0 ≠ ⊤ :=
    ne_top_of_le_ne_top hchi (chi_mono
      (fun e => intensityProfile_mono (nearestNeighborIntensity d) ht.2 e) 0)
  have hf : ContinuousOn (fun t : ℝ≥0 =>
      fourierBootstrap (intensityProfile (nearestNeighborIntensity d) t)) (Icc 0 β) :=
    fun t ht => (continuousAt_fourierBootstrap_nearestNeighborIntensity hdpos
      (hfin t ht)).continuousWithinAt
  have hs : fourierBootstrap (intensityProfile (nearestNeighborIntensity d) 0) ≤ 2 := by
    simpa only [show intensityProfile (nearestNeighborIntensity d) 0 = (fun _ => 0) from
      funext (intensityProfile_zero _), fourierBootstrap_zero_profile] using
      (by norm_num : (1 : ℝ) ≤ 2)
  have hi (t : ℝ≥0) (ht : t ∈ Icc 0 β)
      (hw : fourierBootstrap (intensityProfile (nearestNeighborIntensity d) t) ≤ 2) :
      fourierBootstrap (intensityProfile (nearestNeighborIntensity d) t) ≤ 17 / 10 := by
    have hc := hfin t ht
    rw [intensityProfile_nearestNeighborIntensity] at hc hw ⊢
    exact nn_fourierBootstrap_improves hd (nearestNeighborProbability d t) hc hw
  exact le_on_Icc_of_improves_le hf hs (by norm_num : (17 : ℝ) / 10 < 2) hi β
    ⟨bot_le, le_rfl⟩

/-- The actual all-order coefficient mass is uniformly small below criticality,
with the weak bootstrap hypothesis discharged. -/
theorem laceCoefficient_mass_nearestNeighborIntensity_le_of_chi_ne_top
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0)
    (hchi : chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤) :
    (∑' n : ℕ, ∑' y, laceCoefficient
      (intensityProfile (nearestNeighborIntensity d) β) n 0 y) ≤
        ENNReal.ofReal (44 / (d : ℝ)) := by
  have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  rw [intensityProfile_nearestNeighborIntensity] at hchi hw ⊢
  exact nn_laceCoefficient_total_mass_le (by omega) _ hchi
    (nn_step_mass_le_of_fourierBootstrap_le _ hw) ((fourierBootstrap_le_iff _ _).mp hw).2.1

/-- The finite-susceptibility step-mass correction retains its dimension dependence. -/
theorem step_mass_nearestNeighborIntensity_le_of_chi_ne_top
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0)
    (hchi : chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤) :
    2 * d * (nearestNeighborProbability d β : ℝ) ≤ (d : ℝ) / (d - 44) := by
  have hw := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  rw [intensityProfile_nearestNeighborIntensity] at hchi hw
  have hj := nn_step_mass_le_of_fourierBootstrap_le (nearestNeighborProbability d β) hw
  have hK := ((fourierBootstrap_le_iff _ _).mp hw).2.1
  have hn := nn_step_mass_le_normalization (by omega) _ hchi hj hK
  have hLam := (susceptibilityWalkParameter_mem_Ico _ hchi).2.le
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    _ ≤ 1 + 44 / ((d : ℝ) - 44) := hn.trans (add_le_add hLam le_rfl)
    _ = _ := by
      field_simp [show (d : ℝ) - 44 ≠ 0 by linarith]
      ring

/-- Every finite-susceptibility normalized intensity has an explicit finite upper bound. -/
theorem intensity_le_of_nearestNeighbor_chi_ne_top
    {d : ℕ} (hd : 50000 ≤ d) (β : ℝ≥0)
    (hchi : chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤) :
    (β : ℝ) ≤ 2 * d / (2 * d - 89) := by
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd44 : (0 : ℝ) < d - 44 := by linarith
  have hm : (d : ℝ) / (d - 44) < 2 * d := by
    have htwo : (d : ℝ) / (d - 44) ≤ 2 := (div_le_iff₀ hd44).mpr (by linarith)
    exact htwo.trans_lt (by linarith)
  refine (intensity_le_of_nearestNeighbor_step_mass_le (by omega) β hm
    (step_mass_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi)).trans_eq ?_
  field_simp
  ring

/-- The usual percolation threshold is finite and has the same explicit upper bound. -/
@[tag "V1P7"]
theorem rootCriticalIntensity_nearestNeighbor_le {d : ℕ} (hd : 50000 ≤ d) :
    rootCriticalIntensity (nearestNeighborIntensity d) 0 ≤
      ENNReal.ofReal (2 * (d : ℝ) / (2 * d - 89)) := by
  rw [rootCriticalIntensity_eq_sSup_chi_lt_top (nearestNeighborIntensity d)
    (nearestNeighborIntensity_transitive d) (summable_nearestNeighborIntensity d)]
  refine sSup_le ?_
  rintro _ ⟨β, hβ, rfl⟩
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (intensity_le_of_nearestNeighbor_chi_ne_top hd β hβ.ne)

/-- Finiteness is proved before converting the extended critical intensity to a real parameter. -/
theorem rootCriticalIntensity_nearestNeighbor_ne_top {d : ℕ} (hd : 50000 ≤ d) :
    rootCriticalIntensity (nearestNeighborIntensity d) 0 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rootCriticalIntensity_nearestNeighbor_le hd)

/-- Unit total rate gives the matching universal lower bound one. -/
theorem one_le_rootCriticalIntensity_nearestNeighbor (d : ℕ) :
    1 ≤ rootCriticalIntensity (nearestNeighborIntensity d) 0 := by
  simpa using inv_le_rootCriticalIntensity (nearestNeighborIntensity d) 1
    (rowSum_nearestNeighborIntensity_le_one d) 0

/-- Susceptibility diverges at the actual finite nearest-neighbour critical intensity. -/
theorem chi_nearestNeighbor_critical_eq_top {d : ℕ} (hd : 50000 ≤ d) :
    chi (intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal) 0 = ⊤ := by
  have heq := rootCriticalIntensity_eq_sSup_chi_lt_top (nearestNeighborIntensity d)
    (nearestNeighborIntensity_transitive d) (summable_nearestNeighborIntensity d) 0
  have h := chi_intensity_sSup_eq_top
    (fun x => nearestNeighborIntensity_transitive d 0 x)
    (show rowSum (fun e => (nearestNeighborIntensity d e : ℝ≥0∞)) 0 < ⊤ by
      rw [rowSum_nearestNeighborIntensity (by omega)]
      exact ENNReal.one_lt_top)
    (show sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) ''
        {β | chi (intensityProfile (nearestNeighborIntensity d) β) 0 < ⊤}) < ⊤ by
      rw [← heq]
      exact (rootCriticalIntensity_nearestNeighbor_ne_top hd).lt_top)
  simpa only [← heq] using h

end PercLib.Percolation.Bond.Lace
