/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.SharpnessThreshold

/-!
# Sharpness for transitive summable intensities: correspondence

Correspondence wrapper for sharpness and the supercritical density bound, from
`PercLib/Percolation/Bond/Sharpness.lean` and
`PercLib/Percolation/Bond/SharpnessThreshold.lean`. No new definitions.

## Main results

* `rootCriticalIntensity_eq_sInf_and_chi_lt_top_and_density_ge`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

open Classical in
/-- **Sharpness and the supercritical density bound for transitive summable intensities.**
Let `J` have summable rows and be preserved by bijections acting transitively on `V`. Then
`β_c = t := inf {β ≥ 0 | Φ_β(o,T) ≥ 1 for every finite T ∋ o}` (`inf ∅ = ∞`); `χ_β(o) < ∞`
for finite `β < β_c`; for finite `β > β_c`, `P_β(|K_o| = ∞) ≥ 1 - β_c/β` and
`P_β(|K_o| = ∞) ≥ (β_c + 1)⁻¹ min {β - β_c, 1}`; and `β_c` equals the threshold for an
infinite cluster anywhere. -/
@[tag "L0TE"]
theorem rootCriticalIntensity_eq_sInf_and_chi_lt_top_and_density_ge (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    rootCriticalIntensity J o =
        sInf ((↑) '' {β : ℝ≥0 | ∀ T : Finset V, o ∈ T →
          1 ≤ boundaryFlux (intensityProfile J β) T o}) ∧
    (∀ β : ℝ≥0, (β : ℝ≥0∞) < rootCriticalIntensity J o →
      chi (intensityProfile J β) o < ⊤) ∧
    (∀ β : ℝ≥0, rootCriticalIntensity J o < β →
      1 - rootCriticalIntensity J o / β ≤
        law (intensityProfile J β) {ω | (cluster ω o).Infinite}) ∧
    (∀ β : ℝ≥0, rootCriticalIntensity J o < β →
      ((rootCriticalIntensity J o).toReal + 1)⁻¹ *
          min ((β : ℝ) - (rootCriticalIntensity J o).toReal) 1 ≤
        (law (intensityProfile J β)).real {ω | (cluster ω o).Infinite}) ∧
    rootCriticalIntensity J o = globalCriticalIntensity J :=
  ⟨rootCriticalIntensity_eq_sInf_one_le_boundaryFlux J hT hJ o,
    fun _ hβ => chi_lt_top_of_lt_rootCriticalIntensity J hT hJ hβ,
    fun _ hβ => one_sub_div_le_law_cluster_infinite J hT hJ hβ,
    fun _ hβ => inv_mul_min_le_law_real_cluster_infinite J hT hJ hβ,
    rootCriticalIntensity_eq_globalCriticalIntensity_of_transitive J hT o⟩

end PercLib.Percolation.Bond
