/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.SharpnessThreshold

/-!
# Finite-set contraction and finite susceptibility: correspondence

Correspondence wrapper for the characterisation of finite susceptibility by finite-set
contraction and the critical blow-up, from `PercLib/Percolation/Bond/SharpnessThreshold.lean`.
No new definitions.

## Main results

* `chi_lt_top_iff_exists_boundaryFlux_lt_one_iff_and_tendsto_chi`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

open Classical in
/-- **Finite-set contraction characterizes finite susceptibility and gives critical
blow-up.** Let `J` have summable rows and be preserved by bijections acting transitively on
`V`. At every finite `β ≥ 0`, `χ_β(o) < ∞` iff some finite `T ∋ o` has `Φ_β(o,T) < 1`
iff `β < β_c`. If `β_c` is finite, `χ_{β_c}(o) = ∞` and `χ_β(o) → ∞` as `β ↑ β_c`. -/
@[tag "RDF0"]
theorem chi_lt_top_iff_exists_boundaryFlux_lt_one_iff_and_tendsto_chi (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hJ : ∀ u, Summable fun v => (J s(u, v) : ℝ)) (o : V) :
    (∀ β : ℝ≥0,
      (chi (intensityProfile J β) o < ⊤ ↔
        ∃ T : Finset V, o ∈ T ∧ boundaryFlux (intensityProfile J β) T o < 1) ∧
      ((∃ T : Finset V, o ∈ T ∧ boundaryFlux (intensityProfile J β) T o < 1) ↔
        (β : ℝ≥0∞) < rootCriticalIntensity J o)) ∧
    ∀ b : ℝ≥0, rootCriticalIntensity J o = b →
      chi (intensityProfile J b) o = ⊤ ∧
      Tendsto (fun β : ℝ≥0 => chi (intensityProfile J β) o) (𝓝[<] b) (𝓝 ⊤) :=
  ⟨fun β => ⟨chi_lt_top_iff_exists_boundaryFlux_lt_one J hT hJ o β,
      exists_boundaryFlux_lt_one_iff_lt_rootCriticalIntensity J hT hJ o β⟩,
    fun _ hb => ⟨chi_eq_top_of_rootCriticalIntensity_eq J hT hJ hb,
      tendsto_chi_nhdsLT_of_rootCriticalIntensity_eq J hT hJ hb⟩⟩

end PercLib.Percolation.Bond
