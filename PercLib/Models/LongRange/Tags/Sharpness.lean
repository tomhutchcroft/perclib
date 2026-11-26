/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for sharpness of translation-invariant long-range percolation on `ℤ^d`.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.FiniteSusceptibility

/-!
# Sharpness on `ℤ^d`: correspondence

Wiki correspondence for sharpness of translation-invariant long-range percolation on `ℤ^d`.

## Main results

* `sharpness_translationInvariant_int`
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-- Sharpness on `ℤ^d` for a summable translation-invariant kernel with
`0 < β_c < ∞`: every root threshold equals `β_c`, the susceptibility is finite below `β_c`,
and above `β_c` the probability of an infinite cluster is at least `(β - β_c)/β`. -/
@[tag "DYUM"]
theorem sharpness_translationInvariant_int {d : ℕ} (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (k : (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = k (y - x)) (hk : ∑' z, (k z : ℝ≥0∞) < ⊤)
    (_hβc : 0 < globalCriticalIntensity J ∧ globalCriticalIntensity J < ⊤) :
    (∀ x, rootCriticalIntensity J x = globalCriticalIntensity J) ∧
    (∀ β : ℝ≥0, (β : ℝ≥0∞) < globalCriticalIntensity J → ∀ x,
      chi (intensityProfile J β) x < ⊤) ∧
    (∀ β : ℝ≥0, globalCriticalIntensity J < β → ∀ x,
        ((β : ℝ≥0∞) - globalCriticalIntensity J) / β ≤
          law (intensityProfile J β) {ω | (cluster ω x).Infinite}) := by
  obtain ⟨hchi, hroot⟩ := chi_lt_top_of_lt_globalCriticalIntensity_int J k hJ hk
  refine ⟨hroot, hchi, fun β hβ x => ?_⟩
  have h := one_sub_div_le_law_cluster_infinite J (transitive_of_translationInvariant J k hJ)
    (summable_rows_of_translationInvariant J k hJ hk) (o := x) (β := β)
    (by rw [hroot x]; exact hβ)
  rw [hroot x] at h
  have hβ0 : (β : ℝ≥0∞) ≠ 0 := (lt_of_le_of_lt bot_le hβ).ne'
  have hβt : (β : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc ((β : ℝ≥0∞) - globalCriticalIntensity J) / β
      = (β : ℝ≥0∞) / β - globalCriticalIntensity J / β :=
        ENNReal.sub_div (fun _ _ => hβ0)
    _ = 1 - globalCriticalIntensity J / β := by rw [ENNReal.div_self hβ0 hβt]
    _ ≤ _ := h

end PercLib.Models
