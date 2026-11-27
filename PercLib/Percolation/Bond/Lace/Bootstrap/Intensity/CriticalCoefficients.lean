/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Intensity.CriticalExpansion
public import PercLib.Percolation.Bond.Lace.Expansion.KernelContinuity

/-!
# Sharp coefficient mass at the actual critical point

## Main results

The subcritical all-order coefficient bound passes to the actual critical
profile by joint coefficient continuity. The estimate retains `44/d`, and the
cosine-weighted all-order mass retains one third of the symbol deficit. Neither
result assumes finite critical susceptibility.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond.Lace

/-- Every bounded spatial moment of the actual canonical coefficients is
continuous from below at the critical nearest-neighbour profile. -/
theorem continuousWithinAt_nn_critical_coefficient_moment {d : ℕ} (hd : 50000 ≤ d)
    (x : Fin d → ℤ) (w : (Fin d → ℤ) → ℝ) (C : ℝ) (hw : ∀ y, |w y| ≤ C) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    ContinuousWithinAt (fun r : Sym2 (Fin d → ℤ) → unitInterval =>
      ∑' n : ℕ, ∑' y, w y * (laceCoefficient r n x y).toReal) (Iic q) q := by
  apply continuousWithinAt_tsum_mul_laceCoefficient_toReal_Iic_of_diagram_bounds
    _ x (ENNReal.ofReal (1 / 855 : ℝ)) (ENNReal.ofReal (1 / 1712 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top
    (nn_critical_diagramTransfer_mass_le_one_div hd)
    (nn_critical_diagramTerminal_mass_le_one_div hd)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (nn_critical_diagramInitial_mass_le hd x))
    (ae_finite_cluster_nearestNeighbor_critical hd) w C hw

private theorem weighted_coefficient_total_toReal {V : Type*}
    (q : Sym2 V → unitInterval) (x : V) (w : V → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hf : (∑' n : ℕ, ∑' y, ENNReal.ofReal (w y) * laceCoefficient q n x y) ≠ ⊤) :
    (∑' n : ℕ, ∑' y, ENNReal.ofReal (w y) * laceCoefficient q n x y).toReal =
      ∑' n : ℕ, ∑' y, w y * (laceCoefficient q n x y).toReal := by
  have hn (n : ℕ) : (∑' y, ENNReal.ofReal (w y) * laceCoefficient q n x y) ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top hf n
  rw [ENNReal.tsum_toReal_eq hn]
  apply tsum_congr
  intro n
  rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top (hn n))]
  apply tsum_congr
  intro y
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw y)]

private theorem coefficient_total_toReal {V : Type*}
    (q : Sym2 V → unitInterval) (x : V)
    (hf : (∑' n : ℕ, ∑' y, laceCoefficient q n x y) ≠ ⊤) :
    (∑' n : ℕ, ∑' y, laceCoefficient q n x y).toReal =
      ∑' n : ℕ, ∑' y, (laceCoefficient q n x y).toReal := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    weighted_coefficient_total_toReal q x (fun _ => 1) (fun _ => zero_le_one)
      (by simpa only [ENNReal.ofReal_one, one_mul] using hf)

private theorem critical_coefficient_moment_le {d : ℕ} (hd : 50000 ≤ d)
    (x : Fin d → ℤ) (w : (Fin d → ℤ) → ℝ) (C : ℝ) (hw : ∀ y, |w y| ≤ C)
    (B : ℝ) (hbound : ∀ β : ℝ≥0,
      chi (intensityProfile (nearestNeighborIntensity d) β) 0 ≠ ⊤ →
      (∑' n : ℕ, ∑' y, w y *
        (laceCoefficient (intensityProfile (nearestNeighborIntensity d) β) n x y).toReal) ≤ B) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' n : ℕ, ∑' y, w y * (laceCoefficient q n x y).toReal) ≤ B := by
  let q := intensityProfile (nearestNeighborIntensity d)
    (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let b := (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  have hbfinite := rootCriticalIntensity_nearestNeighbor_ne_top hd
  have hbone : (1 : ℝ≥0) ≤ b := by
    apply ENNReal.coe_le_coe.mp
    simpa only [b, ENNReal.coe_one, ENNReal.coe_toNNReal hbfinite] using
      one_le_rootCriticalIntensity_nearestNeighbor d
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le (by norm_num) hbone
  have hclosure : b ∈ closure (Ioo 0 b) := by
    rw [closure_Ioo hb.ne]
    exact ⟨hb.le, le_rfl⟩
  obtain ⟨β, hβ, hlim⟩ := mem_closure_iff_seq_limit.mp hclosure
  have hchi (n : ℕ) : chi (intensityProfile (nearestNeighborIntensity d) (β n)) 0 ≠ ⊤ :=
    chi_nearestNeighborIntensity_ne_top_below_critical hd (β n) (hβ n).2
  have hp : Tendsto (fun n => intensityProfile (nearestNeighborIntensity d) (β n))
      atTop (𝓝[Iic q] q) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · apply tendsto_pi_nhds.mpr
      intro e
      have he : Continuous (fun t : ℝ≥0 => intensityProfile (nearestNeighborIntensity d) t e) :=
        (continuous_intensityProfile (nearestNeighborIntensity d) e).subtype_mk _
      exact he.continuousAt.tendsto.comp hlim
    · exact Eventually.of_forall fun n e =>
        intensityProfile_mono (nearestNeighborIntensity d) (hβ n).2.le e
  have hm := (continuousWithinAt_nn_critical_coefficient_moment hd x w C hw).tendsto.comp hp
  exact le_of_tendsto hm (Eventually.of_forall fun n => hbound (β n) (hchi n))

/-- The actual critical all-order coefficient mass retains the subcritical
`44/d` bound, without assuming finite critical susceptibility. -/
theorem laceCoefficient_total_mass_nearestNeighbor_critical_le {d : ℕ} (hd : 50000 ≤ d) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' n : ℕ, ∑' y, laceCoefficient q n 0 y) ≤ ENNReal.ofReal (44 / (d : ℝ)) := by
  apply (ENNReal.le_ofReal_iff_toReal_le
    (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd 0) (by positivity)).mpr
  rw [coefficient_total_toReal _ _
    (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd 0)]
  have h := critical_coefficient_moment_le hd 0 (fun _ => 1) 1
    (fun _ => by norm_num) (44 / (d : ℝ)) ?_
  · simpa only [one_mul] using h
  intro β hchi
  simp only [one_mul]
  have h := laceCoefficient_mass_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [coefficient_total_toReal _ _ hf, ENNReal.toReal_ofReal (by positivity)] at ht
  exact ht

/-- The actual critical cosine-weighted coefficient mass is at most one third
of the nearest-neighbour symbol deficit, including all orders and zero deficit. -/
theorem laceCoefficient_weighted_mass_nearestNeighbor_critical_le {d : ℕ}
    (hd : 50000 ≤ d) (k : Fin d → ℝ) :
    let q := intensityProfile (nearestNeighborIntensity d)
      (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
    (∑' n : ℕ, ∑' y : Fin d → ℤ,
      ENNReal.ofReal (1 - Real.cos (∑ i, k i * (y i : ℝ))) * laceCoefficient q n 0 y) ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 - nearestNeighborSymbol k)) := by
  let q := intensityProfile (nearestNeighborIntensity d)
    (rootCriticalIntensity (nearestNeighborIntensity d) 0).toNNReal
  let w (y : Fin d → ℤ) := 1 - Real.cos (∑ i, k i * (y i : ℝ))
  have hw0 (y : Fin d → ℤ) : 0 ≤ w y := sub_nonneg.mpr (Real.cos_le_one _)
  have hw2 (y : Fin d → ℤ) : |w y| ≤ 2 := by
    rw [abs_of_nonneg (hw0 y)]
    dsimp only [w]
    linarith [Real.neg_one_le_cos (∑ i, k i * (y i : ℝ))]
  have hB0 : 0 ≤ (1 / 3 : ℝ) * (1 - nearestNeighborSymbol k) :=
    mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((le_abs_self _).trans
        (nearestNeighborSymbol_abs_le_one (by omega) k)))
  have hf : (∑' n : ℕ, ∑' y, ENNReal.ofReal (w y) * laceCoefficient q n 0 y) ≠ ⊤ :=
    cosine_weightedCoefficientMass_ne_top q 0 (fun y => ∑ i, k i * (y i : ℝ))
      (tsum_laceCoefficient_all_mass_nearestNeighbor_critical_ne_top hd 0)
  apply (ENNReal.le_ofReal_iff_toReal_le hf hB0).mpr
  rw [weighted_coefficient_total_toReal q 0 w hw0 hf]
  apply critical_coefficient_moment_le hd 0 w 2 hw2
  intro β hchi
  have hweak := (fourierBootstrap_nearestNeighborIntensity_le_of_chi_ne_top hd β hchi).trans
    (by norm_num : (17 : ℝ) / 10 ≤ 2)
  have h : (∑' n : ℕ, ∑' y,
      ENNReal.ofReal (w y) *
        laceCoefficient (intensityProfile (nearestNeighborIntensity d) β) n 0 y) ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 - nearestNeighborSymbol k)) := by
    rw [intensityProfile_nearestNeighborIntensity] at hchi hweak ⊢
    exact nn_laceCoefficient_weighted_mass_le hd _ hchi hweak k
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [weighted_coefficient_total_toReal _ 0 w hw0 hfinite,
    ENNReal.toReal_ofReal hB0] at ht
  exact ht

end PercLib.Percolation.Bond.Lace
