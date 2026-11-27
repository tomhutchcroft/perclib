/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Control
public import PercLib.Percolation.Bond.Lace.Bootstrap.NNMassImprovement
public import PercLib.Percolation.Bond.Lace.Bootstrap.WeightedPairUniform

/-!
# Explicit nearest-neighbour norms for weighted coefficient summation

At dimension at least `50000`, the proved scalar and weighted-pair estimates
have small rational bounds. The actual step mass is improved before it is used
in the weighted Fourier estimates. The two transfer directions remain separate.

## Main results

The initial and triangle masses are at most `1001/1000`; the two deleted connector
masses are at most `3/5000`; both transfer products are at most `1/830`.
The origin and uniform weighted-pair bounds have constants `1/80` and `16`.
These statements do not estimate the joining core or assert bootstrap closure.
-/

@[expose] public section
noncomputable section

open Real PercLib.Analysis PercLib.Models.Site
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The first component of the canonical bootstrap is the actual lattice step mass. -/
theorem nn_step_mass_le_of_fourierBootstrap_le (p : unitInterval) {K : ℝ}
    (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K) :
    2 * d * (p : ℝ) ≤ K := by
  have h := ((fourierBootstrap_le_iff _ _).mp hK).1
  rwa [rowSum_homogeneous_zdGraph,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) p.2.1)] at h

/-- The actual zero-frequency improvement gives the smaller step mass used below. -/
theorem nn_step_mass_le_1001_div_1000 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    2 * d * (p : ℝ) ≤ 1001 / 1000 := by
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hfrac : (44 : ℝ) / ((d : ℝ) - 44) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hlam := (susceptibilityWalkParameter_mem_Ico (homogeneousProfile (zdGraph d) p) hchi).2
  have h := nn_step_mass_le_normalization (by omega) p hchi hj hK
  linarith

/-- The actual uniform continuation is small enough for the dimension-dependent
transfer estimate, instead of retaining a fixed low-dimensional contraction bound. -/
theorem nn_step_tau_three_le_three_div_5000 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) (x : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    (J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤
      ENNReal.ofReal (3 / 5000 : ℝ) := by
  apply (nn_step_tau_three_le (by omega) p hchi hj hK x).trans (ENNReal.ofReal_le_ofReal ?_)
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_iff₀ (show (0 : ℝ) < 315 * d by positivity)).mpr
  linarith

/-- The actual initial mass is at most `1001/1000`. -/
theorem nn_diagramInitial_mass_le_1001_div_1000 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' a, diagramInitial (homogeneousProfile (zdGraph d) p) 0 a) ≤
      ENNReal.ofReal (1001 / 1000 : ℝ) := by
  apply (nn_diagramInitial_mass_le (by omega) p hchi hj hK).trans (ENNReal.ofReal_le_ofReal ?_)
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdiv : (8882 : ℝ) / (315 * d) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  linarith

/-- The actual full triangle is at most `1001/1000`. -/
theorem nn_triangle_le_1001_div_1000 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤
      ENNReal.ofReal (1001 / 1000 : ℝ) := by
  apply (nn_triangle_le (by omega) p hchi hj hK).trans (ENNReal.ofReal_le_ofReal ?_)
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdiv : (4441 : ℝ) / (105 * d) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  linarith

open Classical in
/-- Removing the certain initial diagonal leaves actual mass at most `3/5000`. -/
theorem nn_nontrivial_initial_mass_le_three_div_5000 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' a : (Fin d → ℤ) × (Fin d → ℤ),
      if a.2 = 0 then 0 else diagramInitial (homogeneousProfile (zdGraph d) p) 0 a) ≤
        ENNReal.ofReal (3 / 5000 : ℝ) := by
  classical
  have h := (nontrivial_initial_mass_le_step_tau_three_zero _
    (homogeneous_zdGraph_add p)).trans
      (nn_step_tau_three_le_three_div_5000 hd p hchi hj hK 0)
  convert h using 1
  apply tsum_congr
  intro a
  by_cases ha : a.2 = 0 <;> simp [ha]

/-- The actual forward deleted connector mass is at most `3/5000`. -/
theorem nn_diagramConnector_mass_le_three_div_5000 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' b, diagramConnector q a b * tau q b.1 b.2) ≤ ENNReal.ofReal (3 / 5000 : ℝ) :=
  (diagramConnector_mass_le_step_tau_three _ (homogeneous_zdGraph_add p) a).trans
    (nn_step_tau_three_le_three_div_5000 hd p hchi hj hK _)

/-- The actual reverse deleted connector mass is bounded independently. -/
theorem nn_diagramConnector_reverse_mass_le_three_div_5000
    (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' b, diagramConnector q b a * tau q b.1 b.2) ≤ ENNReal.ofReal (3 / 5000 : ℝ) :=
  (diagramConnector_reverse_mass_le_step_tau_three _ (homogeneous_zdGraph_add p) a).trans
    (nn_step_tau_three_le_three_div_5000 hd p hchi hj hK _)

open Classical in
/-- The actual nontrivial triangle retains its factor-three-halves improvement. -/
theorem nn_nontrivial_triangle_mass_le_nine_div_10000
    (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' a : (Fin d → ℤ) × (Fin d → ℤ), if a = (0, 0) then 0 else
      tau q 0 a.1 * tau q a.1 a.2 * tau q a.2 0) ≤ ENNReal.ofReal (9 / 10000 : ℝ) := by
  classical
  have h := (nontrivial_triangle_mass_le_three_halves_initial
    (homogeneousProfile (zdGraph d) p)).trans (mul_le_mul' le_rfl
      ((nontrivial_initial_mass_le_step_tau_three_zero _ (homogeneous_zdGraph_add p)).trans
        (nn_step_tau_three_le_three_div_5000 hd p hchi hj hK 0)))
  have hc : (3 / 2 : ℝ≥0∞) = ENNReal.ofReal (3 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num)] at h
  norm_num at h
  convert h using 1
  apply tsum_congr
  intro a
  by_cases ha : a = (0, 0) <;> simp [ha]

/-- The actual forward transfer uses the smaller dimension-dependent norms. -/
theorem nn_diagramTransfer_mass_le_one_div_830 (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    (∑' b, diagramTransfer (homogeneousProfile (zdGraph d) p) a b) ≤
      ENNReal.ofReal (1 / 830 : ℝ) := by
  refine (diagramTransfer_mass_le_two_mul_triangle_continuation _
    (homogeneous_zdGraph_add p) _ _ (nn_triangle_le_1001_div_1000 hd p hchi hj hK)
    (nn_step_tau_three_le_three_div_5000 hd p hchi hj hK) a).trans ?_
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The actual backward interior-connector product has its own small bound. -/
theorem nn_diagramInterior_connector_mass_le_one_div_830
    (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    (∑' b, ∑' c, diagramInterior (homogeneousProfile (zdGraph d) p) b c *
      diagramConnector (homogeneousProfile (zdGraph d) p) c a) ≤
        ENNReal.ofReal (1 / 830 : ℝ) := by
  refine (diagramInterior_connector_mass_le_two_mul_triangle_continuation _
    (homogeneous_zdGraph_add p) _ _ (nn_triangle_le_1001_div_1000 hd p hchi hj hK)
    (nn_step_tau_three_le_three_div_5000 hd p hchi hj hK) a).trans ?_
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The actual origin weighted pair has coefficient at most `1/80` times
its frequency deficit, after improving the actual step mass. -/
theorem nn_diagramWeightedPair_zero_le_small (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    diagramWeightedPair (homogeneousProfile (zdGraph d) p)
      (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) 0 ≤
        ENNReal.ofReal ((1 / 80 : ℝ) * (1 - nearestNeighborSymbol k)) := by
  let j : ℝ := 2 * d * (p : ℝ)
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < d := by omega
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hj0 : 0 ≤ j := mul_nonneg (by positivity) p.2.1
  have hj := nn_step_mass_le_1001_div_1000 hd p hchi
    (nn_step_mass_le_of_fourierBootstrap_le p hweak) ((fourierBootstrap_le_iff _ _).mp hweak).2.1
  change j ≤ 1001 / 1000 at hj
  have hp : (p : ℝ) ≤ 1001 / 100000000 := by
    have h := mul_le_mul_of_nonneg_right hdR p.2.1
    dsimp only [j] at hj
    nlinarith
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have h631 : (631 : ℝ) / (1260 * d) ≤ 631 / (1260 * 50000) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have h53 : (53 : ℝ) / (105 * d) ≤ 53 / (105 * 50000) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hfirst := mul_le_mul hj
    (add_le_add hp (mul_le_mul (mul_le_mul_of_nonneg_right hj2 (by norm_num : (0 : ℝ) ≤ 2))
      h631 (by positivity) (by norm_num))) (by positivity) (by norm_num)
  have hsecond := mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj2 (by norm_num : (0 : ℝ) ≤ 300))
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2)) h53 (by positivity) (by norm_num)
  have hcoeff : j * ((p : ℝ) + j ^ 2 * 2 * (631 / (1260 * (d : ℝ)))) +
      300 * j ^ 2 * 2 ^ 2 * (53 / (105 * (d : ℝ))) ≤ 1 / 80 := by
    apply (add_le_add hfirst hsecond).trans
    norm_num
  apply (diagramWeightedPair_nn_zero_le_ofReal_explicit (by omega) p hchi hweak k).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hcoeff
    (sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 k)).2)

/-- The actual weighted pair is uniformly bounded by `16` times its frequency
 deficit. The square-root walk gain is retained before numerical substitution. -/
theorem nn_diagramWeightedPair_le_small (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2)
    (k : Fin d → ℝ) (a : Fin d → ℤ) :
    diagramWeightedPair (homogeneousProfile (zdGraph d) p)
      (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) a ≤
        ENNReal.ofReal (16 * (1 - nearestNeighborSymbol k)) := by
  let q := homogeneousProfile (zdGraph d) p
  let j : ℝ := 2 * d * (p : ℝ)
  let r := susceptibilityWalkParameter q
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < d := by omega
  have hj0 : 0 ≤ j := mul_nonneg (by positivity) p.2.1
  have hj := nn_step_mass_le_1001_div_1000 hd p hchi
    (nn_step_mass_le_of_fourierBootstrap_le p hweak) ((fourierBootstrap_le_iff _ _).mp hweak).2.1
  change j ≤ 1001 / 1000 at hj
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hr2 : r ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hr.1 hr.2.le 2
  have hc2 : (379 : ℝ) / (252 * d) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hc3 : (253 : ℝ) / (84 * d) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hR2 : 1 + r ^ 2 * (379 / (252 * (d : ℝ))) ≤ 1001 / 1000 := by
    have h := mul_le_of_le_one_left (show 0 ≤ 379 / (252 * (d : ℝ)) by positivity) hr2
    linarith
  have hR3 : 1 + r ^ 2 * (253 / (84 * (d : ℝ))) ≤ 1001 / 1000 := by
    have h := mul_le_of_le_one_left (show 0 ≤ 253 / (84 * (d : ℝ)) by positivity) hr2
    linarith
  have hB : (53 : ℝ) / (105 * d) ≤ 53 / (105 * 50000) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hsqrt : sqrt ((53 / (105 * (d : ℝ))) *
      (1 + r ^ 2 * (253 / (84 * (d : ℝ))))) ≤ 2 / 625 := by
    apply (sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    apply (mul_le_mul hB hR3 (by positivity) (by norm_num)).trans
    norm_num
  have hcoeff : 2 * j * 2 ^ 2 * (1 + r ^ 2 * (379 / (252 * (d : ℝ))) +
      300 * sqrt ((53 / (105 * (d : ℝ))) *
        (1 + r ^ 2 * (253 / (84 * (d : ℝ)))))) ≤ 16 := by
    have hfac : 2 * j * (2 : ℝ) ^ 2 ≤ 2 * (1001 / 1000 : ℝ) * 2 ^ 2 := by
      nlinarith
    have hbracket : 1 + r ^ 2 * (379 / (252 * (d : ℝ))) +
        300 * sqrt ((53 / (105 * (d : ℝ))) *
          (1 + r ^ 2 * (253 / (84 * (d : ℝ))))) ≤ 1001 / 1000 + 300 * (2 / 625) := by
      linarith
    exact (mul_le_mul hfac hbracket (by positivity) (by norm_num)).trans (by norm_num)
  apply (diagramWeightedPair_nn_le_ofReal_explicit (by omega) p hchi hweak k a).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hcoeff
    (sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 k)).2)

end PercLib.Percolation.Bond.Lace
