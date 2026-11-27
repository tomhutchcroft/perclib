/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.JoiningBounds
public import PercLib.Percolation.Bond.Lace.Bootstrap.NNWeightedNorms
public import PercLib.Percolation.Bond.Lace.Diagrams.WeightedTotalMass

/-!
# The actual nearest-neighbour weighted coefficient series

The joining integral estimate and the explicit scalar norms control the whole
nonnegative weighted coefficient series at dimension at least `50000`.
The zeroth coefficient is included through its actual weighted-pair bound.

## Main results

* `nn_diagramMarkedJoiningSecondCore_le_small`: the actual joining bound with constant `4/5`.
* `nn_laceCoefficient_weighted_mass_le`: all coefficient orders have weighted mass
  at most one third of the nearest-neighbour symbol deficit.

The hypotheses concern finite susceptibility and the canonical weak bootstrap.
No diagram estimate or expansion identity is assumed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real PercLib.Analysis PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The actual joining core has a uniform weighted bound, derived from its
Fourier contraction and the proved walk integrals. -/
theorem nn_diagramMarkedJoiningSecondCore_le_small (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2)
    (k : Fin d → ℝ) (s t : (Fin d → ℤ) × (Fin d → ℤ)) :
    diagramMarkedJoiningSecondCore (homogeneousProfile (zdGraph d) p)
      (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) s t ≤
        ENNReal.ofReal ((4 / 5 : ℝ) * (1 - nearestNeighborSymbol k)) := by
  let q := homogeneousProfile (zdGraph d) p
  let r := susceptibilityWalkParameter q
  let S := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
    nearestNeighborResolvent r l ^ 3
  let B := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
    nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3
  have hdR : (50000 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < d := by omega
  have hparts := (fourierBootstrap_le_iff q 2).mp hweak
  have hj := nn_step_mass_le_1001_div_1000 hd p hchi
    (nn_step_mass_le_of_fourierBootstrap_le p hweak) hparts.2.1
  have hj0 : 0 ≤ 2 * d * (p : ℝ) := mul_nonneg (by positivity) p.2.1
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hr2 : r ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hr.1 hr.2.le 2
  have hS0 : 0 ≤ S := mul_nonneg (by positivity)
    (integral_nonneg fun l => pow_nonneg (nearestNeighborResolvent_pos hd0 hr l).le 3)
  have hS : S ≤ 1001 / 1000 := by
    have h := integral_nearestNeighborResolvent_cube_le_refined (by omega : 1000 ≤ d) hr
    have hc : (253 : ℝ) / (84 * d) ≤ 1 / 1000 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    have hm := mul_le_of_le_one_left (show 0 ≤ 253 / (84 * (d : ℝ)) by positivity) hr2
    dsimp only [S]
    linarith
  have hS2 := pow_le_pow_left₀ hS0 hS 2
  have hB0 : 0 ≤ B := mul_nonneg (by positivity)
    (integral_nonneg fun l => mul_nonneg (sq_nonneg _)
      (pow_nonneg (nearestNeighborResolvent_pos hd0 hr l).le 3))
  have hB : B ≤ 53 / (105 * 50000) := by
    have h : B ≤ 53 / (105 * (d : ℝ)) := by
      simpa only [B, nearestNeighborSymbol, nearestNeighborResolvent, inv_pow, div_eq_mul_inv]
        using integral_nearestNeighborSymbol_sq_mul_inv_cube_le (by omega : 1000 ≤ d) hr.1 hr.2
    apply h.trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hcoeff : 300 * (2 * d * (p : ℝ)) ^ 2 * (2 : ℝ) ^ 8 * S ^ 2 * B ≤ 4 / 5 := by
    apply (mul_le_mul
      (mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hj2 (by norm_num : (0 : ℝ) ≤ 300))
          (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 8)) hS2 (sq_nonneg _) (by norm_num))
      hB hB0 (by norm_num)).trans
    norm_num
  apply (diagramMarkedJoiningSecondCore_le_nn_walk_integrals hd0 p hchi (by norm_num)
    hparts.2.1 hparts.2.2 k s t).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hcoeff
    (sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 k)).2)

private theorem nn_weighted_series_numeric_bound (g : ℝ≥0∞) :
    let r := ENNReal.ofReal (1 / 830 : ℝ)
    let c := ENNReal.ofReal (1001 / 1000 : ℝ)
    let m := ENNReal.ofReal (3 / 5000 : ℝ)
    let gamma := ENNReal.ofReal (9 / 10000 : ℝ)
    let R := (1 - r)⁻¹
    let E := (1 - r ^ 2)⁻¹
    let A := 5 * r * R + 2 * r ^ 2 * R ^ 2
    let B := R * R * (5 + 2 * r * R + 2 * r * R)
    let C := A + r ^ 2 * E * R * (7 + 4 * r ^ 2 * E + 2 * r * R) +
      c * r * E * R * (5 + 4 * r ^ 2 * E + 2 * r * R)
    let O := r * E * R * (7 + 4 * r ^ 2 * E + 2 * r * R)
    let F := 3 * (c * m + m * c + m * m) + 2 * (gamma + m) +
      c * m * A + c * m * A + c * c * C + c * c * m * m * B
    ENNReal.ofReal (1 / 80 : ℝ) * g +
      (ENNReal.ofReal (1 / 80 : ℝ) * g + F * (16 * g) +
        c * c * (ENNReal.ofReal (4 / 5 : ℝ) * g) * O) ≤ ENNReal.ofReal (1 / 3 : ℝ) * g := by
  have hR : (1 - ENNReal.ofReal (1 / 830 : ℝ))⁻¹ = ENNReal.ofReal (830 / 829 : ℝ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hE : (1 - ENNReal.ofReal (1 / 830 : ℝ) ^ 2)⁻¹ =
      ENNReal.ofReal (688900 / 688899 : ℝ) := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  let r := ENNReal.ofReal (1 / 830 : ℝ)
  let c := ENNReal.ofReal (1001 / 1000 : ℝ)
  let m := ENNReal.ofReal (3 / 5000 : ℝ)
  let gamma := ENNReal.ofReal (9 / 10000 : ℝ)
  let R := (1 - r)⁻¹
  let E := (1 - r ^ 2)⁻¹
  let A := 5 * r * R + 2 * r ^ 2 * R ^ 2
  let B := R * R * (5 + 2 * r * R + 2 * r * R)
  let C := A + r ^ 2 * E * R * (7 + 4 * r ^ 2 * E + 2 * r * R) +
    c * r * E * R * (5 + 4 * r ^ 2 * E + 2 * r * R)
  let O := r * E * R * (7 + 4 * r ^ 2 * E + 2 * r * R)
  let F := 3 * (c * m + m * c + m * m) + 2 * (gamma + m) +
    c * m * A + c * m * A + c * c * C + c * c * m * m * B
  change ENNReal.ofReal (1 / 80 : ℝ) * g +
    (ENNReal.ofReal (1 / 80 : ℝ) * g + F * (16 * g) +
      c * c * (ENNReal.ofReal (4 / 5 : ℝ) * g) * O) ≤ _
  calc
    _ = (2 * ENNReal.ofReal (1 / 80 : ℝ) + F * 16 +
        c * c * ENNReal.ofReal (4 / 5 : ℝ) * O) * g := by ring
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      dsimp only [F, C, B, A, O, R, E, r, c, m, gamma]
      rw [hR, hE]
      simp (disch := positivity) only [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul,
        ← ENNReal.ofReal_add, ← ENNReal.ofReal_pow]
      exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- The actual full weighted coefficient series is at most one third of the
nearest-neighbour symbol deficit, including order zero. -/
theorem nn_laceCoefficient_weighted_mass_le (hd : 50000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hweak : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ 2) (k : Fin d → ℝ) :
    (∑' n : ℕ, ∑' y : Fin d → ℤ,
      ENNReal.ofReal (1 - cos (∑ i, k i * (y i : ℝ))) *
        laceCoefficient (homogeneousProfile (zdGraph d) p) n 0 y) ≤
      ENNReal.ofReal ((1 / 3 : ℝ) * (1 - nearestNeighborSymbol k)) := by
  classical
  let q := homogeneousProfile (zdGraph d) p
  let w : (Fin d → ℤ) → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - cos (∑ i, k i * (y i : ℝ)))
  let g := ENNReal.ofReal (1 - nearestNeighborSymbol k)
  let r := ENNReal.ofReal (1 / 830 : ℝ)
  let c := ENNReal.ofReal (1001 / 1000 : ℝ)
  let m := ENNReal.ofReal (3 / 5000 : ℝ)
  let gamma := ENNReal.ofReal (9 / 10000 : ℝ)
  let R := (1 - r)⁻¹
  let E := (1 - r ^ 2)⁻¹
  let A := 5 * r * R + 2 * r ^ 2 * R ^ 2
  let B := R * R * (5 + 2 * r * R + 2 * r * R)
  let C := A + r ^ 2 * E * R * (7 + 4 * r ^ 2 * E + 2 * r * R) +
    c * r * E * R * (5 + 4 * r ^ 2 * E + 2 * r * R)
  let O := r * E * R * (7 + 4 * r ^ 2 * E + 2 * r * R)
  let F := 3 * (c * m + m * c + m * m) + 2 * (gamma + m) +
    c * m * A + c * m * A + c * c * C + c * c * m * m * B
  have hj := nn_step_mass_le_of_fourierBootstrap_le p hweak
  have hK := ((fourierBootstrap_le_iff q 2).mp hweak).2.1
  have hα : (∑' a, diagramInitial q 0 a) ≤ c :=
    nn_diagramInitial_mass_le_1001_div_1000 hd p hchi hj hK
  have hΔ : (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ c :=
    nn_triangle_le_1001_div_1000 hd p hchi hj hK
  have ha : (∑' a : (Fin d → ℤ) × (Fin d → ℤ),
      if a.2 = 0 then 0 else diagramInitial q 0 a) ≤ m :=
    nn_nontrivial_initial_mass_le_three_div_5000 hd p hchi hj hK
  have hΓ : (∑' a : (Fin d → ℤ) × (Fin d → ℤ), if a = (0, 0) then 0 else
      tau q 0 a.1 * tau q a.1 a.2 * tau q a.2 0) ≤ gamma :=
    nn_nontrivial_triangle_mass_le_nine_div_10000 hd p hchi hj hK
  have hMd0 : (∑' b, diagramConnector q (0, 0) b * tau q b.1 b.2) ≤ m :=
    nn_diagramConnector_mass_le_three_div_5000 hd p hchi hj hK (0, 0)
  have hW0 : diagramWeightedPair q w 0 ≤ ENNReal.ofReal (1 / 80 : ℝ) * g := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 80)] using
      nn_diagramWeightedPair_zero_le_small hd p hchi hweak k
  have hW : (⨆ z, diagramWeightedPair q w z) ≤ 16 * g := by
    apply iSup_le
    intro z
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16), ENNReal.ofReal_ofNat] using
      nn_diagramWeightedPair_le_small hd p hchi hweak k z
  have hH : (⨆ a, ⨆ b, diagramMarkedJoiningSecondCore q w a b) ≤
      ENNReal.ofReal (4 / 5 : ℝ) * g := by
    apply iSup_le
    intro a
    apply iSup_le
    intro b
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 5)] using
      nn_diagramMarkedJoiningSecondCore_le_small hd p hchi hweak k a b
  have hJ : (∑' v, offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0 v) ≤ c := by
    simp_rw [q, nn_offDiagonal_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun z =>
      (homogeneousProfile (zdGraph d) p s(0, z)).2.1) (summable_homogeneous_zdGraph p)]
    have hs := tsum_homogeneous_zdGraph_mul (d := d) p (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, mul_one] at hs
    apply ENNReal.ofReal_le_ofReal
    rw [hs]
    convert nn_step_mass_le_1001_div_1000 hd p hchi hj hK using 1
    push_cast
    ring
  have hsource := tsum_laceCoefficient_positive_character_weight_mass_le q
    (homogeneous_zdGraph_add p) (latticeCharacter k) r r m m
    (nn_diagramTransfer_mass_le_one_div_830 hd p hchi hj hK)
    (nn_diagramInterior_connector_mass_le_one_div_830 hd p hchi hj hK)
    (nn_diagramConnector_mass_le_three_div_5000 hd p hchi hj hK)
    (nn_diagramConnector_reverse_mass_le_three_div_5000 hd p hchi hj hK)
  dsimp only at hsource
  simp only [latticeCharacter_re] at hsource
  have hpos : (∑' n : ℕ, ∑' y, w y * laceCoefficient q (n + 1) 0 y) ≤
      ENNReal.ofReal (1 / 80 : ℝ) * g + F * (16 * g) +
        c * c * (ENNReal.ofReal (4 / 5 : ℝ) * g) * O := by
    apply hsource.trans
    dsimp only [F, C, B, A, O, R, E]
    gcongr <;> first
      | solve
        | convert ha using 1
          apply tsum_congr
          intro a
          by_cases h : a.2 = 0 <;> simp [h]
      | solve
        | convert hΓ using 1
          apply tsum_congr
          intro a
          by_cases h : a = (0, 0) <;> simp [h]
  have hzero : (∑' y, w y * piZero q 0 y) ≤ ENNReal.ofReal (1 / 80 : ℝ) * g :=
    (tsum_weight_mul_piZero_le_weightedPair q w (by simp [w])).trans hW0
  change (∑' n : ℕ, ∑' y, w y * laceCoefficient q n 0 y) ≤ _
  rw [tsum_laceCoefficient_character_weight_eq_piZero_add]
  apply (add_le_add hzero hpos).trans
  have hn := nn_weighted_series_numeric_bound g
  dsimp only at hn
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 3)] using hn

end PercLib.Percolation.Bond.Lace
