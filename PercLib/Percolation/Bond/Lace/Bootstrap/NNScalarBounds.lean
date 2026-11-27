/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.DiagramNorms
public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborIntegrals

/-!
# Explicit nearest-neighbour scalar diagram bounds

The hypotheses are finite susceptibility and the actual weak bootstrap bounds
on the step mass and Fourier ratio. The diagram estimates are derived from the
proved first-step expansion and weighted walk integrals, rather than assumed.

## Main results

The continuation triangle is bounded by `9197/(315d)`, its origin value by
`8882/(315d)`, and the full triangle by `1 + 4441/(105d)`. The actual forward
and backward diagram products consequently have a strict contraction bound.
-/

@[expose] public section
noncomputable section

open PercLib.Models.Site
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- Finite susceptibility makes the actual nearest-neighbour continuation
triangle finite at every displacement. -/
theorem nn_step_tau_three_ne_top (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤) (x : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    (J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≠ ⊤ := by
  dsimp only
  have hT : (∑' z, tau (homogeneousProfile (zdGraph d) p) 0 z) ≠ ⊤ := by
    rwa [← chi_eq_tsum_tau]
  apply addRingConvolution_ennreal_ne_top (nn_step_mass_ne_top p)
  rw [tsum_addRingConvolution_ennreal, tsum_addRingConvolution_ennreal]
  exact ENNReal.mul_ne_top hT (ENNReal.mul_ne_top hT hT)

/-- Real projection identifies the actual continuation triangle with the
real convolution to which the Fourier coefficient bounds apply. -/
theorem nn_step_tau_three_toReal (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤) (x : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    ((J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x).toReal =
      ((fun z => (q s(0, z) : ℝ)) ⋆ᵣ₊ ((fun z => (tau q 0 z).toReal) ⋆ᵣ₊
        ((fun z => (tau q 0 z).toReal) ⋆ᵣ₊ (fun z => (tau q 0 z).toReal)))) x := by
  let T := tau (homogeneousProfile (zdGraph d) p) 0
  have hT : (∑' z, T z) ≠ ⊤ := by rwa [chi_eq_tsum_tau] at hchi
  have hT2 : (∑' z, (T ⋆ᵣ₊ T) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hT
  have hT3 : (∑' z, (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hT2
  let J := offDiagonal (fun a b : Fin d → ℤ =>
    (unitInterval.toNNReal (homogeneousProfile (zdGraph d) p s(a, b)) : ℝ≥0∞)) 0
  change ((J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x).toReal = _
  rw [toReal_addRingConvolution_ennreal (f := J) (g := T ⋆ᵣ₊ (T ⋆ᵣ₊ T))
    (ENNReal.ne_top_of_tsum_ne_top (nn_step_mass_ne_top p))
    (ENNReal.ne_top_of_tsum_ne_top hT3)]
  simp only [toReal_addRingConvolution_ennreal (f := T) (g := T ⋆ᵣ₊ T)
      (ENNReal.ne_top_of_tsum_ne_top hT) (ENNReal.ne_top_of_tsum_ne_top hT2),
    toReal_addRingConvolution_ennreal (f := T) (g := T)
      (ENNReal.ne_top_of_tsum_ne_top hT) (ENNReal.ne_top_of_tsum_ne_top hT),
    J, nn_offDiagonal_toReal]
  rfl

private theorem nn_step_tau_three_toReal_le_profile_add (hd : 1000 ≤ d)
    (p : unitInterval) (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) (x : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    ((J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x).toReal ≤
      (q s(0, x) : ℝ) + 8882 / (315 * (d : ℝ)) := by
  let q := homogeneousProfile (zdGraph d) p
  let J : (Fin d → ℤ) → ℝ := fun z => (q s(0, z) : ℝ)
  let T : (Fin d → ℤ) → ℝ := fun z => (tau q 0 z).toReal
  have h := step_tau_three_toReal_le_firstStep_expansion q
    (homogeneous_zdGraph_add p) (nn_step_mass_ne_top p) hchi x
  dsimp only [q] at h
  simp only [nn_offDiagonal_toReal, Pi.add_apply] at h
  have h1 := (le_abs_self _).trans
    (abs_homogeneous_step_twice_tau_le hd p hchi (K := 2) (by norm_num) hK x)
  have h2 := (le_abs_self _).trans
    (abs_homogeneous_step_twice_tau_sq_le hd p hchi (K := 2) (by norm_num) hK x)
  have h3 := (le_abs_self _).trans
    (abs_homogeneous_step_twice_tau_cube_le hd p hchi (K := 2) (by norm_num) hK x)
  have hj0 : 0 ≤ 2 * d * (p : ℝ) := mul_nonneg (by positivity) p.2.1
  have hj2 : (2 * d * (p : ℝ)) ^ 2 ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
      _ = 4 := by norm_num
  have hcoeff : (2 * d * (p : ℝ)) ^ 2 * 2 * (631 / (1260 * (d : ℝ))) +
      (2 * d * (p : ℝ)) ^ 2 * 2 ^ 2 * (211 / (420 * (d : ℝ))) +
      (2 * d * (p : ℝ)) ^ 2 * 2 ^ 3 * (53 / (105 * (d : ℝ))) ≤
        8882 / (315 * (d : ℝ)) := by
    calc
      _ = (2 * d * (p : ℝ)) ^ 2 *
          (2 * (631 / (1260 * (d : ℝ))) + 2 ^ 2 * (211 / (420 * (d : ℝ))) +
            2 ^ 3 * (53 / (105 * (d : ℝ)))) := by ring
      _ ≤ 4 * (2 * (631 / (1260 * (d : ℝ))) + 2 ^ 2 * (211 / (420 * (d : ℝ))) +
          2 ^ 3 * (53 / (105 * (d : ℝ)))) := mul_le_mul_of_nonneg_right hj2 (by positivity)
      _ = _ := by ring
  dsimp only
  rw [nn_step_tau_three_toReal p hchi]
  change (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x ≤ J x + _
  change (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x ≤ J x + (J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) x +
    (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x + (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)))) x at h
  linarith only [h, h1, h2, h3, hcoeff]

/-- Under the weak bootstrap bound two, the actual continuation triangle is
at most `9197/(315d)` uniformly over all displacements. -/
theorem nn_step_tau_three_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) (x : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    (J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤
      ENNReal.ofReal (9197 / (315 * (d : ℝ))) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (nn_step_tau_three_ne_top p hchi x)
    (by positivity)).mpr
  have h := nn_step_tau_three_toReal_le_profile_add hd p hchi hj hK x
  have hx : (homogeneousProfile (zdGraph d) p s(0, x) : ℝ) ≤ p := by
    classical
    by_cases hx : s((0 : Fin d → ℤ), x) ∈ (zdGraph d).edgeSet
    · simp [homogeneousProfile, hx]
    · simp [homogeneousProfile, hx, p.2.1]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : (p : ℝ) ≤ 1 / d := (le_div_iff₀ hdpos).mpr (by nlinarith)
  calc
    _ ≤ (p : ℝ) + 8882 / (315 * (d : ℝ)) := h.trans (add_le_add hx le_rfl)
    _ ≤ 1 / (d : ℝ) + 8882 / (315 * (d : ℝ)) := add_le_add hp le_rfl
    _ = _ := by ring

/-- At zero the actual step kernel vanishes, saving `1/d` in the bound. -/
theorem nn_step_tau_three_zero_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    (J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) 0 ≤
      ENNReal.ofReal (8882 / (315 * (d : ℝ))) := by
  apply (ENNReal.le_ofReal_iff_toReal_le (nn_step_tau_three_ne_top p hchi 0)
    (by positivity)).mpr
  have h := nn_step_tau_three_toReal_le_profile_add hd p hchi hj hK 0
  have hz : (homogeneousProfile (zdGraph d) p s(0, (0 : Fin d → ℤ)) : ℝ) = 0 := by
    simp [homogeneousProfile]
  dsimp only at h
  rwa [hz, zero_add] at h

/-- The actual full triangle has the explicit origin constant `4441/105`. -/
theorem nn_triangle_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤
      ENNReal.ofReal (1 + 4441 / (105 * (d : ℝ))) := by
  refine (triangle_le_one_add_three_halves_step_tau_three _
    (homogeneous_zdGraph_add p)).trans ?_
  refine (add_le_add le_rfl (mul_le_mul' le_rfl
    (nn_step_tau_three_zero_le hd p hchi hj hK))).trans_eq ?_
  have hc : (3 / 2 : ℝ≥0∞) = ENNReal.ofReal (3 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 1
  ring

/-- A convenient uniform continuation bound at the same dimension threshold. -/
theorem nn_step_tau_three_le_three_hundredths (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) (x : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J := offDiagonal (fun a b : Fin d → ℤ =>
      (unitInterval.toNNReal (q s(a, b)) : ℝ≥0∞)) 0
    (J ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ ENNReal.ofReal (3 / 100 : ℝ) := by
  refine (nn_step_tau_three_le hd p hchi hj hK x).trans (ENNReal.ofReal_le_ofReal ?_)
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_iff₀ (show (0 : ℝ) < 315 * d by positivity)).mpr
  linarith

/-- The triangle is at most `21/20` already at dimension 1000. -/
theorem nn_triangle_le_twenty_one_twentieths (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' u, ∑' v, tau q 0 u * tau q u v * tau q v 0) ≤ ENNReal.ofReal (21 / 20 : ℝ) := by
  refine (nn_triangle_le hd p hchi hj hK).trans (ENNReal.ofReal_le_ofReal ?_)
  have hdR : (1000 : ℝ) ≤ d := by exact_mod_cast hd
  have hdiv : (4441 : ℝ) / (105 * d) ≤ 1 / 20 := by
    apply (div_le_iff₀ (show (0 : ℝ) < 105 * d by positivity)).mpr
    linarith
  linarith

/-- The actual forward deleted connector norm obeys the uniform model bound. -/
theorem nn_diagramConnector_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' b, diagramConnector q a b * tau q b.1 b.2) ≤
      ENNReal.ofReal (9197 / (315 * (d : ℝ))) :=
  (diagramConnector_mass_le_step_tau_three _ (homogeneous_zdGraph_add p) a).trans
    (nn_step_tau_three_le hd p hchi hj hK _)

/-- The actual reverse deleted connector norm is bounded separately. -/
theorem nn_diagramConnector_reverse_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    let q := homogeneousProfile (zdGraph d) p
    (∑' b, diagramConnector q b a * tau q b.1 b.2) ≤
      ENNReal.ofReal (9197 / (315 * (d : ℝ))) :=
  (diagramConnector_reverse_mass_le_step_tau_three _ (homogeneous_zdGraph_add p) a).trans
    (nn_step_tau_three_le hd p hchi hj hK _)

/-- The exact initial diagonal yields a smaller model bound than the full triangle. -/
theorem nn_diagramInitial_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2) :
    (∑' a, diagramInitial (homogeneousProfile (zdGraph d) p) 0 a) ≤
      ENNReal.ofReal (1 + 8882 / (315 * (d : ℝ))) := by
  refine (diagramInitial_mass_le_min_triangle_step _ (homogeneous_zdGraph_add p)).trans ?_
  refine (min_le_right _ _).trans ?_
  refine (add_le_add le_rfl (nn_step_tau_three_zero_le hd p hchi hj hK)).trans_eq ?_
  rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]

/-- The terminal norm keeps its distinct bubble factor and the sharper origin constant. -/
theorem nn_diagramTerminal_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    (∑' y, diagramTerminal (homogeneousProfile (zdGraph d) p) a y) ≤
      ENNReal.ofReal ((9197 / (315 * (d : ℝ))) * (1 + 4441 / (315 * (d : ℝ)))) := by
  refine (diagramTerminal_mass_le_continuation_bound _ (homogeneous_zdGraph_add p) _
    (nn_step_tau_three_le hd p hchi hj hK) a).trans ?_
  refine (mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl
    (nn_step_tau_three_zero_le hd p hchi hj hK)))).trans_eq ?_
  have hc : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (by norm_num) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The actual forward transfer is a strict contraction under the weak model bounds. -/
theorem nn_diagramTransfer_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    (∑' b, diagramTransfer (homogeneousProfile (zdGraph d) p) a b) ≤
      ENNReal.ofReal (63 / 1000 : ℝ) := by
  refine (diagramTransfer_mass_le_two_mul_triangle_continuation _
    (homogeneous_zdGraph_add p) _ _ (nn_triangle_le_twenty_one_twentieths hd p hchi hj hK)
    (nn_step_tau_three_le_three_hundredths hd p hchi hj hK) a).trans_eq ?_
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The backward interior-connector product has an independently proved strict
contraction, without reversing the deleted connector. -/
theorem nn_diagramInterior_connector_mass_le (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (hj : 2 * d * (p : ℝ) ≤ 2)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ 2)
    (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    (∑' b, ∑' c, diagramInterior (homogeneousProfile (zdGraph d) p) b c *
      diagramConnector (homogeneousProfile (zdGraph d) p) c a) ≤
        ENNReal.ofReal (63 / 1000 : ℝ) := by
  refine (diagramInterior_connector_mass_le_two_mul_triangle_continuation _
    (homogeneous_zdGraph_add p) _ _ (nn_triangle_le_twenty_one_twentieths hd p hchi hj hK)
    (nn_step_tau_three_le_three_hundredths hd p hchi hj hK) a).trans_eq ?_
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

end PercLib.Percolation.Bond.Lace
