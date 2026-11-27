/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original weighted-pair estimates for the actual percolation kernel.
Mathematical reference: Heydenreich and van der Hofstad (2017), Chapter 8.
No upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Bounds
public import PercLib.Percolation.Bond.Lace.Bootstrap.Convolution
public import PercLib.Percolation.Bond.Lace.Bootstrap.FirstStep
public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborGeometry

/-!
# Actual weighted-pair diagrams in the Fourier bootstrap

## Main results

The weighted pair is reduced to actual nonnegative convolutions by splitting
the character mark across its first step. The unshifted pair retains two step
factors after its direct nearest-neighbour contribution. The cosine transform
of the marked two-point function is exactly a symmetric second difference.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real PercLib.Analysis DiscreteConvolution
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G]

private theorem rooted_tau_neg (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y)) (x : G) :
    tau q 0 (-x) = tau q 0 x := by
  rw [← zero_sub x, ← tau_eq_rooted_of_add_right q hq x 0, tau_comm]

private theorem tsum_shifted_triple_eq_convolution
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (f g : G → ℝ≥0∞) (a : G) :
    (∑' v, ∑' z, f v * g (z - v) * tau q 0 (z + a)) =
      (f ⋆ᵣ₊ (g ⋆ᵣ₊ tau q 0)) (-a) := by
  simp only [addRingConvolution_eq_tsum_sub]
  simp_rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro v
  rw [← (Equiv.addRight v).tsum_eq]
  apply tsum_congr
  intro z
  change f v * g (z + v - v) * tau q 0 (z + v + a) =
    f v * (g z * tau q 0 (-a - v - z))
  have he : -a - v - z = -(z + v + a) := by abel
  rw [add_sub_cancel_right, he, rooted_tau_neg q hq]
  ac_rfl

private theorem tsum_mul_tau_eq_convolution
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (f : G → ℝ≥0∞) (z : G) :
    (∑' v, f v * tau q v z) = (f ⋆ᵣ₊ tau q 0) z := by
  rw [addRingConvolution_eq_tsum_sub]
  apply tsum_congr
  intro v
  rw [tau_eq_rooted_of_add_right q hq v z]

/-- Splitting the character mark across the first step expresses the actual
weighted pair through two nonnegative convolutions. -/
theorem diagramWeightedPair_character_le_convolutions
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (ψ : AddChar G Circle) (a : G) :
    let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
    let J := offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
    let T := tau q 0
    diagramWeightedPair q w a ≤
      2 * (((fun z => J z * w z) ⋆ᵣ₊ (T ⋆ᵣ₊ T)) (-a) +
        (J ⋆ᵣ₊ ((fun z => T z * w z) ⋆ᵣ₊ T)) (-a)) := by
  dsimp only
  let w : G → ℝ≥0∞ := fun z => ENNReal.ofReal (1 - (ψ z : ℂ).re)
  let J := offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  have hw (z v : G) : w z ≤ 2 * (w v + w (z - v)) := by
    have he : v + (z - v) = z := by abel
    simpa only [w, he] using character_weight_add_le ψ v (z - v)
  unfold diagramWeightedPair
  simp_rw [tsum_mul_tau_eq_convolution q hq, addRingConvolution_eq_tsum_sub]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  calc
    _ ≤ ∑' v, ∑' z, (2 * (w v + w (z - v))) * (J v * tau q 0 (z - v)) *
        tau q 0 (z + a) :=
      ENNReal.tsum_le_tsum fun v => ENNReal.tsum_le_tsum fun z =>
        mul_le_mul' (mul_le_mul' (hw z v) le_rfl) le_rfl
    _ = 2 * ((∑' v, ∑' z, (J v * w v) * tau q 0 (z - v) * tau q 0 (z + a)) +
        (∑' v, ∑' z, J v * (tau q 0 (z - v) * w (z - v)) * tau q 0 (z + a))) := by
      simp_rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      apply tsum_congr
      intro z
      ring
    _ = _ := by
      rw [tsum_shifted_triple_eq_convolution q hq (fun z => J z * w z) (tau q 0) a,
        tsum_shifted_triple_eq_convolution q hq J (fun z => tau q 0 z * w z) a]
      simp only [addRingConvolution_eq_tsum_sub, ← ENNReal.tsum_mul_left, J, w]

/-- The unshifted weighted pair keeps two step factors after its direct-step
term. This is a physical-space inequality, so the step symbol need not be positive. -/
theorem diagramWeightedPair_zero_le_direct_add_double_step [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) :
    let J := offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
    let T := tau q 0
    diagramWeightedPair q w 0 ≤
      (∑' z, w z * J z * T z) +
        ((J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) ⋆ᵣ₊ (fun z => w (-z) * T z)) 0 := by
  classical
  dsimp only
  let J := offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  let T := tau q 0
  have hstep : J ⋆ᵣ₊ T ≤ J + J ⋆ᵣ₊ (J ⋆ᵣ₊ T) := by
    have h := addRingConvolution_ennreal_mono (le_refl J)
      (tau_le_single_add_addRingConvolution q hq)
    simpa only [addRingConvolution_add _ _ _ (fun _ => ENNReal.summable)
      (fun _ => ENNReal.summable), addRingConvolution_single] using h
  have hW : diagramWeightedPair q w 0 = ∑' z, w z * (J ⋆ᵣ₊ T) z * T z := by
    simp only [diagramWeightedPair, add_zero, J, T, tsum_mul_tau_eq_convolution q hq]
  rw [hW]
  calc
    _ ≤ ∑' z, w z * (J z + (J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) z) * T z :=
      ENNReal.tsum_le_tsum fun z => mul_le_mul' (mul_le_mul' le_rfl (hstep z)) le_rfl
    _ = (∑' z, w z * J z * T z) +
        ∑' z, w z * (J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) z * T z := by
      simp_rw [mul_add, add_mul, ENNReal.tsum_add]
    _ = _ := by
      congr 1
      rw [addRingConvolution_eq_tsum_sub]
      apply tsum_congr
      intro z
      simp only [zero_sub, neg_neg, T, rooted_tau_neg q hq]
      ac_rfl

/-- The marked two-point function is absolutely summable whenever susceptibility
is finite; no spatial moment assumption is needed for this bounded mark. -/
theorem summable_tau_mul_cosine_weight {d : ℕ}
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤) (k : Fin d → ℝ) :
    Summable (fun z => (tau q 0 z).toReal * (1 - cos (∑ i, k i * (z i : ℝ)))) := by
  have hτ : Summable (fun z => (tau q 0 z).toReal) :=
    ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  simpa only [abs_of_nonneg ENNReal.toReal_nonneg] using
    summable_abs_mul_one_sub_cos hτ (fun z => ∑ i, k i * (z i : ℝ))

/-- The actual cosine transform of the marked two-point kernel is minus one
half of its symmetric second difference. -/
theorem latticeCosineTransform_tau_mul_weight_eq {d : ℕ}
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (k l : Fin d → ℝ) :
    latticeCosineTransform
      (fun z => (tau q 0 z).toReal * (1 - cos (∑ i, k i * (z i : ℝ)))) l =
      -(tauFourier q (l - k) + tauFourier q (l + k) - 2 * tauFourier q l) / 2 := by
  have hτ : Summable (fun z => (tau q 0 z).toReal) :=
    ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have h0 := summable_mul_cos hτ (fun z => ∑ i, l i * (z i : ℝ))
  have hm := summable_mul_cos hτ (fun z => ∑ i, (l i - k i) * (z i : ℝ))
  have hp := summable_mul_cos hτ (fun z => ∑ i, (l i + k i) * (z i : ℝ))
  unfold latticeCosineTransform
  calc
    _ = ∑' z, ((2 * ((tau q 0 z).toReal * cos (∑ i, l i * (z i : ℝ))) -
        (tau q 0 z).toReal * cos (∑ i, (l i - k i) * (z i : ℝ))) -
        (tau q 0 z).toReal * cos (∑ i, (l i + k i) * (z i : ℝ))) / 2 := by
      apply tsum_congr
      intro z
      simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        cos_sub, cos_add]
      ring
    _ = _ := by
      rw [tsum_div_const, ((h0.mul_left 2).sub hm).tsum_sub hp,
        (h0.mul_left 2).tsum_sub hm, tsum_mul_left]
      simp only [tauFourier_def, Pi.sub_apply, Pi.add_apply]
      ring

/-- Bounded nonnegative marks give a finite actual pair whenever the rooted
step mass and susceptibility are finite. -/
theorem diagramWeightedPair_le_step_mass_mul_chi [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (c : ℝ≥0∞) (hw : ∀ z, w z ≤ c) (a : G) :
    diagramWeightedPair q w a ≤ c *
      (∑' v, offDiagonal (fun x y : G =>
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0 v) * chi q 0 := by
  let J := offDiagonal (fun x y : G =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  calc
    _ ≤ ∑' z, c * (J ⋆ᵣ₊ tau q 0) z := by
      unfold diagramWeightedPair
      apply ENNReal.tsum_le_tsum
      intro z
      rw [tsum_mul_tau_eq_convolution q hq]
      exact (mul_le_mul' (mul_le_mul' (hw z) (le_refl ((J ⋆ᵣ₊ tau q 0) z)))
        (tau_le_one q 0 (z + a))).trans_eq (mul_one _)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, tsum_addRingConvolution_ennreal, ← chi_eq_tsum_tau]
      ac_rfl

theorem diagramWeightedPair_ne_top_of_bounded_weight [Countable G]
    (q : Sym2 G → unitInterval)
    (hq : ∀ x y g : G, q s(x + g, y + g) = q s(x, y))
    (w : G → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) (hw : ∀ z, w z ≤ c)
    (hJ : (∑' v, offDiagonal (fun x y : G =>
      (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0 v) ≠ ⊤)
    (hchi : chi q 0 ≠ ⊤) (a : G) : diagramWeightedPair q w a ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hJ) hchi)
    (diagramWeightedPair_le_step_mass_mul_chi q hq w c hw a)

/-- The pointwise bootstrap estimate for the transform of the actual marked
kernel also covers zero-deficit frequencies, where the transform vanishes. -/
theorem abs_tau_weightFourier_le_of_fourierDifferenceSup_le {d : ℕ} (hd : 0 < d)
    (q : Sym2 (Fin d → ℤ) → unitInterval) (hchi : chi q 0 ≠ ⊤)
    (hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤)
    {K : ℝ} (hK : fourierDifferenceSup q ≤ K) (k l : Fin d → ℝ) :
    |latticeCosineTransform
      (fun z => (tau q 0 z).toReal * (1 - cos (∑ i, k i * (z i : ℝ)))) l| ≤
      100 * K * (1 - nearestNeighborSymbol k) *
        bootstrapTripleProduct (susceptibilityWalkParameter q) k l := by
  rw [latticeCosineTransform_tau_mul_weight_eq q hchi, abs_div, abs_neg]
  have hdef : 0 ≤ 1 - nearestNeighborSymbol k :=
    sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd k)).2
  by_cases hk : 0 < 1 - nearestNeighborSymbol k
  · have h := abs_fwdDiff_two_tauFourier_le_mul_majorant_of_fourierDifferenceSup_le
      hd q hchi hsecond hK (l := l) hk
    rw [fwdDiff_two_at_sub, bootstrapMajorant] at h
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · have hz : 1 - nearestNeighborSymbol k = 0 := le_antisymm (le_of_not_gt hk) hdef
    have h := abs_fwdDiff_two_tauFourier_le_spatialMoment q hchi hsecond k l
    rw [fwdDiff_two_at_sub, sum_one_sub_cos_eq_mul_deficit hd, hz] at h
    simp only [mul_zero] at h
    simp only [hz, mul_zero, zero_mul]
    exact div_nonpos_of_nonpos_of_nonneg h (abs_nonneg _)

/-- The exact cosine-marked mass of the actual nearest-neighbour step kernel
is `2 d p` times the canonical symbol deficit. -/
theorem tsum_homogeneous_zdGraph_cosine_weight {d : ℕ} (hd : 0 < d)
    (p : unitInterval) (k : Fin d → ℝ) :
    (∑' z, (homogeneousProfile (PercLib.Models.Site.zdGraph d) p s(0, z) : ℝ) *
      (1 - cos (∑ i, k i * (z i : ℝ)))) =
      (2 * d * (p : ℝ)) * (1 - nearestNeighborSymbol k) := by
  classical
  rw [tsum_homogeneous_zdGraph_mul, Fintype.sum_prod_type]
  have hdir (i : Fin d) :
      (∑ b : Bool, (1 - cos (∑ j, k j *
        ((Function.update (0 : Fin d → ℤ) i (if b then 1 else -1)) j : ℝ)))) =
        2 * (1 - cos (k i)) := by
    simp [Finset.sum_ite_eq', Function.update_apply]
    ring
  simp_rw [hdir]
  rw [← Finset.mul_sum, sum_one_sub_cos_eq_mul_deficit hd]
  ring

end PercLib.Percolation.Bond.Lace
