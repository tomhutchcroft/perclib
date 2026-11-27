/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.Convolution
public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborGeometry
public import PercLib.Percolation.Bond.Lace.Bootstrap.Bounds
public import PercLib.Analysis.NearestNeighborWeightedResolventPowers
public import PercLib.Analysis.NearestNeighborResolventCritical

/-!
# Squared step-symbol bounds for actual nearest-neighbour convolutions

## Main results

Two actual nearest-neighbour step factors give a squared Fourier symbol. The
coefficient estimate retains that square before comparing the two-point
transform with the walk resolvent, so no signed-symbol comparison is needed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real
open PercLib.Analysis PercLib.Models.Site
open scoped DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

/-- Convolution preserves evenness by the negation reindexing. -/
theorem even_addRingConvolution {G R : Type*} [AddCommGroup G]
    [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    {f g : G → R} (hf : Function.Even f) (hg : Function.Even g) :
    Function.Even (DiscreteConvolution.addRingConvolution f g) := by
  intro x
  simp only [addRingConvolution_eq_tsum_sub]
  rw [← (Equiv.neg G).tsum_eq]
  apply tsum_congr
  intro y
  simp only [Equiv.neg_apply, neg_sub_neg, ← neg_sub x y]
  rw [hf y, hg (x - y)]

/-- The actual nearest-neighbour step kernel is even. -/
theorem even_homogeneous_zdGraph {d : ℕ} (p : unitInterval) :
    Function.Even (fun z : Fin d → ℤ =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)) := by
  intro z
  have h := homogeneous_zdGraph_add p 0 (-z) z
  simpa only [zero_add, neg_add_cancel, Sym2.eq_swap] using
    congrArg (fun t : unitInterval => (t : ℝ)) h.symm

/-- Two actual step factors retain the squared normalized walk symbol in the
physical-frequency coefficient bound. -/
theorem abs_homogeneous_step_twice_convolution_le_integral {d : ℕ} (hd : 0 < d)
    (p : unitInterval) {f : (Fin d → ℤ) → ℝ} (hf : Summable f)
    (heven : Function.Even f) (x : Fin d → ℤ) :
    let J : (Fin d → ℤ) → ℝ := fun z =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)
    |(J ⋆ᵣ₊ (J ⋆ᵣ₊ f)) x| ≤ (2 * d * (p : ℝ)) ^ 2 *
      (((2 * π) ^ d)⁻¹ * ∫ k in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol k ^ 2 * |latticeCosineTransform f k|) := by
  let J : (Fin d → ℤ) → ℝ := fun z =>
    (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)
  have hJ : Summable J := summable_homogeneous_zdGraph p
  have heJ : Function.Even J := even_homogeneous_zdGraph p
  have h := abs_addRingConvolution_le_normalized_integral hJ
    (summable_addRingConvolution_real hJ hf) heJ
    (even_addRingConvolution heJ heven) x
  simp_rw [latticeCosineTransform_addRingConvolution hJ hf heJ] at h
  dsimp only [J] at h
  simp_rw [latticeCosineTransform_homogeneous_zdGraph hd p] at h
  have hpoint (k : Fin d → ℝ) :
      |(2 * d * (p : ℝ) * nearestNeighborSymbol k) *
        (2 * d * (p : ℝ) * nearestNeighborSymbol k * latticeCosineTransform f k)| =
      (2 * d * (p : ℝ)) ^ 2 *
        (nearestNeighborSymbol k ^ 2 * |latticeCosineTransform f k|) := by
    rw [show (2 * d * (p : ℝ) * nearestNeighborSymbol k) *
        (2 * d * (p : ℝ) * nearestNeighborSymbol k * latticeCosineTransform f k) =
        (2 * d * (p : ℝ)) ^ 2 * nearestNeighborSymbol k ^ 2 *
          latticeCosineTransform f k by ring]
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    ring
  simp_rw [hpoint] at h
  rw [integral_const_mul] at h
  simpa only [mul_left_comm] using h

private theorem abs_step_twice_le_of_transform_bound {d : ℕ} (hd : 0 < d)
    (p : unitInterval) {f : (Fin d → ℤ) → ℝ} (hf : Summable f)
    (heven : Function.Even f) {r L B : ℝ} (hr : r ∈ Set.Ico 0 1)
    (hL0 : 0 ≤ L) (s : ℕ)
    (hfourier : ∀ k, |latticeCosineTransform f k| ≤
      L * nearestNeighborResolvent r k ^ (s + 1))
    (hwalk : ((2 * π) ^ d)⁻¹ * (∫ k in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol k ^ 2 * nearestNeighborResolvent r k ^ (s + 1)) ≤ B)
    (x : Fin d → ℤ) :
    let J : (Fin d → ℤ) → ℝ := fun z =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)
    |(J ⋆ᵣ₊ (J ⋆ᵣ₊ f)) x| ≤ (2 * d * (p : ℝ)) ^ 2 * L * B := by
  have hbase := abs_homogeneous_step_twice_convolution_le_integral hd p hf heven x
  have hint : IntegrableOn (fun k : Fin d → ℝ =>
      nearestNeighborSymbol k ^ 2 * nearestNeighborResolvent r k ^ (s + 1)) (ball 0 π) := by
    rw [IntegrableOn, volume_restrict_pi_ball_eq_pi_Ioo]
    let μ : Measure (Fin d → ℝ) :=
      Measure.pi (fun _ => volume.restrict (Set.Ioo (-π) π))
    have hi := integrable_nearestNeighborSymbol_inv_pow hd μ hr.1 hr.2 s
    have hm : AEStronglyMeasurable (fun k : Fin d → ℝ => nearestNeighborSymbol k ^ 2)
        μ := by
      apply Continuous.aestronglyMeasurable
      unfold nearestNeighborSymbol
      fun_prop
    have h := hi.bdd_mul (c := 1) hm (Filter.Eventually.of_forall (fun k => by
      have ha := abs_nearestNeighborSymbol_le_one hd k
      simpa only [Real.norm_eq_abs, abs_pow, nearestNeighborSymbol] using
        pow_le_one₀ (abs_nonneg _) ha))
    simpa only [nearestNeighborSymbol, nearestNeighborResolvent, one_div, inv_pow, μ] using h
  have hpoint (k : Fin d → ℝ) :
      nearestNeighborSymbol k ^ 2 * |latticeCosineTransform f k| ≤
        L * (nearestNeighborSymbol k ^ 2 * nearestNeighborResolvent r k ^ (s + 1)) := by
    have ht := hfourier k
    calc
      _ ≤ nearestNeighborSymbol k ^ 2 * (L * nearestNeighborResolvent r k ^ (s + 1)) :=
        mul_le_mul_of_nonneg_left ht (sq_nonneg _)
      _ = _ := by ring
  have hi := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun k : Fin d → ℝ =>
      mul_nonneg (sq_nonneg (nearestNeighborSymbol k)) (abs_nonneg _)))
    (hint.const_mul L) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hi
  have hn := mul_le_mul_of_nonneg_left hi
    (show (0 : ℝ) ≤ ((2 * π) ^ d)⁻¹ by positivity)
  have hn' : ((2 * π) ^ d)⁻¹ *
      (∫ k in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol k ^ 2 * |latticeCosineTransform f k|) ≤
      L * B := by
    calc
      _ ≤ L * (((2 * π) ^ d)⁻¹ * ∫ k in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol k ^ 2 * nearestNeighborResolvent r k ^ (s + 1)) := by
        simpa only [mul_left_comm] using hn
      _ ≤ _ := mul_le_mul_of_nonneg_left hwalk hL0
  exact hbase.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn'
      (sq_nonneg (2 * d * (p : ℝ))))

/-- A weak bound on the actual two-point Fourier ratio gives an explicit
coefficient estimate after two nearest-neighbour steps. -/
theorem abs_homogeneous_step_twice_tau_le {d : ℕ} (hd : 1000 ≤ d)
    (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (x : Fin d → ℤ) :
    let J : (Fin d → ℤ) → ℝ := fun z =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)
    let T : (Fin d → ℤ) → ℝ := fun z =>
      (tau (homogeneousProfile (zdGraph d) p) 0 z).toReal
    |(J ⋆ᵣ₊ (J ⋆ᵣ₊ T)) x| ≤
      (2 * d * (p : ℝ)) ^ 2 * K * (631 / (1260 * (d : ℝ))) := by
  let q := homogeneousProfile (zdGraph d) p
  let T : (Fin d → ℤ) → ℝ := fun z => (tau q 0 z).toReal
  let r := susceptibilityWalkParameter q
  have hd0 : 0 < d := by omega
  have hr : r ∈ Set.Ico 0 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  apply abs_step_twice_le_of_transform_bound hd0 p hT heT hr hK0 0
  · intro k
    simpa only [Nat.zero_add, pow_one, tauFourier, T] using
      abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd0 q hchi hK k
  · simpa only [Nat.zero_add, pow_one, nearestNeighborSymbol, nearestNeighborResolvent,
      div_eq_mul_inv] using integral_nearestNeighborSymbol_sq_mul_inv_le hd hr.1 hr.2

/-- Explicit two-step coefficient bound for the actual 2-fold two-point convolution. -/
theorem abs_homogeneous_step_twice_tau_sq_le {d : ℕ} (hd : 1000 ≤ d)
    (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (x : Fin d → ℤ) :
    let J : (Fin d → ℤ) → ℝ := fun z =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)
    let T : (Fin d → ℤ) → ℝ := fun z =>
      (tau (homogeneousProfile (zdGraph d) p) 0 z).toReal
    |(J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ T))) x| ≤
      (2 * d * (p : ℝ)) ^ 2 * K ^ 2 * (211 / (420 * (d : ℝ))) := by
  let q := homogeneousProfile (zdGraph d) p
  let T : (Fin d → ℤ) → ℝ := fun z => (tau q 0 z).toReal
  let r := susceptibilityWalkParameter q
  have hd0 : 0 < d := by omega
  have hr : r ∈ Set.Ico 0 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  have hF : Summable (T ⋆ᵣ₊ T) :=
    summable_addRingConvolution_real hT hT
  have heF : Function.Even (T ⋆ᵣ₊ T) :=
    even_addRingConvolution heT heT
  apply abs_step_twice_le_of_transform_bound hd0 p hF heF hr (pow_nonneg hK0 2) 1
  · intro k
    simp only [show 1 + 1 = 2 from rfl]
    rw [latticeCosineTransform_addRingConvolution hT hT heT]
    have ht := abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd0 q hchi hK k
    change |latticeCosineTransform T k| ≤ K * nearestNeighborResolvent r k at ht
    have hp := pow_le_pow_left₀ (abs_nonneg (latticeCosineTransform T k)) ht 2
    simpa only [mul_pow, abs_mul, pow_succ, pow_zero, mul_one, one_mul,
      mul_assoc, mul_left_comm, mul_comm] using hp
  · simpa only [show 1 + 1 = 2 from rfl, nearestNeighborSymbol,
      nearestNeighborResolvent, div_eq_mul_inv, inv_pow] using
      integral_nearestNeighborSymbol_sq_mul_inv_sq_le hd hr.1 hr.2

/-- Explicit two-step coefficient bound for the actual 3-fold two-point convolution. -/
theorem abs_homogeneous_step_twice_tau_cube_le {d : ℕ} (hd : 1000 ≤ d)
    (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ K)
    (x : Fin d → ℤ) :
    let J : (Fin d → ℤ) → ℝ := fun z =>
      (homogeneousProfile (zdGraph d) p s(0, z) : ℝ)
    let T : (Fin d → ℤ) → ℝ := fun z =>
      (tau (homogeneousProfile (zdGraph d) p) 0 z).toReal
    |(J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)))) x| ≤
      (2 * d * (p : ℝ)) ^ 2 * K ^ 3 * (53 / (105 * (d : ℝ))) := by
  let q := homogeneousProfile (zdGraph d) p
  let T : (Fin d → ℤ) → ℝ := fun z => (tau q 0 z).toReal
  let r := susceptibilityWalkParameter q
  have hd0 : 0 < d := by omega
  have hr : r ∈ Set.Ico 0 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  have hF : Summable (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) :=
    summable_addRingConvolution_real hT (summable_addRingConvolution_real hT hT)
  have heF : Function.Even (T ⋆ᵣ₊ (T ⋆ᵣ₊ T)) :=
    even_addRingConvolution heT (even_addRingConvolution heT heT)
  apply abs_step_twice_le_of_transform_bound hd0 p hF heF hr (pow_nonneg hK0 3) 2
  · intro k
    simp only [show 2 + 1 = 3 from rfl]
    rw [latticeCosineTransform_addRingConvolution hT
      (summable_addRingConvolution_real hT hT) heT,
      latticeCosineTransform_addRingConvolution hT hT heT]
    have ht := abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd0 q hchi hK k
    change |latticeCosineTransform T k| ≤ K * nearestNeighborResolvent r k at ht
    have hp := pow_le_pow_left₀ (abs_nonneg (latticeCosineTransform T k)) ht 3
    simpa only [mul_pow, abs_mul, pow_succ, pow_zero, mul_one, one_mul,
      mul_assoc, mul_left_comm, mul_comm] using hp
  · simpa only [show 2 + 1 = 3 from rfl, nearestNeighborSymbol,
      nearestNeighborResolvent, div_eq_mul_inv, inv_pow] using
      integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr.1 hr.2

end PercLib.Percolation.Bond.Lace
