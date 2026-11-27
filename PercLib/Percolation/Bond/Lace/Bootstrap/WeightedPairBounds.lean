/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original weighted-pair estimates for the actual percolation kernel.
Mathematical reference: Heydenreich and van der Hofstad (2017), Chapter 8.
No upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.WeightedPair
public import PercLib.Percolation.Bond.Lace.Bootstrap.NearestNeighborIntegrals
public import PercLib.Analysis.LatticeFourier.ShiftedResolvent
public import PercLib.Analysis.NearestNeighborResolventCritical
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weighted-pair bounds retaining the actual nearest-neighbour step mass

## Main results

The direct contribution at the origin is evaluated exactly using lattice
symmetry. The remaining contribution retains two actual step factors in its
Fourier bound. All model quantities come from the homogeneous nearest-neighbour
law and its canonical Fourier bootstrap.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real PercLib.Analysis PercLib.Models.Site DiscreteConvolution
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

private theorem cosine_mark_even (k : Fin d → ℝ) :
    Function.Even (fun z : Fin d → ℤ => 1 - cos (∑ i, k i * (z i : ℝ))) := by
  intro z
  simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, cos_neg]

private theorem nn_tau_summable (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤) :
    Summable (fun z => (tau (homogeneousProfile (zdGraph d) p) 0 z).toReal) :=
  ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])

private theorem nn_tau_even (p : unitInterval) :
    Function.Even (fun z : Fin d → ℤ =>
      (tau (homogeneousProfile (zdGraph d) p) 0 z).toReal) := by
  intro z
  exact congrArg ENNReal.toReal (tau_homogeneous_zdGraph_neg p z)

/-- Lattice symmetry evaluates the direct marked step contribution exactly.
Its coefficient is the actual step mass times the actual neighbour two-point value. -/
theorem tsum_nn_marked_step_mul_tau {e : Fin d → ℤ}
    (hd : 0 < d) (p : unitInterval) (he : (zdGraph d).Adj 0 e) (k : Fin d → ℝ) :
    (∑' z : Fin d → ℤ,
      (1 - cos (∑ i, k i * (z i : ℝ))) *
        (homogeneousProfile (zdGraph d) p s(0, z) : ℝ) *
          (tau (homogeneousProfile (zdGraph d) p) 0 z).toReal) =
      (2 * d * (p : ℝ)) * (tau (homogeneousProfile (zdGraph d) p) 0 e).toReal *
        (1 - nearestNeighborSymbol k) := by
  calc
    _ = ∑' z : Fin d → ℤ,
        ((homogeneousProfile (zdGraph d) p s(0, z) : ℝ) *
          (1 - cos (∑ i, k i * (z i : ℝ)))) *
            (tau (homogeneousProfile (zdGraph d) p) 0 e).toReal := by
      apply tsum_congr
      intro z
      by_cases hz : (zdGraph d).Adj 0 z
      · rw [tau_homogeneous_zdGraph_eq_of_neighbors p hz he]
        ring
      · have hzero : homogeneousProfile (zdGraph d) p s(0, z) = 0 :=
          homogeneousProfile_of_notMem p (by simpa only [SimpleGraph.mem_edgeSet] using hz)
        simp [hzero]
    _ = _ := by
      rw [tsum_mul_right, tsum_homogeneous_zdGraph_cosine_weight hd p]
      ring

/-- The real-valued unshifted diagram retains two actual steps in its remainder.
Only finite susceptibility is required; the cosine mark is bounded. -/
theorem diagramWeightedPair_nn_zero_toReal_le {e : Fin d → ℤ}
    (hd : 0 < d) (p : unitInterval) (he : (zdGraph d).Adj 0 e)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤) (k : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    let J : (Fin d → ℤ) → ℝ := fun z => (q s(0, z) : ℝ)
    let T := fun z => (tau q 0 z).toReal
    let Tk := fun z => T z * (1 - cos (∑ i, k i * (z i : ℝ)))
    (diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) 0).toReal ≤
      (2 * d * (p : ℝ)) * T e * (1 - nearestNeighborSymbol k) +
        (J ⋆ᵣ₊ (J ⋆ᵣ₊ (T ⋆ᵣ₊ Tk))) 0 := by
  let q := homogeneousProfile (zdGraph d) p
  let J := offDiagonal (fun x y : Fin d → ℤ =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  let T := tau q 0
  let w : (Fin d → ℤ) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))
  have hw (z) : w z ≤ 2 := by
    calc
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal
        (show 1 - cos (∑ i, k i * (z i : ℝ)) ≤ 2 by
          linarith [neg_one_le_cos (∑ i, k i * (z i : ℝ))])
      _ = _ := by norm_num
  have hJ : (∑' z, J z) ≠ ⊤ := nn_step_mass_ne_top p
  have hT : (∑' z, T z) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have hJz (z) : J z ≠ ⊤ := ne_top_of_le_ne_top hJ (ENNReal.le_tsum z)
  have hTz (z) : T z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q 0 z)
  have hmark : (∑' z, w (-z) * T z) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hT)
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun z => mul_le_mul' (hw (-z)) le_rfl
  have hmarkz (z) : w (-z) * T z ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hTz z)
  have hTM : (∑' z, (T ⋆ᵣ₊ (fun z => w (-z) * T z)) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hmark
  have hTMz (z) : (T ⋆ᵣ₊ (fun z => w (-z) * T z)) z ≠ ⊤ :=
    addRingConvolution_ennreal_ne_top hT hmark z
  have hJTM : (∑' z, (J ⋆ᵣ₊ (T ⋆ᵣ₊ (fun z => w (-z) * T z))) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hJ hTM
  have hJTMz (z) : (J ⋆ᵣ₊ (T ⋆ᵣ₊ (fun z => w (-z) * T z))) z ≠ ⊤ :=
    addRingConvolution_ennreal_ne_top hJ hTM z
  have hdirect : (∑' z, w z * J z * T z) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hJ)
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun z =>
      (mul_le_mul' (mul_le_mul' (hw z) le_rfl) (tau_le_one q 0 z)).trans_eq (mul_one _)
  have hraw := diagramWeightedPair_zero_le_direct_add_double_step q (homogeneous_zdGraph_add p) w
  dsimp only at hraw
  rw [addRingConvolution_ennreal_assoc, addRingConvolution_ennreal_assoc] at hraw
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hdirect, addRingConvolution_ennreal_ne_top hJ hJTM 0⟩) hraw
  rw [ENNReal.toReal_add hdirect (addRingConvolution_ennreal_ne_top hJ hJTM 0),
    ENNReal.tsum_toReal_eq (fun z => ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hJz z)) (hTz z))] at h
  simp only [toReal_addRingConvolution_ennreal hJz hJTMz,
    toReal_addRingConvolution_ennreal hJz hTMz,
    toReal_addRingConvolution_ennreal hTz hmarkz, ENNReal.toReal_mul] at h
  have hwreal (z : Fin d → ℤ) : (ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))).toReal =
      1 - cos (∑ i, k i * (z i : ℝ)) :=
    ENNReal.toReal_ofReal (sub_nonneg.mpr (cos_le_one _))
  simp only [w, hwreal, J, T, q, nn_offDiagonal_toReal, Pi.neg_apply, Int.cast_neg,
    mul_neg, Finset.sum_neg_distrib, cos_neg] at h
  rw [tsum_nn_marked_step_mul_tau hd p he k] at h
  have hm : (fun z : Fin d → ℤ =>
      (1 - cos (∑ i, k i * (z i : ℝ))) * (T z).toReal) =
      (fun z => (T z).toReal * (1 - cos (∑ i, k i * (z i : ℝ)))) := by
    funext z
    exact mul_comm _ _
  rw [hm] at h
  exact h

private theorem continuous_nn_resolvent (hd : 0 < d) {r : ℝ}
    (hr : r ∈ Set.Ico (0 : ℝ) 1) : Continuous (nearestNeighborResolvent (d := d) r) := by
  unfold nearestNeighborResolvent
  apply Continuous.inv₀
  · unfold nearestNeighborSymbol
    fun_prop
  · intro l
    exact (nearestNeighborResolvent_den_pos hd hr l).ne'

private theorem integrableOn_fourierBall_of_continuous
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) : IntegrableOn f (ball 0 π) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Fin d → ℝ) π)).mono_set
    ball_subset_closedBall

/-- The three terms in the canonical second-difference majorant cost exactly
three weighted cubic resolvent integrals. The squared symbol remains in place. -/
theorem integral_symbol_sq_mul_resolvent_mul_bootstrapTriple_le
    (hd : 0 < d) {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l *
        bootstrapTripleProduct r k l) ≤
      3 * (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) := by
  let C := nearestNeighborResolvent (d := d) r
  have hc : Continuous C := continuous_nn_resolvent hd hr
  have hint (a b : Fin d → ℝ) : IntegrableOn
      (fun l => nearestNeighborSymbol l ^ 2 * C l * C (l + a) * C (l + b)) (ball 0 π) := by
    apply integrableOn_fourierBall_of_continuous
    unfold nearestNeighborSymbol
    fun_prop
  have hp (l : Fin d → ℝ) :
      nearestNeighborSymbol l ^ 2 * C l * bootstrapTripleProduct r k l =
        (nearestNeighborSymbol l ^ 2 * C l * C (l + -k) * C (l + 0) +
          nearestNeighborSymbol l ^ 2 * C l * C (l + 0) * C (l + k)) +
            nearestNeighborSymbol l ^ 2 * C l * C (l + -k) * C (l + k) := by
    simp only [bootstrapTripleProduct, add_zero, ← sub_eq_add_neg, C]
    ring
  change _ * (∫ l in ball (0 : Fin d → ℝ) π,
    nearestNeighborSymbol l ^ 2 * C l * bootstrapTripleProduct r k l) ≤ _
  simp_rw [hp]
  have hiadd : IntegrableOn (fun l =>
      nearestNeighborSymbol l ^ 2 * C l * C (l + -k) * C (l + 0) +
        nearestNeighborSymbol l ^ 2 * C l * C (l + 0) * C (l + k)) (ball 0 π) :=
    (hint (-k) 0).add (hint 0 k)
  rw [integral_add hiadd (hint (-k) k),
    integral_add (hint (-k) 0) (hint 0 k), mul_add, mul_add]
  have h1 := integral_nearestNeighborSymbol_sq_mul_shifted_resolvents_le hd hr.1 hr.2 (-k) 0
  have h2 := integral_nearestNeighborSymbol_sq_mul_shifted_resolvents_le hd hr.1 hr.2 0 k
  have h3 := integral_nearestNeighborSymbol_sq_mul_shifted_resolvents_le hd hr.1 hr.2 (-k) k
  linarith

/-- Under the actual canonical weak bootstrap, the remaining unshifted pair
retains `j²` and the squared-symbol cubic integral. The direct term is still exact. -/
theorem diagramWeightedPair_nn_zero_le_weighted_integral {e : Fin d → ℤ}
    (hd : 0 < d) (p : unitInterval) (he : (zdGraph d).Adj 0 e)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    let j : ℝ := 2 * d * (p : ℝ)
    let r := susceptibilityWalkParameter q
    let B := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3
    (diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) 0).toReal ≤
      (j * (tau q 0 e).toReal + 300 * j ^ 2 * K ^ 2 * B) *
        (1 - nearestNeighborSymbol k) := by
  let q := homogeneousProfile (zdGraph d) p
  let T := fun z => (tau q 0 z).toReal
  let Tk := fun z => T z * (1 - cos (∑ i, k i * (z i : ℝ)))
  let r := susceptibilityWalkParameter q
  let C := nearestNeighborResolvent (d := d) r
  let j : ℝ := 2 * d * (p : ℝ)
  let N : ℝ := ((2 * π) ^ d)⁻¹
  let g : ℝ := 1 - nearestNeighborSymbol k
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have hparts : (rowSum (fun e => unitInterval.toENNReal (q e)) 0).toReal ≤ K ∧
      fourierRatioSup q ≤ K ∧ fourierDifferenceSup q ≤ K := by
    simpa only [fourierBootstrap, max_le_iff] using hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg.trans hparts.1
  have hg : 0 ≤ g := sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd k)).2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤ :=
    (spatialMoment_sq_lt_top_of_finiteRange_of_transitive q 0 (by norm_num : (0 : ℝ) ≤ 1)
      (homogeneous_zdGraph_eq_zero_of_one_lt_norm p) (homogeneous_zdGraph_transitive p) hchi).ne
  have ht : Summable T := nn_tau_summable p hchi
  have htk : Summable Tk := summable_tau_mul_cosine_weight q hchi k
  have heT : Function.Even T := nn_tau_even p
  have heTk : Function.Even Tk := by
    intro z
    simp only [Tk, heT z, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, cos_neg]
  have hpoint (l : Fin d → ℝ) :
      |latticeCosineTransform (T ⋆ᵣ₊ Tk) l| ≤
        (100 * K ^ 2 * g) * (C l * bootstrapTripleProduct r k l) := by
    rw [latticeCosineTransform_addRingConvolution ht htk heT, abs_mul]
    have hτ := abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd q hchi hparts.2.1 l
    have hτk := abs_tau_weightFourier_le_of_fourierDifferenceSup_le
      hd q hchi hsecond hparts.2.2 k l
    exact (mul_le_mul hτ hτk (abs_nonneg _)
      (mul_nonneg hK0 (nearestNeighborResolvent_pos hd hr l).le)).trans_eq (by ring)
  have hc : Continuous C := continuous_nn_resolvent hd hr
  have hV : Continuous (bootstrapTripleProduct r k) := by
    change Continuous (fun l => C (l - k) * C l + C l * C (l + k) + C (l - k) * C (l + k))
    fun_prop
  have hcont : Continuous (fun l => nearestNeighborSymbol l ^ 2 * C l *
      bootstrapTripleProduct r k l) := by
    unfold nearestNeighborSymbol
    fun_prop
  have hintleft : IntegrableOn
      (fun l => nearestNeighborSymbol l ^ 2 * |latticeCosineTransform (T ⋆ᵣ₊ Tk) l|)
      (ball 0 π) := by
    apply integrableOn_fourierBall_of_continuous
    have hf := continuous_latticeCosineTransform (summable_addRingConvolution_real ht htk)
    unfold nearestNeighborSymbol
    fun_prop
  have hint : N * (∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * |latticeCosineTransform (T ⋆ᵣ₊ Tk) l|) ≤
      300 * K ^ 2 * g * (N * ∫ l in ball (0 : Fin d → ℝ) π,
        nearestNeighborSymbol l ^ 2 * C l ^ 3) := by
    calc
      _ ≤ N * ∫ l in ball (0 : Fin d → ℝ) π,
          (100 * K ^ 2 * g) * (nearestNeighborSymbol l ^ 2 * C l *
            bootstrapTripleProduct r k l) := by
        apply mul_le_mul_of_nonneg_left _ hN
        apply integral_mono_ae hintleft ((integrableOn_fourierBall_of_continuous hcont).const_mul _)
        exact Filter.Eventually.of_forall fun l =>
          (mul_le_mul_of_nonneg_left (hpoint l) (sq_nonneg _)).trans_eq (by ring)
      _ = (100 * K ^ 2 * g) * (N * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * C l * bootstrapTripleProduct r k l) := by
        rw [integral_const_mul]
        ring
      _ ≤ (100 * K ^ 2 * g) * (3 * (N * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * C l ^ 3)) :=
        mul_le_mul_of_nonneg_left (integral_symbol_sq_mul_resolvent_mul_bootstrapTriple_le hd hr k)
          (by positivity)
      _ = _ := by ring
  have hconv := abs_homogeneous_step_twice_convolution_le_integral hd p
    (summable_addRingConvolution_real ht htk) (even_addRingConvolution heT heTk) 0
  have h := (diagramWeightedPair_nn_zero_toReal_le hd p he hchi k).trans
    (add_le_add le_rfl ((le_abs_self _).trans
      (hconv.trans (mul_le_mul_of_nonneg_left hint (sq_nonneg j)))))
  convert h using 1
  dsimp only [j, N, g, C, r]
  ring

/-- Two actual first-step expansions bound a neighbour connection probability,
retaining the sharper first-power weighted resolvent constant. -/
theorem tau_nn_neighbor_toReal_le_firstStep {e : Fin d → ℤ}
    (hd : 1000 ≤ d) (p : unitInterval) (he : (zdGraph d).Adj 0 e)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : fourierRatioSup (homogeneousProfile (zdGraph d) p) ≤ K) :
    (tau (homogeneousProfile (zdGraph d) p) 0 e).toReal ≤
      (p : ℝ) + (2 * d * (p : ℝ)) ^ 2 * K * (631 / (1260 * (d : ℝ))) := by
  classical
  let q := homogeneousProfile (zdGraph d) p
  let J := offDiagonal (fun x y : Fin d → ℤ =>
    (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞)) 0
  let T := tau q 0
  have hJ : (∑' z, J z) ≠ ⊤ := nn_step_mass_ne_top p
  have hT : (∑' z, T z) ≠ ⊤ := by rwa [← chi_eq_tsum_tau]
  have hJz (z) : J z ≠ ⊤ := ne_top_of_le_ne_top hJ (ENNReal.le_tsum z)
  have hTz (z) : T z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (tau_le_one q 0 z)
  have hJT : (∑' z, (J ⋆ᵣ₊ T) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hJ hT
  have hJTz (z) : (J ⋆ᵣ₊ T) z ≠ ⊤ := addRingConvolution_ennreal_ne_top hJ hT z
  have hfirst := tau_le_single_add_addRingConvolution q (homogeneous_zdGraph_add p)
  have hsecond : J ⋆ᵣ₊ T ≤ J + J ⋆ᵣ₊ (J ⋆ᵣ₊ T) := by
    have h := addRingConvolution_ennreal_mono (le_refl J) hfirst
    simpa only [addRingConvolution_add _ _ _ (fun _ => ENNReal.summable)
      (fun _ => ENNReal.summable), addRingConvolution_single] using h
  have hTe : T e ≤ (J ⋆ᵣ₊ T) e := by
    refine (tau_le_tsum_offDiagonal_mul_tau q he.ne).trans_eq ?_
    rw [addRingConvolution_eq_tsum_sub]
    apply tsum_congr
    intro v
    rw [tau_eq_rooted_of_add_right q (homogeneous_zdGraph_add p) v e]
  have h := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hJz e, addRingConvolution_ennreal_ne_top hJ hJT e⟩)
    (hTe.trans (hsecond e))
  rw [ENNReal.toReal_add (hJz e) (addRingConvolution_ennreal_ne_top hJ hJT e)] at h
  simp only [toReal_addRingConvolution_ennreal hJz hJTz,
    toReal_addRingConvolution_ennreal hJz hTz, J, q, nn_offDiagonal_toReal] at h
  have hJe : homogeneousProfile (zdGraph d) p s(0, e) = p :=
    homogeneousProfile_of_mem p (by simpa only [SimpleGraph.mem_edgeSet] using he)
  rw [hJe] at h
  exact h.trans (add_le_add le_rfl ((le_abs_self _).trans
    (abs_homogeneous_step_twice_tau_le hd p hchi hK0 hK e)))

/-- The actual origin weighted pair has an explicit `1/d` bound. The direct
neighbour term uses `631/1260`, and the marked cubic term uses `53/105`.
The actual step mass is retained instead of replacing it by the weak bound. -/
theorem diagramWeightedPair_nn_zero_le_explicit
    (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    let j : ℝ := 2 * d * (p : ℝ)
    (diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) 0).toReal ≤
      (j * ((p : ℝ) + j ^ 2 * K * (631 / (1260 * (d : ℝ)))) +
        300 * j ^ 2 * K ^ 2 * (53 / (105 * (d : ℝ)))) * (1 - nearestNeighborSymbol k) := by
  let q := homogeneousProfile (zdGraph d) p
  let j : ℝ := 2 * d * (p : ℝ)
  have hd0 : 0 < d := by omega
  let e : Fin d → ℤ := Function.update 0 ⟨0, hd0⟩ 1
  have he : (zdGraph d).Adj 0 e := by
    apply (zdGraph_adj_iff_eq_update 0 e).mpr
    exact ⟨(⟨0, hd0⟩, true), by simp [e]⟩
  have hparts : (rowSum (fun e => unitInterval.toENNReal (q e)) 0).toReal ≤ K ∧
      fourierRatioSup q ≤ K ∧ fourierDifferenceSup q ≤ K := by
    simpa only [fourierBootstrap, max_le_iff] using hK
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg.trans hparts.1
  have hr := susceptibilityWalkParameter_mem_Ico q hchi
  have ht := tau_nn_neighbor_toReal_le_firstStep hd p he hchi hK0 hparts.2.1
  have hB : ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
    nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent (susceptibilityWalkParameter q) l ^ 3) ≤
      53 / (105 * (d : ℝ)) := by
    simpa only [nearestNeighborSymbol, nearestNeighborResolvent, inv_pow, div_eq_mul_inv]
      using integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr.1 hr.2
  apply (diagramWeightedPair_nn_zero_le_weighted_integral hd0 p he hchi hK k).trans
  apply mul_le_mul_of_nonneg_right _
    (sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 k)).2)
  exact add_le_add (mul_le_mul_of_nonneg_left ht
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) p.2.1))
    (mul_le_mul_of_nonneg_left hB (by positivity))

end PercLib.Percolation.Bond.Lace
