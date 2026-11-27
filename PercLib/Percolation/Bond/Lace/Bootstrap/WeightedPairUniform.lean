/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original weighted-pair estimates retaining the nearest-neighbour Fourier symbol.
No upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.WeightedPairBounds
public import PercLib.Analysis.NearestNeighborResolventSmallPowers

/-!
# Uniform weighted-pair estimates with the actual step symbol

## Main results

Cauchy--Schwarz is applied to the positive product of three massive resolvents.
The two resulting integrals use the actual shifted positive-series bounds.
The squared-symbol weight is never translated with the resolvent factors.
-/

@[expose] public section
noncomputable section

open MeasureTheory Metric Real PercLib.Analysis PercLib.Models.Site DiscreteConvolution
open scoped ENNReal DiscreteConvolution

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- The actual cosine-weighted pair is finite at finite susceptibility.
Consequently its real-valued estimates also control its extended-nonnegative value. -/
theorem diagramWeightedPair_nn_cosine_ne_top
    (p : unitInterval) (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (k : Fin d → ℝ) (a : Fin d → ℤ) :
    diagramWeightedPair (homogeneousProfile (zdGraph d) p)
      (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) a ≠ ⊤ := by
  apply diagramWeightedPair_ne_top_of_bounded_weight _ (homogeneous_zdGraph_add p) _ 2
    (by norm_num) _ (nn_step_mass_ne_top p) hchi a
  intro z
  calc
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal
      (show 1 - cos (∑ i, k i * (z i : ℝ)) ≤ 2 by
        linarith [neg_one_le_cos (∑ i, k i * (z i : ℝ))])
    _ = _ := by norm_num

private theorem continuous_fourierBall_integrable
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) : IntegrableOn f (ball 0 π) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Fin d → ℝ) π)).mono_set
    ball_subset_closedBall

/-- A single absolute step symbol is controlled by the geometric mean of the
weighted and unweighted cubic resolvent integrals, uniformly in both shifts. -/
theorem integral_abs_symbol_mul_shifted_resolvents_le
    (hd : 0 < d) {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (a b : Fin d → ℝ) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      |nearestNeighborSymbol l| * nearestNeighborResolvent r l *
        nearestNeighborResolvent r (l + a) * nearestNeighborResolvent r (l + b)) ≤
      sqrt ((((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) *
        (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborResolvent r l ^ 3)) := by
  let C := nearestNeighborResolvent (d := d) r
  let P : (Fin d → ℝ) → ℝ := fun l => C l * C (l + a) * C (l + b)
  let f : (Fin d → ℝ) → ℝ := fun l => |nearestNeighborSymbol l| * sqrt (P l)
  let g : (Fin d → ℝ) → ℝ := fun l => sqrt (P l)
  let N : ℝ := ((2 * π) ^ d)⁻¹
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hC : Continuous C := continuous_nearestNeighborResolvent hd hr
  have hD : Continuous (nearestNeighborSymbol (d := d)) := by unfold nearestNeighborSymbol; fun_prop
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hP0 (l) : 0 ≤ P l := mul_nonneg
    (mul_nonneg (nearestNeighborResolvent_pos hd hr l).le
      (nearestNeighborResolvent_pos hd hr (l + a)).le)
    (nearestNeighborResolvent_pos hd hr (l + b)).le
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hfm : MemLp f 2 (volume.restrict (ball 0 π)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
      (continuous_fourierBall_integrable (hf.pow 2))
  have hgm : MemLp g 2 (volume.restrict (ball 0 π)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
      (continuous_fourierBall_integrable (hg.pow 2))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (ball 0 π))
    (f := f) (g := g) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun l => mul_nonneg (abs_nonneg _) (sqrt_nonneg (P l))))
    (Filter.Eventually.of_forall (fun l => sqrt_nonneg (P l)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) _ by simpa using hfm)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) _ by simpa using hgm)
  have hfg (l) : f l * g l = |nearestNeighborSymbol l| * P l := by
    dsimp only [f, g]
    rw [mul_assoc, mul_self_sqrt (hP0 l)]
  have hf2 (l) : f l ^ (2 : ℝ) = nearestNeighborSymbol l ^ 2 * P l := by
    rw [Real.rpow_two]
    dsimp only [f]
    rw [mul_pow, sq_abs, sq_sqrt (hP0 l)]
  have hg2 (l) : g l ^ (2 : ℝ) = P l := by
    rw [Real.rpow_two]
    exact sq_sqrt (hP0 l)
  simp only [hfg, hf2, hg2, ← sqrt_eq_rpow] at h
  have hR0 : 0 ≤ ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * P l :=
    integral_nonneg fun l => mul_nonneg (sq_nonneg _) (hP0 l)
  have hS0 : 0 ≤ ∫ l in ball (0 : Fin d → ℝ) π, P l := integral_nonneg hP0
  have hB := integral_nearestNeighborSymbol_sq_mul_shifted_resolvents_le hd hr.1 hr.2 a b
  have hS := integral_shifted_nearestNeighborResolvents_le hd hr.1 hr.2 a b
  have hB0 : 0 ≤ N * ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * C l ^ 3 :=
    mul_nonneg hN (integral_nonneg fun l =>
      mul_nonneg (sq_nonneg _) (pow_nonneg (nearestNeighborResolvent_pos hd hr l).le _))
  have hB' : N * (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * P l) ≤
      N * ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * C l ^ 3 := by
    simpa only [P, C, mul_assoc, N] using hB
  calc
    _ = N * ∫ l in ball (0 : Fin d → ℝ) π, |nearestNeighborSymbol l| * P l := by
      simp only [P, C, N, mul_assoc]
    _ ≤ N * (sqrt (∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * P l) *
        sqrt (∫ l in ball (0 : Fin d → ℝ) π, P l)) := mul_le_mul_of_nonneg_left h hN
    _ = sqrt ((N * ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * P l) *
        (N * ∫ l in ball (0 : Fin d → ℝ) π, P l)) := by
      rw [show (N * ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * P l) *
          (N * ∫ l in ball (0 : Fin d → ℝ) π, P l) =
          N ^ 2 * ((∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborSymbol l ^ 2 * P l) *
            ∫ l in ball (0 : Fin d → ℝ) π, P l) by ring,
        sqrt_mul (sq_nonneg N), sqrt_sq_eq_abs, abs_of_nonneg hN, sqrt_mul hR0]
    _ ≤ _ := sqrt_le_sqrt (mul_le_mul hB' hS (mul_nonneg hN hS0) hB0)

/-- The three marked resolvent terms retain a single absolute step symbol,
with the factor three supplied by the actual arbitrary-shift estimates. -/
theorem integral_abs_symbol_mul_resolvent_mul_bootstrapTriple_le
    (hd : 0 < d) {r : ℝ} (hr : r ∈ Set.Ico (0 : ℝ) 1) (k : Fin d → ℝ) :
    ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      |nearestNeighborSymbol l| * nearestNeighborResolvent r l *
        bootstrapTripleProduct r k l) ≤
      3 * sqrt ((((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) *
        (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
          nearestNeighborResolvent r l ^ 3)) := by
  let C := nearestNeighborResolvent (d := d) r
  have hc : Continuous C := continuous_nearestNeighborResolvent hd hr
  have hint (a b : Fin d → ℝ) : IntegrableOn
      (fun l => |nearestNeighborSymbol l| * C l * C (l + a) * C (l + b)) (ball 0 π) := by
    apply continuous_fourierBall_integrable
    unfold nearestNeighborSymbol
    fun_prop
  have hp (l : Fin d → ℝ) :
      |nearestNeighborSymbol l| * C l * bootstrapTripleProduct r k l =
        (|nearestNeighborSymbol l| * C l * C (l + -k) * C (l + 0) +
          |nearestNeighborSymbol l| * C l * C (l + 0) * C (l + k)) +
            |nearestNeighborSymbol l| * C l * C (l + -k) * C (l + k) := by
    simp only [bootstrapTripleProduct, add_zero, ← sub_eq_add_neg, C]
    ring
  change _ * (∫ l in ball (0 : Fin d → ℝ) π,
    |nearestNeighborSymbol l| * C l * bootstrapTripleProduct r k l) ≤ _
  simp_rw [hp]
  have hiadd : IntegrableOn (fun l =>
      |nearestNeighborSymbol l| * C l * C (l + -k) * C (l + 0) +
        |nearestNeighborSymbol l| * C l * C (l + 0) * C (l + k)) (ball 0 π) :=
    (hint (-k) 0).add (hint 0 k)
  rw [integral_add hiadd (hint (-k) k), integral_add (hint (-k) 0) (hint 0 k),
    mul_add, mul_add]
  have h1 := integral_abs_symbol_mul_shifted_resolvents_le hd hr (-k) 0
  have h2 := integral_abs_symbol_mul_shifted_resolvents_le hd hr 0 k
  have h3 := integral_abs_symbol_mul_shifted_resolvents_le hd hr (-k) k
  linarith

/-- The real convolution form of the uniform character split applies to the
actual nearest-neighbour law at every finite-susceptibility probability. -/
theorem diagramWeightedPair_nn_toReal_le_convolutions
    (p : unitInterval) (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    (k : Fin d → ℝ) (a : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let J : (Fin d → ℤ) → ℝ := fun z => (q s(0, z) : ℝ)
    let T := fun z => (tau q 0 z).toReal
    let w := fun z : Fin d → ℤ => 1 - cos (∑ i, k i * (z i : ℝ))
    (diagramWeightedPair q (fun z => ENNReal.ofReal (w z)) a).toReal ≤
      2 * (((fun z => J z * w z) ⋆ᵣ₊ (T ⋆ᵣ₊ T)) (-a) +
        (J ⋆ᵣ₊ ((fun z => T z * w z) ⋆ᵣ₊ T)) (-a)) := by
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
  have hmarked (F : (Fin d → ℤ) → ℝ≥0∞) (hF : (∑' z, F z) ≠ ⊤) :
      (∑' z, F z * w z) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hF (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hw z)
  have hJW := hmarked J hJ
  have hTW := hmarked T hT
  have hJWz (z) : J z * w z ≠ ⊤ := ENNReal.mul_ne_top (hJz z) ENNReal.ofReal_ne_top
  have hTWz (z) : T z * w z ≠ ⊤ := ENNReal.mul_ne_top (hTz z) ENNReal.ofReal_ne_top
  have hTT : (∑' z, (T ⋆ᵣ₊ T) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hT hT
  have hTTz (z) : (T ⋆ᵣ₊ T) z ≠ ⊤ := addRingConvolution_ennreal_ne_top hT hT z
  have hTWT : (∑' z, ((fun z => T z * w z) ⋆ᵣ₊ T) z) ≠ ⊤ := by
    rw [tsum_addRingConvolution_ennreal]
    exact ENNReal.mul_ne_top hTW hT
  have hTWTz (z) : ((fun z => T z * w z) ⋆ᵣ₊ T) z ≠ ⊤ :=
    addRingConvolution_ennreal_ne_top hTW hT z
  have hraw := diagramWeightedPair_character_le_convolutions q
    (homogeneous_zdGraph_add p) (latticeCharacter k) a
  dsimp only at hraw
  simp only [latticeCharacter_re] at hraw
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (ENNReal.add_ne_top.mpr ⟨addRingConvolution_ennreal_ne_top hJW hTT (-a),
        addRingConvolution_ennreal_ne_top hJ hTWT (-a)⟩)) hraw
  rw [ENNReal.toReal_mul, ENNReal.toReal_add
    (addRingConvolution_ennreal_ne_top hJW hTT (-a))
    (addRingConvolution_ennreal_ne_top hJ hTWT (-a))] at h
  simp only [toReal_addRingConvolution_ennreal hJWz hTTz,
    toReal_addRingConvolution_ennreal hJz hTWTz,
    toReal_addRingConvolution_ennreal hTz hTz,
    toReal_addRingConvolution_ennreal hTWz hTz, ENNReal.toReal_mul] at h
  have hwreal (z : Fin d → ℤ) : (ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))).toReal =
      1 - cos (∑ i, k i * (z i : ℝ)) :=
    ENNReal.toReal_ofReal (sub_nonneg.mpr (cos_le_one _))
  simpa only [w, hwreal, J, T, q, nn_offDiagonal_toReal, ENNReal.toReal_ofNat] using h

private theorem convolution_le_integral_majorant
    {f g : (Fin d → ℤ) → ℝ} (hf : Summable f) (hg : Summable g)
    (hef : Function.Even f) (heg : Function.Even g)
    {M : (Fin d → ℝ) → ℝ} (hM : IntegrableOn M (ball 0 π)) (A : ℝ)
    (hpoint : ∀ l, |latticeCosineTransform f l * latticeCosineTransform g l| ≤ A * M l)
    (x : Fin d → ℤ) :
    (f ⋆ᵣ₊ g) x ≤ A * (((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π, M l) := by
  have hbase := (le_abs_self _).trans
    (abs_addRingConvolution_le_normalized_integral hf hg hef heg x)
  have hi := integral_mono_of_nonneg (Filter.Eventually.of_forall fun l => abs_nonneg
      (latticeCosineTransform f l * latticeCosineTransform g l))
    (hM.const_mul A) (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hi
  exact hbase.trans (by
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left hi
      (show (0 : ℝ) ≤ ((2 * π) ^ d)⁻¹ by positivity))

/-- The actual uniform weighted pair keeps one absolute nearest-neighbour
symbol. Cauchy--Schwarz turns that symbol into a square-root dimensional gain. -/
theorem diagramWeightedPair_nn_le_resolvent_integrals
    (hd : 0 < d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) (a : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let j : ℝ := 2 * d * (p : ℝ)
    let r := susceptibilityWalkParameter q
    let S2 := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborResolvent r l ^ 2
    let S3 := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π, nearestNeighborResolvent r l ^ 3
    let B3 := ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3
    (diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) a).toReal ≤
      2 * j * K ^ 2 * (S2 + 300 * sqrt (B3 * S3)) * (1 - nearestNeighborSymbol k) := by
  let q := homogeneousProfile (zdGraph d) p
  let J : (Fin d → ℤ) → ℝ := fun z => (q s(0, z) : ℝ)
  let T := fun z => (tau q 0 z).toReal
  let w := fun z : Fin d → ℤ => 1 - cos (∑ i, k i * (z i : ℝ))
  let Jk := fun z => J z * w z
  let Tk := fun z => T z * w z
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
  have hj : 0 ≤ j := mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) p.2.1
  have hg : 0 ≤ g := sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd k)).2
  have hC0 (l) : 0 ≤ C l := (nearestNeighborResolvent_pos hd hr l).le
  have hJ : Summable J := summable_homogeneous_zdGraph p
  have hT : Summable T := ENNReal.summable_toReal (by rwa [← chi_eq_tsum_tau])
  have hw0 (z) : 0 ≤ w z := sub_nonneg.mpr (cos_le_one _)
  have hJ0 (z) : 0 ≤ J z := (q s(0, z)).2.1
  have hJk : Summable Jk := by
    simpa only [abs_of_nonneg (hJ0 _)] using
      summable_abs_mul_one_sub_cos hJ (fun z => ∑ i, k i * (z i : ℝ))
  have hTk : Summable Tk := summable_tau_mul_cosine_weight q hchi k
  have heJ : Function.Even J := even_homogeneous_zdGraph p
  have heT : Function.Even T := fun z => congrArg ENNReal.toReal
    (tau_homogeneous_zdGraph_neg p z)
  have hew : Function.Even w := by
    intro z
    simp only [w, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, cos_neg]
  have heJk : Function.Even Jk := by intro z; exact congrArg₂ (· * ·) (heJ z) (hew z)
  have heTk : Function.Even Tk := by intro z; exact congrArg₂ (· * ·) (heT z) (hew z)
  have hsecond : spatialMoment q 0 (fun z => ENNReal.ofReal (‖z‖ ^ 2)) ≠ ⊤ :=
    (spatialMoment_sq_lt_top_of_finiteRange_of_transitive q 0 (by norm_num : (0 : ℝ) ≤ 1)
      (homogeneous_zdGraph_eq_zero_of_one_lt_norm p) (homogeneous_zdGraph_transitive p) hchi).ne
  have hJkhat (l : Fin d → ℝ) : |latticeCosineTransform Jk l| ≤ j * g := by
    calc
      _ ≤ ∑' z, Jk z := by
        simpa only [latticeCosineTransform, Real.norm_eq_abs] using
          (tsum_of_norm_bounded hJk.hasSum (fun z =>
            show ‖Jk z * cos (∑ i, l i * (z i : ℝ))‖ ≤ Jk z by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hJ0 z) (hw0 z))]
              exact mul_le_of_le_one_right (mul_nonneg (hJ0 z) (hw0 z)) (abs_cos_le_one _)))
      _ = _ := tsum_homogeneous_zdGraph_cosine_weight hd p k
  have hτ (l) : |latticeCosineTransform T l| ≤ K * C l :=
    abs_tauFourier_le_mul_resolvent_of_fourierRatioSup_le hd q hchi hparts.2.1 l
  have hτk (l) : |latticeCosineTransform Tk l| ≤
      100 * K * g * bootstrapTripleProduct r k l :=
    abs_tau_weightFourier_le_of_fourierDifferenceSup_le hd q hchi hsecond hparts.2.2 k l
  have hfirst : (Jk ⋆ᵣ₊ (T ⋆ᵣ₊ T)) (-a) ≤
      (j * K ^ 2 * g) * (N * ∫ l in ball (0 : Fin d → ℝ) π, C l ^ 2) := by
    apply convolution_le_integral_majorant hJk (summable_addRingConvolution_real hT hT)
      heJk (even_addRingConvolution heT heT) (integrableOn_nearestNeighborResolvent_pow hd hr 2)
    intro l
    rw [latticeCosineTransform_addRingConvolution hT hT heT, abs_mul, abs_mul]
    exact (mul_le_mul (hJkhat l)
      (mul_le_mul (hτ l) (hτ l) (abs_nonneg _) (mul_nonneg hK0 (hC0 l)))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hj hg)).trans_eq (by ring)
  have hc : Continuous C := continuous_nearestNeighborResolvent hd hr
  have hV : Continuous (bootstrapTripleProduct r k) := by
    change Continuous (fun l => C (l - k) * C l + C l * C (l + k) + C (l - k) * C (l + k))
    fun_prop
  have hM : IntegrableOn (fun l => |nearestNeighborSymbol l| * C l *
      bootstrapTripleProduct r k l) (ball 0 π) := by
    apply continuous_fourierBall_integrable
    unfold nearestNeighborSymbol
    fun_prop
  have hmarked : (J ⋆ᵣ₊ (Tk ⋆ᵣ₊ T)) (-a) ≤
      (100 * j * K ^ 2 * g) * (N * ∫ l in ball (0 : Fin d → ℝ) π,
        |nearestNeighborSymbol l| * C l * bootstrapTripleProduct r k l) := by
    apply convolution_le_integral_majorant hJ (summable_addRingConvolution_real hTk hT)
      heJ (even_addRingConvolution heTk heT) hM
    intro l
    rw [latticeCosineTransform_addRingConvolution hTk hT heTk,
      latticeCosineTransform_homogeneous_zdGraph hd p]
    change |(j * nearestNeighborSymbol l) *
      (latticeCosineTransform Tk l * latticeCosineTransform T l)| ≤ _
    rw [abs_mul (j * nearestNeighborSymbol l) _, abs_mul j (nearestNeighborSymbol l),
      abs_of_nonneg hj, abs_mul (latticeCosineTransform Tk l) (latticeCosineTransform T l)]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul (hτk l) (hτ l) (abs_nonneg _) (by
        have hV0 : 0 ≤ bootstrapTripleProduct r k l :=
          add_nonneg (add_nonneg (mul_nonneg (hC0 (l - k)) (hC0 l))
            (mul_nonneg (hC0 l) (hC0 (l + k))))
            (mul_nonneg (hC0 (l - k)) (hC0 (l + k)))
        positivity)) (mul_nonneg hj (abs_nonneg (nearestNeighborSymbol l)))
    exact hh.trans_eq (by ring)
  have hshift := integral_abs_symbol_mul_resolvent_mul_bootstrapTriple_le hd hr k
  have hmarked' := hmarked.trans (mul_le_mul_of_nonneg_left hshift
    (show 0 ≤ 100 * j * K ^ 2 * g by positivity))
  have h := (diagramWeightedPair_nn_toReal_le_convolutions p hchi k a).trans
    (mul_le_mul_of_nonneg_left (add_le_add hfirst hmarked') (by norm_num : (0 : ℝ) ≤ 2))
  convert h using 1
  dsimp only [N, g, j, C, r]
  ring

/-- An explicit uniform weighted-pair bound retaining the actual step mass,
the squared massive parameter, and the square-root dimensional gain. -/
theorem diagramWeightedPair_nn_le_explicit
    (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) (a : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let j : ℝ := 2 * d * (p : ℝ)
    let r := susceptibilityWalkParameter q
    (diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) a).toReal ≤
      2 * j * K ^ 2 * (1 + r ^ 2 * (379 / (252 * (d : ℝ))) +
        300 * sqrt ((53 / (105 * (d : ℝ))) *
          (1 + r ^ 2 * (253 / (84 * (d : ℝ)))))) * (1 - nearestNeighborSymbol k) := by
  let q := homogeneousProfile (zdGraph d) p
  let j : ℝ := 2 * d * (p : ℝ)
  let r := susceptibilityWalkParameter q
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hj : 0 ≤ j := mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) p.2.1
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := susceptibilityWalkParameter_mem_Ico q hchi
  have h2 := integral_nearestNeighborResolvent_sq_le_refined hd hr
  have h3 := integral_nearestNeighborResolvent_cube_le_refined hd hr
  have hB : ((2 * π) ^ d)⁻¹ * (∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborSymbol l ^ 2 * nearestNeighborResolvent r l ^ 3) ≤
      53 / (105 * (d : ℝ)) := by
    simpa only [nearestNeighborSymbol, nearestNeighborResolvent, inv_pow, div_eq_mul_inv]
      using integral_nearestNeighborSymbol_sq_mul_inv_cube_le hd hr.1 hr.2
  have h3pos : 0 ≤ ((2 * π) ^ d)⁻¹ * ∫ l in ball (0 : Fin d → ℝ) π,
      nearestNeighborResolvent r l ^ 3 := mul_nonneg (by positivity)
        (integral_nonneg fun l => pow_nonneg (nearestNeighborResolvent_pos hd0 hr l).le _)
  have hsqrt := sqrt_le_sqrt (mul_le_mul hB h3 h3pos
    (show 0 ≤ 53 / (105 * (d : ℝ)) by positivity))
  apply (diagramWeightedPair_nn_le_resolvent_integrals hd0 p hchi hK k a).trans
  apply mul_le_mul_of_nonneg_right _
    (sub_nonneg.mpr (abs_le.mp (nearestNeighborSymbol_abs_le_one hd0 k)).2)
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ 2 * j * K ^ 2 by positivity)
  exact add_le_add h2 (mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 300))

/-- The explicit uniform estimate in the extended-nonnegative diagram interface. -/
theorem diagramWeightedPair_nn_le_ofReal_explicit
    (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) (a : Fin d → ℤ) :
    let q := homogeneousProfile (zdGraph d) p
    let j : ℝ := 2 * d * (p : ℝ)
    let r := susceptibilityWalkParameter q
    diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) a ≤
      ENNReal.ofReal (2 * j * K ^ 2 * (1 + r ^ 2 * (379 / (252 * (d : ℝ))) +
        300 * sqrt ((53 / (105 * (d : ℝ))) *
          (1 + r ^ 2 * (253 / (84 * (d : ℝ)))))) * (1 - nearestNeighborSymbol k)) := by
  have h := ENNReal.ofReal_le_ofReal (diagramWeightedPair_nn_le_explicit hd p hchi hK k a)
  rwa [ENNReal.ofReal_toReal (diagramWeightedPair_nn_cosine_ne_top p hchi k a)] at h

/-- The explicit origin estimate in the extended-nonnegative diagram interface. -/
theorem diagramWeightedPair_nn_zero_le_ofReal_explicit
    (hd : 1000 ≤ d) (p : unitInterval)
    (hchi : chi (homogeneousProfile (zdGraph d) p) 0 ≠ ⊤)
    {K : ℝ} (hK : fourierBootstrap (homogeneousProfile (zdGraph d) p) ≤ K)
    (k : Fin d → ℝ) :
    let q := homogeneousProfile (zdGraph d) p
    let j : ℝ := 2 * d * (p : ℝ)
    diagramWeightedPair q (fun z => ENNReal.ofReal (1 - cos (∑ i, k i * (z i : ℝ)))) 0 ≤
      ENNReal.ofReal ((j * ((p : ℝ) + j ^ 2 * K * (631 / (1260 * (d : ℝ)))) +
        300 * j ^ 2 * K ^ 2 * (53 / (105 * (d : ℝ)))) * (1 - nearestNeighborSymbol k)) := by
  have h := ENNReal.ofReal_le_ofReal (diagramWeightedPair_nn_zero_le_explicit hd p hchi hK k)
  rwa [ENNReal.ofReal_toReal (diagramWeightedPair_nn_cosine_ne_top p hchi k 0)] at h

end PercLib.Percolation.Bond.Lace
