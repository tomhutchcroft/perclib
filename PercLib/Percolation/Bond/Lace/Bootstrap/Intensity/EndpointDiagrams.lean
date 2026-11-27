/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Bootstrap.DiagramNorms
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.IntensityScaling

/-!
# Passing positive diagram bounds to an intensity endpoint

## Main results

Left convergence of the actual two-point probabilities passes a uniform bound
on the step-weighted triple convolution to the endpoint. The proof uses finite
partial sums of nonnegative diagrams and does not require finite susceptibility
or finite clusters at the endpoint. In particular, it does not use an unordered
Fourier series for a nonsummable critical two-point function.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter DiscreteConvolution
open scoped ENNReal NNReal Topology DiscreteConvolution

namespace PercLib.Percolation.Bond

/-- Actual two-point probabilities converge along intensities approaching a
larger endpoint from below, including at infinite susceptibility. -/
theorem tendsto_tau_intensity_of_le {V : Type*} [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℕ → ℝ≥0) (b : ℝ≥0)
    (hle : ∀ n, β n ≤ b) (hlim : Tendsto β atTop (𝓝 b)) (x y : V) :
    Tendsto (fun n => tau (intensityProfile J (β n)) x y) atTop
      (𝓝 (tau (intensityProfile J b) x y)) := by
  have ht := continuousWithinAt_tau_Iic (q := intensityProfile J)
    (fun _ _ hab e => intensityProfile_mono J hab e)
    (fun e => (continuous_intensityProfile J e).subtype_mk _) x y b
  exact ht.tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim, Eventually.of_forall hle⟩)

namespace Lace

private theorem tsum_le_of_pointwise_limit {ι : Type*} {F : ℕ → ι → ℝ≥0∞}
    {f : ι → ℝ≥0∞} {C : ℝ≥0∞}
    (hlim : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (f i)))
    (hbound : ∀ n, (∑' i, F n i) ≤ C) : (∑' i, f i) ≤ C := by
  classical
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  apply le_of_tendsto (tendsto_finsetSum s fun i _ => hlim i)
  exact Eventually.of_forall fun n => (ENNReal.sum_le_tsum s).trans (hbound n)

/-- Uniform actual continuation-triangle bounds pass to the endpoint by
nonnegative partial-sum limits, with no critical susceptibility premise. -/
theorem step_tau_three_intensity_endpoint_le {G : Type*} [AddCommGroup G] [Countable G]
    (J : Sym2 G → ℝ≥0) (β : ℕ → ℝ≥0) (b : ℝ≥0)
    (hle : ∀ n, β n ≤ b) (hlim : Tendsto β atTop (𝓝 b)) (x : G) (C : ℝ≥0∞)
    (hbound : ∀ n,
      let q := intensityProfile J (β n)
      (offDiagonal (fun u v : G =>
        (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) 0 ⋆ᵣ₊
          (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ C) :
    let q := intensityProfile J b
    (offDiagonal (fun u v : G =>
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) 0 ⋆ᵣ₊
        (tau q 0 ⋆ᵣ₊ (tau q 0 ⋆ᵣ₊ tau q 0))) x ≤ C := by
  classical
  let T (t : ℝ≥0) : G → ℝ≥0∞ := tau (intensityProfile J t) 0
  let S (t : ℝ≥0) : G → ℝ≥0∞ := offDiagonal (fun u v : G =>
    (unitInterval.toNNReal (intensityProfile J t s(u, v)) : ℝ≥0∞)) 0
  have hT (z : G) : Tendsto (fun n => T (β n) z) atTop (𝓝 (T b z)) :=
    tendsto_tau_intensity_of_le J β b hle hlim 0 z
  have hTf (z : G) : T b z ≠ ⊤ := measure_ne_top _ _
  have hSf (z : G) : S b z ≠ ⊤ := by
    dsimp only [S]
    rw [offDiagonal_apply]
    split_ifs <;> simp
  have hS (z : G) : Tendsto (fun n => S (β n) z) atTop (𝓝 (S b z)) := by
    by_cases hz : z = 0
    · simp only [S, hz, offDiagonal_self]
      exact tendsto_const_nhds
    · have hp := (ENNReal.continuous_ofReal.comp
        (continuous_intensityProfile J s(0, z))).continuousAt.tendsto.comp hlim
      simpa only [Function.comp_def, S, offDiagonal_apply, hz, ↓reduceIte,
        ← unitInterval.coe_toNNReal, ENNReal.ofReal_coe_nnreal] using hp
  let F (t : ℝ≥0) (p : G × G × G) : ℝ≥0∞ :=
    S t p.1 * (T t p.2.1 * (T t p.2.2 * T t (x - p.1 - p.2.1 - p.2.2)))
  have hF (p : G × G × G) : Tendsto (fun n => F (β n) p) atTop (𝓝 (F b p)) := by
    have h23 := ENNReal.Tendsto.mul (hT p.2.2)
      (Or.inr (hTf (x - p.1 - p.2.1 - p.2.2)))
      (hT (x - p.1 - p.2.1 - p.2.2)) (Or.inr (hTf p.2.2))
    have h123 := ENNReal.Tendsto.mul (hT p.2.1)
      (Or.inr (ENNReal.mul_ne_top (hTf _) (hTf _))) h23 (Or.inr (hTf p.2.1))
    exact ENNReal.Tendsto.mul (hS p.1)
      (Or.inr (ENNReal.mul_ne_top (hTf _) (ENNReal.mul_ne_top (hTf _) (hTf _))))
      h123 (Or.inr (hSf p.1))
  have hsum (n : ℕ) : (∑' p : G × G × G, F (β n) p) ≤ C := by
    have hn := hbound n
    simpa only [F, S, T, addRingConvolution_eq_tsum_sub,
      ← ENNReal.tsum_mul_left, ENNReal.tsum_prod'] using hn
  have h := tsum_le_of_pointwise_limit hF hsum
  simpa only [F, S, T, addRingConvolution_eq_tsum_sub,
    ← ENNReal.tsum_mul_left, ENNReal.tsum_prod'] using h

end Lace
end PercLib.Percolation.Bond
