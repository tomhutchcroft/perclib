/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The Lévy measures of display (I.5.16), the Lévy exponent, and the law of a symmetric Lévy process
stopped at an independent `Exp(1)` time (the displacement law `ν_disp` of Definition I.5.16), from
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, §I.5.2.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files `PercLib/CriticalLRP/LevyAnalysis/Measures.lean`
(`levyDensInf`, `levyDensLam`, `PiInf`, `PiLam`) and
`PercLib/CriticalLRP/LevyAnalysis/Dispersion.lean` (`levyExp`, and the characteristic-function form
of `exists_nuDisp`, `exists_laplaceMixture`); licence Apache-2.0 as declared in those file headers;
upstream `yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the Haar measure parameter is replaced by `volume`; `levyDensOne`/`PiOne` are not defined
(they are the case `l = 1`); the two regimes of Definition I.5.16 are one predicate taking the
exponent. The API lemmas and witnesses are new.
-/
module

public import PercLib.Analysis.ModelNorm.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! # Lévy measures and exponentially stopped laws

On a finite-dimensional real inner product space `E` of dimension `d`, with Lebesgue measure
`volume` and a model norm `N : Seminorm ℝ E` (the norm type of the long-range kernels of
`PercLib/Models/LongRange/Defs.lean`; the paper allows any norm, and the Euclidean one is
`normSeminorm ℝ E`), display (I.5.16) defines for `α > 0`
* the cut-off Lévy measure `Π_l` with density `α ∫_{N(x)}^{l} s^(-d-α-1) ds =
  α/(d+α) (N(x)^(-d-α) - l^(-d-α))₊` (the closed form is the definition; `Π₁` is `l = 1`);
* the stable Lévy measure `Π_∞` with density `α/(d+α) N(x)^(-d-α)`.

A seminorm is absolutely homogeneous (`map_smul_eq_mul`). The densities do not need
definiteness, so they take a seminorm; the statements that use definiteness take a
`ModelNorm E` (a seminorm that vanishes only at `0`), which coerces to a seminorm. When `N` is
definite (so a norm on `E`), `E` has positive dimension, `0 < α < 2` (the
paper's jump regime) and, for `Π_l`, `l > 0`, these are Lévy measures
(`∫ min (‖x‖², 1) dΠ < ∞`), and `Π_∞` is the Lévy measure of a symmetric `α`-stable process.

The Lévy exponent of a symmetric Lévy measure `Π` is `ψ(u) = ∫ (1 - cos ⟪x, u⟫) dΠ`, taken as a
lower integral (it is finite when `∫ min (‖x‖², 1) dΠ < ∞`). Definition I.5.16 defines `ν_disp`
as the law of a symmetric Lévy process at an independent `Exp(1)` time: for `α < 2` the jump
process with Lévy measure `Π₁`, for `α ≥ 2` a Brownian motion with covariance `Σ`. In both cases
that law is the probability measure with characteristic function `u ↦ (1 + ψ(u))⁻¹`, with
`ψ(u) = ∫ (1 - cos ⟪x, u⟫) dΠ₁` or `ψ(u) = ⟪Σ u, u⟫ / 2`, and by Lévy's uniqueness theorem
this determines it; `IsExpTimeStoppedLaw` is that characterisation. The inner product is used
only in the pairing `⟪x, u⟫` of mathlib's `charFun`; the model norm `N` is independent of it.

Not defined here, and written out where used: convolutions and powers (mathlib
`Measure.conv`), the exponential law (mathlib `expMeasure`), Gaussians (mathlib
`gaussianReal`), chi-square laws (`gammaMeasure`), size-biasing (`Probability/SizeBias.lean`),
truncations, and the moment-convergence notions of the source's `MomentConvergence.lean`
(`HasSameMoments Φ ν₁ ν₂` is `∀ t, ∫ Φ t ∂ν₁ = ∫ Φ t ∂ν₂`; `monomialAlgebra` is
`Algebra.adjoin ℝ (range Φ)`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped ENNReal RealInnerProductSpace

namespace PercLib.Probability

open PercLib.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The density of the **cut-off Lévy measure** `Π_l` of (I.5.16) for the model norm `N`:
`α/(d+α) (N(x)^(-d-α) - l^(-d-α))₊`, which equals `α ∫_{N(x)}^{l} s^(-d-α-1) ds` on
`0 < N(x) ≤ l` and vanishes for `N(x) > l`. The model norm `N` is independent of the inner
product, which is used only in the pairing `⟪x, u⟫`. -/
def cutoffLevyDensity (N : Seminorm ℝ E) (α l : ℝ) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (α / (finrank ℝ E + α) *
    (N x ^ (-(finrank ℝ E : ℝ) - α) - l ^ (-(finrank ℝ E : ℝ) - α)))

/-- The density of the **stable Lévy measure** `Π_∞` of (I.5.16) for the model norm `N`:
`α/(d+α) N(x)^(-d-α)`. -/
def stableLevyDensity (N : Seminorm ℝ E) (α : ℝ) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (α / (finrank ℝ E + α) * N x ^ (-(finrank ℝ E : ℝ) - α))

/-- The **cut-off Lévy measure** `Π_l` of (I.5.16) on Lebesgue measure, for the model norm `N`;
a Lévy measure when `N` is definite, `finrank ℝ E ≥ 1`, `0 < α < 2` and `l > 0`. -/
def cutoffLevyMeasure [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Seminorm ℝ E) (α l : ℝ) : Measure E :=
  volume.withDensity (cutoffLevyDensity N α l)

/-- The **stable Lévy measure** `Π_∞` of (I.5.16) on Lebesgue measure, for the model norm `N`:
when `N` is definite, `finrank ℝ E ≥ 1` and `0 < α < 2`, the Lévy measure of the symmetric
`α`-stable process. -/
def stableLevyMeasure [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Seminorm ℝ E) (α : ℝ) : Measure E :=
  volume.withDensity (stableLevyDensity N α)

/-- The **Lévy exponent** of a symmetric Lévy measure `Π`: `ψ(u) = ∫ (1 - cos ⟪x, u⟫) dΠ(x)`,
as a lower integral. -/
def levyExponent [MeasurableSpace E] (L : Measure E) (u : E) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪x, u⟫) ∂L

/-- `ν` is the **law at an independent `Exp(1)` time** of a symmetric Lévy process with exponent
`ψ`: a probability measure with characteristic function `u ↦ (1 + ψ u)⁻¹`. With
`ψ u = (levyExponent (cutoffLevyMeasure N α 1) u).toReal` (`N` definite, `0 < α < 2`) or
`ψ u = ⟪Σ u, u⟫ / 2` (`α ≥ 2`) this characterises the displacement law `ν_disp` of Definition
I.5.16. -/
def IsExpTimeStoppedLaw [MeasurableSpace E] (ψ : E → ℝ) (ν : Measure E) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ u, charFun ν u = ((1 + ψ u : ℝ) : ℂ)⁻¹

/-! ### API -/

section Measures

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem cutoffLevyMeasure_def (N : Seminorm ℝ E) (α l : ℝ) :
    cutoffLevyMeasure N α l = volume.withDensity (cutoffLevyDensity N α l) := rfl

theorem stableLevyMeasure_def (N : Seminorm ℝ E) (α : ℝ) :
    stableLevyMeasure N α = volume.withDensity (stableLevyDensity N α) := rfl

end Measures

section Exponent

variable [MeasurableSpace E]

theorem levyExponent_def (L : Measure E) (u : E) :
    levyExponent L u = ∫⁻ x, ENNReal.ofReal (1 - Real.cos ⟪x, u⟫) ∂L := rfl

theorem isExpTimeStoppedLaw_def (ψ : E → ℝ) (ν : Measure E) :
    IsExpTimeStoppedLaw ψ ν ↔ IsProbabilityMeasure ν ∧ ∀ u, charFun ν u = ((1 + ψ u : ℝ) : ℂ)⁻¹ :=
  Iff.rfl

end Exponent

@[fun_prop]
theorem measurable_cutoffLevyDensity [MeasurableSpace E] {N : Seminorm ℝ E}
    (hN : Measurable N) (α l : ℝ) : Measurable (cutoffLevyDensity N α l) :=
  (measurable_const.mul ((hN.pow_const _).sub measurable_const)).ennreal_ofReal

@[fun_prop]
theorem measurable_stableLevyDensity [MeasurableSpace E] {N : Seminorm ℝ E}
    (hN : Measurable N) (α : ℝ) : Measurable (stableLevyDensity N α) :=
  (measurable_const.mul (hN.pow_const _)).ennreal_ofReal

/-- The cut-off density vanishes outside the ball of radius `l`. -/
theorem cutoffLevyDensity_eq_zero {N : Seminorm ℝ E} {α l : ℝ} (hα : 0 < α) (hl : 0 < l)
    {x : E} (hx : l < N x) : cutoffLevyDensity N α l x = 0 := by
  refine ENNReal.ofReal_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_)
  exact sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos hl hx.le (by linarith))

/-- Monotonicity in the cut-off: `Π_l` increases with `l` and is dominated by `Π_∞`. -/
theorem cutoffLevyDensity_mono {N : Seminorm ℝ E} {α l l' : ℝ} (hα : 0 < α) (hl : 0 < l)
    (hll' : l ≤ l') (x : E) : cutoffLevyDensity N α l x ≤ cutoffLevyDensity N α l' x := by
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact sub_le_sub_left (Real.rpow_le_rpow_of_nonpos hl hll' (by linarith)) _

theorem cutoffLevyDensity_le_stable {N : Seminorm ℝ E} {α l : ℝ} (hα : 0 < α) (hl : 0 < l)
    (x : E) : cutoffLevyDensity N α l x ≤ stableLevyDensity N α x := by
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact sub_le_self _ (Real.rpow_nonneg hl.le _)

theorem cutoffLevyMeasure_mono [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N : Seminorm ℝ E} {α l l' : ℝ} (hα : 0 < α) (hl : 0 < l) (hll' : l ≤ l') :
    cutoffLevyMeasure N α l ≤ cutoffLevyMeasure N α l' :=
  withDensity_mono (Filter.Eventually.of_forall (cutoffLevyDensity_mono hα hl hll'))

theorem cutoffLevyMeasure_le_stable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N : Seminorm ℝ E} {α l : ℝ} (hα : 0 < α) (hl : 0 < l) :
    cutoffLevyMeasure N α l ≤ stableLevyMeasure N α :=
  withDensity_mono (Filter.Eventually.of_forall (cutoffLevyDensity_le_stable hα hl))

/-- The Lévy exponent vanishes at `u = 0`. -/
@[simp] theorem levyExponent_zero_right [MeasurableSpace E]
    (L : Measure E) : levyExponent L 0 = 0 := by
  simp [levyExponent]

/-- Monotonicity of the Lévy exponent in the Lévy measure. -/
theorem levyExponent_mono [MeasurableSpace E] {L L' : Measure E} (h : L ≤ L') (u : E) :
    levyExponent L u ≤ levyExponent L' u :=
  lintegral_mono' h le_rfl

/-- For a definite `N`, the stable density is positive away from `0`. -/
theorem stableLevyDensity_pos_of_ne {N : ModelNorm E} {α : ℝ} (hα : 0 < α) {x : E}
    (hx : x ≠ 0) : 0 < stableLevyDensity N α x :=
  ENNReal.ofReal_pos.2 (mul_pos (by positivity) (Real.rpow_pos_of_pos (N.pos_iff_ne_zero.2 hx) _))

/-! ### Witnesses -/

/-- The point mass at `0` is the stopped law of the zero exponent. -/
theorem isExpTimeStoppedLaw_dirac_zero [MeasurableSpace E] [BorelSpace E] : IsExpTimeStoppedLaw
    (fun _ : E => 0) (Measure.dirac 0) :=
  ⟨inferInstance, fun u => by simp⟩

/-- At `d = 1`, `α = 1`, `l = 1` (on `ℝ`), `Π₁` is a Lévy measure:
`∫ min (x², 1) dΠ₁ < ∞`. -/
theorem lintegral_min_sq_cutoffLevyMeasure_lt_top :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂cutoffLevyMeasure (normSeminorm ℝ ℝ) 1 1 < ⊤ := by
  have hN : ∀ x : ℝ, normSeminorm ℝ ℝ x = ‖x‖ := fun _ => rfl
  rw [cutoffLevyMeasure_def, lintegral_withDensity_eq_lintegral_mul₀
    (measurable_cutoffLevyDensity (N := normSeminorm ℝ ℝ) continuous_norm.measurable 1
        1).aemeasurable
    (by fun_prop)]
  have hb : ∀ x : ℝ, cutoffLevyDensity (normSeminorm ℝ ℝ) 1 1 x *
      ENNReal.ofReal (min (‖x‖ ^ 2) 1) ≤
      (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    simp only [cutoffLevyDensity, finrank_self, Nat.cast_one, hN]
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_mul' (by positivity)]
      refine ENNReal.ofReal_le_one.2 ?_
      have hx' : ‖x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; exact hx
      rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
      · rw [← h0]; simp
      · have hp : ‖x‖ ^ (-(1 : ℝ) - 1) = (‖x‖ ^ 2)⁻¹ := by
          rw [show -(1 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg h0.le]; norm_cast
        rw [hp, min_eq_left (pow_le_one₀ h0.le hx'), Real.one_rpow]
        have h2 : 0 < ‖x‖ ^ 2 := by positivity
        rw [show 1 / (1 + 1 : ℝ) * ((‖x‖ ^ 2)⁻¹ - 1) * ‖x‖ ^ 2 = (1 - ‖x‖ ^ 2) / 2 by
          field_simp; ring]
        nlinarith
    · rw [Set.indicator_of_notMem hx]
      have hx' : 1 < ‖x‖ := by
        rw [Real.norm_eq_abs, lt_abs]; simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with h | h <;> [right; left] <;> linarith
      have := cutoffLevyDensity_eq_zero (N := normSeminorm ℝ ℝ) one_pos one_pos hx'
      simp only [cutoffLevyDensity, finrank_self, Nat.cast_one, hN] at this
      rw [this, zero_mul]
  calc _ ≤ ∫⁻ x, (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x := lintegral_mono hb
    _ = volume (Set.Icc (-1 : ℝ) 1) := lintegral_indicator_one measurableSet_Icc
    _ < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top

/-- At `d = 1`, `α = 1`, the stable density is positive away from `0`. -/
theorem stableLevyDensity_pos {x : ℝ} (hx : x ≠ 0) :
    0 < stableLevyDensity (normSeminorm ℝ ℝ) 1 x :=
  stableLevyDensity_pos_of_ne (N := ModelNorm.ofNorm ℝ) one_pos hx

end PercLib.Probability
