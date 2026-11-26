/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc, file `PercLib/CriticalLRP/RussoInf/DominatedFlux.lean`,
contributed by `yujinhkim`. Licence: Apache-2.0, as declared in that file's header and in
`third_party/critical-lrp/NOTICE.md` of that commit (upstream origin
`yujinhkim/Critical-Long-range-percolation` at 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf, not
independently verified). Changes: namespace `RussoDominated` becomes `PercLib.Analysis`; the helper
`ioc_subset_uIcc` is replaced by mathlib's `Set.Icc_subset_uIcc`; focused imports; `autoImplicit`
off.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Limits of derivatives under a dominator

Analytic core of the infinite-volume exchange in the proof of Lemma I.4.1 of Hutchcroft,
*Critical long-range percolation I*, arXiv:2508.18807v1.

* `integral_eq_sub_of_tendsto_hasDerivAt`: if `f n → g` and `f' n → g'` pointwise on `I`,
  `f' n` is the derivative of `f n` on `I` and `‖f' n‖ ≤ bound` with `bound` interval
  integrable, then `∫_a^b g' = g b − g a` whenever `uIcc a b ⊆ I`.
* `hasDerivAt_of_tendsto_hasDerivAt`: on an open `I`, `g` has derivative `g' x₀` at every
  `x₀ ∈ I` where `g'` is continuous.

No uniform convergence of the derivatives is assumed (compare mathlib's
`hasDerivAt_of_tendstoLocallyUniformlyOn`).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace PercLib.Analysis

/-! ### The integrated identity -/

/-- **Integrated limit-of-derivatives theorem.**

Let `f n` have derivative `f' n` at every point of a set `I` containing `uIcc a b`, let the
derivatives `f' n` converge pointwise on `I` to `g'` and be dominated there by a single function
`bound` which is interval integrable on `a`, `b`, and let `f n` converge pointwise on `I` to `g`.
Then `∫ x in a..b, g' x = g b - g a`.

No uniformity of the convergence of the derivatives is assumed; this is the dominated-convergence
(equivalently, Vitali-type) replacement for Mathlib's
`hasDerivAt_of_tendstoLocallyUniformlyOn`. -/
theorem integral_eq_sub_of_tendsto_hasDerivAt
    {I : Set ℝ} {f f' : ℕ → ℝ → ℝ} {g g' bound : ℝ → ℝ} {a b : ℝ}
    (hsub : Set.uIcc a b ⊆ I)
    (hderiv : ∀ n, ∀ x ∈ I, HasDerivAt (f n) (f' n x) x)
    (hmeas : ∀ n, AEStronglyMeasurable (f' n) volume)
    (hbound : ∀ n, ∀ x ∈ I, ‖f' n x‖ ≤ bound x)
    (hboundint : IntervalIntegrable bound volume a b)
    (hfg : ∀ x ∈ I, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hfg' : ∀ x ∈ I, Tendsto (fun n => f' n x) atTop (𝓝 (g' x))) :
    ∫ x in a..b, g' x = g b - g a := by
  -- (i) the exact finite-window identities
  have key : ∀ n, ∫ x in a..b, f' n x = f n b - f n a := by
    intro n
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv n x (hsub hx)) ?_
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' hboundint.1 ((hmeas n).mono_measure Measure.restrict_le_self) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hbound n x (hsub (Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self hx)))
    · refine Integrable.mono' hboundint.2 ((hmeas n).mono_measure Measure.restrict_le_self) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hbound n x (hsub (Set.Icc_subset_uIcc' (Set.Ioc_subset_Icc_self hx)))
  -- (ii) dominated convergence identifies the limit of the integrals
  have hDCT : Tendsto (fun n => ∫ x in a..b, f' n x) atTop (𝓝 (∫ x in a..b, g' x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (a := a) (b := b) (f := g') (bound := bound)
      ?_ ?_ hboundint ?_
    · exact Eventually.of_forall fun n => (hmeas n).mono_measure Measure.restrict_le_self
    · exact Eventually.of_forall fun n => Eventually.of_forall fun x hx =>
        hbound n x (hsub (Set.uIoc_subset_uIcc hx))
    · exact Eventually.of_forall fun x hx => hfg' x (hsub (Set.uIoc_subset_uIcc hx))
  -- (iii) the finite-window identities converge to the increment of the limit
  have h1 : Tendsto (fun n => ∫ x in a..b, f' n x) atTop (𝓝 (g b - g a)) := by
    have hb : Tendsto (fun n => f n b - f n a) atTop (𝓝 (g b - g a)) :=
      (hfg b (hsub Set.right_mem_uIcc)).sub (hfg a (hsub Set.left_mem_uIcc))
    refine hb.congr' (Eventually.of_forall fun n => ?_)
    exact (key n).symm
  exact tendsto_nhds_unique hDCT h1

/-! ### Differentiation at continuity points of the limit flux -/

/-- **Dominated limit-of-derivatives, pointwise form.**

Under the same hypotheses as `integral_eq_sub_of_tendsto_hasDerivAt`, uniformly over the
sub-intervals of `I`, if the limiting flux `g'` is strongly measurable and continuous at `x₀`,
then `g` has derivative `g' x₀` at `x₀`.

This is the statement that replaces `hunif`: local uniform convergence of `f' n` to `g'` is not
assumed, only a dominator for `f' n` and continuity of `g'`.

Note that measurability of `f' n` and of `g'` are the only extra hypotheses compared with the
uniform-convergence theorem; in the percolation instantiation they follow from measurability in
the parameter of the edge law. -/
theorem hasDerivAt_of_tendsto_hasDerivAt
    {I : Set ℝ} (hI : IsOpen I) {f f' : ℕ → ℝ → ℝ} {g g' bound : ℝ → ℝ} {x₀ : ℝ}
    (hderiv : ∀ n, ∀ x ∈ I, HasDerivAt (f n) (f' n x) x)
    (hmeas : ∀ n, AEStronglyMeasurable (f' n) volume)
    (hbound : ∀ n, ∀ x ∈ I, ‖f' n x‖ ≤ bound x)
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable bound volume a b)
    (hfg : ∀ x ∈ I, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hfg' : ∀ x ∈ I, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)))
    (hmeasg : StronglyMeasurableAtFilter g' (𝓝 x₀) volume)
    (hcont : ContinuousAt g' x₀) (hx₀ : x₀ ∈ I) :
    HasDerivAt g (g' x₀) x₀ := by
  -- locally, `g` is the indefinite integral of `g'`
  have hident : g =ᶠ[𝓝 x₀] fun u => g x₀ + ∫ y in x₀..u, g' y := by
    obtain ⟨ρ, hρ, hρI⟩ := Metric.isOpen_iff.mp hI x₀ hx₀
    filter_upwards [Metric.ball_mem_nhds x₀ hρ] with u hu
    have hsub : Set.uIcc x₀ u ⊆ I :=
      ((convex_ball x₀ ρ).ordConnected.uIcc_subset (Metric.mem_ball_self hρ) hu).trans hρI
    have h := integral_eq_sub_of_tendsto_hasDerivAt hsub hderiv hmeas hbound
      (hboundint x₀ hx₀ u (hρI hu)) hfg hfg'
    rw [h]
    ring
  -- the indefinite integral of a continuous integrand differentiates back
  have hInt : HasDerivAt (fun u => g x₀ + ∫ y in x₀..u, g' y) (g' x₀) x₀ :=
    (intervalIntegral.integral_hasDerivAt_right (f := g') (a := x₀) (b := x₀)
      ⟨by simp, by simp⟩ hmeasg hcont).const_add (g x₀)
  exact hInt.congr_of_eventuallyEq hident


/-! ### Non-vacuity witnesses: the constant sequence `f n = sin`, `bound = 1` -/

example (a b : ℝ) : ∫ x in a..b, Real.cos x = Real.sin b - Real.sin a :=
  integral_eq_sub_of_tendsto_hasDerivAt (I := univ) (f := fun _ => Real.sin)
    (f' := fun _ => Real.cos) (bound := fun _ => 1) (subset_univ _)
    (fun _ x _ => Real.hasDerivAt_sin x)
    (fun _ => Real.continuous_cos.aestronglyMeasurable)
    (fun _ x _ => by simpa using Real.abs_cos_le_one x)
    intervalIntegrable_const
    (fun _ _ => tendsto_const_nhds) (fun _ _ => tendsto_const_nhds)

example (x₀ : ℝ) : HasDerivAt Real.sin (Real.cos x₀) x₀ :=
  hasDerivAt_of_tendsto_hasDerivAt (I := univ) isOpen_univ (f := fun _ => Real.sin)
    (f' := fun _ => Real.cos) (bound := fun _ => 1)
    (fun _ x _ => Real.hasDerivAt_sin x)
    (fun _ => Real.continuous_cos.aestronglyMeasurable)
    (fun _ x _ => by simpa using Real.abs_cos_le_one x)
    (fun _ _ _ _ => intervalIntegrable_const)
    (fun _ _ => tendsto_const_nhds) (fun _ _ => tendsto_const_nhds)
    (Real.continuous_cos.stronglyMeasurableAtFilter _ _)
    Real.continuous_cos.continuousAt (mem_univ _)

end PercLib.Analysis
