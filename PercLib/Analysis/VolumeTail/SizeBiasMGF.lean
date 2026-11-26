/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Size-biased Laplace identities and the fixed-rate cut-off limit in the proof of
Proposition I.3.2 of T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/SizeBiasedMGF.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source's `mean`, `secMoment`, `sbMean` and `sizeBiasedLaw` are written out as
the size-biased law `(P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ X ∂P)).map (X / a)` of
`PercLib/Probability/SizeBiasLimits.lean`, and the source's change of variables
`integral_sizeBiasedLaw` is `integral_withDensity_ofReal_div` of
`PercLib/Probability/ChiSquareMoments.lean` composed with `integral_map`; the source's kernel `kern`
(value `0` at `0`) is replaced by the kernel `f_λ` of that file (value `λ` at `0`), and the source's
kernel lemmas by `laplaceKernel_mem_Icc` and `abs_laplaceKernel_sub_le`; the identities are stated
for a random variable `X ≥ 0` a.e. on any measure space and any scale `a > 0`, with the source's
form on `ℝ` as a corollary; `import Mathlib`, `autoImplicit`, disabled linters and `#print`
lines are removed.
-/
module

public import PercLib.Probability.ChiSquareMoments

/-! # Size-biased Laplace identities and the fixed-rate cut-off limit

Let `X ≥ 0` a.e. under a measure `P`, with `0 < m = ∫ X ∂P`, and let `Q` be the law of `X / a`
under the size-biased measure `(X / m) P`,
`Q = (P.withDensity fun ω => ENNReal.ofReal (X ω / m)).map (X / a)`. Write
`f_λ(y) = (1 - e^{-λy}) / y`, `f_λ(0) = λ`.

## Main results

* `map_withDensity_ofReal_div_Iio_zero`: `Q` is carried by `[0, ∞)`.
* `isProbabilityMeasure_withDensity_ofReal_div_integral`: the size-biased measure is a
  probability measure.
* `integral_one_sub_exp_eq_mul_integral_laplaceKernel`: `E[1 - e^{-hX}] = (m / a) ∫ f_{ha} dQ`.
* `integral_mul_exp_neg_eq_mul_integral`: `E[X e^{-cX}] = m ∫ e^{-cay} dQ(y)`.
* `abs_integral_laplaceKernel_sub_le`: `λ ↦ ∫ f_λ dQ` is Lipschitz with constant `Q(ℝ)`.
* `tendsto_laplace_div_of_tendsto_integral_laplaceKernel`: the fixed-rate limit (I.3.7) along
  a cut-off family with `h_r a_r → λ`, from the convergence of `∫ f_λ dQ_r` at the fixed rate;
  `tendsto_laplace_div_of_tendsto_integral_laplaceKernel_law` is the source's form for laws on
  `ℝ` with `a_r = E X_r² / E X_r`.

This is an analytic step of the proof of Proposition I.3.2, not that proposition.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory Real
open scoped Topology ENNReal

namespace PercLib.Analysis

open PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The size-biased law -/

/-- The law of `X / a` under `(X / m) P` is carried by `[0, ∞)`. -/
theorem map_withDensity_ofReal_div_Iio_zero (P : Measure Ω) {X : Ω → ℝ} (hXm : Measurable X)
    (hX0 : 0 ≤ᵐ[P] X) (m : ℝ) {a : ℝ} (ha : 0 < a) :
    ((P.withDensity fun ω => ENNReal.ofReal (X ω / m)).map fun ω => X ω / a) (Iio 0) = 0 := by
  rw [Measure.map_apply (hXm.div_const a) measurableSet_Iio,
    withDensity_apply _ (measurableSet_Iio.preimage (hXm.div_const a))]
  have hnull : P ((fun ω => X ω / a) ⁻¹' Iio 0) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hX0)
    have h1 : X ω / a < 0 := hω
    rw [div_lt_iff₀ ha, zero_mul] at h1
    exact not_le.2 h1
  rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

/-- **The size-biased measure is a probability measure**: `(X / ∫ X ∂P) P` for integrable
`X ≥ 0` with `∫ X ∂P > 0`. -/
theorem isProbabilityMeasure_withDensity_ofReal_div_integral (P : Measure Ω) {X : Ω → ℝ}
    (hXi : Integrable X P) (hX0 : 0 ≤ᵐ[P] X) (hpos : 0 < ∫ ω, X ω ∂P) :
    IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hnn : 0 ≤ᵐ[P] fun ω => X ω / ∫ ω, X ω ∂P := by
    filter_upwards [hX0] with ω hω
    exact div_nonneg hω hpos.le
  rw [← ofReal_integral_eq_lintegral_ofReal (hXi.div_const _) hnn, integral_div,
    div_self hpos.ne', ENNReal.ofReal_one]

/-- The law of `X / a` under the size-biased measure is a probability measure. -/
theorem isProbabilityMeasure_map_withDensity_ofReal_div_integral (P : Measure Ω) {X : Ω → ℝ}
    (hXi : Integrable X P) (hX0 : 0 ≤ᵐ[P] X) (hpos : 0 < ∫ ω, X ω ∂P)
    (a : ℝ) :
    IsProbabilityMeasure
      ((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map fun ω => X ω / a) := by
  have := isProbabilityMeasure_withDensity_ofReal_div_integral P hXi hX0 hpos
  infer_instance

/-! ### The two size-biased identities -/

/-- **The Laplace transform as a size-biased kernel integral.** With `Q` the law of `X / a`
under `(X / m) P`, `m = ∫ X ∂P > 0`: `E[1 - e^{-hX}] = (m / a) ∫ f_{ha} dQ`. -/
theorem integral_one_sub_exp_eq_mul_integral_laplaceKernel (P : Measure Ω) {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : 0 ≤ᵐ[P] X) {a : ℝ} (ha : 0 < a) (hm : 0 < ∫ ω, X ω ∂P)
    (h : ℝ) :
    ∫ ω, (1 - exp (-(h * X ω))) ∂P =
      (∫ ω, X ω ∂P) / a * ∫ y, (if y = 0 then h * a else (1 - exp (-(h * a * y))) / y)
        ∂((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map fun ω => X ω / a) := by
  rw [integral_map (hXm.div_const a).aemeasurable
    (continuous_laplaceKernel (h * a)).aestronglyMeasurable,
        integral_withDensity_ofReal_div P hXm hX0]
  have hpt : ∀ ω, X ω * (if X ω / a = 0 then h * a else
      (1 - exp (-(h * a * (X ω / a)))) / (X ω / a)) = a * (1 - exp (-(h * X ω))) := by
    intro ω
    by_cases hX : X ω = 0
    · simp [hX]
    · have hXa : X ω / a ≠ 0 := div_ne_zero hX ha.ne'
      simp only [hXa, ↓reduceIte]
      rw [show h * a * (X ω / a) = h * X ω by field_simp]
      field_simp
  simp_rw [hpt]
  rw [integral_const_mul]
  field_simp

/-- **The exponential moment as a size-biased integral.** With `Q` the law of `X / a` under
`(X / m) P`, `m = ∫ X ∂P > 0`: `E[X e^{-cX}] = m ∫ e^{-cay} dQ(y)`. -/
theorem integral_mul_exp_neg_eq_mul_integral (P : Measure Ω) {X : Ω → ℝ} (hXm : Measurable X)
    (hX0 : 0 ≤ᵐ[P] X) {a : ℝ} (ha : a ≠ 0) (hm : 0 < ∫ ω, X ω ∂P) (c : ℝ) :
    ∫ ω, X ω * exp (-(c * X ω)) ∂P =
      (∫ ω, X ω ∂P) * ∫ y, exp (-(c * a * y))
        ∂((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map fun ω => X ω / a) := by
  rw [integral_map (hXm.div_const a).aemeasurable (by fun_prop),
    integral_withDensity_ofReal_div P hXm hX0, mul_div_cancel₀ _ hm.ne']
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [show c * a * (X ω / a) = c * X ω by field_simp]

/-! ### Bounds for the kernel integrals -/

/-- On a finite measure carried by `[0, ∞)`, `∫ f_s dQ ≤ s Q(ℝ)` for `s ≥ 0`. -/
theorem integral_laplaceKernel_le {Q : Measure ℝ} [IsFiniteMeasure Q] (hQ : Q (Iio 0) = 0)
    {s : ℝ} (hs : 0 ≤ s) :
    ∫ y, (if y = 0 then s else (1 - exp (-(s * y))) / y) ∂Q ≤ s * Q.real univ := by
  have hsup : ∀ᵐ y ∂Q, 0 ≤ y := ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) hQ)
  calc ∫ y, (if y = 0 then s else (1 - exp (-(s * y))) / y) ∂Q ≤ ∫ _y, s ∂Q := by
        refine integral_mono_ae ?_ (integrable_const s) ?_
        · refine Integrable.of_bound (continuous_laplaceKernel s).aestronglyMeasurable s ?_
          filter_upwards [hsup] with y hy
          have h := laplaceKernel_mem_Icc hs hy
          rw [Real.norm_eq_abs, abs_of_nonneg h.1]
          exact h.2
        · filter_upwards [hsup] with y hy
          exact (laplaceKernel_mem_Icc hs hy).2
    _ = s * Q.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

/-- **`λ ↦ ∫ f_λ dQ` is Lipschitz**, with constant `Q(ℝ)`, on a finite measure carried by
`[0, ∞)`. -/
theorem abs_integral_laplaceKernel_sub_le {Q : Measure ℝ} [IsFiniteMeasure Q]
    (hQ : Q (Iio 0) = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |(∫ y, (if y = 0 then s else (1 - exp (-(s * y))) / y) ∂Q) -
        ∫ y, (if y = 0 then t else (1 - exp (-(t * y))) / y) ∂Q| ≤ |s - t| * Q.real univ := by
  have hsup : ∀ᵐ y ∂Q, 0 ≤ y := ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) hQ)
  have hint : ∀ {u : ℝ}, 0 ≤ u →
      Integrable (fun y => if y = 0 then u else (1 - exp (-(u * y))) / y) Q := by
    intro u hu
    refine Integrable.of_bound (continuous_laplaceKernel u).aestronglyMeasurable u ?_
    filter_upwards [hsup] with y hy
    have h := laplaceKernel_mem_Icc hu hy
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  rw [← integral_sub (hint hs) (hint ht)]
  calc _ ≤ ∫ y, |(if y = 0 then s else (1 - exp (-(s * y))) / y) -
          (if y = 0 then t else (1 - exp (-(t * y))) / y)| ∂Q := abs_integral_le_integral_abs
    _ ≤ ∫ _y, |s - t| ∂Q := by
        refine integral_mono_ae ((hint hs).sub (hint ht)).abs (integrable_const _) ?_
        filter_upwards [hsup] with y hy
        exact abs_laplaceKernel_sub_le hs ht hy
    _ = |s - t| * Q.real univ := by rw [integral_const, smul_eq_mul, mul_comm]

/-! ### The fixed-rate limit along a cut-off family -/

/-- **The fixed-rate cut-off limit (I.3.7)** (first stage of the proof of Proposition I.3.2).
Let `X_r ≥ 0` a.e. under `P_r` with `m_r = E X_r > 0` and `m_r ~ A₁ r^α`, scales `a_r > 0`, and
let `Q_r` be the law of `X_r / a_r` under `(X_r / m_r) P_r`, a probability measure. If
`h_r > 0` eventually, `h_r a_r → λ > 0` and `∫ f_λ dQ_r → ∫ f_λ dQ`, then
`E[1 - e^{-h_r X_r}] / (r^α h_r) → A₁ ∫ f_λ dQ / λ`. -/
theorem tendsto_laplace_div_of_tendsto_integral_laplaceKernel (P : ℝ → Measure Ω)
    (X : ℝ → Ω → ℝ) (hXm : ∀ r, Measurable (X r)) (hX0 : ∀ r, 0 ≤ᵐ[P r] X r)
    (hm : ∀ r, 0 < ∫ ω, X r ω ∂P r) (a : ℝ → ℝ) (ha : ∀ r, 0 < a r)
    (hprob : ∀ r, IsProbabilityMeasure
      (((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / a r))
    (Q : Measure ℝ) {A₁ α lam : ℝ} (hlam : 0 < lam) (h : ℝ → ℝ) (hh : ∀ᶠ r in atTop, 0 < h r)
    (hE : Tendsto (fun r => (∫ ω, X r ω ∂P r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hrate : Tendsto (fun r => h r * a r) atTop (𝓝 lam))
    (hker : Tendsto (fun r => ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y)
        ∂(((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
          fun ω => X r ω / a r)) atTop
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Q))) :
    Tendsto (fun r => (∫ ω, (1 - exp (-(h r * X r ω))) ∂P r) / (r ^ α * h r)) atTop
      (𝓝 (A₁ * (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Q) / lam)) := by
  -- `A₁ ≠ 0`, since otherwise the ratio in `hE` vanishes identically
  have hA₁ : A₁ ≠ 0 := by
    rintro rfl
    simp at hE
  obtain ⟨K, hK⟩ : ∃ K : ℝ → ℝ → ℝ,
      K = fun s y => if y = 0 then s else (1 - exp (-(s * y))) / y := ⟨_, rfl⟩
  obtain ⟨Qr, hQr⟩ : ∃ Qr : ℝ → Measure ℝ, Qr = fun r =>
      ((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / a r := ⟨_, rfl⟩
  have hker' : Tendsto (fun r => ∫ y, K lam y ∂Qr r) atTop (𝓝 (∫ y, K lam y ∂Q)) := by
    subst hK hQr
    exact hker
  have heq : ∀ᶠ r in atTop, (∫ ω, (1 - exp (-(h r * X r ω))) ∂P r) / (r ^ α * h r) =
      (∫ ω, X r ω ∂P r) / (A₁ * r ^ α) * (A₁ / (h r * a r)) *
        ∫ y, K (h r * a r) y ∂Qr r := by
    filter_upwards [hh, eventually_gt_atTop 0] with r hr hrpos
    have hrp : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hrpos α).ne'
    have har : a r ≠ 0 := (ha r).ne'
    have halg : ∀ m I : ℝ, m / a r * I / (r ^ α * h r) =
        m / (A₁ * r ^ α) * (A₁ / (h r * a r)) * I := fun m I => by
      field_simp
    rw [integral_one_sub_exp_eq_mul_integral_laplaceKernel (P r) (hXm r) (hX0 r) (ha r) (hm r),
      halg]
    subst hK hQr
    rfl
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  have hstep2 : Tendsto (fun r => A₁ / (h r * a r)) atTop (𝓝 (A₁ / lam)) :=
    tendsto_const_nhds.div hrate hlam.ne'
  have hlip : ∀ r, 0 < h r →
      |(∫ y, K (h r * a r) y ∂Qr r) - ∫ y, K lam y ∂Qr r| ≤ |h r * a r - lam| := by
    intro r hr
    have := hprob r
    have h1 := abs_integral_laplaceKernel_sub_le
      (map_withDensity_ofReal_div_Iio_zero (P r) (hXm r) (hX0 r) (∫ ω, X r ω ∂P r) (ha r))
      (mul_pos hr (ha r)).le hlam.le
    rw [probReal_univ, mul_one] at h1
    subst hK hQr
    exact h1
  have hstep3 : Tendsto (fun r => ∫ y, K (h r * a r) y ∂Qr r) atTop
      (𝓝 (∫ y, K lam y ∂Q)) := by
    have hbd : ∀ᶠ r in atTop, |(∫ y, K (h r * a r) y ∂Qr r) - ∫ y, K lam y ∂Q| ≤
        |h r * a r - lam| + |(∫ y, K lam y ∂Qr r) - ∫ y, K lam y ∂Q| := by
      filter_upwards [hh] with r hr
      calc _ ≤ |(∫ y, K (h r * a r) y ∂Qr r) - ∫ y, K lam y ∂Qr r| +
            |(∫ y, K lam y ∂Qr r) - ∫ y, K lam y ∂Q| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add_left (hlip r hr) _
    have hzero : Tendsto (fun r => |h r * a r - lam| +
        |(∫ y, K lam y ∂Qr r) - ∫ y, K lam y ∂Q|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r => |h r * a r - lam|) atTop (𝓝 0) := by
        simpa using (hrate.sub_const lam).abs
      have h2 : Tendsto (fun r => |(∫ y, K lam y ∂Qr r) - ∫ y, K lam y ∂Q|) atTop (𝓝 0) := by
        simpa using (hker'.sub_const (∫ y, K lam y ∂Q)).abs
      simpa using h1.add h2
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using
      squeeze_zero' (Eventually.of_forall fun r => abs_nonneg _) hbd hzero
  have hlim := (hE.mul hstep2).mul hstep3
  rw [show 1 * (A₁ / lam) * (∫ y, K lam y ∂Q) = A₁ * (∫ y, K lam y ∂Q) / lam by ring]
    at hlim
  subst hK
  exact hlim

/-- **The fixed-rate cut-off limit (I.3.7), for laws on `ℝ`**: the source's form, with `μ_r`
the law of the cluster volume, `a_r = E X_r² / E X_r` the size-biased mean and `Q_r` the law of
`X_r / a_r` under the size-biased law. -/
theorem tendsto_laplace_div_of_tendsto_integral_laplaceKernel_law (μ : ℝ → Measure ℝ)
    (Q : Measure ℝ) (hμ : ∀ r, μ r (Iio 0) = 0) (hEpos : ∀ r, 0 < ∫ x, x ∂μ r)
    (hSpos : ∀ r, 0 < (∫ x, x ^ 2 ∂μ r) / ∫ x, x ∂μ r)
    (hprob : ∀ r, IsProbabilityMeasure
      (((μ r).withDensity fun x => ENNReal.ofReal (x / ∫ x, x ∂μ r)).map
        fun x => x / ((∫ x, x ^ 2 ∂μ r) / ∫ x, x ∂μ r)))
    {A₁ α lam : ℝ} (hlam : 0 < lam) (h : ℝ → ℝ) (hh : ∀ᶠ r in atTop, 0 < h r)
    (hE : Tendsto (fun r => (∫ x, x ∂μ r) / (A₁ * r ^ α)) atTop (𝓝 1))
    (hrate : Tendsto (fun r => h r * ((∫ x, x ^ 2 ∂μ r) / ∫ x, x ∂μ r)) atTop (𝓝 lam))
    (hker : Tendsto (fun r => ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y)
        ∂(((μ r).withDensity fun x => ENNReal.ofReal (x / ∫ x, x ∂μ r)).map
          fun x => x / ((∫ x, x ^ 2 ∂μ r) / ∫ x, x ∂μ r))) atTop
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Q))) :
    Tendsto (fun r => (∫ x, (1 - exp (-(h r * x))) ∂μ r) / (r ^ α * h r)) atTop
      (𝓝 (A₁ * (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂Q) / lam)) :=
  tendsto_laplace_div_of_tendsto_integral_laplaceKernel μ (fun _ x => x)
    (fun _ => measurable_id) (fun r => ae_iff.2 (measure_mono_null
      (fun y hy => by simpa using hy) (hμ r))) hEpos _ hSpos hprob Q hlam h hh hE hrate hker

end PercLib.Analysis
