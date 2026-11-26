/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The weak-convergence layer of the proof of Proposition I.3.2 of T. Hutchcroft, *Critical
long-range percolation I: High effective dimension*, arXiv:2508.18807v1: kernel and exponential
integrals of weakly convergent laws on `ℝ`, at fixed and moving rates.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/WeakKernels.lean` and
`PercLib/CriticalLRP/Analysis/WeakBoundedKernels.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the two source files are merged; the source kernels `kern`, `kernE`, `kernB` (value
`0` at `0`) are replaced by the continuous kernel `f_λ` of
`PercLib/Probability/SizeBiasLimits.lean` (value `λ` at `0`), so the no-atom hypotheses
`Q {0} = 0` of the kernel statements and the layer-cake route (`laplace`, `clipExp`,
`layerCake`) are removed; the definitions `expK`, `kernBCF`, `expKBCF` are written out; the
support hypothesis on the limit law is derived from the one on the approximating laws; the
source's `sizeBiasedLaw` and `sbMean` are written out as the size-biased law
`(P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ X ∂P)).map (X / a)` with an arbitrary scale
`a`; the moving-rate exponential limit is proved through a uniform Lipschitz bound and a general
transfer lemma for uniformly approximated test functions; the order isomorphism of the
scale-selection lemmas may have any preordered domain; declarations are renamed; `import
Mathlib`, `autoImplicit`, `maxHeartbeats`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.VolumeTail.SizeBiasMGF
public import PercLib.Probability.ChiSquareLimit

/-! # Weak convergence and the kernel integrals of Proposition I.3.2

Let `Q_i ⇒ Q₀` be weakly convergent probability laws on `ℝ` along any filter. Write
`f_λ(y) = (1 - e^{-λy}) / y`, `f_λ(0) = λ`, for the kernel of
`PercLib/Probability/SizeBiasLimits.lean`. Since `f_λ` is continuous, weak convergence applies
to it directly once the laws are carried by `[0, ∞)`; no hypothesis on atoms is needed.

## Main results

* `ProbabilityMeasure.tendsto_integral_of_tendsto_of_ae_abs_sub_le`: if `Q_i ⇒ Q₀` and test
  functions `F_i` are uniformly within `ε_i → 0` of a bounded continuous `G`, `Q_i`-a.e., then
  `∫ F_i dQ_i → ∫ G dQ₀`.
* `tendsto_integral_laplaceKernel_of_tendsto_rate`: for laws carried by `[0, ∞)` and rates
  `c_i → λ > 0`, `∫ f_{c_i} dQ_i → ∫ f_λ dQ₀`; `tendsto_integral_laplaceKernel_comp` is the
  same along a reindexing `r : κ → ι`.
* `tendsto_integral_exp_neg_mul_abs` and `tendsto_integral_exp_neg_mul_abs_of_tendsto_rate`:
  the exponential test `y ↦ e^{-c|y|}` at a fixed rate `c ≥ 0` and at moving rates
  `c_i → λ > 0`, with no support hypothesis.
* `integral_exp_neg_mul_abs_le` and `tendsto_integral_exp_neg_mul_abs_atTop`: for a finite
  measure, `∫ e^{-c|y|} dQ ≤ Q(-δ, δ) + e^{-cδ} Q(ℝ)`, and `∫ e^{-c|y|} dQ → 0` as `c → ∞`
  when `Q {0} = 0`.
* `map_withDensity_ofReal_div_singleton_zero`: the size-biased law has no atom at `0`.
* `tendsto_orderIso_symm_div_nhdsGT_zero`, `tendsto_mul_comp_orderIso_symm_div_nhdsGT_zero`,
  `tendsto_integral_laplaceKernel_comp_orderIso_symm_div` and
  `tendsto_integral_laplaceKernel_sizeBias_orderIso_symm_div`: the scale selection
  `r(λ, h) = e⁻¹(λ / (A h))` attached to an order isomorphism `e`, the moving rate
  `h a_{r(λ,h)} → λ`, and the kernel limit along it.

This is an analytic step of the proof of Proposition I.3.2, not that proposition.
-/

@[expose] public section

noncomputable section

open Filter Set MeasureTheory Real
open scoped Topology ENNReal BoundedContinuousFunction

namespace PercLib.Probability

open PercLib.Analysis

/-! ### Transfer for uniformly approximated test functions -/

/-- **Weak convergence with uniformly approximated test functions.** If `Q_i ⇒ Q₀` and the test
functions `F_i` satisfy `|F_i - G| ≤ ε_i` `Q_i`-a.e. for a bounded continuous `G`, with
`ε_i → 0`, then `∫ F_i dQ_i → ∫ G dQ₀`. -/
theorem ProbabilityMeasure.tendsto_integral_of_tendsto_of_ae_abs_sub_le {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] {ι : Type*}
    {l : Filter ι} {Q : ι → ProbabilityMeasure X} {Q₀ : ProbabilityMeasure X}
    (hconv : Tendsto Q l (𝓝 Q₀)) (G : X →ᵇ ℝ) {F : ι → X → ℝ}
    (hF : ∀ i, AEStronglyMeasurable (F i) (Q i : Measure X)) {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0))
    (hFG : ∀ᶠ i in l, ∀ᵐ x ∂(Q i : Measure X), |F i x - G x| ≤ ε i) :
    Tendsto (fun i => ∫ x, F i x ∂(Q i : Measure X)) l (𝓝 (∫ x, G x ∂(Q₀ : Measure X))) := by
  have hG := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv G
  have hbd : ∀ᶠ i in l,
      |(∫ x, F i x ∂(Q i : Measure X)) - ∫ x, G x ∂(Q i : Measure X)| ≤ ε i := by
    filter_upwards [hFG] with i hi
    have hi' : ∀ᵐ x ∂(Q i : Measure X), ‖F i x - G x‖ ≤ ε i := by
      filter_upwards [hi] with x hx
      rwa [Real.norm_eq_abs]
    have hint : Integrable (fun x => F i x - G x) (Q i : Measure X) :=
      Integrable.of_bound ((hF i).sub G.continuous.aestronglyMeasurable) (ε i) hi'
    have hFi : Integrable (F i) (Q i : Measure X) := by
      refine (hint.add (G.integrable (Q i : Measure X))).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, sub_add_cancel]
    rw [← integral_sub hFi (G.integrable _)]
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const hi'
  have hdiff : Tendsto (fun i => (∫ x, F i x ∂(Q i : Measure X)) -
      ∫ x, G x ∂(Q i : Measure X)) l (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun i => abs_nonneg _) hbd hε
  simpa using hdiff.add hG

/-! ### The kernel `f_λ` at a moving rate -/

/-- **Moving-rate kernel limit.** Let `Q_i ⇒ Q₀` be probability laws on `ℝ`, the `Q_i` carried
by `[0, ∞)`, and let `c_i → λ > 0`. Then `∫ f_{c_i} dQ_i → ∫ f_λ dQ₀`, where
`f_λ(y) = (1 - e^{-λy}) / y` and `f_λ(0) = λ`. -/
theorem tendsto_integral_laplaceKernel_of_tendsto_rate {ι : Type*} {l : Filter ι}
    {Q : ι → ProbabilityMeasure ℝ} {Q₀ : ProbabilityMeasure ℝ} (hconv : Tendsto Q l (𝓝 Q₀))
    (hQ : ∀ i, (Q i : Measure ℝ) (Iio 0) = 0) {c : ι → ℝ} {lam : ℝ}
    (hc : Tendsto c l (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun i => ∫ y, (if y = 0 then c i else (1 - exp (-(c i * y))) / y)
        ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ))) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hQ' : ∀ i, ∀ᵐ y ∂(Q i : Measure ℝ), 0 ≤ y := fun i =>
    ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) (hQ i))
  have hQ₀ := ae_nonneg_of_tendsto hQ' hconv
  obtain ⟨G, hG⟩ := exists_bcf_laplaceKernel hlam.le
  have htarget : ∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ) =
      ∫ y, G y ∂(Q₀ : Measure ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [hQ₀] with y hy
    rw [hG y, max_eq_left hy]
  rw [htarget]
  refine ProbabilityMeasure.tendsto_integral_of_tendsto_of_ae_abs_sub_le hconv G
    (F := fun i y => if y = 0 then c i else (1 - exp (-(c i * y))) / y)
    (fun i => (continuous_laplaceKernel (c i)).aestronglyMeasurable)
    (ε := fun i => |c i - lam|) (by simpa using (hc.sub_const lam).abs) ?_
  filter_upwards [hc.eventually (eventually_gt_nhds hlam)] with i hi
  filter_upwards [hQ' i] with y hy
  rw [hG y, max_eq_left hy]
  exact abs_laplaceKernel_sub_le hi.le hlam.le hy

/-- **Moving-rate kernel limit along a reindexing** `r : κ → ι` with `r → l`: the law index
`r a` and the rate `c a` both move with `a`. -/
theorem tendsto_integral_laplaceKernel_comp {ι κ : Type*} {l : Filter ι} {l' : Filter κ}
    {Q : ι → ProbabilityMeasure ℝ} {Q₀ : ProbabilityMeasure ℝ} (hconv : Tendsto Q l (𝓝 Q₀))
    (hQ : ∀ i, (Q i : Measure ℝ) (Iio 0) = 0) {r : κ → ι} (hr : Tendsto r l' l) {c : κ → ℝ}
    {lam : ℝ} (hc : Tendsto c l' (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun a => ∫ y, (if y = 0 then c a else (1 - exp (-(c a * y))) / y)
        ∂(Q (r a) : Measure ℝ)) l'
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ))) :=
  tendsto_integral_laplaceKernel_of_tendsto_rate (hconv.comp hr) (fun a => hQ (r a)) hc hlam

/-! ### The exponential test `y ↦ e^{-c|y|}` -/

/-- For `c ≥ 0`, `y ↦ e^{-c|y|}` is a bounded continuous function on `ℝ`. -/
theorem exists_bcf_exp_neg_mul_abs {c : ℝ} (hc : 0 ≤ c) :
    ∃ G : ℝ →ᵇ ℝ, ∀ y, G y = exp (-(c * |y|)) := by
  let g : C(ℝ, ℝ) := ⟨fun y => exp (-(c * |y|)), by fun_prop⟩
  refine ⟨BoundedContinuousFunction.mkOfBound g 1 fun x y => ?_, fun y => rfl⟩
  have hx : exp (-(c * |x|)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [abs_nonneg x])
  have hy : exp (-(c * |y|)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [abs_nonneg y])
  simp only [g, ContinuousMap.coe_mk, Real.dist_eq]
  rw [abs_le]
  constructor <;> linarith [exp_pos (-(c * |x|)), exp_pos (-(c * |y|))]

/-- **Fixed-rate exponential limit.** If `Q_i ⇒ Q₀` and `c ≥ 0`, then
`∫ e^{-c|y|} dQ_i → ∫ e^{-c|y|} dQ₀`. No support or atom hypothesis is needed. -/
theorem tendsto_integral_exp_neg_mul_abs {ι : Type*} {l : Filter ι}
    {Q : ι → ProbabilityMeasure ℝ} {Q₀ : ProbabilityMeasure ℝ} (hconv : Tendsto Q l (𝓝 Q₀))
    {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun i => ∫ y, exp (-(c * |y|)) ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, exp (-(c * |y|)) ∂(Q₀ : Measure ℝ))) := by
  obtain ⟨G, hG⟩ := exists_bcf_exp_neg_mul_abs hc
  simpa only [hG] using ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv G

/-- **Uniform Lipschitz bound in the rate.** For `0 < m ≤ a, b` and `t ≥ 0`,
`|e^{-at} - e^{-bt}| ≤ |a - b| e^{-1} / m`. -/
theorem abs_exp_neg_mul_sub_exp_neg_mul_le {a b m t : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b)
    (ht : 0 ≤ t) : |exp (-(a * t)) - exp (-(b * t))| ≤ |a - b| * (exp (-1) / m) := by
  have h1 : exp (-(a * t)) - exp (-(b * t)) =
      exp (-(m * t)) * (exp (-((a - m) * t)) - exp (-((b - m) * t))) := by
    rw [mul_sub, ← exp_add, ← exp_add]
    congr 1 <;> congr 1 <;> ring
  have h2 := abs_exp_neg_sub_exp_neg_le (mul_nonneg (sub_nonneg.2 ha) ht)
    (mul_nonneg (sub_nonneg.2 hb) ht)
  have h3 : |(a - m) * t - (b - m) * t| = |a - b| * t := by
    rw [← sub_mul, abs_mul, abs_of_nonneg ht, sub_sub_sub_cancel_right]
  rw [h3] at h2
  have h4 : m * t * exp (-(m * t)) ≤ exp (-1) := mul_exp_neg_le_exp_neg_one _
  rw [h1, abs_mul, abs_of_pos (exp_pos _)]
  calc exp (-(m * t)) * |exp (-((a - m) * t)) - exp (-((b - m) * t))|
      ≤ exp (-(m * t)) * (|a - b| * t) := mul_le_mul_of_nonneg_left h2 (exp_pos _).le
    _ = |a - b| * (t * exp (-(m * t))) := by ring
    _ ≤ |a - b| * (exp (-1) / m) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [le_div_iff₀ hm]
        nlinarith [h4]

/-- **Moving-rate exponential limit.** If `Q_i ⇒ Q₀` and `c_i → λ > 0`, then
`∫ e^{-c_i|y|} dQ_i → ∫ e^{-λ|y|} dQ₀`. No support, atom or moment hypothesis is needed. -/
theorem tendsto_integral_exp_neg_mul_abs_of_tendsto_rate {ι : Type*} {l : Filter ι}
    {Q : ι → ProbabilityMeasure ℝ} {Q₀ : ProbabilityMeasure ℝ} (hconv : Tendsto Q l (𝓝 Q₀))
    {c : ι → ℝ} {lam : ℝ} (hc : Tendsto c l (𝓝 lam)) (hlam : 0 < lam) :
    Tendsto (fun i => ∫ y, exp (-(c i * |y|)) ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ y, exp (-(lam * |y|)) ∂(Q₀ : Measure ℝ))) := by
  obtain ⟨G, hG⟩ := exists_bcf_exp_neg_mul_abs hlam.le
  have htarget : ∫ y, exp (-(lam * |y|)) ∂(Q₀ : Measure ℝ) = ∫ y, G y ∂(Q₀ : Measure ℝ) := by
    simp only [hG]
  rw [htarget]
  refine ProbabilityMeasure.tendsto_integral_of_tendsto_of_ae_abs_sub_le hconv G
    (F := fun i y => exp (-(c i * |y|)))
    (fun i => (by fun_prop : Continuous fun y : ℝ => exp (-(c i * |y|))).aestronglyMeasurable)
    (ε := fun i => |c i - lam| * (exp (-1) / (lam / 2)))
    (by simpa using (hc.sub_const lam).abs.mul_const (exp (-1) / (lam / 2))) ?_
  filter_upwards [hc.eventually (eventually_gt_nhds (half_lt_self hlam))] with i hi
  refine Eventually.of_forall fun y => ?_
  rw [hG y]
  exact abs_exp_neg_mul_sub_exp_neg_mul_le (half_pos hlam) hi.le (half_le_self hlam.le)
    (abs_nonneg y)

/-- **Explicit bound for the exponential test.** For a finite measure, `c ≥ 0` and `δ ≥ 0`,
`∫ e^{-c|y|} dQ ≤ Q(-δ, δ) + e^{-cδ} Q(ℝ)`. -/
theorem integral_exp_neg_mul_abs_le {Q : Measure ℝ} [IsFiniteMeasure Q] {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) :
    ∫ y, exp (-(c * |y|)) ∂Q ≤ Q.real (Ioo (-δ) δ) + exp (-(c * δ)) * Q.real univ := by
  have hpt : ∀ y, exp (-(c * |y|)) ≤ (Ioo (-δ) δ).indicator 1 y + exp (-(c * δ)) := by
    intro y
    by_cases hy : y ∈ Ioo (-δ) δ
    · rw [indicator_of_mem hy, Pi.one_apply]
      have : exp (-(c * |y|)) ≤ 1 := exp_le_one_iff.2 (by nlinarith [abs_nonneg y])
      linarith [exp_pos (-(c * δ))]
    · rw [indicator_of_notMem hy, zero_add, exp_le_exp]
      have : δ ≤ |y| := by
        rw [mem_Ioo, not_and_or, not_lt, not_lt] at hy
        rcases hy with h | h
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          exact h
      nlinarith
  have hint : Integrable (fun y => exp (-(c * |y|))) Q := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    nlinarith [abs_nonneg y]
  have hint1 : Integrable ((Ioo (-δ) δ).indicator (1 : ℝ → ℝ)) Q :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioo
  calc ∫ y, exp (-(c * |y|)) ∂Q ≤ ∫ y, ((Ioo (-δ) δ).indicator 1 y + exp (-(c * δ))) ∂Q :=
        integral_mono hint (hint1.add (integrable_const _)) hpt
    _ = Q.real (Ioo (-δ) δ) + exp (-(c * δ)) * Q.real univ := by
        rw [integral_add hint1 (integrable_const _), integral_indicator_one measurableSet_Ioo,
          integral_const, smul_eq_mul, mul_comm]

/-- **No-atom limit.** For a finite measure with `Q {0} = 0`, `∫ e^{-c|y|} dQ → 0` as
`c → ∞`. -/
theorem tendsto_integral_exp_neg_mul_abs_atTop {Q : Measure ℝ} [IsFiniteMeasure Q]
    (hQ : Q {0} = 0) :
    Tendsto (fun c : ℝ => ∫ y, exp (-(c * |y|)) ∂Q) atTop (𝓝 0) := by
  have hae : ∀ᵐ y ∂Q, y ≠ 0 := by
    rw [ae_iff]
    simpa using hQ
  have key : Tendsto (fun c : ℝ => ∫ y, exp (-(c * |y|)) ∂Q) atTop
      (𝓝 (∫ _y, (0 : ℝ) ∂Q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun c =>
        (by fun_prop : Continuous fun y : ℝ => exp (-(c * |y|))).aestronglyMeasurable)
      ?_ (integrable_const 1) ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
      refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      nlinarith [abs_nonneg y]
    · filter_upwards [hae] with y hy
      exact tendsto_exp_neg_atTop_nhds_zero.comp
        (Tendsto.atTop_mul_const (abs_pos.2 hy) tendsto_id)
  simpa using key

/-! ### The size-biased law has no atom at `0` -/

/-- **No atom at `0`.** The law of `X / a` under `(X / m) P` gives `{0}` measure `0`, for
`a ≠ 0` and any `m`: the size-biasing density vanishes where `X = 0`. -/
theorem map_withDensity_ofReal_div_singleton_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hXm : Measurable X) (m : ℝ) {a : ℝ} (ha : a ≠ 0) :
    ((P.withDensity fun ω => ENNReal.ofReal (X ω / m)).map fun ω => X ω / a) {0} = 0 := by
  have hs := (measurableSet_singleton (0 : ℝ)).preimage (hXm.div_const a)
  have hzero : ∀ ω ∈ (fun ω => X ω / a) ⁻¹' {0}, ENNReal.ofReal (X ω / m) = 0 := by
    intro ω hω
    have hX : X ω = 0 := by simpa [ha] using hω
    simp [hX]
  rw [Measure.map_apply (hXm.div_const a) (measurableSet_singleton 0), withDensity_apply _ hs,
    setLIntegral_congr_fun hs hzero, lintegral_zero]

/-! ### Scale selection by an order isomorphism -/

/-- For an order isomorphism `e : α ≃o ℝ` and `v > 0`, `e⁻¹(v / h) → ∞` as `h ↓ 0`. -/
theorem tendsto_orderIso_symm_div_nhdsGT_zero {α : Type*} [Preorder α] (e : α ≃o ℝ) {v : ℝ}
    (hv : 0 < v) : Tendsto (fun h : ℝ => e.symm (v / h)) (𝓝[>] 0) atTop := by
  have hmul : Tendsto (fun h : ℝ => v / h) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hv
  exact e.symm.tendsto_atTop.comp hmul

/-- **The moving rate at the selected scale.** If `S_r / (A e(r)) → 1` with `A > 0`, `λ > 0`
and `v = λ / A`, then `h S_{e⁻¹(v / h)} → λ` as `h ↓ 0`. -/
theorem tendsto_mul_comp_orderIso_symm_div_nhdsGT_zero {α : Type*} [Preorder α] {S : α → ℝ}
    {e : α ≃o ℝ} {A lam v : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hv : v = lam / A)
    (hS : Tendsto (fun r => S r / (A * e r)) atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => h * S (e.symm (v / h))) (𝓝[>] 0) (𝓝 lam) := by
  have hv0 : 0 < v := hv ▸ div_pos hlam hA
  have hratio : Tendsto (fun h : ℝ => S (e.symm (v / h)) / (A * (v / h))) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, OrderIso.apply_symm_apply] using
      hS.comp (tendsto_orderIso_symm_div_nhdsGT_zero e hv0)
  have hAv : A * v = lam := by
    rw [hv]
    field_simp
  have hlim := hratio.mul_const (A * v)
  rw [one_mul, hAv] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hA0 : A ≠ 0 := hA.ne'
  have hv0' : v ≠ 0 := hv0.ne'
  rw [← hAv]
  field_simp

/-- **Kernel limit along the selected scale.** If `Q_r ⇒ Q₀` as `r → ∞`, the `Q_r` are carried
by `[0, ∞)`, `e : α ≃o ℝ`, `v > 0` and `c_h → λ > 0` as `h ↓ 0`, then
`∫ f_{c_h} dQ_{e⁻¹(v / h)} → ∫ f_λ dQ₀`. -/
theorem tendsto_integral_laplaceKernel_comp_orderIso_symm_div {α : Type*} [Preorder α]
    {Q : α → ProbabilityMeasure ℝ} {Q₀ : ProbabilityMeasure ℝ}
    (hconv : Tendsto Q atTop (𝓝 Q₀)) (hQ : ∀ r, (Q r : Measure ℝ) (Iio 0) = 0) (e : α ≃o ℝ)
    {v : ℝ} (hv : 0 < v) {c : ℝ → ℝ} {lam : ℝ} (hc : Tendsto c (𝓝[>] 0) (𝓝 lam))
    (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => ∫ y, (if y = 0 then c h else (1 - exp (-(c h * y))) / y)
        ∂(Q (e.symm (v / h)) : Measure ℝ)) (𝓝[>] 0)
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ))) :=
  tendsto_integral_laplaceKernel_comp hconv hQ (tendsto_orderIso_symm_div_nhdsGT_zero e hv) hc
    hlam

/-- **Kernel limit of size-biased laws along the selected scale.** Let `X_r ≥ 0` a.e. under
`P_r`, scales `a_r > 0`, and let `Q_r` be the law of `X_r / a_r` under `(X_r / m_r) P_r`,
`m_r = ∫ X_r ∂P_r`. If `Q_r ⇒ Q₀`, `e : α ≃o ℝ`, `A > 0`, `λ > 0` and `a_r / (A e(r)) → 1`,
then with `r(λ, h) = e⁻¹(λ / (A h))`, `∫ f_{h a_{r(λ,h)}} dQ_{r(λ,h)} → ∫ f_λ dQ₀` as
`h ↓ 0`. -/
theorem tendsto_integral_laplaceKernel_sizeBias_orderIso_symm_div {α Ω : Type*} [Preorder α]
    [MeasurableSpace Ω] (P : α → Measure Ω) (X : α → Ω → ℝ) (hXm : ∀ r, Measurable (X r))
    (hX0 : ∀ r, 0 ≤ᵐ[P r] X r) (a : α → ℝ) (ha : ∀ r, 0 < a r) (Q : α → ProbabilityMeasure ℝ)
    (hQ : ∀ r, (Q r : Measure ℝ) =
      ((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / a r)
    (Q₀ : ProbabilityMeasure ℝ) (hconv : Tendsto Q atTop (𝓝 Q₀)) {e : α ≃o ℝ} {A lam : ℝ}
    (hA : 0 < A) (hlam : 0 < lam) (hS : Tendsto (fun r => a r / (A * e r)) atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => ∫ y, (if y = 0 then h * a (e.symm (lam / (A * h))) else
        (1 - exp (-(h * a (e.symm (lam / (A * h))) * y))) / y)
        ∂(Q (e.symm (lam / (A * h))) : Measure ℝ)) (𝓝[>] 0)
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q₀ : Measure ℝ))) := by
  simp_rw [div_mul_eq_div_div lam A]
  exact tendsto_integral_laplaceKernel_comp_orderIso_symm_div hconv
    (fun r => by
      rw [hQ r]
      exact map_withDensity_ofReal_div_Iio_zero (P r) (hXm r) (hX0 r) _ (ha r))
    e (div_pos hlam hA) (tendsto_mul_comp_orderIso_symm_div_nhdsGT_zero hA hlam rfl hS) hlam

/-! ### Checks -/

/-- The exponential test of a Gamma law, `∫ e^{-t|y|} dΓ(a, r) = (r / (r + t))^a` for
`t > -r`, is the Gamma Laplace transform of `PercLib/Probability/ChiSquareMoments.lean`. -/
example {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : -r < t) :
    ∫ y, exp (-(t * |y|)) ∂ProbabilityTheory.gammaMeasure a r = (r / (r + t)) ^ a := by
  rw [← integral_exp_neg_mul_gammaMeasure ha hr ht]
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_gammaMeasure a r] with y hy
  rw [abs_of_pos hy]

/-- The no-atom limit at the chi-square law `Γ(1/2, 1/2)`. -/
example : Tendsto (fun c : ℝ => ∫ y, exp (-(c * |y|))
    ∂ProbabilityTheory.gammaMeasure (1 / 2) (1 / 2)) atTop (𝓝 0) := by
  have := ProbabilityTheory.isProbabilityMeasure_gammaMeasure (a := 1 / 2) (r := 1 / 2)
    (by norm_num) (by norm_num)
  exact tendsto_integral_exp_neg_mul_abs_atTop
    (withDensity_absolutelyContinuous _ _ Real.volume_singleton)

/-- A constant family of laws and a moving rate `λ + 1/(n+1) → λ`. -/
example {Q : ProbabilityMeasure ℝ} (hQ : (Q : Measure ℝ) (Iio 0) = 0) {lam : ℝ}
    (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => ∫ y, (if y = 0 then lam + 1 / ((n : ℝ) + 1) else
        (1 - exp (-((lam + 1 / ((n : ℝ) + 1)) * y))) / y) ∂(Q : Measure ℝ)) atTop
      (𝓝 (∫ y, (if y = 0 then lam else (1 - exp (-(lam * y))) / y) ∂(Q : Measure ℝ))) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_integral_laplaceKernel_of_tendsto_rate tendsto_const_nhds (fun _ => hQ)
    (by simpa using (tendsto_const_nhds (x := lam)).add h) hlam

end PercLib.Probability
