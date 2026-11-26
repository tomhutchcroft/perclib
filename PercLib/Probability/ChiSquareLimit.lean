/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Weak convergence from convergence of moments to a moment-determinate law on `[0,∞)`, and the
squared-normal (chi-square) limit of size-biased laws, for T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, Remark I.1.7 and the proof of (I.1.7), p. 32.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/MomentProblem/ChiSquareTail.lean` (the support, tightness, moment-passage
and identification part); licence Apache-2.0 as declared in that commit's file headers and
`third_party/critical-lrp/NOTICE.md`; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: sequences are indexed by an arbitrary countably generated filter in the main
statements; the uniform moment bounds of the source are derived from the convergence of the
moments instead of assumed; the identification step is proved for every law on `[0,∞)` whose
moment series converges somewhere, with the chi-square law as a corollary; the truncation
`powCut` (with its cut-off) is replaced by `(min (max x 0) R) ^ p`, used only inside proofs;
`chiSqPM` is replaced by a probability measure `μ` with `(μ : Measure ℝ) = gammaMeasure (1/2)
(1/2)`; `oddFact p` is `Nat.doubleFactorial (2 * p - 1)`; supports are stated almost
everywhere; `import Mathlib`, `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Probability.ChiSquareMoments
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Moment convergence and the chi-square limit of size-biased laws

## Main results

* `ae_nonneg_of_tendsto`: a weak limit of laws on `[0,∞)` is a law on `[0,∞)`.
* `isTightMeasureSet_range_of_lintegral_abs_le`: a uniform first-moment bound gives tightness.
* `integrable_pow_of_tendsto`, `tendsto_integral_pow_of_tendsto`: along a weakly convergent
  sequence of laws on `[0,∞)`, a uniform bound on the `p`-th moments makes the `p`-th moment of
  the limit finite, and a uniform bound on the `(p+1)`-st moments makes the `p`-th moments
  converge.
* `tendsto_of_tendsto_integral_pow`: if the moments of laws `Q i` on `[0,∞)` converge to those
  of a law `μ` on `[0,∞)` whose moment series converges on a disc of positive radius, then
  `Q i → μ` weakly.
* `tendsto_gammaMeasure_one_half_of_tendsto_integral_pow`: moments tending to `(2p-1)!!` give
  weak convergence to the chi-square law with one degree of freedom (the step "by Carleman's
  criterion" of the proof of (I.1.7)).
* `tendsto_integral_one_sub_exp_neg_mul_div_of_tendsto_integral_pow`: the tail integral
  `∫ (1 - e^{-λx}) / x dQ i` then tends to `√(1 + 2λ) - 1`.
* `tendsto_map_withDensity_gammaMeasure_one_half`: the squared-normal size-biased limit from
  cutoff moment asymptotics. If `X_r ≥ 0` has finite moments of all positive orders,
  `a_r = E X_r² / E X_r`, `Q_r` is the law of `X_r / a_r` under size bias by `X_r`, and
  `E X_r^{p+1} / (E X_r · a_r^p) → (2p-1)!!` for every `p ≥ 1`, then `Q_r` converges weakly to
  the chi-square law `gammaMeasure (1/2) (1/2)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

/-! ### Supports, tightness and passage of moments -/

/-- **A weak limit of laws on `[0,∞)` is carried by `[0,∞)`.** -/
theorem ae_nonneg_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {Q : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hQ0 : ∀ i, ∀ᵐ x ∂(Q i : Measure ℝ), 0 ≤ x) (hconv : Tendsto Q l (𝓝 ν)) :
    ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := by
  have h1 : ∀ i, (Q i : Measure ℝ) (Ici 0) = 1 := fun i =>
    (prob_compl_eq_zero_iff measurableSet_Ici).1 (mem_ae_iff.1 (hQ0 i))
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
      (isClosed_Ici (a := (0 : ℝ)))
  simp only [h1, limsup_const] at hle
  exact mem_ae_iff.2 ((prob_compl_eq_zero_iff measurableSet_Ici).2
    (le_antisymm prob_le_one hle))

/-- **Tightness from a uniform first-moment bound.** -/
theorem isTightMeasureSet_range_of_lintegral_abs_le {ι : Type*} {Q : ι → Measure ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i, ∫⁻ x, ENNReal.ofReal |x| ∂Q i ≤ ENNReal.ofReal C) :
    IsTightMeasureSet (range Q) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with htop | htop
  · exact ⟨∅, isCompact_empty, fun μ _ => by rw [htop]; exact le_top⟩
  have he0 : (0 : ℝ) < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  set R : ℝ := C / ε.toReal + 1 with hRdef
  have hR0 : 0 < R := by positivity
  refine ⟨Icc (-R) R, isCompact_Icc, ?_⟩
  rintro μ ⟨i, rfl⟩
  have hsub : (Icc (-R) R)ᶜ ⊆ {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    simp only [mem_ofPred_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases hx with h' | h'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  calc Q i (Icc (-R) R)ᶜ ≤ Q i {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} :=
        measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal |x| ∂Q i) / ENNReal.ofReal R :=
        meas_ge_le_lintegral_div (by fun_prop) (by simpa using hR0) (by simp)
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal R := by gcongr; exact h i
    _ = ENNReal.ofReal (C / R) := (ENNReal.ofReal_div_of_pos hR0).symm
    _ ≤ ENNReal.ofReal ε.toReal := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hR0, hRdef, mul_add, mul_div_cancel₀ _ he0.ne', mul_one]
        linarith
    _ = ε := ENNReal.ofReal_toReal htop

/-- **A uniform bound on the `p`-th moments passes to a weak limit** (portmanteau and Fatou),
so the limit has a finite `p`-th moment. -/
theorem integrable_pow_of_tendsto {Q : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {p : ℕ} {C : ℝ} (hQ0 : ∀ n, ∀ᵐ x ∂(Q n : Measure ℝ), 0 ≤ x) (hconv : Tendsto Q atTop (𝓝 ν))
    (hint : ∀ n, Integrable (fun x => x ^ p) (Q n : Measure ℝ))
    (hbound : ∀ n, ∫ x, x ^ p ∂(Q n : Measure ℝ) ≤ C) :
    Integrable (fun x => x ^ p) (ν : Measure ℝ) := by
  have hν0 := ae_nonneg_of_tendsto hQ0 hconv
  have hFatou := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure ℝ)) (μs := fun n => (Q n : Measure ℝ)) (f := fun x : ℝ => (max x 0) ^ p)
    (by fun_prop) (fun x => by positivity)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG)
  have hcongr : ∀ μ : Measure ℝ, (∀ᵐ x ∂μ, 0 ≤ x) →
      ∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ = ∫⁻ x, ENNReal.ofReal (x ^ p) ∂μ := by
    intro μ hμ
    refine lintegral_congr_ae ?_
    filter_upwards [hμ] with x hx
    rw [max_eq_left hx]
  have hn : ∀ n, ∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂(Q n : Measure ℝ) ≤ ENNReal.ofReal C := by
    intro n
    rw [hcongr _ (hQ0 n), ← ofReal_integral_eq_lintegral_ofReal (hint n)
      ((hQ0 n).mono fun x hx => pow_nonneg hx p)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfin : ∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂(ν : Measure ℝ) < ⊤ :=
    (hFatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hn))).trans_lt
      ENNReal.ofReal_lt_top
  refine ⟨(by fun_prop : Measurable fun x : ℝ => x ^ p).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hfin
  filter_upwards [hν0] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx p), max_eq_left hx]

/-- The bounded continuous truncation `x ↦ (min (max x 0) R)^p` of `x^p`. -/
theorem exists_bcf_eq_min_max_pow (p : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ G : BoundedContinuousFunction ℝ ℝ, ∀ x, G x = (min (max x 0) R) ^ p := by
  have hb : ∀ x : ℝ, 0 ≤ (min (max x 0) R) ^ p ∧ (min (max x 0) R) ^ p ≤ R ^ p := fun x =>
    ⟨pow_nonneg (le_min (le_max_right _ _) hR) p,
      pow_le_pow_left₀ (le_min (le_max_right _ _) hR) (min_le_right _ _) p⟩
  refine ⟨BoundedContinuousFunction.mkOfBound
    ⟨fun x => (min (max x 0) R) ^ p, by fun_prop⟩ (R ^ p) fun x y => ?_, fun x => rfl⟩
  simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith [hb x, hb y]

/-- **Passage of one moment under weak convergence.** Along a weakly convergent sequence of
laws on `[0,∞)` with uniformly bounded `(p+1)`-st moments, the `p`-th moments converge to that
of the limit. -/
theorem tendsto_integral_pow_of_tendsto {Q : ℕ → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} {p : ℕ} {C : ℝ} (hQ0 : ∀ n, ∀ᵐ x ∂(Q n : Measure ℝ), 0 ≤ x)
    (hconv : Tendsto Q atTop (𝓝 ν))
    (hintp : ∀ n, Integrable (fun x => x ^ p) (Q n : Measure ℝ))
    (hint1 : ∀ n, Integrable (fun x => x ^ (p + 1)) (Q n : Measure ℝ))
    (hbound : ∀ n, ∫ x, x ^ (p + 1) ∂(Q n : Measure ℝ) ≤ C)
    (hνint : Integrable (fun x => x ^ p) (ν : Measure ℝ)) :
    Tendsto (fun n => ∫ x, x ^ p ∂(Q n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ p ∂(ν : Measure ℝ))) := by
  have hν0 := ae_nonneg_of_tendsto hQ0 hconv
  -- the pointwise truncation estimates on `[0,∞)`
  have hle : ∀ {R x : ℝ}, 0 ≤ R → 0 ≤ x → (min (max x 0) R) ^ p ≤ x ^ p := fun hR hx =>
    pow_le_pow_left₀ (le_min (le_max_right _ _) hR) ((min_le_left _ _).trans
      (max_le le_rfl hx)) p
  have herr : ∀ {R x : ℝ}, 0 < R → 0 ≤ x → x ^ p - (min (max x 0) R) ^ p ≤ x ^ (p + 1) / R := by
    intro R x hR hx
    rcases le_or_gt x R with hxR | hxR
    · rw [max_eq_left hx, min_eq_left hxR, sub_self]
      positivity
    · have h3 : x ^ p ≤ x ^ (p + 1) / R := by
        rw [le_div_iff₀ hR, pow_succ]
        exact mul_le_mul_of_nonneg_left hxR.le (by positivity)
      linarith [pow_nonneg (le_min (le_max_right x 0) hR.le) p]
  -- the truncation error of the limit tends to zero
  have hνerr : Tendsto (fun R : ℝ => ∫ x, (x ^ p - (min (max x 0) R) ^ p) ∂(ν : Measure ℝ))
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := (ν : Measure ℝ))
      (l := atTop) (F := fun (R : ℝ) (x : ℝ) => x ^ p - (min (max x 0) R) ^ p)
      (f := fun _ => (0 : ℝ)) (fun x => x ^ p)
      (Eventually.of_forall fun R => (by fun_prop : Continuous fun x : ℝ =>
        x ^ p - (min (max x 0) R) ^ p).aestronglyMeasurable)
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
        filter_upwards [hν0] with x hx
        rw [Real.norm_of_nonneg (sub_nonneg.2 (hle hR hx))]
        linarith [pow_nonneg (le_min (le_max_right x 0) hR) p])
      hνint
      (by
        filter_upwards [hν0] with x hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop x] with R hR
        rw [max_eq_left hx, min_eq_left hR, sub_self])
    simpa using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose the truncation level
  have hCR : Tendsto (fun R : ℝ => C / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨R, hR0, hRC, hRν⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (((hCR.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3)))).and
      (hνerr.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))))).exists
  obtain ⟨G, hG⟩ := exists_bcf_eq_min_max_pow p hR0.le
  have hGint : ∀ μ : Measure ℝ, ∫ x, G x ∂μ = ∫ x, (min (max x 0) R) ^ p ∂μ := fun μ => by
    simp_rw [hG]
  have htrunc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) G
  simp_rw [hGint] at htrunc
  filter_upwards [Metric.tendsto_nhds.1 htrunc (ε / 3) (by linarith)] with n hn
  have hGi : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] →
      Integrable (fun x => (min (max x 0) R) ^ p) μ := fun μ _ => by
    rw [← funext hG]
    exact G.integrable μ
  have hsubν := integral_sub hνint (hGi (ν : Measure ℝ))
  have hsubQ := integral_sub (hintp n) (hGi (Q n : Measure ℝ))
  have hQerr : ∫ x, (x ^ p - (min (max x 0) R) ^ p) ∂(Q n : Measure ℝ) ≤ C / R := by
    calc ∫ x, (x ^ p - (min (max x 0) R) ^ p) ∂(Q n : Measure ℝ)
        ≤ ∫ x, x ^ (p + 1) / R ∂(Q n : Measure ℝ) :=
          integral_mono_ae ((hintp n).sub (hGi _)) ((hint1 n).div_const R)
            ((hQ0 n).mono fun x hx => herr hR0 hx)
      _ ≤ C / R := by
          rw [integral_div]
          exact div_le_div_of_nonneg_right (hbound n) hR0.le
  have hQnn : 0 ≤ ∫ x, (x ^ p - (min (max x 0) R) ^ p) ∂(Q n : Measure ℝ) :=
    integral_nonneg_of_ae ((hQ0 n).mono fun x hx => sub_nonneg.2 (hle hR0.le hx))
  have hνnn : 0 ≤ ∫ x, (x ^ p - (min (max x 0) R) ^ p) ∂(ν : Measure ℝ) :=
    integral_nonneg_of_ae (hν0.mono fun x hx => sub_nonneg.2 (hle hR0.le hx))
  rw [Real.dist_eq] at hn ⊢
  rw [hsubν] at hRν hνnn
  rw [hsubQ] at hQerr hQnn
  rw [abs_lt] at hn ⊢
  constructor <;> linarith [hn.1, hn.2]

/-! ### Identification of the limit -/

/-- **Moment convergence to a moment-determinate law gives weak convergence.** Let `Q i` be
probability laws on `[0,∞)` with moments of every order, indexed along a countably generated
filter, and let `μ` be a probability law on `[0,∞)` with moments of every order whose moment
series `∑ t^p / p! ∫ |x|^p dμ` converges for some `t > 0`. If every moment of `Q i` converges to
the corresponding moment of `μ`, then `Q i → μ` weakly. -/
theorem tendsto_of_tendsto_integral_pow {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {Q : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hQ0 : ∀ i, ∀ᵐ x ∂(Q i : Measure ℝ), 0 ≤ x)
    (hint : ∀ (p : ℕ) i, Integrable (fun x => x ^ p) (Q i : Measure ℝ))
    (hμ0 : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x)
    (hμint : ∀ p : ℕ, Integrable (fun x => |x| ^ p) (μ : Measure ℝ))
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable fun p : ℕ => t ^ p / p.factorial * ∫ x, |x| ^ p ∂(μ : Measure ℝ))
    (hmom : ∀ p : ℕ, Tendsto (fun i => ∫ x, x ^ p ∂(Q i : Measure ℝ)) l
      (𝓝 (∫ x, x ^ p ∂(μ : Measure ℝ)))) :
    Tendsto Q l (𝓝 μ) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- uniform moment bounds along the sequence
  have hbdd : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∫ x, x ^ p ∂(Q (ns n) : Measure ℝ) ≤ C := by
    intro p
    obtain ⟨C, hC⟩ := ((hmom p).comp hns).bddAbove_range
    exact ⟨max C 0, le_max_right _ _, fun n => (hC ⟨n, rfl⟩).trans (le_max_left _ _)⟩
  -- tightness
  obtain ⟨C₁, hC₁, h1⟩ := hbdd 1
  have htight : IsTightMeasureSet (range fun n => (Q (ns n) : Measure ℝ)) := by
    refine isTightMeasureSet_range_of_lintegral_abs_le hC₁ fun n => ?_
    have hnn := hQ0 (ns n)
    rw [lintegral_congr_ae (hnn.mono fun x hx => by rw [abs_of_nonneg hx]),
      ← ofReal_integral_eq_lintegral_ofReal (by simpa using hint 1 (ns n)) hnn]
    exact ENNReal.ofReal_le_ofReal (by simpa using h1 n)
  have hS : IsCompact (closure (range fun n => Q (ns n))) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 2
    ext ν
    simp [eq_comm]
  obtain ⟨ν, -, φ, hφ, hconv⟩ := hS.tendsto_subseq fun n => subset_closure ⟨n, rfl⟩
  have hconv' : Tendsto (fun k => Q (ns (φ k))) atTop (𝓝 ν) := hconv
  have hQ0' : ∀ k, ∀ᵐ x ∂(Q (ns (φ k)) : Measure ℝ), 0 ≤ x := fun k => hQ0 _
  have hν0 := ae_nonneg_of_tendsto hQ0' hconv'
  -- the limit has the moments of `μ`
  have hνint : ∀ p : ℕ, Integrable (fun x => x ^ p) (ν : Measure ℝ) := fun p => by
    obtain ⟨C, -, hC⟩ := hbdd p
    exact integrable_pow_of_tendsto hQ0' hconv' (fun k => hint p _) fun k => hC _
  have hνmom : ∀ p : ℕ, ∫ x, x ^ p ∂(ν : Measure ℝ) = ∫ x, x ^ p ∂(μ : Measure ℝ) := by
    intro p
    obtain ⟨C, -, hC⟩ := hbdd (p + 1)
    exact tendsto_nhds_unique (tendsto_integral_pow_of_tendsto hQ0' hconv' (fun k => hint p _)
      (fun k => hint (p + 1) _) (fun k => hC _) (hνint p))
      ((hmom p).comp (hns.comp hφ.tendsto_atTop))
  have hνabs : ∀ p : ℕ, Integrable (fun x => |x| ^ p) (ν : Measure ℝ) := fun p =>
    (hνint p).congr (hν0.mono fun x hx => by
      change x ^ p = |x| ^ p
      rw [abs_of_nonneg hx])
  have heq : (ν : Measure ℝ) = μ :=
    Measure.eq_of_forall_moment_eq_of_summable hν0 hμ0 hνabs hμint
      (fun p => (hνmom p).symm) ht hsum
  refine ⟨φ, ?_⟩
  rwa [show μ = ν from Subtype.ext heq.symm]

/-- **Moment asymptotics `(2p-1)!!` identify the chi-square limit.** If laws `Q i` on `[0,∞)`
with moments of every order have `p`-th moments tending to `(2p-1)!!` for every `p`, then they
converge weakly to the chi-square law with one degree of freedom. This is the step "by
Carleman's criterion" in the proof of (I.1.7). -/
theorem tendsto_gammaMeasure_one_half_of_tendsto_integral_pow {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {Q : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2))
    (hQ0 : ∀ i, ∀ᵐ x ∂(Q i : Measure ℝ), 0 ≤ x)
    (hint : ∀ (p : ℕ) i, Integrable (fun x => x ^ p) (Q i : Measure ℝ))
    (hmom : ∀ p : ℕ, Tendsto (fun i => ∫ x, x ^ p ∂(Q i : Measure ℝ)) l
      (𝓝 ((2 * p - 1).doubleFactorial : ℝ))) :
    Tendsto Q l (𝓝 μ) := by
  refine tendsto_of_tendsto_integral_pow hQ0 hint (hμ ▸ gammaMeasure_one_half_ae_nonneg)
    (hμ ▸ integrable_abs_pow_gammaMeasure_one_half) (t := 1 / 4) (by norm_num) ?_ ?_
  · simp_rw [hμ, integral_abs_pow_gammaMeasure_one_half]
    exact summable_gammaMeasure_moment_series (by norm_num) (by norm_num)
  · simpa only [hμ, integral_pow_gammaMeasure_one_half] using hmom

/-- **Moment asymptotics give the limit of the tail integral.** If laws `Q i` on `(0,∞)` with
moments of every order have `p`-th moments tending to `(2p-1)!!`, then
`∫ (1 - e^{-λx}) / x dQ i → √(1 + 2λ) - 1` for every `λ ≥ 0`. This is the chain
(I.1.6) ⇒ `Q_r → Q∞` ⇒ tail integral in the proof of (I.1.7), which feeds (I.3.7). -/
theorem tendsto_integral_one_sub_exp_neg_mul_div_of_tendsto_integral_pow {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {Q : ι → ProbabilityMeasure ℝ}
    (hQpos : ∀ i, ∀ᵐ x ∂(Q i : Measure ℝ), 0 < x)
    (hint : ∀ (p : ℕ) i, Integrable (fun x => x ^ p) (Q i : Measure ℝ))
    (hmom : ∀ p : ℕ, Tendsto (fun i => ∫ x, x ^ p ∂(Q i : Measure ℝ)) l
      (𝓝 ((2 * p - 1).doubleFactorial : ℝ)))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun i => ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(Q i : Measure ℝ)) l
      (𝓝 (Real.sqrt (1 + 2 * lam) - 1)) := by
  let μ : ProbabilityMeasure ℝ :=
    ⟨gammaMeasure (1 / 2) (1 / 2), isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)⟩
  have hμ : (μ : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2) := rfl
  have hconv := tendsto_gammaMeasure_one_half_of_tendsto_integral_pow hμ
    (fun i => (hQpos i).mono fun x hx => hx.le) hint hmom
  have h := tendsto_integral_one_sub_exp_neg_mul_div_of_tendsto hQpos
    (hμ ▸ ae_pos_gammaMeasure_one_half) hconv hlam
  rwa [hμ, integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half hlam] at h

/-! ### The squared-normal size-biased limit -/

/-- **Squared-normal size-biased limit from cutoff moment asymptotics.** Let `X_r ≥ 0` have
finite moments of every positive integer order, put `m_r = E X_r` and `a_r = E X_r² / m_r`, and
let `Q_r` be the law of `X_r / a_r` under size bias by `X_r`. If for every integer `p ≥ 1`
`E X_r^{p+1} / (m_r a_r^p) → (2p-1)!!`, then `Q_r` converges weakly to the chi-square law with
one degree of freedom (the law of the square of a standard normal variable). That `m_r > 0` is
implied by `Q_r` being a probability measure. -/
theorem tendsto_map_withDensity_gammaMeasure_one_half {ι Ω : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [MeasurableSpace Ω] (P : ι → Measure Ω) (X : ι → Ω → ℝ)
    (hXm : ∀ r, Measurable (X r)) (hX0 : ∀ r, ∀ᵐ ω ∂P r, 0 ≤ X r ω)
    (hint : ∀ r (p : ℕ), Integrable (fun ω => X r ω ^ (p + 1)) (P r))
    (Q : ι → ProbabilityMeasure ℝ)
    (hQ : ∀ r, (Q r : Measure ℝ) =
      ((P r).withDensity fun ω => ENNReal.ofReal (X r ω / ∫ ω, X r ω ∂P r)).map
        fun ω => X r ω / ((∫ ω, X r ω ^ 2 ∂P r) / ∫ ω, X r ω ∂P r))
    (hmom : ∀ p : ℕ, 1 ≤ p → Tendsto (fun r => (∫ ω, X r ω ^ (p + 1) ∂P r) /
      ((∫ ω, X r ω ∂P r) * ((∫ ω, X r ω ^ 2 ∂P r) / ∫ ω, X r ω ∂P r) ^ p)) l
        (𝓝 ((2 * p - 1).doubleFactorial : ℝ)))
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2)) :
    Tendsto Q l (𝓝 μ) := by
  have hm0 : ∀ r, 0 ≤ ∫ ω, X r ω ∂P r := fun r => integral_nonneg_of_ae (hX0 r)
  have ha0 : ∀ r, 0 ≤ (∫ ω, X r ω ^ 2 ∂P r) / ∫ ω, X r ω ∂P r := fun r => div_nonneg
    (integral_nonneg_of_ae ((hX0 r).mono fun ω hω => sq_nonneg _)) (hm0 r)
  -- `Q r` is carried by `[0,∞)`
  have hQ0 : ∀ r, ∀ᵐ x ∂(Q r : Measure ℝ), 0 ≤ x := by
    intro r
    rw [hQ r, ae_map_iff ((hXm r).div_const _).aemeasurable measurableSet_Ici]
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((hX0 r).mono fun ω hω => div_nonneg hω (ha0 r))
  -- `Q r` has moments of every order
  have hQint : ∀ (p : ℕ) r, Integrable (fun x => x ^ p) (Q r : Measure ℝ) := by
    intro p r
    rw [hQ r, integrable_map_measure (by fun_prop) ((hXm r).div_const _).aemeasurable,
      integrable_withDensity_iff_integrable_smul₀' ((hXm r).div_const _).ennreal_ofReal.aemeasurable
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine ((hint r p).div_const ((∫ ω, X r ω ∂P r) *
      ((∫ ω, X r ω ^ 2 ∂P r) / ∫ ω, X r ω ∂P r) ^ p)).congr ?_
    filter_upwards [hX0 r] with ω hω
    simp only [Function.comp_apply, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (div_nonneg hω (hm0 r)), div_pow (X r ω),
      div_mul_div_comm, ← pow_succ']
  refine tendsto_gammaMeasure_one_half_of_tendsto_integral_pow hμ hQ0 hQint fun p => ?_
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simpa using tendsto_const_nhds
  · refine (hmom p hp).congr fun r => ?_
    rw [hQ r, integral_pow_map_withDensity_ofReal_div (P r) (hXm r) (hX0 r)]

end PercLib.Probability

/-! ### Non-vacuity witness (D-5) -/

namespace PercLib.Probability

/-- The chi-square law itself: the constant family `Q i = μ` satisfies every hypothesis of
`tendsto_gammaMeasure_one_half_of_tendsto_integral_pow`. -/
example (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2)) :
    Tendsto (fun _ : ℕ => μ) atTop (𝓝 μ) :=
  tendsto_gammaMeasure_one_half_of_tendsto_integral_pow hμ
    (fun _ => hμ ▸ gammaMeasure_one_half_ae_nonneg)
    (fun p _ => hμ ▸ integrable_pow_gammaMeasure_one_half p)
    (fun p => by simp only [hμ, integral_pow_gammaMeasure_one_half]; exact tendsto_const_nhds)

end PercLib.Probability
