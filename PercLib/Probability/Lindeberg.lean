/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-26, against pinned mathlib. No upstream proof is copied.
Mathematical reference: J. W. Lindeberg, *Eine neue Herleitung des Exponentialgesetzes in der
Wahrscheinlichkeitsrechnung*, Math. Z. 15 (1922); the characteristic-function proof as in
P. Billingsley, *Probability and Measure*, 3rd ed., Theorem 27.2.
-/
module

public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# The Lindeberg central limit theorem for triangular arrays

For each `n`, let `X n i` (`i` in a finite set `s n`) be independent, centred, square-integrable
real random variables whose variances sum to `1`, and suppose the Lindeberg condition: for every
`ε > 0`, `∑ i, E[(X n i)² ; |X n i| > ε] → 0`. Then `∑ i, X n i` converges in distribution to a
standard Gaussian.

The proof compares characteristic functions. The elementary bounds
`|e^{ix} - 1 - ix + x²/2| ≤ min(|x|³, 2x²)` and the telescoping bound
`|∏ zᵢ - ∏ wᵢ| ≤ ∑ |zᵢ - wᵢ|` for points of the closed unit disc reduce the claim to the
Lindeberg condition, which also forces the largest variance in a row to vanish.

## Main results

* `norm_prod_sub_prod_le_sum`: telescoping bound for products in the unit ball.
* `Complex.norm_exp_ofReal_mul_I_sub_le`: Taylor bounds for `e^{ix}` up to order two.
* `ProbabilityTheory.tendsto_charFun_sum_of_lindeberg`: convergence of characteristic functions.
* `ProbabilityTheory.tendstoInDistribution_sum_of_lindeberg`: the Lindeberg central limit
  theorem.
-/

public section

open MeasureTheory ProbabilityTheory Complex Filter Finset
open scoped Real Topology

/-- In a normed commutative ring, the difference of two finite products of elements of norm at
most one is bounded by the sum of the differences of the factors. -/
theorem norm_prod_sub_prod_le_sum {ι R : Type*} [NormedCommRing R] [NormOneClass R]
    (s : Finset ι) {z w : ι → R} (hz : ∀ i ∈ s, ‖z i‖ ≤ 1) (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) :
    ‖∏ i ∈ s, z i - ∏ i ∈ s, w i‖ ≤ ∑ i ∈ s, ‖z i - w i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    have hz' : ∀ i ∈ s, ‖z i‖ ≤ 1 := fun i hi => hz i (mem_insert_of_mem hi)
    have hw' : ∀ i ∈ s, ‖w i‖ ≤ 1 := fun i hi => hw i (mem_insert_of_mem hi)
    have hW : ‖∏ i ∈ s, w i‖ ≤ 1 :=
      (Finset.norm_prod_le _ _).trans (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) hw')
    have key : z a * ∏ i ∈ s, z i - w a * ∏ i ∈ s, w i =
        z a * (∏ i ∈ s, z i - ∏ i ∈ s, w i) + (z a - w a) * ∏ i ∈ s, w i := by ring
    rw [key]
    calc ‖z a * (∏ i ∈ s, z i - ∏ i ∈ s, w i) + (z a - w a) * ∏ i ∈ s, w i‖
        ≤ ‖z a‖ * ‖∏ i ∈ s, z i - ∏ i ∈ s, w i‖ + ‖z a - w a‖ * ‖∏ i ∈ s, w i‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * ∑ i ∈ s, ‖z i - w i‖ + ‖z a - w a‖ * 1 := by
          gcongr
          · exact hz a (mem_insert_self a s)
          · exact ih hz' hw'
      _ = ‖z a - w a‖ + ∑ i ∈ s, ‖z i - w i‖ := by ring

namespace Complex

/-- Mean value bound on the closed ball `[-|x|, |x|]` for a function `ℝ → ℂ` vanishing at `0`. -/
private theorem norm_le_of_hasDerivAt_of_norm_le {f f' : ℝ → ℂ} {x C : ℝ} (h0 : f 0 = 0)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hC : ∀ y, |y| ≤ |x| → ‖f' y‖ ≤ C) :
    ‖f x‖ ≤ C * |x| := by
  have := (convex_closedBall (0 : ℝ) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (C := C) (fun y _ => (hf y).hasDerivWithinAt)
    (fun y hy => hC y (by simpa [Real.norm_eq_abs] using hy))
    (Metric.mem_closedBall_self (abs_nonneg x))
    (show x ∈ Metric.closedBall (0 : ℝ) |x| by simp [Real.norm_eq_abs])
  simpa [h0, Real.norm_eq_abs] using this

private theorem hasDerivAt_exp_ofReal_mul_I (y : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (t * I)) (cexp (y * I) * I) y := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) y :=
    (hasDerivAt_id y).ofReal_comp.mul_const I
  simpa using h.cexp

theorem norm_exp_ofReal_mul_I_sub_one_le (x : ℝ) : ‖cexp (x * I) - 1‖ ≤ |x| := by
  have := norm_le_of_hasDerivAt_of_norm_le (f := fun t : ℝ => cexp (t * I) - 1) (x := x) (C := 1)
    (by simp) (fun y => (hasDerivAt_exp_ofReal_mul_I y).sub_const 1)
    (fun y _ => by simp [norm_exp_ofReal_mul_I])
  simpa using this

theorem norm_exp_ofReal_mul_I_sub_one_sub_le (x : ℝ) :
    ‖cexp (x * I) - 1 - x * I‖ ≤ x ^ 2 := by
  have := norm_le_of_hasDerivAt_of_norm_le (f := fun t : ℝ => cexp (t * I) - 1 - t * I) (x := x)
    (f' := fun y => (cexp (y * I) - 1) * I) (C := |x|) (by simp)
    (fun y => by
      have h : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) y :=
        (hasDerivAt_id y).ofReal_comp.mul_const I
      convert ((hasDerivAt_exp_ofReal_mul_I y).sub_const 1).sub h using 1
      ring)
    (fun y hy => by
      simpa using (norm_exp_ofReal_mul_I_sub_one_le y).trans hy)
  simpa [sq_abs, sq] using this

/-- Second-order Taylor bounds for `t ↦ e^{it}`: the remainder is at most `|x|³` and at most
`2 x²`. -/
theorem norm_exp_ofReal_mul_I_sub_le (x : ℝ) :
    ‖cexp (x * I) - (1 + x * I - x ^ 2 / 2)‖ ≤ min (|x| ^ 3) (2 * x ^ 2) := by
  refine le_min ?_ ?_
  · have := norm_le_of_hasDerivAt_of_norm_le
      (f := fun t : ℝ => cexp (t * I) - (1 + t * I - t ^ 2 / 2)) (x := x)
      (f' := fun y => (cexp (y * I) - 1 - y * I) * I) (C := x ^ 2) (by simp)
      (fun y => by
        have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) y :=
          (hasDerivAt_id y).ofReal_comp.mul_const I
        have h2 : HasDerivAt (fun t : ℝ => ((t : ℂ)) ^ 2 / 2) (2 * (y : ℂ) * 1 / 2) y := by
          have := ((hasDerivAt_id y).ofReal_comp).pow 2
          simpa using this.div_const 2
        convert (hasDerivAt_exp_ofReal_mul_I y).sub ((h1.const_add 1).sub h2) using 1
        ring_nf
        simp only [I_sq]
        ring)
      (fun y hy => by
        have := norm_exp_ofReal_mul_I_sub_one_sub_le y
        simp only [norm_mul, norm_I, mul_one]
        refine this.trans ?_
        rw [← sq_abs y, ← sq_abs x]
        exact pow_le_pow_left₀ (abs_nonneg y) hy 2)
    calc _ ≤ x ^ 2 * |x| := this
      _ = |x| ^ 3 := by rw [← sq_abs]; ring
  · calc ‖cexp (x * I) - (1 + x * I - x ^ 2 / 2)‖
        = ‖(cexp (x * I) - 1 - x * I) + ((x ^ 2 / 2 : ℝ) : ℂ)‖ := by
          congr 1; push_cast; ring
      _ ≤ x ^ 2 + x ^ 2 / 2 := by
          refine (norm_add_le _ _).trans (add_le_add (norm_exp_ofReal_mul_I_sub_one_sub_le x) ?_)
          rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg x]

end Complex

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Pointwise form of the Lindeberg estimate. -/
private theorem norm_exp_mul_I_sub_le_indicator (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    ‖cexp (↑(t * x) * I) - (1 + ↑(t * x) * I - (((t * x) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 * ε * x ^ 2 + 2 * t ^ 2 * {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) x := by
  have h := Complex.norm_exp_ofReal_mul_I_sub_le (t * x)
  have h' : ‖cexp (↑(t * x) * I) - (1 + ↑(t * x) * I - (((t * x) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      min (|t * x| ^ 3) (2 * (t * x) ^ 2) := by
    convert h using 3; push_cast; ring
  by_cases hx : ε < |x|
  · rw [Set.indicator_of_mem (by exact hx)]
    have : 0 ≤ |t| ^ 3 * ε * x ^ 2 := by positivity
    nlinarith [min_le_right (|t * x| ^ 3) (2 * (t * x) ^ 2)]
  · rw [Set.indicator_of_notMem (by exact hx)]
    push Not at hx
    have : |t * x| ^ 3 ≤ |t| ^ 3 * ε * x ^ 2 := by
      rw [abs_mul, mul_pow, ← sq_abs x]
      have : |x| ^ 3 ≤ ε * |x| ^ 2 := by
        rw [pow_succ']; exact mul_le_mul_of_nonneg_right hx (by positivity)
      nlinarith [pow_nonneg (abs_nonneg t) 3]
    simpa using (h'.trans (min_le_left _ _)).trans this

/-- A centred square-integrable variable has variance at most `ε²` plus its Lindeberg term. -/
theorem integral_sq_le_sq_add_setIntegral {X : Ω → ℝ} (hX : Measurable X) (h2 : MemLp X 2 P)
    (ε : ℝ) : P[X ^ 2] ≤ ε ^ 2 + ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P := by
  have hint : Integrable (fun ω => X ω ^ 2) P := h2.integrable_sq
  have hs : MeasurableSet {ω | ε < |X ω|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hX)
  have hc : ∫ _ : Ω, ε ^ 2 ∂P = ε ^ 2 := by simp
  rw [← integral_indicator hs, ← hc, ← integral_add (integrable_const _) (hint.indicator hs)]
  refine integral_mono hint ((integrable_const _).add (hint.indicator hs)) fun ω => ?_
  by_cases h : ε < |X ω|
  · simp [Set.indicator_of_mem (show ω ∈ {ω | ε < |X ω|} from h), sq_nonneg]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | ε < |X ω|} from h)]
    push Not at h
    simp only [Pi.pow_apply, add_zero]
    have := sq_le_sq' (by linarith [neg_abs_le (X ω), abs_nonneg (X ω)] : -ε ≤ X ω)
      ((le_abs_self _).trans h)
    exact this

/-- The second-order expansion of a characteristic function with Lindeberg remainder. -/
theorem norm_charFun_sub_le {X : Ω → ℝ} (hX : Measurable X) (h2 : MemLp X 2 P)
    (h0 : P[X] = 0) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖charFun (P.map X) t - (1 - ((t ^ 2 * P[X ^ 2] / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 * ε * P[X ^ 2] + 2 * t ^ 2 * ∫ ω in {ω | ε < |X ω|}, X ω ^ 2 ∂P := by
  have hint1 : Integrable X P := h2.integrable one_le_two
  have hint : Integrable (fun ω => X ω ^ 2) P := h2.integrable_sq
  have hs : MeasurableSet {ω | ε < |X ω|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hX)
  have hexp : Integrable (fun ω => cexp (↑(t * X ω) * I)) P := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (Eventually.of_forall fun ω => ?_)
    · exact (by fun_prop : Measurable fun ω => cexp (↑(t * X ω) * I)).aestronglyMeasurable
    · rw [norm_exp_ofReal_mul_I]
  have hlin : Integrable (fun ω => (↑(t * X ω) : ℂ) * I) P :=
    ((hint1.const_mul t).ofReal).mul_const I
  have hsq : Integrable (fun ω => (((t * X ω) ^ 2 / 2 : ℝ) : ℂ)) P := by
    refine Integrable.ofReal ((hint.const_mul (t ^ 2 / 2)).congr
      (Eventually.of_forall fun ω => ?_))
    change (t ^ 2 / 2) * X ω ^ 2 = (t * X ω) ^ 2 / 2
    ring
  have hrepr : charFun (P.map X) t - (1 - ((t ^ 2 * P[X ^ 2] / 2 : ℝ) : ℂ)) =
      ∫ ω, (cexp (↑(t * X ω) * I) - (1 + ↑(t * X ω) * I - (((t * X ω) ^ 2 / 2 : ℝ) : ℂ))) ∂P := by
    have h4 : Integrable (fun ω => 1 + (↑(t * X ω) : ℂ) * I) P := (integrable_const _).add hlin
    have h3 : Integrable (fun ω => 1 + (↑(t * X ω) : ℂ) * I - (((t * X ω) ^ 2 / 2 : ℝ) : ℂ)) P :=
      h4.sub hsq
    have e1 : ∫ ω, cexp (↑(t * X ω) * I) ∂P = charFun (P.map X) t := by
      rw [charFun_apply_real, integral_map hX.aemeasurable (by fun_prop)]
      push_cast; rfl
    have e2 : ∫ ω, (↑(t * X ω) : ℂ) * I ∂P = 0 := by
      rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, h0]; simp
    have e3 : ∫ ω, (((t * X ω) ^ 2 / 2 : ℝ) : ℂ) ∂P = ((t ^ 2 * P[X ^ 2] / 2 : ℝ) : ℂ) := by
      rw [integral_complex_ofReal]
      congr 1
      rw [show (fun ω => (t * X ω) ^ 2 / 2) = fun ω => (t ^ 2 / 2) * X ω ^ 2 from
        funext fun ω => by ring, integral_const_mul]
      simp only [Pi.pow_apply]; ring
    rw [integral_sub hexp h3, integral_sub h4 hsq, integral_add (integrable_const _) hlin, e1, e2,
      e3]
    simp
  rw [hrepr]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : Integrable (fun ω => |t| ^ 3 * ε * X ω ^ 2 +
      2 * t ^ 2 * {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω)) P := by
    refine (hint.const_mul _).add (Integrable.const_mul ?_ _)
    have : (fun ω => {y : ℝ | ε < |y|}.indicator (fun y => y ^ 2) (X ω)) =
        {ω | ε < |X ω|}.indicator (fun ω => X ω ^ 2) := by
      ext ω; simp [Set.indicator_apply]
    rw [this]; exact hint.indicator hs
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hbound
    (Eventually.of_forall fun ω => norm_exp_mul_I_sub_le_indicator t hε (X ω))).trans_eq ?_
  rw [integral_add (hint.const_mul (|t| ^ 3 * ε)) ?_, integral_const_mul, integral_const_mul,
    ← integral_indicator hs]
  · congr 2
  · exact hbound.sub (hint.const_mul (|t| ^ 3 * ε)) |>.congr
      (Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring)

/-- `|1 - u - e^{-u}| ≤ u² e^{|u|}`. -/
theorem norm_one_sub_sub_exp_neg_le (u : ℝ) :
    ‖(1 - (u : ℂ)) - cexp (-(u : ℂ))‖ ≤ u ^ 2 * Real.exp |u| := by
  calc ‖(1 - (u : ℂ)) - cexp (-(u : ℂ))‖
      = ‖cexp (-(u : ℂ)) - ∑ m ∈ range 2, (-(u : ℂ)) ^ m / m.factorial‖ := by
        rw [norm_sub_rev]; congr 2; simp [Finset.sum_range_succ]; ring
    _ ≤ ‖-(u : ℂ)‖ ^ 2 * Real.exp ‖-(u : ℂ)‖ := Complex.norm_exp_sub_sum_le_norm_mul_exp _ 2
    _ = u ^ 2 * Real.exp |u| := by simp [norm_neg, Complex.norm_real, sq_abs]

variable {ι : Type*}

/-- The characteristic-function estimate for one row of a Lindeberg array. -/
theorem norm_charFun_sum_sub_exp_le {s : Finset ι} {X : ι → Ω → ℝ}
    (hind : iIndepFun (s.restrict X) P) (hmeas : ∀ i ∈ s, Measurable (X i))
    (h2 : ∀ i ∈ s, MemLp (X i) 2 P) (h0 : ∀ i ∈ s, P[X i] = 0)
    (h1 : ∑ i ∈ s, P[X i ^ 2] = 1) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖charFun (P.map fun ω => ∑ i ∈ s, X i ω) t - cexp (-((t ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      |t| ^ 3 * ε + 2 * t ^ 2 * (∑ i ∈ s, ∫ ω in {ω | ε < |X i ω|}, X i ω ^ 2 ∂P) +
        (t ^ 2 / 2) ^ 2 * Real.exp (t ^ 2 / 2) *
          (ε ^ 2 + ∑ i ∈ s, ∫ ω in {ω | ε < |X i ω|}, X i ω ^ 2 ∂P) := by
  set L := ∑ i ∈ s, ∫ ω in {ω | ε < |X i ω|}, X i ω ^ 2 ∂P with hLdef
  set C := (t ^ 2 / 2) ^ 2 * Real.exp (t ^ 2 / 2) with hC
  have hσ0 : ∀ i, 0 ≤ P[X i ^ 2] := fun i =>
    integral_nonneg fun ω => by simp only [Pi.pow_apply]; positivity
  have hL0 : ∀ i, 0 ≤ ∫ ω in {ω | ε < |X i ω|}, X i ω ^ 2 ∂P := fun i =>
    integral_nonneg fun ω => sq_nonneg _
  have hσ1 : ∀ i ∈ s, P[X i ^ 2] ≤ 1 := fun i hi =>
    h1 ▸ single_le_sum (fun j _ => hσ0 j) hi
  have hLi : ∀ i ∈ s, ∫ ω in {ω | ε < |X i ω|}, X i ω ^ 2 ∂P ≤ L := fun i hi =>
    single_le_sum (fun j _ => hL0 j) hi
  have hprod : charFun (P.map fun ω => ∑ i ∈ s, X i ω) t =
      ∏ i ∈ s, charFun (P.map (X i)) t := by
    rw [iIndepFun.charFun_map_fun_finsetSum_eq_prod (fun i hi => (hmeas i hi).aemeasurable) hind,
      Finset.prod_apply]
  have h1c : ∑ i ∈ s, ((P[X i ^ 2] : ℝ) : ℂ) = 1 := by rw [← ofReal_sum, h1]; simp
  have hexp : cexp (-((t ^ 2 / 2 : ℝ) : ℂ)) =
      ∏ i ∈ s, cexp (-((t ^ 2 * P[X i ^ 2] / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib]
    push_cast
    rw [← Finset.sum_div, ← Finset.mul_sum, h1c, mul_one]
  rw [hprod, hexp]
  calc _ ≤ ∑ i ∈ s, ‖charFun (P.map (X i)) t - cexp (-((t ^ 2 * P[X i ^ 2] / 2 : ℝ) : ℂ))‖ :=
        norm_prod_sub_prod_le_sum s (fun i _ => norm_charFun_le_one _) fun i _ => by
          rw [← ofReal_neg, norm_exp_ofReal]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by have := hσ0 i; positivity))
    _ ≤ ∑ i ∈ s, (|t| ^ 3 * ε * P[X i ^ 2] +
          2 * t ^ 2 * ∫ ω in {ω | ε < |X i ω|}, X i ω ^ 2 ∂P + C * (ε ^ 2 + L) * P[X i ^ 2]) := by
        refine sum_le_sum fun i hi => ?_
        set σ := P[X i ^ 2] with hσ
        set u := t ^ 2 * σ / 2 with hu
        have hu0 : 0 ≤ u := by have := hσ0 i; positivity
        have hut : u ≤ t ^ 2 / 2 := by
          have := hσ1 i hi
          rw [hu]; nlinarith [sq_nonneg t]
        have hσL : σ ≤ ε ^ 2 + L :=
          (integral_sq_le_sq_add_setIntegral (hmeas i hi) (h2 i hi) ε).trans
            (by linarith [hLi i hi])
        have hA := norm_charFun_sub_le (hmeas i hi) (h2 i hi) (h0 i hi) t hε
        have hB : ‖((1 : ℂ) - ((u : ℝ) : ℂ)) - cexp (-((u : ℝ) : ℂ))‖ ≤ C * (ε ^ 2 + L) * σ := by
          refine (norm_one_sub_sub_exp_neg_le u).trans ?_
          rw [abs_of_nonneg hu0, hC]
          have hexpu : Real.exp u ≤ Real.exp (t ^ 2 / 2) := Real.exp_le_exp.mpr hut
          have hσ0' : 0 ≤ σ := hσ0 i
          have : u ^ 2 = (t ^ 2 / 2) ^ 2 * σ * σ := by rw [hu]; ring
          rw [this]
          calc (t ^ 2 / 2) ^ 2 * σ * σ * Real.exp u
              ≤ (t ^ 2 / 2) ^ 2 * σ * (ε ^ 2 + L) * Real.exp (t ^ 2 / 2) := by
                gcongr
            _ = _ := by ring
        calc _ ≤ ‖charFun (P.map (X i)) t - (1 - ((t ^ 2 * σ / 2 : ℝ) : ℂ))‖ +
              ‖(1 - ((u : ℝ) : ℂ)) - cexp (-((u : ℝ) : ℂ))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := add_le_add hA hB
    _ = |t| ^ 3 * ε + 2 * t ^ 2 * L + C * (ε ^ 2 + L) := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, h1]
        ring

/-- **Lindeberg's theorem**, characteristic-function form: for a triangular array of independent
centred square-integrable rows with unit total variance satisfying the Lindeberg condition, the
characteristic functions of the row sums converge to that of the standard Gaussian. -/
theorem tendsto_charFun_sum_of_lindeberg {s : ℕ → Finset ι} {X : ℕ → ι → Ω → ℝ}
    (hind : ∀ n, iIndepFun ((s n).restrict (X n)) P)
    (hmeas : ∀ n, ∀ i ∈ s n, Measurable (X n i)) (h2 : ∀ n, ∀ i ∈ s n, MemLp (X n i) 2 P)
    (h0 : ∀ n, ∀ i ∈ s n, P[X n i] = 0) (h1 : ∀ n, ∑ i ∈ s n, P[X n i ^ 2] = 1)
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i ∈ s n, ∫ ω in {ω | ε < |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => charFun (P.map fun ω => ∑ i ∈ s n, X n i ω) t) atTop
      (𝓝 (cexp (-((t ^ 2 / 2 : ℝ) : ℂ)))) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set C := (t ^ 2 / 2) ^ 2 * Real.exp (t ^ 2 / 2) with hC
  have hC0 : 0 ≤ C := by positivity
  set K := |t| ^ 3 + C + 1 with hK
  have hK0 : 0 < K := by positivity
  set ε := min 1 (δ / (2 * K)) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : ε * K ≤ δ / 2 := by
    have := min_le_right 1 (δ / (2 * K))
    calc ε * K ≤ δ / (2 * K) * K := by gcongr
      _ = δ / 2 := by field_simp
  have hsmall : |t| ^ 3 * ε + C * ε ^ 2 < δ / 2 := by
    have : C * ε ^ 2 ≤ C * ε := by
      apply mul_le_mul_of_nonneg_left _ hC0
      nlinarith
    nlinarith [abs_nonneg t, pow_nonneg (abs_nonneg t) 3]
  have hM : 0 < 2 * t ^ 2 + C + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hL ε hε0) (δ / 2 / (2 * t ^ 2 + C + 1))
    (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hLn := hN n hn
  set Ln := ∑ i ∈ s n, ∫ ω in {ω | ε < |X n i ω|}, X n i ω ^ 2 ∂P with hLndef
  have hLn0 : 0 ≤ Ln := sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hLn0] at hLn
  have hLn' : (2 * t ^ 2 + C) * Ln < δ / 2 := by
    rw [lt_div_iff₀ hM] at hLn
    nlinarith
  rw [dist_eq_norm]
  calc _ ≤ |t| ^ 3 * ε + 2 * t ^ 2 * Ln + C * (ε ^ 2 + Ln) :=
        norm_charFun_sum_sub_exp_le (hind n) (hmeas n) (h2 n) (h0 n) (h1 n) t hε0.le
    _ < δ := by nlinarith

/-- **Lindeberg's central limit theorem**: for a triangular array of independent centred
square-integrable rows with unit total variance satisfying the Lindeberg condition, the row sums
converge in distribution to a standard Gaussian. -/
theorem tendstoInDistribution_sum_of_lindeberg {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P')
    {s : ℕ → Finset ι} {X : ℕ → ι → Ω → ℝ}
    (hind : ∀ n, iIndepFun ((s n).restrict (X n)) P)
    (hmeas : ∀ n, ∀ i ∈ s n, Measurable (X n i)) (h2 : ∀ n, ∀ i ∈ s n, MemLp (X n i) 2 P)
    (h0 : ∀ n, ∀ i ∈ s n, P[X n i] = 0) (h1 : ∀ n, ∑ i ∈ s n, P[X n i ^ 2] = 1)
    (hL : ∀ ε > 0, Tendsto (fun n => ∑ i ∈ s n, ∫ ω in {ω | ε < |X n i ω|}, X n i ω ^ 2 ∂P)
      atTop (𝓝 0)) :
    TendstoInDistribution (fun n ω => ∑ i ∈ s n, X n i ω) atTop Y (fun _ => P) P' where
  forall_aemeasurable n := Finset.aemeasurable_fun_sum _ fun i hi => (hmeas n i hi).aemeasurable
  aemeasurable_limit := hY.aemeasurable
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    rw! [hY.map_eq]
    have := tendsto_charFun_sum_of_lindeberg hind hmeas h2 h0 h1 hL t
    simpa [charFun_gaussianReal, neg_div] using this

end ProbabilityTheory
