/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Exponential moments from double-factorial moment bounds, and explicit tails. New proofs
against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream proof is
copied. The binomial series of `(1 − z)^{∓1/2}` is mathlib's
`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`.
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.RingTheory.Binomial
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Exponential moments from double-factorial moment bounds

If `X ≥ 0` and `E X^m ≤ (2m-3)!! a M^{2m-2}` for all `m ≥ 1`, then `X` has explicit
exponential moments and explicit tail bounds, with the prefactor `a` and the scale `M` kept
apart. The one-parameter hypothesis `E X^m ≤ (2m-3)!! χ^{2m-1}` is the case `a = M = χ`.

## Main results

* `hasSum_inv_sqrt_one_sub`
* `lintegral_mul_exp_le_of_moment_le`: `E[X e^{rX}] ≤ a/√(1 - 2rM²)` for `0 ≤ r < (2M²)⁻¹`.
* `lintegral_exp_le_of_moment_le`: `E e^{rX} ≤ 1 + (a/M²)(1 - √(1 - 2rM²))` for
  `0 ≤ r ≤ (2M²)⁻¹`, endpoint included.
* `measure_le_le_min_of_moment_le`, `measure_le_le_exp_of_moment_le`: the explicit tails.
* `lintegral_mul_exp_le`, `lintegral_exp_le`, `measure_le_le_sqrt_two_mul`,
  `measure_le_le_min`, `measure_le_le_exp`: the one-parameter case `a = M = χ`.
-/

@[expose] public section

open Real Filter MeasureTheory Set
open scoped Nat ENNReal Topology

namespace PercLib.Probability

/-! ### Coefficients -/

theorem doubleFactorial_two_mul_add_one (n : ℕ) :
    Nat.doubleFactorial (2 * n + 1) = (2 * n + 1) * Nat.doubleFactorial (2 * n - 1) := by
  rcases n with _ | n
  · rfl
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.doubleFactorial_add_two,
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega]

theorem ascPochhammer_eval_half (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2) = (Nat.doubleFactorial (2 * n - 1) : ℝ) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      doubleFactorial_two_mul_add_one]
    push_cast
    field_simp
    ring

theorem ascPochhammer_eval_neg_half (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval (-1 / 2) = -(Nat.doubleFactorial (2 * n - 1) : ℝ) / 2 ^
        (n + 1) := by
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
    show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, ascPochhammer_eval_half]
  field_simp
  ring

theorem multichoose_eq_eval_div (r : ℝ) (n : ℕ) :
    Ring.multichoose r n = (ascPochhammer ℝ n).eval r / n ! := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  rw [← h]
  field_simp

/-- For `0 ≤ z < 1`: `∑ (2n−1)!!/(n! 2^n) z^n = (1 − z)^{−1/2}`. -/
theorem hasSum_inv_sqrt_one_sub {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => (Nat.doubleFactorial (2 * n - 1) : ℝ) / (n ! * 2 ^ n) * z ^ n)
        (1 / sqrt (1 - z)) := by
  have hb : z ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_of_nonneg hz0]
    exact hz1
  have h := (one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)).hasSum hb
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  rw [sqrt_eq_rpow]
  convert h using 2 with n
  rw [← Ring.multichoose_eq, multichoose_eq_eval_div, ascPochhammer_eval_half]
  field_simp

/-- For `0 ≤ z < 1`: `∑_{n ≥ 0} (2n−1)!!/((n+1)! 2^{n+1}) z^{n+1} = 1 − (1 − z)^{1/2}`. -/
theorem hasSum_one_sub_sqrt_one_sub {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun n : ℕ => (Nat.doubleFactorial (2 * n - 1) : ℝ) / ((n + 1) ! * 2 ^ (n + 1)) * z ^
        (n + 1))
      (1 - sqrt (1 - z)) := by
  have hb : z ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_one_iff,
      ← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_of_nonneg hz0]
    exact hz1
  have h := (one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (-1 / 2)).hasSum hb
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, Nat.cast_zero,
    add_zero] at h1
  have h2 := h1.neg
  convert h2 using 1
  · ext n
    rw [← Ring.multichoose_eq, multichoose_eq_eval_div, ascPochhammer_eval_neg_half]
    field_simp
  · have e : (1 - z) ^ (-1 / 2 : ℝ) = (sqrt (1 - z))⁻¹ := by
      rw [sqrt_eq_rpow, ← rpow_neg (by linarith)]; norm_num
    rw [e, one_div, inv_inv, Ring.choose_zero_right]
    ring

/-- For `0 ≤ z ≤ 1` (endpoint included), the partial sums of the series of `1 − √(1 − z)`
are at most `1 − √(1 − z)`. -/
theorem sum_range_le_one_sub_sqrt {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        (Nat.doubleFactorial (2 * n - 1) : ℝ) / ((n + 1) ! * 2 ^ (n + 1)) * z ^ (n + 1) ≤
      1 - sqrt (1 - z) := by
  have hle : ∀ y : ℝ, 0 ≤ y → y < 1 → ∑ n ∈ Finset.range N,
      (Nat.doubleFactorial (2 * n - 1) : ℝ) / ((n + 1) ! * 2 ^ (n + 1)) * y ^ (n + 1) ≤
        1 - sqrt (1 - y) := fun y hy0 hy1 =>
    sum_le_hasSum _ (fun n _ => by positivity) (hasSum_one_sub_sqrt_one_sub hy0 hy1)
  rcases hz1.lt_or_eq with hz1 | rfl
  · exact hle z hz0 hz1
  · rw [sub_self, sqrt_zero, sub_zero]
    have hc : Continuous fun y : ℝ => ∑ n ∈ Finset.range N,
        (Nat.doubleFactorial (2 * n - 1) : ℝ) / ((n + 1) ! * 2 ^ (n + 1)) * y ^ (n + 1) := by
      fun_prop
    refine le_of_tendsto ((hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))) ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with y hy
    exact (hle y hy.1.le hy.2).trans (sub_le_self _ (sqrt_nonneg _))

/-! ### Moment expansions -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- `E[X^j e^{rX}] = ∑_k r^k/k! E[X^{j+k}]` for `X ≥ 0` and `r ≥ 0`. -/
theorem lintegral_pow_mul_exp (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {r : ℝ} (hr : 0 ≤ r)
    (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ j * exp (r * X ω)) ∂P =
      ∑' k : ℕ, ENNReal.ofReal (r ^ k / k !) * ∫⁻ ω, ENNReal.ofReal (X ω ^ (j + k)) ∂P := by
  have hpt : ∀ ω, ENNReal.ofReal (X ω ^ j * exp (r * X ω)) =
      ∑' k : ℕ, ENNReal.ofReal (r ^ k / k !) * ENNReal.ofReal (X ω ^ (j + k)) := by
    intro ω
    have h := (NormedSpace.expSeries_div_hasSum_exp (r * X ω)).mul_left (X ω ^ j)
    rw [← Real.exp_eq_exp_ℝ] at h
    have hnn : ∀ k : ℕ, 0 ≤ X ω ^ j * ((r * X ω) ^ k / k !) := fun k => by
      have := hX0 ω; positivity
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn h.summable]
    congr 1 with k
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hpt]
  rw [lintegral_tsum fun k => ((hX.pow_const _).ennreal_ofReal.const_mul _).aemeasurable]
  congr 1 with k
  rw [lintegral_const_mul _ (hX.pow_const _).ennreal_ofReal]

variable {a M : ℝ}

/-- The two-parameter moment hypothesis, re-indexed: `E X^{k+1} ≤ (2k−1)!! a M^{2k}`. -/
theorem lintegral_pow_succ_le_of_moment_le
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2))) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * k - 1) * a * M ^ (2 * k)) := by
  have h := hmom (k + 1) (by omega)
  rwa [show 2 * (k + 1) - 3 = 2 * k - 1 by omega, show 2 * (k + 1) - 2 = 2 * k by omega] at h

/-- **Weighted exponential moment, two parameters.** If `X ≥ 0`, `a, M > 0` and
`E X^m ≤ (2m−3)!! a M^{2m−2}` for all `m ≥ 1`, then for `0 ≤ r < (2M²)⁻¹`:
`E[X e^{rX}] ≤ a / √(1 − 2rM²)`. The measure is arbitrary. -/
theorem lintegral_mul_exp_le_of_moment_le (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < (2 * M ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (X ω * exp (r * X ω)) ∂P ≤
      ENNReal.ofReal (a / sqrt (1 - 2 * r * M ^ 2)) := by
  have h2 : 0 < 2 * M ^ 2 := by positivity
  have hz1 : 2 * r * M ^ 2 < 1 := by
    calc 2 * r * M ^ 2 = r * (2 * M ^ 2) := by ring
      _ < (2 * M ^ 2)⁻¹ * (2 * M ^ 2) := mul_lt_mul_of_pos_right hr1 h2
      _ = 1 := inv_mul_cancel₀ h2.ne'
  have hz0 : 0 ≤ 2 * r * M ^ 2 := by positivity
  have hs := (hasSum_inv_sqrt_one_sub hz0 hz1).mul_left a
  have h1 := lintegral_pow_mul_exp (P := P) hX hX0 hr 1
  simp only [pow_one] at h1
  rw [h1]
  calc ∑' k : ℕ, ENNReal.ofReal (r ^ k / k !) * ∫⁻ ω, ENNReal.ofReal (X ω ^ (1 + k)) ∂P
      ≤ ∑' k : ℕ, ENNReal.ofReal (a * ((Nat.doubleFactorial (2 * k - 1) : ℝ) /
          (k ! * 2 ^ k) * (2 * r * M ^ 2) ^ k)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [add_comm 1 k]
        calc ENNReal.ofReal (r ^ k / k !) * ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P
            ≤ ENNReal.ofReal (r ^ k / k !) *
                ENNReal.ofReal (Nat.doubleFactorial (2 * k - 1) * a * M ^ (2 * k)) := by
              gcongr; exact lintegral_pow_succ_le_of_moment_le hmom k
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              field_simp
              ring
    _ = ENNReal.ofReal (a / sqrt (1 - 2 * r * M ^ 2)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable, hs.tsum_eq,
          mul_one_div]

/-- **Ordinary exponential moment, two parameters.** Under the hypotheses of
`lintegral_mul_exp_le_of_moment_le`, for a probability measure and `0 ≤ r ≤ (2M²)⁻¹`
(endpoint included): `E e^{rX} ≤ 1 + (a/M²)(1 − √(1 − 2rM²))`. -/
theorem lintegral_exp_le_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ (2 * M ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (exp (r * X ω)) ∂P ≤
      ENNReal.ofReal (1 + a / M ^ 2 * (1 - sqrt (1 - 2 * r * M ^ 2))) := by
  have h2 : 0 < 2 * M ^ 2 := by positivity
  have hz1 : 2 * r * M ^ 2 ≤ 1 := by
    calc 2 * r * M ^ 2 = r * (2 * M ^ 2) := by ring
      _ ≤ (2 * M ^ 2)⁻¹ * (2 * M ^ 2) := mul_le_mul_of_nonneg_right hr1 h2.le
      _ = 1 := inv_mul_cancel₀ h2.ne'
  have hz0 : 0 ≤ 2 * r * M ^ 2 := by positivity
  have hsq : 0 ≤ 1 - sqrt (1 - 2 * r * M ^ 2) := by
    rw [sub_nonneg, sqrt_le_one]; linarith
  have h1 := lintegral_pow_mul_exp (P := P) hX hX0 hr 0
  simp only [pow_zero, one_mul, zero_add] at h1
  rw [h1, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  rcases N with _ | N
  · simp
  rw [Finset.sum_range_succ', add_comm]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]
  gcongr
  calc ∑ k ∈ Finset.range N, ENNReal.ofReal (r ^ (k + 1) / (k + 1) !) *
        ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P
      ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal (a / M ^ 2 *
          ((Nat.doubleFactorial (2 * k - 1) : ℝ) / ((k + 1) ! * 2 ^ (k + 1)) *
            (2 * r * M ^ 2) ^ (k + 1))) := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc ENNReal.ofReal (r ^ (k + 1) / (k + 1) !) * ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P
            ≤ ENNReal.ofReal (r ^ (k + 1) / (k + 1) !) *
                ENNReal.ofReal (Nat.doubleFactorial (2 * k - 1) * a * M ^ (2 * k)) := by
              gcongr; exact lintegral_pow_succ_le_of_moment_le hmom k
          _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              field_simp
              ring
    _ ≤ ENNReal.ofReal (a / M ^ 2 * (1 - sqrt (1 - 2 * r * M ^ 2))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_range_le_one_sub_sqrt hz0 hz1 N) (by positivity)

variable {χ : ℝ}

/-- The one-parameter moment hypothesis `E X^m ≤ (2m−3)!! χ^{2m−1}` is the two-parameter one
with `a = M = χ`. -/
private theorem moment_le_mul_pow_of_moment_le_pow
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1))) :
    ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ * χ ^ (2 * m - 2)) := by
  intro m hm
  rw [mul_assoc, ← pow_succ', show 2 * m - 2 + 1 = 2 * m - 1 by omega]
  exact hmom m hm

/-- The moment hypothesis, re-indexed: `E X^{k+1} ≤ (2k−1)!! χ^{2k+1}`. -/
theorem lintegral_pow_succ_le
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1))) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (k + 1)) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * k - 1) * χ ^ (2 * k + 1)) := by
  have h := lintegral_pow_succ_le_of_moment_le (moment_le_mul_pow_of_moment_le_pow hmom) k
  rwa [mul_assoc, ← pow_succ'] at h

/-- **First bound.** If `X ≥ 0`, `χ > 0` and `E X^m ≤ (2m−3)!! χ^{2m−1}` for all
`m ≥ 1`, then for `0 ≤ r < (2χ²)⁻¹`: `E[X e^{rX}] ≤ χ / √(1 − 2rχ²)`. -/
theorem lintegral_mul_exp_le (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < (2 * χ ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (X ω * exp (r * X ω)) ∂P ≤
        ENNReal.ofReal (χ / sqrt (1 - 2 * r * χ ^ 2)) :=
  lintegral_mul_exp_le_of_moment_le hX hX0 hχ hχ (moment_le_mul_pow_of_moment_le_pow hmom) hr hr1

/-- **Second bound.** Under the same hypotheses, for a probability measure and
`0 ≤ r ≤ (2χ²)⁻¹` (endpoint included): `E e^{rX} ≤ 1 + (1 − √(1 − 2rχ²))/χ`. -/
theorem lintegral_exp_le [IsProbabilityMeasure P] (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ (2 * χ ^ 2)⁻¹) :
    ∫⁻ ω, ENNReal.ofReal (exp (r * X ω)) ∂P ≤
      ENNReal.ofReal (1 + (1 - sqrt (1 - 2 * r * χ ^ 2)) / χ) := by
  have h := lintegral_exp_le_of_moment_le hX hX0 hχ.le hχ
    (moment_le_mul_pow_of_moment_le_pow hmom) hr hr1
  rwa [show χ / χ ^ 2 = χ⁻¹ by rw [pow_two, div_mul_cancel_left₀ hχ.ne'], inv_mul_eq_div] at h

/-! ### Explicit tails (SNB3) -/

/-- Markov's inequality for a real nonnegative function dominating `ε > 0` on `s`. -/
theorem measure_le_ofReal_div {f : Ω → ℝ} (hf : Measurable f) {s : Set Ω} {ε B : ℝ}
    (hε : 0 < ε) (hs : ∀ ω ∈ s, ε ≤ f ω) (hB : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal B) :
    P s ≤ ENNReal.ofReal (B / ε) := by
  have hm := mul_meas_ge_le_lintegral₀ (μ := P) hf.ennreal_ofReal.aemeasurable (ENNReal.ofReal ε)
  have hsub : s ⊆ {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal (f ω)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (hs ω hω)
  have hεpos : ENNReal.ofReal ε ≠ 0 := by simpa using hε
  rw [ENNReal.ofReal_div_of_pos hε, ENNReal.le_div_iff_mul_le (Or.inl hεpos)
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact (mul_le_mul_right (measure_mono hsub) _ |>.trans hm).trans hB

/-- `P(X ≥ n) ≤ (√2 a / n) e^{−n/(4M²)}` for `n > 0`, under the two-parameter moment
hypothesis. -/
theorem measure_le_le_sqrt_two_mul_of_moment_le (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {n : ℝ} (hn : 0 < n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2)))) := by
  set r := (4 * M ^ 2)⁻¹ with hrdef
  have hr : 0 ≤ r := by positivity
  have hr1 : r < (2 * M ^ 2)⁻¹ := by
    rw [hrdef]; exact inv_strictAnti₀ (by positivity) (by nlinarith [sq_pos_of_pos hM])
  have hB := lintegral_mul_exp_le_of_moment_le hX hX0 ha hM hmom hr hr1
  have hz : 1 - 2 * r * M ^ 2 = 1 / 2 := by rw [hrdef]; field_simp; ring
  rw [hz] at hB
  refine (measure_le_ofReal_div (hX.mul (measurable_const.mul hX).exp)
    (mul_pos hn (exp_pos (r * n))) (fun ω hω => ?_) hB).trans_eq ?_
  · exact mul_le_mul hω (exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hr)) (exp_pos _).le
      (hX0 ω)
  · congr 1
    have hs2 : sqrt (1 / 2 : ℝ) = (sqrt 2)⁻¹ := by rw [one_div, sqrt_inv]
    have hs : 0 < sqrt (2 : ℝ) := by positivity
    rw [hs2, exp_neg, hrdef]
    field_simp

/-- `P(X ≥ n) ≤ (1 + a/M²) e^{−n/(2M²)}` for every real `n`, for a probability measure, under
the two-parameter moment hypothesis. -/
theorem measure_le_le_one_add_mul_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    (n : ℝ) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))) := by
  set r := (2 * M ^ 2)⁻¹ with hrdef
  have hr : 0 ≤ r := by positivity
  have hB := lintegral_exp_le_of_moment_le hX hX0 ha hM hmom hr le_rfl
  have hz : 1 - 2 * r * M ^ 2 = 0 := by rw [hrdef]; field_simp; ring
  rw [hz, sqrt_zero, sub_zero, mul_one] at hB
  refine (measure_le_ofReal_div (measurable_const.mul hX).exp (exp_pos (r * n))
    (fun ω hω => exp_le_exp.2 (mul_le_mul_of_nonneg_left hω hr)) hB).trans_eq ?_
  congr 1
  rw [div_eq_mul_inv, ← exp_neg, hrdef]
  congr 2
  field_simp

/-- **Tail bounds, two parameters.** For every real `n > 0`,
`P(X ≥ n) ≤ min{1, (√2 a/n) e^{−n/(4M²)}, (1 + a/M²) e^{−n/(2M²)}}`. -/
theorem measure_le_le_min_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 < a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {n : ℝ} (hn : 0 < n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (min 1 (min (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2))))
      ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))))) := by
  rcases min_choice 1 (min (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2))))
      ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2))))) with h | h <;> rw [h]
  · rw [ENNReal.ofReal_one]; exact prob_le_one
  · rcases min_choice (sqrt 2 * a / n * exp (-(n / (4 * M ^ 2))))
      ((1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))) with h' | h' <;> rw [h']
    · exact measure_le_le_sqrt_two_mul_of_moment_le hX hX0 ha hM hmom hn
    · exact measure_le_le_one_add_mul_of_moment_le hX hX0 ha.le hM hmom n

/-- **Pure exponential tail, two parameters.** `P(X ≥ n) ≤ e^{−n/(4M²)}` once
`n ≥ 4M² log(1 + a/M²)`. -/
theorem measure_le_le_exp_of_moment_le [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a) (hM : 0 < M)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * a * M ^ (2 * m - 2)))
    {n : ℝ} (hn : 4 * M ^ 2 * log (1 + a / M ^ 2) ≤ n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (exp (-(n / (4 * M ^ 2)))) := by
  refine (measure_le_le_one_add_mul_of_moment_le hX hX0 ha hM hmom n).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h4 : 0 < 4 * M ^ 2 := by positivity
  have hl : log (1 + a / M ^ 2) ≤ n / (4 * M ^ 2) := by rw [le_div_iff₀ h4]; linarith
  have h1 : 1 + a / M ^ 2 ≤ exp (n / (4 * M ^ 2)) := by
    rw [← exp_log (by positivity : 0 < 1 + a / M ^ 2)]; exact exp_le_exp.2 hl
  calc (1 + a / M ^ 2) * exp (-(n / (2 * M ^ 2)))
      ≤ exp (n / (4 * M ^ 2)) * exp (-(n / (2 * M ^ 2))) :=
        mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp (-(n / (4 * M ^ 2))) := by
        rw [← exp_add]; congr 1; field_simp; ring

/-- **Second bound.** `P(X ≥ n) ≤ (√2 χ / n) e^{−n/(4χ²)}` for `n > 0`. -/
theorem measure_le_le_sqrt_two_mul (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)))
    {n : ℝ} (hn : 0 < n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (sqrt 2 * χ / n * exp (-(n / (4 * χ ^ 2)))) :=
  measure_le_le_sqrt_two_mul_of_moment_le hX hX0 hχ hχ (moment_le_mul_pow_of_moment_le_pow hmom)
    hn

/-- **Third bound.** `P(X ≥ n) ≤ (1 + χ⁻¹) e^{−n/(2χ²)}` for a probability measure. -/
theorem measure_le_le_one_add_inv_mul [IsProbabilityMeasure P] (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)))
    (n : ℝ) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal ((1 + χ⁻¹) * exp (-(n / (2 * χ ^ 2)))) := by
  have h := measure_le_le_one_add_mul_of_moment_le hX hX0 hχ.le hχ
    (moment_le_mul_pow_of_moment_le_pow hmom) n
  rwa [show χ / χ ^ 2 = χ⁻¹ by rw [pow_two, div_mul_cancel_left₀ hχ.ne']] at h

/-- **Tail bounds.** For every real `n > 0`,
`P(X ≥ n) ≤ min{1, (√2 χ/n) e^{−n/(4χ²)}, (1 + χ⁻¹) e^{−n/(2χ²)}}`. -/
theorem measure_le_le_min [IsProbabilityMeasure P] (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)))
    {n : ℝ} (hn : 0 < n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (min 1 (min (sqrt 2 * χ / n * exp (-(n / (4 * χ ^ 2))))
      ((1 + χ⁻¹) * exp (-(n / (2 * χ ^ 2)))))) := by
  have h := measure_le_le_min_of_moment_le hX hX0 hχ hχ
    (moment_le_mul_pow_of_moment_le_pow hmom) hn
  rwa [show χ / χ ^ 2 = χ⁻¹ by rw [pow_two, div_mul_cancel_left₀ hχ.ne']] at h

/-- **Last bound.** `P(X ≥ n) ≤ e^{−n/(4χ²)}` once `n ≥ 4χ² log(1 + χ⁻¹)`. -/
theorem measure_le_le_exp [IsProbabilityMeasure P] (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hχ : 0 < χ)
    (hmom : ∀ m : ℕ, 1 ≤ m → ∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂P ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)))
    {n : ℝ} (hn : 4 * χ ^ 2 * log (1 + χ⁻¹) ≤ n) :
    P {ω | n ≤ X ω} ≤ ENNReal.ofReal (exp (-(n / (4 * χ ^ 2)))) :=
  measure_le_le_exp_of_moment_le hX hX0 hχ.le hχ (moment_le_mul_pow_of_moment_le_pow hmom)
    (by rwa [show χ / χ ^ 2 = χ⁻¹ by rw [pow_two, div_mul_cancel_left₀ hχ.ne']])

/-! ### Non-vacuity witnesses -/

/-- The point mass `X = χ` with `χ ≥ 1` satisfies the moment hypothesis for every `m ≥ 1`. -/
theorem dirac_moment_hyp {χ : ℝ} (hχ : 1 ≤ χ) (m : ℕ) (hm : 1 ≤ m) :
    ∫⁻ _ω, ENNReal.ofReal (χ ^ m) ∂(Measure.dirac ()) ≤
      ENNReal.ofReal (Nat.doubleFactorial (2 * m - 3) * χ ^ (2 * m - 1)) := by
  rw [lintegral_const, measure_univ, mul_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : χ ^ m ≤ χ ^ (2 * m - 1) := pow_le_pow_right₀ hχ (by omega)
  have h2 : (1 : ℝ) ≤ Nat.doubleFactorial (2 * m - 3) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  have h3 : 0 ≤ χ ^ (2 * m - 1) := by positivity
  nlinarith

/-- The point mass `X = χ` with `χ ≥ 1`: all the conclusions apply, at the endpoint
`r = (2χ²)⁻¹` and at `n = χ`. -/
example {χ : ℝ} (hχ : 1 ≤ χ) :
    ∫⁻ _ω, ENNReal.ofReal (exp ((2 * χ ^ 2)⁻¹ * χ)) ∂(Measure.dirac ()) ≤
        ENNReal.ofReal (1 + (1 - sqrt (1 - 2 * (2 * χ ^ 2)⁻¹ * χ ^ 2)) / χ) ∧
      (Measure.dirac ()) {_ω : Unit | χ ≤ χ} ≤
        ENNReal.ofReal (min 1 (min (sqrt 2 * χ / χ * exp (-(χ / (4 * χ ^ 2))))
          ((1 + χ⁻¹) * exp (-(χ / (2 * χ ^ 2)))))) :=
  have hχ0 : 0 < χ := zero_lt_one.trans_le hχ
  ⟨lintegral_exp_le (X := fun _ : Unit => χ) measurable_const (fun _ => hχ0.le) hχ0
      (dirac_moment_hyp hχ) (by positivity) le_rfl,
    measure_le_le_min (X := fun _ : Unit => χ) measurable_const (fun _ => hχ0.le) hχ0
      (dirac_moment_hyp hχ) hχ0⟩

end PercLib.Probability
