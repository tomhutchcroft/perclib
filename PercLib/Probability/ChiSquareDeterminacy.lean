/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from contributor yujinhkim, repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file `PercLib/CriticalLRP/MomentProblem/ChiSquare.lean`
(blob `cf6b336a11`). Licence: Apache-2.0 as declared in that revision's header and
`third_party/critical-lrp/NOTICE.md`. Upstream origin: `yujinhkim/Critical-Long-range-percolation`,
revision `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified). Changes: use
Nat.doubleFactorial and Real.Gamma_nat_add_half instead of the source's odd-factorial definition and
Gamma recurrence; use native moment determinacy, focused imports, enabled linters and an explicit
witness. The private helper `doubleFactorial_odd_succ` is replaced by PercLib's
`PercLib.Combinatorics.doubleFactorial_two_mul_succ_sub_one`.

Chi-square moments and determinacy, supporting Hutchcroft, Critical long-range
percolation I, arXiv:2508.18807v1, Remark I.1.7 and proof of (I.1.7), p. 32.
-/
module

public import PercLib.Combinatorics.DoubleFactorialConvolution
public import PercLib.Probability.MomentDeterminacy
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Chi-square moments and determinacy

The chi-square law with one degree of freedom has moments `(2n-1)!!`, its moment series converges
near zero, and it is determined by its moments.

## Main results

* `integral_pow_gammaMeasure_one_half`
* `summable_gammaMeasure_moment_series`
* `eq_gammaMeasure_of_forall_moment_eq`
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

lemma measurable_gammaPDF' (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

/-- **The moments of the chi-square law with one degree of freedom are `(2n-1)!!`.** -/
theorem integral_pow_gammaMeasure_one_half (n : ℕ) :
    ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2)) = ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hGamma : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos ha
  -- reduce to an integral against Lebesgue measure of the density times `x^n`
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' _ _)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => x ^ n)]
  have hpt : ∀ x : ℝ, (gammaPDF (1 / 2) (1 / 2) x).toReal • x ^ n
      = gammaPDFReal (1 / 2) (1 / 2) x * x ^ n := by
    intro x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha ha x), smul_eq_mul]
  simp_rw [hpt]
  -- the density vanishes off `(0,∞)`
  have hzero : ∀ x : ℝ, x ∉ Set.Ioi (0 : ℝ) → gammaPDFReal (1 / 2) (1 / 2) x * x ^ n = 0 := by
    intro x hx
    have hx' : x ≤ 0 := by simpa using hx
    rcases lt_or_eq_of_le hx' with h | h
    · rw [gammaPDFReal, ite_eq_right (by linarith : ¬ (0 : ℝ) ≤ x), zero_mul]
    · subst h
      rw [gammaPDFReal, ite_eq_left le_rfl]
      have hz : (0 : ℝ) ^ ((1 / 2 : ℝ) - 1) = 0 := Real.zero_rpow (by norm_num)
      rw [hz]
      ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (0:ℝ)) hzero]
  -- compute the integral over `(0,∞)`
  have hfun : ∀ x ∈ Set.Ioi (0 : ℝ),
      gammaPDFReal (1 / 2) (1 / 2) x * x ^ n
        = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2))
            * (x ^ ((n : ℝ) + 1 / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [gammaPDFReal, ite_eq_left hx0.le]
    have hpow : x ^ ((1 / 2 : ℝ) - 1) * x ^ n = x ^ ((n : ℝ) + 1 / 2 - 1) := by
      rw [← Real.rpow_natCast x n, ← Real.rpow_add hx0]
      congr 1
      ring
    calc (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2) * x ^ ((1 / 2 : ℝ) - 1)
          * Real.exp (-((1 / 2 : ℝ) * x)) * x ^ n
        = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2)
            * (x ^ ((1 / 2 : ℝ) - 1) * x ^ n) * Real.exp (-((1 / 2 : ℝ) * x)) := by ring
      _ = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2)
            * (x ^ ((n : ℝ) + 1 / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * x))) := by
          rw [hpow]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0:ℝ) < (n : ℝ) + 1 / 2) ha]
  -- simplify the constants
  have hA2 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt 2 = 1 := by
    have h1 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (1 / 2) := (Real.sqrt_eq_rpow _).symm
    rw [h1, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1 / 2)]
    have h2 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [h2, Real.sqrt_one]
  have hT : (2 : ℝ) ^ ((n : ℝ) + 1 / 2) = 2 ^ n * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_natCast,
      show ((1 / 2 : ℝ)) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  have hgn : Real.Gamma ((n : ℝ) + 1 / 2)
      = Real.Gamma (1 / 2) * (((Nat.doubleFactorial (2 * n - 1)) : ℝ) / 2 ^ n) := by
    rw [Real.Gamma_nat_add_half, Real.Gamma_one_half_eq]
    ring
  rw [show (1 / (1 / 2 : ℝ)) = 2 by norm_num, hT, hgn, Real.Gamma_one_half_eq]
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [show (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.sqrt Real.pi
      * ((2 : ℝ) ^ n * Real.sqrt 2 * (Real.sqrt Real.pi *
          (((Nat.doubleFactorial (2 * n - 1)) : ℝ) / 2 ^ n)))
      = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt 2) *
          (((Nat.doubleFactorial (2 * n - 1)) : ℝ) / 2 ^ n) * 2 ^ n
      by field_simp]
  rw [hA2, one_mul]
  exact div_mul_cancel₀ _ h2n.ne'

end PercLib.Probability

namespace PercLib.Probability

/-! ### The moment series of the chi-square law and its determinacy -/

lemma doubleFactorial_odd_le_two_pow_mul_factorial (n : ℕ) : (Nat.doubleFactorial (2 * n - 1)) ≤ 2 ^
    n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [PercLib.Combinatorics.doubleFactorial_two_mul_succ_sub_one, mul_comm (2 * n + 1), pow_succ,
      Nat.factorial_succ]
    calc (Nat.doubleFactorial (2 * n - 1)) * (2 * n + 1) ≤ (2 ^ n * n.factorial) * (2 * n + 1) :=
          Nat.mul_le_mul_right _ ih
      _ ≤ (2 ^ n * n.factorial) * (2 * (n + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          omega
      _ = 2 ^ n * 2 * ((n + 1) * n.factorial) := by ring

/-- The moment series of the chi-square law with one degree of freedom converges for `r < 1/2`:
`(2n-1)!! / n! = binom(2n,n) / 2^n ≤ 2^n`. -/
lemma summable_gammaMeasure_moment_series {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2) :
    Summable (fun n : ℕ => r ^ n / n.factorial * ((Nat.doubleFactorial (2 * n - 1)) : ℝ)) := by
  have hbound : ∀ n : ℕ, r ^ n / n.factorial * ((Nat.doubleFactorial (2 * n - 1)) : ℝ) ≤
      (2 * r) ^ n := by
    intro n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have h1 : ((Nat.doubleFactorial (2 * n - 1)) : ℝ) ≤ 2 ^ n * (n.factorial : ℝ) := by
      exact_mod_cast doubleFactorial_odd_le_two_pow_mul_factorial n
    have h2 : 0 ≤ r ^ n / (n.factorial : ℝ) := by positivity
    calc r ^ n / n.factorial * ((Nat.doubleFactorial (2 * n - 1)) : ℝ)
        ≤ r ^ n / n.factorial * (2 ^ n * (n.factorial : ℝ)) := mul_le_mul_of_nonneg_left h1 h2
      _ = (2 * r) ^ n := by
          rw [mul_pow]
          field_simp
  refine Summable.of_nonneg_of_le (fun n => by positivity) hbound ?_
  refine summable_geometric_of_lt_one (by positivity) ?_
  linarith

/-- The chi-square law with one degree of freedom is supported in `[0,∞)`. -/
lemma gammaMeasure_one_half_Iio_zero : gammaMeasure (1 / 2) (1 / 2) (Set.Iio 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  have hzero : ∀ x ∈ Set.Iio (0 : ℝ), gammaPDF (1 / 2) (1 / 2) x = 0 := by
    intro x hx
    exact gammaPDF_of_neg hx
  rw [setLIntegral_congr_fun measurableSet_Iio hzero, lintegral_zero]

lemma gammaMeasure_one_half_ae_nonneg : ∀ᵐ x ∂(gammaMeasure (1 / 2) (1 / 2)), 0 ≤ x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ (0 ≤ x)} = Set.Iio 0 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, not_le]
  rw [hset]
  exact gammaMeasure_one_half_Iio_zero

/-- All polynomial moments of the chi-square law are integrable. -/
lemma integrable_pow_gammaMeasure_one_half (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gammaMeasure (1 / 2) (1 / 2)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n) (gammaMeasure (1 / 2) (1 / 2)) := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hnn : ∀ᵐ x ∂(gammaMeasure (1 / 2) (1 / 2)), 0 ≤ x ^ n := by
    filter_upwards [gammaMeasure_one_half_ae_nonneg] with x hx
    exact pow_nonneg hx n
  have hlin : ∫⁻ x, ENNReal.ofReal ‖x ^ n‖ ∂(gammaMeasure (1 / 2) (1 / 2))
      = ∫⁻ x, ENNReal.ofReal (x ^ n) ∂(gammaMeasure (1 / 2) (1 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [hlin]
  have hreal : (∫⁻ x, ENNReal.ofReal (x ^ n) ∂(gammaMeasure (1 / 2) (1 / 2))).toReal
      = ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
    rw [← integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    exact integral_pow_gammaMeasure_one_half n
  have hpos : (0 : ℝ) < ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * n - 1)
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop, ENNReal.toReal_top] at hreal
  exact hpos.ne' hreal.symm

end PercLib.Probability

namespace PercLib.Probability

/-- Absolute moments of the chi-square law, in the form needed by the determinacy theorem. -/
lemma integral_abs_pow_gammaMeasure_one_half (n : ℕ) :
    ∫ x, |x| ^ n ∂(gammaMeasure (1 / 2) (1 / 2)) = ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
  rw [← integral_pow_gammaMeasure_one_half n]
  refine integral_congr_ae ?_
  filter_upwards [gammaMeasure_one_half_ae_nonneg] with x hx
  rw [abs_of_nonneg hx]

lemma integrable_abs_pow_gammaMeasure_one_half (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gammaMeasure (1 / 2) (1 / 2)) := by
  refine (integrable_pow_gammaMeasure_one_half n).congr ?_
  filter_upwards [gammaMeasure_one_half_ae_nonneg] with x hx
  rw [abs_of_nonneg hx]


/-- Moment equality with the chi-square law forces integrability of all moments. -/
lemma integrable_pow_of_forall_moment_eq_gammaMeasure {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν0 : ∀ᵐ x : ℝ ∂ν, 0 ≤ x)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2))) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) ν := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n) ν := by fun_prop
  have hnn : ∀ᵐ x ∂ν, 0 ≤ x ^ n := by
    filter_upwards [hν0] with x hx
    exact pow_nonneg hx n
  have habs : ∀ᵐ x ∂ν, |x| ^ n = x ^ n := by
    filter_upwards [hν0] with x hx
    rw [abs_of_nonneg hx]
  have hlin : ∫⁻ x, ENNReal.ofReal ‖|x| ^ n‖ ∂ν = ∫⁻ x, ENNReal.ofReal (x ^ n) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnn, habs] with x hx hx'
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx']
  refine ⟨hmeas.congr (by filter_upwards [habs] with x hx; exact hx.symm), ?_⟩
  rw [hasFiniteIntegral_iff_norm, hlin]
  have hreal : (∫⁻ x, ENNReal.ofReal (x ^ n) ∂ν).toReal =
      ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
    rw [← integral_eq_lintegral_of_nonneg_ae hnn hmeas, hmom n,
      integral_pow_gammaMeasure_one_half n]
  have hpos : (0 : ℝ) < ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos (2 * n - 1)
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop, ENNReal.toReal_top] at hreal
  exact hpos.ne' hreal.symm

/-- **Moment determinacy of the chi-square law with one degree of freedom.**

Any finite measure on `[0,∞)` whose `n`-th moment is `(2n-1)!!` for every `n` is the chi-square law
with one degree of freedom. This is the statement that the paper's proof of (I.1.7) obtains from
"Carleman's criterion"; here it is proved directly from the convergence of the moment series. -/
theorem eq_gammaMeasure_of_forall_moment_eq {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν0 : ∀ᵐ x : ℝ ∂ν, 0 ≤ x)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2))) :
    ν = gammaMeasure (1 / 2) (1 / 2) := by
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  -- the moment values
  have hval : ∀ n : ℕ, ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2)) =
      ((Nat.doubleFactorial (2 * n - 1)) : ℝ) :=
    integral_pow_gammaMeasure_one_half
  -- the moment series of `ν` converges at `r = 1/4`
  have hsum : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n / n.factorial * ∫ x, |x| ^ n ∂ν) := by
    have hcongr : (fun n : ℕ => (1 / 4 : ℝ) ^ n / n.factorial * ∫ x, |x| ^ n ∂ν)
        = fun n : ℕ => (1 / 4 : ℝ) ^ n / n.factorial * ((Nat.doubleFactorial (2 * n - 1)) : ℝ) := by
      funext n
      have habs : ∫ x, |x| ^ n ∂ν = ∫ x, x ^ n ∂ν := by
        refine integral_congr_ae (hν0.mono fun x hx => ?_)
        simp only [abs_of_nonneg hx]
      rw [habs, hmom n, hval n]
    rw [hcongr]
    exact summable_gammaMeasure_moment_series (by norm_num) (by norm_num)
  exact (Measure.eq_of_forall_moment_eq_of_summable (μ := gammaMeasure (1 / 2) (1 / 2))
    (ν := ν) gammaMeasure_one_half_ae_nonneg hν0 integrable_abs_pow_gammaMeasure_one_half
    (integrable_pow_of_forall_moment_eq_gammaMeasure hν0 hmom) hmom (by norm_num) hsum).symm

end PercLib.Probability

namespace PercLib.Probability

/-- Non-vacuity: the gamma law itself satisfies the determinacy hypotheses;
its zeroth, first and second moments are 1, 1 and 3. -/
example :
    (∫ x : ℝ, x ^ 0 ∂gammaMeasure (1 / 2) (1 / 2)) = 1 ∧
    (∫ x : ℝ, x ^ 1 ∂gammaMeasure (1 / 2) (1 / 2)) = 1 ∧
    (∫ x : ℝ, x ^ 2 ∂gammaMeasure (1 / 2) (1 / 2)) = 3 ∧
    gammaMeasure (1 / 2) (1 / 2) = gammaMeasure (1 / 2) (1 / 2) := by
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_, eq_gammaMeasure_of_forall_moment_eq
    gammaMeasure_one_half_ae_nonneg (fun _ => rfl)⟩
  · simpa using integral_pow_gammaMeasure_one_half 0
  · simpa using integral_pow_gammaMeasure_one_half 1
  · simpa using integral_pow_gammaMeasure_one_half 2

end PercLib.Probability
