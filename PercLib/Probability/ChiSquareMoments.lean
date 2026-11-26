/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Size-biased moments, the Laplace transform of the Gamma law and the chi-square tail
integral, for T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Remark I.1.7 and the proof of (I.1.7), p. 32.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/MomentProblem/SizeBiasing.lean` (all of it) and
`PercLib/CriticalLRP/MomentProblem/ChiSquareTail.lean` (the tail integral, the transfer along
weak convergence and the `√2` asymptotics); licence Apache-2.0 as declared in that commit's
file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: the source's unnormalised `sizeBias μ = μ.withDensity (ofReal ·)` and its normalised
form `(ofReal m₁)⁻¹ • sizeBias μ` become the size-biased law
`P.withDensity fun ω => ofReal (X ω / ∫ X ∂P)` used in `PercLib/Probability/SizeBiasLimits.lean`,
for a random variable `X` on an arbitrary measure space; `oddFact n` is
`Nat.doubleFactorial (2 * n - 1)`; `laplaceProfile lam x = ∫ t in 0..lam, exp (-(t * x))` is
written out and its bounded continuous version is `exists_bcf_laplaceKernel` of
`SizeBiasLimits.lean`; the Laplace transform is proved for every Gamma law; supports are
stated almost everywhere; `import Mathlib`, `autoImplicit`, disabled linters,
`maxHeartbeats` and `#print` lines are removed.
-/
module

public import PercLib.Probability.ChiSquareDeterminacy
public import PercLib.Probability.SizeBiasLimits
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Size-biased moments and the chi-square tail integral

Let `X ≥ 0` be a random variable with mean `m = E X > 0`. Its size-biased law is
`P.withDensity fun ω => ofReal (X ω / m)`, and `Q` denotes the law of `X / a` under it.

## Main results

* `integral_withDensity_ofReal_div`: `Ê F = E[X F] / E X` for every `F`.
* `integral_pow_map_withDensity_ofReal_div`: the `p`-th moment of `Q` is
  `E X^{p+1} / (m a^p)`; `integral_pow_map_withDensity_ofReal_div_of_one_le` is the form
  `m^{p-1} E X^{p+1} / (E X²)^p` for `a = E X² / m` used in the proof of (I.1.7).
* `withDensity_ofReal_div_integral_eq`: this size-biased law agrees with the `ℝ≥0∞`-valued
  form of `PercLib/Probability/SizeBias.lean`.
* `mul_pow_mul_pow_div_pow_eq`: the moment formula of Theorem I.1.6 gives the normalised
  moments exactly, with no limit.
* `integral_exp_neg_mul_gammaMeasure`: the Laplace transform `(r / (r + t))^a` of the Gamma law,
  and `integral_exp_neg_mul_gammaMeasure_one_half`: `E e^{-tX} = (1 + 2t)^{-1/2}` for the
  chi-square law with one degree of freedom.
* `integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half`: the chi-square tail integral
  `∫ (1 - e^{-λx}) / x dQ∞(x) = √(1 + 2λ) - 1`, and
  `integral_one_sub_exp_neg_mul_mul_exp_neg_half_rpow`, the same identity in the paper's
  displayed density form.
* `tendsto_integral_one_sub_exp_neg_mul_div_of_tendsto`: the tail integral passes to weak
  limits of laws on `(0,∞)`.
* `tendsto_integral_one_sub_exp_neg_mul_div_gammaMeasure_div_sqrt`: the constant `√2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

/-! ### Moments of size-biased laws -/

section SizeBias

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Expectations under the size-biased law.** `Ê F = E[X F] / E X` for every `F`. -/
theorem integral_withDensity_ofReal_div (P : Measure Ω) {X : Ω → ℝ} (hXm : Measurable X)
    (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) (F : Ω → ℝ) :
    ∫ ω, F ω ∂(P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)) =
      (∫ ω, X ω * F ω ∂P) / ∫ ω, X ω ∂P := by
  rw [integral_withDensity_eq_integral_toReal_smul (hXm.div_const _).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  refine integral_congr_ae ?_
  filter_upwards [hX0] with ω hω
  rw [ENNReal.toReal_ofReal (div_nonneg hω (integral_nonneg_of_ae hX0)), smul_eq_mul]
  ring

/-- **Moments of the size-biased law of `X / a`.** The `p`-th moment is
`E X^{p+1} / (E X · a^p)`. -/
theorem integral_pow_map_withDensity_ofReal_div (P : Measure Ω) {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) (a : ℝ) (p : ℕ) :
    ∫ y, y ^ p ∂((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map
        fun ω => X ω / a) =
      (∫ ω, X ω ^ (p + 1) ∂P) / ((∫ ω, X ω ∂P) * a ^ p) := by
  rw [integral_map (hXm.div_const a).aemeasurable (by fun_prop),
    integral_withDensity_ofReal_div P hXm hX0]
  simp_rw [div_pow, ← mul_div_assoc, ← pow_succ']
  rw [integral_div, div_div, mul_comm (a ^ p)]

/-- **The normalised size-biased moments of the proof of (I.1.7).** With `m₁ = E X > 0`,
`m₂ = E X²` and `a = m₂ / m₁`, the `p`-th moment of the size-biased law of `X / a` is
`m₁^{p-1} E X^{p+1} / m₂^p` for `p ≥ 1`. -/
theorem integral_pow_map_withDensity_ofReal_div_of_one_le (P : Measure Ω) {X : Ω → ℝ}
    (hXm : Measurable X) (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) (hm₁ : 0 < ∫ ω, X ω ∂P) {p : ℕ}
    (hp : 1 ≤ p) :
    ∫ y, y ^ p ∂((P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)).map
        fun ω => X ω / ((∫ ω, X ω ^ 2 ∂P) / ∫ ω, X ω ∂P)) =
      (∫ ω, X ω ∂P) ^ (p - 1) * (∫ ω, X ω ^ (p + 1) ∂P) / (∫ ω, X ω ^ 2 ∂P) ^ p := by
  rw [integral_pow_map_withDensity_ofReal_div P hXm hX0]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hp
  simp only [Nat.add_sub_cancel]
  rw [div_pow, pow_succ (∫ ω, X ω ∂P) k]
  rcases eq_or_ne (∫ ω, X ω ^ 2 ∂P) 0 with h2 | h2
  · simp [h2]
  · field_simp

/-- The size-biased law in the real form used here is the `ℝ≥0∞`-valued size-biased law of
`PercLib/Probability/SizeBias.lean` (`isProbabilityMeasure_withDensity_div`). -/
theorem withDensity_ofReal_div_integral_eq (P : Measure Ω) {X : Ω → ℝ} (hX : Integrable X P)
    (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) :
    (P.withDensity fun ω => ENNReal.ofReal (X ω / ∫ ω, X ω ∂P)) =
      P.withDensity fun ω => ENNReal.ofReal (X ω) / ∫⁻ ω, ENNReal.ofReal (X ω) ∂P := by
  rw [← ofReal_integral_eq_lintegral_ofReal hX hX0]
  rcases (integral_nonneg_of_ae hX0).eq_or_lt with h0 | hpos
  · have hX0' : X =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hX0 hX).1 h0.symm
    refine withDensity_congr_ae ?_
    filter_upwards [hX0'] with ω hω
    simp [hω]
  · congr 1
    funext ω
    exact ENNReal.ofReal_div_of_pos hpos

/-- **The moment formula of Theorem I.1.6 gives the normalised moments exactly.** If the
moments have the shape `m_p = c_p A^{p-1} u^{2p-1}` (in the paper `c_p = (2p-3)!!`), then
`m_{p+1} m_1^{p-1} / m_2^p = c_{p+1} A^p u^{2p+1} u^{p-1} / (A u^3)^p = c_{p+1}`, with no
limit taken. -/
theorem mul_pow_mul_pow_div_pow_eq (c : ℝ) {A u : ℝ} (hA : A ≠ 0) (hu : u ≠ 0) {p : ℕ}
    (hp : 1 ≤ p) :
    c * A ^ p * u ^ (2 * p + 1) * u ^ (p - 1) / (A * u ^ 3) ^ p = c := by
  have hexp : 2 * p + 1 + (p - 1) = 3 * p := by omega
  rw [mul_assoc (c * A ^ p), ← pow_add, hexp, mul_pow, ← pow_mul, mul_comm 3 p]
  field_simp

end SizeBias

/-! ### The Laplace transform of the Gamma law -/

/-- Every Gamma law is carried by `(0,∞)`. -/
theorem ae_pos_gammaMeasure (a r : ℝ) : ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  have h : gammaMeasure a r (Iic 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
      ← setLIntegral_congr (Iio_ae_eq_Iic (μ := volume) (a := (0 : ℝ)))]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  rw [ae_iff]
  exact measure_mono_null (fun x hx => by simpa using hx) h

/-- **The Laplace transform of the Gamma law.** `∫ e^{-tx} dΓ(a, r)(x) = (r / (r + t))^a` for
`t > -r`. -/
theorem integral_exp_neg_mul_gammaMeasure {a r t : ℝ} (ha : 0 < a) (hr : 0 < r)
    (ht : -r < t) :
    ∫ x, Real.exp (-(t * x)) ∂gammaMeasure a r = (r / (r + t)) ^ a := by
  have hrt : 0 < r + t := by linarith
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' _ _)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hzero : ∀ x ∉ Ici (0 : ℝ), (gammaPDF a r x).toReal • Real.exp (-(t * x)) = 0 := by
    intro x hx
    rw [gammaPDF_of_neg (by simpa using hx)]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi]
  have hfun : ∀ x ∈ Ioi (0 : ℝ), (gammaPDF a r x).toReal • Real.exp (-(t * x)) =
      r ^ a / Real.Gamma a * (x ^ (a - 1) * Real.exp (-((r + t) * x))) := by
    intro x hx
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul,
      gammaPDFReal, ite_eq_left (le_of_lt hx), mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha hrt]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [Real.div_rpow hr.le hrt.le, one_div, Real.inv_rpow hrt.le]
  field_simp

/-- The chi-square law with one degree of freedom vanishes on `(-∞, 0]`. -/
theorem ae_pos_gammaMeasure_one_half : ∀ᵐ x ∂gammaMeasure (1 / 2) (1 / 2), 0 < x :=
  ae_pos_gammaMeasure _ _

/-- **Laplace transform of the chi-square law.** `E e^{-tX} = (1 + 2t)^{-1/2}` for `t > -1/2`. -/
theorem integral_exp_neg_mul_gammaMeasure_one_half {t : ℝ} (ht : -(1 / 2) < t) :
    ∫ x, Real.exp (-(t * x)) ∂gammaMeasure (1 / 2) (1 / 2) = 1 / Real.sqrt (1 + 2 * t) := by
  rw [integral_exp_neg_mul_gammaMeasure (by norm_num) (by norm_num) ht]
  have hpos : 0 < 1 + 2 * t := by linarith
  have h : (1 / 2 : ℝ) / (1 / 2 + t) = (1 + 2 * t)⁻¹ := by
    field_simp
  rw [h, Real.inv_rpow hpos.le, ← Real.sqrt_eq_rpow, one_div]

/-! ### The chi-square tail integral -/

/-- `∫_0^λ e^{-tx} dt = (1 - e^{-λx}) / x` for `x ≠ 0`. -/
theorem integral_exp_neg_mul_eq_one_sub_exp_div {lam x : ℝ} (hx : x ≠ 0) :
    ∫ t in (0)..lam, Real.exp (-(t * x)) = (1 - Real.exp (-(lam * x))) / x := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t => -Real.exp (-(t * x)) / x) (Real.exp (-(t * x))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(t * x)) (-x) t := (hasDerivAt_mul_const x).neg
    have h2 := (h1.exp.neg).div_const x
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t * x))).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  ring

/-- **Fubini for the tail integral.** For a finite measure carried by `(0,∞)`,
`∫ (1 - e^{-λx}) / x dμ(x) = ∫_0^λ (∫ e^{-tx} dμ(x)) dt`. -/
theorem integral_one_sub_exp_neg_mul_div_eq {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 < x) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-(lam * x))) / x ∂μ =
      ∫ t in Ioc 0 lam, ∫ x, Real.exp (-(t * x)) ∂μ := by
  have hInt : Integrable (Function.uncurry fun x t : ℝ => Real.exp (-(t * x)))
      (μ.prod (volume.restrict (Ioc 0 lam))) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [hpos] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Function.uncurry_apply_pair, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_one_iff]
    nlinarith [ht.1]
  rw [← integral_integral_swap hInt]
  refine integral_congr_ae ?_
  filter_upwards [hpos] with x hx
  rw [← integral_exp_neg_mul_eq_one_sub_exp_div hx.ne', intervalIntegral.integral_of_le hlam]

/-- `∫_0^λ (1 + 2t)^{-1/2} dt = √(1 + 2λ) - 1`. -/
theorem integral_inv_sqrt_one_add_two_mul {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ t in (0)..lam, (Real.sqrt (1 + 2 * t))⁻¹ = Real.sqrt (1 + 2 * lam) - 1 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) lam,
      HasDerivAt (fun t => Real.sqrt (1 + 2 * t)) ((Real.sqrt (1 + 2 * t))⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hlam] at ht
    have hpos : (0 : ℝ) < 1 + 2 * t := by linarith [ht.1]
    have hs := (((hasDerivAt_id t).const_mul 2).const_add 1).sqrt hpos.ne'
    refine hs.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  have hInt : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 + 2 * t))⁻¹) volume 0 lam := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlam]
    refine ContinuousOn.inv₀ (by fun_prop) fun t ht => ?_
    have : (0 : ℝ) < 1 + 2 * t := by linarith [ht.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt]
  norm_num

/-- **The chi-square tail integral.** `∫ (1 - e^{-λx}) / x dQ∞(x) = √(1 + 2λ) - 1`. -/
theorem integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-(lam * x))) / x ∂gammaMeasure (1 / 2) (1 / 2) =
      Real.sqrt (1 + 2 * lam) - 1 := by
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  rw [integral_one_sub_exp_neg_mul_div_eq ae_pos_gammaMeasure_one_half hlam]
  have hfun : ∀ t ∈ Ioc (0 : ℝ) lam,
      ∫ x, Real.exp (-(t * x)) ∂gammaMeasure (1 / 2) (1 / 2) = (Real.sqrt (1 + 2 * t))⁻¹ := by
    intro t ht
    rw [integral_exp_neg_mul_gammaMeasure_one_half (by linarith [ht.1]), one_div]
  rw [setIntegral_congr_fun measurableSet_Ioc hfun, ← intervalIntegral.integral_of_le hlam]
  exact integral_inv_sqrt_one_add_two_mul hlam

/-- The chi-square density with one degree of freedom, written out:
`x^{-1/2} e^{-x/2} / √(2π)` on `(0,∞)`. -/
theorem gammaPDFReal_one_half_eq {x : ℝ} (hx : 0 < x) :
    gammaPDFReal (1 / 2) (1 / 2) x =
      1 / Real.sqrt (2 * Real.pi) * (Real.exp (-(x / 2)) * x ^ (-(1 / 2) : ℝ)) := by
  have hconst : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2) =
      1 / Real.sqrt (2 * Real.pi) := by
    rw [Real.Gamma_one_half_eq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi,
      ← Real.sqrt_eq_rpow, one_div (2 : ℝ), Real.sqrt_inv]
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
  rw [gammaPDFReal, ite_eq_left hx.le, hconst]
  ring_nf

/-- **The tail integral in the paper's displayed form.** With the chi-square density written
out, `(1/√(2π)) ∫_0^∞ (1 - e^{-λx}) e^{-x/2} x^{-3/2} dx = √(1 + 2λ) - 1`. -/
theorem integral_one_sub_exp_neg_mul_mul_exp_neg_half_rpow {lam : ℝ} (hlam : 0 ≤ lam) :
    1 / Real.sqrt (2 * Real.pi) *
        ∫ x in Ioi (0 : ℝ), (1 - Real.exp (-(lam * x))) * Real.exp (-(x / 2)) *
          x ^ (-(3 / 2) : ℝ) =
      Real.sqrt (1 + 2 * lam) - 1 := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  rw [← integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half hlam, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' _ _)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hzero : ∀ x ∉ Ici (0 : ℝ),
      (gammaPDF (1 / 2) (1 / 2) x).toReal • ((1 - Real.exp (-(lam * x))) / x) = 0 := by
    intro x hx
    rw [gammaPDF_of_neg (by simpa using hx)]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha ha x), smul_eq_mul,
    gammaPDFReal_one_half_eq hx0]
  have hcomb : x ^ (-(3 / 2) : ℝ) = x⁻¹ * x ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]
    norm_num
  rw [hcomb, div_eq_mul_inv]
  ring

/-! ### Transfer along weak convergence and the constant `√2` -/

/-- **Transfer of the tail integral along weak convergence.** If probability laws `μ i` on
`(0,∞)`, indexed along any filter, converge weakly to a law `μ₀` on `(0,∞)`, then
`∫ (1 - e^{-λx}) / x dμ i → ∫ (1 - e^{-λx}) / x dμ₀`. On `(0,∞)` the integrand agrees with the
bounded continuous kernel of `exists_bcf_laplaceKernel`, so no moment bound is needed. -/
theorem tendsto_integral_one_sub_exp_neg_mul_div_of_tendsto {ι : Type*} {l : Filter ι}
    {μ : ι → ProbabilityMeasure ℝ} {μ₀ : ProbabilityMeasure ℝ}
    (hpos : ∀ i, ∀ᵐ x ∂(μ i : Measure ℝ), 0 < x) (hpos₀ : ∀ᵐ x ∂(μ₀ : Measure ℝ), 0 < x)
    (hconv : Tendsto μ l (𝓝 μ₀)) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun i => ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(μ i : Measure ℝ)) l
      (𝓝 (∫ x, (1 - Real.exp (-(lam * x))) / x ∂(μ₀ : Measure ℝ))) := by
  obtain ⟨G, hG⟩ := exists_bcf_laplaceKernel hlam
  have hfun : ∀ ν : Measure ℝ, (∀ᵐ x ∂ν, 0 < x) →
      ∫ x, (1 - Real.exp (-(lam * x))) / x ∂ν = ∫ x, G x ∂ν := by
    intro ν hν
    refine integral_congr_ae ?_
    filter_upwards [hν] with x hx
    rw [hG x, max_eq_left hx.le]
    simp [hx.ne']
  rw [hfun _ hpos₀]
  simp_rw [hfun _ (hpos _)]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv G

/-- `(√(1 + 2λ) - 1) / √λ → √2` as `λ → ∞`. -/
theorem tendsto_sqrt_one_add_two_mul_sub_one_div_sqrt :
    Tendsto (fun lam : ℝ => (Real.sqrt (1 + 2 * lam) - 1) / Real.sqrt lam) atTop
      (𝓝 (Real.sqrt 2)) := by
  have hfirst : Tendsto (fun lam : ℝ => Real.sqrt (2 + lam⁻¹)) atTop (𝓝 (Real.sqrt 2)) := by
    have h : Tendsto (fun lam : ℝ => 2 + lam⁻¹) atTop (𝓝 2) := by
      simpa using tendsto_inv_atTop_zero.const_add (2 : ℝ)
    exact (Real.continuous_sqrt.tendsto 2).comp h
  have hsecond : Tendsto (fun lam : ℝ => (Real.sqrt lam)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  refine (by simpa using hfirst.sub hsecond :
    Tendsto (fun lam : ℝ => Real.sqrt (2 + lam⁻¹) - (Real.sqrt lam)⁻¹) atTop
      (𝓝 (Real.sqrt 2))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hsqrt : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hdiv : 2 + lam⁻¹ = (1 + 2 * lam) / lam := by
    field_simp
    ring
  rw [hdiv, Real.sqrt_div' (1 + 2 * lam) hlam.le]
  field_simp

/-- **The constant `√2`.** `λ^{-1/2} ∫ (1 - e^{-λx}) / x dQ∞(x) → √2` as `λ → ∞`. -/
theorem tendsto_integral_one_sub_exp_neg_mul_div_gammaMeasure_div_sqrt :
    Tendsto (fun lam : ℝ =>
        (∫ x, (1 - Real.exp (-(lam * x))) / x ∂gammaMeasure (1 / 2) (1 / 2)) /
          Real.sqrt lam) atTop (𝓝 (Real.sqrt 2)) := by
  refine tendsto_sqrt_one_add_two_mul_sub_one_div_sqrt.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
  rw [integral_one_sub_exp_neg_mul_div_gammaMeasure_one_half hlam]

end PercLib.Probability

/-! ### Non-vacuity witnesses (D-5) -/

namespace PercLib.Probability

/-- The point mass at `1` is carried by `(0,∞)`; its tail integral is `1 - e^{-λ}`, and the
constant sequence converges weakly to it. -/
example {lam : ℝ} :
    Tendsto (fun _ : ℕ => ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(Measure.dirac (1 : ℝ))) atTop
      (𝓝 (1 - Real.exp (-lam))) := by
  simp

/-- The size-biased law of `X ≡ 1` under the point mass is the point mass, and its first
moment is `E X² / (E X · 1) = 1`. -/
example :
    ∫ y, y ^ 1 ∂(((Measure.dirac ()).withDensity fun ω => ENNReal.ofReal
        ((fun _ : Unit => (1 : ℝ)) ω / ∫ ω, (fun _ : Unit => (1 : ℝ)) ω ∂Measure.dirac ())).map
        fun ω => (fun _ : Unit => (1 : ℝ)) ω / 1) = 1 := by
  rw [integral_pow_map_withDensity_ofReal_div _ measurable_const (ae_of_all _ fun _ => zero_le_one)]
  simp

end PercLib.Probability
