/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16 against pinned mathlib. No upstream proof is copied. The
statements are the standard Abelian theorems for power series (e.g. Feller, *An Introduction to
Probability Theory*, vol. II, XIII.5).
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import PercLib.Probability.LaplaceTail

/-!
# Abelian theorems for sums `∑ bₙ e^{-λn}`

Let `b : ℕ → ℝ` and write `B(λ) = ∑' n, bₙ e^{-λn}` for `λ > 0`.

1. `tendsto_rpow_mul_tsum_exp_of_isEquivalent` (item (i)): if `bₙ ~ c n^{a-1}` with `a > 0`,
   `c > 0`, then `λ^a B(λ) → c Γ(a)` as `λ ↓ 0`.
2. `tsum_exp_isEquivalent_log_of_isEquivalent` (item (ii)): if `bₙ ~ c/n` with `c > 0`, then
   `B(λ) ~ c log(1/λ)` as `λ ↓ 0`.
3. `tendsto_tsum_exp_of_summable` (item (iii)): if `∑ bₙ` converges, then `B(λ) → ∑ bₙ`.

The route for (i) and (ii) is a comparison lemma (`tsum_exp_isEquivalent_of_isEquivalent`):
if `bₙ ~ dₙ` with `dₙ ≥ 0` and `D(λ) = ∑ dₙ e^{-λn} → ∞`, then `B ~ D`. For (i) the
comparison sequence is the binomial coefficient `dₙ = C(a+n-1, n)`, whose generating function
is `(1-x)^{-a}` (`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`) and which satisfies
`C(a+n-1, n) ~ n^{a-1}/Γ(a)` by Euler's limit formula (`Real.GammaSeq_tendsto_Gamma`). For
(ii) it is `dₙ = 1/n`, with `∑ e^{-λn}/n = -log(1 - e^{-λ})`.

Changed hypotheses (strengthenings): (i) does not need `bₙ ≥ 0`; (ii) does not need
`bₙ ≥ 0`; (iii) needs only that `∑ bₙ` converges (in `ℝ` this is absolute convergence).
This file adds no definition.
-/

@[expose] public section

noncomputable section

open Filter Topology Asymptotics Real Finset

namespace PercLib.Analysis

/-! ### The comparison lemma -/

/-- **Comparison.** If `bₙ ~ dₙ`, `dₙ ≥ 0`, each `∑ dₙ e^{-λn}` converges and these sums tend
to `∞` as `λ ↓ 0`, then `∑ bₙ e^{-λn} ~ ∑ dₙ e^{-λn}`. -/
theorem tsum_exp_isEquivalent_of_isEquivalent {b d : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n)
    (hbd : b ~[atTop] d) (hsum : ∀ t : ℝ, 0 < t → Summable fun n : ℕ => d n * exp (-(t * n)))
    (hdiv : Tendsto (fun t : ℝ => ∑' n : ℕ, d n * exp (-(t * n))) (𝓝[>] 0) atTop) :
    (fun t : ℝ => ∑' n : ℕ, b n * exp (-(t * n))) ~[𝓝[>] 0]
      fun t : ℝ => ∑' n : ℕ, d n * exp (-(t * n)) := by
  rw [IsEquivalent, isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (isLittleO_iff.1 hbd.isLittleO (half_pos hε))
  set K := ∑ n ∈ range N, |b n - d n| with hKdef
  have hK : 0 ≤ K := sum_nonneg fun _ _ => abs_nonneg _
  filter_upwards [hdiv.eventually_ge_atTop (2 * K / ε), self_mem_nhdsWithin] with t hKt ht
  have ht : 0 < t := ht
  set e : ℕ → ℝ := fun n => exp (-(t * n))
  have he0 : ∀ n, 0 ≤ e n := fun n => (exp_pos _).le
  have he1 : ∀ n, e n ≤ 1 := fun n => exp_le_one_iff.2 (by
    have : 0 ≤ t * n := mul_nonneg ht.le n.cast_nonneg
    linarith)
  set g : ℕ → ℝ := fun n => (if n < N then |b n - d n| else 0) + ε / 2 * (d n * e n)
  have hfin : Summable fun n : ℕ => if n < N then |b n - d n| else 0 :=
    summable_of_ne_finset_zero (s := range N) fun n hn => by
      rw [mem_range] at hn; simp [hn]
  have hg : HasSum g (K + ε / 2 * ∑' n, d n * e n) := by
    refine HasSum.add ?_ ((hsum t ht).hasSum.mul_left _)
    convert hfin.hasSum using 1
    rw [tsum_eq_sum (s := range N) fun n hn => by rw [mem_range] at hn; simp [hn]]
    exact sum_congr rfl fun n hn => by rw [mem_range] at hn; simp [hn]
  have hbound : ∀ n, ‖(b n - d n) * e n‖ ≤ g n := fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (he0 n)]
    by_cases hn : n < N
    · simp only [g, hn, ite_true]
      have : |b n - d n| * e n ≤ |b n - d n| :=
        mul_le_of_le_one_right (abs_nonneg _) (he1 n)
      have : 0 ≤ ε / 2 * (d n * e n) := by have := hd n; have := he0 n; positivity
      linarith
    · simp only [g, hn, ite_false, zero_add]
      have h := hN n (not_lt.1 hn)
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (hd n)] at h
      calc |b n - d n| * e n ≤ ε / 2 * d n * e n := mul_le_mul_of_nonneg_right h (he0 n)
        _ = ε / 2 * (d n * e n) := by ring
  have hsumbd : Summable fun n => (b n - d n) * e n := Summable.of_norm_bounded hg.summable hbound
  have hsumb : Summable fun n => b n * e n := by
    convert hsumbd.add (hsum t ht) using 1
    ext n; simp only [e]; ring
  have hD0 : 0 ≤ ∑' n, d n * e n := tsum_nonneg fun n => mul_nonneg (hd n) (he0 n)
  have hdiff : (∑' n, b n * e n) - ∑' n, d n * e n = ∑' n, (b n - d n) * e n := by
    rw [← hsumb.tsum_sub (hsum t ht)]
    exact tsum_congr fun n => by ring
  change ‖(∑' n, b n * e n) - ∑' n, d n * e n‖ ≤ ε * ‖∑' n, d n * e n‖
  rw [hdiff, Real.norm_eq_abs (∑' n, d n * e n), abs_of_nonneg hD0]
  refine (tsum_of_norm_bounded hg hbound).trans ?_
  have : 2 * K / ε ≤ ∑' n, d n * e n := hKt
  rw [div_le_iff₀ hε] at this
  nlinarith

/-! ### Item (iii): convergent series -/

/-- **Abelian theorem, item (iii).** If `∑ bₙ` converges, then `∑ bₙ e^{-λn} → ∑ bₙ` as
`λ ↓ 0`. -/
theorem tendsto_tsum_exp_of_summable {b : ℕ → ℝ} (hb : Summable b) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, b n * exp (-(t * n))) (𝓝[>] 0) (𝓝 (∑' n, b n)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => ‖b n‖) hb.norm
    (fun n => ?_) ?_
  · have : Tendsto (fun t : ℝ => b n * exp (-(t * n))) (𝓝 0) (𝓝 (b n * exp (-(0 * n)))) :=
      (continuous_const.mul (continuous_exp.comp
        ((continuous_id.mul continuous_const).neg))).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht n
    rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (exp_le_one_iff.2 (by
      have : 0 ≤ t * n := mul_nonneg (le_of_lt ht) n.cast_nonneg
      linarith))

/-! ### Binomial coefficients -/

/-- `(a)ₙ = a (a+1) ⋯ (a+n-1)`. -/
theorem ascPochhammer_eval_eq_prod_range (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval a = ∏ j ∈ range n, (a + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, Polynomial.eval_mul, ih, prod_range_succ]
    simp

/-- `C(a+n-1, n) = a (a+1) ⋯ (a+n-1) / n!`. -/
theorem choose_add_sub_one_eq (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (∏ j ∈ range n, (a + j)) / n.factorial := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    show a + n - 1 - n + 1 = a by ring, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_eq_prod_range, smul_eq_mul, div_eq_inv_mul]

/-- For `a > 0`, `C(a+n-1, n) > 0`. -/
theorem choose_add_sub_one_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < Ring.choose (a + n - 1) n := by
  rw [choose_add_sub_one_eq]
  exact div_pos (prod_pos fun j _ => by positivity) (by positivity)

/-- **Binomial series.** `∑ C(a+n-1, n) xⁿ = (1-x)^{-a}` for `0 ≤ x < 1`. -/
theorem hasSum_choose_mul_pow (a : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => Ring.choose (a + n - 1) n * x ^ n) ((1 - x) ^ (-a)) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum
    (y := x) (by
      rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
      have : ‖x‖₊ < 1 := by
        rw [← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_of_nonneg hx0]; exact hx1
      exact_mod_cast this)
  rw [FormalMultilinearSeries.ofScalars_apply_eq'] at h
  simpa [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - x), one_div] using h

/-- **Euler.** `C(a+n-1, n) ~ n^{a-1}/Γ(a)` for `a > 0`. -/
theorem choose_add_sub_one_isEquivalent {a : ℝ} (ha : 0 < a) :
    (fun n : ℕ => Ring.choose (a + n - 1) n) ~[atTop] fun n => (n : ℝ) ^ (a - 1) / Gamma a := by
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun n : ℕ => Gamma a / GammaSeq a n * ((n : ℝ) / (n + a))) atTop
      (𝓝 (Gamma a / Gamma a * 1)) :=
    ((tendsto_const_nhds.div (GammaSeq_tendsto_Gamma a) hG.ne').mul
      (tendsto_natCast_div_add_atTop a))
  rw [div_self hG.ne', mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hP : 0 < ∏ j ∈ range n, (a + j) := prod_pos fun j _ => by positivity
  have hseq : GammaSeq a n = (n : ℝ) ^ a * n.factorial / ((∏ j ∈ range n, (a + j)) * (a + n)) := by
    rw [GammaSeq, prod_range_succ]
  have hrp : (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a / n := Real.rpow_sub_one hn0.ne' a
  have hna : (0 : ℝ) < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  simp only [Pi.div_apply]
  rw [choose_add_sub_one_eq, hseq, hrp]
  field_simp
  ring

/-! ### Item (i) -/

/-- `λ^a (1 - e^{-λ})^{-a} → 1` as `λ ↓ 0`. -/
theorem tendsto_rpow_mul_one_sub_exp_rpow_neg {a : ℝ} :
    Tendsto (fun t : ℝ => t ^ a * (1 - exp (-t)) ^ (-a)) (𝓝[>] 0) (𝓝 1) := by
  have h1 := PercLib.Probability.tendsto_one_sub_exp_neg_div
  have h3 : Tendsto (fun t : ℝ => ((1 - exp (-t)) / t) ^ (-a)) (𝓝[>] 0) (𝓝 1) := by
    have := h1.rpow_const (p := -a) (Or.inl one_ne_zero)
    simpa using this
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : (0 : ℝ) < t := ht
  have he : 0 ≤ 1 - exp (-t) := by
    have := exp_le_one_iff.2 (by linarith : -t ≤ 0); linarith
  rw [Real.div_rpow he ht.le, Real.rpow_neg ht.le, div_eq_mul_inv, inv_inv, mul_comm]

/-- **Abelian theorem, item (i).** If `bₙ ~ c n^{a-1}` with `a > 0` and `c > 0`, then
`λ^a ∑ bₙ e^{-λn} → c Γ(a)` as `λ ↓ 0`. -/
theorem tendsto_rpow_mul_tsum_exp_of_isEquivalent {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {b : ℕ → ℝ} (hb : b ~[atTop] fun n => c * (n : ℝ) ^ (a - 1)) :
    Tendsto (fun t : ℝ => t ^ a * ∑' n : ℕ, b n * exp (-(t * n))) (𝓝[>] 0)
      (𝓝 (c * Gamma a)) := by
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  set d : ℕ → ℝ := fun n => c * Gamma a * Ring.choose (a + n - 1) n
  have hd : ∀ n, 0 ≤ d n := fun n => (mul_pos (mul_pos hc hG) (choose_add_sub_one_pos ha n)).le
  have hbd : b ~[atTop] d := by
    refine hb.trans ?_
    have := (IsEquivalent.refl (u := fun _ : ℕ => c * Gamma a)).mul
      (choose_add_sub_one_isEquivalent ha).symm
    refine IsEquivalent.trans ?_ this
    refine IsEquivalent.congr_right (v := fun n : ℕ => c * (n : ℝ) ^ (a - 1)) IsEquivalent.refl ?_
    exact Eventually.of_forall fun n => by simp only [Pi.mul_apply]; field_simp
  -- The comparison sums.
  have hD : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => d n * exp (-(t * n))) (c * Gamma a * (1 - exp (-t)) ^ (-a)) := by
    intro t ht
    have hx1 : exp (-t) < 1 := exp_lt_one_iff.2 (by linarith)
    have := (hasSum_choose_mul_pow a (exp_pos (-t)).le hx1).mul_left (c * Gamma a)
    convert this using 2 with n
    simp only [d, ← Real.exp_nat_mul]
    rw [show -(t * n) = n * -t by ring]
    ring
  have hlim := tendsto_rpow_mul_one_sub_exp_rpow_neg (a := a)
  have hdiv : Tendsto (fun t : ℝ => ∑' n : ℕ, d n * exp (-(t * n))) (𝓝[>] 0) atTop := by
    have hcont : Tendsto (fun t : ℝ => t ^ a) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
        simpa [Real.zero_rpow ha.ne'] using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht using Real.rpow_pos_of_pos ht a
    have hinv := tendsto_inv_nhdsGT_zero.comp hcont
    have hprod := (hinv.atTop_mul_pos (by positivity : (0 : ℝ) < c * Gamma a * 1)
      ((tendsto_const_nhds (x := c * Gamma a)).mul hlim))
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : (0 : ℝ) < t := ht
    rw [(hD t ht).tsum_eq]
    simp only [Function.comp_apply]
    have : (t ^ a) ≠ 0 := (Real.rpow_pos_of_pos ht a).ne'
    field_simp
  have heq := tsum_exp_isEquivalent_of_isEquivalent hd hbd
    (fun t ht => (hD t ht).summable) hdiv
  have hfin : Tendsto (fun t : ℝ => t ^ a * ∑' n : ℕ, d n * exp (-(t * n))) (𝓝[>] 0)
      (𝓝 (c * Gamma a)) := by
    have := (tendsto_const_nhds (x := c * Gamma a)).mul hlim
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [(hD t ht).tsum_eq]
    ring
  exact ((IsEquivalent.refl (u := fun t : ℝ => t ^ a)).mul heq).symm.tendsto_nhds hfin

/-! ### Item (ii) -/

/-- `∑ₙ e^{-λn}/n = -log(1 - e^{-λ})` for `λ > 0` (the `n = 0` term is `0`). -/
theorem hasSum_inv_mul_exp {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => (n : ℝ)⁻¹ * exp (-(t * n))) (-log (1 - exp (-t))) := by
  have hx : |exp (-t)| < 1 := by
    rw [abs_of_pos (exp_pos _)]; exact exp_lt_one_iff.2 (by linarith)
  have h := hasSum_pow_div_log_of_abs_lt_one hx
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, Nat.cast_zero, inv_zero, zero_mul, sub_zero]
  convert h using 1
  ext n
  rw [show -(t * ((n + 1 : ℕ) : ℝ)) = ((n + 1 : ℕ) : ℝ) * -t by ring, Real.exp_nat_mul]
  push_cast
  ring

/-- `-log(1 - e^{-λ}) ~ log(1/λ)` as `λ ↓ 0`. -/
theorem neg_log_one_sub_exp_isEquivalent :
    (fun t : ℝ => -log (1 - exp (-t))) ~[𝓝[>] 0] fun t => log (1 / t) := by
  have h1 := PercLib.Probability.tendsto_one_sub_exp_neg_div
  have hlog : Tendsto (fun t : ℝ => log ((1 - exp (-t)) / t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using h1.log one_ne_zero
  have hinf : Tendsto (fun t : ℝ => log (1 / t)) (𝓝[>] 0) atTop := by
    simp only [one_div]
    exact tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  -- `-log(1 - e^{-t}) = log(1/t) - log((1 - e^{-t})/t)`.
  have hO : (fun t : ℝ => -log ((1 - exp (-t)) / t)) =O[𝓝[>] 0] fun _ => (1 : ℝ) :=
    (hlog.neg.isBigO_one ℝ)
  have hsmall : (fun _ : ℝ => (1 : ℝ)) =o[𝓝[>] 0] fun t => log (1 / t) :=
    (isLittleO_one_left_iff ℝ).2 (tendsto_norm_atTop_atTop.comp hinf)
  have := (hO.trans_isLittleO hsmall)
  refine (IsLittleO.add_isEquivalent this IsEquivalent.refl).congr_left ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : (0 : ℝ) < t := ht
  have he : 0 < 1 - exp (-t) := by have := exp_lt_one_iff.2 (by linarith : -t < 0); linarith
  simp only [Pi.add_apply]
  rw [Real.log_div he.ne' ht.ne', one_div, Real.log_inv]
  ring

/-- **Abelian theorem, item (ii).** If `bₙ ~ c/n` with `c > 0`, then
`∑ bₙ e^{-λn} ~ c log(1/λ)` as `λ ↓ 0`. -/
theorem tsum_exp_isEquivalent_log_of_isEquivalent {c : ℝ} (hc : 0 < c) {b : ℕ → ℝ}
    (hb : b ~[atTop] fun n => c / n) :
    (fun t : ℝ => ∑' n : ℕ, b n * exp (-(t * n))) ~[𝓝[>] 0] fun t => c * log (1 / t) := by
  set d : ℕ → ℝ := fun n => c * (n : ℝ)⁻¹
  have hd : ∀ n, 0 ≤ d n := fun n => mul_nonneg hc.le (inv_nonneg.2 n.cast_nonneg)
  have hbd : b ~[atTop] d := hb.congr_right (Eventually.of_forall fun n => by
    simp only [d, div_eq_mul_inv])
  have hD : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => d n * exp (-(t * n))) (c * -log (1 - exp (-t))) := fun t ht => by
    convert (hasSum_inv_mul_exp ht).mul_left c using 1
    ext n; simp only [d]; ring
  have hequiv : (fun t : ℝ => ∑' n : ℕ, d n * exp (-(t * n))) ~[𝓝[>] 0]
      fun t => c * log (1 / t) := by
    have := (IsEquivalent.refl (u := fun _ : ℝ => c)).mul neg_log_one_sub_exp_isEquivalent
    refine IsEquivalent.congr_left this ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((hD t ht).tsum_eq).symm
  have hdiv : Tendsto (fun t : ℝ => ∑' n : ℕ, d n * exp (-(t * n))) (𝓝[>] 0) atTop := by
    refine hequiv.symm.tendsto_atTop ?_
    have hinf : Tendsto (fun t : ℝ => log (1 / t)) (𝓝[>] 0) atTop := by
      simp only [one_div]
      exact tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    exact hinf.const_mul_atTop hc
  exact (tsum_exp_isEquivalent_of_isEquivalent hd hbd (fun t ht => (hD t ht).summable)
    hdiv).trans hequiv

/-! ### Non-vacuity -/

/-- Item (i) for `bₙ = n^{a-1}` exactly (`c = 1`). -/
example {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ a * ∑' n : ℕ, (n : ℝ) ^ (a - 1) * exp (-(t * n))) (𝓝[>] 0)
      (𝓝 (Gamma a)) := by
  simpa using tendsto_rpow_mul_tsum_exp_of_isEquivalent ha one_pos
    (b := fun n : ℕ => (n : ℝ) ^ (a - 1)) (by simpa using IsEquivalent.refl)

/-- Item (ii) for `bₙ = 1/n` exactly (`c = 1`), where the sum is the logarithm series. -/
example : (fun t : ℝ => ∑' n : ℕ, 1 / (n : ℝ) * exp (-(t * n))) ~[𝓝[>] 0]
    fun t => 1 * log (1 / t) :=
  tsum_exp_isEquivalent_log_of_isEquivalent one_pos IsEquivalent.refl

/-- Item (iii) for the summable sequence `bₙ = 2⁻ⁿ`. -/
example : Tendsto (fun t : ℝ => ∑' n : ℕ, (1 / 2 : ℝ) ^ n * exp (-(t * n))) (𝓝[>] 0)
    (𝓝 (∑' n : ℕ, (1 / 2 : ℝ) ^ n)) :=
  tendsto_tsum_exp_of_summable (summable_geometric_of_lt_one (by norm_num) (by norm_num))

end PercLib.Analysis

end
