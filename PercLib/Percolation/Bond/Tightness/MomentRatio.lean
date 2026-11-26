/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc, files `PercLib/CriticalLRP/Tightness/MomentRatio.lean`
(blob 331d362155) and `PercLib/CriticalLRP/Tightness/RealExponent.lean` (blob e177d7bd87),
contributed by `yujinhkim`. Licence: Apache-2.0, as declared in those files' headers and in
`third_party/critical-lrp/NOTICE.md` of that commit (upstream origin
`yujinhkim/Critical-Long-range-percolation` at 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf, not
independently verified). Changes: the abstract results are in namespace `PercLib.Probability`; the
source's definitions `momentConst`, `momentConstR`, `momentConstFull` are written out as expressions
and its `edianOf`/`edianMaxVol`/`clusterMaxVol`/`clusterVolIn`/`TailI26` are replaced by this
library's `tightnessScale`, `maxClusterIntersection`, `clusterIntersection` and the rooted conjunct
of `universalTightness`; the bond-interface statements of Corollary I.2.5 and of the lower bound are
new; the window-monotonicity and edian-existence parts of `RealExponent.lean` are not ported;
focused imports; `autoImplicit` off; linters on.
-/
module

public import PercLib.Percolation.Bond.Tightness.BKStep
public import PercLib.Percolation.Bond.Tightness.FiniteQuantile
public import PercLib.Percolation.Bond.Tightness.Hyperscaling
public import PercLib.Probability.DiscreteLayerCake
public import PercLib.Probability.MomentRatioFromTail
public import PercLib.Probability.TailSums

/-! # Moment ratios of one cluster at the quantile scale (Corollary I.2.5)

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Corollary I.2.5 and the
abstract part of Lemma I.2.6.

Abstract part (namespace `PercLib.Probability`), for `X : Ω → ℝ≥0∞` with the rooted
exponential tail `μ{X ≥ t} ≤ e · e^{-t/(9M)} · μ{X ≥ M}` (`t ≥ M`, `M ≥ 1`):
* `moment_ratio_le`: integer exponents `p ≥ 1`, `q ≥ 0`, integer-valued `X`;
* `moment_ratio_le_rpow_ennreal`, `moment_le_rpow_ennreal_of_tail`,
  `moment_ratio_le_rpow_ennreal_of_nonneg`: real exponents, `X` almost surely finite.

On the bond interface (namespace `PercLib.Percolation.Bond`), with `X = |K_u ∩ Λ|` and
`M = tightnessScale q Λ`:
* `law_clusterIntersection_tail_le`: the rooted tail, from `universalTightness`;
* `lintegral_rpow_clusterIntersection_add_le` and `..._of_nonneg` (Corollary I.2.5):
  `E X^{p+s} ≤ C_{p,s} M^s E X^p` for real `p > 0` (resp. `p ≥ 0`) and `s ≥ 0`;
* `sub_one_rpow_div_exp_le_lintegral_maxClusterIntersection`:
  `(M - 1)^p / e ≤ E max_{v ∈ Λ} |K_v ∩ Λ|^p` for real `p > 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Integer exponents -/

/-- **Corollary I.2.5, integer exponents.** Let `X` be integer-valued (or `∞`), `M ≥ 1`, and
`μ{X ≥ t} ≤ e · e^{-t/(9M)} · μ{X ≥ M}` for `t ≥ M`. Then for integers `p ≥ 1`, `q ≥ 0`,
`∫⁻ X^{p+q} ≤ C(p,q) M^q ∫⁻ X^p` with
`C(p,q) = (p+q) (2^q + e 2^{p+q} (p+q)! 9^{p+q} 36)`. -/
theorem moment_ratio_le {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) {M : ℝ} (hM1 : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω}
      ≤ ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ
      ≤ ENNReal.ofReal (((p + q : ℕ) : ℝ) *
        (2 ^ q + Real.exp 1 * 2 ^ (p + q) * ((p + q).factorial : ℝ) * 9 ^ (p + q) * 36)) *
            ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
  classical
  have hM0 : (0:ℝ) < M := by linarith
  set k : ℕ := p + q with hk
  have hk1 : 1 ≤ k := by omega
  set S : ℕ → ℝ≥0∞ := fun n => μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} with hS
  set TM : ℝ≥0∞ := μ {ω | ENNReal.ofReal M ≤ X ω} with hTM
  have hTMapply : TM = μ {ω | ENNReal.ofReal M ≤ X ω} := hTM
  have hSapply : ∀ n : ℕ, S n = μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := fun n => by rw [hS]
  -- layer cake for exponent `k`
  have hlc : ∫⁻ ω, X ω ^ k ∂μ
      = ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n) := by
    rw [lintegral_pow_eq_tsum_meas_ge hX hint k hk1]
  -- the two majorants
  set A : ℕ → ℝ≥0∞ := fun n => (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
      ((n : ℝ≥0∞) + 1) ^ (p - 1) * S n with hA
  set B : ℕ → ℝ≥0∞ := fun n => (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
      ((n : ℝ≥0∞) + 1) ^ (k - 1) *
      ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * M)))) * TM with hB
  have hAapply : ∀ n : ℕ, A n = (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
      ((n : ℝ≥0∞) + 1) ^ (p - 1) * S n := fun n => by rw [hA]
  have hBapply : ∀ n : ℕ, B n = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
      ((n : ℝ≥0∞) + 1) ^ (k - 1) *
      ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * M)))) * TM := fun n => by rw [hB]
  have hcasts : ∀ n : ℕ, ENNReal.ofReal ((n : ℝ) + 1) = ((n : ℝ≥0∞) + 1) := by
    intro n
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  -- termwise bound
  have hterm : ∀ n : ℕ, (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n ≤ A n + B n := by
    intro n
    have hD : ((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k ≤
        (k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1) := pow_succ_sub_pow_le k hk1 n
    by_cases hcase : ((n : ℝ) + 1) ≤ M
    · -- lower part
      have hkq : k - 1 = q + (p - 1) := by omega
      have hMq : ((n : ℝ≥0∞) + 1) ^ q ≤ ENNReal.ofReal ((M + 1) ^ q) := by
        rw [ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ M + 1)]
        refine pow_le_pow_left' ?_ q
        rw [← hcasts n]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      calc (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
          ≤ ((k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1)) * S n := by gcongr
        _ = (k : ℝ≥0∞) * (((n : ℝ≥0∞) + 1) ^ (k - 1) * S n) := by ring
        _ ≤ (k : ℝ≥0∞) * ((ENNReal.ofReal ((M + 1) ^ q) * ((n : ℝ≥0∞) + 1) ^ (p - 1)) *
              S n) := by
            gcongr
            rw [hkq, pow_add]
            exact mul_le_mul_left hMq _
        _ = A n := by rw [hAapply]; ring
        _ ≤ A n + B n := le_self_add
    · -- upper part
      push Not at hcase
      have htail' := htail ((n : ℝ) + 1) (le_of_lt hcase)
      have hset : {ω : Ω | ENNReal.ofReal ((n : ℝ) + 1) ≤ X ω}
          = {ω : Ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := by rw [hcasts n]
      rw [hset] at htail'
      calc (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
          ≤ ((k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1)) * S n := by gcongr
        _ ≤ ((k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1)) *
              (ENNReal.ofReal (Real.exp 1 * Real.exp (-(((n : ℝ) + 1) / (9 * M)))) * TM) := by
            gcongr
        _ = B n := by
            rw [hBapply, ENNReal.ofReal_mul (Real.exp_pos 1).le]
            ring
        _ ≤ A n + B n := self_le_add_left _ _
  -- sum the majorants
  have hsum : ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
      ≤ ∑' n : ℕ, A n + ∑' n : ℕ, B n := by
    calc ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) * S n
        ≤ ∑' n : ℕ, (A n + B n) := ENNReal.tsum_le_tsum hterm
      _ = ∑' n : ℕ, A n + ∑' n : ℕ, B n := ENNReal.tsum_add
  -- bound `∑ A`
  have hSA : ∑' n : ℕ, A n ≤ (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
    have hpow := lintegral_pow_eq_tsum_meas_ge (μ := μ) hX hint p hp
    have hcmp : ∑' n : ℕ, ((n : ℝ≥0∞) + 1) ^ (p - 1) * S n ≤ ∫⁻ ω, X ω ^ p ∂μ := by
      rw [hpow]
      refine ENNReal.tsum_le_tsum fun n => ?_
      rw [hSapply]
      exact mul_le_mul_left (pow_sub_pow_ge p hp n) _
    calc ∑' n : ℕ, A n
        = (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
            ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ (p - 1) * S n) := by
          rw [show (∑' n : ℕ, A n) = ∑' n : ℕ, (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) *
              (((n : ℝ≥0∞) + 1) ^ (p - 1) * S n) from tsum_congr fun n => by rw [hAapply]; ring]
          rw [ENNReal.tsum_mul_left]
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by gcongr
  -- bound `∑ B`
  have hSB : ∑' n : ℕ, B n ≤
      (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        (ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
          * (4 * (9 * M)))) * TM := by
    have hc0 : (0:ℝ) < 1 / (9 * M) := by positivity
    have hc1 : 1 / (9 * M) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hte := tsum_pow_mul_exp_neg_succ_le (k - 1) hc0 hc1
    have hexp : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) / (9 * M))))
        = ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (1 / (9 * M))))) := by
      intro n
      congr 2
      field_simp
    have hcinv : (1 / (9 * M))⁻¹ = 9 * M := by field_simp
    have h4 : 4 / (1 / (9 * M)) = 4 * (9 * M) := by field_simp
    rw [hcinv, h4] at hte
    calc ∑' n : ℕ, B n
        = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * TM *
            ∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ (k - 1) *
              ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (1 / (9 * M)))))) := by
          rw [show (∑' n : ℕ, B n) = ∑' n : ℕ, ((k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * TM) *
              (((n : ℝ≥0∞) + 1) ^ (k - 1) *
                ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (1 / (9 * M)))))) from
            tsum_congr fun n => by rw [hBapply, hexp n]; ring]
          rw [ENNReal.tsum_mul_left]
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * TM *
            ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
              * (4 * (9 * M))) := by gcongr
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
            (ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
              * (4 * (9 * M)))) * TM := by ring
  -- assemble
  have hfin : ∫⁻ ω, X ω ^ k ∂μ ≤
      (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ +
      (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
          * (4 * (9 * M))) * TM := by
    rw [hlc]
    exact le_trans hsum (add_le_add hSA hSB)
  -- rewrite the second constant and use `M^p * P(X ≥ M) ≤ E X^p`
  have hMeq : ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (9 * M) ^ (k - 1)
        * (4 * (9 * M)))
      = ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36) *
        ENNReal.ofReal (M ^ k) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hMk : M ^ k = M ^ (k - 1) * M := by
      rw [← pow_succ]
      congr 2
      omega
    rw [hMk]
    have h9 : (9 * M) ^ (k - 1) = 9 ^ (k - 1) * M ^ (k - 1) := by rw [mul_pow]
    rw [h9]
    field_simp
    ring
  rw [hMeq] at hfin
  -- final constant manipulations
  set D : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
    with hD
  have hMsplit : ENNReal.ofReal (M ^ k) = ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show k = q + p by omega, pow_add]
  have hTMp : ENNReal.ofReal (M ^ p) * TM ≤ ∫⁻ ω, X ω ^ p ∂μ := by
    rw [hTMapply, ENNReal.ofReal_pow hM0.le]
    exact ofReal_pow_mul_meas_le_lintegral hX hM0.le p
  have hM1 : ENNReal.ofReal ((M + 1) ^ q) ≤ ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (M + 1) ^ q ≤ (2 * M) ^ q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = 2 ^ q * M ^ q := by rw [mul_pow]
  -- bound the two summands
  have hb1 : (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, X ω ^ p ∂μ := by
    have h1 : (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) ≤
        (k : ℝ≥0∞) * (ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q)) :=
      mul_le_mul_right hM1 (k : ℝ≥0∞)
    have h2 := mul_le_mul_left h1 (∫⁻ ω, X ω ^ p ∂μ)
    calc (k : ℝ≥0∞) * ENNReal.ofReal ((M + 1) ^ q) * ∫⁻ ω, X ω ^ p ∂μ
        ≤ ((k : ℝ≥0∞) * (ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q))) *
            ∫⁻ ω, X ω ^ p ∂μ := h2
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) *
            ∫⁻ ω, X ω ^ p ∂μ := by ring
  have hb2flat : (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
        (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p)) * TM
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, X ω ^ p ∂μ := by
    calc (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
          (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p)) * TM
        = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
            ((ENNReal.ofReal (M ^ q)) * (ENNReal.ofReal (M ^ p) * TM)) := by ring
      _ ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
            (ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ) := by
          gcongr
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D * ENNReal.ofReal (M ^ q) *
            ∫⁻ ω, X ω ^ p ∂μ := by ring
  have hb2 : (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        (D * (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p))) * TM
      ≤ (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, X ω ^ p ∂μ := by
    rw [show (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        (D * (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p))) * TM
        = (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) * D *
          (ENNReal.ofReal (M ^ q) * ENNReal.ofReal (M ^ p)) * TM from by ring]
    exact hb2flat
  rw [hMsplit] at hfin
  -- now: combine constants
  have hconst : (k : ℝ) * 2 ^ q + (k : ℝ) * Real.exp 1 *
      ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
      ≤ ((p + q : ℕ) : ℝ) *
        (2 ^ q + Real.exp 1 * 2 ^ (p + q) * ((p + q).factorial : ℝ) * 9 ^ (p + q) * 36) := by
    have h2p : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have h9p : (9 : ℝ) ^ (k - 1) ≤ 9 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have hfac : ((k - 1).factorial : ℝ) ≤ ((k).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have step : ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        ≤ ((2 : ℝ) ^ k * ((k).factorial : ℝ) * 9 ^ k * 36) := by
      have s1 : (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) ≤ (2 : ℝ) ^ k * ((k).factorial : ℝ) :=
        mul_le_mul h2p hfac (by positivity) (by positivity)
      have s2 : (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1)
          ≤ (2 : ℝ) ^ k * ((k).factorial : ℝ) * 9 ^ k :=
        mul_le_mul s1 h9p (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right s2 (by norm_num)
    have h1 : (k : ℝ) * Real.exp 1 * ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^
        (k - 1) * 36)
        ≤ (k : ℝ) * Real.exp 1 * ((2 : ℝ) ^ k * ((k).factorial : ℝ) * 9 ^ k * 36) :=
      mul_le_mul_of_nonneg_left step (by positivity)
    have hconst_k : (k : ℝ) * 2 ^ q + (k : ℝ) * Real.exp 1 *
        ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        ≤ (k : ℝ) * (2 ^ q + Real.exp 1 * 2 ^ k * ((k).factorial : ℝ) * 9 ^ k * 36) := by
      nlinarith [h1]
    exact hconst_k
  refine le_trans hfin ?_
  rw [hD] at hb2 ⊢
  have hA2 : (0:ℝ) ≤ (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36 := by positivity
  have hcomb : (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) * ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ +
      (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36) *
        ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ
      = ENNReal.ofReal ((k : ℝ) * 2 ^ q + (k : ℝ) * Real.exp 1 *
          ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)) *
        ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
    have e1 : (k : ℝ≥0∞) * ENNReal.ofReal (2 ^ q) = ENNReal.ofReal ((k : ℝ) * 2 ^ q) :=
      natCast_mul_ofReal k (by positivity)
    have e2 : (k : ℝ≥0∞) * ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)
        = ENNReal.ofReal ((k : ℝ) * Real.exp 1 *
            ((2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36)) := by
      rw [natCast_mul_ofReal k (by positivity),
        ← ENNReal.ofReal_mul (p := (k : ℝ) * Real.exp 1)
          (q := (2 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * 9 ^ (k - 1) * 36) (by positivity)]
    rw [e1, e2, ← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_trans (add_le_add hb1 hb2) (le_trans (le_of_eq hcomb) ?_)
  gcongr

/-! ### Real exponents -/

/-- Tail events of `X` and of its real truncation agree almost everywhere. -/
lemma measure_toReal_le {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hfin : μ {ω | X ω = ⊤} = 0) (t : ℝ) :
    μ {ω : Ω | t ≤ (X ω).toReal} = μ {ω : Ω | ENNReal.ofReal t ≤ X ω} := by
  have haefin : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := measure_eq_zero_iff_ae_notMem.mp hfin
  refine measure_congr ?_
  filter_upwards [haefin] with ω hω
  exact propext (ENNReal.ofReal_le_iff_le_toReal hω).symm

/-- Moments of `X` and of its real truncation agree. -/
lemma lintegral_rpow_toReal {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hfin : μ {ω | X ω = ⊤} = 0)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, X ω ^ r ∂μ = ∫⁻ ω, ENNReal.ofReal ((X ω).toReal ^ r) ∂μ := by
  have haefin : ∀ᵐ ω ∂μ, X ω ≠ ⊤ := measure_eq_zero_iff_ae_notMem.mp hfin
  refine lintegral_congr_ae ?_
  filter_upwards [haefin] with ω hω
  calc X ω ^ r = (ENNReal.ofReal (X ω).toReal) ^ r := by rw [ENNReal.ofReal_toReal hω]
    _ = ENNReal.ofReal ((X ω).toReal ^ r) :=
      ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr

/-- **Corollary I.2.5, real exponents `p > 0`, `q ≥ 0`,** for an almost surely finite
`X : Ω → ℝ≥0∞`, with `C(p,q) = (p+q)/p + e (p+q) 9^{p+q} Γ(p+q)`. -/
theorem moment_ratio_le_rpow_ennreal {μ : Measure Ω} {X : Ω → ℝ≥0∞} (hX : Measurable X)
    (hfin : μ {ω | X ω = ⊤} = 0) {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ ≤
      ENNReal.ofReal ((p + q) / p + Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
        ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
  have htail' : ∀ t : ℝ, M ≤ t → μ {ω : Ω | t ≤ (X ω).toReal} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω : Ω | M ≤ (X ω).toReal} := by
    intro t ht
    rw [measure_toReal_le hfin t, measure_toReal_le hfin M]
    exact htail t ht
  have hmain := moment_ratio_le_rpow hX.ennreal_toReal
    (fun ω => ENNReal.toReal_nonneg) hM htail' hp hq
  rw [lintegral_rpow_toReal hfin (by linarith : (0 : ℝ) ≤ p + q),
    lintegral_rpow_toReal hfin hp.le]
  exact hmain

/-- **The case `p = 0`:** `E X^r ≤ (1 + e r 9^r Γ(r)) M^r` for `r > 0`. -/
theorem moment_le_rpow_ennreal_of_tail {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0) {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, X ω ^ r ∂μ ≤
      ENNReal.ofReal (1 + Real.exp 1 * r * 9 ^ r * Real.Gamma r) * ENNReal.ofReal (M ^ r) := by
  have htail' : ∀ t : ℝ, M ≤ t → μ {ω : Ω | t ≤ (X ω).toReal} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω : Ω | M ≤ (X ω).toReal} := by
    intro t ht
    rw [measure_toReal_le hfin t, measure_toReal_le hfin M]
    exact htail t ht
  have hmain := moment_le_rpow_of_tail hX.ennreal_toReal
    (fun ω => ENNReal.toReal_nonneg) hM htail' hr
  rw [lintegral_rpow_toReal hfin hr.le]
  exact hmain

/-- **Corollary I.2.5 on the full range `p, q ≥ 0`**, with
`C(p,q) = (p+q)/p + 1 + e (p+q) 9^{p+q} Γ(p+q)` (at `p = 0`, `(p+q)/p = 0` by Lean's
convention and the right-hand side is `C M^q`, since `E X^0 = 1`). -/
theorem moment_ratio_le_rpow_ennreal_of_nonneg {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0) {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | ENNReal.ofReal t ≤ X ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) *
        μ {ω | ENNReal.ofReal M ≤ X ω})
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∫⁻ ω, X ω ^ (p + q) ∂μ ≤
      ENNReal.ofReal ((p + q) / p + 1 + Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
        ENNReal.ofReal (M ^ q) * ∫⁻ ω, X ω ^ p ∂μ := by
  have hX0 : ∫⁻ ω, X ω ^ ((0 : ℝ)) ∂μ = 1 := by
    simp only [ENNReal.rpow_zero, lintegral_one, measure_univ]
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · subst hp0
    rw [zero_add, hX0, mul_one]
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · subst hq0
      simp
    · have hc : q / 0 + 1 + Real.exp 1 * q * 9 ^ q * Real.Gamma q =
          1 + Real.exp 1 * q * 9 ^ q * Real.Gamma q := by simp
      rw [hc]
      exact moment_le_rpow_ennreal_of_tail hX hfin hM htail hqpos
  · refine le_trans (moment_ratio_le_rpow_ennreal hX hfin hM htail hppos hq) ?_
    refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl) le_rfl
    linarith

/-- Markov's bound for extended cardinalities: `M^p μ{M ≤ X} ≤ E X^p`. -/
theorem ofReal_rpow_mul_meas_le_lintegral_ennreal {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hfin : μ {ω | X ω = ⊤} = 0) {M : ℝ} (hM : 0 ≤ M) {p : ℝ}
    (hp : 0 < p) :
    ENNReal.ofReal (M ^ p) * μ {ω | ENNReal.ofReal M ≤ X ω} ≤ ∫⁻ ω, X ω ^ p ∂μ := by
  rw [← measure_toReal_le hfin M, lintegral_rpow_toReal hfin hp.le]
  exact ofReal_rpow_mul_meas_le_lintegral hX.ennreal_toReal hM hp

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- The cluster intersection is never infinite. -/
theorem law_clusterIntersection_eq_top (q : Sym2 V → unitInterval) (Λ : Finset V) (u : V) :
    law q {ω | (clusterIntersection Λ ω u : ℝ≥0∞) = ⊤} = 0 := by
  simp

open Classical in
/-- **The rooted tail (I.2.6)** from `universalTightness`, in the form of the abstract
moment-ratio theorems: for real `t ≥ M`,
`P(X_u ≥ t) ≤ e · e^{-t/(9M)} · P(X_u ≥ M)`. -/
theorem law_clusterIntersection_tail_le [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) (t : ℝ) (ht : (tightnessScale q Λ : ℝ) ≤ t) :
    law q {ω | ENNReal.ofReal t ≤ (clusterIntersection Λ ω u : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * (tightnessScale q Λ : ℝ))))) *
        law q {ω | ENNReal.ofReal (tightnessScale q Λ : ℝ) ≤
          (clusterIntersection Λ ω u : ℝ≥0∞)} := by
  set M := tightnessScale q Λ with hM
  have hM0 : (0 : ℝ) < M := by
    exact_mod_cast (show 0 < M by have := two_le_tightnessScale q hΛ; omega)
  have ha : 1 ≤ t / M := by rwa [le_div_iff₀ hM0, one_mul]
  have h := (universalTightness V q Λ hΛ).2.2 u (t / M) ha
  have hs1 : {ω | ENNReal.ofReal t ≤ (clusterIntersection Λ ω u : ℝ≥0∞)} =
      {ω | t / M * (tightnessScale q Λ : ℝ) ≤ (clusterIntersection Λ ω u : ℝ)} := by
    ext ω
    simp only [mem_ofPred_eq, ← hM, div_mul_cancel₀ _ hM0.ne']
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)]
  have hs2 : {ω | ENNReal.ofReal (M : ℝ) ≤ (clusterIntersection Λ ω u : ℝ≥0∞)} =
      {ω | tightnessScale q Λ ≤ clusterIntersection Λ ω u} := by
    ext ω
    simp only [mem_ofPred_eq, ENNReal.ofReal_natCast, Nat.cast_le, hM]
  rw [hs1, hs2, ENNReal.ofReal_mul (Real.exp_pos 1).le]
  calc _ ≤ _ := h
    _ = _ := by
        rw [show -(t / M) / 9 = -(t / (9 * M)) by field_simp]
        ring

/-- The cluster intersection is measurable as an `ℝ≥0∞`-valued function. -/
theorem measurable_clusterIntersection_ennreal [Countable V] (Λ : Finset V) (u : V) :
    Measurable fun ω : Config V => (clusterIntersection Λ ω u : ℝ≥0∞) :=
  measurable_from_nat.comp (measurable_clusterIntersection Λ u)

/-- **Corollary I.2.5 on the bond interface, `p > 0`.** For real `p > 0` and `s ≥ 0`,
`E X_u^{p+s} ≤ C(p,s) M^s E X_u^p` with `C(p,s) = (p+s)/p + e (p+s) 9^{p+s} Γ(p+s)`. -/
theorem lintegral_rpow_clusterIntersection_add_le [Countable V] (q : Sym2 V → unitInterval)
    {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) :
    ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ^ (p + s) ∂(law q) ≤
      ENNReal.ofReal ((p + s) / p + Real.exp 1 * (p + s) * 9 ^ (p + s) * Real.Gamma (p + s)) *
        ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ s) *
        ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ^ p ∂(law q) :=
  moment_ratio_le_rpow_ennreal (measurable_clusterIntersection_ennreal Λ u)
    (law_clusterIntersection_eq_top q Λ u)
    (by exact_mod_cast (show 1 ≤ tightnessScale q Λ by
      have := two_le_tightnessScale q hΛ; omega))
    (law_clusterIntersection_tail_le q hΛ u) hp hs

/-- **Corollary I.2.5 on the bond interface, full range `p, s ≥ 0`,** with
`C(p,s) = (p+s)/p + 1 + e (p+s) 9^{p+s} Γ(p+s)`. -/
theorem lintegral_rpow_clusterIntersection_add_le_of_nonneg [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) (u : V) {p s : ℝ}
    (hp : 0 ≤ p) (hs : 0 ≤ s) :
    ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ^ (p + s) ∂(law q) ≤
      ENNReal.ofReal ((p + s) / p + 1 + Real.exp 1 * (p + s) * 9 ^ (p + s) *
          Real.Gamma (p + s)) *
        ENNReal.ofReal ((tightnessScale q Λ : ℝ) ^ s) *
        ∫⁻ ω, (clusterIntersection Λ ω u : ℝ≥0∞) ^ p ∂(law q) :=
  moment_ratio_le_rpow_ennreal_of_nonneg (measurable_clusterIntersection_ennreal Λ u)
    (law_clusterIntersection_eq_top q Λ u)
    (by exact_mod_cast (show 1 ≤ tightnessScale q Λ by
      have := two_le_tightnessScale q hΛ; omega))
    (law_clusterIntersection_tail_le q hΛ u) hp hs

/-- **Lower bound at the quantile** (abstract part of Lemma I.2.6): for real `p > 0`,
`(M - 1)^p / e ≤ E max_{v ∈ Λ} |K_v ∩ Λ|^p`. -/
theorem sub_one_rpow_div_exp_le_lintegral_maxClusterIntersection [Countable V]
    (q : Sym2 V → unitInterval) {Λ : Finset V} (hΛ : Λ.Nonempty) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (((tightnessScale q Λ : ℝ) - 1) ^ p / Real.exp 1) ≤
      ∫⁻ ω, (maxClusterIntersection Λ ω : ℝ≥0∞) ^ p ∂(law q) := by
  set M := tightnessScale q Λ with hM
  have hM1 : 1 ≤ M := by have := two_le_tightnessScale q hΛ; omega
  have hMreal : (0 : ℝ) ≤ (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hmin := lt_law_max_tail_of_lt_tightnessScale q Λ (show M - 1 < M by omega)
  have hcast : ((M - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((M : ℝ) - 1) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sub hM1, Nat.cast_one]
  have hset : {ω | M - 1 ≤ maxClusterIntersection Λ ω} =
      {ω | ENNReal.ofReal ((M : ℝ) - 1) ≤ (maxClusterIntersection Λ ω : ℝ≥0∞)} := by
    ext ω
    simp only [mem_ofPred_eq, ← hcast, Nat.cast_le]
  rw [hset] at hmin
  have hmarkov := ofReal_rpow_mul_meas_le_lintegral_ennreal (μ := law q)
    (X := fun ω => (maxClusterIntersection Λ ω : ℝ≥0∞))
    (measurable_from_nat.comp (measurable_maxClusterIntersection Λ)) (by simp) hMreal hp
  rw [div_eq_mul_inv, ← Real.exp_neg, ENNReal.ofReal_mul (Real.rpow_nonneg hMreal _)]
  exact (mul_le_mul' le_rfl hmin.le).trans hmarkov

/-! ### Non-vacuity: `Λ = {v}`, `X = 1`, `M = 2` -/

/-- With `Λ = {0}` in `ℕ`, `X_0 = 1` and `M = 2`: Corollary I.2.5 reads
`1 ≤ C(p,s) 2^s` and the lower bound reads `1/e ≤ 1`; every hypothesis holds. -/
example (q : Sym2 ℕ → unitInterval) {p s : ℝ} (hp : 0 < p) (hs : 0 ≤ s) :
    ∫⁻ ω, (clusterIntersection {0} ω 0 : ℝ≥0∞) ^ (p + s) ∂(law q) ≤
      ENNReal.ofReal ((p + s) / p + Real.exp 1 * (p + s) * 9 ^ (p + s) * Real.Gamma (p + s)) *
        ENNReal.ofReal ((2 : ℝ) ^ s) *
        ∫⁻ ω, (clusterIntersection {0} ω 0 : ℝ≥0∞) ^ p ∂(law q) ∧
    ENNReal.ofReal (((2 : ℝ) - 1) ^ p / Real.exp 1) ≤
      ∫⁻ ω, (maxClusterIntersection {(0 : ℕ)} ω : ℝ≥0∞) ^ p ∂(law q) := by
  have h2 := tightnessScale_singleton q (0 : ℕ)
  have h1 := lintegral_rpow_clusterIntersection_add_le q (Finset.singleton_nonempty 0) 0 hp hs
  have h3 := sub_one_rpow_div_exp_le_lintegral_maxClusterIntersection q
    (Finset.singleton_nonempty (0 : ℕ)) hp
  rw [h2] at h1 h3
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h3⟩

end PercLib.Percolation.Bond
