/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, from pinned mathlib's Stirling formula (`Stirling.tendsto_stirlingSeq_sqrt_pi`) and
Catalan numbers. The statements follow the wiki tags AAZS and V5OZ (binary-tree percolation). No
source text or code is copied.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import PercLib.Models.BinaryTree
public import PercLib.Models.BinaryTreeCatalan
public import PercLib.Percolation.Bond.Susceptibility

/-!
# Binary tree: exact critical volume asymptotics

Write `a_n(p) = Cat(n) 4^{-n} ((1-p)/p) (4p(1-p))^n = Cat(n) p^{n-1} (1-p)^{n+1}` for the
Catalan law of 9K6O (the index `n` is the cluster size, as in
`binaryTree_law_cluster_card_eq_catalan`, `Models/BinaryTreeCatalan.lean`).

* `centralBinom_div_four_pow_mul_sqrt_tendsto`: `C(2n,n) 4^{-n} √n → 1/√π` (Stirling);
* `catalan_div_four_pow_isEquivalent` (item 1): `Cat(n)/4^n ~ n^{-3/2}/√π`;
* `tsum_catalan_div_four_pow_tail` (exact): `∑_{k ≥ n} Cat(k)/4^k = 2 C(2n,n)/4^n`;
* `catalan_critical_isEquivalent`, `catalan_critical_tail_isEquivalent` (AAZS):
  `a_n(1/2) ~ n^{-3/2}/√π` and `∑_{k ≥ n} a_k(1/2) ~ 2 n^{-1/2}/√π`;
* `catalan_tendstoUniformlyOn_ratio` (V5OZ): the ratio
  `a_n(p) / [((1-p)/(p√π)) n^{-3/2} (4p(1-p))^n]` tends to `1` uniformly in `p ∈ (0,1)`;
* `catalan_nearCritical_isEquivalent` (V5OZ): if `p_n = 1/2 + ε_n`, `ε_n → 0` and `n ε_n⁴ → 0`, then
  `a_n(p_n) ~ n^{-3/2} e^{-4 n ε_n²}/√π`.
-/

@[expose] public section
noncomputable section

open Filter Topology Asymptotics Real Nat

namespace PercLib.Models

/-! ### Central binomial coefficients -/

/-- `C(2n,n) 4^{-n} √n = s(2n) / s(n)²` with `s` the Stirling sequence, for `n ≥ 1`. -/
theorem centralBinom_div_four_pow_mul_sqrt_eq {n : ℕ} (hn : 1 ≤ n) :
    (n.centralBinom : ℝ) / 4 ^ n * √(n : ℝ) =
      Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((2 * n)! : ℝ) = n.centralBinom * (n ! : ℝ) * (n ! : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
    rw [show 2 * n - n = n by omega, ← Nat.centralBinom_eq_two_mul_choose] at h
    exact_mod_cast h.symm
  have hs2 : √(2 * ((2 * n : ℕ) : ℝ)) = 2 * √(n : ℝ) := by
    rw [show (2 : ℝ) * ((2 * n : ℕ) : ℝ) = 2 ^ 2 * n by push_cast; ring, Real.sqrt_mul
      (by norm_num), Real.sqrt_sq (by norm_num)]
  have hsq : √(2 * (n : ℝ)) ^ 2 = 2 * n := Real.sq_sqrt (by positivity)
  have he : ((((2 * n : ℕ) : ℝ)) / exp 1) ^ (2 * n) = 4 ^ n * (((n : ℝ) / exp 1) ^ n) ^ 2 := by
    rw [show (((2 * n : ℕ) : ℝ)) / exp 1 = 2 * ((n : ℝ) / exp 1) by push_cast; ring, mul_pow,
      pow_mul (2 : ℝ), pow_mul' ((n : ℝ) / exp 1)]
    norm_num
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hfpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hB : (0 : ℝ) < ((n : ℝ) / exp 1) ^ n := pow_pos (div_pos hn0 (exp_pos 1)) n
  have hnn : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  unfold Stirling.stirlingSeq
  rw [hfac, hs2, he]
  generalize ((n : ℝ) / exp 1) ^ n = B at hB ⊢
  rw [div_pow, mul_pow, hsq]
  field_simp
  rw [hnn]

/-- **Stirling for central binomial coefficients.** `C(2n,n) 4^{-n} √n → 1/√π`. -/
theorem centralBinom_div_four_pow_mul_sqrt_tendsto :
    Tendsto (fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n * √(n : ℝ)) atTop (𝓝 (1 / √π)) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
  have h2 : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n)) atTop (𝓝 √π) :=
    hs.comp (tendsto_id.const_mul_atTop' (by norm_num))
  have hπ : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hlim : Tendsto (fun n : ℕ => Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2)
      atTop (𝓝 (√π / √π ^ 2)) := h2.div (hs.pow 2) (pow_ne_zero 2 hπ)
  rw [show √π / √π ^ 2 = 1 / √π by field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (centralBinom_div_four_pow_mul_sqrt_eq hn).symm

/-- `C(2n,n) 4^{-n} → 0`. -/
theorem centralBinom_div_four_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (n.centralBinom : ℝ) / 4 ^ n) atTop (𝓝 0) := by
  have h := centralBinom_div_four_pow_mul_sqrt_tendsto
  have hinv : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact this.inv_tendsto_atTop
  have := h.mul hinv
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  field_simp

/-! ### Item 1 -/

/-- **Item 1.** `Cat(n)/4^n ~ n^{-3/2}/√π`. -/
theorem catalan_div_four_pow_isEquivalent :
    (fun n : ℕ => (catalan n : ℝ) / 4 ^ n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) / √π := by
  refine isEquivalent_of_tendsto_one ?_
  have h := centralBinom_div_four_pow_mul_sqrt_tendsto
  have hn1 : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    have := tendsto_natCast_div_add_atTop (1 : ℝ)
    simpa using this
  have hπ : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hlim := (h.mul hn1).const_mul √π
  rw [show √π * (1 / √π * 1) = 1 by field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcat : (catalan n : ℝ) = n.centralBinom / ((n : ℝ) + 1) := by
    have h := succ_mul_catalan_eq_centralBinom n
    have h' : ((n : ℝ) + 1) * catalan n = n.centralBinom := by exact_mod_cast h
    field_simp
    linarith
  have hrpow : (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((n : ℝ) * √(n : ℝ)) := by
    rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn0.le (by norm_num)]
    norm_num
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  simp only [Pi.div_apply]
  rw [hcat, hrpow]
  field_simp

/-- Item 1 as a ratio limit. -/
theorem catalan_tendsto_ratio :
    Tendsto ((fun n : ℕ => (catalan n : ℝ) / 4 ^ n) / fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) / √π)
      atTop (𝓝 1) := by
  refine (isEquivalent_iff_tendsto_one ?_).1 catalan_div_four_pow_isEquivalent
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hr : 0 < (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  positivity

/-! ### The exact tail -/

/-- `Cat(k)/4^k = 2 C(2k,k)/4^k - 2 C(2k+2,k+1)/4^{k+1}`. -/
theorem catalan_div_four_pow_eq_sub (k : ℕ) :
    (catalan k : ℝ) / 4 ^ k =
      2 * ((k.centralBinom : ℝ) / 4 ^ k) - 2 * (((k + 1).centralBinom : ℝ) / 4 ^ (k + 1)) := by
  have h1 : ((k : ℝ) + 1) * catalan k = k.centralBinom := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom k
  have h2 : ((k : ℝ) + 1) * (k + 1).centralBinom = 2 * (2 * k + 1) * k.centralBinom := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hc : (catalan k : ℝ) = k.centralBinom / (k + 1) := by field_simp; linarith
  have hc' : ((k + 1).centralBinom : ℝ) = 2 * (2 * k + 1) * k.centralBinom / (k + 1) := by
    field_simp; linarith
  rw [hc, hc', pow_succ]
  field_simp
  ring

/-- **The exact tail.** `∑_{k ≥ n} Cat(k)/4^k = 2 C(2n,n)/4^n`. -/
theorem hasSum_catalan_div_four_pow_tail (n : ℕ) :
    HasSum (fun k : ℕ => (catalan (k + n) : ℝ) / 4 ^ (k + n))
      (2 * ((n.centralBinom : ℝ) / 4 ^ n)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range m, (catalan (k + n) : ℝ) / 4 ^ (k + n) =
      2 * ((n.centralBinom : ℝ) / 4 ^ n) -
        2 * (((m + n).centralBinom : ℝ) / 4 ^ (m + n)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, catalan_div_four_pow_eq_sub, show m + 1 + n = m + n + 1 by
        omega]
      ring
  simp_rw [htel]
  have h0 := (centralBinom_div_four_pow_tendsto_zero.comp
    (tendsto_add_atTop_nat n)).const_mul 2
  rw [mul_zero] at h0
  have := (tendsto_const_nhds (x := 2 * ((n.centralBinom : ℝ) / 4 ^ n))).sub h0
  rw [sub_zero] at this
  exact this

/-- **The exact tail**, as a `tsum`. -/
theorem tsum_catalan_div_four_pow_tail (n : ℕ) :
    ∑' k : ℕ, (catalan (k + n) : ℝ) / 4 ^ (k + n) = 2 * ((n.centralBinom : ℝ) / 4 ^ n) :=
  (hasSum_catalan_div_four_pow_tail n).tsum_eq

/-! ### AAZS -/

/-- **Point mass.** `a_n(1/2) ~ n^{-3/2}/√π`. -/
theorem catalan_critical_isEquivalent :
    (fun n : ℕ => (catalan n : ℝ) / 4 ^ n * ((1 - 1 / 2) / (1 / 2)) *
        (4 * (1 / 2) * (1 - 1 / 2)) ^ n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) / √π := by
  refine IsEquivalent.congr_left catalan_div_four_pow_isEquivalent ?_
  exact Eventually.of_forall fun n => by norm_num

/-- **Tail.** `∑_{k ≥ n} a_k(1/2) ~ 2 n^{-1/2}/√π`. -/
theorem catalan_critical_tail_isEquivalent :
    (fun n : ℕ => ∑' k : ℕ, (catalan (k + n) : ℝ) / 4 ^ (k + n) *
        ((1 - 1 / 2) / (1 / 2)) * (4 * (1 / 2) * (1 - 1 / 2)) ^ (k + n)) ~[atTop]
      fun n : ℕ => 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) / √π := by
  have hπ : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  refine isEquivalent_of_tendsto_one ?_
  have hlim := centralBinom_div_four_pow_mul_sqrt_tendsto.const_mul √π
  rw [show √π * (1 / √π) = 1 by field_simp] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(n : ℝ) := by
    rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow, inv_eq_one_div]
  simp only [Pi.div_apply]
  have hsum : ∑' k : ℕ, (catalan (k + n) : ℝ) / 4 ^ (k + n) *
      ((1 - 1 / 2) / (1 / 2)) * (4 * (1 / 2) * (1 - 1 / 2)) ^ (k + n) =
      2 * ((n.centralBinom : ℝ) / 4 ^ n) := by
    rw [← tsum_catalan_div_four_pow_tail n]
    exact tsum_congr fun k => by norm_num
  rw [hsum, hrpow]
  field_simp

/-! ### V5OZ -/

/-- The ratio of the uniform asymptotics does not depend on `p ∈ (0,1)`. -/
theorem catalan_ratio_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (catalan n : ℝ) / 4 ^ n * ((1 - p) / p) * (4 * p * (1 - p)) ^ n /
        ((1 - p) / (p * √π) * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (4 * p * (1 - p)) ^ n) =
      (catalan n : ℝ) / 4 ^ n / ((n : ℝ) ^ (-(3 / 2 : ℝ)) / √π) := by
  have h1 : 0 < 1 - p := by linarith
  have h4 : 0 < 4 * p * (1 - p) := by positivity
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hpow : (4 * p * (1 - p)) ^ n ≠ 0 := (pow_pos h4 n).ne'
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by norm_num : (-(3 / 2 : ℝ)) ≠ 0)]
  · have hr : 0 < (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    field_simp

/-- **Uniform ratio.** The ratio `a_n(p) / [((1-p)/(p√π)) n^{-3/2} (4p(1-p))^n]` tends to
`1` uniformly in `p ∈ (0,1)`. -/
theorem catalan_tendstoUniformlyOn_ratio :
    TendstoUniformlyOn (fun (n : ℕ) (p : ℝ) =>
      (catalan n : ℝ) / 4 ^ n * ((1 - p) / p) * (4 * p * (1 - p)) ^ n /
        ((1 - p) / (p * √π) * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (4 * p * (1 - p)) ^ n))
      (fun _ => 1) atTop (Set.Ioo 0 1) := by
  have h := catalan_tendsto_ratio
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.1 h ε hε] with n hn p hp
  rw [catalan_ratio_eq hp.1 hp.2 n, dist_comm]
  simpa using hn

/-- `|log (1 - x) + x| ≤ 2 x²` for `0 ≤ x ≤ 1/2`. -/
theorem abs_log_one_sub_add_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [abs_of_nonneg hx0]; linarith) 1
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one, abs_of_nonneg hx0] at h
  rw [add_comm]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith), show x ^ (1 + 1) = x ^ 2 by norm_num]
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]

/-- **Near-critical point mass.** If `p_n = 1/2 + ε_n` with `ε_n → 0` and
`n ε_n⁴ → 0`, then `a_n(p_n) ~ n^{-3/2} e^{-4 n ε_n²}/√π`. -/
theorem catalan_nearCritical_isEquivalent (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hε4 : Tendsto (fun n : ℕ => (n : ℝ) * ε n ^ 4) atTop (𝓝 0)) :
    (fun n : ℕ => (catalan n : ℝ) / 4 ^ n * ((1 - (1 / 2 + ε n)) / (1 / 2 + ε n)) *
        (4 * (1 / 2 + ε n) * (1 - (1 / 2 + ε n))) ^ n) ~[atTop]
      fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) * Real.exp (-4 * n * ε n ^ 2) / √π := by
  -- the three factors of the ratio
  have hA := catalan_tendsto_ratio
  have hB : Tendsto (fun n => (1 - (1 / 2 + ε n)) / (1 / 2 + ε n)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n => 1 - (1 / 2 + ε n)) atTop (𝓝 (1 - (1 / 2 + 0))) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.add hε)
    have h2 : Tendsto (fun n => 1 / 2 + ε n) atTop (𝓝 (1 / 2 + 0)) :=
      tendsto_const_nhds.add hε
    have := h1.div h2 (by norm_num)
    norm_num at this
    exact this
  -- `x_n = 4 ε_n²`
  have hx : Tendsto (fun n => 4 * ε n ^ 2) atTop (𝓝 0) := by
    have := (hε.pow 2).const_mul 4
    simpa using this
  have hC : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (Real.log (1 - 4 * ε n ^ 2) +
      4 * ε n ^ 2))) atTop (𝓝 1) := by
    have hbound : ∀ᶠ n : ℕ in atTop, |(n : ℝ) * (Real.log (1 - 4 * ε n ^ 2) + 4 * ε n ^ 2)| ≤
        32 * ((n : ℝ) * ε n ^ 4) := by
      filter_upwards [hx.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
      have h := abs_log_one_sub_add_le (x := 4 * ε n ^ 2) (by positivity) hn
      rw [abs_mul, Nat.abs_cast]
      calc (n : ℝ) * |Real.log (1 - 4 * ε n ^ 2) + 4 * ε n ^ 2| ≤ n * (2 * (4 * ε n ^ 2) ^ 2) :=
            mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
        _ = 32 * ((n : ℝ) * ε n ^ 4) := by ring
    have h32 := hε4.const_mul 32
    rw [mul_zero] at h32
    have h0 := (Real.continuous_exp.tendsto 0).comp (squeeze_zero_norm' hbound h32)
    rw [Real.exp_zero] at h0
    exact h0
  refine isEquivalent_of_tendsto_one ?_
  have hlim := (hA.mul hB).mul hC
  rw [one_mul, one_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [hx.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 1, hε.eventually (Ioo_mem_nhds (show (-(1 / 2) : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 / 2 by norm_num))]
    with n hn hn1 hεn
  have hεn' := hεn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hp : 0 < 1 / 2 + ε n := by linarith
  have hq : 0 < 1 - (1 / 2 + ε n) := by linarith
  have h4 : 4 * (1 / 2 + ε n) * (1 - (1 / 2 + ε n)) = 1 - 4 * ε n ^ 2 := by ring
  have h4pos : 0 < 1 - 4 * ε n ^ 2 := by linarith
  have hr : 0 < (n : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hn0 _
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hexp : (1 - 4 * ε n ^ 2) ^ n =
      Real.exp ((n : ℝ) * (Real.log (1 - 4 * ε n ^ 2) + 4 * ε n ^ 2)) *
        Real.exp (-4 * n * ε n ^ 2) := by
    rw [← Real.exp_add, ← Real.rpow_natCast, Real.rpow_def_of_pos h4pos]
    congr 1
    ring
  simp only [Pi.div_apply]
  rw [h4, hexp]
  have he : 0 < Real.exp (-4 * n * ε n ^ 2) := Real.exp_pos _
  field_simp

/-! ### Item 4: the rooted binary tree at `p = 1/2` -/

section Tree

open MeasureTheory PercLib.Percolation.Bond

/-- At `p = 1/2` the Catalan law is `Cat(n)/4^n`. -/
theorem binaryTree_law_card_eq_half (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    law q {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite} =
      ENNReal.ofReal ((catalan n : ℝ) / 4 ^ n) := by
  rw [binaryTree_law_cluster_card_eq p q hq hn, hp]
  congr 1
  have h := succ_mul_catalan_eq_centralBinom n
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((n : ℝ) + 1) * catalan n = ((2 * n).choose n : ℝ) := by exact_mod_cast h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← h', show m + 1 - 1 = m by omega]
  field_simp
  ring_nf
  rw [mul_assoc, show ((1 : ℝ) / 2) ^ (m * 2) * 4 ^ m = 1 by rw [pow_mul', ← mul_pow]; norm_num,
    mul_one]

/-- **Critical point mass on the binary tree.** At `p = 1/2`,
`P(|K([])| = n, K([]) finite) ~ n^{-3/2}/√π`. -/
theorem binaryTree_law_card_isEquivalent (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) :
    (fun n : ℕ => (law q {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal)
      ~[atTop] fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) / √π := by
  refine IsEquivalent.congr_left catalan_div_four_pow_isEquivalent ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [binaryTree_law_card_eq_half p q hq hp hn, ENNReal.toReal_ofReal (by positivity)]

/-- The volume tail at `p = 1/2`, exactly: `P(|K([])| ≥ n) = 2 C(2n,n)/4^n` for `n ≥ 1`
(the infinite cluster has probability `0`). -/
theorem binaryTree_law_le_encard_eq (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    law q {ω | (n : ℕ∞) ≤ (cluster ω []).encard} =
      ENNReal.ofReal (2 * ((n.centralBinom : ℝ) / 4 ^ n)) := by
  have hθ := binaryTree_theta_of_le p q hq (by rw [hp])
  have hsplit : {ω : Config (List (Fin 2)) | (n : ℕ∞) ≤ (cluster ω []).encard} =
      {ω | (cluster ω []).Infinite} ∪
        ⋃ k : ℕ, {ω | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro h
      by_cases hfin : (cluster ω []).Finite
      · right
        rw [hfin.encard_eq_coe_toFinset_card] at h ⊢
        refine ⟨hfin.toFinset.card - n, ?_⟩
        have : n ≤ hfin.toFinset.card := by exact_mod_cast h
        congr 1
        omega
      · exact Or.inl hfin
    · rintro (h | ⟨k, hk⟩)
      · rw [Set.Infinite.encard_eq h]
        exact le_top
      · rw [hk]
        exact_mod_cast Nat.le_add_left n k
  have hmeas : ∀ k : ℕ, MeasurableSet
      {ω : Config (List (Fin 2)) | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)} :=
    fun k => measurable_encard_cluster [] (measurableSet_singleton _)
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ =>
      {ω : Config (List (Fin 2)) | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)}) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => hij ?_
    simp only [Set.mem_ofPred_eq] at hi hj
    rw [hi] at hj
    have := Nat.cast_injective (R := ℕ∞) hj
    omega
  have hk : ∀ k : ℕ, law q {ω | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)} =
      ENNReal.ofReal ((catalan (k + n) : ℝ) / 4 ^ (k + n)) := by
    intro k
    rw [← binaryTree_law_card_eq_half p q hq hp (by omega : 1 ≤ k + n)]
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      have hfin : (cluster ω []).Finite := Set.finite_of_encard_eq_coe h
      exact ⟨by rw [← hfin.cast_ncard_eq] at h; exact_mod_cast h, hfin⟩
    · rintro ⟨h, hfin⟩
      rw [← hfin.cast_ncard_eq, h]
  rw [hsplit]
  refine le_antisymm ?_ ?_
  · calc law q ({ω | (cluster ω []).Infinite} ∪
          ⋃ k : ℕ, {ω | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)})
        ≤ law q {ω | (cluster ω []).Infinite} +
            law q (⋃ k : ℕ, {ω | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)}) :=
          measure_union_le _ _
      _ = ∑' k : ℕ, ENNReal.ofReal ((catalan (k + n) : ℝ) / 4 ^ (k + n)) := by
          rw [hθ, zero_add, measure_iUnion hdisj hmeas]
          simp_rw [hk]
      _ = _ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (hasSum_catalan_div_four_pow_tail n).summable, tsum_catalan_div_four_pow_tail]
  · calc ENNReal.ofReal (2 * ((n.centralBinom : ℝ) / 4 ^ n))
        = ∑' k : ℕ, ENNReal.ofReal ((catalan (k + n) : ℝ) / 4 ^ (k + n)) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (hasSum_catalan_div_four_pow_tail n).summable, tsum_catalan_div_four_pow_tail]
      _ = law q (⋃ k : ℕ, {ω | (cluster ω []).encard = ((k + n : ℕ) : ℕ∞)}) := by
          rw [measure_iUnion hdisj hmeas]
          simp_rw [hk]
      _ ≤ _ := measure_mono Set.subset_union_right

/-- **Critical tail on the binary tree.** At `p = 1/2`, `P(|K([])| ≥ n) ~ 2 n^{-1/2}/√π`. -/
theorem binaryTree_law_le_encard_isEquivalent (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) :
    (fun n : ℕ => (law q {ω | (n : ℕ∞) ≤ (cluster ω []).encard}).toReal)
      ~[atTop] fun n : ℕ => 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) / √π := by
  refine IsEquivalent.congr_left catalan_critical_tail_isEquivalent ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [binaryTree_law_le_encard_eq p q hq hp hn, ENNReal.toReal_ofReal (by positivity),
    ← tsum_catalan_div_four_pow_tail n]
  exact tsum_congr fun k => by norm_num

/-- The closed-form Catalan expression of the asymptotic theorems is the Catalan law:
`Cat(n)/4^n · (1-p)/p · (4p(1-p))^n = Cat(n) p^(n-1) (1-p)^(n+1)` for `p ≠ 0`, `n ≥ 1`. -/
theorem catalan_div_four_pow_mul_eq {p : ℝ} (hp : p ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    (catalan n : ℝ) / 4 ^ n * ((1 - p) / p) * (4 * p * (1 - p)) ^ n =
      (catalan n : ℝ) * p ^ (n - 1) * (1 - p) ^ (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, show 4 * p * (1 - p) = 4 * (p * (1 - p)) by ring,
    mul_pow, mul_pow]
  field_simp
  ring

/-- **Uniform asymptotics.** For a family of tree profiles `q p` with parameter `p`,
`P_p(|K| = n) ~ (1-p)/(p√π) n^{-3/2} (4p(1-p))^n` uniformly in `p ∈ (0,1)`. -/
theorem binaryTree_law_card_tendstoUniformlyOn
    (q : unitInterval → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ p e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    TendstoUniformlyOn (fun (n : ℕ) (p : unitInterval) =>
      (law (q p) {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal /
        ((1 - (p : ℝ)) / ((p : ℝ) * √π) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n))
      (fun _ => 1) atTop {p : unitInterval | (p : ℝ) ∈ Set.Ioo 0 1} := by
  have h := catalan_tendstoUniformlyOn_ratio.comp (fun p : unitInterval => (p : ℝ))
  refine h.congr (eventually_atTop.2 ⟨1, fun n hn p hp => ?_⟩)
  have hp0 : (p : ℝ) ≠ 0 := hp.1.ne'
  simp only [Function.comp_apply]
  rw [binaryTree_law_cluster_card_toReal p (q p) (hq p) hn, catalan_div_four_pow_mul_eq hp0 hn]

/-- **Exact ratio.** For `0 < p < 1` and `n ≥ 1`, the ratio of `P_p(|K| = n)` to
`(1-p)/(p√π) n^{-3/2} (4p(1-p))^n` equals `(Cat(n)/4^n) / (n^{-3/2}/√π)`, a function of `n`
alone. -/
theorem binaryTree_law_card_ratio_eq (q : unitInterval → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ p e, ¬ e.IsDiag → q p e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p else 0)
    {p : unitInterval} (hp : (p : ℝ) ∈ Set.Ioo 0 1) {n : ℕ} (hn : 1 ≤ n) :
    (law (q p) {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal /
        ((1 - (p : ℝ)) / ((p : ℝ) * √π) * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
          (4 * (p : ℝ) * (1 - (p : ℝ))) ^ n) =
      (catalan n : ℝ) / 4 ^ n / ((n : ℝ) ^ (-(3 / 2 : ℝ)) / √π) := by
  rw [binaryTree_law_cluster_card_toReal p (q p) (hq p) hn,
    ← catalan_div_four_pow_mul_eq hp.1.ne' hn, catalan_ratio_eq hp.1 hp.2 n]

/-- **Near-critical window.** If `p_n = 1/2 + ε_n` with `ε_n → 0` and `n ε_n⁴ → 0`,
then `P_{p_n}(|K| = n) ~ n^{-3/2} e^{-4nε_n²}/√π`. -/
theorem binaryTree_law_card_nearCritical_isEquivalent (pn : ℕ → unitInterval)
    (q : ℕ → Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ n e, ¬ e.IsDiag → q n e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then pn n
        else 0)
    (h1 : Tendsto (fun n => (pn n : ℝ) - 1 / 2) atTop (𝓝 0))
    (h2 : Tendsto (fun n : ℕ => (n : ℝ) * ((pn n : ℝ) - 1 / 2) ^ 4) atTop (𝓝 0)) :
    (fun n : ℕ => (law (q n) {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}).toReal)
      ~[atTop] (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-4 * n * ((pn n : ℝ) - 1 / 2) ^ 2) / √π) := by
  have h := catalan_nearCritical_isEquivalent (fun n => (pn n : ℝ) - 1 / 2) h1 h2
  refine h.congr_left ?_
  have hev := h1.eventually (Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hp0 : (pn n : ℝ) ≠ 0 := by
    have := hn.1
    intro h0
    rw [h0] at this
    norm_num at this
  simp only [add_sub_cancel]
  rw [binaryTree_law_cluster_card_toReal (pn n) (q n) (hq n) hn1,
    catalan_div_four_pow_mul_eq hp0 hn1]

end Tree

/-! ### Non-vacuity -/

/-- Non-vacuity: `a_0 = 1`, `a_1 = 1/4`, `a_2 = 1/8` at `p = 1/2`
(`a_n(1/2) = Cat(n)/4^n`; `a_0` is the formal value at `n = 0`, not a cluster size). -/
example : (catalan 0 : ℝ) / 4 ^ 0 * ((1 - 1 / 2) / (1 / 2)) * (4 * (1 / 2) * (1 - 1 / 2)) ^ 0 = 1 ∧
    (catalan 1 : ℝ) / 4 ^ 1 * ((1 - 1 / 2) / (1 / 2)) * (4 * (1 / 2) * (1 - 1 / 2)) ^ 1 = 1 / 4 ∧
    (catalan 2 : ℝ) / 4 ^ 2 * ((1 - 1 / 2) / (1 / 2)) * (4 * (1 / 2) * (1 - 1 / 2)) ^ 2 =
      1 / 8 := by
  simp [catalan_zero, catalan_one, catalan_two]
  norm_num

/-- Non-vacuity: `ε_n = n^{-1/3}` satisfies `ε_n → 0` and `n ε_n⁴ → 0`. -/
example : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 4) atTop (𝓝 0) := by
  constructor
  · exact (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  · refine ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp
      tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply]
    calc (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ ((1 : ℝ) + (-(1 / 3 : ℝ)) * (4 : ℕ)) := by norm_num
      _ = _ := by rw [Real.rpow_add hn0, Real.rpow_one, Real.rpow_mul hn0.le, Real.rpow_natCast]

end PercLib.Models
