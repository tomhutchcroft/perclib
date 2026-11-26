/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from the source repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc, files `PercLib/CriticalLRP/Tightness/MomentRatioAux.lean`
and `PercLib/CriticalLRP/Tightness/TailEstimates.lean`, contributed by `yujinhkim`. Licence:
Apache-2.0, as declared in those files' headers and in `third_party/critical-lrp/NOTICE.md` of that
commit (upstream origin `yujinhkim/Critical-Long-range-percolation` at
3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf, not independently verified). Changes: namespace
`PercLib.Probability`; `ofReal_mul_meas_le_lintegral` is not ported (it is mathlib's
`mul_meas_ge_le_lintegral₀` at `ε = ofReal a`), and `ofReal_pow_mul_meas_le_lintegral` is reproved
from that lemma; focused imports; `autoImplicit` off.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Elementary power, Markov and geometric-tail inequalities

Ingredients of the moment-ratio consequence (Corollary I.2.5) of universal tightness in
Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.

* `pow_succ_sub_pow_le_real`, `pow_succ_sub_pow_le`, `pow_sub_pow_ge`: mean-value bounds
  `(n+1)^{p-1} ≤ (n+1)^p − n^p ≤ p (n+1)^{p−1}`.
* `ofReal_pow_mul_meas_le_lintegral`: `M^p μ{M ≤ X} ≤ ∫⁻ X^p`.
* `tsum_exp_neg_succ_le`: `∑ₙ e^{−(n+1)c} ≤ 2/c` for `0 < c ≤ 1`, and
  `tsum_pow_mul_exp_neg_succ_le`: `∑ₙ (n+1)^j e^{−(n+1)c} ≤ 2^j j! c^{−j} (4/c)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Probability


/-! ### Mean-value bounds for powers -/

lemma pow_succ_sub_pow_le_real (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (x + 1) ^ k - x ^ k ≤ (k : ℝ) * (x + 1) ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hkey : (x + 1) ^ (k + 1) - x ^ (k + 1) = ((x + 1) ^ k - x ^ k) * (x + 1) + x ^ k := by
      ring
    rw [hkey]
    have hx1 : (0 : ℝ) ≤ x + 1 := by linarith
    have h1 : ((x + 1) ^ k - x ^ k) * (x + 1) ≤ ((k : ℝ) * (x + 1) ^ (k - 1)) * (x + 1) :=
      mul_le_mul_of_nonneg_right ih hx1
    have h2 : ((k : ℝ) * (x + 1) ^ (k - 1)) * (x + 1) = (k : ℝ) * (x + 1) ^ k := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    have h3 : x ^ k ≤ (x + 1) ^ k := pow_le_pow_left₀ hx (by linarith) k
    have h4 : ((k : ℝ) + 1) * (x + 1) ^ k = (k : ℝ) * (x + 1) ^ k + (x + 1) ^ k := by ring
    push_cast
    nlinarith [h1, h2, h3, h4]

/-- Mean-value bound in `ℝ≥0∞`: `(n+1)^k - n^k ≤ k (n+1)^{k-1}`. -/
lemma pow_succ_sub_pow_le (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k ≤ (k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1) := by
  have hcast1 : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
    norm_num
  have hcast2 : ((n : ℝ≥0∞)) = ENNReal.ofReal ((n : ℝ)) := (ENNReal.ofReal_natCast n).symm
  have hreal := pow_succ_sub_pow_le_real ((n : ℝ)) (by positivity) k hk
  have hL : ((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k
      = ENNReal.ofReal (((n : ℝ) + 1) ^ k - (n : ℝ) ^ k) := by
    rw [hcast1, hcast2, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1),
      ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (n:ℝ)),
      ← ENNReal.ofReal_sub _ (pow_nonneg (by positivity) k)]
  rw [hL]
  calc ENNReal.ofReal (((n : ℝ) + 1) ^ k - (n : ℝ) ^ k)
      ≤ ENNReal.ofReal ((k : ℝ) * ((n : ℝ) + 1) ^ (k - 1)) := ENNReal.ofReal_le_ofReal hreal
    _ = (k : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) ^ (k - 1) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (n:ℝ) + 1), hcast1.symm]

/-- `(n+1)^{p-1} ≤ (n+1)^p - n^p` for `p ≥ 1`. -/
lemma pow_sub_pow_ge (p : ℕ) (hp : 1 ≤ p) (n : ℕ) :
    ((n : ℝ≥0∞) + 1) ^ (p - 1) ≤ ((n : ℝ≥0∞) + 1) ^ p - (n : ℝ≥0∞) ^ p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  have hnat : (n + 1) ^ j + n ^ (j + 1) ≤ (n + 1) ^ (j + 1) := by
    have h1 : n ^ (j + 1) ≤ (n + 1) ^ j * n := by
      rw [pow_succ]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ n) j)
    have h2 : (n + 1) ^ (j + 1) = (n + 1) ^ j * n + (n + 1) ^ j := by
      rw [pow_succ, show n + 1 = Nat.succ n from rfl, Nat.mul_succ]
    rw [h2]
    omega
  have hcast1 : ((n : ℝ≥0∞) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hadd : ((n : ℝ≥0∞) + 1) ^ j + (n : ℝ≥0∞) ^ (j + 1) ≤ ((n : ℝ≥0∞) + 1) ^ (j + 1) := by
    rw [hcast1, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, Nat.cast_le]
    exact hnat
  exact ENNReal.le_sub_of_add_le_right (by simp) hadd

/-! ### Measure bounds -/

/-- Power form: `M^p * μ {M ≤ X} ≤ ∫⁻ X^p` for `M ≥ 0`. -/
lemma ofReal_pow_mul_meas_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ≥0∞} (hX : Measurable X)
    {M : ℝ} (_hM : 0 ≤ M) (p : ℕ) :
    ENNReal.ofReal M ^ p * μ {ω | ENNReal.ofReal M ≤ X ω} ≤ ∫⁻ ω, X ω ^ p ∂μ := by
  calc ENNReal.ofReal M ^ p * μ {ω | ENNReal.ofReal M ≤ X ω}
      ≤ ENNReal.ofReal M ^ p * μ {ω | ENNReal.ofReal M ^ p ≤ X ω ^ p} := by
        exact mul_le_mul_right (measure_mono fun ω (h : ENNReal.ofReal M ≤ X ω) =>
          (pow_le_pow_left' h p : ENNReal.ofReal M ^ p ≤ X ω ^ p)) _
    _ ≤ ∫⁻ ω, X ω ^ p ∂μ := mul_meas_ge_le_lintegral₀ (hX.pow_const p).aemeasurable _

/-- `(n : ℝ≥0∞) * ofReal x = ofReal (n * x)` for `x ≥ 0`. -/
lemma natCast_mul_ofReal (n : ℕ) {x : ℝ} (_hx : 0 ≤ x) :
    (n : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x) := by
  nth_rewrite 1 [← ENNReal.ofReal_natCast n]
  rw [← ENNReal.ofReal_mul (by positivity)]

/-! ### Two elementary real bounds -/

/-- `x ^ j ≤ 2 ^ j * j! * exp (x/2)` for `x ≥ 0` (Taylor's theorem at `x/2`). -/
lemma pow_le_two_pow_mul_factorial_exp {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x ^ j ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (x / 2) := by
  have hfac : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (x / 2) (by positivity) j
  have h1 : (x / 2) ^ j ≤ (j.factorial : ℝ) * Real.exp (x / 2) := by
    rw [div_le_iff₀ hfac] at h
    linarith
  calc x ^ j = (2 * (x / 2)) ^ j := by ring_nf
    _ = 2 ^ j * (x / 2) ^ j := by rw [mul_pow]
    _ ≤ 2 ^ j * ((j.factorial : ℝ) * Real.exp (x / 2)) := by gcongr
    _ = 2 ^ j * (j.factorial : ℝ) * Real.exp (x / 2) := by ring

/-- `u/2 ≤ 1 - e^{-u}` for `0 < u ≤ 1`. -/
lemma half_le_one_sub_exp_neg {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have hexp : (1 : ℝ) + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h1 : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, show (Real.exp u)⁻¹ = 1 / Real.exp u from by ring]
    exact one_div_le_one_div_of_le hpos hexp
  have h2 : 1 / (1 + u) ≤ 1 - u / 2 := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

/-- `x^j * e^{-x} ≤ 2^j j! e^{-x/2}` for `x ≥ 0`. -/
lemma pow_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x ^ j * Real.exp (-x) ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(x / 2)) := by
  have h := pow_le_two_pow_mul_factorial_exp hx j
  have h2 : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc x ^ j * Real.exp (-x)
      ≤ (2 ^ j * (j.factorial : ℝ) * Real.exp (x / 2)) * Real.exp (-x) := by gcongr
    _ = 2 ^ j * (j.factorial : ℝ) * (Real.exp (x / 2) * Real.exp (-x)) := by ring
    _ = 2 ^ j * (j.factorial : ℝ) * Real.exp (-(x / 2)) := by rw [h2]

/-! ### The geometric-majorant series bound in `ℝ≥0∞` -/

/-- `∑_{n} e^{-(n+1)c} ≤ 2/c` in `ℝ≥0∞` for `0 < c ≤ 1`. -/
lemma tsum_exp_neg_succ_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
      ≤ ENNReal.ofReal (2 / c) := by
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-c)) with hr
  have hterm : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))) = r ^ (n + 1) := by
    intro n
    rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring_nf
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hbound : ENNReal.ofReal (c / 2) ≤ 1 - r := by
    rw [hr, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (p := 1) (q := Real.exp (-c)) (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (half_le_one_sub_exp_neg hc0 hc1)
  have hinv : (1 - r)⁻¹ ≤ ENNReal.ofReal (2 / c) := by
    rw [show ENNReal.ofReal (2 / c) = (ENNReal.ofReal (c / 2))⁻¹ from by
      rw [show (2 : ℝ) / c = (c / 2)⁻¹ from by field_simp]
      exact ENNReal.ofReal_inv_of_pos (by positivity)]
    exact ENNReal.inv_le_inv.mpr hbound
  calc (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
      = ∑' n : ℕ, r ^ (n + 1) := by simp only [hterm]
    _ = r * (1 - r)⁻¹ := ENNReal.tsum_geometric_add_one r
    _ ≤ 1 * (1 - r)⁻¹ := by gcongr
    _ = (1 - r)⁻¹ := one_mul _
    _ ≤ ENNReal.ofReal (2 / c) := hinv

/-- `∑_{n} (n+1)^j e^{-(n+1)c} ≤ 2^j j! c^{-j} · (4/c)` in `ℝ≥0∞` for `0 < c ≤ 1`. -/
theorem tsum_pow_mul_exp_neg_succ_le (j : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ j * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c)))))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j * (4 / c)) := by
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(c / 2))) with hr
  have hstep : ∀ n : ℕ, (((n : ℝ≥0∞) + 1) ^ j *
        ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * r ^ (n + 1) := by
    intro n
    have hx : (0 : ℝ) ≤ ((n : ℝ) + 1) * c := by positivity
    have hscal : (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)))
        ≤ (2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j * Real.exp (-(((n : ℝ) + 1) * c / 2)) := by
      have h1 := pow_mul_exp_neg_le hx j
      have hcpos : (0 : ℝ) < c ^ j := by positivity
      have h3 : (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)))
          ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(((n : ℝ) + 1) * c / 2)) / c ^ j := by
        rw [le_div_iff₀ hcpos]
        calc ((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)) * c ^ j
            = (((n : ℝ) + 1) * c) ^ j * Real.exp (-(((n : ℝ) + 1) * c)) := by
              rw [mul_pow]; ring
          _ ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(((n : ℝ) + 1) * c / 2)) := h1
      calc ((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c))
          ≤ 2 ^ j * (j.factorial : ℝ) * Real.exp (-(((n : ℝ) + 1) * c / 2)) / c ^ j := h3
        _ = 2 ^ j * (j.factorial : ℝ) * c⁻¹ ^ j
              * Real.exp (-(((n : ℝ) + 1) * c / 2)) := by
            rw [inv_pow, div_eq_mul_inv]
            ring
    have hcastR : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    have hcast : (((n : ℝ≥0∞) + 1) ^ j * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c))))
        = ENNReal.ofReal (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), hcastR]
    rw [hcast]
    calc ENNReal.ofReal (((n : ℝ) + 1) ^ j * Real.exp (-(((n : ℝ) + 1) * c)))
        ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j
            * Real.exp (-(((n : ℝ) + 1) * c / 2))) := ENNReal.ofReal_le_ofReal hscal
      _ = ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * r ^ (n + 1) := by
          rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
            ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring_nf
  calc (∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ j * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * c)))))
      ≤ ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * r ^ (n + 1) :=
        ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) *
          ∑' n : ℕ, r ^ (n + 1) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j) * ENNReal.ofReal (4 / c) := by
        have hgeom : (∑' n : ℕ, r ^ (n + 1))
            = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * (c / 2)))) := by
          refine tsum_congr fun n => ?_
          rw [hr, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring_nf
        rw [hgeom]
        have hhalf := tsum_exp_neg_succ_le (c := c / 2) (by positivity) (by linarith)
        rw [show (2 : ℝ) / (c / 2) = 4 / c from by field_simp; norm_num] at hhalf
        exact mul_le_mul_right hhalf _
    _ = ENNReal.ofReal ((2 : ℝ) ^ j * (j.factorial : ℝ) * c⁻¹ ^ j * (4 / c)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]

/-! ### Non-vacuity witness: `c = 1` satisfies `0 < c ≤ 1` -/

example : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * 1)))) ≤ ENNReal.ofReal (2 / 1)
    ∧ (∑' n : ℕ, (((n : ℝ≥0∞) + 1) ^ 2 * ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * 1)))))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ 2 * ((2).factorial : ℝ) * 1⁻¹ ^ 2 * (4 / 1)) :=
  ⟨tsum_exp_neg_succ_le one_pos le_rfl, tsum_pow_mul_exp_neg_succ_le 2 one_pos le_rfl⟩

end PercLib.Probability
