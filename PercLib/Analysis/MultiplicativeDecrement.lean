/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
Mathematical reference: T. Hutchcroft, *Critical cluster volumes in hierarchical
percolation*, arXiv:2211.05686v1, Lemma 6.4 (proved here by a difference argument instead
of an integral comparison).
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import PercLib.Meta.Tag

/-!
# A small multiplicative decrement determines a polynomial amplitude

Let `a_n > 0`, `B > 0`, `γ > 0` and `a_{n+1} = a_n exp(-(B + ε_n) a_n^γ)` with `ε_n → 0`.
Then `a_n ∼ (γ B n)^{-1/γ}`. The proof works with `b_n = a_n^{-γ}`, whose increments
`b_{n+1} - b_n = (exp(γ(B + ε_n) a_n^γ) - 1) / a_n^γ` tend to `γ B`.

## Main results

* `le_exp_mul_sub_one_div`, `exp_mul_sub_one_div_le`: `c ≤ (e^{cx} - 1)/x ≤ c e^{cx}` for
  `x > 0`.
* `tendsto_div_natCast_of_tendsto_sub`: if `b_{n+1} - b_n → l` then `b_n / n → l`.
* `tendsto_atTop_of_tendsto_sub`: if moreover `l > 0` then `b_n → ∞`.
* `isEquivalent_rpow_of_eq_mul_exp`: the asymptotics `a_n ∼ (γ B n)^{-1/γ}`.

No definition is introduced.
-/

@[expose] public section
noncomputable section

open Filter Finset Asymptotics
open scoped Topology

namespace PercLib.Analysis

/-- `c ≤ (e^{cx} - 1) / x` for `x > 0`. -/
theorem le_exp_mul_sub_one_div (c : ℝ) {x : ℝ} (hx : 0 < x) :
    c ≤ (Real.exp (c * x) - 1) / x := by
  rw [le_div_iff₀ hx]
  linarith [Real.add_one_le_exp (c * x)]

/-- `(e^{cx} - 1) / x ≤ c e^{cx}` for `x > 0`. -/
theorem exp_mul_sub_one_div_le (c : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.exp (c * x) - 1) / x ≤ c * Real.exp (c * x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(c * x)))
    (Real.exp_pos (c * x)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  rw [div_le_iff₀ hx]
  linarith [show c * Real.exp (c * x) * x = c * x * Real.exp (c * x) by ring]

/-- If `b_{n+1} - b_n → l` then `b_n / n → l`. -/
theorem tendsto_div_natCast_of_tendsto_sub {b : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n => b (n + 1) - b n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => b n / n) atTop (𝓝 l) := by
  have hc := h.cesaro
  have htel : ∀ n : ℕ, ∑ i ∈ range n, (b (i + 1) - b i) = b n - b 0 :=
    fun n => sum_range_sub b n
  simp_rw [htel] at hc
  have h0 : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * b 0) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (b 0)
  have := hc.add h0
  rw [add_zero] at this
  refine this.congr fun n => ?_
  rw [div_eq_inv_mul]
  ring

/-- If `b_{n+1} - b_n → l > 0` then `b_n → ∞`. -/
theorem tendsto_atTop_of_tendsto_sub {b : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (h : Tendsto (fun n => b (n + 1) - b n) atTop (𝓝 l)) : Tendsto b atTop atTop := by
  have := (tendsto_div_natCast_of_tendsto_sub h).pos_mul_atTop hl
    (tendsto_natCast_atTop_atTop (R := ℝ))
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp

/-- **A small multiplicative decrement determines a polynomial amplitude.** If `a_n > 0`,
`B > 0`, `γ > 0`, `ε_n → 0` and `a_{n+1} = a_n exp(-(B + ε_n) a_n^γ)`, then
`a_n ∼ (γ B n)^{-1/γ}`. -/
@[tag "S23T"]
theorem isEquivalent_rpow_of_eq_mul_exp {a ε : ℕ → ℝ} {B γ : ℝ} (ha : ∀ n, 0 < a n)
    (hB : 0 < B) (hγ : 0 < γ) (hε : Tendsto ε atTop (𝓝 0))
    (hrec : ∀ n, a (n + 1) = a n * Real.exp (-(B + ε n) * a n ^ γ)) :
    a ~[atTop] fun n : ℕ => (γ * B * n) ^ (-1 / γ) := by
  have hxpos : ∀ n, 0 < a n ^ γ := fun n => Real.rpow_pos_of_pos (ha n) γ
  have hγB : 0 < γ * B := mul_pos hγ hB
  -- increments of `b_n = (a_n^γ)⁻¹`
  have hd : ∀ n, (a (n + 1) ^ γ)⁻¹ - (a n ^ γ)⁻¹ =
      (Real.exp (γ * (B + ε n) * a n ^ γ) - 1) / a n ^ γ := by
    intro n
    rw [hrec n, Real.mul_rpow (ha n).le (Real.exp_pos _).le, ← Real.exp_mul, mul_inv,
      ← Real.exp_neg, show -(-(B + ε n) * a n ^ γ * γ) = γ * (B + ε n) * a n ^ γ by ring]
    have := (hxpos n).ne'
    field_simp
  have hc : Tendsto (fun n => γ * (B + ε n)) atTop (𝓝 (γ * B)) := by
    simpa using (hε.const_add B).const_mul γ
  -- `b_n → ∞`, by comparison with `b_0 + ∑_{i<n} γ (B + ε_i)`
  have hlow : ∀ n, (a 0 ^ γ)⁻¹ + ∑ i ∈ range n, γ * (B + ε i) ≤ (a n ^ γ)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have h1 := hd n
      have h2 := le_exp_mul_sub_one_div (γ * (B + ε n)) (hxpos n)
      linarith
  have hlowtop : Tendsto (fun n => (a 0 ^ γ)⁻¹ + ∑ i ∈ range n, γ * (B + ε i)) atTop atTop :=
    tendsto_atTop_of_tendsto_sub hγB (by simpa [sum_range_succ] using hc)
  have hbtop : Tendsto (fun n => (a n ^ γ)⁻¹) atTop atTop := tendsto_atTop_mono hlow hlowtop
  have hx0 : Tendsto (fun n => a n ^ γ) atTop (𝓝 0) := by
    refine hbtop.inv_tendsto_atTop.congr fun n => ?_
    simp
  -- the increments tend to `γ B`
  have hdlim : Tendsto (fun n => (a (n + 1) ^ γ)⁻¹ - (a n ^ γ)⁻¹) atTop (𝓝 (γ * B)) := by
    simp_rw [hd]
    have hup : Tendsto (fun n => γ * (B + ε n) * Real.exp (γ * (B + ε n) * a n ^ γ)) atTop
        (𝓝 (γ * B)) := by
      simpa using hc.mul (Real.continuous_exp.continuousAt.tendsto.comp (hc.mul hx0))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hc hup
      (fun n => le_exp_mul_sub_one_div _ (hxpos n)) (fun n => exp_mul_sub_one_div_le _ (hxpos n))
  have hbdiv := tendsto_div_natCast_of_tendsto_sub (b := fun n => (a n ^ γ)⁻¹) hdlim
  -- the ratio
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun n : ℕ => ((a n ^ γ)⁻¹ / n / (γ * B)) ^ (-1 / γ)) atTop (𝓝 1) := by
    have := (hbdiv.div_const (γ * B)).rpow_const (p := -1 / γ) (Or.inl (by simp [hγB.ne']))
    simpa [div_self hγB.ne'] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hinv : ((a n ^ γ)⁻¹) ^ (-1 / γ) = a n := by
    rw [Real.inv_rpow (hxpos n).le, ← Real.rpow_mul (ha n).le,
      show γ * (-1 / γ) = -1 by field_simp, Real.rpow_neg_one, inv_inv]
  rw [div_div, mul_comm (n : ℝ), Real.div_rpow (inv_pos.2 (hxpos n)).le
    (mul_pos hγB hn').le, hinv]
  rfl

end PercLib.Analysis
