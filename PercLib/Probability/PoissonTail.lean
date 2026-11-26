/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Analytic properties of the Poisson tail and the Poisson limit of binomial tails. New for this
project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is
copied. The termwise binomial-to-Poisson limit is mathlib's
`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`. Mathematical reference:
W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1, Chapter VI.
-/
module

public import PercLib.Probability.PoissonTail.Defs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
public import Mathlib.Basic.ENNReal.Real

/-!
# The Poisson tail

For `j ≥ 1`, `Q_j(x) = 1 - e^{-x} ∑_{i < j} x^i / i!` is continuous, has derivative
`e^{-x} x^{j-1} / (j-1)!`, and is a strictly increasing bijection from `[0, ∞)` onto `[0, 1)`.
With `Q_j(∞) = 1`, every `p ∈ [0, 1]` is `Q_j(λ)` for a unique `λ ∈ [0, ∞]`. If `n p_n → λ`,
the tail `P(Bin(n, p_n) ≥ j)` tends to `Q_j(λ)`.

## Main results

* `PercLib.hasDerivAt_poissonTail_succ`: the derivative of `Q_{n+1}`.
* `PercLib.strictMonoOn_poissonTail`, `PercLib.bijOn_poissonTail`: strict monotonicity on
  `[0, ∞)` and bijectivity onto `[0, 1)`.
* `PercLib.existsUnique_eq_poissonTail_ennreal`: the unique extended parameter.
* `PercLib.tendsto_binomial_real_Ici_poissonTail`: Poisson limit of binomial tails, and
  `PercLib.tendsto_binomial_real_Ici_poissonTail_of_eventually_eq_div` for `p_N = λ / N`.
-/

@[expose] public section

open Finset Real Filter Topology MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal

namespace PercLib

theorem continuous_poissonTail (j : ℕ) : Continuous (poissonTail j) := by
  unfold poissonTail
  fun_prop

/-- The derivative of `Q_{n+1}` is `e^{-x} x^n / n!`. -/
theorem hasDerivAt_poissonTail_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (poissonTail (n + 1)) (exp (-x) * x ^ n / n.factorial) x := by
  have hexp : HasDerivAt (fun y ↦ exp (-y)) (-exp (-x)) x := by
    convert (hasDerivAt_neg x).exp using 1
    ring
  induction n with
  | zero =>
    have h : poissonTail 1 = fun y ↦ 1 - exp (-y) := funext poissonTail_one
    rw [h]
    convert hexp.const_sub (1 : ℝ) using 1
    simp
  | succ n ih =>
    have h : poissonTail (n + 1 + 1) =
        fun y ↦ poissonTail (n + 1) y - exp (-y) * y ^ (n + 1) / (n + 1).factorial :=
      funext (poissonTail_succ (n + 1))
    rw [h]
    have hg := (hexp.mul (hasDerivAt_pow (n + 1) x)).div_const ((n + 1).factorial : ℝ)
    convert ih.sub hg using 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

/-- `Q_j` is strictly increasing on `[0, ∞)` for `j ≥ 1`. -/
theorem strictMonoOn_poissonTail {j : ℕ} (hj : 1 ≤ j) :
    StrictMonoOn (poissonTail j) (Set.Ici 0) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_poissonTail _).continuousOn
    fun x hx ↦ ?_
  rw [interior_Ici, Set.mem_Ioi] at hx
  rw [(hasDerivAt_poissonTail_succ n x).deriv]
  positivity

/-- `Q_j(x) → 1` as `x → ∞`. -/
theorem tendsto_poissonTail_atTop (j : ℕ) : Tendsto (poissonTail j) atTop (𝓝 1) := by
  have h : Tendsto (fun x ↦ exp (-x) * ∑ i ∈ range j, x ^ i / i.factorial) atTop (𝓝 0) := by
    simp_rw [mul_sum]
    rw [← sum_const_zero (s := range j)]
    refine tendsto_finsetSum _ fun i _ ↦ ?_
    have := (tendsto_pow_mul_exp_neg_atTop_nhds_zero i).div_const (i.factorial : ℝ)
    rw [zero_div] at this
    exact this.congr fun x ↦ by ring
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [sub_zero] at h1
  exact h1.congr fun x ↦ (poissonTail_def j x).symm

/-- For `j ≥ 1`, `Q_j` is a bijection from `[0, ∞)` onto `[0, 1)`. -/
theorem bijOn_poissonTail {j : ℕ} (hj : 1 ≤ j) :
    Set.BijOn (poissonTail j) (Set.Ici 0) (Set.Ico 0 1) := by
  have hmono := strictMonoOn_poissonTail hj
  refine ⟨fun x hx ↦ ⟨?_, poissonTail_lt_one hj hx⟩, hmono.injOn, fun p hp ↦ ?_⟩
  · rw [← poissonTail_zero_right hj]
    exact hmono.monotoneOn Set.self_mem_Ici hx hx
  · obtain ⟨M, hM⟩ := ((tendsto_poissonTail_atTop j).eventually
      (eventually_gt_nhds hp.2)).exists_forall_of_atTop
    have hM0 : 0 ≤ max M 0 := le_max_right _ _
    have hIVT := intermediate_value_Icc hM0 (continuous_poissonTail j).continuousOn
    rw [poissonTail_zero_right hj] at hIVT
    obtain ⟨x, hx, hxp⟩ := hIVT ⟨hp.1, (hM _ (le_max_left _ _)).le⟩
    exact ⟨x, hx.1, hxp⟩

/-- **The extended parameter.** With `Q_j(∞) = 1`, every `p ∈ [0, 1]` equals `Q_j(λ)` for a
unique `λ ∈ [0, ∞]`. -/
theorem existsUnique_eq_poissonTail_ennreal {j : ℕ} (hj : 1 ≤ j) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∃! l : ℝ≥0∞, p = if l = ⊤ then 1 else poissonTail j l.toReal := by
  rcases hp.2.lt_or_eq with hp1 | rfl
  · obtain ⟨x, hx, hxp⟩ := (bijOn_poissonTail hj).surjOn ⟨hp.1, hp1⟩
    refine ⟨ENNReal.ofReal x, ?_, fun l hl ↦ ?_⟩
    · simp [ENNReal.toReal_ofReal (Set.mem_Ici.1 hx), hxp]
    · by_cases hlt : l = ⊤
      · simp only [hlt, ↓reduceIte] at hl
        exact absurd hl hp1.ne
      · simp only [hlt, ↓reduceIte] at hl
        have hinj := (strictMonoOn_poissonTail hj).injOn (Set.mem_Ici.2 ENNReal.toReal_nonneg) hx
          (hl.symm.trans hxp.symm)
        rw [← hinj, ENNReal.ofReal_toReal hlt]
  · refine ⟨⊤, by simp, fun l hl ↦ ?_⟩
    by_contra hlt
    simp only [hlt, ↓reduceIte] at hl
    exact (poissonTail_lt_one hj ENNReal.toReal_nonneg).ne hl.symm

/-- **Poisson limit of binomial tails.** If `n p_n → r`, then
`P(Bin(n, p_n) ≥ j) → Q_j(r)`. -/
theorem tendsto_binomial_real_Ici_poissonTail {p : ℕ → I} {r : ℝ}
    (hr : Tendsto (fun n : ℕ ↦ n * (p n : ℝ)) atTop (𝓝 r)) (j : ℕ) :
    Tendsto (fun n ↦ (binomial n (p n)).real (Set.Ici j)) atTop (𝓝 (poissonTail j r)) := by
  have hset : Set.Ici j = ((range j : Finset ℕ) : Set ℕ)ᶜ := by
    ext k
    simp
  have h : ∀ n, (binomial n (p n)).real (Set.Ici j) =
      1 - ∑ i ∈ range j, (n.choose i : ℝ) * (p n : ℝ) ^ i * (1 - (p n : ℝ)) ^ (n - i) := by
    intro n
    rw [hset, probReal_compl_eq_one_sub (Finset.measurableSet _),
      ← sum_measureReal_singleton]
    simp only [binomial_real_singleton]
  simp_rw [h]
  rw [poissonTail, mul_sum]
  refine (tendsto_const_nhds).sub (tendsto_finsetSum _ fun i _ ↦ ?_)
  have := tendsto_choose_mul_pow_of_tendsto_mul_atTop (p := fun n ↦ (p n : ℝ)) i hr
  simpa only [mul_div_assoc] using this

/-- **Poisson limit for `N` routes of success probability `λ / N`.** If `p_N = λ / N` for all
large `N`, then `P(Bin(N, p_N) ≥ j) → Q_j(λ)`. -/
theorem tendsto_binomial_real_Ici_poissonTail_of_eventually_eq_div {p : ℕ → I} {r : ℝ}
    (hp : ∀ᶠ n in atTop, (p n : ℝ) = r / n) (j : ℕ) :
    Tendsto (fun n ↦ (binomial n (p n)).real (Set.Ici j)) atTop (𝓝 (poissonTail j r)) := by
  refine tendsto_binomial_real_Ici_poissonTail (tendsto_const_nhds.congr' ?_) j
  filter_upwards [hp, eventually_ge_atTop 1] with n hn hn1
  rw [hn]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

end PercLib
