/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
-/
module

public import PercLib.Analysis.Elementary
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pointwise lower bounds from an integrated square-root lower bound

Let `(p n)_{n ≥ 1}` be nonnegative and nonincreasing, with partial sums
`∑_{j=1}^N p j ≥ c √N` for `N ≥ N₀` and the pointwise upper bound
`p n ≤ C n^{-1/2} log^a (e n)`. Then `p n ≥ c' n^{-1/2} log^{-a} (e n)` for `n ≥ N₀`, with
`c' > 0` depending only on `c, C, a`.

The proof compares the partial sum up to `N = ⌈A n log^{2a}(e n)⌉`, where `c √A ≥ 4 C`, with
the upper bound below `n` (through `∑_{j ≤ n} j^{-1/2} ≤ 2 √n`) and with `p n` above `n`.

## Main results

* `exists_pos_le_of_sqrt_le_sum_of_le_rpow_log`: the pointwise lower bound, with the constant
  `c'` chosen before the sequence.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open Finset

namespace PercLib.Analysis

/-- If `p ≥ 0` is nonincreasing on `n ≥ 1`, `∑_{j=1}^N p j ≥ c √N` for `N ≥ N₀ ≥ 1`, and
`p n ≤ C n^{-1/2} log^a (e n)` for `n ≥ 1`, then `p n ≥ c' n^{-1/2} log^{-a} (e n)` for
`n ≥ N₀`, where `c' > 0` depends only on `c`, `C` and `a`. -/
theorem exists_pos_le_of_sqrt_le_sum_of_le_rpow_log {c C a : ℝ} (hc : 0 < c) (hC : 0 < C)
    (ha : 0 ≤ a) :
    ∃ c' > 0, ∀ (p : ℕ → ℝ) (N₀ : ℕ), 1 ≤ N₀ → (∀ n, 1 ≤ n → 0 ≤ p n) →
      AntitoneOn p (Set.Ici 1) →
      (∀ N, N₀ ≤ N → c * Real.sqrt N ≤ ∑ j ∈ Finset.Icc 1 N, p j) →
      (∀ n, 1 ≤ n → p n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (Real.exp 1 * n) ^ a) →
      ∀ n, N₀ ≤ n →
        c' * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (Real.exp 1 * n) ^ a)⁻¹ ≤ p n := by
  set A : ℝ := max 2 ((4 * C / c) ^ 2) with hAdef
  have hA2 : 2 ≤ A := le_max_left _ _
  have hA0 : 0 < A := by linarith
  have hAc : 4 * C ≤ c * Real.sqrt A := by
    have h1 : 4 * C / c ≤ Real.sqrt A := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 4 * C / c)]
      exact Real.sqrt_le_sqrt (le_max_right _ _)
    rw [div_le_iff₀ hc] at h1
    linarith
  have hA1 : 0 < Real.sqrt (A + 1) := Real.sqrt_pos.2 (by linarith)
  refine ⟨c / (2 * Real.sqrt (A + 1)), by positivity, ?_⟩
  intro p N₀ hN₀ hp0 hanti hsum hup n hn
  have hn1 : 1 ≤ n := hN₀.trans hn
  -- notation: `x = n`, `M = log^a (e n)`
  set x : ℝ := (n : ℝ) with hxdef
  have hx1 : (1 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hn1
  have hx0 : 0 < x := by linarith
  -- the logarithm is at least one, and monotone in `j ≤ n`
  have hlog_ge : ∀ j : ℕ, 1 ≤ j → 1 ≤ Real.log (Real.exp 1 * j) := by
    intro j hj
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hj']
  set M : ℝ := Real.log (Real.exp 1 * x) ^ a with hMdef
  have hM1 : 1 ≤ M := Real.one_le_rpow (hlog_ge n hn1) ha
  have hM0 : 0 < M := by linarith
  have hlogM : ∀ j : ℕ, 1 ≤ j → j ≤ n → Real.log (Real.exp 1 * j) ^ a ≤ M := by
    intro j hj hjn
    have hj' : (0 : ℝ) < j := by exact_mod_cast hj
    refine Real.rpow_le_rpow (by linarith [hlog_ge j hj]) ?_ ha
    refine Real.log_le_log (by positivity) ?_
    have : (j : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hjn
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos 1).le
  have hrpow : ∀ y : ℝ, 0 < y → y ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt y := by
    intro y hy
    simp [Real.rpow_neg hy.le, Real.sqrt_eq_rpow]
  -- the comparison scale `N`
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈A * x * M ^ 2⌉₊ := ⟨_, rfl⟩
  have hxM : 1 ≤ x * M ^ 2 := by nlinarith
  have hN1 : A * x * M ^ 2 ≤ N := hNdef ▸ Nat.le_ceil _
  have hN2 : (N : ℝ) ≤ (A + 1) * x * M ^ 2 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ A * x * M ^ 2)
    rw [← hNdef] at this
    nlinarith
  have hnN : n ≤ N := by
    have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
    have h1 : x ≤ x * M ^ 2 := le_mul_of_one_le_right hx0.le hM2
    have h2 : x * M ^ 2 ≤ A * x * M ^ 2 := by
      rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) (by linarith)
    have : (n : ℝ) ≤ N := by rw [← hxdef]; linarith
    exact_mod_cast this
  -- the partial-sum bound
  have hsplit : ∑ j ∈ Icc 1 N, p j = ∑ j ∈ Icc 1 n, p j + ∑ j ∈ Ioc n N, p j := by
    have e : ∀ k : ℕ, Icc 1 k = Ioc 0 k := fun k => by
      simpa using Finset.Icc_add_one_left_eq_Ioc 0 k
    rw [e, e]
    exact (Finset.sum_Ioc_consecutive p (Nat.zero_le n) hnN).symm
  have hlow : ∑ j ∈ Icc 1 n, p j ≤ 2 * C * M * Real.sqrt x := by
    calc ∑ j ∈ Icc 1 n, p j ≤ ∑ j ∈ Icc 1 n, C * M * (1 / Real.sqrt j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hj
          have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
          refine (hup j hj1).trans ?_
          rw [hrpow _ hj0]
          have : 0 ≤ C * (1 / Real.sqrt j) := by positivity
          nlinarith [hlogM j hj1 hjn]
      _ = C * M * ∑ j ∈ Icc 1 n, 1 / Real.sqrt j := by rw [Finset.mul_sum]
      _ ≤ C * M * (2 * Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (sum_Icc_one_div_sqrt_le_two_mul n) (by positivity)
      _ = 2 * C * M * Real.sqrt x := by ring
  have hhigh : ∑ j ∈ Ioc n N, p j ≤ N * p n := by
    calc ∑ j ∈ Ioc n N, p j ≤ (Ioc n N).card • p n := by
          refine Finset.sum_le_card_nsmul _ _ _ fun j hj => ?_
          have hj := (Finset.mem_Ioc.1 hj).1
          exact hanti (Set.mem_Ici.2 hn1) (Set.mem_Ici.2 (by omega)) hj.le
      _ = ((N - n : ℕ) : ℝ) * p n := by rw [Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ N * p n := by
          refine mul_le_mul_of_nonneg_right ?_ (hp0 n hn1)
          exact_mod_cast Nat.sub_le N n
  have hmain : c * Real.sqrt N ≤ 2 * C * M * Real.sqrt x + N * p n := by
    have := hsum N (hn.trans hnN)
    linarith
  -- square roots of the two bounds on `N`
  set t : ℝ := Real.sqrt N with htdef
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have ht_lo : Real.sqrt A * Real.sqrt x * M ≤ t := by
    have : Real.sqrt (A * x * M ^ 2) = Real.sqrt A * Real.sqrt x * M := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hA0.le, Real.sqrt_sq hM0.le]
    rw [← this]
    exact Real.sqrt_le_sqrt hN1
  have ht_hi : t ≤ Real.sqrt (A + 1) * Real.sqrt x * M := by
    have : Real.sqrt ((A + 1) * x * M ^ 2) = Real.sqrt (A + 1) * Real.sqrt x * M := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by linarith), Real.sqrt_sq hM0.le]
    rw [← this]
    exact Real.sqrt_le_sqrt hN2
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht_lo
  have htt : t * t = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  -- `c/2 ≤ t p n`
  have hkey : c / 2 ≤ t * p n := by
    have h1 : 2 * C * M * Real.sqrt x ≤ c / 2 * t := by
      have : 0 ≤ M * Real.sqrt x := by positivity
      nlinarith
    have h3 : (N : ℝ) * p n = t * (t * p n) := by rw [← htt]; ring
    have h2 : t * (c / 2) ≤ t * (t * p n) := by linarith
    exact le_of_mul_le_mul_left h2 ht0
  -- conclusion
  rw [hrpow x hx0]
  have hden : 0 < 2 * Real.sqrt (A + 1) * Real.sqrt x * M := by positivity
  calc c / (2 * Real.sqrt (A + 1)) * (1 / Real.sqrt x) * M⁻¹
      = c / (2 * Real.sqrt (A + 1) * Real.sqrt x * M) := by field_simp
    _ ≤ c / (2 * t) := by
        refine div_le_div_of_nonneg_left hc.le (by linarith) ?_
        linarith
    _ ≤ p n := by
        rw [div_le_iff₀ (by linarith)]
        linarith

end PercLib.Analysis

end
