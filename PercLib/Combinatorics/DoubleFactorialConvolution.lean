/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Ported on 2026-11-16 from the work of contributor yujinhkim: source repository `yujinhkim/lrp`,
branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/Lemma_I_4_23.lean` and
`PercLib/CriticalLRP/VolumeMoments/DFactorial.lean`; licence Apache-2.0, as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`. Upstream origin
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not
independently verified). Source of the mathematics: T. Hutchcroft, *Critical long-range percolation
I*, arXiv:2508.18807v1, Lemma I.4.23, p. 49.

Changes from the source: focused imports instead of `import Mathlib`; no `autoImplicit` and no
disabled linters; the namespace is `PercLib.Combinatorics`; the source's helper definitions
`dd`, `S`, `U`, `T` (and `VolumeMoments.M`) are not introduced. The proof follows the source's
two steps (Pascal's rule, then the summand identity), stated for any sequence `d` with
`d 0 = 1` and `d (n+1) = (2n+1) d n` and then specialised to `d m = (2m-1)‼`.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Ring

/-! # A double-factorial convolution (Lemma I.4.23)

For `n ≥ 1`, `∑_{k<n} C(n,k) (2k-1)‼ (2n-2k-3)‼ = (2n-1)‼` in `ℕ`, with the convention
`(-1)‼ = 1` (which is `0‼` under truncated subtraction) (`lemma_I_4_23`).

Writing `S n = ∑_{k<n} C(n,k) d_k d_{n-1-k}` for a sequence with `d₀ = 1` and
`d_{n+1} = (2n+1) d_n`, Pascal's rule and `d_{n-k} + d_{k+1}`-splitting give
`S (n+1) = 2n S n + d_n` (`sum_choose_succ_eq`), whence `S n = d_n` for `n ≥ 1`
(`sum_choose_eq`).

This differs from `PercLib.Percolation.Bond.sum_choose_doubleFactorial`, whose second factor
is `(2(n-k)-1)‼`.
-/

@[expose] public section

open scoped Nat
open Finset

namespace PercLib.Combinatorics

/-- `(2(n+1)-1)‼ = (2n+1) (2n-1)‼`. -/
theorem doubleFactorial_two_mul_succ_sub_one (n : ℕ) :
    (2 * (n + 1) - 1)‼ = (2 * n + 1) * (2 * n - 1)‼ := by
  rcases n with _ | m
  · simp
  · have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have h2 : 2 * (m + 1 + 1) - 1 = 2 * m + 1 + 2 := by omega
    have h3 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
    rw [h1, h2, Nat.doubleFactorial_add_two, h3]

section Sequence

variable (d : ℕ → ℕ) (hd : ∀ n, d (n + 1) = (2 * n + 1) * d n)
include hd

/-- The summand identity: `C(n,k) d_k d_{n-k} + C(n,k) d_{k+1} d_{n-1-k} =
2n C(n,k) d_k d_{n-1-k}` for `k < n`. -/
theorem choose_mul_add_choose_mul (n k : ℕ) (hk : k < n) :
    n.choose k * d k * d (n - k) + n.choose k * d (k + 1) * d (n - 1 - k) =
      2 * n * (n.choose k * d k * d (n - 1 - k)) := by
  have h1 : d (n - k) = (2 * (n - 1 - k) + 1) * d (n - 1 - k) := by
    rw [show n - k = (n - 1 - k) + 1 by omega, hd]
  have h3 : 2 * (n - 1 - k) + 1 + (2 * k + 1) = 2 * n := by omega
  rw [h1, hd k]
  calc n.choose k * d k * ((2 * (n - 1 - k) + 1) * d (n - 1 - k))
        + n.choose k * ((2 * k + 1) * d k) * d (n - 1 - k)
      = n.choose k * d k * d (n - 1 - k) * (2 * (n - 1 - k) + 1 + (2 * k + 1)) := by ring
    _ = 2 * n * (n.choose k * d k * d (n - 1 - k)) := by rw [h3]; ring

/-- **Recursion.** With `d 0 = 1`,
`∑_{k<n+1} C(n+1,k) d_k d_{n-k} = 2n ∑_{k<n} C(n,k) d_k d_{n-1-k} + d_n`. -/
theorem sum_choose_succ_eq (hd0 : d 0 = 1) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n + 1).choose k * d k * d (n + 1 - 1 - k) =
      2 * n * ∑ k ∈ range n, n.choose k * d k * d (n - 1 - k) + d n := by
  -- peel off `k = 0` and reindex
  have hpeel : ∑ k ∈ range (n + 1), (n + 1).choose k * d k * d (n + 1 - 1 - k) =
      (∑ k ∈ range n, (n + 1).choose (k + 1) * d (k + 1) * d (n - 1 - k)) + d n := by
    rw [sum_range_succ']
    have hsum : ∀ k ∈ range n, (n + 1).choose (k + 1) * d (k + 1) * d (n + 1 - 1 - (k + 1)) =
        (n + 1).choose (k + 1) * d (k + 1) * d (n - 1 - k) := fun k _ => by
      rw [show n + 1 - 1 - (k + 1) = n - 1 - k by omega]
    rw [sum_congr rfl hsum, show n + 1 - 1 - 0 = n by omega, Nat.choose_zero_right, hd0]
    ring
  -- Pascal's rule
  have hsplit : (∑ k ∈ range n, (n + 1).choose (k + 1) * d (k + 1) * d (n - 1 - k)) =
      (∑ k ∈ range n, n.choose k * d (k + 1) * d (n - 1 - k)) +
        ∑ k ∈ range n, n.choose (k + 1) * d (k + 1) * d (n - 1 - k) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.choose_succ_succ]
    ring
  -- the full convolution, written two ways
  have hU1 : ∑ k ∈ range (n + 1), n.choose k * d k * d (n - k) =
      (∑ k ∈ range n, n.choose (k + 1) * d (k + 1) * d (n - 1 - k)) + d n := by
    rw [sum_range_succ']
    have hsum : ∀ k ∈ range n, n.choose (k + 1) * d (k + 1) * d (n - (k + 1)) =
        n.choose (k + 1) * d (k + 1) * d (n - 1 - k) := fun k _ => by
      rw [show n - (k + 1) = n - 1 - k by omega]
    rw [sum_congr rfl hsum, Nat.choose_zero_right, hd0, Nat.sub_zero]
    ring
  have hU2 : ∑ k ∈ range (n + 1), n.choose k * d k * d (n - k) =
      d n + ∑ k ∈ range n, n.choose k * d k * d (n - k) := by
    rw [sum_range_succ, Nat.choose_self, Nat.sub_self, hd0]
    ring
  have hkey : (∑ k ∈ range n, n.choose k * d k * d (n - k)) +
      ∑ k ∈ range n, n.choose k * d (k + 1) * d (n - 1 - k) =
        2 * n * ∑ k ∈ range n, n.choose k * d k * d (n - 1 - k) := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun k hk => choose_mul_add_choose_mul d hd n k (mem_range.1 hk)
  omega

/-- For `n ≥ 1`, `∑_{k<n} C(n,k) d_k d_{n-1-k} = d_n`. -/
theorem sum_choose_eq (hd0 : d 0 = 1) (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, n.choose k * d k * d (n - 1 - k) = d n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => simp [hd0, hd 0]
  | succ m ih =>
    rw [sum_choose_succ_eq d hd hd0 (m + 1), ih (by omega), hd (m + 1)]
    ring

end Sequence

/-- **Lemma I.4.23** (Hutchcroft, arXiv:2508.18807v1, p. 49). For every `n ≥ 1`,
`∑_{k<n} C(n,k) (2k-1)‼ (2n-2k-3)‼ = (2n-1)‼`. (The paper states `n ≥ 2`; at `n = 1` both
sides are `1`.) -/
theorem lemma_I_4_23 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ range n, n.choose k * (2 * k - 1)‼ * (2 * n - 2 * k - 3)‼ = (2 * n - 1)‼ := by
  have h := sum_choose_eq (fun m => (2 * m - 1)‼) doubleFactorial_two_mul_succ_sub_one
    (by simp) n hn
  rw [← h]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := mem_range.1 hk
  rw [show 2 * n - 2 * k - 3 = 2 * (n - 1 - k) - 1 by omega]

/-- **Sanity check** at `n = 3`: `1·1·3 + 3·1·1 + 3·3·1 = 15 = 5‼`. -/
theorem lemma_I_4_23_three :
    ∑ k ∈ range 3, (3 : ℕ).choose k * (2 * k - 1)‼ * (2 * 3 - 2 * k - 3)‼ = (2 * 3 - 1)‼ :=
  lemma_I_4_23 3 (by norm_num)

end PercLib.Combinatorics
