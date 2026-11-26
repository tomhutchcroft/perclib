/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The Erdős–Rényi critical-window parametrisation. New definition; no upstream code is copied.
Mathematical reference: B. Bollobás, *Random Graphs* (2nd ed., 2001), Ch. 6; T. Łuczak,
"Component behavior near the critical point of the random graph process" (1990).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Erdős–Rényi critical window

`erdosRenyiWindow n λ = 1/n + λ n^{-4/3}` is the edge probability of `G(n, p)` inside the
critical window, with window parameter `λ ∈ ℝ` held fixed as `n → ∞`.

## Main definitions

* `erdosRenyiWindow n λ`

## Main results

* `natCast_mul_erdosRenyiWindow`: `n p = 1 + λ n^{-1/3}` for `n ≠ 0`.
* `tendsto_natCast_mul_erdosRenyiWindow`: `n p → 1`.
* `eventually_erdosRenyiWindow_mem_Icc`: for fixed `λ`, `p ∈ [0, 1]` for all large `n`.
* `erdosRenyiWindow_sub_inv_mul_rpow`: `(p - 1/n) n^{4/3} = λ` for `n ≠ 0`.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace PercLib.Models

/-- The critical-window edge probability `1/n + λ n^{-4/3}` of the Erdős–Rényi graph. -/
def erdosRenyiWindow (n : ℕ) (t : ℝ) : ℝ := 1 / n + t * (n : ℝ) ^ (-(4 / 3 : ℝ))

theorem erdosRenyiWindow_def (n : ℕ) (t : ℝ) :
    erdosRenyiWindow n t = 1 / n + t * (n : ℝ) ^ (-(4 / 3 : ℝ)) := rfl

@[simp]
theorem erdosRenyiWindow_zero_right (n : ℕ) : erdosRenyiWindow n 0 = 1 / n := by
  simp [erdosRenyiWindow]

/-- Monotone in the window parameter. -/
theorem erdosRenyiWindow_mono (n : ℕ) : Monotone (erdosRenyiWindow n) := by
  intro a b hab
  have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) (-(4 / 3 : ℝ))
  simp only [erdosRenyiWindow]
  nlinarith

/-- `n p = 1 + λ n^{-1/3}`. -/
theorem natCast_mul_erdosRenyiWindow {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℝ) * erdosRenyiWindow n t = 1 + t * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h : (n : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hpos]
    norm_num
  rw [erdosRenyiWindow, mul_add, mul_one_div_cancel hpos.ne', mul_left_comm, h]

/-- `(p - 1/n) n^{4/3} = λ`. -/
theorem erdosRenyiWindow_sub_inv_mul_rpow {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (erdosRenyiWindow n t - 1 / n) * (n : ℝ) ^ (4 / 3 : ℝ) = t := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [erdosRenyiWindow, add_sub_cancel_left, mul_assoc, ← Real.rpow_add hpos]
  norm_num

/-- `n p → 1` for fixed `λ`. -/
theorem tendsto_natCast_mul_erdosRenyiWindow (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * erdosRenyiWindow n t) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => 1 + t * (n : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 1) := by
    simpa using (h0.const_mul t).const_add 1
  refine h1.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (natCast_mul_erdosRenyiWindow hn t).symm

/-- For fixed `λ`, the window probability lies in `[0, 1]` for all large `n`. -/
theorem eventually_erdosRenyiWindow_mem_Icc (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, erdosRenyiWindow n t ∈ Set.Icc (0 : ℝ) 1 := by
  have h := (tendsto_natCast_mul_erdosRenyiWindow t).eventually
    (Ioo_mem_nhds (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num))
  filter_upwards [h, eventually_ge_atTop 2] with n hn hn2
  have hpos : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  obtain ⟨h0, h2⟩ := hn
  constructor
  · nlinarith
  · nlinarith

end PercLib.Models
