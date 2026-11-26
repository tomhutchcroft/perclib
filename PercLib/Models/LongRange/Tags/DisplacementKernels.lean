/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for the displacement-kernel assertions on `ℤ^d` and `ℤ`.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.PowerLaw
public import PercLib.Models.LongRange.CutPoints
public import PercLib.Percolation.Bond.Diagonal.Probability

/-!
# Displacement kernels: correspondence

Wiki correspondence for the power-law kernel on `ℤ^d`, sup-norm ball counts and cut probabilities on
`ℤ`.

## Main results

* `powerLaw_kernel_properties`
* `supNorm_ball_sphere_counts`
* `law_cut_eq_tprod_and_pos_iff`
-/

@[expose] public section
noncomputable section
open MeasureTheory PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- The power-law kernel `‖z‖_∞^{-(d+α)}` off the origin on `ℤ^d` (`d ≥ 1`) is nonnegative
and even, has finite mass exactly when `α > 0` (infinite mass for `α ≤ 0`), and for `α > 0`
its tail beyond `r ≥ 1` is at most `2d·3^{d-1}(1 + 1/α) r^{-α}`. -/
@[tag "6VNM"]
theorem powerLaw_kernel_properties {d : ℕ} (hd : 1 ≤ d) (α : ℝ) :
    (∀ z : Fin d → ℤ, 0 ≤ (if z = 0 then (0:ℝ) else ‖z‖ ^ (-((d:ℝ)+α)))) ∧
    (∀ z : Fin d → ℤ, (if -z = 0 then (0:ℝ) else ‖-z‖ ^ (-((d:ℝ)+α))) =
                      (if z = 0 then (0:ℝ) else ‖z‖ ^ (-((d:ℝ)+α)))) ∧
    (∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d:ℝ)+α))) < ∞ ↔ 0 < α) ∧
    (α ≤ 0 → ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d:ℝ)+α))) = ∞) ∧
    (0 < α → ∀ r : ℝ, 1 ≤ r →
      ∑' z : Fin d → ℤ, ENNReal.ofReal (if r ≤ ‖z‖ then ‖z‖ ^ (-((d:ℝ)+α)) else 0) ≤
        ENNReal.ofReal ((2 * d * 3 ^ (d - 1) : ℕ) * ((1 + 1/α) * r ^ (-α)))) :=
  ⟨powerLaw_nonneg _, powerLaw_neg _, tsum_ofReal_powerLaw_lt_top_iff hd α,
    fun h => tsum_ofReal_powerLaw_eq_top hd h, fun h _ hr => tsum_ofReal_powerLaw_tail_le hd h hr⟩

/-- Sup-norm balls and spheres in `ℤ^d`: the ball of radius `n` has `(2n+1)^d` points, the
sphere of radius `0` one point and of radius `n ≥ 1` exactly `(2n+1)^d - (2n-1)^d` points,
between `2d(2n-1)^{d-1}` and `2d(2n+1)^{d-1}`; radial sums are shell sums, and for `d ≥ 1`
they compare with `∑ n^{d-1} g(n)` up to the factor `2d·3^{d-1}`. -/
@[tag "FQCZ"]
theorem supNorm_ball_sphere_counts :
    (∀ d n : ℕ, Nat.card {z : Fin d → ℤ // ‖z‖ ≤ n} = (2*n+1)^d) ∧
    (∀ d : ℕ, Nat.card {z : Fin d → ℤ // ‖z‖ = 0} = 1) ∧
    (∀ d n : ℕ, 1 ≤ n → Nat.card {z : Fin d → ℤ // ‖z‖ = n} = (2*n+1)^d - (2*n-1)^d) ∧
    (∀ d n : ℕ, 1 ≤ d → 1 ≤ n →
      2*d*(2*n-1)^(d-1) ≤ Nat.card {z : Fin d → ℤ // ‖z‖ = n} ∧
      Nat.card {z : Fin d → ℤ // ‖z‖ = n} ≤ 2*d*(2*n+1)^(d-1)) ∧
    (∀ d (g : ℕ → ℝ≥0∞), ∑' z : Fin d → ℤ, g ⌊‖z‖⌋₊ =
        ∑' n : ℕ, (Nat.card {z : Fin d → ℤ // ‖z‖ = n} : ℝ≥0∞) * g n) ∧
    (∀ d (g : ℕ → ℝ≥0∞), 1 ≤ d → g 0 = 0 →
      ∑' n : ℕ, ((n ^ (d - 1) : ℕ) : ℝ≥0∞) * g n ≤ ∑' z : Fin d → ℤ, g ⌊‖z‖⌋₊ ∧
      ∑' z : Fin d → ℤ, g ⌊‖z‖⌋₊ ≤
        ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) * ∑' n : ℕ, ((n ^ (d - 1) : ℕ) : ℝ≥0∞) * g n) := by
  refine ⟨card_norm_le, fun d => ?_, fun d n hn => card_norm_eq d hn,
    fun d n hd hn => card_norm_eq_bounds hd hn, fun d g => tsum_comp_floor_norm g,
    fun d g hd hg => tsum_comp_floor_norm_bounds hd g hg⟩
  have h := card_norm_le d 0
  simp only [Nat.cast_zero, mul_zero, zero_add, one_pow] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun z =>
    ⟨fun hz => hz.le, fun hz => le_antisymm hz (norm_nonneg z)⟩)

/-- Cut probabilities on `ℤ` for a distance profile `p` off the diagonal (the diagonal is
arbitrary): the probability that no open bond crosses the gap after `j` is
`∏_n (1 - p_n)^n`, and it is positive exactly when `p_n < 1` for every `n ≥ 1` and
`∑ n p_n < ∞`. -/
@[tag "BQ44"]
theorem law_cut_eq_tprod_and_pos_iff (p : ℕ → unitInterval) (q : Sym2 ℤ → unitInterval)
    (hq : ∀ a b, a ≠ b → q s(a, b) = p (Int.natAbs (b - a))) (j : ℤ) :
    law q {ω | IsCut ω j} =
        ∏' n : ℕ, (unitInterval.toNNReal (unitInterval.symm (p n)) : ℝ≥0∞) ^ n ∧
    (0 < law q {ω | IsCut ω j} ↔
        (∀ n, 1 ≤ n → p n < 1) ∧ Summable fun n : ℕ => (n : ℝ) * (p n : ℝ)) := by
  classical
  set q' : Sym2 ℤ → unitInterval := fun e => if e.IsDiag then p 0 else q e with hq'def
  have hq' : ∀ a b, q' s(a, b) = p (Int.natAbs (b - a)) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp [q']
    · simp only [q', Sym2.mk_isDiag_iff, hab, ite_false]
      exact hq a b hab
  have hlaw : law q {ω | IsCut ω j} = law q' {ω | IsCut ω j} := by
    refine law_event_eq_of_offDiagonal q q' (fun e he => ?_) (measurableSet_setOf_isCut j) ?_
    · simp [q', he]
    · intro ω ω' h
      have key : ∀ a b : ℤ, a ≤ j → j < b → (s(a, b) ∈ ω ↔ s(a, b) ∈ ω') := by
        intro a b ha hb
        have hnd : ¬ (s(a, b) : Sym2 ℤ).IsDiag := by
          rw [Sym2.mk_isDiag_iff]; omega
        have h1 : s(a, b) ∈ ω \ Sym2.diagSet ↔ s(a, b) ∈ ω' \ Sym2.diagSet := by rw [h]
        simpa [Set.mem_sdiff, Sym2.mem_diagSet, hnd] using h1
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun H a b ha hb hm => H a b ha hb ((key a b ha hb).2 hm),
        fun H a b ha hb hm => H a b ha hb ((key a b ha hb).1 hm)⟩
  rw [hlaw]
  refine ⟨law_cut_eq_tprod p q' hq' j, ⟨fun hpos => ⟨fun n hn => ?_, ?_⟩,
    fun ⟨hlt, hsum⟩ => law_cut_pos p q' hq' hsum hlt j⟩⟩
  · by_contra hge
    have hp1 : p n = 1 := le_antisymm (unitInterval.le_one (p n)) (not_lt.1 hge)
    rw [law_cut_eq_zero_of_certain_length p q' hq' (by omega) hp1 j] at hpos
    exact lt_irrefl _ hpos
  · by_contra hns
    rw [law_cut_eq_zero_of_not_summable p q' hq' hns j] at hpos
    exact lt_irrefl _ hpos

end PercLib.Models.LongRange
