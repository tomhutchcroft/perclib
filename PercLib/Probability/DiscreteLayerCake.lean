/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Ported on 2026-11-16 from the work of contributor yujinhkim: source repository `yujinhkim/lrp`,
branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Tightness/DiscreteLayerCake.lean`; licence Apache-2.0, as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`. Upstream origin
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not
independently verified). Source of the mathematics: T. Hutchcroft, *Critical long-range percolation
I*, arXiv:2508.18807v1, proof of Corollary I.2.5.

Changes from the source: focused imports instead of `import Mathlib`; no `autoImplicit` and no
disabled linters; the namespace is `PercLib.Probability`; the helper definition `ind s` and its
three lemmas are replaced by `s.indicator (fun _ => 1)` and mathlib's
`lintegral_indicator_one`; the cast helpers `cast_min_nat` and `cast_sum_nat` are replaced by
mathlib's `Monotone.map_min` and `Nat.cast_sum`. The file adds no definition.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Discrete layer cake for `ℕ∞`-valued variables

For `X : Ω → ℝ≥0∞` measurable whose values are `⊤` or natural numbers:

* `lintegral_eq_tsum_meas_ge`: `∫⁻ X = ∑' n, μ {n + 1 ≤ X}`;
* `lintegral_pow_eq_tsum_meas_ge` (`k ≥ 1`): `∫⁻ X^k = ∑' n, ((n+1)^k - n^k) μ {n + 1 ≤ X}`.

Both follow from the truncation identities `min X n = ∑_{j<n} 1{j+1 ≤ X}` (`min_eq_sum_ite`) and
`(min X n)^k = ∑_{j<n} ((j+1)^k - j^k) 1{j+1 ≤ X}` (`min_pow_eq_sum_ite`) and monotone
convergence (`iSup_min_eq_self`, `iSup_min_pow_eq_self`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Cast and counting helpers for `ℝ≥0∞` -/

lemma filter_range_succ_le (m n : ℕ) :
    (Finset.range n).filter (fun j => j + 1 ≤ m) = Finset.range (min m n) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The telescoping sum `∑_{j<n} ((j+1)^k - j^k) = n^k` in `ℝ≥0∞`, for `k ≥ 1`. -/
lemma sum_range_pow_sub (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    ∑ j ∈ Finset.range n, (((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) = (n : ℝ≥0∞) ^ k := by
  induction n with
  | zero => simp [zero_pow (by omega : k ≠ 0)]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      show ((n + 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 by push_cast; ring,
      add_tsub_cancel_of_le (pow_le_pow_left' (le_add_right (le_refl (n : ℝ≥0∞))) k)]

/-! ### The truncation identities -/

/-- **Truncation identity.**  If `x : ℝ≥0∞` is either `⊤` or a natural number, then for every
`n`, `min x n = ∑_{j < n} 1 {j + 1 ≤ x}`. -/
lemma min_eq_sum_ite {x : ℝ≥0∞} (hint : x = ⊤ ∨ ∃ m : ℕ, x = (m : ℝ≥0∞)) (n : ℕ) :
    min x (n : ℝ≥0∞) = ∑ j ∈ Finset.range n, (if ((j : ℝ≥0∞) + 1) ≤ x then 1 else 0) := by
  rcases hint with rfl | ⟨m, rfl⟩
  · rw [min_eq_right (le_top : (n : ℝ≥0∞) ≤ ⊤)]
    simp
  · have hstep : ∀ j ∈ Finset.range n,
        (if ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) then (1 : ℝ≥0∞) else 0)
          = ((if j + 1 ≤ m then 1 else 0 : ℕ) : ℝ≥0∞) := by
      intro j _
      have hcast : ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) ↔ j + 1 ≤ m := by
        rw [show ((j : ℝ≥0∞) + 1) = ((j + 1 : ℕ) : ℝ≥0∞) by push_cast; ring, Nat.cast_le]
      by_cases h : j + 1 ≤ m
      · rw [ite_eq_left (hcast.mpr h), ite_eq_left h]; simp
      · rw [ite_eq_right (hcast.not.mpr h), ite_eq_right h]; simp
    have hcard : ((∑ j ∈ Finset.range n, (if j + 1 ≤ m then 1 else 0 : ℕ) : ℕ) : ℝ≥0∞)
        = ((min m n : ℕ) : ℝ≥0∞) := by
      rw [← Finset.card_filter, filter_range_succ_le, Finset.card_range]
    rw [Finset.sum_congr rfl hstep, ← Nat.cast_sum, hcard, (Nat.mono_cast (α := ℝ≥0∞)).map_min]

/-- **Power truncation identity.**  If `x : ℝ≥0∞` is either `⊤` or a natural number, then for
every `n` and `k ≥ 1`, `(min x n)^k = ∑_{j<n} ((j+1)^k - j^k) 1{j+1 ≤ x}`. -/
lemma min_pow_eq_sum_ite {x : ℝ≥0∞} (hint : x = ⊤ ∨ ∃ m : ℕ, x = (m : ℝ≥0∞)) (n k : ℕ)
    (hk : 1 ≤ k) :
    min x (n : ℝ≥0∞) ^ k
      = ∑ j ∈ Finset.range n,
          ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            (if ((j : ℝ≥0∞) + 1) ≤ x then 1 else 0)) := by
  rcases hint with rfl | ⟨m, rfl⟩
  · rw [min_eq_right (le_top : (n : ℝ≥0∞) ≤ ⊤)]
    simp only [le_top, ite_true, mul_one]
    exact (sum_range_pow_sub k hk n).symm
  · have hstep : ∀ j ∈ Finset.range n,
        ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            (if ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) then 1 else 0))
          = (if j + 1 ≤ m then (((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) else 0) := by
      intro j _
      have hcast : ((j : ℝ≥0∞) + 1) ≤ ((m : ℝ≥0∞)) ↔ j + 1 ≤ m := by
        rw [show ((j : ℝ≥0∞) + 1) = ((j + 1 : ℕ) : ℝ≥0∞) by push_cast; ring, Nat.cast_le]
      by_cases h : j + 1 ≤ m
      · rw [ite_eq_left (hcast.mpr h), ite_eq_left h, mul_one]
      · rw [ite_eq_right (hcast.not.mpr h), ite_eq_right h, mul_zero]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, filter_range_succ_le,
      sum_range_pow_sub k hk, (Nat.mono_cast (α := ℝ≥0∞)).map_min]

/-! ### The truncations increase to `X` -/

lemma iSup_min_eq_self (x : ℝ≥0∞) : (⨆ n : ℕ, min x (n : ℝ≥0∞)) = x := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases hx : x = ⊤
  · rw [hx]
    exact le_trans (le_of_eq ENNReal.iSup_natCast.symm)
      (iSup_le fun n => le_iSup_of_le n (by rw [min_top_left]))
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ≥0, (r : ℝ≥0∞) = x := WithTop.ne_top_iff_exists.mp hx
    refine le_iSup_of_le ⌈r⌉₊ ?_
    rw [min_eq_left (by exact_mod_cast Nat.le_ceil r)]

lemma iSup_min_pow_eq_self (x : ℝ≥0∞) (k : ℕ) (hk : 1 ≤ k) :
    (⨆ n : ℕ, min x (n : ℝ≥0∞) ^ k) = x ^ k := by
  refine le_antisymm (iSup_le fun n => pow_le_pow_left' (min_le_left _ _) k) ?_
  by_cases hx : x = ⊤
  · have htop : (⊤ : ℝ≥0∞) ^ k = ⊤ := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [pow_succ]
      simp
    rw [hx, htop]
    refine le_trans (le_of_eq ENNReal.iSup_natCast.symm) (iSup_le fun N => ?_)
    refine le_iSup_of_le N ?_
    rw [min_top_left]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [zero_pow (by omega : k ≠ 0)]
    · calc (N : ℝ≥0∞) = (N : ℝ≥0∞) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ≥0∞) ^ k := pow_le_pow_right' (by exact_mod_cast Nat.succ_le_of_lt hN) hk
  · obtain ⟨r, rfl⟩ : ∃ r : ℝ≥0, (r : ℝ≥0∞) = x := WithTop.ne_top_iff_exists.mp hx
    refine le_iSup_of_le ⌈r⌉₊ ?_
    rw [min_eq_left (by exact_mod_cast Nat.le_ceil r)]

section Main

/-- **Discrete layer cake (first moment).** -/
theorem lintegral_eq_tsum_meas_ge {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) :
    ∫⁻ ω, X ω ∂μ = ∑' n : ℕ, μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := by
  have hiSup : (⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ) = ∫⁻ ω, X ω ∂μ := by
    rw [← lintegral_iSup (f := fun n ω => min (X ω) (n : ℝ≥0∞))]
    · exact lintegral_congr fun ω => iSup_min_eq_self (X ω)
    · exact fun n => hX.min (measurable_const (a := (n : ℝ≥0∞)))
    · exact fun a b hab ω => min_le_min_left _ (by exact_mod_cast hab)
  have hterm : ∀ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ
      = ∑ j ∈ Finset.range n, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} := by
    intro n
    have hmeas : ∀ j : ℕ, MeasurableSet {ω : Ω | ((j : ℝ≥0∞) + 1) ≤ X ω} :=
      fun j => hX measurableSet_Ici
    have hpt : ∀ ω, min (X ω) (n : ℝ≥0∞)
        = ∑ j ∈ Finset.range n, {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      intro ω
      rw [min_eq_sum_ite (hint ω) n]
      refine Finset.sum_congr rfl fun j _ => ?_
      classical
      simp only [Set.indicator_apply]
      by_cases h : ((j : ℝ≥0∞) + 1) ≤ X ω <;> simp [h]
    calc ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ
        = ∫⁻ ω, ∑ j ∈ Finset.range n, {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂μ :=
          lintegral_congr hpt
      _ = ∑ j ∈ Finset.range n, ∫⁻ ω, {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
          rw [lintegral_finsetSum]
          exact fun j _ => measurable_const.indicator (hmeas j)
      _ = ∑ j ∈ Finset.range n, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} := by
          exact Finset.sum_congr rfl fun j _ => lintegral_indicator_one (hmeas j)
  calc ∫⁻ ω, X ω ∂μ = ⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ∂μ := hiSup.symm
    _ = ⨆ n : ℕ, ∑ j ∈ Finset.range n, μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω} := by
        simp only [hterm]
    _ = ∑' n : ℕ, μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω} := ENNReal.tsum_eq_iSup_nat.symm

/-- **Discrete layer cake (k-th moment).** -/
theorem lintegral_pow_eq_tsum_meas_ge {μ : Measure Ω} {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞))
    (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ ω, X ω ^ k ∂μ
      = ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) *
          μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω}) := by
  have hiSup : (⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ) = ∫⁻ ω, X ω ^ k ∂μ := by
    rw [← lintegral_iSup (f := fun n ω => min (X ω) (n : ℝ≥0∞) ^ k)]
    · exact lintegral_congr fun ω => iSup_min_pow_eq_self (X ω) k hk
    · exact fun n => (hX.min (measurable_const (a := (n : ℝ≥0∞)))).pow_const k
    · exact fun a b hab ω => pow_le_pow_left' (min_le_min_left _ (by exact_mod_cast hab)) k
  have hterm : ∀ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ
      = ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
          μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}) := by
    intro n
    have hmeas : ∀ j : ℕ, MeasurableSet {ω : Ω | ((j : ℝ≥0∞) + 1) ≤ X ω} :=
      fun j => hX measurableSet_Ici
    have hpt : ∀ ω, min (X ω) (n : ℝ≥0∞) ^ k
        = ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) := by
      intro ω
      rw [min_pow_eq_sum_ite (hint ω) n k hk]
      refine Finset.sum_congr rfl fun j _ => ?_
      classical
      simp only [Set.indicator_apply]
      by_cases h : ((j : ℝ≥0∞) + 1) ≤ X ω <;> simp [h]
    calc ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ
        = ∫⁻ ω, ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂μ :=
                lintegral_congr hpt
      _ = ∑ j ∈ Finset.range n, ∫⁻ ω, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂μ := by
          rw [lintegral_finsetSum]
          exact fun j _ => (measurable_const.indicator (hmeas j)).const_mul _
      _ = ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
            μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_const_mul _ (measurable_const.indicator (hmeas j))]
          congr 1
          exact lintegral_indicator_one (hmeas j)
  calc ∫⁻ ω, X ω ^ k ∂μ = ⨆ n : ℕ, ∫⁻ ω, min (X ω) (n : ℝ≥0∞) ^ k ∂μ := hiSup.symm
    _ = ⨆ n : ℕ, ∑ j ∈ Finset.range n, ((((j : ℝ≥0∞) + 1) ^ k - (j : ℝ≥0∞) ^ k) *
          μ {ω | ((j : ℝ≥0∞) + 1) ≤ X ω}) := by simp only [hterm]
    _ = ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ k - (n : ℝ≥0∞) ^ k) *
          μ {ω | ((n : ℝ≥0∞) + 1) ≤ X ω}) := ENNReal.tsum_eq_iSup_nat.symm

end Main

/-! ### Non-vacuity -/

/-- **Non-vacuity witness.** For `X ≡ 3` under a point mass both sides of the first identity are `3`
and, at `k = 2`, both sides of the second are `9`. -/
theorem discreteLayerCake_three :
    (∫⁻ _ω, (3 : ℝ≥0∞) ∂(Measure.dirac ())) =
        ∑' n : ℕ, (Measure.dirac ()) {_ω : Unit | ((n : ℝ≥0∞) + 1) ≤ 3} ∧
      (∫⁻ _ω, (3 : ℝ≥0∞) ∂(Measure.dirac ())) = 3 ∧
      (∫⁻ _ω, (3 : ℝ≥0∞) ^ 2 ∂(Measure.dirac ())) =
        ∑' n : ℕ, ((((n : ℝ≥0∞) + 1) ^ 2 - (n : ℝ≥0∞) ^ 2) *
          (Measure.dirac ()) {_ω : Unit | ((n : ℝ≥0∞) + 1) ≤ 3}) ∧
      (∫⁻ _ω, (3 : ℝ≥0∞) ^ 2 ∂(Measure.dirac ())) = 9 := by
  have hint : ∀ _ω : Unit, (3 : ℝ≥0∞) = ⊤ ∨ ∃ m : ℕ, (3 : ℝ≥0∞) = (m : ℝ≥0∞) :=
    fun _ => Or.inr ⟨3, by norm_num⟩
  refine ⟨lintegral_eq_tsum_meas_ge measurable_const hint, by simp,
    lintegral_pow_eq_tsum_meas_ge measurable_const hint 2 (by norm_num), ?_⟩
  simp only [lintegral_const, measure_univ, mul_one]
  norm_num

end PercLib.Probability
