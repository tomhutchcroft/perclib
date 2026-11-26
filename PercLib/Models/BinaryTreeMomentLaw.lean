/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied.
-/
module

public import PercLib.Models.BinaryTreeCatalan
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Central

/-!
# Binary tree: the moment series is a truncated moment of the cluster law (GGVG)

For bond percolation on the rooted binary tree with open probability `p ∈ (0,1)`, `p ≠ 1/2`,
and every real `s`,

`E_p[|K|^s; |K| < ∞] = ((1-p)/p) ∑_{n ≥ 1} n^s Cat(n) 4^{-n} e^{-λ(p) n}`,
`λ(p) = -log(4p(1-p))` (`lintegral_cluster_rpow_eq_moment`). The right side is the series
`M_s(p)` of `PercLib/Models/BinaryTreeMoments.lean`, written with the index `n + 1`. The
proof sums the Catalan law `binaryTree_law_cluster_card_eq_catalan`.
At `p = 1/2` the real series need not converge, which is why `p ≠ 1/2` is assumed.
This file adds no definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-- A finite cluster of size `n` is a cluster of extended cardinality `n`. -/
theorem setOf_ncard_eq_and_finite (n : ℕ) :
    {ω : Config (List (Fin 2)) | (cluster ω []).ncard = n ∧ (cluster ω []).Finite} =
      (fun ω : Config (List (Fin 2)) => (cluster ω []).encard) ⁻¹' {(n : ℕ∞)} := by
  ext ω
  simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← h2.cast_ncard_eq, h1]
  · intro h
    have hfin : (cluster ω []).Finite := Set.finite_of_encard_eq_coe h
    refine ⟨?_, hfin⟩
    have := hfin.cast_ncard_eq
    rw [h] at this
    exact_mod_cast this

/-- `Cat(n) ≤ 4ⁿ`. -/
theorem catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  have h := succ_mul_catalan_eq_centralBinom n
  calc catalan n ≤ (n + 1) * catalan n := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    _ = Nat.centralBinom n := h
    _ ≤ 4 ^ n := Nat.centralBinom_le_four_pow n

/-- The moment series converges for `p ∈ (0,1)`, `p ≠ 1/2`. -/
theorem summable_moment_terms {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≠ 1 / 2) (s : ℝ) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ s * ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
      Real.exp (-(-Real.log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ))) := by
  set r := 4 * p * (1 - p)
  have hr0 : 0 < r := mul_pos (mul_pos (by norm_num) hp0) (by linarith)
  have hr1 : r < 1 := by
    have : 0 < (2 * p - 1) ^ 2 := by
      have : 2 * p - 1 ≠ 0 := fun h => hp (by linarith)
      positivity
    simp only [r]; nlinarith
  set k := ⌈max s 0⌉₊
  have hg : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r ^ (n + 1) := by
    have := summable_pow_mul_geometric_of_norm_lt_one k (r := r)
      (by rw [Real.norm_of_nonneg hr0.le]; exact hr1)
    exact (summable_nat_add_iff 1).2 this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hexp : Real.exp (-(-Real.log r * ((n + 1 : ℕ) : ℝ))) = r ^ (n + 1) := by
    rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
  rw [hexp]
  have hpow : ((n + 1 : ℕ) : ℝ) ^ s ≤ ((n + 1 : ℕ) : ℝ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1
      ((le_max_left s 0).trans (Nat.le_ceil _))
  have hcat : (catalan (n + 1) : ℝ) / 4 ^ (n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast catalan_le_four_pow (n + 1)
  have hcat0 : 0 ≤ (catalan (n + 1) : ℝ) / 4 ^ (n + 1) := by positivity
  calc ((n + 1 : ℕ) : ℝ) ^ s * ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) * r ^ (n + 1)
      ≤ ((n + 1 : ℕ) : ℝ) ^ k * 1 * r ^ (n + 1) := by
        gcongr
    _ = _ := by ring

open Classical in
/-- **Identification.** On the rooted binary tree with open probability `p ∈ (0,1)`,
`p ≠ 1/2`, `E_p[|K|^s; |K| < ∞] = ((1-p)/p) ∑_{n≥1} n^s Cat(n) 4^{-n} e^{-λ(p) n}`. -/
theorem lintegral_cluster_rpow_eq_moment (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hp : (p : ℝ) ≠ 1 / 2) (s : ℝ) :
    ∫⁻ ω, (if (cluster ω []).Finite then ENNReal.ofReal (((cluster ω []).ncard : ℝ) ^ s)
        else 0) ∂law q =
      ENNReal.ofReal ((1 - (p : ℝ)) / p * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ s *
        ((catalan (n + 1) : ℝ) / 4 ^ (n + 1)) *
        Real.exp (-(-Real.log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ)))) := by
  set A : ℕ → Set (Config (List (Fin 2))) := fun n =>
    {ω | (cluster ω []).ncard = n ∧ (cluster ω []).Finite}
  have hA : ∀ n, MeasurableSet (A n) := fun n => by
    simp only [A]
    rw [setOf_ncard_eq_and_finite]
    exact measurable_encard_cluster [] (measurableSet_singleton _)
  have hA0 : A 0 = ∅ := by
    ext ω
    simp only [A, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro h hfin
    rw [Set.ncard_eq_zero hfin] at h
    exact (Set.eq_empty_iff_forall_notMem.1 h) [] (mem_cluster_self ω [])
  -- the integrand as a sum of indicators
  have hF : (fun ω : Config (List (Fin 2)) =>
      if (cluster ω []).Finite then ENNReal.ofReal (((cluster ω []).ncard : ℝ) ^ s) else 0) =
      fun ω => ∑' n : ℕ, (A n).indicator (fun _ => ENNReal.ofReal ((n : ℝ) ^ s)) ω := by
    funext ω
    by_cases hfin : (cluster ω []).Finite
    · simp only [hfin, ↓reduceIte]
      rw [tsum_eq_single (cluster ω []).ncard]
      · simp [A, Set.indicator, hfin]
      · intro n hn
        simp only [A, Set.indicator, mem_ofPred_eq, hfin, and_true]
        simp [Ne.symm hn]
    · simp only [hfin, ↓reduceIte]
      symm
      exact ENNReal.tsum_eq_zero.2 fun n => by simp [A, Set.indicator, hfin]
  rw [hF, lintegral_tsum fun n => (measurable_const.indicator (hA n)).aemeasurable]
  simp_rw [lintegral_indicator_const (hA _)]
  have h0 : law q (A 0) = 0 := by rw [hA0, measure_empty]
  have e := tsum_eq_zero_add' (f := fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ s) * law q (A n))
    ENNReal.summable
  simp only [h0, mul_zero, zero_add] at e
  rw [e]
  -- the real side
  have hsum := summable_moment_terms hp0 hp1 hp s
  have hpq : 0 ≤ (1 - (p : ℝ)) / p := div_nonneg (by linarith) hp0.le
  rw [← hsum.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg hpq (by positivity)) (hsum.mul_left _)]
  refine tsum_congr fun n => ?_
  have hr0 : 0 < 4 * (p : ℝ) * (1 - p) := mul_pos (mul_pos (by norm_num) hp0) (by linarith)
  rw [binaryTree_law_cluster_card_eq_catalan p q hq (Nat.succ_pos n)]
  have hexp : Real.exp (-(-Real.log (4 * p * (1 - p)) * ((n + 1 : ℕ) : ℝ))) =
      (4 * (p : ℝ) * (1 - p)) ^ (n + 1) := by
    rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
  have hp' : ((unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_coe_nnreal]; rfl
  have hq' : ((unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (1 - p) := by
    rw [← ENNReal.ofReal_coe_nnreal]; rfl
  rw [hexp, hp', hq', ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hp0.le,
    ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, mul_pow]
  field_simp
  ring

/-- Non-vacuity: the hypotheses hold at `p = 1/4` with `q` the tree profile, for every `s`. -/
example (s : ℝ) := lintegral_cluster_rpow_eq_moment
  (⟨1 / 4, by norm_num, by norm_num⟩ : unitInterval)
  (fun e => if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet
    then ⟨1 / 4, by norm_num, by norm_num⟩ else 0)
  (fun _ _ => rfl) (by norm_num) (by norm_num) (by norm_num) s

end PercLib.Models

end
