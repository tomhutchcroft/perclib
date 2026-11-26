/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied.
Mathematical reference: the ghost-field recursion on the rooted binary tree, obtained from
the Catalan law of the finite root cluster and the generating function of the Catalan
numbers.
-/
module

public import PercLib.Models.BinaryTreeMomentLaw
public import PercLib.Probability.GhostTransform
public import PercLib.Probability.LaplaceTail
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Ghost field on the rooted binary tree

For bond percolation on the rooted binary tree with open probability `p ∈ [0, 1]` and the
ghost transform `M_p(h) = E[1 - e^{-h|K|}]` of the root cluster (with `e^{-h∞} = 0`), this
file proves the fixed-point recursion

`M_p(h) = 1 - e^{-h} (1 - p M_p(h))^2` for `h > 0`,

and, at `p = 1/2`, the closed form `M_{1/2}(h) = 2√(1-e^{-h}) / (1 + √(1-e^{-h}))` together
with `M_{1/2}(h) ~ 2√h` as `h ↓ 0`.

The proof sums the Catalan law `binaryTree_law_cluster_card_eq_catalan`:
`1 - M_p(h) = G(e^{-h})` with `G(a) = ∑_{n ≥ 0} Cat(n+1) p^n (1-p)^{n+2} a^{n+1}`, and the
Catalan convolution `∑ Cat(n+1) x^n = (∑ Cat(n) x^n)^2` gives `G = a (1 - p + p G)^2`.
This file adds no definition.

## Main results

* `tsum_catalan_succ_mul_pow`: `∑ Cat(n+1) x^n = (∑ Cat(n) x^n)^2` for `0 ≤ x < 1/4`.
* `binaryTree_mass_series_eq`: the series `G` satisfies `G = a (1 - p + p G)^2`.
* `binaryTree_ghost_toReal_eq`: `M_p(h) = 1 - G(e^{-h})`.
* `binaryTree_ghost_recursion`: `M_p(h) = 1 - e^{-h} (1 - p M_p(h))^2`.
* `binaryTree_ghost_critical_eq`: the closed form at `p = 1/2`.
* `binaryTree_ghost_critical_isEquivalent`: `M_{1/2}(h) ~ 2√h` as `h ↓ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics PercLib.Probability
  PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

/-! ### The Catalan generating function -/

/-- `∑ Cat(n) x^n` converges for `0 ≤ x < 1/4`. -/
theorem summable_catalan_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1 / 4) :
    Summable fun n : ℕ => (catalan n : ℝ) * x ^ n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 4 * x) (by linarith))
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast catalan_le_four_pow n) (by positivity)

/-- **Catalan convolution.** For `0 ≤ x < 1/4`, `∑ Cat(n+1) x^n = (∑ Cat(n) x^n)^2`. -/
theorem tsum_catalan_succ_mul_pow {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1 / 4) :
    ∑' n : ℕ, (catalan (n + 1) : ℝ) * x ^ n = (∑' n : ℕ, (catalan n : ℝ) * x ^ n) ^ 2 := by
  have hs := summable_catalan_mul_pow hx0 hx
  have hn : Summable fun n : ℕ => ‖(catalan n : ℝ) * x ^ n‖ :=
    hs.congr fun n => (Real.norm_of_nonneg (by positivity)).symm
  rw [sq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hn hn]
  refine tsum_congr fun n => ?_
  rw [catalan_succ', Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [← hij, pow_add]
  push_cast
  ring

/-- **Binary-tree mass series.** For `p ∈ [0, 1]` and `0 ≤ a < 1`, the series
`G = ∑_{n ≥ 0} Cat(n+1) p^n (1-p)^{n+2} a^{n+1}` satisfies `G = a (1 - p + p G)^2`. -/
theorem binaryTree_mass_series_eq {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a < 1) :
    ∑' n : ℕ, (catalan (n + 1) : ℝ) * p ^ n * (1 - p) ^ (n + 2) * a ^ (n + 1) =
      a * (1 - p + p * ∑' n : ℕ, (catalan (n + 1) : ℝ) * p ^ n * (1 - p) ^ (n + 2) *
        a ^ (n + 1)) ^ 2 := by
  set x := p * (1 - p) * a with hxdef
  have hx0 : 0 ≤ x := by have : 0 ≤ 1 - p := by linarith
                         positivity
  have hx : x < 1 / 4 := by
    have h4 : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    have : x ≤ a / 4 := by rw [hxdef]; nlinarith
    linarith
  have hs := summable_catalan_mul_pow hx0 hx
  have hG : ∑' n : ℕ, (catalan (n + 1) : ℝ) * p ^ n * (1 - p) ^ (n + 2) * a ^ (n + 1) =
      (1 - p) ^ 2 * a * ∑' n : ℕ, (catalan (n + 1) : ℝ) * x ^ n := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [hxdef, mul_pow, mul_pow]
    ring
  have hS : ∑' n : ℕ, (catalan n : ℝ) * x ^ n =
      1 + x * ∑' n : ℕ, (catalan (n + 1) : ℝ) * x ^ n := by
    rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
    simp only [catalan_zero, Nat.cast_one, pow_zero, mul_one]
    congr 1
    refine tsum_congr fun n => ?_
    ring
  rw [tsum_catalan_succ_mul_pow hx0 hx] at hS hG
  rw [hG]
  set S := ∑' n : ℕ, (catalan n : ℝ) * x ^ n
  rw [hxdef] at hS
  linear_combination (a * (1 - p) ^ 2 * (S + 1 + p * (1 - p) * a * S ^ 2)) * hS

/-! ### The ghost transform as a series -/

/-- `e^{-ht}` (with `e^{-h∞} = 0`) as the series `∑_n 1{t = n} e^{-hn}`, for `h > 0`. -/
theorem ghost_exp_eq_tsum {h : ℝ} (hh : 0 < h) (t : ℕ∞) :
    EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal))) =
      ∑' n : ℕ, if t = n then ENNReal.ofReal (Real.exp (-h)) ^ n else 0 := by
  induction t using ENat.recTopCoe with
  | top => simp [EReal.coe_mul_top_of_pos hh]
  | coe m =>
    rw [ghost_exp_natCast, tsum_eq_single m (fun n hn => by simp [Ne.symm hn])]
    simp

/-- `e^{-ht} ≤ 1` for `h > 0`. -/
theorem ghost_exp_le_one {h : ℝ} (hh : 0 < h) (t : ℕ∞) :
    EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal))) ≤ 1 := by
  induction t using ENat.recTopCoe with
  | top => simp [EReal.coe_mul_top_of_pos hh]
  | coe m =>
    rw [ghost_exp_natCast]
    exact pow_le_one₀ (by positivity)
      (ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by linarith)))

/-- **Ghost transform on the binary tree.** For `h > 0`,
`M_p(h) = 1 - ∑_{n ≥ 0} Cat(n+1) p^n (1-p)^{n+2} e^{-h(n+1)}`. -/
theorem binaryTree_ghost_toReal_eq (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
        ∂law q).toReal =
      1 - ∑' n : ℕ, (catalan (n + 1) : ℝ) * (p : ℝ) ^ n * (1 - (p : ℝ)) ^ (n + 2) *
        Real.exp (-h) ^ (n + 1) := by
  set A : ℕ → Set (Config (List (Fin 2))) := fun n =>
    (fun ω : Config (List (Fin 2)) => (cluster ω []).encard) ⁻¹' {(n : ℕ∞)}
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurable_encard_cluster [] (measurableSet_singleton _)
  set g : Config (List (Fin 2)) → ℝ≥0∞ := fun ω =>
    EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal)))
  have hg : g = fun ω => ∑' n : ℕ, (A n).indicator
      (fun _ => ENNReal.ofReal (Real.exp (-h)) ^ n) ω := by
    funext ω
    simp only [g, ghost_exp_eq_tsum hh, A, Set.indicator, mem_preimage, mem_singleton_iff]
  have hgm : Measurable g :=
    (measurable_of_countable fun t : ℕ∞ =>
      EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal)))).comp (measurable_encard_cluster [])
  have hE : ∫⁻ ω, g ω ∂law q =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-h)) ^ n * law q (A n) := by
    rw [hg, lintegral_tsum fun n => (measurable_const.indicator (hA n)).aemeasurable]
    simp_rw [lintegral_indicator_const (hA _)]
  have hle : ∫⁻ ω, g ω ∂law q ≤ 1 := by
    calc ∫⁻ ω, g ω ∂law q ≤ ∫⁻ _, 1 ∂law q :=
          lintegral_mono fun ω => ghost_exp_le_one hh _
      _ = 1 := by simp
  have hfin : ∫⁻ ω, g ω ∂law q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hM : ∫⁻ ω, (1 - g ω) ∂law q = 1 - ∫⁻ ω, g ω ∂law q := by
    rw [lintegral_sub hgm hfin (ae_of_all _ fun ω => ghost_exp_le_one hh _)]
    simp
  change (∫⁻ ω, (1 - g ω) ∂law q).toReal = _
  rw [hM, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one]
  congr 1
  rw [hE] at hfin ⊢
  have hterm : ∀ n, ENNReal.ofReal (Real.exp (-h)) ^ n * law q (A n) ≠ ⊤ := fun n =>
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)
  rw [ENNReal.tsum_toReal_eq hterm, (ENNReal.summable_toReal hfin).tsum_eq_zero_add]
  have hA0 : law q (A 0) = 0 := by
    have : A 0 = ∅ := by
      ext ω
      simp only [A, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false,
        Nat.cast_zero, Set.encard_eq_zero]
      exact (Set.nonempty_of_mem (mem_cluster_self ω [])).ne_empty
    rw [this, measure_empty]
  rw [hA0, mul_zero, ENNReal.toReal_zero, zero_add]
  refine tsum_congr fun n => ?_
  have hlaw := binaryTree_law_cluster_card_toReal p q hq (Nat.succ_pos n)
  rw [setOf_ncard_eq_and_finite] at hlaw
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hlaw
  rw [ENNReal.toReal_mul, hlaw, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  ring

/-! ### The recursion and the critical closed form -/

/-- **Ghost recursion on the binary tree.** For `h > 0`,
`M_p(h) = 1 - e^{-h} (1 - p M_p(h))^2`. -/
theorem binaryTree_ghost_recursion (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
        ∂law q).toReal =
      1 - Real.exp (-h) * (1 - (p : ℝ) *
        (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
          ∂law q).toReal) ^ 2 := by
  rw [binaryTree_ghost_toReal_eq p q hq hh]
  have hG := binaryTree_mass_series_eq p.2.1 p.2.2 (Real.exp_pos (-h)).le
    (Real.exp_lt_one_iff.2 (by linarith))
  set G := ∑' n : ℕ, (catalan (n + 1) : ℝ) * (p : ℝ) ^ n * (1 - (p : ℝ)) ^ (n + 2) *
    Real.exp (-h) ^ (n + 1)
  linear_combination (-1 : ℝ) * hG

/-- **The critical quadratic.** If `0 < a < 1`, `M ≥ 0` and `M = 1 - a (1 - M/2)^2`, then
`M = 2√(1-a) / (1 + √(1-a))`. -/
theorem eq_of_eq_one_sub_mul_sq {a M : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hM0 : 0 ≤ M)
    (hM : M = 1 - a * (1 - 1 / 2 * M) ^ 2) :
    M = 2 * √(1 - a) / (1 + √(1 - a)) := by
  set s := √(1 - a) with hsdef
  have hs2 : s ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs1 : s < 1 := by nlinarith
  set u := 1 - 1 / 2 * M with hu
  have hfac : ((1 - s) * u - 1) * ((1 + s) * u - 1) = 0 := by
    have : a = 1 - s ^ 2 := by linarith
    rw [this] at hM
    linear_combination hM - 2 * hu
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exfalso
    have : 1 < u := by nlinarith
    linarith
  · rw [eq_div_iff (by linarith)]
    linear_combination (-2 : ℝ) * h1 + 2 * (1 + s) * hu

/-- **Critical closed form.** At `p = 1/2`, for `h > 0`,
`M_{1/2}(h) = 2√(1-e^{-h}) / (1 + √(1-e^{-h}))`. -/
theorem binaryTree_ghost_critical_eq (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω []).encard : ℝ≥0∞) : EReal))))
        ∂law q).toReal =
      2 * √(1 - Real.exp (-h)) / (1 + √(1 - Real.exp (-h))) := by
  have hrec := binaryTree_ghost_recursion p q hq hh
  rw [hp] at hrec
  exact eq_of_eq_one_sub_mul_sq (Real.exp_pos _) (Real.exp_lt_one_iff.2 (by linarith))
    ENNReal.toReal_nonneg hrec

/-- `2√(1-e^{-h}) / (1 + √(1-e^{-h})) ~ 2√h` as `h ↓ 0`. -/
theorem critical_ghost_formula_isEquivalent :
    (fun h : ℝ => 2 * √(1 - Real.exp (-h)) / (1 + √(1 - Real.exp (-h))))
      ~[𝓝[>] 0] fun h => 2 * √h := by
  refine isEquivalent_of_tendsto_one ?_
  have hs : Tendsto (fun h : ℝ => √(1 - Real.exp (-h))) (𝓝[>] 0) (𝓝 0) := by
    have : Continuous fun h : ℝ => √(1 - Real.exp (-h)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun h : ℝ => √((1 - Real.exp (-h)) / h) / (1 + √(1 - Real.exp (-h))))
      (𝓝[>] 0) (𝓝 1) := by
    have h3 := (tendsto_one_sub_exp_neg_div.sqrt).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add hs) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simp only [Real.sqrt_one, add_zero, div_one] at h3
    exact h3
  refine hr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh : 0 < h := hh
  have hsq : 0 < √h := Real.sqrt_pos.2 hh
  have h1 : 0 ≤ 1 - Real.exp (-h) := by
    have := Real.exp_le_one_iff.2 (by linarith : -h ≤ 0); linarith
  rw [Pi.div_apply, Real.sqrt_div' _ hh.le]
  have : 0 < 1 + √(1 - Real.exp (-h)) := by positivity
  field_simp

/-- **Critical asymptotics.** At `p = 1/2`, `M_{1/2}(h) ~ 2√h` as `h ↓ 0`. -/
theorem binaryTree_ghost_critical_isEquivalent (p : unitInterval)
    (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) = 1 / 2) :
    (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω []).encard : ℝ≥0∞) : EReal)))) ∂law q).toReal)
      ~[𝓝[>] 0] fun h => 2 * √h := by
  refine IsEquivalent.congr_left critical_ghost_formula_isEquivalent ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (binaryTree_ghost_critical_eq p q hq hp hh).symm

end PercLib.Models
