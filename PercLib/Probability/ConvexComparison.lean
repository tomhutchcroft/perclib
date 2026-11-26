/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
Mathematical reference: T. Hutchcroft, *Critical cluster volumes in hierarchical
percolation*, arXiv:2211.05686v1, Theorem 6.12 and Remark 6.13 (an integrable form with
real-valued increments is proved here by discretisation and supporting lines).
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic

/-!
# Convex comparison under negative quadrant dependence with preceding sums

Let `Z₀, …, Z_{n-1}` be integrable real random variables such that every increment `Z_i`
is negatively quadrant dependent with the preceding sum `S_i = Z₀ + ⋯ + Z_{i-1}`:
`P(S_i ≥ u, Z_i ≥ v) ≤ P(S_i ≥ u) P(Z_i ≥ v)`. If `Z*_i` are independent with the same
marginal laws, then `E φ(S_n) ≤ E φ(S*_n)` for every convex `φ : ℝ → ℝ`, as extended
expectations in `(-∞, ∞]`.

The two-variable case is proved for convex Lipschitz `φ` by discretising both variables on
a finite grid, where a two-dimensional summation by parts expresses `E φ(X + Y)` through the
joint upper tails with nonnegative mixed second differences of `φ` as coefficients. The
general case follows by induction and by approximating `φ` from below by finite maxima of
supporting lines.

## Main results

* `eq_add_sum_sum_mixedDiff`: two-dimensional telescoping on `ℕ × ℕ`.
* `integral_comp_min_le_integral_prod_of_tail_le`: the discrete comparison.
* `integral_comp_add_le_integral_prod_of_tail_le`: two variables, convex Lipschitz `φ`.
* `integral_comp_sum_le_of_tail_le_of_lipschitzWith`: `n` increments, convex Lipschitz `φ`.
* `ConvexOn.exists_lipschitzWith_tendsto`: convex Lipschitz approximation from below.
* `convex_comparison_of_lipschitzWith_comparison`: from Lipschitz to general convex `φ`.
* `convex_comparison_sum_of_tail_le`, `integral_max_sub_le_of_tail_le`,
  `lintegral_abs_sub_integral_rpow_le_of_tail_le`: the comparison for `n` increments.
* `ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum`: absolute a.e. and `L¹`
  convergence of a series with `∑ E |Y_i| < ∞`.
* `convex_comparison_tsum_of_tail_le`, `lintegral_exp_mul_sub_integral_le_of_tail_le`,
  `lintegral_abs_sub_integral_tsum_rpow_le_of_tail_le`: the comparison for countable sums.

No definition is introduced.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Topology NNReal

namespace PercLib.Probability

variable {Ω Ω' γ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace γ]
  [MeasurableSpace α] [MeasurableSpace β]

/-! ### Two-dimensional summation by parts -/

/-- Two-dimensional telescoping: a function on `ℕ × ℕ` is its value at the origin plus its
increments along the axes plus the sum of its mixed second differences. -/
theorem eq_add_sum_sum_mixedDiff (ψ : ℕ → ℕ → ℝ) (a b : ℕ) :
    ψ a b = ψ 0 0 + ∑ j ∈ range a, (ψ (j + 1) 0 - ψ j 0) +
      ∑ k ∈ range b, (ψ 0 (k + 1) - ψ 0 k) +
      ∑ j ∈ range a, ∑ k ∈ range b,
        (ψ (j + 1) (k + 1) - ψ j (k + 1) - ψ (j + 1) k + ψ j k) := by
  have h1 : ∀ j, ∑ k ∈ range b, (ψ (j + 1) (k + 1) - ψ j (k + 1) - ψ (j + 1) k + ψ j k) =
      (ψ (j + 1) b - ψ j b) - (ψ (j + 1) 0 - ψ j 0) := by
    intro j
    rw [← Finset.sum_range_sub (fun k => ψ (j + 1) k - ψ j k) b]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∑ j ∈ range a, ((ψ (j + 1) b - ψ j b) - (ψ (j + 1) 0 - ψ j 0)) =
      (ψ a b - ψ 0 b) - (ψ a 0 - ψ 0 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => ψ j b) a,
      Finset.sum_range_sub (fun j => ψ j 0) a]
  rw [Finset.sum_congr rfl fun j _ => h1 j, h2, Finset.sum_range_sub (fun j => ψ j 0) a,
    Finset.sum_range_sub (fun k => ψ 0 k) b]
  ring

theorem sum_range_min_eq_sum_ite (f : ℕ → ℝ) (a N : ℕ) :
    ∑ j ∈ range (min a N), f j = ∑ j ∈ range N, if j < a then f j else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- The expectation of a function of two bounded natural random variables, written through
their upper tails and joint upper tails. -/
theorem integral_comp_min_eq (ρ : Measure γ) [IsProbabilityMeasure ρ] {u v : γ → ℕ}
    (hu : Measurable u) (hv : Measurable v) (ψ : ℕ → ℕ → ℝ) (N : ℕ) :
    ∫ w, ψ (min (u w) N) (min (v w) N) ∂ρ = ψ 0 0 +
      ∑ j ∈ range N, ρ.real {w | j < u w} * (ψ (j + 1) 0 - ψ j 0) +
      ∑ k ∈ range N, ρ.real {w | k < v w} * (ψ 0 (k + 1) - ψ 0 k) +
      ∑ j ∈ range N, ∑ k ∈ range N, ρ.real ({w | j < u w} ∩ {w | k < v w}) *
        (ψ (j + 1) (k + 1) - ψ j (k + 1) - ψ (j + 1) k + ψ j k) := by
  have hsu : ∀ j, MeasurableSet {w | j < u w} := fun j => measurableSet_lt measurable_const hu
  have hsv : ∀ k, MeasurableSet {w | k < v w} := fun k => measurableSet_lt measurable_const hv
  have hpt : ∀ w, ψ (min (u w) N) (min (v w) N) = ψ 0 0 +
      ∑ j ∈ range N, {w | j < u w}.indicator (fun _ => ψ (j + 1) 0 - ψ j 0) w +
      ∑ k ∈ range N, {w | k < v w}.indicator (fun _ => ψ 0 (k + 1) - ψ 0 k) w +
      ∑ j ∈ range N, ∑ k ∈ range N, ({w | j < u w} ∩ {w | k < v w}).indicator
        (fun _ => ψ (j + 1) (k + 1) - ψ j (k + 1) - ψ (j + 1) k + ψ j k) w := by
    intro w
    rw [eq_add_sum_sum_mixedDiff ψ (min (u w) N) (min (v w) N)]
    simp only [sum_range_min_eq_sum_ite, Set.indicator_apply, Set.mem_inter_iff]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j < u w
    · simp [hj]
    · simp [hj]
  have hI : ∀ (s : Set γ) (c : ℝ), MeasurableSet s → Integrable (s.indicator fun _ => c) ρ :=
    fun s c hs => (integrable_const c).indicator hs
  have hA : Integrable (fun w => ∑ j ∈ range N,
      {w | j < u w}.indicator (fun _ => ψ (j + 1) 0 - ψ j 0) w) ρ :=
    integrable_finsetSum _ fun j _ => hI _ _ (hsu j)
  have hB : Integrable (fun w => ∑ k ∈ range N,
      {w | k < v w}.indicator (fun _ => ψ 0 (k + 1) - ψ 0 k) w) ρ :=
    integrable_finsetSum _ fun k _ => hI _ _ (hsv k)
  have hD : Integrable (fun w => ∑ j ∈ range N, ∑ k ∈ range N,
      ({w | j < u w} ∩ {w | k < v w}).indicator
        (fun _ => ψ (j + 1) (k + 1) - ψ j (k + 1) - ψ (j + 1) k + ψ j k) w) ρ :=
    integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hI _ _ ((hsu j).inter (hsv k))
  simp_rw [hpt]
  rw [integral_add, integral_add, integral_add]
  all_goals try (first | exact integrable_const _ | exact hA | exact hB | exact hD |
    exact (integrable_const _).add hA | exact ((integrable_const _).add hA).add hB)
  rw [integral_const, integral_finsetSum _ fun j _ => hI _ _ (hsu j),
    integral_finsetSum _ fun k _ => hI _ _ (hsv k),
    integral_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => hI _ _ ((hsu j).inter (hsv k))]
  simp_rw [integral_finsetSum _ fun k _ => hI _ _ ((hsu _).inter (hsv k)),
    integral_indicator_const _ (hsu _), integral_indicator_const _ (hsv _),
    integral_indicator_const _ ((hsu _).inter (hsv _))]
  simp

/-- Discrete comparison: if two bounded natural observables of `X` and `Y` satisfy the
joint upper-tail bound, then for every function with nonnegative mixed second differences
the expectation under the joint law is at most that under the product of the marginals. -/
theorem integral_comp_min_le_integral_prod_of_tail_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y) {f : α → ℕ} {g : β → ℕ}
    (hf : Measurable f) (hg : Measurable g) (N : ℕ)
    (htail : ∀ j < N, ∀ k < N, μ.real ({ω | j < f (X ω)} ∩ {ω | k < g (Y ω)}) ≤
      μ.real {ω | j < f (X ω)} * μ.real {ω | k < g (Y ω)})
    (ψ : ℕ → ℕ → ℝ) (hψ : ∀ j k, 0 ≤ ψ (j + 1) (k + 1) - ψ j (k + 1) - ψ (j + 1) k + ψ j k) :
    ∫ ω, ψ (min (f (X ω)) N) (min (g (Y ω)) N) ∂μ ≤
      ∫ p, ψ (min (f p.1) N) (min (g p.2) N) ∂((μ.map X).prod (μ.map Y)) := by
  rw [integral_comp_min_eq μ (u := fun ω => f (X ω)) (v := fun ω => g (Y ω)) (hf.comp hX)
      (hg.comp hY),
    integral_comp_min_eq _ (u := fun p : α × β => f p.1) (v := fun p : α × β => g p.2)
      (hf.comp measurable_fst) (hg.comp measurable_snd)]
  have hsf : ∀ j, MeasurableSet {x | j < f x} := fun j => measurableSet_lt measurable_const hf
  have hsg : ∀ k, MeasurableSet {y | k < g y} := fun k => measurableSet_lt measurable_const hg
  have e1 : ∀ j, ((μ.map X).prod (μ.map Y)).real {p : α × β | j < f p.1} =
      μ.real {ω | j < f (X ω)} := by
    intro j
    rw [show {p : α × β | j < f p.1} = {x | j < f x} ×ˢ (univ : Set β) by ext; simp,
      measureReal_prod_prod, probReal_univ, mul_one, map_measureReal_apply hX (hsf j)]
    rfl
  have e2 : ∀ k, ((μ.map X).prod (μ.map Y)).real {p : α × β | k < g p.2} =
      μ.real {ω | k < g (Y ω)} := by
    intro k
    rw [show {p : α × β | k < g p.2} = (univ : Set α) ×ˢ {y | k < g y} by ext; simp,
      measureReal_prod_prod, probReal_univ, one_mul, map_measureReal_apply hY (hsg k)]
    rfl
  have e3 : ∀ j k, ((μ.map X).prod (μ.map Y)).real
      ({p : α × β | j < f p.1} ∩ {p : α × β | k < g p.2}) =
      μ.real {ω | j < f (X ω)} * μ.real {ω | k < g (Y ω)} := by
    intro j k
    rw [show {p : α × β | j < f p.1} ∩ {p : α × β | k < g p.2} =
        {x | j < f x} ×ˢ {y | k < g y} by ext; simp,
      measureReal_prod_prod, map_measureReal_apply hX (hsf j), map_measureReal_apply hY (hsg k)]
    rfl
  simp only [e1, e2, e3]
  gcongr with j hj k hk
  all_goals first | exact hψ j k |
    exact htail j (Finset.mem_range.1 hj) k (Finset.mem_range.1 hk)

/-! ### Discretisation of the real line -/

/-- The second difference of a convex function is nonnegative. -/
theorem ConvexOn.add_two_mul_sub_two_mul_add_nonneg {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ)
    (t h : ℝ) : 0 ≤ φ (t + 2 * h) - 2 * φ (t + h) + φ t := by
  have := hφ.2 (mem_univ t) (mem_univ (t + 2 * h)) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  have e : 1 / 2 * t + 1 / 2 * (t + 2 * h) = t + h := by ring
  rw [e] at this
  linarith

theorem lt_floor_mul_clamp_add_sq_iff {m j : ℕ} (hm : 0 < m) (hj : j < 2 * m ^ 2) (x : ℝ) :
    j < ⌊(m : ℝ) * max (-(m : ℝ)) (min x m) + (m : ℝ) ^ 2⌋₊ ↔
      ((j : ℝ) + 1 - (m : ℝ) ^ 2) / m ≤ x := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj' : (j : ℝ) + 1 ≤ 2 * (m : ℝ) ^ 2 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hnn : 0 ≤ (m : ℝ) * max (-(m : ℝ)) (min x m) + (m : ℝ) ^ 2 := by
    have := le_max_left (-(m : ℝ)) (min x m)
    nlinarith
  rw [← Nat.add_one_le_iff, Nat.le_floor_iff hnn]
  push_cast
  have hlow : -(m : ℝ) < ((j : ℝ) + 1 - (m : ℝ) ^ 2) / m := by
    rw [lt_div_iff₀ hm']; nlinarith
  have hup : ((j : ℝ) + 1 - (m : ℝ) ^ 2) / m ≤ m := by
    rw [div_le_iff₀ hm']; nlinarith
  constructor
  · intro h
    have h' : ((j : ℝ) + 1 - (m : ℝ) ^ 2) / m ≤ max (-(m : ℝ)) (min x m) := by
      rw [div_le_iff₀ hm']; linarith
    rcases le_max_iff.1 h' with h'' | h''
    · exact absurd h'' (not_le.2 hlow)
    · exact (le_min_iff.1 h'').1
  · intro h
    have h' : ((j : ℝ) + 1 - (m : ℝ) ^ 2) / m ≤ max (-(m : ℝ)) (min x m) :=
      le_max_of_le_right (le_min h hup)
    rw [div_le_iff₀ hm'] at h'
    linarith

theorem floor_mul_clamp_add_sq_le {m : ℕ} (x : ℝ) :
    ⌊(m : ℝ) * max (-(m : ℝ)) (min x m) + (m : ℝ) ^ 2⌋₊ ≤ 2 * m ^ 2 := by
  refine Nat.floor_le_of_le ?_
  push_cast
  have := min_le_right x (m : ℝ)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : max (-(m : ℝ)) (min x m) ≤ m := max_le (by linarith) this
  nlinarith

theorem abs_floor_mul_clamp_add_sq_sub_div_le {m : ℕ} (hm : 0 < m) (x : ℝ) :
    |((⌊(m : ℝ) * max (-(m : ℝ)) (min x m) + (m : ℝ) ^ 2⌋₊ : ℝ) - (m : ℝ) ^ 2) / m| ≤
      |x| + 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set t := max (-(m : ℝ)) (min x m) with ht
  have htx : |t| ≤ |x| := by
    rw [abs_le]
    constructor
    · exact le_max_of_le_right (le_min (neg_abs_le x) (by linarith [abs_nonneg x]))
    · exact max_le (by linarith [abs_nonneg x]) ((min_le_left _ _).trans (le_abs_self x))
  have hnn : 0 ≤ (m : ℝ) * t + (m : ℝ) ^ 2 := by
    have := le_max_left (-(m : ℝ)) (min x m)
    nlinarith
  have h1 := Nat.floor_le hnn
  have h2 := Nat.lt_floor_add_one ((m : ℝ) * t + (m : ℝ) ^ 2)
  have ht' := abs_le.1 htx
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hm']; nlinarith
  · rw [div_le_iff₀ hm']; nlinarith

theorem tendsto_floor_mul_clamp_add_sq_sub_div (x : ℝ) :
    Tendsto (fun m : ℕ => ((⌊((m : ℝ) + 1) * max (-((m : ℝ) + 1)) (min x ((m : ℝ) + 1)) +
      ((m : ℝ) + 1) ^ 2⌋₊ : ℝ) - ((m : ℝ) + 1) ^ 2) / ((m : ℝ) + 1)) atTop (𝓝 x) := by
  have hlow : Tendsto (fun m : ℕ => x - 1 / ((m : ℝ) + 1)) atTop (𝓝 x) := by
    have := (tendsto_const_nhds (x := x) (f := (atTop : Filter ℕ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  all_goals
    obtain ⟨M, hM⟩ := exists_nat_ge |x|
    filter_upwards [eventually_ge_atTop M] with m hm
    have hm' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hxm : |x| ≤ (m : ℝ) + 1 := hM.trans (by exact_mod_cast hm.trans (Nat.le_succ m))
    have hc : max (-((m : ℝ) + 1)) (min x ((m : ℝ) + 1)) = x := by
      have := abs_le.1 hxm
      rw [min_eq_left this.2, max_eq_right this.1]
    rw [hc]
    have hnn : 0 ≤ ((m : ℝ) + 1) * x + ((m : ℝ) + 1) ^ 2 := by
      have := (abs_le.1 hxm).1
      nlinarith
    have h1 := Nat.floor_le hnn
    have h2 := Nat.lt_floor_add_one (((m : ℝ) + 1) * x + ((m : ℝ) + 1) ^ 2)
  · rw [le_div_iff₀ hm', sub_mul, one_div, inv_mul_cancel₀ hm'.ne']; nlinarith
  · rw [div_le_iff₀ hm']; nlinarith

theorem measurable_floor_mul_clamp_add_sq (m : ℕ) :
    Measurable fun x : ℝ => ⌊(m : ℝ) * max (-(m : ℝ)) (min x m) + (m : ℝ) ^ 2⌋₊ :=
  Nat.measurable_floor.comp (by fun_prop)

/-- For a Lipschitz `φ`, `|φ u| ≤ |φ 0| + K |u|`. -/
theorem LipschitzWith.abs_le_abs_zero_add {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (u : ℝ) : |φ u| ≤ |φ 0| + K * |u| := by
  have := hφ.dist_le_mul u 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  have := abs_sub_abs_le_abs_sub (φ u) (φ 0)
  linarith

/-! ### Two variables -/

/-- **Two-variable convex comparison** for convex Lipschitz functions: if `X` and `Y` are
integrable and negatively quadrant dependent, then `E φ(X + Y)` is at most the integral of
`φ(x + y)` against the product of the laws of `X` and `Y`. -/
theorem integral_comp_add_le_integral_prod_of_tail_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hXm : Measurable X) (hYm : Measurable Y) (hX : Integrable X μ)
    (hY : Integrable Y μ)
    (htail : ∀ u v, μ.real ({ω | u ≤ X ω} ∩ {ω | v ≤ Y ω}) ≤
      μ.real {ω | u ≤ X ω} * μ.real {ω | v ≤ Y ω})
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ConvexOn ℝ univ φ) (hφK : LipschitzWith K φ) :
    ∫ ω, φ (X ω + Y ω) ∂μ ≤ ∫ p, φ (p.1 + p.2) ∂((μ.map X).prod (μ.map Y)) := by
  set q : ℕ → ℝ → ℝ := fun m x => ((⌊((m : ℝ) + 1) * max (-((m : ℝ) + 1))
    (min x ((m : ℝ) + 1)) + ((m : ℝ) + 1) ^ 2⌋₊ : ℝ) - ((m : ℝ) + 1) ^ 2) / ((m : ℝ) + 1)
    with hq
  have hqm : ∀ m, Measurable (q m) := fun m => by
    have := measurable_floor_mul_clamp_add_sq (m + 1)
    push_cast at this
    exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp this |>.sub_const _).div_const _
  have hqb : ∀ m x, |q m x| ≤ |x| + 1 := fun m x => by
    have := abs_floor_mul_clamp_add_sq_sub_div_le (m := m + 1) (Nat.succ_pos m) x
    push_cast at this
    exact this
  have hqt : ∀ x, Tendsto (fun m => q m x) atTop (𝓝 x) :=
    tendsto_floor_mul_clamp_add_sq_sub_div
  have hφc := hφK.continuous
  -- the discrete comparison at each grid size
  have hstep : ∀ m, ∫ ω, φ (q m (X ω) + q m (Y ω)) ∂μ ≤
      ∫ p, φ (q m p.1 + q m p.2) ∂((μ.map X).prod (μ.map Y)) := by
    intro m
    set M := m + 1 with hM
    have hM0 : 0 < M := Nat.succ_pos m
    set d : ℝ → ℕ := fun x => ⌊(M : ℝ) * max (-(M : ℝ)) (min x M) + (M : ℝ) ^ 2⌋₊ with hd
    set ψ : ℕ → ℕ → ℝ := fun a b =>
      φ (((a : ℝ) - (M : ℝ) ^ 2) / M + ((b : ℝ) - (M : ℝ) ^ 2) / M) with hψ
    have hdq : ∀ x, ((d x : ℝ) - (M : ℝ) ^ 2) / M = q m x := fun x => by
      simp [hd, hq, hM]
    have hdN : ∀ x, min (d x) (2 * M ^ 2) = d x := fun x =>
      min_eq_left (floor_mul_clamp_add_sq_le x)
    have hset : ∀ (Z : Ω → ℝ) (j : ℕ), j < 2 * M ^ 2 →
        {ω | j < d (Z ω)} = {ω | ((j : ℝ) + 1 - (M : ℝ) ^ 2) / M ≤ Z ω} := by
      intro Z j hj
      ext ω
      exact lt_floor_mul_clamp_add_sq_iff hM0 hj (Z ω)
    have key := integral_comp_min_le_integral_prod_of_tail_le hXm hYm
      (measurable_floor_mul_clamp_add_sq M) (measurable_floor_mul_clamp_add_sq M) (2 * M ^ 2)
      (fun j hj k hk => by
        change μ.real ({ω | j < d (X ω)} ∩ {ω | k < d (Y ω)}) ≤
          μ.real {ω | j < d (X ω)} * μ.real {ω | k < d (Y ω)}
        rw [hset X j hj, hset Y k hk]
        exact htail _ _) ψ
      (fun j k => by
        have e : ∀ a b : ℕ, ψ a b = φ (((a : ℝ) + b - 2 * (M : ℝ) ^ 2) / M) := fun a b => by
          simp only [hψ]; congr 1; ring
        simp only [e]
        have := ConvexOn.add_two_mul_sub_two_mul_add_nonneg hφ
          (((j : ℝ) + k - 2 * (M : ℝ) ^ 2) / M) (1 / M)
        have h1 : (((j + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) - 2 * (M : ℝ) ^ 2) / M =
            ((j : ℝ) + k - 2 * (M : ℝ) ^ 2) / M + 2 * (1 / M) := by push_cast; ring
        have h2 : (((j : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) - 2 * (M : ℝ) ^ 2) / M =
            ((j : ℝ) + k - 2 * (M : ℝ) ^ 2) / M + 1 / M := by push_cast; ring
        have h3 : (((j + 1 : ℕ) : ℝ) + ((k : ℕ) : ℝ) - 2 * (M : ℝ) ^ 2) / M =
            ((j : ℝ) + k - 2 * (M : ℝ) ^ 2) / M + 1 / M := by push_cast; ring
        rw [h1, h2, h3]
        linarith)
    change ∫ ω, ψ (min (d (X ω)) (2 * M ^ 2)) (min (d (Y ω)) (2 * M ^ 2)) ∂μ ≤
      ∫ p, ψ (min (d p.1) (2 * M ^ 2)) (min (d p.2) (2 * M ^ 2))
        ∂((μ.map X).prod (μ.map Y)) at key
    simp only [hdN, hψ, hdq] at key
    exact key
  -- pass to the limit on both sides by dominated convergence
  have hXmap : Integrable (fun x : ℝ => x) (μ.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hXm.aemeasurable).2 hX
  have hYmap : Integrable (fun y : ℝ => y) (μ.map Y) :=
    (integrable_map_measure aestronglyMeasurable_id hYm.aemeasurable).2 hY
  have hbd : ∀ m a b, ‖φ (q m a + q m b)‖ ≤ |φ 0| + K * ((|a| + 1) + (|b| + 1)) := by
    intro m a b
    rw [Real.norm_eq_abs]
    refine (LipschitzWith.abs_le_abs_zero_add hφK _).trans ?_
    gcongr
    exact (abs_add_le _ _).trans (add_le_add (hqb m a) (hqb m b))
  have hL : Tendsto (fun m => ∫ ω, φ (q m (X ω) + q m (Y ω)) ∂μ) atTop
      (𝓝 (∫ ω, φ (X ω + Y ω) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => |φ 0| + K * ((|X ω| + 1) + (|Y ω| + 1))) (fun m => ?_) ?_
      (fun m => Eventually.of_forall fun ω => hbd m _ _) (Eventually.of_forall fun ω => ?_)
    · exact (hφc.measurable.comp (((hqm m).comp hXm).add ((hqm m).comp hYm))).aestronglyMeasurable
    · exact (integrable_const _).add (((hX.abs.add (integrable_const _)).add
        (hY.abs.add (integrable_const _))).const_mul _)
    · exact (hφc.tendsto _).comp ((hqt _).add (hqt _))
  have hR : Tendsto (fun m => ∫ p, φ (q m p.1 + q m p.2) ∂((μ.map X).prod (μ.map Y))) atTop
      (𝓝 (∫ p, φ (p.1 + p.2) ∂((μ.map X).prod (μ.map Y)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p : ℝ × ℝ => |φ 0| + K * ((|p.1| + 1) + (|p.2| + 1))) (fun m => ?_) ?_
      (fun m => Eventually.of_forall fun p => hbd m _ _) (Eventually.of_forall fun p => ?_)
    · exact (hφc.measurable.comp (((hqm m).comp measurable_fst).add
        ((hqm m).comp measurable_snd))).aestronglyMeasurable
    · exact (integrable_const _).add ((((hXmap.abs.add (integrable_const _)).comp_fst _).add
        ((hYmap.abs.add (integrable_const _)).comp_snd _)).const_mul _)
    · exact (hφc.tendsto _).comp ((hqt _).add (hqt _))
  exact le_of_tendsto_of_tendsto' hL hR hstep


/-! ### Lipschitz functions and averaged translates -/

theorem integrable_comp_of_lipschitzWith {ν : Measure γ} [IsFiniteMeasure ν] {f : γ → ℝ}
    (hf : Integrable f ν) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    Integrable (fun w => φ (f w)) ν :=
  ((integrable_const |φ 0|).add (hf.abs.const_mul K)).mono'
    (hφ.continuous.comp_aestronglyMeasurable hf.1)
    (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact LipschitzWith.abs_le_abs_zero_add hφ _)

theorem integrable_id_map {μ : Measure Ω} {X : Ω → ℝ} (hXm : Measurable X)
    (hX : Integrable X μ) : Integrable (fun x : ℝ => x) (μ.map X) :=
  (integrable_map_measure aestronglyMeasurable_id hXm.aemeasurable).2 hX

/-- Averaging translates of a convex function against an integrable law keeps it convex. -/
theorem convexOn_integral_comp_add {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable (fun y => y) ν) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ConvexOn ℝ univ φ)
    (hφK : LipschitzWith K φ) : ConvexOn ℝ univ fun x => ∫ y, φ (x + y) ∂ν := by
  have hi : ∀ x, Integrable (fun y => φ (x + y)) ν := fun x =>
    integrable_comp_of_lipschitzWith ((integrable_const x).add hν) hφK
  refine ⟨convex_univ, fun x _ x' _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi x).const_mul a) ((hi x').const_mul b)]
  refine integral_mono (hi _) (((hi x).const_mul a).add ((hi x').const_mul b)) fun y => ?_
  have := hφ.2 (mem_univ (x + y)) (mem_univ (x' + y)) ha hb hab
  simp only [smul_eq_mul] at this
  rw [show a * x + b * x' + y = a * (x + y) + b * (x' + y) by linear_combination (-y) * hab]
  exact this

/-- Averaging translates of a `K`-Lipschitz function keeps it `K`-Lipschitz. -/
theorem lipschitzWith_integral_comp_add {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable (fun y => y) ν) {φ : ℝ → ℝ} {K : ℝ≥0} (hφK : LipschitzWith K φ) :
    LipschitzWith K fun x => ∫ y, φ (x + y) ∂ν := by
  have hi : ∀ x, Integrable (fun y => φ (x + y)) ν := fun x =>
    integrable_comp_of_lipschitzWith ((integrable_const x).add hν) hφK
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, Real.dist_eq, ← integral_sub (hi x) (hi x')]
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ y, |φ (x + y) - φ (x' + y)| ∂ν ≤ ∫ _y, (K : ℝ) * |x - x'| ∂ν :=
        integral_mono ((hi x).sub (hi x')).abs (integrable_const _) fun y => by
          have := hφK.dist_le_mul (x + y) (x' + y)
          rw [Real.dist_eq, Real.dist_eq, add_sub_add_right_eq_sub] at this
          exact this
    _ = K * |x - x'| := by simp

/-! ### Finitely many increments, Lipschitz case -/

/-- Convex comparison of a sum whose increments are negatively quadrant dependent with their
preceding sums, for convex Lipschitz functions. -/
theorem integral_comp_sum_le_of_tail_le_of_lipschitzWith {μ : Measure Ω}
    [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ}
    {Z' : ℕ → Ω' → ℝ} (n : ℕ) (hZm : ∀ i < n, Measurable (Z i))
    (hZ : ∀ i < n, Integrable (Z i) μ) (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : ∀ i < n, IndepFun (fun ω => ∑ j ∈ range i, Z' j ω) (Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i))
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ConvexOn ℝ univ φ) (hφK : LipschitzWith K φ) :
    ∫ ω, φ (∑ i ∈ range n, Z i ω) ∂μ ≤ ∫ ω, φ (∑ i ∈ range n, Z' i ω) ∂μ' := by
  induction n generalizing φ K with
  | zero => simp
  | succ n ih =>
    have hlt : n < n + 1 := Nat.lt_succ_self n
    have hZm' : ∀ i < n, Measurable (Z i) := fun i hi => hZm i (hi.trans hlt)
    have hZ'm' : ∀ i < n, Measurable (Z' i) := fun i hi => hZ'm i (hi.trans hlt)
    have hZ' : ∀ i < n + 1, Integrable (Z' i) μ' := fun i hi => by
      have h := integrable_id_map (hZm i hi) (hZ i hi)
      rw [← hlaw i hi] at h
      exact (integrable_map_measure aestronglyMeasurable_id (hZ'm i hi).aemeasurable).1 h
    set S : Ω → ℝ := fun ω => ∑ j ∈ range n, Z j ω with hS
    set S' : Ω' → ℝ := fun ω => ∑ j ∈ range n, Z' j ω with hS'
    have hSm : Measurable S :=
      Finset.measurable_sum _ fun i hi => hZm' i (Finset.mem_range.1 hi)
    have hS'm : Measurable S' :=
      Finset.measurable_sum _ fun i hi => hZ'm' i (Finset.mem_range.1 hi)
    have hSi : Integrable S μ :=
      integrable_finsetSum _ fun i hi => hZ i ((Finset.mem_range.1 hi).trans hlt)
    have hS'i : Integrable S' μ' :=
      integrable_finsetSum _ fun i hi => hZ' i ((Finset.mem_range.1 hi).trans hlt)
    have htail' : ∀ u v, μ.real ({ω | u ≤ S ω} ∩ {ω | v ≤ Z n ω}) ≤
        μ.real {ω | u ≤ S ω} * μ.real {ω | v ≤ Z n ω} := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · intro u v
        subst h0
        by_cases hu : u ≤ 0
        · simp [hS, hu]
        · simp [hS, hu]
      · exact htail n hpos hlt
    simp only [Finset.sum_range_succ]
    set ν := μ.map (Z n) with hν
    have hνi : Integrable (fun y => y) ν := integrable_id_map (hZm n hlt) (hZ n hlt)
    set g : ℝ → ℝ := fun x => ∫ y, φ (x + y) ∂ν with hg
    have hgc : ConvexOn ℝ univ g := convexOn_integral_comp_add hνi hφ hφK
    have hgK : LipschitzWith K g := lipschitzWith_integral_comp_add hνi hφK
    have hprod : ∀ {P : Measure ℝ} [IsProbabilityMeasure P], Integrable (fun x => x) P →
        Integrable (fun p : ℝ × ℝ => φ (p.1 + p.2)) (P.prod ν) := fun hP =>
      integrable_comp_of_lipschitzWith ((hP.comp_fst ν).add (hνi.comp_snd _)) hφK
    have h1 := integral_comp_add_le_integral_prod_of_tail_le hSm (hZm n hlt) hSi (hZ n hlt)
      htail' hφ hφK
    rw [integral_prod _ (hprod (integrable_id_map hSm hSi)),
      integral_map hSm.aemeasurable hgK.continuous.aestronglyMeasurable] at h1
    have h2 := ih hZm' (fun i hi => hZ i (hi.trans hlt)) hZ'm'
      (fun i hi1 hi2 => htail i hi1 (hi2.trans hlt)) (fun i hi => hind i (hi.trans hlt))
      (fun i hi => hlaw i (hi.trans hlt)) hgc hgK
    have h3 : ∫ ω, g (S' ω) ∂μ' = ∫ ω, φ (S' ω + Z' n ω) ∂μ' := by
      rw [← integral_map hS'm.aemeasurable hgK.continuous.aestronglyMeasurable,
        ← integral_prod _ (hprod (integrable_id_map hS'm hS'i)), hν, ← hlaw n hlt,
        ← (hind n hlt).map_prod_eq_prod_map_map hS'm.aemeasurable (hZ'm n hlt).aemeasurable,
        integral_map (f := fun z : ℝ × ℝ => φ (z.1 + z.2))
          (hS'm.prodMk (hZ'm n hlt)).aemeasurable
          (hφK.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable]
    exact h1.trans (h2.trans h3.le)


/-! ### Supporting lines and Lipschitz approximation from below -/

/-- A convex function on `ℝ` lies above its tangent line with the right derivative as slope. -/
theorem ConvexOn.add_rightDeriv_mul_sub_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) (c x : ℝ) :
    φ c + derivWithin φ (Ioi c) c * (x - c) ≤ φ x := by
  have hc : c ∈ interior (univ : Set ℝ) := by simp
  rcases lt_trichotomy c x with h | rfl | h
  · have := hφ.rightDeriv_le_slope (mem_univ c) (mem_univ x) h
      (hφ.differentiableWithinAt_Ioi_of_mem_interior hc)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    linarith
  · simp
  · have h1 := hφ.slope_le_leftDeriv_of_mem_interior (mem_univ x) hc h
    have h2 := hφ.leftDeriv_le_rightDeriv_of_mem_interior hc
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at h1
    nlinarith [mul_le_mul_of_nonneg_right h2 (sub_pos.2 h).le]

/-- A convex function on `ℝ` is the increasing pointwise limit of convex Lipschitz functions,
each lying between a fixed affine function and the function itself. -/
theorem ConvexOn.exists_lipschitzWith_tendsto {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    ∃ F : ℕ → ℝ → ℝ, (∀ m, ConvexOn ℝ univ (F m)) ∧ (∀ m, ∃ K, LipschitzWith K (F m)) ∧
      (∀ x, Monotone fun m => F m x) ∧ (∀ m x, F m x ≤ φ x) ∧
      (∀ x, Tendsto (fun m => F m x) atTop (𝓝 (φ x))) ∧ ∃ a b : ℝ, ∀ x, F 0 x = a + b * x := by
  set σ : ℝ → ℝ := fun c => derivWithin φ (Ioi c) c with hσ
  set ℓ : ℝ → ℝ → ℝ := fun c x => φ c + σ c * (x - c) with hℓ
  have hℓle : ∀ c x, ℓ c x ≤ φ x := fun c x => ConvexOn.add_rightDeriv_mul_sub_le hφ c x
  have hℓc : ∀ c, ConvexOn ℝ univ (ℓ c) := fun c =>
    ⟨convex_univ, fun x _ y _ a b _ _ hab => le_of_eq (by
      simp only [hℓ, smul_eq_mul]; linear_combination (σ c * c - φ c) * hab)⟩
  have hℓK : ∀ c, LipschitzWith ‖σ c‖₊ (ℓ c) := fun c =>
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [hℓ, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
      rw [show φ c + σ c * (x - c) - (φ c + σ c * (y - c)) = σ c * (x - y) by ring, abs_mul]
  set e : ℕ → ℝ := fun i => ((Denumerable.ofNat ℚ i : ℚ) : ℝ) with he
  set F : ℕ → ℝ → ℝ := fun m =>
    Nat.rec (motive := fun _ => ℝ → ℝ) (ℓ 0) (fun k Fk x => max (Fk x) (ℓ (e k) x)) m with hF
  have hFs : ∀ m x, F (m + 1) x = max (F m x) (ℓ (e m) x) := fun _ _ => rfl
  have hFle : ∀ m x, F m x ≤ φ x := by
    intro m; induction m with
    | zero => exact hℓle 0
    | succ m ih => intro x; rw [hFs]; exact max_le (ih x) (hℓle _ x)
  have hFge : ∀ i m, i < m → ∀ x, ℓ (e i) x ≤ F m x := by
    intro i m; induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h x
      rw [hFs]
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
      · exact (ih h x).trans (le_max_left _ _)
      · exact le_max_right _ _
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  refine ⟨F, fun m => ?_, fun m => ?_, fun x => monotone_nat_of_le_succ fun m => ?_, hFle,
    fun x => ?_, φ 0 - σ 0 * 0, σ 0, fun x => by simp [hF, hℓ]⟩
  · induction m with
    | zero => exact hℓc 0
    | succ m ih => exact ih.sup (hℓc _)
  · induction m with
    | zero => exact ⟨_, hℓK 0⟩
    | succ m ih =>
      obtain ⟨K, hK⟩ := ih
      exact ⟨_, hK.max (hℓK _)⟩
  · rw [hFs]; exact le_max_left _ _
  · rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun m => (hFle m x).trans_lt ha⟩
    set B := max |σ (x - 1)| |σ (x + 1)| with hB
    have hσB : ∀ c ∈ Icc (x - 1) (x + 1), |σ c| ≤ B := fun c hc => by
      have hmono := hφ.monotoneOn_rightDeriv
      rw [interior_univ] at hmono
      exact abs_le_max_abs_abs (hmono (mem_univ _) (mem_univ _) hc.1)
        (hmono (mem_univ _) (mem_univ _) hc.2)
    set U := {c : ℝ | a < φ c - B * |x - c|} ∩ Ioo (x - 1) (x + 1) with hU
    have hUo : IsOpen U := (isOpen_lt continuous_const (hcont.sub (continuous_const.mul
      (continuous_const.sub continuous_id).abs))).inter isOpen_Ioo
    have hxU : x ∈ U := ⟨by simp [ha], by constructor <;> linarith⟩
    obtain ⟨q, hq⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_mem_open hUo ⟨x, hxU⟩
    obtain ⟨i, hi⟩ : ∃ i, e i = q := by
      obtain ⟨i, hi⟩ := (Denumerable.eqv ℚ).symm.surjective q
      exact ⟨i, by rw [he, ← hi]; rfl⟩
    have hlt : a < ℓ (e i) x := by
      rw [hi]
      have hb := hσB q ⟨hq.2.1.le, hq.2.2.le⟩
      have h1 := neg_abs_le (σ q * (x - q))
      have h2 : |σ q * (x - q)| ≤ B * |x - q| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      have h3 : a < φ q - B * |x - q| := hq.1
      simp only [hℓ]
      linarith
    filter_upwards [eventually_gt_atTop i] with m hm
    exact hlt.trans_le (hFge i m hm x)

/-- Monotone convergence along the approximants of `ConvexOn.exists_lipschitzWith_tendsto`. -/
theorem tendsto_ofReal_integral_sub_of_tendsto {ρ : Measure γ} [IsProbabilityMeasure ρ]
    {Y : γ → ℝ} (hYm : AEMeasurable Y ρ) (hY : Integrable Y ρ) {φ : ℝ → ℝ}
    {F : ℕ → ℝ → ℝ} (hFK : ∀ m, ∃ K, LipschitzWith K (F m)) (hFm : ∀ x, Monotone fun m => F m x)
    (hFt : ∀ x, Tendsto (fun m => F m x) atTop (𝓝 (φ x))) :
    Tendsto (fun m => ENNReal.ofReal (∫ t, (F m (Y t) - F 0 (Y t)) ∂ρ)) atTop
      (𝓝 (∫⁻ t, ENNReal.ofReal (φ (Y t) - F 0 (Y t)) ∂ρ)) := by
  have hint : ∀ m, Integrable (fun t => F m (Y t) - F 0 (Y t)) ρ := fun m => by
    obtain ⟨K, hK⟩ := hFK m
    obtain ⟨K0, hK0⟩ := hFK 0
    exact (integrable_comp_of_lipschitzWith hY hK).sub (integrable_comp_of_lipschitzWith hY hK0)
  have hnn : ∀ m t, 0 ≤ F m (Y t) - F 0 (Y t) := fun m t =>
    sub_nonneg.2 (hFm _ (Nat.zero_le m))
  have hcF : ∀ m, Continuous (F m) := fun m => (hFK m).choose_spec.continuous
  simp_rw [fun m => ofReal_integral_eq_lintegral_ofReal (hint m) (Eventually.of_forall (hnn m))]
  refine lintegral_tendsto_of_tendsto_of_monotone (fun m => ?_) (Eventually.of_forall fun t =>
    fun m m' hmm' => ENNReal.ofReal_le_ofReal (sub_le_sub_right (hFm _ hmm') _))
    (Eventually.of_forall fun t => ?_)
  · exact ENNReal.measurable_ofReal.comp_aemeasurable
      (((hcF m).measurable.comp_aemeasurable hYm).sub ((hcF 0).measurable.comp_aemeasurable hYm))
  · exact (ENNReal.continuous_ofReal.tendsto _).comp ((hFt _).sub tendsto_const_nhds)

/-- **From Lipschitz to general convex comparison.** If `E ψ(X) ≤ E ψ(X')` for every convex
Lipschitz `ψ`, then for every convex `φ` the negative parts of `φ(X)` and `φ(X')` are
integrable, and integrability of `φ(X')` implies that of `φ(X)` with `E φ(X) ≤ E φ(X')`; that
is, `E φ(X) ≤ E φ(X')` as extended expectations in `(-∞, ∞]`. -/
theorem convex_comparison_of_lipschitzWith_comparison {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {X : Ω → ℝ} {X' : Ω' → ℝ}
    (hXm : AEMeasurable X μ) (hX'm : AEMeasurable X' μ') (hX : Integrable X μ)
    (hX' : Integrable X' μ')
    (h : ∀ (ψ : ℝ → ℝ) (K : ℝ≥0), ConvexOn ℝ univ ψ → LipschitzWith K ψ →
      ∫ ω, ψ (X ω) ∂μ ≤ ∫ ω, ψ (X' ω) ∂μ')
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    Integrable (fun ω => (φ (X ω))⁻) μ ∧ Integrable (fun ω => (φ (X' ω))⁻) μ' ∧
      (Integrable (fun ω => φ (X' ω)) μ' →
        Integrable (fun ω => φ (X ω)) μ ∧ ∫ ω, φ (X ω) ∂μ ≤ ∫ ω, φ (X' ω) ∂μ') := by
  obtain ⟨F, hFc, hFK, hFm, hFle, hFt, a, b, hF0⟩ := ConvexOn.exists_lipschitzWith_tendsto hφ
  have hcont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  obtain ⟨K0, hK0⟩ := hFK 0
  have hF0X : Integrable (fun ω => F 0 (X ω)) μ := integrable_comp_of_lipschitzWith hX hK0
  have hF0X' : Integrable (fun ω => F 0 (X' ω)) μ' := integrable_comp_of_lipschitzWith hX' hK0
  -- equal means of the affine minorant
  have hmean : ∫ ω, X ω ∂μ = ∫ ω, X' ω ∂μ' := by
    refine le_antisymm (h id 1 (convexOn_id convex_univ) LipschitzWith.id) ?_
    have := h (fun x => -x) 1 (concaveOn_id convex_univ).neg LipschitzWith.id.neg
    simp only [integral_neg] at this
    linarith
  have hF0mean : ∫ ω, F 0 (X ω) ∂μ = ∫ ω, F 0 (X' ω) ∂μ' := by
    simp only [hF0]
    rw [integral_add (integrable_const _) (hX.const_mul _),
      integral_add (integrable_const _) (hX'.const_mul _), integral_const_mul,
      integral_const_mul, hmean]
    simp
  have hneg : ∀ y, ‖(φ y)⁻‖ ≤ |F 0 y| := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (negPart_nonneg _), negPart_def]
    exact max_le (by linarith [neg_abs_le (F 0 y), hFle 0 y]) (abs_nonneg _)
  refine ⟨hF0X.abs.mono' (hcont.measurable.comp_aemeasurable hXm).aestronglyMeasurable.negPart
      (Eventually.of_forall fun ω => hneg _),
    hF0X'.abs.mono' (hcont.measurable.comp_aemeasurable hX'm).aestronglyMeasurable.negPart
      (Eventually.of_forall fun ω => hneg _), fun hφX' => ?_⟩
  have hL := tendsto_ofReal_integral_sub_of_tendsto hXm hX hFK hFm hFt
  have hL' := tendsto_ofReal_integral_sub_of_tendsto hX'm hX' hFK hFm hFt
  have hle := le_of_tendsto_of_tendsto' hL hL' fun m => by
    obtain ⟨K, hK⟩ := hFK m
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_sub (integrable_comp_of_lipschitzWith hX hK) hF0X,
      integral_sub (integrable_comp_of_lipschitzWith hX' hK) hF0X', hF0mean]
    linarith [h (F m) K (hFc m) hK]
  have hnn : ∀ y, 0 ≤ φ y - F 0 y := fun y => sub_nonneg.2 (hFle 0 y)
  have hD' : Integrable (fun ω => φ (X' ω) - F 0 (X' ω)) μ' := hφX'.sub hF0X'
  have hE' := ofReal_integral_eq_lintegral_ofReal hD' (Eventually.of_forall fun ω => hnn _)
  have htop : ∫⁻ ω, ENNReal.ofReal (φ (X ω) - F 0 (X ω)) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (hE' ▸ ENNReal.ofReal_ne_top) hle
  have hD : Integrable (fun ω => φ (X ω) - F 0 (X ω)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((hcont.measurable.comp_aemeasurable hXm).aestronglyMeasurable.sub hF0X.1)
      (Eventually.of_forall fun ω => hnn _)).1 htop
  have hE := ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall fun ω => hnn _)
  have hφX : Integrable (fun ω => φ (X ω)) μ :=
    (hD.add hF0X).congr (Eventually.of_forall fun ω => by simp)
  refine ⟨hφX, ?_⟩
  rw [← hE, ← hE'] at hle
  have := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => hnn _)).1 hle
  rw [integral_sub hφX hF0X, integral_sub hφX' hF0X', hF0mean] at this
  linarith


/-! ### Finitely many increments: the general statement -/

theorem integrable_of_map_eq {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {X' : Ω' → ℝ}
    (hXm : Measurable X) (hX'm : Measurable X') (hX : Integrable X μ)
    (h : μ'.map X' = μ.map X) : Integrable X' μ' := by
  have h' := integrable_id_map hXm hX
  rw [← h] at h'
  exact (integrable_map_measure aestronglyMeasurable_id hX'm.aemeasurable).1 h'

/-- Independence of a family indexed by `Fin n` makes each member independent of the sum of
the preceding ones. -/
theorem indepFun_sum_range_of_iIndepFun {μ' : Measure Ω'} {Z' : ℕ → Ω' → ℝ} {n : ℕ}
    (h : iIndepFun (fun i : Fin n => Z' i) μ') (hm : ∀ i < n, Measurable (Z' i)) {i : ℕ}
    (hi : i < n) : IndepFun (fun ω => ∑ j ∈ range i, Z' j ω) (Z' i) μ' := by
  have := h.indepFun_finsetSum_of_notMem (fun j => hm j j.2)
    (s := univ.filter (fun j : Fin n => j.val < i)) (i := ⟨i, hi⟩) (by simp)
  convert this using 1
  ext ω
  rw [Finset.sum_apply]
  refine Finset.sum_bij (fun j hj => (⟨j, (Finset.mem_range.1 hj).trans hi⟩ : Fin n))
    (fun j hj => by simpa using Finset.mem_range.1 hj) (fun a _ b _ hab => by simpa using hab)
    (fun b hb => ⟨b.val, by simpa using hb, rfl⟩) (fun j _ => rfl)

theorem integral_comp_sum_le_of_tail_le_of_iIndepFun_of_lipschitzWith
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} {n : ℕ}
    (hZm : ∀ i < n, Measurable (Z i)) (hZ : ∀ i < n, Integrable (Z i) μ)
    (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i))
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ConvexOn ℝ univ φ) (hφK : LipschitzWith K φ) :
    ∫ ω, φ (∑ i ∈ range n, Z i ω) ∂μ ≤ ∫ ω, φ (∑ i ∈ range n, Z' i ω) ∂μ' :=
  integral_comp_sum_le_of_tail_le_of_lipschitzWith n hZm hZ hZ'm htail
    (fun _ hi => indepFun_sum_range_of_iIndepFun hind hZ'm hi) hlaw hφ hφK

/-- **Convex comparison for increments negatively quadrant dependent with their preceding
sums.** Let `Z₀, …, Z_{n-1}` be integrable with
`P(S_i ≥ u, Z_i ≥ v) ≤ P(S_i ≥ u) P(Z_i ≥ v)` for `1 ≤ i < n`, where `S_i = ∑_{j<i} Z_j`, and
let `Z'_i` be independent with the same marginal laws. For every convex `φ : ℝ → ℝ`, the
negative parts of `φ(S_n)` and `φ(S'_n)` are integrable, and if `φ(S'_n)` is integrable then
so is `φ(S_n)` with `E φ(S_n) ≤ E φ(S'_n)`: the comparison holds in `(-∞, ∞]`. -/
theorem convex_comparison_sum_of_tail_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} {n : ℕ}
    (hZm : ∀ i < n, Measurable (Z i)) (hZ : ∀ i < n, Integrable (Z i) μ)
    (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i))
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    Integrable (fun ω => (φ (∑ i ∈ range n, Z i ω))⁻) μ ∧
      Integrable (fun ω => (φ (∑ i ∈ range n, Z' i ω))⁻) μ' ∧
      (Integrable (fun ω => φ (∑ i ∈ range n, Z' i ω)) μ' →
        Integrable (fun ω => φ (∑ i ∈ range n, Z i ω)) μ ∧
          ∫ ω, φ (∑ i ∈ range n, Z i ω) ∂μ ≤ ∫ ω, φ (∑ i ∈ range n, Z' i ω) ∂μ') :=
  convex_comparison_of_lipschitzWith_comparison
    (Finset.measurable_sum _ fun i hi => hZm i (Finset.mem_range.1 hi)).aemeasurable
    (Finset.measurable_sum _ fun i hi => hZ'm i (Finset.mem_range.1 hi)).aemeasurable
    (integrable_finsetSum _ fun i hi => hZ i (Finset.mem_range.1 hi))
    (integrable_finsetSum _ fun i hi => integrable_of_map_eq (hZm i (Finset.mem_range.1 hi))
      (hZ'm i (Finset.mem_range.1 hi)) (hZ i (Finset.mem_range.1 hi))
      (hlaw i (Finset.mem_range.1 hi)))
    (fun _ _ hψ hψK => integral_comp_sum_le_of_tail_le_of_iIndepFun_of_lipschitzWith hZm hZ hZ'm
      htail hind hlaw hψ hψK) hφ

/-- Equal means of the two sums. -/
theorem integral_sum_eq_of_tail_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} {n : ℕ}
    (hZm : ∀ i < n, Measurable (Z i)) (hZ : ∀ i < n, Integrable (Z i) μ)
    (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i)) :
    ∫ ω, ∑ i ∈ range n, Z i ω ∂μ = ∫ ω, ∑ i ∈ range n, Z' i ω ∂μ' := by
  refine le_antisymm (integral_comp_sum_le_of_tail_le_of_iIndepFun_of_lipschitzWith
    (φ := id) hZm hZ hZ'm htail hind hlaw (convexOn_id convex_univ) LipschitzWith.id) ?_
  have := integral_comp_sum_le_of_tail_le_of_iIndepFun_of_lipschitzWith (φ := fun x => -x)
    hZm hZ hZ'm htail hind hlaw (concaveOn_id convex_univ).neg LipschitzWith.id.neg
  simp only [integral_neg] at this
  linarith

/-- The hinge comparison `E (S_n - a)₊ ≤ E (S'_n - a)₊`. -/
theorem integral_max_sub_le_of_tail_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} {n : ℕ}
    (hZm : ∀ i < n, Measurable (Z i)) (hZ : ∀ i < n, Integrable (Z i) μ)
    (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i)) (a : ℝ) :
    ∫ ω, max (∑ i ∈ range n, Z i ω - a) 0 ∂μ ≤ ∫ ω, max (∑ i ∈ range n, Z' i ω - a) 0 ∂μ' := by
  have hc : ConvexOn ℝ univ ((fun x : ℝ => x - a) ⊔ fun _ => (0 : ℝ)) :=
    ConvexOn.sup ⟨convex_univ, fun x _ y _ p q _ _ hpq => le_of_eq (by
      simp only [smul_eq_mul]; linear_combination a * hpq)⟩ (convexOn_const 0 convex_univ)
  have hl : LipschitzWith 1 fun x : ℝ => max (x - a) 0 :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      have := abs_max_sub_max_le_abs (x - a) (y - a) 0
      rwa [sub_sub_sub_cancel_right] at this
  exact integral_comp_sum_le_of_tail_le_of_iIndepFun_of_lipschitzWith hZm hZ hZ'm htail hind
    hlaw hc hl

/-- `x ↦ |x - c| ^ r` is convex for `r ≥ 1`. -/
theorem convexOn_abs_sub_rpow (c : ℝ) {r : ℝ} (hr : 1 ≤ r) :
    ConvexOn ℝ univ fun x : ℝ => |x - c| ^ r := by
  have habs : ConvexOn ℝ univ fun x : ℝ => |x - c| :=
    ⟨convex_univ, fun x _ y _ p q hp hq hpq => by
      simp only [smul_eq_mul]
      calc |p * x + q * y - c| = |p * (x - c) + q * (y - c)| := by
            congr 1; linear_combination c * hpq
        _ ≤ |p * (x - c)| + |q * (y - c)| := abs_add_le _ _
        _ = p * |x - c| + q * |y - c| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]⟩
  have himg : (fun x : ℝ => |x - c|) '' univ = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩; exact abs_nonneg _
    · intro hy; exact ⟨c + y, mem_univ _, by simp [abs_of_nonneg (Set.mem_Ici.1 hy)]⟩
  have h1 : ConvexOn ℝ ((fun x : ℝ => |x - c|) '' univ) fun x : ℝ => x ^ r := by
    rw [himg]; exact convexOn_rpow hr
  have h2 : MonotoneOn (fun x : ℝ => x ^ r) ((fun x : ℝ => |x - c|) '' univ) := by
    rw [himg]; exact fun x hx y _ hxy => Real.rpow_le_rpow hx hxy (by linarith)
  exact h1.comp habs h2

/-- The central moment comparison `E |S_n - E S_n|^r ≤ E |S'_n - E S'_n|^r` for `r ≥ 1`, as
lower Lebesgue integrals (either side may be infinite). -/
theorem lintegral_abs_sub_integral_rpow_le_of_tail_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} {n : ℕ}
    (hZm : ∀ i < n, Measurable (Z i)) (hZ : ∀ i < n, Integrable (Z i) μ)
    (hZ'm : ∀ i < n, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → i < n → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hind : iIndepFun (fun i : Fin n => Z' i) μ')
    (hlaw : ∀ i < n, μ'.map (Z' i) = μ.map (Z i)) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range n, Z i ω - ∫ ω', ∑ i ∈ range n, Z i ω' ∂μ| ^ r) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range n, Z' i ω - ∫ ω', ∑ i ∈ range n, Z' i ω' ∂μ'| ^ r)
        ∂μ' := by
  rw [integral_sum_eq_of_tail_le hZm hZ hZ'm htail hind hlaw]
  set c := ∫ ω', ∑ i ∈ range n, Z' i ω' ∂μ'
  have ext := convex_comparison_sum_of_tail_le hZm hZ hZ'm htail hind hlaw
    (convexOn_abs_sub_rpow c hr)
  by_cases htop : ∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range n, Z' i ω - c| ^ r) ∂μ' = ⊤
  · rw [htop]; exact le_top
  have hnn : ∀ t : ℝ, 0 ≤ |t - c| ^ r := fun t => Real.rpow_nonneg (abs_nonneg _) r
  have hS'm : Measurable fun ω => ∑ i ∈ range n, Z' i ω :=
    Finset.measurable_sum _ fun i hi => hZ'm i (Finset.mem_range.1 hi)
  have hI' : Integrable (fun ω => |∑ i ∈ range n, Z' i ω - c| ^ r) μ' :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((continuous_abs.measurable.comp (hS'm.sub_const c)).pow_const r).aestronglyMeasurable
      (Eventually.of_forall fun ω => hnn _)).1 htop
  obtain ⟨hI, hle⟩ := ext.2.2 hI'
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun ω => hnn _),
    ← ofReal_integral_eq_lintegral_ofReal hI' (Eventually.of_forall fun ω => hnn _)]
  exact ENNReal.ofReal_le_ofReal hle


/-! ### Absolutely summable sequences -/

/-- A nonnegative comparison `E f ≤ E f'` stated through integrability transfers to lower
Lebesgue integrals. -/
theorem lintegral_ofReal_le_of_integrable_imp {ρ : Measure γ} {ρ' : Measure α} {f : γ → ℝ}
    {f' : α → ℝ} (hf'm : AEStronglyMeasurable f' ρ') (hf0 : ∀ w, 0 ≤ f w)
    (hf'0 : ∀ w, 0 ≤ f' w) (h : Integrable f' ρ' → Integrable f ρ ∧ ∫ w, f w ∂ρ ≤ ∫ w, f' w ∂ρ') :
    ∫⁻ w, ENNReal.ofReal (f w) ∂ρ ≤ ∫⁻ w, ENNReal.ofReal (f' w) ∂ρ' := by
  by_cases htop : ∫⁻ w, ENNReal.ofReal (f' w) ∂ρ' = ⊤
  · rw [htop]; exact le_top
  have hI' := (lintegral_ofReal_ne_top_iff_integrable hf'm (Eventually.of_forall hf'0)).1 htop
  obtain ⟨hI, hle⟩ := h hI'
  rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hI' (Eventually.of_forall hf'0)]
  exact ENNReal.ofReal_le_ofReal hle

/-- If `∑ E |Y_i| < ∞`, the series `∑ Y_i` converges absolutely almost everywhere, its sum is
integrable, and the partial sums converge to it in `L¹`. -/
theorem ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum {ρ : Measure γ}
    {Y : ℕ → γ → ℝ} (hY : ∀ i, Integrable (Y i) ρ)
    (hsum : Summable fun i => ∫ w, |Y i w| ∂ρ) :
    (∀ᵐ w ∂ρ, Summable fun i => |Y i w|) ∧ Integrable (fun w => ∑' i, Y i w) ρ ∧
      Tendsto (fun n => ∫ w, |∑ i ∈ range n, Y i w - ∑' i, Y i w| ∂ρ) atTop (𝓝 0) := by
  have hmeas : ∀ i, AEMeasurable (fun w => ENNReal.ofReal |Y i w|) ρ := fun i =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable (hY i).1.aemeasurable)
  have hlin : ∫⁻ w, ∑' i, ENNReal.ofReal |Y i w| ∂ρ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    simp_rw [fun i => (ofReal_integral_eq_lintegral_ofReal (hY i).abs
      (Eventually.of_forall fun w => abs_nonneg (Y i w))).symm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun w => abs_nonneg _) hsum]
    exact ENNReal.ofReal_ne_top
  have hfin : ∀ᵐ w ∂ρ, ∑' i, ENNReal.ofReal |Y i w| ≠ ⊤ :=
    (ae_lt_top' (AEMeasurable.tsum hmeas) hlin).mono fun w hw => hw.ne
  have hsumm : ∀ᵐ w ∂ρ, Summable fun i => |Y i w| := hfin.mono fun w hw =>
    (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 hw)).congr
      fun i => Real.coe_toNNReal _ (abs_nonneg _)
  set G : γ → ℝ := fun w => ∑' i, |Y i w| with hG
  have hGeq : ∀ w, G w = (∑' i, ENNReal.ofReal |Y i w|).toReal := fun w => by
    rw [ENNReal.tsum_toReal_eq fun i => ENNReal.ofReal_ne_top]
    exact tsum_congr fun i => (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hGi : Integrable G ρ := by
    rw [show G = fun w => (∑' i, ENNReal.ofReal |Y i w|).toReal from funext hGeq]
    exact integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hmeas) hlin
  have hlim : ∀ᵐ w ∂ρ, Tendsto (fun n => ∑ i ∈ range n, Y i w) atTop (𝓝 (∑' i, Y i w)) :=
    hsumm.mono fun w hw => (Summable.of_abs hw).hasSum.tendsto_sum_nat
  have hSm : AEStronglyMeasurable (fun w => ∑' i, Y i w) ρ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (integrable_finsetSum (range n) fun i _ => hY i).1) hlim
  have hpart : ∀ᵐ w ∂ρ, ∀ n, |∑ i ∈ range n, Y i w| ≤ G w := hsumm.mono fun w hw n =>
    (Finset.abs_sum_le_sum_abs _ _).trans (hw.sum_le_tsum _ fun i _ => abs_nonneg _)
  have htot : ∀ᵐ w ∂ρ, |∑' i, Y i w| ≤ G w := hsumm.mono fun w hw => by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun i => Y i w)
      (by simpa [Real.norm_eq_abs] using hw)
  refine ⟨hsumm, hGi.mono' hSm (htot.mono fun w hw => by rwa [Real.norm_eq_abs]), ?_⟩
  have := tendsto_integral_of_dominated_convergence (fun w => 2 * G w)
    (F := fun n w => |∑ i ∈ range n, Y i w - ∑' i, Y i w|) (f := fun _ => (0 : ℝ))
    (fun n => continuous_abs.comp_aestronglyMeasurable
      ((integrable_finsetSum (range n) fun i _ => hY i).1.sub hSm))
    (hGi.const_mul 2)
    (fun n => (hpart.and htot).mono fun w ⟨h1, h2⟩ => by
      rw [Real.norm_eq_abs, abs_abs]
      linarith [abs_sub (∑ i ∈ range n, Y i w) (∑' i, Y i w), h1 n])
    (hlim.mono fun w hw => by
      simpa using (hw.sub_const (∑' i, Y i w)).abs)
  simpa using this

/-- `L¹` convergence carries integrals of a Lipschitz function. -/
theorem tendsto_integral_comp_of_tendsto_integral_abs_sub {ρ : Measure γ} [IsFiniteMeasure ρ]
    {X : ℕ → γ → ℝ} {Y : γ → ℝ} (hX : ∀ n, Integrable (X n) ρ) (hY : Integrable Y ρ)
    (hlim : Tendsto (fun n => ∫ w, |X n w - Y w| ∂ρ) atTop (𝓝 0)) {ψ : ℝ → ℝ} {K : ℝ≥0}
    (hψ : LipschitzWith K ψ) :
    Tendsto (fun n => ∫ w, ψ (X n w) ∂ρ) atTop (𝓝 (∫ w, ψ (Y w) ∂ρ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (by simpa using hlim.const_mul (K : ℝ))
  rw [Real.dist_eq, ← integral_sub (integrable_comp_of_lipschitzWith (hX n) hψ)
    (integrable_comp_of_lipschitzWith hY hψ), ← integral_const_mul]
  refine abs_integral_le_integral_abs.trans (integral_mono
    ((integrable_comp_of_lipschitzWith (hX n) hψ).sub
      (integrable_comp_of_lipschitzWith hY hψ)).abs (((hX n).sub hY).abs.const_mul _)
    fun w => ?_)
  have := hψ.dist_le_mul (X n w) (Y w)
  rwa [Real.dist_eq, Real.dist_eq] at this


theorem integral_comp_eq_of_map_eq {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {X' : Ω' → ℝ}
    (hXm : Measurable X) (hX'm : Measurable X') (h : μ'.map X' = μ.map X) {f : ℝ → ℝ}
    (hf : Continuous f) : ∫ ω, f (X' ω) ∂μ' = ∫ ω, f (X ω) ∂μ := by
  rw [← integral_map hX'm.aemeasurable hf.aestronglyMeasurable, h,
    integral_map hXm.aemeasurable hf.aestronglyMeasurable]

theorem summable_integral_abs_of_map_eq {μ : Measure Ω} {μ' : Measure Ω'} {Z : ℕ → Ω → ℝ}
    {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i)) (hZ'm : ∀ i, Measurable (Z' i))
    (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ) (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i)) :
    Summable fun i => ∫ ω, |Z' i ω| ∂μ' :=
  hsum.congr fun i =>
    (integral_comp_eq_of_map_eq (hZm i) (hZ'm i) (hlaw i) continuous_abs).symm

/-- Equal finite means of the two series. -/
theorem integral_tsum_eq_of_map_eq {μ : Measure Ω} {μ' : Measure Ω'} {Z : ℕ → Ω → ℝ}
    {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i)) (hZ : ∀ i, Integrable (Z i) μ)
    (hZ'm : ∀ i, Measurable (Z' i)) (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ)
    (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i)) :
    ∫ ω, ∑' i, Z i ω ∂μ = ∫ ω, ∑' i, Z' i ω ∂μ' := by
  have hZ' : ∀ i, Integrable (Z' i) μ' := fun i =>
    integrable_of_map_eq (hZm i) (hZ'm i) (hZ i) (hlaw i)
  rw [← integral_tsum_of_summable_integral_norm hZ (by simpa [Real.norm_eq_abs] using hsum),
    ← integral_tsum_of_summable_integral_norm hZ' (by
      simpa [Real.norm_eq_abs] using summable_integral_abs_of_map_eq hZm hZ'm hsum hlaw)]
  exact tsum_congr fun i =>
    (integral_comp_eq_of_map_eq (hZm i) (hZ'm i) (hlaw i) continuous_id).symm

theorem integral_comp_tsum_le_of_tail_le_of_lipschitzWith
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, Integrable (Z i) μ) (hZ'm : ∀ i, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ) (hind : iIndepFun Z' μ')
    (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i))
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : ConvexOn ℝ univ φ) (hφK : LipschitzWith K φ) :
    ∫ ω, φ (∑' i, Z i ω) ∂μ ≤ ∫ ω, φ (∑' i, Z' i ω) ∂μ' := by
  have hZ' : ∀ i, Integrable (Z' i) μ' := fun i =>
    integrable_of_map_eq (hZm i) (hZ'm i) (hZ i) (hlaw i)
  obtain ⟨-, hS, hL⟩ := ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ hsum
  obtain ⟨-, hS', hL'⟩ := ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ'
    (summable_integral_abs_of_map_eq hZm hZ'm hsum hlaw)
  refine le_of_tendsto_of_tendsto'
    (tendsto_integral_comp_of_tendsto_integral_abs_sub
      (fun n => integrable_finsetSum (range n) fun i _ => hZ i) hS hL hφK)
    (tendsto_integral_comp_of_tendsto_integral_abs_sub
      (fun n => integrable_finsetSum (range n) fun i _ => hZ' i) hS' hL' hφK) fun n => ?_
  exact integral_comp_sum_le_of_tail_le_of_iIndepFun_of_lipschitzWith (n := n)
    (fun i _ => hZm i) (fun i _ => hZ i) (fun i _ => hZ'm i) (fun i h1 _ => htail i h1)
    (hind.precomp Fin.val_injective) (fun i _ => hlaw i) hφ hφK

/-- **Convex comparison for absolutely integrable series.** Under the hypotheses of
`convex_comparison_sum_of_tail_le` at every finite index and `∑ E |Z_i| < ∞`, the sums
`S = ∑ Z_i` and `S' = ∑ Z'_i` satisfy `E φ(S) ≤ E φ(S')` in `(-∞, ∞]` for every convex `φ`. -/
theorem convex_comparison_tsum_of_tail_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, Integrable (Z i) μ) (hZ'm : ∀ i, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ) (hind : iIndepFun Z' μ')
    (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i))
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ univ φ) :
    Integrable (fun ω => (φ (∑' i, Z i ω))⁻) μ ∧
      Integrable (fun ω => (φ (∑' i, Z' i ω))⁻) μ' ∧
      (Integrable (fun ω => φ (∑' i, Z' i ω)) μ' →
        Integrable (fun ω => φ (∑' i, Z i ω)) μ ∧
          ∫ ω, φ (∑' i, Z i ω) ∂μ ≤ ∫ ω, φ (∑' i, Z' i ω) ∂μ') := by
  have hZ' : ∀ i, Integrable (Z' i) μ' := fun i =>
    integrable_of_map_eq (hZm i) (hZ'm i) (hZ i) (hlaw i)
  obtain ⟨-, hS, -⟩ := ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ hsum
  obtain ⟨-, hS', -⟩ := ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ'
    (summable_integral_abs_of_map_eq hZm hZ'm hsum hlaw)
  exact convex_comparison_of_lipschitzWith_comparison hS.1.aemeasurable hS'.1.aemeasurable hS
    hS'
    (fun _ _ hψ hψK => integral_comp_tsum_le_of_tail_le_of_lipschitzWith hZm hZ hZ'm htail hsum
      hind hlaw hψ hψK) hφ

/-- The exponential-moment comparison `E e^{t(S - E S)} ≤ E e^{t(S' - E S')}`. -/
theorem lintegral_exp_mul_sub_integral_le_of_tail_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, Integrable (Z i) μ) (hZ'm : ∀ i, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ) (hind : iIndepFun Z' μ')
    (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i)) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (∑' i, Z i ω - ∫ ω', ∑' i, Z i ω' ∂μ))) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (∑' i, Z' i ω - ∫ ω', ∑' i, Z' i ω' ∂μ'))) ∂μ' := by
  rw [integral_tsum_eq_of_map_eq hZm hZ hZ'm hsum hlaw]
  set c := ∫ ω', ∑' i, Z' i ω' ∂μ'
  have hc : ConvexOn ℝ univ fun x : ℝ => Real.exp (t * (x - c)) :=
    ⟨convex_univ, fun x _ y _ a b ha hb hab => by
      have := convexOn_exp.2 (mem_univ (t * (x - c))) (mem_univ (t * (y - c))) ha hb hab
      simp only [smul_eq_mul] at this ⊢
      rw [show t * (a * x + b * y - c) = a * (t * (x - c)) + b * (t * (y - c)) by
        linear_combination (t * c) * hab]
      exact this⟩
  have hZ' : ∀ i, Integrable (Z' i) μ' := fun i =>
    integrable_of_map_eq (hZm i) (hZ'm i) (hZ i) (hlaw i)
  obtain ⟨-, hS', -⟩ := ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ'
    (summable_integral_abs_of_map_eq hZm hZ'm hsum hlaw)
  exact lintegral_ofReal_le_of_integrable_imp
    ((Real.continuous_exp.comp (continuous_const.mul
      (continuous_id.sub continuous_const))).comp_aestronglyMeasurable hS'.1)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (convex_comparison_tsum_of_tail_le hZm hZ hZ'm htail hsum hind hlaw hc).2.2

/-- The central moment comparison `E |S - E S|^r ≤ E |S' - E S'|^r` for `r ≥ 1`. -/
theorem lintegral_abs_sub_integral_tsum_rpow_le_of_tail_le
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : ℕ → Ω → ℝ} {Z' : ℕ → Ω' → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i, Integrable (Z i) μ) (hZ'm : ∀ i, Measurable (Z' i))
    (htail : ∀ i, 1 ≤ i → ∀ u v,
      μ.real ({ω | u ≤ ∑ j ∈ range i, Z j ω} ∩ {ω | v ≤ Z i ω}) ≤
        μ.real {ω | u ≤ ∑ j ∈ range i, Z j ω} * μ.real {ω | v ≤ Z i ω})
    (hsum : Summable fun i => ∫ ω, |Z i ω| ∂μ) (hind : iIndepFun Z' μ')
    (hlaw : ∀ i, μ'.map (Z' i) = μ.map (Z i)) {r : ℝ}
    (hr : 1 ≤ r) :
    ∫⁻ ω, ENNReal.ofReal (|∑' i, Z i ω - ∫ ω', ∑' i, Z i ω' ∂μ| ^ r) ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (|∑' i, Z' i ω - ∫ ω', ∑' i, Z' i ω' ∂μ'| ^ r) ∂μ' := by
  rw [integral_tsum_eq_of_map_eq hZm hZ hZ'm hsum hlaw]
  set c := ∫ ω', ∑' i, Z' i ω' ∂μ'
  have hZ' : ∀ i, Integrable (Z' i) μ' := fun i =>
    integrable_of_map_eq (hZm i) (hZ'm i) (hZ i) (hlaw i)
  obtain ⟨-, hS', -⟩ := ae_summable_abs_and_tendsto_integral_abs_sum_range_sub_tsum hZ'
    (summable_integral_abs_of_map_eq hZm hZ'm hsum hlaw)
  exact lintegral_ofReal_le_of_integrable_imp
    (((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
      fun _ => Or.inr (zero_le_one.trans hr)).comp_aestronglyMeasurable hS'.1)
    (fun _ => Real.rpow_nonneg (abs_nonneg _) r) (fun _ => Real.rpow_nonneg (abs_nonneg _) r)
    (convex_comparison_tsum_of_tail_le hZm hZ hZ'm htail hsum hind hlaw
      (convexOn_abs_sub_rpow c hr)).2.2

end PercLib.Probability
