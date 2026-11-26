/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
Mathematical reference: elementary calculus (iterated integral of `(a + x + y)⁻²` and the
integral test for antitone functions).
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# The inverse-square block integral

The iterated integral of `(a + x + y)⁻²` over the square `[0, A]²`, and the resulting
logarithmic lower bound for the double sum of `(6K + i + j)⁻²` over a block of side at least
`⌊Km/2⌋`.

## Main results

* `PercLib.Analysis.integral_integral_one_div_add_add_sq`: for `a > 0`, `A ≥ 0`,
  `∫₀^A ∫₀^A (a + x + y)⁻² dy dx = log ((a + A)² / (a (a + 2A)))`.
* `PercLib.Analysis.integral_integral_one_div_add_add_sq_le_sum_sum`: integral test for the
  double sum, `∫₀^M ∫₀^M (c + 2 + x + y)⁻² ≤ ∑_{i,j=1}^M (c + i + j)⁻²` for `c ≥ 0`.
* `PercLib.Analysis.log_div_le_sum_sum_one_div_sq`: for integers `K, m ≥ 2` and
  `u, v ≥ ⌊Km/2⌋`, `log (m / 64) ≤ ∑_{i=1}^u ∑_{j=1}^v (6K + i + j)⁻²`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set intervalIntegral

namespace PercLib.Analysis

/-- The inner integral: `∫₀^A (b + y)⁻² dy = 1/b - 1/(b + A)` for `b > 0`, `A ≥ 0`. -/
theorem integral_one_div_add_sq {b A : ℝ} (hb : 0 < b) (hA : 0 ≤ A) :
    ∫ y in (0 : ℝ)..A, 1 / (b + y) ^ 2 = 1 / b - 1 / (b + A) := by
  have hderiv : ∀ y ∈ uIcc (0 : ℝ) A,
      HasDerivAt (fun y => -(b + y)⁻¹) (1 / (b + y) ^ 2) y := by
    intro y hy
    rw [uIcc_of_le hA] at hy
    have hne : b + y ≠ 0 := by linarith [hy.1]
    have := ((hasDerivAt_id y).const_add b).inv hne
    convert this.neg using 1
    · ext; simp
    · simp [neg_div]
  have hcont : ContinuousOn (fun y : ℝ => 1 / (b + y) ^ 2) (uIcc 0 A) := by
    rw [uIcc_of_le hA]
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun y hy => ?_
    have : 0 < b + y := by linarith [hy.1]
    positivity
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [add_zero, one_div]
  ring

theorem integral_integral_one_div_add_add_sq {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) :
    ∫ x in (0 : ℝ)..A, ∫ y in (0 : ℝ)..A, 1 / (a + x + y) ^ 2 =
      Real.log ((a + A) ^ 2 / (a * (a + 2 * A))) := by
  have hinner : EqOn (fun x => ∫ y in (0 : ℝ)..A, 1 / (a + x + y) ^ 2)
      (fun x => 1 / (a + x) - 1 / (a + x + A)) (uIcc 0 A) := by
    intro x hx
    rw [uIcc_of_le hA] at hx
    exact integral_one_div_add_sq (by linarith [hx.1]) hA
  rw [integral_congr hinner]
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) A, HasDerivAt
      (fun x => Real.log (a + x) - Real.log (a + x + A))
      (1 / (a + x) - 1 / (a + x + A)) x := by
    intro x hx
    rw [uIcc_of_le hA] at hx
    have h1 : a + x ≠ 0 := by linarith [hx.1]
    have h2 : a + x + A ≠ 0 := by linarith [hx.1]
    have d1 := ((hasDerivAt_id x).const_add a).log h1
    have d2 := (((hasDerivAt_id x).const_add a).add_const A).log h2
    convert d1.sub d2 using 1
    · ext; simp
    · simp
  have hcont : ContinuousOn (fun x : ℝ => 1 / (a + x) - 1 / (a + x + A)) (uIcc 0 A) := by
    rw [uIcc_of_le hA]
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
      linarith [hx.1]
    · refine ContinuousOn.div continuousOn_const (by fun_prop) fun x hx => ?_
      linarith [hx.1]
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  have h1 : 0 < a + A := by linarith
  have h2 : 0 < a + 2 * A := by linarith
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul ha.ne' h2.ne', Real.log_pow]
  simp only [add_zero]
  rw [show a + A + A = a + 2 * A by ring]
  push_cast
  ring

/-- Integral test for one row: `∫₀^M (b + 1 + y)⁻² dy ≤ ∑_{j<M} (b + (j + 1))⁻²` for
`b ≥ 0`. -/
theorem integral_one_div_add_sq_le_sum {b : ℝ} (hb : 0 ≤ b) (M : ℕ) :
    ∫ y in (0 : ℝ)..M, 1 / (b + 1 + y) ^ 2 ≤
      ∑ j ∈ Finset.range M, 1 / (b + ((j : ℝ) + 1)) ^ 2 := by
  have hanti : AntitoneOn (fun y : ℝ => 1 / (b + y) ^ 2) (Icc 1 (1 + M)) := by
    intro x hx y hy hxy
    have hx0 : 0 < b + x := by linarith [hx.1]
    simp only
    gcongr
  have h := hanti.integral_le_sum
  have hshift : ∫ y in (0 : ℝ)..M, 1 / (b + 1 + y) ^ 2 =
      ∫ y in (1 : ℝ)..1 + M, 1 / (b + y) ^ 2 := by
    have := integral_comp_add_left (a := (0 : ℝ)) (b := (M : ℝ))
      (fun y : ℝ => 1 / (b + y) ^ 2) 1
    simp only [add_zero] at this
    rw [← this]
    congr 1
    ext y
    ring_nf
  rw [hshift]
  refine h.trans_eq (Finset.sum_congr rfl fun j _ => ?_)
  ring_nf

theorem integral_integral_one_div_add_add_sq_le_sum_sum {c : ℝ} (hc : 0 ≤ c) (M : ℕ) :
    ∫ x in (0 : ℝ)..M, ∫ y in (0 : ℝ)..M, 1 / (c + 2 + x + y) ^ 2 ≤
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
        1 / (c + ((i : ℝ) + 1) + ((j : ℝ) + 1)) ^ 2 := by
  have hM : (0 : ℝ) ≤ M := M.cast_nonneg
  -- the inner integral as a function of the first coordinate
  set G : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..M, 1 / (c + 1 + x + y) ^ 2 with hG
  have hGval : ∀ x, 0 ≤ x → G x = M / ((c + 1 + x) * (c + 1 + x + M)) := by
    intro x hx
    have hp : 0 < c + 1 + x := by linarith
    have hq : 0 < c + 1 + x + M := by linarith
    simp only [hG]
    rw [integral_one_div_add_sq hp hM]
    field_simp
    ring
  have hanti : AntitoneOn G (Icc 1 (1 + M)) := by
    intro x hx y hy hxy
    rw [hGval x (by linarith [hx.1]), hGval y (by linarith [hy.1])]
    have hp : 0 < c + 1 + x := by linarith [hx.1]
    have hq : 0 < c + 1 + y := by linarith [hy.1]
    gcongr
  have hrow : ∀ i : ℕ, G (1 + i) ≤
      ∑ j ∈ Finset.range M, 1 / (c + ((i : ℝ) + 1) + ((j : ℝ) + 1)) ^ 2 := by
    intro i
    have h := integral_one_div_add_sq_le_sum (b := c + ((i : ℝ) + 1)) (by positivity) M
    refine le_trans (le_of_eq ?_) h
    simp only [hG]
    congr 1
    ext y
    ring_nf
  have hshift : ∫ x in (0 : ℝ)..M, ∫ y in (0 : ℝ)..M, 1 / (c + 2 + x + y) ^ 2 =
      ∫ x in (1 : ℝ)..1 + M, G x := by
    have := integral_comp_add_left (a := (0 : ℝ)) (b := (M : ℝ)) G 1
    simp only [add_zero] at this
    rw [← this]
    congr 1
    ext x
    simp only [hG]
    congr 1
    ext y
    ring_nf
  rw [hshift]
  exact hanti.integral_le_sum.trans (Finset.sum_le_sum fun i _ => hrow i)

/-- For `t > 0`, `t / 2 ≤ (1 + t)² / (1 + 2t)`; stated for the ratio
`(a + M)² / (a (a + 2M))` with `a > 0` and `t = M / a`. -/
theorem div_le_sq_add_div_mul_add {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    M / (2 * a) ≤ (a + M) ^ 2 / (a * (a + 2 * M)) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg a, mul_nonneg ha.le hM, sq_nonneg M]

theorem log_div_le_sum_sum_one_div_sq {K m u v : ℕ} (hK : 2 ≤ K) (hm : 2 ≤ m)
    (hu : K * m / 2 ≤ u) (hv : K * m / 2 ≤ v) :
    Real.log (m / 64) ≤ ∑ i ∈ Finset.Icc 1 u, ∑ j ∈ Finset.Icc 1 v,
      1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2 := by
  set M := K * m / 2 with hMdef
  -- `M ≥ K m / 4`
  have hKm : 4 ≤ K * m := by nlinarith
  have hM2 : K * m ≤ 2 * M + 1 := by omega
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (K : ℝ) * m ≤ 4 * M := by
    have h1 : ((K * m : ℕ) : ℝ) ≤ 2 * M + 1 := by exact_mod_cast hM2
    have h2 : (4 : ℝ) ≤ ((K * m : ℕ) : ℝ) := by exact_mod_cast hKm
    push_cast at h1 h2
    linarith
  have hMpos : (0 : ℝ) < M := by nlinarith
  -- restrict to the block `[1, M]²`
  have hnonneg : ∀ i j : ℕ, 0 ≤ 1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2 := fun _ _ => by positivity
  have hrestrict : ∑ i ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
      1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2 ≤ ∑ i ∈ Finset.Icc 1 u, ∑ j ∈ Finset.Icc 1 v,
      1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2 := by
    calc _ ≤ ∑ i ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 v, 1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_right hv) fun j _ _ => hnonneg i j
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hu)
            fun i _ _ => Finset.sum_nonneg fun j _ => hnonneg i j
  have hIcc : ∀ f : ℕ → ℝ, ∑ i ∈ Finset.Icc 1 M, f i = ∑ i ∈ Finset.range M, f (i + 1) := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 M 1]
    rfl
  have hblock := integral_integral_one_div_add_add_sq_le_sum_sum
    (c := 6 * (K : ℝ)) (by positivity) M
  have hint : ∫ x in (0 : ℝ)..M, ∫ y in (0 : ℝ)..M, 1 / (6 * (K : ℝ) + 2 + x + y) ^ 2 =
      Real.log ((6 * K + 2 + M) ^ 2 / ((6 * K + 2) * (6 * K + 2 + 2 * M))) :=
    integral_integral_one_div_add_add_sq (by positivity) hMpos.le
  have hsum : ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
      1 / (6 * (K : ℝ) + ((i : ℝ) + 1) + ((j : ℝ) + 1)) ^ 2 =
      ∑ i ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, 1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2 := by
    rw [hIcc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hIcc]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  refine le_trans ?_ (hrestrict.trans' (hsum ▸ hint ▸ hblock))
  -- the constant: `m / 64 ≤ M / (2 a) ≤ (a + M)² / (a (a + 2M))` with `a = 6K + 2 ≤ 8K`
  have ha : (0 : ℝ) < 6 * K + 2 := by positivity
  refine Real.log_le_log (by positivity) ?_
  refine le_trans ?_ (div_le_sq_add_div_mul_add ha hMpos.le)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

end PercLib.Analysis
