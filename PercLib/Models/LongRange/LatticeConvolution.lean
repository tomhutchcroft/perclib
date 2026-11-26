/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Power-law convolution bounds on `ℤ^d` for the Euclidean bracket `⟨x⟩ = max 1 |x|`. New for
this project against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code
is copied. Mathematical reference: Hara, *Decay of correlations in nearest-neighbour
self-avoiding walk, percolation, lattice trees and animals*, Ann. Probab. 36 (2008),
Proposition 1.7.
-/
module

public import PercLib.Analysis.PowerLawConvolution
public import PercLib.Models.LongRange.SoftCutoff

/-!
# Power-law convolution bounds on `ℤ^d`

Write `⟨x⟩ = max 1 √(∑ᵢ xᵢ²)` and `(f ⋆ g)(x) = ∑ y, f y g (x - y)` for real kernels on `ℤ^d`.
If `|f x| ≤ A ⟨x⟩^(-a)` and `|g x| ≤ B ⟨x⟩^(-b)` with `a, b > 0`, then the convolution sum
converges absolutely and `|(f ⋆ g)(x)| ≤ C A B ⟨x⟩^(-min a b)` when `max a b > d`, and
`|(f ⋆ g)(x)| ≤ C A B ⟨x⟩^(-(a + b - d))` when `a, b < d < a + b`, with `C` depending only on
`a`, `b` and `d`. The logarithmic endpoints are not treated.

## Main results

* `abs_tsum_mul_sub_le_of_tsum_le`: a kernel bound in `ℝ≥0∞` gives absolute convergence and the
  bound for kernels dominated by the weights.
* `tsum_ite_max_euclid_le_le`: `#{⟨y⟩ ≤ t} ≤ 3^d t^d`.
* `exists_abs_tsum_mul_sub_le_of_lt_max`: the bound `⟨x⟩^(-min a b)` for `max a b > d`.
* `exists_abs_tsum_mul_sub_le_of_lt_add`: the bound `⟨x⟩^(-(a+b-d))` for `a, b < d < a + b`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PercLib.Models.LongRange

open PercLib.Analysis

/-! ### From kernel bounds to real convolutions -/

/-- If `∑ w(y)^(-a) w(x-y)^(-b) ≤ C w(x)^(-e)` in `ℝ≥0∞`, and `|f| ≤ A w^(-a)`,
`|g| ≤ B w^(-b)`, then `∑ f(y) g(x-y)` converges absolutely and is at most
`C A B w(x)^(-e)` in absolute value. -/
theorem abs_tsum_mul_sub_le_of_tsum_le {G : Type*} [AddCommGroup G] {w : G → ℝ}
    (hw1 : ∀ y, 1 ≤ w y) {a b C e A B : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f g : G → ℝ} (hf : ∀ x, |f x| ≤ A * w x ^ (-a)) (hg : ∀ x, |g x| ≤ B * w x ^ (-b))
    {x : G}
    (hker : ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) ≤
      ENNReal.ofReal (C * w x ^ (-e))) :
    Summable (fun y => |f y * g (x - y)|) ∧
      |∑' y, f y * g (x - y)| ≤ C * A * B * w x ^ (-e) := by
  have hw0 : ∀ y, 0 ≤ w y := fun y => zero_le_one.trans (hw1 y)
  have hk0 : ∀ y, 0 ≤ w y ^ (-a) * w (x - y) ^ (-b) := fun y =>
    mul_nonneg (Real.rpow_nonneg (hw0 y) _) (Real.rpow_nonneg (hw0 _) _)
  have hks : Summable fun y => w y ^ (-a) * w (x - y) ^ (-b) :=
    (summable_iff_tsum_ofReal_ne_top hk0).2 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hker)
  have hle : ∀ y, |f y * g (x - y)| ≤ A * B * (w y ^ (-a) * w (x - y) ^ (-b)) := by
    intro y
    rw [abs_mul]
    calc |f y| * |g (x - y)| ≤ (A * w y ^ (-a)) * (B * w (x - y) ^ (-b)) :=
          mul_le_mul (hf y) (hg _) (abs_nonneg _)
            (mul_nonneg hA (Real.rpow_nonneg (hw0 y) _))
      _ = A * B * (w y ^ (-a) * w (x - y) ^ (-b)) := by ring
  have hs : Summable fun y => |f y * g (x - y)| :=
    Summable.of_nonneg_of_le (fun y => abs_nonneg _) hle (hks.mul_left (A * B))
  have htk : ∑' y, w y ^ (-a) * w (x - y) ^ (-b) ≤ C * w x ^ (-e) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hk0 hks] at hker
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg (hw0 x) _))).1 hker
  refine ⟨hs, ?_⟩
  calc |∑' y, f y * g (x - y)| ≤ ∑' y, |f y * g (x - y)| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun y => f y * g (x - y))
            (by simpa only [Real.norm_eq_abs] using hs)
    _ ≤ ∑' y, A * B * (w y ^ (-a) * w (x - y) ^ (-b)) :=
        Summable.tsum_le_tsum hle hs (hks.mul_left _)
    _ = A * B * ∑' y, w y ^ (-a) * w (x - y) ^ (-b) := tsum_mul_left
    _ ≤ A * B * (C * w x ^ (-e)) := mul_le_mul_of_nonneg_left htk (mul_nonneg hA hB)
    _ = C * A * B * w x ^ (-e) := by ring

/-! ### The Euclidean bracket on `ℤ^d` -/

variable {d : ℕ}

/-- The Euclidean bracket is subadditive. -/
theorem max_euclid_add_le (y z : Fin d → ℤ) :
    max 1 √(∑ i, (((y + z) i : ℤ) : ℝ) ^ 2) ≤
      max 1 √(∑ i, ((y i : ℝ)) ^ 2) + max 1 √(∑ i, ((z i : ℝ)) ^ 2) := by
  rw [euclid_eq_norm, euclid_eq_norm, euclid_eq_norm]
  have hfun : (fun i => (((y + z) i : ℤ) : ℝ)) = (fun i => (y i : ℝ)) + fun i => (z i : ℝ) := by
    funext i
    simp
  rw [hfun, WithLp.toLp_add]
  have := norm_add_le (WithLp.toLp 2 fun i => (y i : ℝ)) (WithLp.toLp 2 fun i => (z i : ℝ))
  refine max_le ?_ ?_
  · linarith [le_max_left (1 : ℝ) ‖(WithLp.toLp 2 fun i => (y i : ℝ) : EuclideanSpace ℝ (Fin d))‖,
      le_max_left (1 : ℝ) ‖(WithLp.toLp 2 fun i => (z i : ℝ) : EuclideanSpace ℝ (Fin d))‖]
  · linarith [le_max_right (1 : ℝ) ‖(WithLp.toLp 2 fun i => (y i : ℝ) : EuclideanSpace ℝ (Fin d))‖,
      le_max_right (1 : ℝ) ‖(WithLp.toLp 2 fun i => (z i : ℝ) : EuclideanSpace ℝ (Fin d))‖]

/-- The Euclidean bracket is symmetric. -/
theorem max_euclid_neg (y : Fin d → ℤ) :
    max 1 √(∑ i, (((-y) i : ℤ) : ℝ) ^ 2) = max 1 √(∑ i, ((y i : ℝ)) ^ 2) := by
  simp

/-- **Ball counts.** `#{⟨y⟩ ≤ t} ≤ 3^d t^d` for every real `t`. -/
theorem tsum_ite_max_euclid_le_le (t : ℝ) :
    ∑' y : Fin d → ℤ, (if max 1 √(∑ i, ((y i : ℝ)) ^ 2) ≤ t then (1 : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal (3 ^ d * t ^ (d : ℝ)) := by
  rw [tsum_ite_const_eq, mul_one]
  by_cases h1 : 1 ≤ t
  · have hset : {y : Fin d → ℤ | max 1 √(∑ i, ((y i : ℝ)) ^ 2) ≤ t} =
        {y : Fin d → ℤ | √(∑ i, ((y i : ℝ)) ^ 2) ≤ t} := by
      ext y
      simp [h1]
    rw [hset, Real.rpow_natCast, ← mul_pow]
    exact encard_euclid_le h1
  · have hset : {y : Fin d → ℤ | max 1 √(∑ i, ((y i : ℝ)) ^ 2) ≤ t} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.1 h1) (le_max_left _ _)
    rw [hset, Set.encard_empty]
    simp

/-! ### The convolution bounds -/

/-- **Power-law convolution bound, `max a b > d`.** There is `C`, depending only on `a`, `b`
and `d`, such that `|f| ≤ A ⟨·⟩^(-a)` and `|g| ≤ B ⟨·⟩^(-b)` imply that `∑ f(y) g(x-y)`
converges absolutely with `|∑ f(y) g(x-y)| ≤ C A B ⟨x⟩^(-min a b)`. -/
theorem exists_abs_tsum_mul_sub_le_of_lt_max (d : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : (d : ℝ) < max a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℝ) (f g : (Fin d → ℤ) → ℝ), 0 ≤ A → 0 ≤ B →
      (∀ x, |f x| ≤ A * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) →
      (∀ x, |g x| ≤ B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-b)) →
      ∀ x, Summable (fun y => |f y * g (x - y)|) ∧
        |∑' y, f y * g (x - y)| ≤ C * A * B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-min a b) := by
  obtain ⟨C, hC, hker⟩ := exists_tsum_rpow_mul_rpow_sub_le_of_lt_max
    (w := fun x : Fin d → ℤ => max 1 √(∑ i, ((x i : ℝ)) ^ 2)) (fun y => le_max_left _ _)
    max_euclid_add_le max_euclid_neg (fun t _ => tsum_ite_max_euclid_le_le t)
    (by positivity) ha hb hD
  exact ⟨C, hC, fun A B f g hA hB hf hg x =>
    abs_tsum_mul_sub_le_of_tsum_le (fun y => le_max_left _ _) hC hA hB hf hg (hker x)⟩

/-- **Power-law convolution bound, `a, b < d < a + b`.** There is `C`, depending only on `a`,
`b` and `d`, such that `|f| ≤ A ⟨·⟩^(-a)` and `|g| ≤ B ⟨·⟩^(-b)` imply that `∑ f(y) g(x-y)`
converges absolutely with `|∑ f(y) g(x-y)| ≤ C A B ⟨x⟩^(-(a+b-d))`. -/
theorem exists_abs_tsum_mul_sub_le_of_lt_add (d : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haD : a < d) (hbD : b < d) (hD : (d : ℝ) < a + b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℝ) (f g : (Fin d → ℤ) → ℝ), 0 ≤ A → 0 ≤ B →
      (∀ x, |f x| ≤ A * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) →
      (∀ x, |g x| ≤ B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-b)) →
      ∀ x, Summable (fun y => |f y * g (x - y)|) ∧
        |∑' y, f y * g (x - y)| ≤
          C * A * B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-(a + b - d)) := by
  obtain ⟨C, hC, hker⟩ := exists_tsum_rpow_mul_rpow_sub_le_of_lt_add
    (w := fun x : Fin d → ℤ => max 1 √(∑ i, ((x i : ℝ)) ^ 2)) (fun y => le_max_left _ _)
    max_euclid_add_le max_euclid_neg (fun t _ => tsum_ite_max_euclid_le_le t)
    (by positivity) ha hb haD hbD hD
  exact ⟨C, hC, fun A B f g hA hB hf hg x =>
    abs_tsum_mul_sub_le_of_tsum_le (fun y => le_max_left _ _) hC hA hB hf hg (hker x)⟩

end PercLib.Models.LongRange
