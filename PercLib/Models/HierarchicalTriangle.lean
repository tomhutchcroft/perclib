/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # The triangle diagram under one hierarchical block extension

Glue identical finite blocks with constant off-block kernel `t`. At a fixed
root the triangle increment has three contributions with exactly two blocks
occupied and one contribution with three blocks occupied. No independence of
the three two-point functions is assumed.
-/

@[expose] public section

namespace PercLib.Models

open Finset

/-- Row sum and rooted triangle after adding a top coordinate. The old block
has `M` sites and there are `b + 1` blocks. The new coordinates use `Option`
so that the root block is distinguished without assuming an ordering. -/
theorem hierarchical_triangle_extension {I X : Type*} [Fintype I] [Fintype X]
    [DecidableEq I] (o : X) (K : X → X → ℝ) (s t : ℝ)
    (hrow : ∀ x, ∑ y, K x y = s) (hcol : ∀ y, ∑ x, K x y = s) :
    let M : ℝ := Fintype.card X
    let b : ℝ := Fintype.card I
    let T : Option I × X → Option I × X → ℝ := fun x y =>
      if x.1 = y.1 then K x.2 y.2 else t
    (∑ x, T (none, o) x) = s + b * M * t ∧
    (∑ x, ∑ y, T (none, o) x * T x y * T y (none, o)) =
      (∑ x, ∑ y, K o x * K x y * K y o) +
        3 * b * M * s * t ^ 2 + b * (b - 1) * M ^ 2 * t ^ 3 := by
  classical
  dsimp only
  constructor
  · simp [Fintype.sum_prod_type, Fintype.sum_option, hrow, nsmul_eq_mul]
    ring
  · have hdiff (i : I) (a c : ℝ) :
        (∑ j : I, if i = j then a else c) = a + (Fintype.card I - 1 : ℝ) * c := by
      have h (j : I) : (if i = j then a else c) =
          (if i = j then a - c else 0) + c := by split_ifs <;> ring
      simp_rw [h, Finset.sum_add_distrib]
      simp [nsmul_eq_mul]
      ring
    simp only [Fintype.sum_prod_type, Fintype.sum_option, reduceCtorEq, ↓reduceIte,
      Option.some.injEq]
    simp_rw [Finset.sum_add_distrib]
    simp [← Finset.sum_mul, ← Finset.mul_sum, hrow, hcol, nsmul_eq_mul,
      apply_ite, ite_mul, hdiff]
    ring

/-- For a geometric radial profile the shell increment splits into two
geometric sequences. This formula includes the marginal case without a
division by the leading ratio minus one. Here `c * r^n` is the off-block
entry when extending from level `n` to level `n+1`. -/
theorem hierarchical_triangle_geometric
    (B c r U v : ℝ) (S D : ℕ → ℝ)
    (hS : S 0 = U + v) (hU : U * (B * r - 1) = (B - 1) * c)
    (hsucc : ∀ n, S (n+1) = S n + (B-1) * B^n * (c*r^n))
    (hd : ∀ n, D (n+1) = D n +
      3 * (B-1) * B^n * S n * (c*r^n)^2 +
      (B-1) * (B-2) * (B^n)^2 * (c*r^n)^3) (N : ℕ) :
    S N = U * (B*r)^N + v ∧
    D N = D 0 +
      (3*(B-1)*U*c^2 + (B-1)*(B-2)*c^3) *
        (∑ n ∈ range N, (B^2*r^3)^n) +
      3*(B-1)*v*c^2 * (∑ n ∈ range N, (B*r^2)^n) := by
  induction N with
  | zero => simp [hS]
  | succ n ih =>
    constructor
    · rw [hsucc, ih.1, pow_succ, mul_pow]
      linear_combination -(B^n * r^n) * hU
    · rw [hd, ih.1, ih.2, sum_range_succ, sum_range_succ]
      simp only [mul_pow, ← pow_mul]
      ring_nf

end PercLib.Models
