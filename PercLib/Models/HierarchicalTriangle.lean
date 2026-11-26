/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21, against pinned mathlib. No upstream proof is copied.
Mathematical reference: T. Hutchcroft, *Critical cluster volumes in hierarchical
percolation*, arXiv:2211.05686v1 (the triangle condition on the hierarchical lattice); the
argument here uses only two-sided kernel bounds and the ultrametric inequality.
-/
module

public import PercLib.Models.HierarchicalAmplificationStep
public import PercLib.Models.HierarchicalBallSums

/-!
# The hierarchical triangle sum from two-sided kernel bounds

On `V = ℕ →₀ (Fin d → ZMod L)` write `h(z) = z.support.sup Nat.succ` for the level and
`Λ_N = {z | h(z) ≤ N}`. Let `f : V → ℝ` with
`c L^{-(d-α) h(x)} ≤ f(x) ≤ C L^{-(d-α) h(x)}` for constants `0 < c ≤ C` and `0 < α < d`, and
put `Δ_N = ∑_{x, y ∈ Λ_N} f(x) f(y - x) f(y)`. Then the increments satisfy
`a L^{(3α-d)n} ≤ Δ_n - Δ_{n-1} ≤ A L^{(3α-d)n}` for `n ≥ 1`, so the full triangle sum is finite
exactly when `3α < d`, `Δ_N ≍ N + 1` when `3α = d` and `Δ_N ≍ L^{(3α-d)N}` when `3α > d`.

## Main results

* `level_sub_le_max_level`, `level_le_max_level_sub`: ultrametric inequalities for `x`, `y`
  and `y - x`.
* `le_sum_level_ball`, `sum_level_ball_le`: two-sided bounds on `∑_{z ∈ Λ_n} f(z)` from
  pointwise bounds `c q^{h(z)} ≤ f(z) ≤ C q^{h(z)}`.
* `triangle_increment_le`, `le_triangle_increment`: the increment bounds in terms of `q`.
* `triangle_increment_bounds`: the increment bounds `a L^{(3α-d)n} ≤ Δ_n - Δ_{n-1} ≤ A L^{(3α-d)n}`.
* `bddAbove_iff_of_increment_bounds`, `linear_bounds_of_increment_bounds`,
  `geometric_bounds_of_increment_bounds`: growth of a sequence with geometric increments.
* `summable_triangle_iff`, `triangle_linear_bounds`, `triangle_geometric_bounds`: the three
  regimes of the triangle sum.

No definition is introduced.
-/

@[expose] public section
noncomputable section

open Finset

namespace PercLib.Models

/-! ### Sequences with geometric increments -/

section Sequences

variable {Δ : ℕ → ℝ} {ρ a A : ℝ}

theorem eq_add_sum_sub (Δ : ℕ → ℝ) (N : ℕ) :
    Δ N = Δ 0 + ∑ i ∈ range N, (Δ (i + 1) - Δ i) := by
  rw [sum_range_sub]; ring

theorem add_mul_sum_le_of_increment (hinc : ∀ n : ℕ, a * ρ ^ (n + 1) ≤ Δ (n + 1) - Δ n)
    (N : ℕ) : Δ 0 + a * ∑ i ∈ range N, ρ ^ (i + 1) ≤ Δ N := by
  rw [eq_add_sum_sub Δ N, mul_sum]
  gcongr with i
  exact hinc i

theorem le_add_mul_sum_of_increment (hinc : ∀ n : ℕ, Δ (n + 1) - Δ n ≤ A * ρ ^ (n + 1))
    (N : ℕ) : Δ N ≤ Δ 0 + A * ∑ i ∈ range N, ρ ^ (i + 1) := by
  rw [eq_add_sum_sub Δ N, mul_sum]
  gcongr with i
  exact hinc i

/-- A sequence whose increments are comparable to `ρ^n` (with `ρ > 0`) is bounded above
exactly when `ρ < 1`. -/
theorem bddAbove_iff_of_increment_bounds (hρ : 0 < ρ) (ha : 0 < a)
    (hlow : ∀ n : ℕ, a * ρ ^ (n + 1) ≤ Δ (n + 1) - Δ n)
    (hup : ∀ n : ℕ, Δ (n + 1) - Δ n ≤ A * ρ ^ (n + 1)) :
    (∃ M, ∀ N, Δ N ≤ M) ↔ ρ < 1 := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hρ1
    push Not at hρ1
    obtain ⟨N, hN⟩ := exists_nat_gt ((M - Δ 0) / a)
    have hsum : (N : ℝ) ≤ ∑ i ∈ range N, ρ ^ (i + 1) := by
      calc (N : ℝ) = ∑ _i ∈ range N, (1 : ℝ) := by simp
        _ ≤ _ := sum_le_sum fun i _ => one_le_pow₀ hρ1
    have h1 := add_mul_sum_le_of_increment hlow N
    have h2 := hM N
    rw [div_lt_iff₀ ha] at hN
    nlinarith
  · intro hρ1
    have hA : 0 ≤ A := by
      have := (hlow 0).trans (hup 0)
      have hp : 0 < ρ ^ (0 + 1) := pow_pos hρ _
      nlinarith
    refine ⟨Δ 0 + A * (ρ / (1 - ρ)), fun N => (le_add_mul_sum_of_increment hup N).trans ?_⟩
    gcongr
    have h1ρ : 0 < 1 - ρ := by linarith
    have hgeom : ∀ N : ℕ, (1 - ρ) * ∑ i ∈ range N, ρ ^ (i + 1) = ρ - ρ ^ (N + 1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [sum_range_succ, mul_add, ih]; ring
    rw [le_div_iff₀ h1ρ, mul_comm, hgeom N]
    have := pow_pos hρ (N + 1)
    linarith

/-- If `0 < b₀ ≤ Δ 0 ≤ B₀` and `a ≤ Δ (n+1) - Δ n ≤ A`, then
`min b₀ a (N + 1) ≤ Δ N ≤ max B₀ A (N + 1)`. -/
theorem linear_bounds_of_increment_bounds {b₀ B₀ : ℝ} (h0l : b₀ ≤ Δ 0) (h0u : Δ 0 ≤ B₀)
    (hlow : ∀ n : ℕ, a ≤ Δ (n + 1) - Δ n) (hup : ∀ n : ℕ, Δ (n + 1) - Δ n ≤ A) (N : ℕ) :
    min b₀ a * (N + 1) ≤ Δ N ∧ Δ N ≤ max B₀ A * (N + 1) := by
  have h1 := add_mul_sum_le_of_increment (ρ := 1) (fun n => by simpa using hlow n) N
  have h2 := le_add_mul_sum_of_increment (ρ := 1) (fun n => by simpa using hup n) N
  simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h1 h2
  have hN : (0 : ℝ) ≤ N := N.cast_nonneg
  constructor
  · nlinarith [min_le_left b₀ a, min_le_right b₀ a]
  · nlinarith [le_max_left B₀ A, le_max_right B₀ A]

/-- If `0 < Δ 0`, `b₀ ≤ Δ 0 ≤ B₀`, `ρ > 1` and `a ρ^{n+1} ≤ Δ (n+1) - Δ n ≤ A ρ^{n+1}` with
`A ≥ 0`, then `min b₀ a ρ^N ≤ Δ N ≤ (B₀ + A ρ/(ρ - 1)) ρ^N`. -/
theorem geometric_bounds_of_increment_bounds {b₀ B₀ : ℝ} (hρ : 1 < ρ) (h0 : 0 < Δ 0)
    (h0l : b₀ ≤ Δ 0) (h0u : Δ 0 ≤ B₀) (ha : 0 ≤ a) (hA : 0 ≤ A)
    (hlow : ∀ n : ℕ, a * ρ ^ (n + 1) ≤ Δ (n + 1) - Δ n)
    (hup : ∀ n : ℕ, Δ (n + 1) - Δ n ≤ A * ρ ^ (n + 1)) (N : ℕ) :
    min b₀ a * ρ ^ N ≤ Δ N ∧ Δ N ≤ (B₀ + A * (ρ / (ρ - 1))) * ρ ^ N := by
  have hρ0 : 0 < ρ := by linarith
  constructor
  · rcases N with _ | N
    · simpa using (min_le_left _ _).trans h0l
    · have h1 := add_mul_sum_le_of_increment hlow (N + 1)
      rw [sum_range_succ] at h1
      have hs : 0 ≤ ∑ i ∈ range N, ρ ^ (i + 1) := sum_nonneg fun i _ => by positivity
      have hp : 0 < ρ ^ (N + 1) := pow_pos hρ0 _
      have hm : min b₀ a * ρ ^ (N + 1) ≤ a * ρ ^ (N + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le
      nlinarith [mul_nonneg ha hs]
  · have h2 := le_add_mul_sum_of_increment hup N
    have h3 := sum_range_pow_succ_le hρ N
    have hp : 1 ≤ ρ ^ N := one_le_pow₀ hρ.le
    have hB : 0 ≤ B₀ := h0.le.trans h0u
    calc Δ N ≤ B₀ + A * (ρ / (ρ - 1) * ρ ^ N) := h2.trans (by gcongr)
      _ ≤ B₀ * ρ ^ N + A * (ρ / (ρ - 1) * ρ ^ N) := by nlinarith
      _ = _ := by ring

end Sequences

/-! ### Ultrametric facts and ball sums -/

variable {d L : ℕ}

section Geometry

variable {G : Type*} [AddCommGroup G]

/-- `h(y - x) ≤ max (h x) (h y)`. -/
theorem level_sub_le_max_level (x y : ℕ →₀ G) :
    (y - x).support.sup Nat.succ ≤ max (x.support.sup Nat.succ) (y.support.sup Nat.succ) := by
  simpa [level_sub_comm 0 x] using level_sub_le_max x 0 y

/-- `h x ≤ max (h y) (h (y - x))`. -/
theorem level_le_max_level_sub (x y : ℕ →₀ G) :
    x.support.sup Nat.succ ≤ max (y.support.sup Nat.succ) ((y - x).support.sup Nat.succ) := by
  simpa [level_sub_comm x y] using level_sub_le_max 0 y x

end Geometry

variable [NeZero L]

theorem mem_toFinset_level_ball {z : ℕ →₀ (Fin d → ZMod L)} {n : ℕ} :
    z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset ↔ z.support.sup Nat.succ ≤ n := by
  simp

theorem toFinset_level_ball_zero :
    (finite_level_ball (A := Fin d → ZMod L) 0).toFinset = {0} := by
  ext z
  rw [mem_toFinset_level_ball, Nat.le_zero, level_eq_zero_iff, mem_singleton]

theorem filter_toFinset_level_ball_succ (n : ℕ) :
    (finite_level_ball (A := Fin d → ZMod L) (n + 1)).toFinset.filter
      (fun z => z.support.sup Nat.succ ≤ n) =
      (finite_level_ball (A := Fin d → ZMod L) n).toFinset := by
  ext z
  simp only [mem_filter, mem_toFinset_level_ball]
  omega

/-- Translating by a vertex of `Λ_n` permutes `Λ_n`. -/
theorem sum_toFinset_level_ball_sub (f : (ℕ →₀ (Fin d → ZMod L)) → ℝ) {n : ℕ}
    {x : ℕ →₀ (Fin d → ZMod L)} (hx : x.support.sup Nat.succ ≤ n) :
    ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset, f (y - x) =
      ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset, f z := by
  refine sum_nbij' (fun y => y - x) (fun z => z + x) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [
      mem_toFinset_level_ball] at hy ⊢
    exact (level_sub_le_max_level x y).trans (max_le hx hy)
  · intro z hz
    simp only [mem_toFinset_level_ball] at hz ⊢
    exact (level_add_le_max z x).trans (max_le hz hx)
  · intro y _; simp
  · intro z _; simp
  · intro y _; rfl

/-- If `c q^{h(z)} ≤ f(z)` with `0 ≤ c` and `0 ≤ q ≤ 1`, then `c (L^d q)^n ≤ ∑_{z ∈ Λ_n} f(z)`. -/
theorem le_sum_level_ball {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ} {c q : ℝ} (hc : 0 ≤ c)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hf : ∀ z, c * q ^ z.support.sup Nat.succ ≤ f z) (n : ℕ) :
    c * ((L : ℝ) ^ d * q) ^ n ≤
      ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset, f z := by
  calc c * ((L : ℝ) ^ d * q) ^ n
      = ∑ _z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset, c * q ^ n := by
        rw [sum_const, card_toFinset_level_ball, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := sum_le_sum fun z hz => (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hq0 hq1 (mem_toFinset_level_ball.1 hz)) hc).trans (hf z)

/-- If `f(z) ≤ C q^{h(z)}` with `0 ≤ C`, `0 ≤ q`, then
`∑_{z ∈ Λ_n} f(z) ≤ C ∑_{k ≤ n} (L^d q)^k`. -/
theorem sum_level_ball_le {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ} {C q : ℝ} (hC : 0 ≤ C)
    (hq0 : 0 ≤ q) (hf : ∀ z, f z ≤ C * q ^ z.support.sup Nat.succ) (n : ℕ) :
    ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset, f z ≤
      C * ∑ k ∈ range (n + 1), ((L : ℝ) ^ d * q) ^ k := by
  induction n with
  | zero =>
    rw [toFinset_level_ball_zero, sum_singleton]
    simpa using hf 0
  | succ n ih =>
    rw [← sum_filter_add_sum_filter_not _ (fun z => z.support.sup Nat.succ ≤ n),
      filter_toFinset_level_ball_succ, sum_range_succ, mul_add]
    refine add_le_add ih ?_
    calc ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) (n + 1)).toFinset.filter
          (fun z => ¬z.support.sup Nat.succ ≤ n), f z
        ≤ ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) (n + 1)).toFinset.filter
          (fun z => ¬z.support.sup Nat.succ ≤ n), C * q ^ (n + 1) := by
          refine sum_le_sum fun z hz => (hf z).trans_eq ?_
          simp only [mem_filter, mem_toFinset_level_ball] at hz
          rw [show z.support.sup Nat.succ = n + 1 by omega]
      _ ≤ ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) (n + 1)).toFinset, C * q ^ (n + 1) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = C * ((L : ℝ) ^ d * q) ^ (n + 1) := by
          rw [sum_const, card_toFinset_level_ball, nsmul_eq_mul]
          push_cast
          ring

/-! ### The increments of the triangle sum -/

/-- The increment `Δ_{m+1} - Δ_m` as a sum over pairs with a vertex outside `Λ_m`. -/
theorem triangle_sub_eq (f : (ℕ →₀ (Fin d → ZMod L)) → ℝ) (m : ℕ) :
    (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
          f x * f (y - x) * f y) -
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f x * f (y - x) * f y =
    ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
      ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
        if x.support.sup Nat.succ ≤ m ∧ y.support.sup Nat.succ ≤ m then 0
        else f x * f (y - x) * f y := by
  rw [← filter_toFinset_level_ball_succ m, sum_filter]
  simp_rw [sum_filter]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x.support.sup Nat.succ ≤ m
  · simp only [hx, ↓reduceIte]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : y.support.sup Nat.succ ≤ m <;> simp [hy]
  · simp [hx]

theorem mul_mul_le_sq_mul {u v w W : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hu : u ≤ W) (hw : w ≤ W) : u * v * w ≤ W ^ 2 * v := by
  have hW : 0 ≤ W := hu0.trans hu
  calc u * v * w ≤ W * v * W :=
        mul_le_mul (mul_le_mul_of_nonneg_right hu hv0) hw hw0 (mul_nonneg hW hv0)
    _ = W ^ 2 * v := by ring

/-- Upper bound on the increment: `Δ_{m+1} - Δ_m ≤ 3 W² L^{d(m+1)} ∑_{z ∈ Λ_{m+1}} f(z)` with
`W = C q^{m+1}`. -/
theorem triangle_increment_le {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ} {C q : ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hf : ∀ z, f z ≤ C * q ^ z.support.sup Nat.succ) (m : ℕ) :
    (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
          f x * f (y - x) * f y) -
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f x * f (y - x) * f y ≤
    (C * q ^ (m + 1)) ^ 2 * (3 * ((L : ℝ) ^ d) ^ (m + 1) *
      ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset, f z) := by
  set S := (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset with hS
  set W := C * q ^ (m + 1)
  have hW : ∀ z : ℕ →₀ (Fin d → ZMod L), z.support.sup Nat.succ = m + 1 → f z ≤ W := by
    intro z hz; have := hf z; rw [hz] at this; exact this
  rw [triangle_sub_eq]
  calc ∑ x ∈ S, ∑ y ∈ S, (if x.support.sup Nat.succ ≤ m ∧ y.support.sup Nat.succ ≤ m then 0
        else f x * f (y - x) * f y)
      ≤ ∑ x ∈ S, ∑ y ∈ S, W ^ 2 * (f x + f (y - x) + f y) := by
        refine sum_le_sum fun x hx => sum_le_sum fun y hy => ?_
        rw [hS, mem_toFinset_level_ball] at hx hy
        have hsum0 : 0 ≤ f x + f (y - x) + f y := by
          linarith [hf0 x, hf0 (y - x), hf0 y]
        split_ifs with hxy
        · positivity
        have h1 := level_sub_le_max_level x y
        have h2 := level_le_max_level_sub x y
        have h3 := level_le_max_level_sub y x
        rw [show x - y = -(y - x) by abel, Finsupp.support_neg] at h3
        simp only [le_max_iff] at h1 h2 h3
        have hfx := hf0 x; have hfyx := hf0 (y - x); have hfy := hf0 y
        by_cases hxm : x.support.sup Nat.succ ≤ m
        · have hym : y.support.sup Nat.succ = m + 1 := by omega
          have hyxm : (y - x).support.sup Nat.succ = m + 1 := by omega
          have := mul_mul_le_sq_mul hfyx hfx hfy (hW _ hyxm) (hW _ hym)
          nlinarith [sq_nonneg W]
        · have hxm' : x.support.sup Nat.succ = m + 1 := by omega
          by_cases hym : y.support.sup Nat.succ ≤ m
          · have hyxm : (y - x).support.sup Nat.succ = m + 1 := by omega
            have := mul_mul_le_sq_mul hfx hfy hfyx (hW _ hxm') (hW _ hyxm)
            nlinarith [sq_nonneg W]
          · have hym' : y.support.sup Nat.succ = m + 1 := by omega
            have := mul_mul_le_sq_mul hfx hfyx hfy (hW _ hxm') (hW _ hym')
            nlinarith [sq_nonneg W]
    _ = W ^ 2 * (3 * ((L : ℝ) ^ d) ^ (m + 1) * ∑ z ∈ S, f z) := by
        simp only [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
        rw [sum_congr rfl fun x hx =>
          sum_toFinset_level_ball_sub f (mem_toFinset_level_ball.1 (hS ▸ hx))]
        rw [sum_const, nsmul_eq_mul, hS, card_toFinset_level_ball]
        push_cast
        ring

/-- Lower bound on the increment:
`w² (L^{d(m+1)} - L^{dm}) ∑_{z ∈ Λ_m} f(z) ≤ Δ_{m+1} - Δ_m` with `w = c q^{m+1}`. -/
theorem le_triangle_increment {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ} {c q : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hf0 : ∀ z, 0 ≤ f z)
    (hf : ∀ z, c * q ^ z.support.sup Nat.succ ≤ f z) (m : ℕ) :
    (c * q ^ (m + 1)) ^ 2 * ((((L : ℝ) ^ d) ^ (m + 1) - ((L : ℝ) ^ d) ^ m) *
      ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f z) ≤
    (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
          f x * f (y - x) * f y) -
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f x * f (y - x) * f y := by
  set S := (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset with hS
  set w := c * q ^ (m + 1)
  have hw0 : 0 ≤ w := by positivity
  have hw : ∀ z : ℕ →₀ (Fin d → ZMod L), z.support.sup Nat.succ = m + 1 → w ≤ f z := by
    intro z hz; have := hf z; rw [hz] at this; exact this
  rw [triangle_sub_eq]
  have hcard : ((S.filter fun x => ¬x.support.sup Nat.succ ≤ m).card : ℝ) =
      ((L : ℝ) ^ d) ^ (m + 1) - ((L : ℝ) ^ d) ^ m := by
    have h := card_filter_add_card_filter_not (s := S)
      (fun x => x.support.sup Nat.succ ≤ m)
    rw [hS, filter_toFinset_level_ball_succ, card_toFinset_level_ball,
      card_toFinset_level_ball] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact_mod_cast h
  calc w ^ 2 * ((((L : ℝ) ^ d) ^ (m + 1) - ((L : ℝ) ^ d) ^ m) *
        ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f z)
      = ∑ x ∈ S, ∑ y ∈ S, (if ¬x.support.sup Nat.succ ≤ m ∧ y.support.sup Nat.succ ≤ m then
          w ^ 2 * f y else 0) := by
        have hrow : ∀ x ∈ S, (∑ y ∈ S, (if ¬x.support.sup Nat.succ ≤ m ∧
            y.support.sup Nat.succ ≤ m then w ^ 2 * f y else 0)) =
            if ¬x.support.sup Nat.succ ≤ m then w ^ 2 *
              ∑ z ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f z else 0 := by
          intro x _
          by_cases hx : x.support.sup Nat.succ ≤ m
          · simp [hx]
          · simp only [hx, not_false_eq_true, true_and, ite_true]
            rw [← sum_filter, hS, filter_toFinset_level_ball_succ, mul_sum]
        rw [sum_congr rfl hrow, ← sum_filter, sum_const, nsmul_eq_mul, hcard]
        ring
    _ ≤ _ := by
        refine sum_le_sum fun x hx => sum_le_sum fun y hy => ?_
        rw [hS, mem_toFinset_level_ball] at hx hy
        have hfx := hf0 x; have hfyx := hf0 (y - x); have hfy := hf0 y
        split_ifs with h1 h2 h2
        · exact absurd h2.1 h1.1
        · have hxm : x.support.sup Nat.succ = m + 1 := by omega
          have h3 := level_le_max_level_sub x y
          have h4 := level_sub_le_max_level x y
          have hyxm : (y - x).support.sup Nat.succ = m + 1 := by omega
          calc w ^ 2 * f y = w * w * f y := by ring
            _ ≤ f x * f (y - x) * f y :=
              mul_le_mul_of_nonneg_right (mul_le_mul (hw _ hxm) (hw _ hyxm) hw0 hfx) hfy
        · exact le_rfl
        · positivity

/-! ### The triangle sum under two-sided power-law bounds -/

/-- `Δ_0 = f(0)³`. -/
theorem triangle_zero (f : (ℕ →₀ (Fin d → ZMod L)) → ℝ) :
    ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) 0).toFinset,
      ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) 0).toFinset, f x * f (y - x) * f y =
      f 0 ^ 3 := by
  rw [toFinset_level_ball_zero, sum_singleton, sum_singleton]
  simp only [sub_self]
  ring

/-- For nonnegative `f`, the full triangle sum converges exactly when the ball sums `Δ_N`
are bounded. -/
theorem summable_triangle_iff_bounded {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) :
    Summable (fun p : (ℕ →₀ (Fin d → ZMod L)) × (ℕ →₀ (Fin d → ZMod L)) =>
      f p.1 * f (p.2 - p.1) * f p.2) ↔
    ∃ M, ∀ N, ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
      ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ≤ M := by
  have hg0 : ∀ p : (ℕ →₀ (Fin d → ZMod L)) × (ℕ →₀ (Fin d → ZMod L)),
      0 ≤ f p.1 * f (p.2 - p.1) * f p.2 := fun p => by
    have := hf0 p.1; have := hf0 (p.2 - p.1); have := hf0 p.2; positivity
  constructor
  · intro hs
    refine ⟨∑' p : (ℕ →₀ (Fin d → ZMod L)) × (ℕ →₀ (Fin d → ZMod L)),
      f p.1 * f (p.2 - p.1) * f p.2, fun N => ?_⟩
    rw [← sum_product' (f := fun x y => f x * f (y - x) * f y)]
    exact hs.sum_le_tsum _ fun p _ => hg0 p
  · rintro ⟨M, hM⟩
    refine summable_of_sum_le (c := M) (fun p => hg0 p) fun u => ?_
    set N := u.sup fun p => max (p.1.support.sup Nat.succ) (p.2.support.sup Nat.succ)
    refine le_trans ?_ (hM N)
    rw [← sum_product' (f := fun x y => f x * f (y - x) * f y)]
    refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => hg0 p
    have := le_sup (f := fun p : (ℕ →₀ (Fin d → ZMod L)) × (ℕ →₀ (Fin d → ZMod L)) =>
      max (p.1.support.sup Nat.succ) (p.2.support.sup Nat.succ)) hp
    rw [mem_product, mem_toFinset_level_ball, mem_toFinset_level_ball]
    exact max_le_iff.1 this

variable {α c C : ℝ}

/-- **Increment bounds** with explicit constants: for `m ≥ 0`,
`c³ (L^d - 1)/(L^d L^α) L^{(3α-d)(m+1)} ≤ Δ_{m+1} - Δ_m` and
`Δ_{m+1} - Δ_m ≤ 3 C³ (1 + L^α/(L^α - 1)) L^{(3α-d)(m+1)}`. -/
theorem triangle_increment_bounds (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ}
    (hf : ∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
      f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) (m : ℕ) :
    c ^ 3 * ((L : ℝ) ^ d - 1) / ((L : ℝ) ^ d * (L : ℝ) ^ α) *
        (L : ℝ) ^ ((3 * α - d) * ((m + 1 : ℕ) : ℝ)) ≤
      (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
          f x * f (y - x) * f y) -
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f x * f (y - x) * f y ∧
    (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (m + 1)).toFinset,
          f x * f (y - x) * f y) -
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset,
        ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) m).toFinset, f x * f (y - x) * f y ≤
      3 * C ^ 3 * (1 + (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) *
        (L : ℝ) ^ ((3 * α - d) * ((m + 1 : ℕ) : ℝ)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hd : d ≠ 0 := by rintro rfl; simp at hαd; linarith
  obtain ⟨q, hq⟩ : ∃ q, q = (L : ℝ) ^ (-((d : ℝ) - α)) := ⟨_, rfl⟩
  have hq0 : 0 < q := hq ▸ Real.rpow_pos_of_pos hL0 _
  have hq1 : q ≤ 1 := hq ▸ Real.rpow_le_one_of_one_le_of_nonpos hL1.le (by linarith)
  have hpow : ∀ k : ℕ, (L : ℝ) ^ (-((d : ℝ) - α) * (k : ℝ)) = q ^ k := fun k => by
    rw [hq, Real.rpow_mul_natCast hL0.le]
  have hlow : ∀ x : ℕ →₀ (Fin d → ZMod L), c * q ^ x.support.sup Nat.succ ≤ f x := fun x => by
    rw [← hpow]; exact (hf x).1
  have hup : ∀ x : ℕ →₀ (Fin d → ZMod L), f x ≤ C * q ^ x.support.sup Nat.succ := fun x => by
    rw [← hpow]; exact (hf x).2
  have hf0 : ∀ x, 0 ≤ f x := fun x => (by positivity : 0 ≤ c * q ^ _).trans (hlow x)
  have hC : 0 ≤ C := by
    have h1 := hlow 0
    have h2 := hup 0
    simp only [Finsupp.support_zero, Finset.sup_empty, Nat.bot_eq_zero, pow_zero,
      mul_one] at h1 h2
    linarith
  have hP : (2 : ℝ) ≤ (L : ℝ) ^ d := by
    have := le_self_pow₀ hL1.le hd
    have h2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hρ : (L : ℝ) ^ d * q = (L : ℝ) ^ α := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_add hL0]
    congr 1; ring
  have hρ1 : 1 < (L : ℝ) ^ α := Real.one_lt_rpow hL1 hα
  have hr : (L : ℝ) ^ ((3 * α - d) * ((m + 1 : ℕ) : ℝ)) =
      (q ^ 2 * (L : ℝ) ^ d * (L : ℝ) ^ α) ^ (m + 1) := by
    rw [Real.rpow_mul_natCast hL0.le]
    congr 1
    rw [show 3 * α - (d : ℝ) = α + α + (-((d : ℝ) - α)) by ring, Real.rpow_add hL0,
      Real.rpow_add hL0, ← hq, ← hρ]
    ring
  rw [hr]
  constructor
  · have hF := le_sum_level_ball hc.le hq0.le hq1 hlow m
    rw [hρ] at hF
    have hinc := le_triangle_increment hc.le hq0.le hf0 hlow m
    have hPm : ((L : ℝ) ^ d) ^ m ≤ ((L : ℝ) ^ d) ^ (m + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hρ0 : 0 < (L : ℝ) ^ α := by linarith
    refine le_trans (le_of_eq ?_) (le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hF (sub_nonneg.2 hPm)) (sq_nonneg (c * q ^ (m + 1)))) hinc)
    field_simp
    ring
  · have hF := sum_level_ball_le hC hq0.le hup (m + 1)
    rw [hρ] at hF
    have hgeom : ∑ k ∈ range (m + 1 + 1), ((L : ℝ) ^ α) ^ k ≤
        (1 + (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)) * ((L : ℝ) ^ α) ^ (m + 1) := by
      rw [sum_range_succ', pow_zero]
      have h1 := sum_range_pow_succ_le hρ1 (m + 1)
      have h2 : 1 ≤ ((L : ℝ) ^ α) ^ (m + 1) := one_le_pow₀ hρ1.le
      nlinarith
    have hinc := triangle_increment_le hf0 hup m
    refine hinc.trans (le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (hF.trans (mul_le_mul_of_nonneg_left hgeom hC)) (by positivity))
      (sq_nonneg (C * q ^ (m + 1)))) (le_of_eq ?_))
    ring

/-- The increment bounds with constants depending only on `c, C, L, d, α`, in the indexing
`a L^{(3α-d)n} ≤ Δ_n - Δ_{n-1} ≤ A L^{(3α-d)n}` for `n ≥ 1`. -/
theorem exists_triangle_increment_bounds (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    (hcC : c ≤ C) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      ∀ n : ℕ, 1 ≤ n →
        a * (L : ℝ) ^ ((3 * α - d) * (n : ℝ)) ≤
          (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
              f x * f (y - x) * f y) -
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
              f x * f (y - x) * f y ∧
        (∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) n).toFinset,
              f x * f (y - x) * f y) -
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) (n - 1)).toFinset,
              f x * f (y - x) * f y ≤ A * (L : ℝ) ^ ((3 * α - d) * (n : ℝ)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hd : d ≠ 0 := by rintro rfl; simp at hαd; linarith
  have hP : (1 : ℝ) < (L : ℝ) ^ d := one_lt_pow₀ hL1 hd
  have hρ1 : 1 < (L : ℝ) ^ α := Real.one_lt_rpow hL1 hα
  have hC : 0 < C := hc.trans_le hcC
  refine ⟨c ^ 3 * ((L : ℝ) ^ d - 1) / ((L : ℝ) ^ d * (L : ℝ) ^ α),
    3 * C ^ 3 * (1 + (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)), ?_, ?_, fun f hf n hn => ?_⟩
  · have : 0 < (L : ℝ) ^ d - 1 := by linarith
    positivity
  · have : 0 < (L : ℝ) ^ α - 1 := by linarith
    positivity
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa using triangle_increment_bounds hL hα hαd hc hf m

/-- **The triangle threshold.** The full triangle sum `∑_{x,y} f(x) f(y - x) f(y)` converges
exactly when `3α < d`. -/
theorem summable_triangle_iff (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ}
    (hf : ∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
      f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) :
    Summable (fun p : (ℕ →₀ (Fin d → ZMod L)) × (ℕ →₀ (Fin d → ZMod L)) =>
      f p.1 * f (p.2 - p.1) * f p.2) ↔ 3 * α < d := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hd : d ≠ 0 := by rintro rfl; simp at hαd; linarith
  have hf0 : ∀ x, 0 ≤ f x := fun x =>
    (mul_nonneg hc.le (Real.rpow_nonneg hL0.le _)).trans (hf x).1
  have hP : (1 : ℝ) < (L : ℝ) ^ d := one_lt_pow₀ hL1 hd
  have hρ1 : 1 < (L : ℝ) ^ α := Real.one_lt_rpow hL1 hα
  have hpow : ∀ n : ℕ, (L : ℝ) ^ ((3 * α - d) * ((n + 1 : ℕ) : ℝ)) =
      ((L : ℝ) ^ (3 * α - d)) ^ (n + 1) := fun n => Real.rpow_mul_natCast hL0.le _ _
  rw [summable_triangle_iff_bounded hf0, bddAbove_iff_of_increment_bounds
    (Real.rpow_pos_of_pos hL0 _) (a := c ^ 3 * ((L : ℝ) ^ d - 1) / ((L : ℝ) ^ d * (L : ℝ) ^ α))
    (A := 3 * C ^ 3 * (1 + (L : ℝ) ^ α / ((L : ℝ) ^ α - 1)))
    (by have : 0 < (L : ℝ) ^ d - 1 := by linarith
        positivity)
    (fun n => by rw [← hpow]; exact (triangle_increment_bounds hL hα hαd hc hf n).1)
    (fun n => by rw [← hpow]; exact (triangle_increment_bounds hL hα hαd hc hf n).2)]
  rw [← Real.rpow_zero (L : ℝ), Real.rpow_lt_rpow_left_iff hL1]
  constructor <;> intro h <;> linarith

omit [NeZero L] in
/-- Bounds on `Δ_0 = f(0)³`. -/
theorem triangle_zero_bounds (hc : 0 < c) {f : (ℕ →₀ (Fin d → ZMod L)) → ℝ}
    (hf : ∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
      f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) :
    c ^ 3 ≤ f 0 ^ 3 ∧ f 0 ^ 3 ≤ C ^ 3 := by
  have h := hf 0
  simp only [Finsupp.support_zero, Finset.sup_empty, Nat.bot_eq_zero, CharP.cast_eq_zero,
    mul_zero, Real.rpow_zero, mul_one] at h
  exact ⟨pow_le_pow_left₀ hc.le h.1 3, pow_le_pow_left₀ (hc.le.trans h.1) h.2 3⟩

/-- **The critical case `3α = d`:** `Δ_N ≍ N + 1`, with constants depending only on
`c, C, L, d, α`. -/
theorem exists_triangle_linear_bounds (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d) (hc : 0 < c)
    (hcC : c ≤ C) (h3 : 3 * α = d) :
    ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      ∀ N : ℕ, k * (N + 1) ≤
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ∧
        ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ≤
          K * (N + 1) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hd : d ≠ 0 := by rintro rfl; simp at hαd; linarith
  have hP : (1 : ℝ) < (L : ℝ) ^ d := one_lt_pow₀ hL1 hd
  have hC : 0 < C := hc.trans_le hcC
  set a := c ^ 3 * ((L : ℝ) ^ d - 1) / ((L : ℝ) ^ d * (L : ℝ) ^ α)
  set A := 3 * C ^ 3 * (1 + (L : ℝ) ^ α / ((L : ℝ) ^ α - 1))
  have ha : 0 < a := by
    have : 0 < (L : ℝ) ^ d - 1 := by linarith
    positivity
  refine ⟨min (c ^ 3) a, max (C ^ 3) A, lt_min (by positivity) ha,
    lt_max_of_lt_left (by positivity), fun f hf N => ?_⟩
  have hz : (3 * α - d) = 0 := by linarith
  have h0 := triangle_zero_bounds hc hf
  rw [← triangle_zero f] at h0
  exact linear_bounds_of_increment_bounds (Δ := fun N =>
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
      ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y) h0.1 h0.2
    (fun n => by
      have h := (triangle_increment_bounds hL hα hαd hc hf n).1
      rw [hz, zero_mul, Real.rpow_zero, mul_one] at h
      exact h)
    (fun n => by
      have h := (triangle_increment_bounds hL hα hαd hc hf n).2
      rw [hz, zero_mul, Real.rpow_zero, mul_one] at h
      exact h) N

/-- **The case `3α > d`:** `Δ_N ≍ L^{(3α-d)N}`, with constants depending only on
`c, C, L, d, α`. -/
theorem exists_triangle_geometric_bounds (hL : 2 ≤ L) (hα : 0 < α) (hαd : α < d)
    (hc : 0 < c) (hcC : c ≤ C) (h3 : d < 3 * α) :
    ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ f : (ℕ →₀ (Fin d → ZMod L)) → ℝ,
      (∀ x, c * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ)) ≤ f x ∧
        f x ≤ C * (L : ℝ) ^ (-((d : ℝ) - α) * ((x.support.sup Nat.succ : ℕ) : ℝ))) →
      ∀ N : ℕ, k * (L : ℝ) ^ ((3 * α - d) * (N : ℝ)) ≤
          ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ∧
        ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
            ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y ≤
          K * (L : ℝ) ^ ((3 * α - d) * (N : ℝ)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hd : d ≠ 0 := by rintro rfl; simp at hαd; linarith
  have hP : (1 : ℝ) < (L : ℝ) ^ d := one_lt_pow₀ hL1 hd
  have hρ1 : 1 < (L : ℝ) ^ α := Real.one_lt_rpow hL1 hα
  have hC : 0 < C := hc.trans_le hcC
  have hr1 : 1 < (L : ℝ) ^ (3 * α - d) := Real.one_lt_rpow hL1 (by linarith)
  set r := (L : ℝ) ^ (3 * α - d)
  set a := c ^ 3 * ((L : ℝ) ^ d - 1) / ((L : ℝ) ^ d * (L : ℝ) ^ α)
  set A := 3 * C ^ 3 * (1 + (L : ℝ) ^ α / ((L : ℝ) ^ α - 1))
  have ha : 0 < a := by
    have : 0 < (L : ℝ) ^ d - 1 := by linarith
    positivity
  have hA : 0 < A := by
    have : 0 < (L : ℝ) ^ α - 1 := by linarith
    positivity
  have hpow : ∀ n : ℕ, (L : ℝ) ^ ((3 * α - d) * (n : ℝ)) = r ^ n := fun n =>
    Real.rpow_mul_natCast hL0.le _ _
  have hr0 : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
  refine ⟨min (c ^ 3) a, C ^ 3 + A * (r / (r - 1)), lt_min (by positivity) ha,
    by positivity, fun f hf N => ?_⟩
  have h0 := triangle_zero_bounds hc hf
  rw [← triangle_zero f] at h0
  have hpos : 0 < c ^ 3 := by positivity
  simp only [hpow]
  exact geometric_bounds_of_increment_bounds (Δ := fun N =>
      ∑ x ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset,
      ∑ y ∈ (finite_level_ball (A := Fin d → ZMod L) N).toFinset, f x * f (y - x) * f y)
    hr1 (hpos.trans_le h0.1) h0.1 h0.2 ha.le hA.le
    (fun n => by rw [← hpow]; exact (triangle_increment_bounds hL hα hαd hc hf n).1)
    (fun n => by rw [← hpow]; exact (triangle_increment_bounds hL hα hαd hc hf n).2) N

end PercLib.Models
