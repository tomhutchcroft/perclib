/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Models.LongRange.SoftCutoff
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.NumberTheory.Harmonic.Bounds
public import PercLib.Percolation.Bond.Tightness.Hyperscaling
public import Mathlib.NumberTheory.ZetaValues

/-!
# The Fourier symbol of a lazy power-law step distribution on `ℤ^d` (VJCW)

Let `p` be a probability mass function on `ℤ^d` with `p(0) ≥ 1/2` and
`c |x|^{-d-α} ≤ p(x) ≤ C |x|^{-d-α}` for `x ≠ 0`, where `|x| = √(∑ᵢ xᵢ²)` is the Euclidean
norm and `α > 0`. Its Fourier symbol is `φ(k) = ∑ₓ p(x) cos(k · x)`, written out.

* `fourierSymbol_nonneg`, `fourierSymbol_le_one`, `eq_zero_of_fourierSymbol_eq_one`
  (item 1): `0 ≤ φ ≤ 1`, and on `[-π, π]^d` the value `1` is taken only at `k = 0`.
* `one_sub_fourierSymbol_asymp_of_lt_two`, `…_of_eq_two`, `…_of_two_lt` (item 2): near
  `k = 0`, `1 - φ(k) ≍ |k|^α` for `α < 2`, `≍ |k|² log(1/|k|)` for `α = 2` and `≍ |k|²` for
  `α > 2`, with two-sided bounds by positive constants.

Route: `1 - φ(k) = ∑ₓ p(x)(1 - cos(k·x))`. Upper bound: `1 - cos t ≤ min(t²/2, 2)`,
Cauchy–Schwarz and the shell counts of `PowerLaw.lean` reduce to the one-dimensional sum
`∑_{n ≥ 1} n^{-1-α} min(s²n², 1)` with `s = √d |k|`. Lower bound: pairing `x` with its
reflection in the coordinate `j` where `|k_j|` is largest gives
`1 - cos(a + b) + 1 - cos(a - b) ≥ 2(1 - |cos b|)`, and the points with `x_j = n` and sup
norm `n` (there are `(2n+1)^{d-1}` of them) reduce to `∑_{n ≤ 1/|k_j|} n^{-1-α}(k_j n)²/4`.
-/

@[expose] public section
noncomputable section

open Finset Real
open scoped ENNReal

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### The symbol as a series -/

/-- The series defining the symbol is summable. -/
theorem summable_mul_cos {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hps : Summable p)
    (k : Fin d → ℝ) : Summable fun x => p x * cos (∑ i, k i * (x i : ℝ)) :=
  hps.of_norm_bounded fun x => by
    rw [norm_mul, Real.norm_of_nonneg (hp0 x)]
    exact mul_le_of_le_one_right (hp0 x) (abs_cos_le_one _)

/-- The series `∑ₓ p(x)(1 - cos(k·x))` is summable. -/
theorem summable_mul_one_sub_cos {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hps : Summable p) (k : Fin d → ℝ) :
    Summable fun x => p x * (1 - cos (∑ i, k i * (x i : ℝ))) := by
  simp_rw [mul_sub, mul_one]
  exact hps.sub (summable_mul_cos hp0 hps k)

/-- `1 - φ(k) = ∑ₓ p(x)(1 - cos(k·x))`. -/
theorem one_sub_fourierSymbol_eq {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp : HasSum p 1) (k : Fin d → ℝ) :
    1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) =
      ∑' x, p x * (1 - cos (∑ i, k i * (x i : ℝ))) := by
  have h := hp.summable.tsum_sub (summable_mul_cos hp0 hp.summable k)
  rw [hp.tsum_eq] at h
  rw [← h]
  simp_rw [mul_sub, mul_one]

/-- Every term of `∑ₓ p(x)(1 - cos(k·x))` is nonnegative. -/
theorem mul_one_sub_cos_nonneg {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (k : Fin d → ℝ) (x : Fin d → ℤ) : 0 ≤ p x * (1 - cos (∑ i, k i * (x i : ℝ))) :=
  mul_nonneg (hp0 x) (sub_nonneg.2 (cos_le_one _))

/-! ### Item 1 -/

/-- **Item 1, upper bound.** `φ(k) ≤ 1`. -/
theorem fourierSymbol_le_one {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp : HasSum p 1) (k : Fin d → ℝ) : ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ 1 := by
  have := one_sub_fourierSymbol_eq hp0 hp k
  have h0 : 0 ≤ ∑' x, p x * (1 - cos (∑ i, k i * (x i : ℝ))) :=
    tsum_nonneg (mul_one_sub_cos_nonneg hp0 k)
  linarith

/-- **Item 1, lower bound.** If `p(0) ≥ 1/2` then `φ(k) ≥ 0`. -/
theorem fourierSymbol_nonneg {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp : HasSum p 1) (hlazy : 1 / 2 ≤ p 0) (k : Fin d → ℝ) :
    0 ≤ ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) := by
  classical
  -- `φ(k) ≥ ∑ₓ (2·1_{x=0} - 1) p(x) = 2 p(0) - 1`.
  have hs1 : HasSum (fun x : Fin d → ℤ => if x = 0 then p x else 0) (p 0) := by
    convert hasSum_ite_eq (0 : Fin d → ℤ) (p 0) using 2 with x
    split_ifs with h <;> simp [h]
  have hs : HasSum (fun x : Fin d → ℤ => 2 * (if x = 0 then p x else 0) - p x)
      (2 * p 0 - 1) := (hs1.mul_left 2).sub hp
  have hle : ∀ x, 2 * (if x = 0 then p x else 0) - p x ≤
      p x * cos (∑ i, k i * (x i : ℝ)) := by
    intro x
    split_ifs with h
    · subst h
      have h0 : (∑ i, k i * (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = 0 := by simp
      rw [h0, cos_zero]
      linarith
    · have := neg_one_le_cos (∑ i, k i * (x i : ℝ))
      nlinarith [hp0 x]
  have := hs.tsum_eq ▸ hs.summable.tsum_le_tsum hle (summable_mul_cos hp0 hp.summable k)
  linarith

/-- **Item 1, the value `1`.** If `p(eᵢ) > 0` for every unit vector, which holds when
`p(x) ≥ c |x|^{-d-α}` with `c > 0`, then on `[-π, π]^d` the symbol equals `1` only at
`k = 0`. -/
theorem eq_zero_of_fourierSymbol_eq_one {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp : HasSum p 1) {c α : ℝ} (hc : 0 < c)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)) ≤ p x)
    {k : Fin d → ℝ} (hk : ∀ i, |k i| ≤ π)
    (h1 : ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) = 1) : k = 0 := by
  classical
  have hsum : ∑' x, p x * (1 - cos (∑ i, k i * (x i : ℝ))) = 0 := by
    rw [← one_sub_fourierSymbol_eq hp0 hp k, h1, sub_self]
  have hzero := (hasSum_zero_iff_of_nonneg (mul_one_sub_cos_nonneg hp0 k)).1
    (hsum ▸ (summable_mul_one_sub_cos hp0 hp.summable k).hasSum)
  funext i
  set e : Fin d → ℤ := Pi.single i 1
  have he0 : e ≠ 0 := by
    intro h
    have := congr_fun h i
    simp [e] at this
  have hpe : 0 < p e := by
    refine lt_of_lt_of_le ?_ (hlow e he0)
    have : √(∑ l, ((e l : ℝ)) ^ 2) = 1 := by
      rw [Finset.sum_eq_single i (fun l _ hl => by simp [e, hl]) (by simp)]
      simp [e]
    rw [this, one_rpow, mul_one]
    exact hc
  have hdot : ∑ l, k l * (e l : ℝ) = k i := by
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [e, hl]) (by simp)]
    simp [e]
  have hcos : cos (k i) = 1 := by
    have := congr_fun hzero e
    simp only [Pi.zero_apply, hdot, mul_eq_zero, hpe.ne', false_or] at this
    linarith
  obtain ⟨n, hn⟩ := (cos_eq_one_iff _).1 hcos
  have hn0 : n = 0 := by
    have hb := hk i
    rw [← hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hb
    have : |(n : ℝ)| < 1 := by nlinarith [pi_pos]
    rw [← Int.cast_abs] at this
    have : |n| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.1 this
  rw [← hn, hn0]
  simp

/-! ### Elementary bounds -/

/-- `1 - cos u ≥ u²/4` for `|u| ≤ 1`. -/
theorem sq_div_four_le_one_sub_cos {u : ℝ} (hu : |u| ≤ 1) : u ^ 2 / 4 ≤ 1 - cos u := by
  have h := cos_bound hu
  have h4 : |u| ^ 4 ≤ |u| ^ 2 := pow_le_pow_of_le_one (abs_nonneg u) hu (by norm_num)
  have e4 : |u| ^ 4 = (u ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
  rw [sq_abs, e4] at h4
  rw [e4] at h
  have := (abs_le.1 h).2
  nlinarith [sq_nonneg u]

/-- `1 - cos u ≤ 2 min(u², 1)`. -/
theorem one_sub_cos_le_two_mul_min (u : ℝ) : 1 - cos u ≤ 2 * min (u ^ 2) 1 := by
  rcases le_total (u ^ 2) 1 with h | h
  · rw [min_eq_left h]
    have := one_sub_sq_div_two_le_cos (x := u)
    nlinarith [sq_nonneg u]
  · rw [min_eq_right h]
    linarith [neg_one_le_cos u]

/-- Pairing `a + b` with `a - b`: `(1 - cos(a+b)) + (1 - cos(a-b)) ≥ 2(1 - |cos b|)`. -/
theorem two_mul_one_sub_abs_cos_le (a b : ℝ) :
    2 * (1 - |cos b|) ≤ (1 - cos (a + b)) + (1 - cos (a - b)) := by
  rw [cos_add, cos_sub]
  have h1 : cos a * cos b ≤ |cos b| := by
    calc cos a * cos b ≤ |cos a * cos b| := le_abs_self _
      _ = |cos a| * |cos b| := abs_mul _ _
      _ ≤ 1 * |cos b| := mul_le_mul_of_nonneg_right (abs_cos_le_one a) (abs_nonneg _)
      _ = |cos b| := one_mul _
  linarith

/-! ### Lattice boxes with one coordinate fixed -/

/-- The integer points with `x_j = m` and every coordinate in `[-m, m]`. -/
theorem mem_box_iff (j : Fin d) (m : ℕ) (x : Fin d → ℤ) :
    x ∈ Finset.Icc (Function.update (fun _ => -(m : ℤ)) j (m : ℤ)) (fun _ => (m : ℤ)) ↔
      x j = m ∧ ∀ i, |x i| ≤ m := by
  simp only [Finset.mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨le_antisymm (h2 j) (by simpa using h1 j), fun i => abs_le.2 ⟨?_, h2 i⟩⟩
    have := h1 i
    by_cases hij : i = j
    · subst hij; simp at this; omega
    · simpa [Function.update_of_ne hij] using this
  · rintro ⟨hj, h⟩
    refine ⟨fun i => ?_, fun i => (abs_le.1 (h i)).2⟩
    by_cases hij : i = j
    · subst hij; simp [hj]
    · simpa [Function.update_of_ne hij] using (abs_le.1 (h i)).1

/-- The box has `(2m+1)^{d-1} ≥ m^{d-1}` points. -/
theorem pow_le_card_box (j : Fin d) (m : ℕ) :
    m ^ (d - 1) ≤
      #(Finset.Icc (Function.update (fun _ => -(m : ℤ)) j (m : ℤ)) (fun _ => (m : ℤ))) := by
  classical
  rw [Pi.card_Icc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hj : #(Finset.Icc (Function.update (fun _ => -(m : ℤ)) j (m : ℤ) j) (m : ℤ)) = 1 := by
    simp
  have hi : ∀ i ∈ Finset.univ.erase j,
      #(Finset.Icc (Function.update (fun _ => -(m : ℤ)) j (m : ℤ) i) (m : ℤ)) = 2 * m + 1 := by
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Int.card_Icc]
    omega
  rw [hj, one_mul, Finset.prod_congr rfl hi, Finset.prod_const, Finset.card_erase_of_mem
    (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  exact Nat.pow_le_pow_left (by omega) _

/-- Distinct boxes are disjoint. -/
theorem disjoint_box (j : Fin d) {m m' : ℕ} (h : m ≠ m') :
    Disjoint (Finset.Icc (Function.update (fun _ => -(m : ℤ)) j (m : ℤ)) (fun _ => (m : ℤ)))
      (Finset.Icc (Function.update (fun _ => -(m' : ℤ)) j (m' : ℤ)) (fun _ => (m' : ℤ))) := by
  rw [Finset.disjoint_left]
  intro x h1 h2
  rw [mem_box_iff] at h1 h2
  exact h (by exact_mod_cast h1.1.symm.trans h2.1)

/-! ### Reflection in one coordinate -/

/-- Reflecting the coordinate `j` subtracts `2 k_j x_j` from `k · x`. -/
theorem dot_update_neg (k : Fin d → ℝ) (x : Fin d → ℤ) (j : Fin d) :
    ∑ i, k i * ((Function.update x j (-(x j)) i : ℤ) : ℝ) =
      ∑ i, k i * (x i : ℝ) - 2 * (k j * (x j : ℝ)) := by
  classical
  have h : ∀ i, k i * ((Function.update x j (-(x j)) i : ℤ) : ℝ) =
      k i * (x i : ℝ) - if i = j then 2 * (k j * (x j : ℝ)) else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]
  simp_rw [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Reflecting a coordinate preserves the Euclidean norm. -/
theorem sum_sq_update_neg (x : Fin d → ℤ) (j : Fin d) :
    ∑ i, (((Function.update x j (-(x j)) i : ℤ) : ℝ)) ^ 2 = ∑ i, ((x i : ℝ)) ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [Function.update_of_ne hij]

/-- Reflecting a coordinate is an involution. -/
theorem update_neg_involutive (j : Fin d) :
    Function.Involutive fun x : Fin d → ℤ => Function.update x j (-(x j)) := by
  intro x
  funext i
  by_cases hij : i = j
  · subst hij; simp
  · simp [Function.update_of_ne hij]

/-! ### The lower bound -/

open Classical in
/-- **Master lower bound.** If `p(x) ≥ c |x|^{-d-α}` for `x ≠ 0`, then for every coordinate
`j` and every `N` with `N |k_j| ≤ 1`,
`1 - φ(k) ≥ c (√d)^{-d-α} / 4 · k_j² · ∑_{n=1}^{N} n^{1-α}`. -/
theorem le_one_sub_fourierSymbol {p : (Fin d → ℤ) → ℝ} (hp0 : ∀ x, 0 ≤ p x)
    (hp : HasSum p 1) {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)) ≤ p x)
    (k : Fin d → ℝ) (j : Fin d) (N : ℕ) (hN : (N : ℝ) * |k j| ≤ 1) :
    c * √(d : ℝ) ^ (-((d : ℝ) + α)) / 4 * k j ^ 2 *
        ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α) ≤
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) := by
  classical
  set e : ℝ := -((d : ℝ) + α) with he
  -- The pure power weight.
  set w : (Fin d → ℤ) → ℝ := fun x => if x = 0 then 0 else √(∑ i, ((x i : ℝ)) ^ 2) ^ e
    with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by
    simp only [hw]; split_ifs
    · exact le_rfl
    · exact rpow_nonneg (sqrt_nonneg _) _
  have hwp : ∀ x, w x ≤ p x / c := fun x => by
    rw [le_div_iff₀ hc, mul_comm]
    simp only [hw]; split_ifs with h
    · simpa using hp0 x
    · exact hlow x h
  have hws : Summable w := (hp.summable.div_const c).of_nonneg_of_le hw0 hwp
  -- The weighted series.
  set F : (Fin d → ℤ) → ℝ := fun x => w x * (1 - cos (∑ i, k i * (x i : ℝ))) with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x => mul_nonneg (hw0 x) (sub_nonneg.2 (cos_le_one _))
  have hFs : Summable F := (hws.mul_left 2).of_nonneg_of_le hF0 fun x => by
    simp only [hF]
    rw [mul_comm 2]
    exact mul_le_mul_of_nonneg_left (by linarith [neg_one_le_cos (∑ i, k i * (x i : ℝ))])
      (hw0 x)
  -- Step 1: `c ∑ F ≤ 1 - φ`.
  have h1 : c * ∑' x, F x ≤ 1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) := by
    rw [one_sub_fourierSymbol_eq hp0 hp k, ← tsum_mul_left]
    refine (hFs.mul_left c).tsum_le_tsum (fun x => ?_)
      (summable_mul_one_sub_cos hp0 hp.summable k)
    simp only [hF, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 (cos_le_one _))
    have := hwp x
    rwa [le_div_iff₀ hc, mul_comm] at this
  -- Step 2: reflection in the coordinate `j`.
  set ρ : Equiv.Perm (Fin d → ℤ) := (update_neg_involutive j).toPerm _ with hρ
  have hρw : ∀ x, w (ρ x) = w x := fun x => by
    have h0 : ρ x = 0 ↔ x = 0 := by
      constructor
      · intro h
        have := congr_arg ρ h
        rw [show ρ (ρ x) = x from update_neg_involutive j x] at this
        rw [this]
        funext i; by_cases hij : i = j
        · subst hij; simp [hρ]
        · simp [hρ, Function.update_of_ne hij]
      · rintro rfl
        funext i; by_cases hij : i = j
        · subst hij; simp [hρ]
        · simp [hρ, Function.update_of_ne hij]
    simp only [hw, h0]
    split_ifs
    · rfl
    · simp only [hρ, Function.Involutive.coe_toPerm, sum_sq_update_neg]
  set G : (Fin d → ℤ) → ℝ := fun x => w x * (1 - |cos (k j * (x j : ℝ))|) with hG
  have hG0 : ∀ x, 0 ≤ G x := fun x => mul_nonneg (hw0 x) (sub_nonneg.2 (abs_cos_le_one _))
  have hGs : Summable G := hws.of_nonneg_of_le hG0 fun x =>
    mul_le_of_le_one_right (hw0 x) (by linarith [abs_nonneg (cos (k j * (x j : ℝ)))])
  have h2 : ∑' x, G x ≤ ∑' x, F x := by
    have hFρ : ∑' x, F (ρ x) = ∑' x, F x := ρ.tsum_eq F
    have hsum : ∑' x, (F x + F (ρ x)) = 2 * ∑' x, F x := by
      have h := hFs.tsum_add (ρ.summable_iff.2 hFs)
      simp only [Function.comp_apply] at h
      rw [h, hFρ, two_mul]
    have hle : ∑' x, 2 * G x ≤ ∑' x, (F x + F (ρ x)) := by
      refine (hGs.mul_left 2).tsum_le_tsum (fun x => ?_) (hFs.add (ρ.summable_iff.2 hFs))
      simp only [hF, hG, hρw]
      have hd : ∑ i, k i * ((ρ x i : ℤ) : ℝ) = ∑ i, k i * (x i : ℝ) - 2 * (k j * (x j : ℝ)) :=
        dot_update_neg k x j
      rw [hd]
      have := two_mul_one_sub_abs_cos_le (∑ i, k i * (x i : ℝ) - k j * (x j : ℝ))
        (k j * (x j : ℝ))
      rw [sub_add_cancel, show ∑ i, k i * (x i : ℝ) - k j * (x j : ℝ) - k j * (x j : ℝ) =
        ∑ i, k i * (x i : ℝ) - 2 * (k j * (x j : ℝ)) by ring] at this
      nlinarith [hw0 x]
    rw [tsum_mul_left, hsum] at hle
    linarith
  -- Step 3: the boxes `x_j = m`, `|x_i| ≤ m`, `1 ≤ m ≤ N`.
  set Box : ℕ → Finset (Fin d → ℤ) := fun m =>
    Finset.Icc (Function.update (fun _ => -(m : ℤ)) j (m : ℤ)) (fun _ => (m : ℤ)) with hBox
  have hbox : ∀ n ∈ range N, ((n : ℝ) + 1) ^ (d - 1 : ℕ) *
      (√(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e * ((k j * ((n : ℝ) + 1)) ^ 2 / 4)) ≤
      ∑ x ∈ Box (n + 1), G x := by
    intro n hn
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmN : ((n : ℝ) + 1) ≤ N := by
      have := Finset.mem_range.1 hn
      exact_mod_cast this
    have hlow' : ∀ x ∈ Box (n + 1),
        √(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e * ((k j * ((n : ℝ) + 1)) ^ 2 / 4) ≤ G x := by
      intro x hx
      rw [hBox, mem_box_iff] at hx
      obtain ⟨hxj, hxi⟩ := hx
      have hx0 : x ≠ 0 := fun h => by
        rw [h] at hxj; simp at hxj; omega
      have hpos : 0 < √(∑ i, ((x i : ℝ)) ^ 2) :=
        lt_of_lt_of_le one_pos (one_le_euclid hx0)
      have hle : √(∑ i, ((x i : ℝ)) ^ 2) ≤ √(d : ℝ) * ((n : ℝ) + 1) := by
        rw [← sqrt_sq hm.le, ← sqrt_mul (Nat.cast_nonneg d)]
        refine sqrt_le_sqrt ?_
        calc ∑ i, ((x i : ℝ)) ^ 2 ≤ ∑ _i : Fin d, ((n : ℝ) + 1) ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [← sq_abs]
              refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
              have := hxi i
              rw [← Int.cast_abs]
              exact_mod_cast this
          _ = (d : ℝ) * ((n : ℝ) + 1) ^ 2 := by simp
      have hwx : √(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e ≤ w x := by
        simp only [hw, hx0, ↓reduceIte]
        rw [← mul_rpow (sqrt_nonneg _) hm.le]
        exact rpow_le_rpow_of_nonpos hpos hle
          (by rw [he]; linarith [hα, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
      have hcos : (k j * ((n : ℝ) + 1)) ^ 2 / 4 ≤ 1 - |cos (k j * (x j : ℝ))| := by
        have hxj' : (x j : ℝ) = (n : ℝ) + 1 := by rw [hxj]; push_cast; ring
        rw [hxj']
        have hu : |k j * ((n : ℝ) + 1)| ≤ 1 := by
          rw [abs_mul, abs_of_pos hm, mul_comm]
          exact le_trans (mul_le_mul_of_nonneg_right hmN (abs_nonneg _)) hN
        rw [abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by
          linarith [neg_abs_le (k j * ((n : ℝ) + 1)), two_le_pi],
          by linarith [le_abs_self (k j * ((n : ℝ) + 1)), two_le_pi]⟩)]
        exact sq_div_four_le_one_sub_cos hu
      exact mul_le_mul hwx hcos (by positivity) (hw0 x)
    calc ((n : ℝ) + 1) ^ (d - 1 : ℕ) *
          (√(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e * ((k j * ((n : ℝ) + 1)) ^ 2 / 4))
        ≤ (#(Box (n + 1)) : ℝ) *
          (√(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e * ((k j * ((n : ℝ) + 1)) ^ 2 / 4)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := pow_le_card_box j (n + 1)
          exact_mod_cast this
      _ ≤ ∑ x ∈ Box (n + 1), G x := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          exact Finset.sum_le_sum hlow'
  have h3 : ∑ n ∈ range N, ∑ x ∈ Box (n + 1), G x ≤ ∑' x, G x := by
    rw [← Finset.sum_biUnion]
    · exact hGs.sum_le_tsum _ fun x _ => hG0 x
    · intro a _ b _ hab
      exact disjoint_box j (by omega)
  -- Exponent arithmetic: `m^{d-1} m^{-d-α} m² = m^{1-α}`.
  have hexp : ∀ n : ℕ, ((n : ℝ) + 1) ^ (d - 1 : ℕ) *
      (√(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e * ((k j * ((n : ℝ) + 1)) ^ 2 / 4)) =
      √(d : ℝ) ^ e / 4 * k j ^ 2 * ((n : ℝ) + 1) ^ (1 - α) := by
    intro n
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact j.elim0
    have hcomb : ((n : ℝ) + 1) ^ (d - 1 : ℕ) * ((n : ℝ) + 1) ^ e * ((n : ℝ) + 1) ^ 2 =
        ((n : ℝ) + 1) ^ (1 - α) := by
      rw [← rpow_natCast, ← rpow_natCast _ 2, ← rpow_add hm, ← rpow_add hm]
      congr 1
      rw [he, Nat.cast_sub hd]
      push_cast
      ring
    rw [← hcomb]
    ring
  calc c * √(d : ℝ) ^ e / 4 * k j ^ 2 * ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α)
      = c * ∑ n ∈ range N, ((n : ℝ) + 1) ^ (d - 1 : ℕ) *
          (√(d : ℝ) ^ e * ((n : ℝ) + 1) ^ e * ((k j * ((n : ℝ) + 1)) ^ 2 / 4)) := by
        simp_rw [hexp, ← Finset.mul_sum]
        ring
    _ ≤ c * ∑' x, G x := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_sum hbox).trans h3) hc.le
    _ ≤ c * ∑' x, F x := mul_le_mul_of_nonneg_left h2 hc.le
    _ ≤ _ := h1

/-! ### The upper bound -/

/-- The sup norm of an integer point is at most its Euclidean norm. -/
theorem norm_le_euclid (x : Fin d → ℤ) : ‖x‖ ≤ √(∑ i, ((x i : ℝ)) ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (sqrt_nonneg _)).2 fun i => ?_
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  have := abs_le_euclid x i
  rwa [← Int.cast_abs] at this

/-- The Euclidean norm squared is at most `d` times the sup norm squared. -/
theorem sum_sq_le_card_mul_norm_sq (x : Fin d → ℤ) :
    ∑ i, ((x i : ℝ)) ^ 2 ≤ d * ‖x‖ ^ 2 := by
  calc ∑ i, ((x i : ℝ)) ^ 2 ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        have := norm_le_pi_norm x i
        rwa [Int.norm_eq_abs] at this
    _ = d * ‖x‖ ^ 2 := by simp

/-- **Master upper bound.** If `p(x) ≤ C |x|^{-d-α}` for `x ≠ 0` and `s = √d |k|`, then
`1 - φ(k) ≤ 2C · 2d3^{d-1} · ∑_{n ≥ 1} n^{-1-α} min(s²n², 1)`, in `ℝ≥0∞`. -/
theorem ofReal_one_sub_fourierSymbol_le (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : HasSum p 1) {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)))
    (k : Fin d → ℝ) :
    ENNReal.ofReal (1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ))) ≤
      ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * C) *
        ∑' n : ℕ, ENNReal.ofReal (if n = 0 then 0 else
          (n : ℝ) ^ (-(1 + α)) * min ((√(d : ℝ) * √(∑ i, k i ^ 2)) ^ 2 * (n : ℝ) ^ 2) 1) := by
  classical
  set s := √(d : ℝ) * √(∑ i, k i ^ 2) with hs
  set e : ℝ := -((d : ℝ) + α) with he
  set g : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (if n = 0 then 0 else
    2 * C * ((n : ℝ) ^ e * min (s ^ 2 * (n : ℝ) ^ 2) 1)) with hg
  -- Termwise bound by a function of the sup norm.
  have hterm : ∀ x, ENNReal.ofReal (p x * (1 - cos (∑ i, k i * (x i : ℝ)))) ≤ g ⌊‖x‖⌋₊ := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    have hn : ((⌊‖x‖⌋₊ : ℕ) : ℝ) = ‖x‖ := natCast_floor_norm x
    have hn0 : ⌊‖x‖⌋₊ ≠ 0 := fun h => hx ((floor_norm_eq_zero_iff x).1 h)
    have hnpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.2 hx
    simp only [hg, hn0, ↓reduceIte, hn]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpx : p x ≤ C * ‖x‖ ^ e := (hup x hx).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos hnpos (norm_le_euclid x)
        (by rw [he]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])) hC)
    have hdot : (∑ i, k i * (x i : ℝ)) ^ 2 ≤ s ^ 2 * ‖x‖ ^ 2 := by
      calc (∑ i, k i * (x i : ℝ)) ^ 2 ≤ (∑ i, k i ^ 2) * ∑ i, ((x i : ℝ)) ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ ≤ (∑ i, k i ^ 2) * (d * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left
            (sum_sq_le_card_mul_norm_sq x) (Finset.sum_nonneg fun i _ => sq_nonneg _)
        _ = s ^ 2 * ‖x‖ ^ 2 := by
            rw [hs, mul_pow, sq_sqrt (Nat.cast_nonneg d),
              sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
            ring
    have hcos : 1 - cos (∑ i, k i * (x i : ℝ)) ≤ 2 * min (s ^ 2 * ‖x‖ ^ 2) 1 :=
      (one_sub_cos_le_two_mul_min _).trans (mul_le_mul_of_nonneg_left
        (min_le_min_right _ hdot) (by norm_num))
    calc p x * (1 - cos (∑ i, k i * (x i : ℝ)))
        ≤ (C * ‖x‖ ^ e) * (2 * min (s ^ 2 * ‖x‖ ^ 2) 1) :=
          mul_le_mul hpx hcos (sub_nonneg.2 (cos_le_one _))
            (mul_nonneg hC (rpow_nonneg (norm_nonneg _) _))
      _ = 2 * C * (‖x‖ ^ e * min (s ^ 2 * ‖x‖ ^ 2) 1) := by ring
  have hsum : ENNReal.ofReal (1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ))) ≤
      ∑' x : Fin d → ℤ, g ⌊‖x‖⌋₊ := by
    rw [one_sub_fourierSymbol_eq hp0 hp k, ENNReal.ofReal_tsum_of_nonneg
      (mul_one_sub_cos_nonneg hp0 k) (summable_mul_one_sub_cos hp0 hp.summable k)]
    exact ENNReal.tsum_le_tsum hterm
  refine hsum.trans ((tsum_comp_floor_norm_bounds hd g (by simp [hg])).2.trans ?_)
  refine le_trans ?_ (le_of_eq (mul_assoc _ _ _).symm)
  refine mul_le_mul' le_rfl ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun n => ?_
  by_cases hn : n = 0
  · simp [hg, hn]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  simp only [hg, hn, ↓reduceIte]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by linarith)]
  refine le_of_eq (congr_arg ENNReal.ofReal ?_)
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
  have hpow : ((n ^ (d - 1) : ℕ) : ℝ) * (n : ℝ) ^ e = (n : ℝ) ^ (-(1 + α)) := by
    rw [Nat.cast_pow, ← rpow_natCast, ← rpow_add hnpos, hd1, he]
    congr 1
    ring
  rw [← hpow]
  ring

/-- **The one-dimensional sum, split at `n = 1/s`.** For `0 < s ≤ 1` and `N = ⌊1/s⌋`:
`∑_{n ≥ 1} n^{-1-α} min(s²n², 1) ≤ s² ∑_{n=1}^{N} n^{1-α} + (1 + 1/α) s^α`. -/
theorem tsum_rpow_mul_min_le {α s : ℝ} (hα : 0 < α) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ∑' n : ℕ, ENNReal.ofReal (if n = 0 then 0 else (n : ℝ) ^ (-(1 + α)) *
        min (s ^ 2 * (n : ℝ) ^ 2) 1)
      ≤ ENNReal.ofReal (s ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α)) +
        ENNReal.ofReal ((1 + 1 / α) * s ^ α) := by
  classical
  set N := ⌊1 / s⌋₊ with hN
  have hr : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  -- Split each term.
  set A : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (if n = 0 ∨ N < n then 0 else
    s ^ 2 * (n : ℝ) ^ (1 - α)) with hA
  set B : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (if 1 / s ≤ n then (n : ℝ) ^ (-(1 + α)) else 0)
    with hB
  have hsplit : ∀ n : ℕ, ENNReal.ofReal (if n = 0 then 0 else
      (n : ℝ) ^ (-(1 + α)) * min (s ^ 2 * (n : ℝ) ^ 2) 1) ≤ A n + B n := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    simp only [hn, ↓reduceIte, hA, hB, false_or]
    by_cases hNn : N < n
    · -- `n > N`, so `n ≥ 1/s`.
      have h1 : 1 / s ≤ n := by
        have := Nat.lt_of_floor_lt hNn
        exact this.le
      rw [ite_eq_left hNn, ite_eq_left h1, ENNReal.ofReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (rpow_nonneg hnpos.le _)
        (min_le_right _ _))
    · rw [ite_eq_right hNn]
      refine (ENNReal.ofReal_le_ofReal ?_).trans le_self_add
      calc (n : ℝ) ^ (-(1 + α)) * min (s ^ 2 * (n : ℝ) ^ 2) 1
          ≤ (n : ℝ) ^ (-(1 + α)) * (s ^ 2 * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (rpow_nonneg hnpos.le _)
        _ = s ^ 2 * (n : ℝ) ^ (1 - α) := by
            have h2 : (n : ℝ) ^ (-(1 + α)) * (n : ℝ) ^ 2 = (n : ℝ) ^ (1 - α) := by
              rw [← rpow_natCast (n : ℝ) 2, ← rpow_add hnpos]
              congr 1
              push_cast
              ring
            rw [mul_left_comm, h2]
  -- The first part is a finite sum.
  have hAsum : ∑' n, A n = ENNReal.ofReal (s ^ 2 * ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α)) := by
    rw [tsum_eq_sum (s := range (N + 1)) fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp only [hA]
      rw [ite_eq_left (Or.inr (by omega)), ENNReal.ofReal_zero]]
    rw [Finset.sum_range_succ', Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun n _ =>
      mul_nonneg (sq_nonneg s) (rpow_nonneg (by positivity) _)]
    simp only [hA, Nat.succ_ne_zero, false_or, true_or, ↓reduceIte, ENNReal.ofReal_zero,
      add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ite_eq_right (by have := Finset.mem_range.1 hn; omega)]
    push_cast
    rfl
  have hBsum : ∑' n, B n ≤ ENNReal.ofReal ((1 + 1 / α) * s ^ α) := by
    have := tsum_ite_rpow_le α hα hr
    have hpow : (1 / s) ^ (-α) = s ^ α := by
      rw [one_div, inv_rpow hs0.le, rpow_neg hs0.le, inv_inv]
    rwa [hpow] at this
  calc _ ≤ ∑' n, (A n + B n) := ENNReal.tsum_le_tsum hsplit
    _ = ∑' n, A n + ∑' n, B n := ENNReal.tsum_add
    _ ≤ _ := add_le_add (le_of_eq hAsum) hBsum

/-! ### One-dimensional sums -/

/-- `∑_{n=1}^{N} n^{1-α} ≥ N^{2-α}/2` for `α > 0` and `N ≥ 1`. -/
theorem half_rpow_le_sum_rpow {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (2 - α) / 2 ≤ ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgauss : ∀ M : ℕ, (∑ n ∈ range M, ((n : ℝ) + 1)) * 2 = M * (M + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, add_mul, ih]; push_cast; ring
  have hterm : ∀ n ∈ range N, ((n : ℝ) + 1) * (N : ℝ) ^ (-α) ≤ ((n : ℝ) + 1) ^ (1 - α) := by
    intro n hn
    have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmN : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hn
    rw [show (1 : ℝ) - α = 1 + -α by ring, rpow_add hm, rpow_one]
    exact mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hm hmN (by linarith)) hm.le
  calc (N : ℝ) ^ (2 - α) / 2 = (N : ℝ) ^ (-α) * ((N : ℝ) * N) / 2 := by
        rw [show (2 : ℝ) - α = -α + 1 + 1 by ring, rpow_add hNpos, rpow_add hNpos, rpow_one]
        ring
    _ ≤ (N : ℝ) ^ (-α) * ((N : ℝ) * (N + 1)) / 2 := by
        gcongr
        linarith
    _ = ∑ n ∈ range N, ((n : ℝ) + 1) * (N : ℝ) ^ (-α) := by
        rw [← Finset.sum_mul, ← hgauss N]
        ring
    _ ≤ _ := Finset.sum_le_sum hterm

/-- `∑_{n=1}^{N} n^{1-α} ≤ (1 + 1/(2-α)) N^{2-α}` for `0 < α < 2`. -/
theorem sum_rpow_le_of_lt_two {α : ℝ} (hα2 : α < 2) (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α) ≤ (1 + 1 / (2 - α)) * (N : ℝ) ^ (2 - α) := by
  have h2 : 0 < 2 - α := by linarith
  have hN0 : 0 ≤ (N : ℝ) ^ (2 - α) := rpow_nonneg (Nat.cast_nonneg N) _
  rcases le_or_gt 1 α with h1 | h1
  · have := PercLib.Percolation.Bond.sum_rpow_neg_le N (θ := α - 1) (by linarith) (by linarith)
    rw [show -(α - 1) = 1 - α by ring, show 1 - (α - 1) = 2 - α by ring] at this
    refine this.trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hN0
  · have hterm : ∀ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α) ≤ (N : ℝ) ^ (1 - α) := fun n hn =>
      rpow_le_rpow (by positivity) (by exact_mod_cast Finset.mem_range.1 hn) (by linarith)
    calc ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α) ≤ ∑ _n ∈ range N, (N : ℝ) ^ (1 - α) :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) ^ (2 - α) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos N with h0 | hpos
          · subst h0; simp [zero_rpow h2.ne']
          · have hNpos : (0 : ℝ) < N := by exact_mod_cast hpos
            rw [show (2 : ℝ) - α = 1 + (1 - α) by ring, rpow_add hNpos, rpow_one]
      _ ≤ _ := le_mul_of_one_le_left hN0 (by linarith [one_div_pos.2 h2])

/-- For `α = 2`: `log(N+1) ≤ ∑_{n=1}^{N} 1/n ≤ 1 + log N`. -/
theorem log_le_sum_rpow_neg_one_le (N : ℕ) :
    Real.log ((N : ℝ) + 1) ≤ ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - (2 : ℝ)) ∧
      ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - (2 : ℝ)) ≤ 1 + Real.log N := by
  have hh : ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - (2 : ℝ)) = (harmonic N : ℝ) := by
    rw [harmonic]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (1 : ℝ) - 2 = -1 by norm_num, rpow_neg_one]
  rw [hh]
  have h1 := log_add_one_le_harmonic N
  push_cast at h1
  exact ⟨h1, harmonic_le_one_add_log N⟩

/-- For `α > 2`: `∑_{n=1}^{N} n^{1-α} ≤ 1 + 1/(α-2)`. -/
theorem sum_rpow_le_of_two_lt {α : ℝ} (hα2 : 2 < α) (N : ℕ) :
    ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α) ≤ 1 + 1 / (α - 2) := by
  have hβ : 0 < α - 2 := by linarith
  have h := tsum_ite_rpow_le (α - 2) hβ (le_refl (1 : ℝ))
  rw [one_rpow, mul_one] at h
  have hnn : ∀ n ∈ range N, 0 ≤ ((n : ℝ) + 1) ^ (1 - α) := fun n _ =>
    rpow_nonneg (by positivity) _
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_sum_of_nonneg hnn]
  refine le_trans ?_ h
  have hsum : ∑ n ∈ range N, ENNReal.ofReal (((n : ℝ) + 1) ^ (1 - α)) =
      ∑ m ∈ (range N).map ⟨Nat.succ, Nat.succ_injective⟩,
        ENNReal.ofReal (if (1 : ℝ) ≤ m then (m : ℝ) ^ (-(1 + (α - 2))) else 0) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      le_add_iff_nonneg_left, Nat.cast_nonneg, ↓reduceIte]
    congr 2
    ring
  rw [hsum]
  exact ENNReal.sum_le_tsum _

/-- A coordinate of largest absolute value carries a `1/√d` share of the Euclidean norm. -/
theorem exists_euclid_le_mul_abs (hd : 1 ≤ d) (k : Fin d → ℝ) :
    ∃ j, (∀ i, |k i| ≤ |k j|) ∧ √(∑ i, k i ^ 2) ≤ √(d : ℝ) * |k j| := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |k i|) Finset.univ_nonempty
  refine ⟨j, fun i => hj i (Finset.mem_univ i), ?_⟩
  rw [← sqrt_sq (abs_nonneg (k j)), ← sqrt_mul (Nat.cast_nonneg d)]
  refine sqrt_le_sqrt ?_
  calc ∑ i, k i ^ 2 ≤ ∑ _i : Fin d, |k j| ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hj i (Finset.mem_univ i)) 2
    _ = (d : ℝ) * |k j| ^ 2 := by simp

/-- The integer part of `1/t` for `0 < t ≤ 1/2`. -/
theorem floor_one_div_bounds {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    1 ≤ ⌊1 / t⌋₊ ∧ (⌊1 / t⌋₊ : ℝ) * t ≤ 1 ∧ 1 / (2 * t) ≤ ⌊1 / t⌋₊ ∧
      1 / t < (⌊1 / t⌋₊ : ℝ) + 1 := by
  have h2 : 2 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
  have hfl := Nat.floor_le (show 0 ≤ 1 / t by positivity)
  have hlt := Nat.lt_floor_add_one (1 / t)
  refine ⟨Nat.le_floor (by push_cast; linarith), ?_, ?_, hlt⟩
  · calc (⌊1 / t⌋₊ : ℝ) * t ≤ (1 / t) * t := mul_le_mul_of_nonneg_right hfl ht0.le
      _ = 1 := by field_simp
  · have : 1 / (2 * t) = (1 / t) / 2 := by field_simp
    rw [this]
    linarith

/-! ### Assembly -/

/-- The upper bound in real form, for `0 < s = √d |k| ≤ 1`. -/
theorem one_sub_fourierSymbol_le_of_small (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : HasSum p 1) {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)))
    (k : Fin d → ℝ) (hs0 : 0 < √(d : ℝ) * √(∑ i, k i ^ 2))
    (hs1 : √(d : ℝ) * √(∑ i, k i ^ 2) ≤ 1) :
    1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤
      ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) * (2 * C) *
        ((√(d : ℝ) * √(∑ i, k i ^ 2)) ^ 2 *
            ∑ n ∈ range ⌊1 / (√(d : ℝ) * √(∑ i, k i ^ 2))⌋₊, ((n : ℝ) + 1) ^ (1 - α) +
          (1 + 1 / α) * (√(d : ℝ) * √(∑ i, k i ^ 2)) ^ α) := by
  set s := √(d : ℝ) * √(∑ i, k i ^ 2) with hs
  have hS0 : 0 ≤ ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α) :=
    Finset.sum_nonneg fun n _ => rpow_nonneg (by positivity) _
  have hX : 0 ≤ s ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α) := by positivity
  have hY : 0 ≤ (1 + 1 / α) * s ^ α := by positivity
  have h1 := ofReal_one_sub_fourierSymbol_le hd hp0 hp hC hα hup k
  have h2 := tsum_rpow_mul_min_le hα hs0 hs1
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_add hX hY]
  exact h1.trans (mul_le_mul' le_rfl h2)

/-- `s² (1/s)^{2-α} = s^α` for `s > 0`. -/
theorem sq_mul_one_div_rpow {s α : ℝ} (hs : 0 < s) : s ^ 2 * (1 / s) ^ (2 - α) = s ^ α := by
  rw [one_div, inv_rpow hs.le, ← rpow_neg hs.le, ← rpow_natCast s 2, ← rpow_add hs]
  congr 1
  push_cast
  ring

/-- The constants are positive: `0 < c ≤ p(eᵢ) ≤ C`. -/
theorem pos_of_low_up (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ} {c C e : ℝ} (hc : 0 < c)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ e ≤ p x)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ e) : 0 < C := by
  classical
  set i : Fin d := ⟨0, hd⟩
  set x : Fin d → ℤ := Pi.single i 1
  have hx0 : x ≠ 0 := by
    intro h
    have := congr_fun h i
    simp [x] at this
  have h1 : √(∑ l, ((x l : ℝ)) ^ 2) = 1 := by
    rw [Finset.sum_eq_single i (fun l _ hl => by simp [x, hl]) (by simp)]
    simp [x]
  have := (hlow x hx0).trans (hup x hx0)
  rw [h1, one_rpow, mul_one, mul_one] at this
  linarith

/-- **Item 2, `0 < α < 2`.** `1 - φ(k) ≍ |k|^α` near `k = 0`. -/
theorem one_sub_fourierSymbol_asymp_of_lt_two (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : HasSum p 1) {c C α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hα2 : α < 2)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)) ≤ p x)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α))) :
    ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin d → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * √(∑ i, k i ^ 2) ^ α ≤ 1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ b * √(∑ i, k i ^ 2) ^ α := by
  have hCpos := pos_of_low_up hd hc hlow hup
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : 1 ≤ √(d : ℝ) := by rw [one_le_sqrt]; exact_mod_cast hd
  have hsd0 : 0 < √(d : ℝ) := by linarith
  have h2α : 0 < 2 - α := by linarith
  set K : ℝ := ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by rw [hK]; exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  set e : ℝ := -((d : ℝ) + α) with he
  refine ⟨1 / (2 * √(d : ℝ)), by positivity,
    c * √(d : ℝ) ^ e / 4 * ((1 / 2) ^ (2 - α) / 2) / √(d : ℝ) ^ α, by positivity,
    K * (2 * C) * ((1 + 1 / (2 - α)) + (1 + 1 / α)) * √(d : ℝ) ^ α, by positivity, ?_⟩
  intro k hr0 hrδ
  set r := √(∑ i, k i ^ 2) with hr
  have hrhalf : r ≤ 1 / 2 := hrδ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  constructor
  · -- Lower bound.
    obtain ⟨j, -, hrj⟩ := exists_euclid_le_mul_abs hd k
    set t := |k j| with ht
    have ht0 : 0 < t := by
      by_contra h
      have : t = 0 := le_antisymm (not_lt.1 h) (abs_nonneg _)
      rw [this, mul_zero] at hrj
      linarith
    have htr : t ≤ r := Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => k i ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
    obtain ⟨hN1, hNt, hN2, -⟩ := floor_one_div_bounds ht0 (htr.trans hrhalf)
    set N := ⌊1 / t⌋₊
    have hL := le_one_sub_fourierSymbol hp0 hp hc hα hlow k j N hNt
    have hS := half_rpow_le_sum_rpow hα hN1
    have hNpow : (1 / (2 * t)) ^ (2 - α) ≤ (N : ℝ) ^ (2 - α) :=
      rpow_le_rpow (by positivity) hN2 h2α.le
    have hkt : k j ^ 2 = t ^ 2 := (sq_abs _).symm
    have hcore : t ^ 2 * (1 / (2 * t)) ^ (2 - α) = (1 / 2) ^ (2 - α) * t ^ α := by
      rw [show 1 / (2 * t) = (1 / 2) * (1 / t) by ring, mul_rpow (by norm_num) (by positivity),
        mul_left_comm, sq_mul_one_div_rpow ht0]
    have hrt : (r / √(d : ℝ)) ^ α ≤ t ^ α :=
      rpow_le_rpow (by positivity) (by rw [div_le_iff₀ hsd0]; linarith) hα.le
    rw [div_rpow (by positivity) hsd0.le] at hrt
    have hc0 : 0 ≤ c * √(d : ℝ) ^ e / 4 := by positivity
    calc c * √(d : ℝ) ^ e / 4 * ((1 / 2) ^ (2 - α) / 2) / √(d : ℝ) ^ α * r ^ α
        = c * √(d : ℝ) ^ e / 4 * ((1 / 2) ^ (2 - α) / 2) * (r ^ α / √(d : ℝ) ^ α) := by ring
      _ ≤ c * √(d : ℝ) ^ e / 4 * ((1 / 2) ^ (2 - α) / 2) * t ^ α :=
          mul_le_mul_of_nonneg_left hrt (by positivity)
      _ = c * √(d : ℝ) ^ e / 4 * (t ^ 2 * ((1 / (2 * t)) ^ (2 - α) / 2)) := by
          rw [show t ^ 2 * ((1 / (2 * t)) ^ (2 - α) / 2) =
            (t ^ 2 * (1 / (2 * t)) ^ (2 - α)) / 2 by ring, hcore]
          ring
      _ ≤ c * √(d : ℝ) ^ e / 4 * (k j ^ 2 * ∑ n ∈ range N, ((n : ℝ) + 1) ^ (1 - α)) := by
          rw [hkt]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)) hc0
          linarith
      _ = _ := by ring
      _ ≤ _ := hL
  · -- Upper bound.
    set s := √(d : ℝ) * r with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s ≤ 1 := by
      calc s ≤ √(d : ℝ) * (1 / (2 * √(d : ℝ))) := mul_le_mul_of_nonneg_left hrδ hsd0.le
        _ = 1 / 2 := by field_simp
        _ ≤ 1 := by norm_num
    have hU := one_sub_fourierSymbol_le_of_small hd hp0 hp hCpos.le hα hup k hs0 hs1
    have hsum := sum_rpow_le_of_lt_two hα2 ⌊1 / s⌋₊
    have hNs : (⌊1 / s⌋₊ : ℝ) ^ (2 - α) ≤ (1 / s) ^ (2 - α) :=
      rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) h2α.le
    have hX : s ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α) ≤
        (1 + 1 / (2 - α)) * s ^ α := by
      calc s ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α)
          ≤ s ^ 2 * ((1 + 1 / (2 - α)) * (1 / s) ^ (2 - α)) :=
            mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hNs
              (by positivity))) (sq_nonneg s)
        _ = (1 + 1 / (2 - α)) * (s ^ 2 * (1 / s) ^ (2 - α)) := by ring
        _ = (1 + 1 / (2 - α)) * s ^ α := by rw [sq_mul_one_div_rpow hs0]
    have hsα : s ^ α = √(d : ℝ) ^ α * r ^ α := mul_rpow hsd0.le hr0.le
    refine hU.trans ?_
    rw [← hK]
    calc K * (2 * C) * (s ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α) +
          (1 + 1 / α) * s ^ α)
        ≤ K * (2 * C) * ((1 + 1 / (2 - α)) * s ^ α + (1 + 1 / α) * s ^ α) := by
          gcongr
      _ = _ := by rw [hsα]; ring

/-- The lower-bound data shared by the regimes: a coordinate `j` with `t = |k_j|`,
`r ≤ √d t`, `t ≤ r` and `N = ⌊1/t⌋ ≥ 1` with `N t ≤ 1`, `1/(2t) ≤ N` and `1/t < N + 1`. -/
theorem exists_coordinate_floor (hd : 1 ≤ d) (k : Fin d → ℝ) (hr0 : 0 < √(∑ i, k i ^ 2))
    (hr : √(∑ i, k i ^ 2) ≤ 1 / 2) :
    ∃ j, 0 < |k j| ∧ √(∑ i, k i ^ 2) ≤ √(d : ℝ) * |k j| ∧ |k j| ≤ √(∑ i, k i ^ 2) ∧
      1 ≤ ⌊1 / |k j|⌋₊ ∧ (⌊1 / |k j|⌋₊ : ℝ) * |k j| ≤ 1 ∧
      1 / (2 * |k j|) ≤ ⌊1 / |k j|⌋₊ ∧ 1 / |k j| < (⌊1 / |k j|⌋₊ : ℝ) + 1 := by
  obtain ⟨j, -, hrj⟩ := exists_euclid_le_mul_abs hd k
  have ht0 : 0 < |k j| := by
    by_contra h
    have : |k j| = 0 := le_antisymm (not_lt.1 h) (abs_nonneg _)
    rw [this, mul_zero] at hrj
    linarith
  have htr : |k j| ≤ √(∑ i, k i ^ 2) := Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => k i ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  exact ⟨j, ht0, hrj, htr, floor_one_div_bounds ht0 (htr.trans hr)⟩

/-- **Item 2, `α = 2`.** `1 - φ(k) ≍ |k|² log(1/|k|)` near `k = 0`. -/
theorem one_sub_fourierSymbol_asymp_of_eq_two (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : HasSum p 1) {c C : ℝ} (hc : 0 < c)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + 2)) ≤ p x)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + 2))) :
    ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin d → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * (√(∑ i, k i ^ 2) ^ 2 * Real.log (1 / √(∑ i, k i ^ 2))) ≤
        1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤
        b * (√(∑ i, k i ^ 2) ^ 2 * Real.log (1 / √(∑ i, k i ^ 2))) := by
  have hCpos := pos_of_low_up hd hc hlow hup
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : 1 ≤ √(d : ℝ) := by rw [one_le_sqrt]; exact_mod_cast hd
  have hsd0 : 0 < √(d : ℝ) := by linarith
  set K : ℝ := ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by rw [hK]; exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  set e : ℝ := -((d : ℝ) + 2) with he
  refine ⟨min (1 / (2 * √(d : ℝ))) (Real.exp (-1)), by positivity,
    c * √(d : ℝ) ^ e / 4 / d, by positivity, K * (2 * C) * d * (7 / 2), by positivity, ?_⟩
  intro k hr0 hrδ
  set r := √(∑ i, k i ^ 2) with hr
  have hrδ1 : r ≤ 1 / (2 * √(d : ℝ)) := hrδ.trans (min_le_left _ _)
  have hre : r ≤ Real.exp (-1) := hrδ.trans (min_le_right _ _)
  have hrhalf : r ≤ 1 / 2 := hrδ1.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  have hlog1 : 1 ≤ Real.log (1 / r) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hr0]
    calc Real.exp 1 * r ≤ Real.exp 1 * Real.exp (-1) :=
          mul_le_mul_of_nonneg_left hre (Real.exp_pos 1).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
  constructor
  · -- Lower bound.
    obtain ⟨j, ht0, hrj, htr, hN1, hNt, -, hN3⟩ := exists_coordinate_floor hd k hr0 hrhalf
    have hL := le_one_sub_fourierSymbol hp0 hp hc two_pos hlow k j _ hNt
    have hS := (log_le_sum_rpow_neg_one_le ⌊1 / |k j|⌋₊).1
    have hlogt : Real.log (1 / r) ≤ Real.log ((⌊1 / |k j|⌋₊ : ℝ) + 1) := by
      refine Real.log_le_log (by positivity) ?_
      exact (one_div_le_one_div_of_le ht0 htr).trans hN3.le
    have hkt : r ^ 2 / d ≤ k j ^ 2 := by
      rw [div_le_iff₀ hdpos, ← sq_abs (k j)]
      have := pow_le_pow_left₀ hr0.le hrj 2
      rw [mul_pow, sq_sqrt hdpos.le] at this
      linarith
    have hc0 : 0 ≤ c * √(d : ℝ) ^ e / 4 := by positivity
    calc c * √(d : ℝ) ^ e / 4 / d * (r ^ 2 * Real.log (1 / r))
        = c * √(d : ℝ) ^ e / 4 * ((r ^ 2 / d) * Real.log (1 / r)) := by ring
      _ ≤ c * √(d : ℝ) ^ e / 4 * (k j ^ 2 *
            ∑ n ∈ range ⌊1 / |k j|⌋₊, ((n : ℝ) + 1) ^ (1 - (2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hkt (hlogt.trans hS) (by linarith)
            (sq_nonneg _)) hc0
      _ = _ := by ring
      _ ≤ _ := hL
  · -- Upper bound.
    set s := √(d : ℝ) * r with hs
    have hs0 : 0 < s := by positivity
    have hs12 : s ≤ 1 / 2 := by
      calc s ≤ √(d : ℝ) * (1 / (2 * √(d : ℝ))) := mul_le_mul_of_nonneg_left hrδ1 hsd0.le
        _ = 1 / 2 := by field_simp
    have hU := one_sub_fourierSymbol_le_of_small hd hp0 hp hCpos.le two_pos hup k hs0
      (by linarith)
    obtain ⟨hN1, -, -, -⟩ := floor_one_div_bounds hs0 hs12
    have hsum := (log_le_sum_rpow_neg_one_le ⌊1 / s⌋₊).2
    have hlogN : Real.log (⌊1 / s⌋₊ : ℝ) ≤ Real.log (1 / r) := by
      refine Real.log_le_log (by exact_mod_cast hN1) ?_
      refine (Nat.floor_le (by positivity)).trans (one_div_le_one_div_of_le hr0 ?_)
      rw [hs]; nlinarith
    have hs2 : s ^ 2 = d * r ^ 2 := by rw [hs, mul_pow, sq_sqrt hdpos.le]
    refine hU.trans ?_
    rw [← hK, rpow_two, hs2]
    have hS0 : 0 ≤ ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - (2 : ℝ)) :=
      Finset.sum_nonneg fun n _ => rpow_nonneg (by positivity) _
    calc K * (2 * C) * (d * r ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - (2 : ℝ)) +
          (1 + 1 / 2) * (d * r ^ 2))
        ≤ K * (2 * C) * (d * r ^ 2 * (1 + Real.log (1 / r)) + (1 + 1 / 2) * (d * r ^ 2)) := by
          gcongr
          linarith
      _ ≤ K * (2 * C) * (d * r ^ 2 * (7 / 2 * Real.log (1 / r))) := by
          gcongr
          nlinarith [sq_nonneg r]
      _ = _ := by ring

/-- **Item 2, `α > 2`.** `1 - φ(k) ≍ |k|²` near `k = 0`. -/
theorem one_sub_fourierSymbol_asymp_of_two_lt (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : HasSum p 1) {c C α : ℝ} (hc : 0 < c) (hα2 : 2 < α)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)) ≤ p x)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α))) :
    ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin d → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * √(∑ i, k i ^ 2) ^ 2 ≤ 1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ b * √(∑ i, k i ^ 2) ^ 2 := by
  have hα : 0 < α := by linarith
  have hCpos := pos_of_low_up hd hc hlow hup
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : 1 ≤ √(d : ℝ) := by rw [one_le_sqrt]; exact_mod_cast hd
  have hsd0 : 0 < √(d : ℝ) := by linarith
  set K : ℝ := ((2 * d * 3 ^ (d - 1) : ℕ) : ℝ) with hK
  have hK0 : 0 < K := by rw [hK]; exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  set e : ℝ := -((d : ℝ) + α) with he
  have hβ : 0 < α - 2 := by linarith
  refine ⟨1 / (2 * √(d : ℝ)), by positivity, c * √(d : ℝ) ^ e / 4 / d, by positivity,
    K * (2 * C) * ((1 + 1 / (α - 2)) + (1 + 1 / α)) * d, by positivity, ?_⟩
  intro k hr0 hrδ
  set r := √(∑ i, k i ^ 2) with hr
  have hrhalf : r ≤ 1 / 2 := hrδ.trans (by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  constructor
  · -- Lower bound.
    obtain ⟨j, ht0, hrj, htr, hN1, hNt, -, -⟩ := exists_coordinate_floor hd k hr0 hrhalf
    have hL := le_one_sub_fourierSymbol hp0 hp hc hα hlow k j _ hNt
    have hS : 1 ≤ ∑ n ∈ range ⌊1 / |k j|⌋₊, ((n : ℝ) + 1) ^ (1 - α) := by
      have := Finset.single_le_sum (f := fun n : ℕ => ((n : ℝ) + 1) ^ (1 - α))
        (fun n _ => rpow_nonneg (by positivity) _) (Finset.mem_range.2 hN1)
      simpa using this
    have hkt : r ^ 2 / d ≤ k j ^ 2 := by
      rw [div_le_iff₀ hdpos, ← sq_abs (k j)]
      have := pow_le_pow_left₀ hr0.le hrj 2
      rw [mul_pow, sq_sqrt hdpos.le] at this
      linarith
    have hc0 : 0 ≤ c * √(d : ℝ) ^ e / 4 := by positivity
    calc c * √(d : ℝ) ^ e / 4 / d * r ^ 2 = c * √(d : ℝ) ^ e / 4 * (r ^ 2 / d * 1) := by ring
      _ ≤ c * √(d : ℝ) ^ e / 4 * (k j ^ 2 *
            ∑ n ∈ range ⌊1 / |k j|⌋₊, ((n : ℝ) + 1) ^ (1 - α)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hkt hS zero_le_one (sq_nonneg _)) hc0
      _ = _ := by ring
      _ ≤ _ := hL
  · -- Upper bound.
    set s := √(d : ℝ) * r with hs
    have hs0 : 0 < s := by positivity
    have hs1 : s ≤ 1 := by
      calc s ≤ √(d : ℝ) * (1 / (2 * √(d : ℝ))) := mul_le_mul_of_nonneg_left hrδ hsd0.le
        _ = 1 / 2 := by field_simp
        _ ≤ 1 := by norm_num
    have hU := one_sub_fourierSymbol_le_of_small hd hp0 hp hCpos.le hα hup k hs0 hs1
    have hsum := sum_rpow_le_of_two_lt hα2 ⌊1 / s⌋₊
    have hsα : s ^ α ≤ s ^ 2 := by
      rw [← rpow_two]
      exact rpow_le_rpow_of_exponent_ge hs0 hs1 hα2.le
    have hs2 : s ^ 2 = d * r ^ 2 := by rw [hs, mul_pow, sq_sqrt hdpos.le]
    refine hU.trans ?_
    rw [← hK]
    calc K * (2 * C) * (s ^ 2 * ∑ n ∈ range ⌊1 / s⌋₊, ((n : ℝ) + 1) ^ (1 - α) +
          (1 + 1 / α) * s ^ α)
        ≤ K * (2 * C) * (s ^ 2 * (1 + 1 / (α - 2)) + (1 + 1 / α) * s ^ 2) := by
          gcongr
      _ = _ := by rw [hs2]; ring

/-! ### Non-vacuity witnesses -/

/-- Non-vacuity witness: on `ℤ`, `p(0) = 1/2` and `p(x) = c₀ |x|^{-2}` with
`c₀ = 3/(2π²)`, so that the masses sum to one (`∑_{x ≠ 0} x^{-2} = π²/3`). -/
theorem hasSum_lazy_inverse_square :
    HasSum (fun x : Fin 1 → ℤ => if x = 0 then (1 / 2 : ℝ) else
      3 / (2 * π ^ 2) * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-(((1 : ℕ) : ℝ) + 1))) 1 := by
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff]
  have hpt : ∀ n : ℤ, (fun x : Fin 1 → ℤ => if x = 0 then (1 / 2 : ℝ) else
      3 / (2 * π ^ 2) * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-(((1 : ℕ) : ℝ) + 1)))
        ((Equiv.funUnique (Fin 1) ℤ).symm n) =
      (if n = 0 then 1 / 2 else 0) + 3 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) := by
    intro n
    have he : ((Equiv.funUnique (Fin 1) ℤ).symm n) = fun _ => n := rfl
    simp only [he]
    by_cases hn : n = 0
    · subst hn
      have h0 : (fun _ => (0 : ℤ) : Fin 1 → ℤ) = 0 := rfl
      simp [h0]
    · have hx : (fun _ => n : Fin 1 → ℤ) ≠ 0 := fun h => hn (congr_fun h 0)
      rw [ite_eq_right hx, ite_eq_right hn, zero_add, Fin.sum_univ_one, sqrt_sq_eq_abs,
        show -(((1 : ℕ) : ℝ) + 1) = -2 by norm_num, rpow_neg (abs_nonneg _), rpow_two,
        sq_abs, one_div]
  simp_rw [Function.comp_def, hpt]
  have hneg : HasSum (fun n : ℕ => 1 / (((-((n : ℤ) + 1) : ℤ)) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, sub_zero] at this
    convert this using 2 with n
    push_cast
    ring
  have hz : HasSum (fun n : ℤ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6 + π ^ 2 / 6) :=
    HasSum.of_nat_of_neg_add_one (by simpa using hasSum_zeta_two) hneg
  have := (hasSum_ite_eq (0 : ℤ) (1 / 2 : ℝ)).add (hz.mul_left (3 / (2 * π ^ 2)))
  convert this using 1
  have hπ : π ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Item 1 for the witness: `0 ≤ φ ≤ 1`, and `φ(k) = 1` on `[-π, π]` only at `k = 0`. -/
example (p : (Fin 1 → ℤ) → ℝ) (hpdef : p = fun x => if x = 0 then (1 / 2 : ℝ) else
      3 / (2 * π ^ 2) * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-(((1 : ℕ) : ℝ) + 1))) (k : Fin 1 → ℝ) :
    0 ≤ ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧ ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ 1 ∧
      ((∀ i, |k i| ≤ π) → ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) = 1 → k = 0) := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => by
    rw [hpdef]; dsimp only; split_ifs
    · norm_num
    · positivity
  have hp : HasSum p 1 := hpdef ▸ hasSum_lazy_inverse_square
  have hlow : ∀ x, x ≠ 0 → 3 / (2 * π ^ 2) * √(∑ i, ((x i : ℝ)) ^ 2) ^
      (-(((1 : ℕ) : ℝ) + 1)) ≤ p x := fun x hx => by rw [hpdef]; simp [hx]
  exact ⟨fourierSymbol_nonneg hp0 hp (by rw [hpdef]; simp) k, fourierSymbol_le_one hp0 hp k,
    fun hk h1 => eq_zero_of_fourierSymbol_eq_one hp0 hp (by positivity) hlow hk h1⟩

/-- Item 2 for the witness (`d = 1`, `α = 1`): `1 - φ(k) ≍ |k|` near `0`. -/
example (p : (Fin 1 → ℤ) → ℝ) (hpdef : p = fun x => if x = 0 then (1 / 2 : ℝ) else
      3 / (2 * π ^ 2) * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-(((1 : ℕ) : ℝ) + 1))) :
    ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin 1 → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * √(∑ i, k i ^ 2) ^ (1 : ℝ) ≤ 1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ b * √(∑ i, k i ^ 2) ^ (1 : ℝ) := by
  have hp0 : ∀ x, 0 ≤ p x := fun x => by
    rw [hpdef]; dsimp only; split_ifs
    · norm_num
    · positivity
  have hp : HasSum p 1 := hpdef ▸ hasSum_lazy_inverse_square
  have hbd : ∀ x, x ≠ 0 → p x = 3 / (2 * π ^ 2) * √(∑ i, ((x i : ℝ)) ^ 2) ^
      (-(((1 : ℕ) : ℝ) + 1)) := fun x hx => by rw [hpdef]; simp [hx]
  exact one_sub_fourierSymbol_asymp_of_lt_two le_rfl hp0 hp (by positivity) one_pos
    (by norm_num) (fun x hx => (hbd x hx).ge) (fun x hx => (hbd x hx).le)

end PercLib.Models.LongRange
