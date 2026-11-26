/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Power-law convolution bounds for a weight with polynomial ball growth. New for this project
against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied.
Mathematical reference: the standard convolution estimate for power-law kernels on `ℤ^d`,
e.g. Hara, *Decay of correlations in nearest-neighbour self-avoiding walk, percolation, lattice
trees and animals*, Ann. Probab. 36 (2008), Proposition 1.7.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Power-law convolution bounds

Let `G` be an additive group with a weight `w ≥ 1` that is subadditive and symmetric, and
whose balls have polynomial growth of degree `D`: `#{w ≤ t} ≤ K t^D` for `t > 0`. Writing
`(f ⋆ g)(x) = ∑ y, f y g (x - y)`, the convolution of `w^(-a)` and `w^(-b)` (for `a, b > 0`)
is bounded by `C w(x)^(-min a b)` when `max a b > D`, and by `C w(x)^(-(a + b - D))` when
`a, b < D < a + b`. Sums are in `ℝ≥0∞`. The proof splits at `w y = w x / 2` and
`w (x - y) = w x / 2` and sums dyadic shells.

## Main results

* `tsum_ite_le_rpow_le_of_count`: `∑_{w y ≤ R} w(y)^(-u) ≤ C R^(D-u)` for `0 ≤ u < D`.
* `tsum_ite_ge_rpow_le_of_count`: `∑_{w y ≥ T} w(y)^(-s) ≤ C T^(D-s)` for `s > D`.
* `tsum_rpow_mul_rpow_sub_le_three`: the three-region split of the convolution.
* `exists_tsum_rpow_mul_rpow_sub_le_of_lt_add`: the bound `w(x)^(-(a+b-D))` for
  `a, b < D < a + b`.
* `exists_tsum_rpow_mul_rpow_sub_le_of_lt_max`: the bound `w(x)^(-min a b)` for `max a b > D`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PercLib.Analysis

/-! ### Elementary estimates -/

/-- A geometric series of `ofReal` terms. -/
theorem tsum_ofReal_mul_pow {c ρ : ℝ} (hc : 0 ≤ c) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∑' k : ℕ, ENNReal.ofReal (c * ρ ^ k) = ENNReal.ofReal (c / (1 - ρ)) := by
  have hs : Summable fun k : ℕ => c * ρ ^ k :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left c
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc (pow_nonneg hρ0 k)) hs,
    tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1, div_eq_mul_inv]

/-- For `r ≥ 1/2`, a smaller power of `r` is at most `2^(q-p)` times a larger one. -/
theorem rpow_le_two_rpow_mul_rpow {r p q : ℝ} (hr : 1 / 2 ≤ r) (hpq : p ≤ q) :
    r ^ p ≤ 2 ^ (q - p) * r ^ q := by
  have hr0 : 0 < r := by linarith
  have h1 : r ^ (p - q) ≤ (1 / 2) ^ (p - q) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hr (by linarith)
  rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_sub] at h1
  calc r ^ p = r ^ (p - q) * r ^ q := by rw [← Real.rpow_add hr0, sub_add_cancel]
    _ ≤ 2 ^ (q - p) * r ^ q := by gcongr

/-- `((2^n)^p) = (2^p)^n`. -/
theorem two_pow_rpow (n : ℕ) (p : ℝ) : ((2 : ℝ) ^ n) ^ p = ((2 : ℝ) ^ p) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

/-- `(w/2)^(-e) = 2^e w^(-e)`. -/
theorem div_two_rpow_neg {w : ℝ} (hw : 0 ≤ w) (e : ℝ) :
    (w / 2) ^ (-e) = 2 ^ e * w ^ (-e) := by
  rw [Real.div_rpow hw (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
    mul_comm]

theorem ite_ofReal_mul {p : Prop} [Decidable p] {c v : ℝ} (hc : 0 ≤ c) :
    (if p then ENNReal.ofReal (c * v) else 0) = ENNReal.ofReal c * if p then ENNReal.ofReal v
      else 0 := by
  split_ifs <;> simp [ENNReal.ofReal_mul hc]

/-! ### Ball and tail sums from polynomial growth -/

section Growth

variable {G : Type*} {w : G → ℝ} {D K : ℝ}

/-- **Ball sums.** If `w ≥ 1` and `#{w ≤ t} ≤ K t^D` for `t > 0`, then for `0 ≤ u < D`,
`∑_{w y ≤ R} w(y)^(-u) ≤ K 2^u / (1 - 2^(u-D)) R^(D-u)`. -/
theorem tsum_ite_le_rpow_le_of_count (hw1 : ∀ y, 1 ≤ w y)
    (hcount : ∀ t > 0, ∑' y, (if w y ≤ t then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K * t ^ D))
    (hK : 0 ≤ K) {u : ℝ} (hu0 : 0 ≤ u) (huD : u < D) {R : ℝ} (hR : 0 < R) :
    ∑' y, (if w y ≤ R then ENNReal.ofReal (w y ^ (-u)) else 0) ≤
      ENNReal.ofReal (K * 2 ^ u / (1 - 2 ^ (u - D)) * R ^ (D - u)) := by
  classical
  have hpt : ∀ y, (if w y ≤ R then ENNReal.ofReal (w y ^ (-u)) else 0) ≤
      ∑' k : ℕ, (if w y ≤ R / 2 ^ k then ENNReal.ofReal ((R / 2 ^ (k + 1)) ^ (-u)) else 0) := by
    intro y
    split_ifs with hy
    · have hex : ∃ k : ℕ, R / 2 ^ (k + 1) < w y := by
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
        refine ⟨k, ?_⟩
        rw [div_lt_iff₀ (by positivity)]
        calc R < 2 ^ k := hk
          _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)
          _ ≤ w y * 2 ^ (k + 1) := le_mul_of_one_le_left (by positivity) (hw1 y)
      obtain ⟨k, hk, hmin⟩ : ∃ k, R / 2 ^ (k + 1) < w y ∧ ∀ m < k, ¬ R / 2 ^ (m + 1) < w y :=
        ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
      have hk' : w y ≤ R / 2 ^ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · rw [h0, pow_zero, div_one]
          exact hy
        · have := hmin (k - 1) (Nat.sub_lt hpos one_pos)
          rw [show k - 1 + 1 = k by omega] at this
          exact not_lt.1 this
      refine le_trans ?_ (ENNReal.le_tsum k)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk')]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos (by positivity) hk.le (by linarith))
    · exact zero_le
  have hρ : (2 : ℝ) ^ (u - D) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  calc ∑' y, (if w y ≤ R then ENNReal.ofReal (w y ^ (-u)) else 0)
      ≤ ∑' y, ∑' k : ℕ,
          (if w y ≤ R / 2 ^ k then ENNReal.ofReal ((R / 2 ^ (k + 1)) ^ (-u)) else 0) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' k : ℕ, ∑' y,
          (if w y ≤ R / 2 ^ k then ENNReal.ofReal ((R / 2 ^ (k + 1)) ^ (-u)) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' k : ℕ, ENNReal.ofReal ((R / 2 ^ (k + 1)) ^ (-u)) *
          ∑' y, (if w y ≤ R / 2 ^ k then (1 : ℝ≥0∞) else 0) := by
        congr 1
        funext k
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext y
        split_ifs <;> simp
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((R / 2 ^ (k + 1)) ^ (-u)) *
          ENNReal.ofReal (K * (R / 2 ^ k) ^ D) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hcount _ (by positivity)) _
    _ = ∑' k : ℕ, ENNReal.ofReal (K * 2 ^ u * R ^ (D - u) * (2 ^ (u - D)) ^ k) := by
        congr 1
        funext k
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have hX : (0 : ℝ) < 2 ^ u := by positivity
        have hY : (0 : ℝ) < 2 ^ D := by positivity
        rw [Real.div_rpow hR.le (by positivity), Real.div_rpow hR.le (by positivity),
          two_pow_rpow, two_pow_rpow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_sub (by norm_num : (0 : ℝ) < 2), sub_eq_add_neg D u,
          Real.rpow_add hR, inv_pow, div_inv_eq_mul, pow_succ, div_pow]
        field_simp
    _ = ENNReal.ofReal (K * 2 ^ u * R ^ (D - u) / (1 - 2 ^ (u - D))) :=
        tsum_ofReal_mul_pow (by positivity) (by positivity) hρ
    _ = ENNReal.ofReal (K * 2 ^ u / (1 - 2 ^ (u - D)) * R ^ (D - u)) := by
        congr 1
        ring

/-- **Tail sums.** If `#{w ≤ t} ≤ K t^D` for `t > 0`, then for `s > D`,
`∑_{w y ≥ T} w(y)^(-s) ≤ K 2^D / (1 - 2^(D-s)) T^(D-s)`. -/
theorem tsum_ite_ge_rpow_le_of_count
    (hcount : ∀ t > 0, ∑' y, (if w y ≤ t then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K * t ^ D))
    (hK : 0 ≤ K) {s : ℝ} (hs0 : 0 ≤ s) (hsD : D < s) {T : ℝ} (hT : 0 < T) :
    ∑' y, (if T ≤ w y then ENNReal.ofReal (w y ^ (-s)) else 0) ≤
      ENNReal.ofReal (K * 2 ^ D / (1 - 2 ^ (D - s)) * T ^ (D - s)) := by
  classical
  have hpt : ∀ y, (if T ≤ w y then ENNReal.ofReal (w y ^ (-s)) else 0) ≤
      ∑' k : ℕ, (if w y ≤ T * 2 ^ (k + 1) then ENNReal.ofReal ((T * 2 ^ k) ^ (-s)) else 0) := by
    intro y
    split_ifs with hy
    · have hex : ∃ k : ℕ, w y < T * 2 ^ (k + 1) := by
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (w y / T) (by norm_num : (1 : ℝ) < 2)
        refine ⟨k, ?_⟩
        rw [div_lt_iff₀ hT] at hk
        calc w y < 2 ^ k * T := hk
          _ ≤ 2 ^ (k + 1) * T :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ k)) hT.le
          _ = T * 2 ^ (k + 1) := mul_comm _ _
      obtain ⟨k, hk, hmin⟩ : ∃ k, w y < T * 2 ^ (k + 1) ∧ ∀ m < k, ¬ w y < T * 2 ^ (m + 1) :=
        ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
      have hk' : T * 2 ^ k ≤ w y := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · rw [h0, pow_zero, mul_one]
          exact hy
        · have := hmin (k - 1) (Nat.sub_lt hpos one_pos)
          rw [show k - 1 + 1 = k by omega] at this
          exact not_lt.1 this
      refine le_trans ?_ (ENNReal.le_tsum k)
      rw [ite_eq_left_of_eq_true _ _ (eq_true hk.le)]
      exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos (by positivity) hk' (by linarith))
    · exact zero_le
  have hρ : (2 : ℝ) ^ (D - s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  calc ∑' y, (if T ≤ w y then ENNReal.ofReal (w y ^ (-s)) else 0)
      ≤ ∑' y, ∑' k : ℕ,
          (if w y ≤ T * 2 ^ (k + 1) then ENNReal.ofReal ((T * 2 ^ k) ^ (-s)) else 0) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' k : ℕ, ∑' y,
          (if w y ≤ T * 2 ^ (k + 1) then ENNReal.ofReal ((T * 2 ^ k) ^ (-s)) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' k : ℕ, ENNReal.ofReal ((T * 2 ^ k) ^ (-s)) *
          ∑' y, (if w y ≤ T * 2 ^ (k + 1) then (1 : ℝ≥0∞) else 0) := by
        congr 1
        funext k
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext y
        split_ifs <;> simp
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((T * 2 ^ k) ^ (-s)) *
          ENNReal.ofReal (K * (T * 2 ^ (k + 1)) ^ D) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hcount _ (by positivity)) _
    _ = ∑' k : ℕ, ENNReal.ofReal (K * 2 ^ D * T ^ (D - s) * (2 ^ (D - s)) ^ k) := by
        congr 1
        funext k
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow hT.le (by positivity), Real.mul_rpow hT.le (by positivity),
          two_pow_rpow, two_pow_rpow, sub_eq_add_neg D s,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_add hT, mul_pow, pow_succ]
        ring
    _ = ENNReal.ofReal (K * 2 ^ D * T ^ (D - s) / (1 - 2 ^ (D - s))) :=
        tsum_ofReal_mul_pow (by positivity) (by positivity) hρ
    _ = ENNReal.ofReal (K * 2 ^ D / (1 - 2 ^ (D - s)) * T ^ (D - s)) := by
        congr 1
        ring

/-- **Total sums.** If `w ≥ 1` and `#{w ≤ t} ≤ K t^D`, then `∑ w(y)^(-s) < ∞` for `s > D`,
with the explicit bound `K 2^D / (1 - 2^(D-s))`. -/
theorem tsum_rpow_le_of_count (hw1 : ∀ y, 1 ≤ w y)
    (hcount : ∀ t > 0, ∑' y, (if w y ≤ t then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K * t ^ D))
    (hK : 0 ≤ K) {s : ℝ} (hs0 : 0 ≤ s) (hsD : D < s) :
    ∑' y, ENNReal.ofReal (w y ^ (-s)) ≤ ENNReal.ofReal (K * 2 ^ D / (1 - 2 ^ (D - s))) := by
  have h := tsum_ite_ge_rpow_le_of_count hcount hK hs0 hsD one_pos
  simp only [hw1, ↓reduceIte, Real.one_rpow, mul_one] at h
  exact h

end Growth

/-! ### The three-region split -/

section Convolution

variable {G : Type*} [AddCommGroup G] {w : G → ℝ} {D K : ℝ}

/-- **Three-region split.** For a weight `w ≥ 1` that is subadditive and symmetric, with
`r = w x / 2`, the convolution `∑ w(y)^(-a) w(x-y)^(-b)` is at most
`r^(-b) ∑_{w y ≤ r} w(y)^(-a) + r^(-a) ∑_{w z ≤ r} w(z)^(-b) + 3^b ∑_{w y ≥ r} w(y)^(-(a+b))`. -/
theorem tsum_rpow_mul_rpow_sub_le_three (hw1 : ∀ y, 1 ≤ w y)
    (htri : ∀ y z, w (y + z) ≤ w y + w z) (hneg : ∀ y, w (-y) = w y) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (x : G) :
    ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) ≤
      ENNReal.ofReal ((w x / 2) ^ (-b)) *
          ∑' y, (if w y ≤ w x / 2 then ENNReal.ofReal (w y ^ (-a)) else 0) +
        ENNReal.ofReal ((w x / 2) ^ (-a)) *
          ∑' y, (if w y ≤ w x / 2 then ENNReal.ofReal (w y ^ (-b)) else 0) +
        ENNReal.ofReal (3 ^ b) *
          ∑' y, (if w x / 2 ≤ w y then ENNReal.ofReal (w y ^ (-(a + b))) else 0) := by
  classical
  set r := w x / 2 with hr_def
  have hr : 0 < r := by have := hw1 x; rw [hr_def]; linarith
  have hw0 : ∀ y, 0 < w y := fun y => one_pos.trans_le (hw1 y)
  have hpt : ∀ y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) ≤
      (if w y ≤ r then ENNReal.ofReal (r ^ (-b) * w y ^ (-a)) else 0) +
        (if w (x - y) ≤ r then ENNReal.ofReal (r ^ (-a) * w (x - y) ^ (-b)) else 0) +
        (if r ≤ w y then ENNReal.ofReal (3 ^ b * w y ^ (-(a + b))) else 0) := by
    intro y
    have hsum : w x ≤ w y + w (x - y) := by simpa using htri y (x - y)
    have hsum' : w y ≤ w x + w (x - y) := by
      have := htri x (y - x)
      rw [add_sub_cancel, ← neg_sub, hneg] at this
      exact this
    by_cases h1 : w y ≤ r
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      refine le_trans ?_ (le_add_right (le_add_right le_rfl))
      refine ENNReal.ofReal_le_ofReal ?_
      have : r ^ (-b) ≥ w (x - y) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (hw0 y).le _)
    · by_cases h2 : w (x - y) ≤ r
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
        refine le_trans ?_ (le_add_right (le_add_left le_rfl))
        refine ENNReal.ofReal_le_ofReal ?_
        have : r ^ (-a) ≥ w y ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
        exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (hw0 _).le _)
      · push Not at h1 h2
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1.le)]
        refine le_trans ?_ (le_add_left le_rfl)
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : w y / 3 ≤ w (x - y) := by rw [hr_def] at h1 h2; linarith
        have h4 : w (x - y) ^ (-b) ≤ (w y / 3) ^ (-b) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [hw0 y]) h3 (by linarith)
        rw [Real.div_rpow (hw0 y).le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
          div_inv_eq_mul] at h4
        rw [neg_add, Real.rpow_add (hw0 y)]
        calc w y ^ (-a) * w (x - y) ^ (-b) ≤ w y ^ (-a) * (w y ^ (-b) * 3 ^ b) :=
              mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg (hw0 y).le _)
          _ = 3 ^ b * (w y ^ (-a) * w y ^ (-b)) := by ring
  have hB : ∑' y, (if w (x - y) ≤ r then ENNReal.ofReal (r ^ (-a) * w (x - y) ^ (-b)) else 0) =
      ∑' z, (if w z ≤ r then ENNReal.ofReal (r ^ (-a) * w z ^ (-b)) else 0) :=
    (Equiv.subLeft x).tsum_eq fun z => if w z ≤ r then ENNReal.ofReal (r ^ (-a) * w z ^ (-b))
      else 0
  calc ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b))
      ≤ ∑' y, ((if w y ≤ r then ENNReal.ofReal (r ^ (-b) * w y ^ (-a)) else 0) +
        (if w (x - y) ≤ r then ENNReal.ofReal (r ^ (-a) * w (x - y) ^ (-b)) else 0) +
        (if r ≤ w y then ENNReal.ofReal (3 ^ b * w y ^ (-(a + b))) else 0)) :=
        ENNReal.tsum_le_tsum hpt
    _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, hB]
        simp_rw [ite_ofReal_mul (Real.rpow_nonneg hr.le _),
          ite_ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) b), ENNReal.tsum_mul_left]

/-- **Convolution bound, `a, b < D < a + b`.** -/
theorem exists_tsum_rpow_mul_rpow_sub_le_of_lt_add (hw1 : ∀ y, 1 ≤ w y)
    (htri : ∀ y z, w (y + z) ≤ w y + w z) (hneg : ∀ y, w (-y) = w y)
    (hcount : ∀ t > 0, ∑' y, (if w y ≤ t then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K * t ^ D))
    (hK : 0 ≤ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (haD : a < D) (hbD : b < D)
    (hD : D < a + b) :
    ∃ C, 0 ≤ C ∧ ∀ x, ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) ≤
      ENNReal.ofReal (C * w x ^ (-(a + b - D))) := by
  have hρa : (2 : ℝ) ^ (a - D) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρb : (2 : ℝ) ^ (b - D) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρc : (2 : ℝ) ^ (D - (a + b)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set Ha := K * 2 ^ a / (1 - 2 ^ (a - D))
  set Hb := K * 2 ^ b / (1 - 2 ^ (b - D))
  set Tc := K * 2 ^ D / (1 - 2 ^ (D - (a + b)))
  have hHa : 0 ≤ Ha := div_nonneg (by positivity) (by linarith)
  have hHb : 0 ≤ Hb := div_nonneg (by positivity) (by linarith)
  have hTc : 0 ≤ Tc := div_nonneg (by positivity) (by linarith)
  refine ⟨(Ha + Hb + 3 ^ b * Tc) * 2 ^ (a + b - D), by positivity, fun x => ?_⟩
  set r := w x / 2 with hr_def
  have hr : 0 < r := by have := hw1 x; rw [hr_def]; linarith
  refine (tsum_rpow_mul_rpow_sub_le_three hw1 htri hneg ha.le hb.le x).trans ?_
  rw [← hr_def]
  calc _ ≤ ENNReal.ofReal (r ^ (-b)) * ENNReal.ofReal (Ha * r ^ (D - a)) +
        ENNReal.ofReal (r ^ (-a)) * ENNReal.ofReal (Hb * r ^ (D - b)) +
        ENNReal.ofReal (3 ^ b) * ENNReal.ofReal (Tc * r ^ (D - (a + b))) :=
        add_le_add (add_le_add
          (mul_le_mul_right (tsum_ite_le_rpow_le_of_count hw1 hcount hK ha.le haD hr) _)
          (mul_le_mul_right (tsum_ite_le_rpow_le_of_count hw1 hcount hK hb.le hbD hr) _))
          (mul_le_mul_right
            (tsum_ite_ge_rpow_le_of_count hcount hK (by linarith) (by linarith) hr) _)
    _ = ENNReal.ofReal ((Ha + Hb + 3 ^ b * Tc) * r ^ (-(a + b - D))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have e1 : r ^ (-b) * r ^ (D - a) = r ^ (-(a + b - D)) := by
          rw [← Real.rpow_add hr]; congr 1; ring
        have e2 : r ^ (-a) * r ^ (D - b) = r ^ (-(a + b - D)) := by
          rw [← Real.rpow_add hr]; congr 1; ring
        have e3 : r ^ (D - (a + b)) = r ^ (-(a + b - D)) := by congr 1; ring
        calc r ^ (-b) * (Ha * r ^ (D - a)) + r ^ (-a) * (Hb * r ^ (D - b)) +
              3 ^ b * (Tc * r ^ (D - (a + b)))
            = Ha * (r ^ (-b) * r ^ (D - a)) + Hb * (r ^ (-a) * r ^ (D - b)) +
              3 ^ b * Tc * r ^ (D - (a + b)) := by ring
          _ = _ := by rw [e1, e2, e3]; ring
    _ = ENNReal.ofReal ((Ha + Hb + 3 ^ b * Tc) * 2 ^ (a + b - D) * w x ^ (-(a + b - D))) := by
        rw [hr_def, div_two_rpow_neg (by linarith [hw1 x])]
        congr 1
        ring

/-- **Convolution bound, `b > D`.** -/
theorem exists_tsum_rpow_mul_rpow_sub_le_of_lt_right (hw1 : ∀ y, 1 ≤ w y)
    (htri : ∀ y z, w (y + z) ≤ w y + w z) (hneg : ∀ y, w (-y) = w y)
    (hcount : ∀ t > 0, ∑' y, (if w y ≤ t then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K * t ^ D))
    (hK : 0 ≤ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hbD : D < b) :
    ∃ C, 0 ≤ C ∧ ∀ x, ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) ≤
      ENNReal.ofReal (C * w x ^ (-min a b)) := by
  classical
  set m := min a b with hm_def
  have hma : m ≤ a := min_le_left a b
  have hmb : m ≤ b := min_le_right a b
  have hm0 : 0 ≤ m := le_min ha.le hb.le
  -- the total sums `S_s = ∑ w^(-s)` for `s > D`
  have hρb : (2 : ℝ) ^ (D - b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρc : (2 : ℝ) ^ (D - (a + b)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set Sb := K * 2 ^ D / (1 - 2 ^ (D - b))
  set Tc := K * 2 ^ D / (1 - 2 ^ (D - (a + b)))
  have hSb : 0 ≤ Sb := div_nonneg (by positivity) (by linarith)
  have hTc : 0 ≤ Tc := div_nonneg (by positivity) (by linarith)
  -- the first region, in both orders of `a` and `b`
  obtain ⟨Ca, hCa, hA⟩ : ∃ Ca, 0 ≤ Ca ∧ ∀ r, 1 / 2 ≤ r →
      ENNReal.ofReal (r ^ (-b)) *
          ∑' y, (if w y ≤ r then ENNReal.ofReal (w y ^ (-a)) else 0) ≤
        ENNReal.ofReal (Ca * r ^ (-m)) := by
    rcases le_or_gt a b with hab | hab
    · refine ⟨Sb, hSb, fun r hr => ?_⟩
      have hr0 : 0 < r := by linarith
      have hpt : ∀ y, (if w y ≤ r then ENNReal.ofReal (w y ^ (-a)) else 0) ≤
          ENNReal.ofReal (r ^ (b - a)) * ENNReal.ofReal (w y ^ (-b)) := by
        intro y
        have hy0 : 0 < w y := one_pos.trans_le (hw1 y)
        split_ifs with hy
        · rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc w y ^ (-a) = w y ^ (b - a) * w y ^ (-b) := by
                rw [← Real.rpow_add hy0]; congr 1; ring
            _ ≤ r ^ (b - a) * w y ^ (-b) := by gcongr
        · exact zero_le
      calc ENNReal.ofReal (r ^ (-b)) *
            ∑' y, (if w y ≤ r then ENNReal.ofReal (w y ^ (-a)) else 0)
          ≤ ENNReal.ofReal (r ^ (-b)) *
            (ENNReal.ofReal (r ^ (b - a)) * ENNReal.ofReal Sb) := by
            gcongr
            refine (ENNReal.tsum_le_tsum hpt).trans ?_
            rw [ENNReal.tsum_mul_left]
            exact mul_le_mul_right (tsum_rpow_le_of_count hw1 hcount hK hb.le hbD) _
        _ = ENNReal.ofReal (Sb * r ^ (-m)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show m = a from min_eq_left hab]
            calc r ^ (-b) * (r ^ (b - a) * Sb) = Sb * (r ^ (-b) * r ^ (b - a)) := by ring
              _ = Sb * r ^ (-a) := by rw [← Real.rpow_add hr0]; congr 2; ring
    · have hρa : (2 : ℝ) ^ (D - a) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      refine ⟨K * 2 ^ D / (1 - 2 ^ (D - a)), div_nonneg (by positivity) (by linarith),
        fun r hr => ?_⟩
      calc ENNReal.ofReal (r ^ (-b)) *
            ∑' y, (if w y ≤ r then ENNReal.ofReal (w y ^ (-a)) else 0)
          ≤ ENNReal.ofReal (r ^ (-b)) * ENNReal.ofReal (K * 2 ^ D / (1 - 2 ^ (D - a))) := by
            gcongr
            refine (ENNReal.tsum_le_tsum fun y => ?_).trans
              (tsum_rpow_le_of_count hw1 hcount hK ha.le (by linarith : D < a))
            split_ifs
            · exact le_rfl
            · exact zero_le
        _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity), show m = b from min_eq_right hab.le]
            congr 1
            ring
  refine ⟨(Ca + 2 ^ (a - m) * Sb + 3 ^ b * Tc * 2 ^ (-m - (D - (a + b)))) * 2 ^ m,
    by positivity, fun x => ?_⟩
  set r := w x / 2 with hr_def
  have hr : 1 / 2 ≤ r := by have := hw1 x; rw [hr_def]; linarith
  have hr0 : 0 < r := by linarith
  refine (tsum_rpow_mul_rpow_sub_le_three hw1 htri hneg ha.le hb.le x).trans ?_
  rw [← hr_def]
  have hB : ENNReal.ofReal (r ^ (-a)) *
        ∑' y, (if w y ≤ r then ENNReal.ofReal (w y ^ (-b)) else 0) ≤
      ENNReal.ofReal (2 ^ (a - m) * Sb * r ^ (-m)) := by
    calc _ ≤ ENNReal.ofReal (r ^ (-a)) * ENNReal.ofReal Sb := by
          gcongr
          refine (ENNReal.tsum_le_tsum fun y => ?_).trans
            (tsum_rpow_le_of_count hw1 hcount hK hb.le hbD)
          split_ifs
          · exact le_rfl
          · exact zero_le
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := rpow_le_two_rpow_mul_rpow hr (show -a ≤ -m by linarith)
          rw [show -m - -a = a - m by ring] at this
          calc r ^ (-a) * Sb ≤ 2 ^ (a - m) * r ^ (-m) * Sb := by gcongr
            _ = _ := by ring
  have hC : ENNReal.ofReal (3 ^ b) *
        ∑' y, (if r ≤ w y then ENNReal.ofReal (w y ^ (-(a + b))) else 0) ≤
      ENNReal.ofReal (3 ^ b * Tc * 2 ^ (-m - (D - (a + b))) * r ^ (-m)) := by
    calc _ ≤ ENNReal.ofReal (3 ^ b) * ENNReal.ofReal (Tc * r ^ (D - (a + b))) :=
          mul_le_mul_right
            (tsum_ite_ge_rpow_le_of_count hcount hK (by linarith) (by linarith) hr0) _
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := rpow_le_two_rpow_mul_rpow hr (show D - (a + b) ≤ -m by linarith)
          calc 3 ^ b * (Tc * r ^ (D - (a + b)))
              ≤ 3 ^ b * (Tc * (2 ^ (-m - (D - (a + b))) * r ^ (-m))) := by gcongr
            _ = _ := by ring
  calc _ ≤ ENNReal.ofReal (Ca * r ^ (-m)) + ENNReal.ofReal (2 ^ (a - m) * Sb * r ^ (-m)) +
        ENNReal.ofReal (3 ^ b * Tc * 2 ^ (-m - (D - (a + b))) * r ^ (-m)) :=
        add_le_add (add_le_add (hA r hr) hB) hC
    _ = ENNReal.ofReal ((Ca + 2 ^ (a - m) * Sb + 3 ^ b * Tc * 2 ^ (-m - (D - (a + b)))) *
          r ^ (-m)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ = _ := by
        rw [hr_def, div_two_rpow_neg (by linarith [hw1 x])]
        congr 1
        ring

/-- **Convolution bound, `max a b > D`.** -/
theorem exists_tsum_rpow_mul_rpow_sub_le_of_lt_max (hw1 : ∀ y, 1 ≤ w y)
    (htri : ∀ y z, w (y + z) ≤ w y + w z) (hneg : ∀ y, w (-y) = w y)
    (hcount : ∀ t > 0, ∑' y, (if w y ≤ t then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (K * t ^ D))
    (hK : 0 ≤ K) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : D < max a b) :
    ∃ C, 0 ≤ C ∧ ∀ x, ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) ≤
      ENNReal.ofReal (C * w x ^ (-min a b)) := by
  rcases lt_max_iff.1 hD with haD | hbD
  · obtain ⟨C, hC, h⟩ :=
      exists_tsum_rpow_mul_rpow_sub_le_of_lt_right hw1 htri hneg hcount hK hb ha haD
    refine ⟨C, hC, fun x => ?_⟩
    have hswap : ∑' y, ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)) =
        ∑' y, ENNReal.ofReal (w y ^ (-b) * w (x - y) ^ (-a)) := by
      refine ((Equiv.subLeft x).tsum_eq
        (fun y => ENNReal.ofReal (w y ^ (-a) * w (x - y) ^ (-b)))).symm.trans ?_
      congr 1
      funext z
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      rw [mul_comm]
    rw [hswap, min_comm]
    exact h x
  · exact exists_tsum_rpow_mul_rpow_sub_le_of_lt_right hw1 htri hneg hcount hK ha hb hbD

end Convolution

end PercLib.Analysis
