/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, on the bond-interface conventions for row sums, from the sup-norm ball counts of
`PowerLaw.lean`. The statements follow the wiki tag C4E9 (size-biased laws). No source text or code
is copied.
-/
module

public import PercLib.Models.LongRange.PowerLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The added layer of a soft power-law cutoff has a small probability row

On `ℤ^d` write `‖z‖₂ = √(∑ᵢ zᵢ²)` (the norm of `z` in `EuclideanSpace ℝ (Fin d)`,
`euclid_eq_norm`). Let `j : ℝ → ℝ` be nonnegative and nonincreasing on `[1, ∞)` with
`j t ≤ A t^{-d-α}` there. For `u ≠ v` put `J(u,v) = j ‖v-u‖₂` and, for `r ≥ 1`,
`J_r(u,v) = 1{‖v-u‖₂ ≤ r} (j ‖v-u‖₂ - j r)` (explicit expressions; no new definition).

* `cutoff_bounds`: `0 ≤ J_r ≤ J` off the diagonal;
* `tsum_cutoff_sub_le` (C4E9): `∑'_{v ≠ u} (J - J_r)(u,v) ≤ A 3^d (1 + 2^d/(1 - 2^{-α})) r^{-α}`;
* `tsum_added_layer_le` (C4E9): the independent added layer at intensity `β ≥ 0` has
  probability rows `∑'_{v ≠ u} (1 - e^{-β (J - J_r)(u,v)}) ≤ β ·` the same bound.

Row sums are in `ℝ≥0∞`, with the diagonal excluded.
-/

@[expose] public section
noncomputable section

open Finset
open scoped ENNReal

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-! ### The Euclidean norm of an integer point -/

/-- The expression `√(∑ᵢ zᵢ²)` is the norm in `EuclideanSpace ℝ (Fin d)`. -/
theorem euclid_eq_norm (z : Fin d → ℤ) :
    √(∑ i, ((z i : ℝ)) ^ 2) = ‖(WithLp.toLp 2 (fun i => (z i : ℝ)) : EuclideanSpace ℝ
        (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp

/-- Each coordinate is at most the Euclidean norm. -/
theorem abs_le_euclid (z : Fin d → ℤ) (i : Fin d) :
    |(z i : ℝ)| ≤ √(∑ i, ((z i : ℝ)) ^ 2) :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => ((z i : ℝ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i))

/-- A nonzero integer point has Euclidean norm at least one. -/
theorem one_le_euclid {z : Fin d → ℤ} (hz : z ≠ 0) : 1 ≤ √(∑ i, ((z i : ℝ)) ^ 2) := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    exact hz (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have h1 : (1 : ℝ) ≤ |(z i : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi
  exact h1.trans (abs_le_euclid z i)

/-- A Euclidean ball of radius `t ≥ 1` has at most `(3t)^d` integer points. -/
theorem encard_euclid_le {t : ℝ} (ht : 1 ≤ t) :
    (({z : Fin d → ℤ | √(∑ i, ((z i : ℝ)) ^ 2) ≤ t}.encard : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal ((3 * t) ^ d) := by
  set n := ⌊t⌋₊
  have hsub : {z : Fin d → ℤ | √(∑ i, ((z i : ℝ)) ^ 2) ≤ t} ⊆ {z | ‖z‖ ≤ n} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [norm_le_natCast_iff]
    intro i
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact (abs_le_euclid z i).trans hz
  have hcard : ({z : Fin d → ℤ | ‖z‖ ≤ n}.encard : ℝ≥0∞) = ((2 * n + 1) ^ d : ℕ) := by
    rw [← (finite_norm_le n).cast_ncard_eq, ← Nat.card_coe_set_eq]
    erw [card_norm_le]
    simp
  calc (({z : Fin d → ℤ | √(∑ i, ((z i : ℝ)) ^ 2) ≤ t}.encard : ℕ∞) : ℝ≥0∞)
      ≤ ({z : Fin d → ℤ | ‖z‖ ≤ n}.encard : ℝ≥0∞) := by
        exact_mod_cast Set.encard_le_encard hsub
    _ = ENNReal.ofReal ((2 * n + 1 : ℝ) ^ d) := by
        rw [hcard, ← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hn : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
        exact pow_le_pow_left₀ (by positivity) (by linarith) d

/-- `∑' z, (if P z then c else 0) = |{P}| c`. -/
theorem tsum_ite_const_eq {α : Type*} (P : α → Prop) [DecidablePred P] (c : ℝ≥0∞) :
    ∑' z, (if P z then c else 0) = ({z | P z}.encard : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_const, tsum_subtype {z | P z} (fun _ => c)]
  exact tsum_congr fun z => by by_cases h : P z <;> simp [h]

/-! ### The cutoff -/

variable {j : ℝ → ℝ} {α A : ℝ}

/-- **The cutoff kernel lies between `0` and `J`.** For `u ≠ v` and `r ≥ 1`,
`0 ≤ 1{‖v-u‖₂ ≤ r} (j ‖v-u‖₂ - j r) ≤ j ‖v-u‖₂`. -/
theorem cutoff_bounds (hj0 : ∀ t, 1 ≤ t → 0 ≤ j t) (hjm : AntitoneOn j (Set.Ici 1))
    {r : ℝ} (hr : 1 ≤ r) {u v : Fin d → ℤ} (huv : u ≠ v) :
    0 ≤ (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0) ∧
      (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0) ≤
        j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) := by
  have he := one_le_euclid (sub_ne_zero.2 huv.symm)
  split_ifs with h
  · exact ⟨sub_nonneg.2 (hjm he hr h), sub_le_self _ (hj0 r hr)⟩
  · exact ⟨le_rfl, hj0 _ he⟩

/-- The difference `J - J_r` at displacement `z ≠ 0`. -/
theorem sub_cutoff_eq (r : ℝ) (z : Fin d → ℤ) :
    j √(∑ i, ((z i : ℤ) : ℝ) ^ 2) -
        (if √(∑ i, ((z i : ℤ) : ℝ) ^ 2) ≤ r then j √(∑ i, ((z i : ℤ) : ℝ) ^ 2) - j r else 0) =
      if √(∑ i, ((z i : ℤ) : ℝ) ^ 2) ≤ r then j r else j √(∑ i, ((z i : ℤ) : ℝ) ^ 2) := by
  split_ifs <;> ring

/-- The real identity behind the dyadic shells. -/
theorem shell_term_eq {r : ℝ} (hr : 0 < r) (A : ℝ) (k : ℕ) :
    (3 * (2 ^ (k + 1) * r)) ^ d * (A * (2 ^ k * r) ^ (-(d : ℝ) - α)) =
      A * 3 ^ d * 2 ^ d * r ^ (-α) * (2 ^ (-α)) ^ k := by
  have h2k : (0 : ℝ) < 2 ^ k * r := by positivity
  have h2α : (0 : ℝ) < 2 ^ α := by positivity
  have hrα : (0 : ℝ) < r ^ α := by positivity
  have hsplit : (2 ^ k * r : ℝ) ^ (-(d : ℝ) - α) = ((2 ^ k * r) ^ d)⁻¹ / ((2 ^ α) ^ k * r ^ α) := by
    rw [Real.rpow_sub h2k, Real.rpow_neg h2k.le, Real.rpow_natCast,
      Real.mul_rpow (by positivity) hr.le]
    congr 2
    rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ) α,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [hsplit, Real.rpow_neg hr.le, Real.rpow_neg (by norm_num)]
  have hpow : (2 ^ k * r : ℝ) ^ d ≠ 0 := pow_ne_zero _ h2k.ne'
  rw [show (3 * (2 ^ (k + 1) * r) : ℝ) = 3 * 2 * (2 ^ k * r) by ring, mul_pow, mul_pow]
  field_simp
  rw [mul_assoc, ← mul_pow, mul_one_div_cancel h2α.ne', one_pow, mul_one]

/-- **The row of `J - J_r`.** For `r ≥ 1`,
`∑'_{v ≠ u} (J - J_r)(u,v) ≤ A 3^d (1 + 2^d/(1 - 2^{-α})) r^{-α}`. -/
theorem tsum_cutoff_sub_le (hα : 0 < α) (hA : 0 ≤ A)
    (hjA : ∀ t, 1 ≤ t → j t ≤ A * t ^ (-(d : ℝ) - α))
    {r : ℝ} (hr : 1 ≤ r) (u : Fin d → ℤ) :
    (∑' v, if v = u then 0 else ENNReal.ofReal (j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) -
        (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
          j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0))) ≤
      ENNReal.ofReal (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α)) := by
  have hr0 : 0 < r := by linarith
  set e : (Fin d → ℤ) → ℝ := fun z => √(∑ i, ((z i : ℤ) : ℝ) ^ 2) with he
  have h2α : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h2α0 : (0 : ℝ) ≤ 2 ^ (-α) := by positivity
  -- shift to the origin
  rw [← (Equiv.addRight u).tsum_eq]
  simp only [Equiv.coe_addRight, add_sub_cancel_right, add_eq_right]
  simp_rw [sub_cutoff_eq]
  -- pointwise domination
  let inner : (Fin d → ℤ) → ℝ≥0∞ := fun z => if e z ≤ r then ENNReal.ofReal (A * r ^ (-(d : ℝ) - α))
    else 0
  let outer : ℕ → (Fin d → ℤ) → ℝ≥0∞ := fun k z =>
    if e z < 2 ^ (k + 1) * r then ENNReal.ofReal (A * (2 ^ k * r) ^ (-(d : ℝ) - α)) else 0
  have hpt : ∀ z : Fin d → ℤ, (if z = 0 then 0 else
      ENNReal.ofReal (if e z ≤ r then j r else j (e z))) ≤ inner z + ∑' k, outer k z := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    have hez := one_le_euclid hz
    simp only [hz, ite_false]
    by_cases h : e z ≤ r
    · simp only [h, ite_true, inner]
      refine le_add_right (ENNReal.ofReal_le_ofReal ?_)
      exact hjA r hr
    · have h' := not_le.1 h
      simp only [h, ite_false, inner, zero_add]
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (show 1 ≤ e z / r by
        rw [le_div_iff₀ hr0]; linarith [h']) (show (1 : ℝ) < 2 by norm_num)
      rw [le_div_iff₀ hr0] at hk1
      rw [div_lt_iff₀ hr0] at hk2
      refine le_trans ?_ (ENNReal.le_tsum k)
      simp only [outer, hk2, ite_true]
      apply ENNReal.ofReal_le_ofReal
      refine (hjA _ hez).trans ?_
      apply mul_le_mul_of_nonneg_left _ hA
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by linarith [d.cast_nonneg (α := ℝ)])
  calc ∑' z : Fin d → ℤ, (if z = 0 then 0 else
        ENNReal.ofReal (if e z ≤ r then j r else j (e z)))
      ≤ ∑' z, (inner z + ∑' k, outer k z) := ENNReal.tsum_le_tsum hpt
    _ = ∑' z, inner z + ∑' k, ∑' z, outer k z := by
        rw [ENNReal.tsum_add, ENNReal.tsum_comm]
    _ ≤ ENNReal.ofReal ((3 * r) ^ d) * ENNReal.ofReal (A * r ^ (-(d : ℝ) - α)) +
          ∑' k : ℕ, ENNReal.ofReal ((3 * (2 ^ (k + 1) * r)) ^ d) *
            ENNReal.ofReal (A * (2 ^ k * r) ^ (-(d : ℝ) - α)) := by
        gcongr with k
        · simp only [inner]
          rw [tsum_ite_const_eq]
          gcongr
          exact encard_euclid_le hr
        · simp only [outer]
          rw [tsum_ite_const_eq]
          gcongr
          calc (({z : Fin d → ℤ | e z < 2 ^ (k + 1) * r}.encard : ℕ∞) : ℝ≥0∞)
              ≤ (({z : Fin d → ℤ | e z ≤ 2 ^ (k + 1) * r}.encard : ℕ∞) : ℝ≥0∞) := by
                exact_mod_cast Set.encard_le_encard fun z (hz : e z < _) => hz.le
            _ ≤ _ := encard_euclid_le (by
                have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
                nlinarith)
    _ = ENNReal.ofReal (A * 3 ^ d * r ^ (-α)) +
          ∑' k : ℕ, ENNReal.ofReal (A * 3 ^ d * 2 ^ d * r ^ (-α)) *
            ENNReal.ofReal (2 ^ (-α)) ^ k := by
        congr 1
        · rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.rpow_sub hr0, Real.rpow_neg hr0.le, Real.rpow_natCast, Real.rpow_neg hr0.le,
            mul_pow]
          have : (0 : ℝ) < r ^ α := by positivity
          field_simp
        · refine tsum_congr fun k => ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow h2α0,
            ← ENNReal.ofReal_mul (by positivity), shell_term_eq hr0 A k]
    _ = ENNReal.ofReal (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ h2α0, ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
        congr 1
        ring

/-- **The added layer.** At intensity `β ≥ 0` the independent added layer
`1 - e^{-β (J - J_r)}` has probability rows at most `β A 3^d (1 + 2^d/(1 - 2^{-α})) r^{-α}`. -/
theorem tsum_added_layer_le (hα : 0 < α) (hA : 0 ≤ A)
    (hjA : ∀ t, 1 ≤ t → j t ≤ A * t ^ (-(d : ℝ) - α))
    {r : ℝ} (hr : 1 ≤ r) {β : ℝ} (hβ : 0 ≤ β) (u : Fin d → ℤ) :
    (∑' v, if v = u then 0 else ENNReal.ofReal (1 - Real.exp (-β *
        (j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) -
          (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ r then
            j √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) - j r else 0))))) ≤
      ENNReal.ofReal (β * (A * 3 ^ d * (1 + 2 ^ d / (1 - 2 ^ (-α))) * r ^ (-α))) := by
  rw [ENNReal.ofReal_mul hβ]
  refine le_trans ?_ (mul_le_mul' le_rfl (tsum_cutoff_sub_le hα hA hjA hr u))
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun v => ?_
  have hX : ∀ X : ℝ, 1 - Real.exp (-β * X) ≤ β * X := fun X => by
    have := Real.add_one_le_exp (-β * X)
    linarith
  by_cases h : v = u
  · simp [h]
  · simp only [h, ite_false]
    rw [← ENNReal.ofReal_mul hβ]
    exact ENNReal.ofReal_le_ofReal (hX _)

/-! ### Non-vacuity -/

/-- Non-vacuity: `j t = t^{-d-α}` with `A = 1`, at `d = 1`, `α = 1`, `r = 1`, satisfies every
hypothesis, so both bounds apply. -/
example (u : Fin 1 → ℤ) :
    (∑' v, if v = u then 0 else ENNReal.ofReal (
        √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ^ (-((1 : ℕ) : ℝ) - 1) -
        (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ 1 then
          √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ^ (-((1 : ℕ) : ℝ) - 1) -
            (1 : ℝ) ^ (-((1 : ℕ) : ℝ) - 1) else 0))) ≤
      ENNReal.ofReal (1 * 3 ^ 1 * (1 + 2 ^ 1 / (1 - 2 ^ (-(1 : ℝ)))) * 1 ^ (-(1 : ℝ))) := by
  exact tsum_cutoff_sub_le (d := 1) (j := fun t => t ^ (-((1 : ℕ) : ℝ) - 1)) (α := 1) (A := 1)
    one_pos zero_le_one (fun t _ => by simp) le_rfl u

/-- Non-vacuity witness for `cutoff_bounds`: `j t = t^{-2}` is nonnegative and nonincreasing on
`[1, ∞)`. -/
example {u v : Fin 1 → ℤ} (huv : u ≠ v) :
    0 ≤ (if √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ≤ 1 then
          √(∑ i, (((v - u) i : ℤ) : ℝ) ^ 2) ^ (-(2 : ℝ)) - (1 : ℝ) ^ (-(2 : ℝ)) else 0) :=
  (cutoff_bounds (j := fun t => t ^ (-(2 : ℝ))) (fun t ht => by positivity)
    (fun a ha b hb hab => Real.rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.1 ha]) hab
      (by norm_num)) le_rfl huv).1

end PercLib.Models.LongRange
