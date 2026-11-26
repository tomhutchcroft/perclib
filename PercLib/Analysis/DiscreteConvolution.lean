/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Convolution of nonnegative functions on a countable group

For a group `Γ` and `f g : Γ → ℝ≥0∞`, the convolution is written inline as
`fun x => ∑' y, f y * g (y⁻¹ * x)`. Mathlib has convolution of measures and of functions on
normed spaces, and finitely supported group algebras, but not these `ℝ≥0∞` series; the
`ℓ^p` inequalities below come from mathlib's finite Hölder inequalities
(`ENNReal.inner_le_Lp_mul_Lq`, `ENNReal.inner_le_weight_mul_Lp_of_nonneg`) by passing to the
supremum over finite sets.

1. `conv_assoc`, `conv_eq_tsum_mul_inv`, `tsum_conv`: associativity, the reflected form
   `(f ⋆ g)(x) = ∑_z f(x z⁻¹) g(z)` and `∑ (f ⋆ g) = (∑ f)(∑ g)`.
2. `young_conv` (Young, `ℓ¹–ℓ^p`, `p ≥ 1`):
   `(∑ (f ⋆ g)^p)^{1/p} ≤ (∑ f)(∑ g^p)^{1/p}`.
3. `conv_le_sqrt_mul_sqrt` (Cauchy–Schwarz): `(f ⋆ g)(x) ≤ (∑ f²)^{1/2}(∑ g²)^{1/2}`.
4. `convPow_le_convPow_one`, `tsum_sq_convPow` (return probabilities): for a symmetric `μ`
   and its convolution powers `μ^{*n}` (from the indicator of `1`),
   `μ^{*2n}(x) ≤ μ^{*2n}(1)` and `∑ (μ^{*n})² = μ^{*2n}(1)`.

The group need not be countable for these identities; countability is the setting of the
applications.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PercLib.Analysis

variable {Γ : Type*} [Group Γ]

/-! ### Hölder for series in `ℝ≥0∞` -/

/-- **Hölder** for `ℝ≥0∞` series. -/
theorem tsum_mul_le_Lp_mul_Lq {ι : Type*} (f g : ι → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∑' i, f i * g i ≤ (∑' i, f i ^ p) ^ (1 / p) * (∑' i, g i ^ q) ^ (1 / q) := by
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  refine (ENNReal.inner_le_Lp_mul_Lq s f g hpq).trans (mul_le_mul' ?_ ?_)
  · exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by have := hpq.pos; positivity)
  · exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) (by have := hpq.symm.pos; positivity)

/-- **Weighted Hölder** for `ℝ≥0∞` series: `∑ w f ≤ (∑ w)^{1-1/p} (∑ w f^p)^{1/p}`. -/
theorem tsum_mul_le_weight_mul_Lp {ι : Type*} {p : ℝ} (hp : 1 ≤ p) (w f : ι → ℝ≥0∞) :
    ∑' i, w i * f i ≤ (∑' i, w i) ^ (1 - p⁻¹) * (∑' i, w i * f i ^ p) ^ p⁻¹ := by
  have h1 : 0 ≤ 1 - p⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hp)
  have h2 : 0 ≤ p⁻¹ := inv_nonneg.2 (by linarith)
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  refine (ENNReal.inner_le_weight_mul_Lp_of_nonneg s hp w f).trans (mul_le_mul' ?_ ?_)
  · exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) h1
  · exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum s) h2

/-- Left translation does not change a series. -/
theorem tsum_comp_mul_left (g : Γ → ℝ≥0∞) (y : Γ) : ∑' x, g (y⁻¹ * x) = ∑' x, g x :=
  (Equiv.mulLeft y⁻¹).tsum_eq g

/-- The reflection `y ↦ y⁻¹ x` does not change a series. -/
theorem tsum_comp_inv_mul (g : Γ → ℝ≥0∞) (x : Γ) : ∑' y, g (y⁻¹ * x) = ∑' y, g y :=
  ((Equiv.inv Γ).trans (Equiv.mulRight x)).tsum_eq g

/-! ### 1. Algebraic identities -/

/-- **Associativity.** `((f ⋆ g) ⋆ h)(x) = (f ⋆ (g ⋆ h))(x)`. -/
theorem conv_assoc (f g h : Γ → ℝ≥0∞) (x : Γ) :
    ∑' z, (∑' y, f y * g (y⁻¹ * z)) * h (z⁻¹ * x) =
      ∑' y, f y * ∑' w, g w * h (w⁻¹ * (y⁻¹ * x)) := by
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [← (Equiv.mulLeft y).tsum_eq]
  refine tsum_congr fun w => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, mul_inv_rev, mul_assoc]

/-- **Reflected form.** `(f ⋆ g)(x) = ∑_z f(x z⁻¹) g(z)`. -/
theorem conv_eq_tsum_mul_inv (f g : Γ → ℝ≥0∞) (x : Γ) :
    ∑' y, f y * g (y⁻¹ * x) = ∑' z, f (x * z⁻¹) * g z := by
  rw [← ((Equiv.inv Γ).trans (Equiv.mulLeft x)).tsum_eq]
  refine tsum_congr fun z => ?_
  simp [mul_assoc]

/-- **Total mass.** `∑ (f ⋆ g) = (∑ f)(∑ g)`. -/
theorem tsum_conv (f g : Γ → ℝ≥0∞) :
    ∑' x, ∑' y, f y * g (y⁻¹ * x) = (∑' y, f y) * ∑' x, g x := by
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun y => ?_
  rw [ENNReal.tsum_mul_left, tsum_comp_mul_left]

/-! ### 2. Young's inequality -/

/-- **Young, `ℓ¹–ℓ^p`.** For `p ≥ 1`, `(∑ (f ⋆ g)^p)^{1/p} ≤ (∑ f)(∑ g^p)^{1/p}`. -/
theorem young_conv (f g : Γ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑' x, (∑' y, f y * g (y⁻¹ * x)) ^ p) ^ (1 / p) ≤
      (∑' y, f y) * (∑' x, g x ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  set F := ∑' y, f y with hF
  -- pointwise: `(f ⋆ g)(x)^p ≤ F^{p-1} ∑_y f(y) g(y⁻¹x)^p`
  have hpt : ∀ x, (∑' y, f y * g (y⁻¹ * x)) ^ p ≤
      F ^ (p - 1) * ∑' y, f y * g (y⁻¹ * x) ^ p := by
    intro x
    have h := tsum_mul_le_weight_mul_Lp hp f (fun y => g (y⁻¹ * x))
    calc (∑' y, f y * g (y⁻¹ * x)) ^ p
        ≤ (F ^ (1 - p⁻¹) * (∑' y, f y * g (y⁻¹ * x) ^ p) ^ p⁻¹) ^ p :=
          ENNReal.rpow_le_rpow h hp0.le
      _ = F ^ (p - 1) * ∑' y, f y * g (y⁻¹ * x) ^ p := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
          congr 2
          field_simp
  have hsum : ∑' x, (∑' y, f y * g (y⁻¹ * x)) ^ p ≤ F ^ p * ∑' x, g x ^ p := by
    calc ∑' x, (∑' y, f y * g (y⁻¹ * x)) ^ p
        ≤ ∑' x, F ^ (p - 1) * ∑' y, f y * g (y⁻¹ * x) ^ p := ENNReal.tsum_le_tsum hpt
      _ = F ^ (p - 1) * (F * ∑' x, g x ^ p) := by
          rw [ENNReal.tsum_mul_left, tsum_conv f (fun x => g x ^ p)]
      _ = F ^ p * ∑' x, g x ^ p := by
          rw [← mul_assoc]
          congr 1
          conv_rhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]
  calc (∑' x, (∑' y, f y * g (y⁻¹ * x)) ^ p) ^ (1 / p)
      ≤ (F ^ p * ∑' x, g x ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = F * (∑' x, g x ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-! ### 3. Cauchy–Schwarz -/

/-- **Cauchy–Schwarz.** `(f ⋆ g)(x) ≤ (∑ f²)^{1/2} (∑ g²)^{1/2}`. -/
theorem conv_le_sqrt_mul_sqrt (f g : Γ → ℝ≥0∞) (x : Γ) :
    ∑' y, f y * g (y⁻¹ * x) ≤
      (∑' y, f y ^ 2) ^ (1 / 2 : ℝ) * (∑' y, g y ^ 2) ^ (1 / 2 : ℝ) := by
  have h := tsum_mul_le_Lp_mul_Lq f (fun y => g (y⁻¹ * x)) Real.HolderConjugate.two_two
  simp only [ENNReal.rpow_two] at h
  rwa [tsum_comp_inv_mul (fun y => g y ^ 2)] at h

/-! ### 4. Return probabilities -/

section Powers

variable (μ : Γ → ℝ≥0∞)

open Classical in
/-- Convolution with the indicator of `1` on the right. -/
theorem conv_indicator_one (f : Γ → ℝ≥0∞) (x : Γ) :
    ∑' y, f y * (if y⁻¹ * x = 1 then 1 else 0) = f x := by
  rw [tsum_eq_single x fun y hy => by
    have : y⁻¹ * x ≠ 1 := fun h => hy (inv_mul_eq_one.1 h)
    simp [this]]
  simp

open Classical in
/-- `μ^{*(a+b)} = μ^{*a} ⋆ μ^{*b}`. -/
theorem convPow_add (a b : ℕ) (x : Γ) :
    (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (a + b) : Γ → ℝ≥0∞) x =
      ∑' y, (Nat.rec (fun z => if z = 1 then 1 else 0)
          (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) a : Γ → ℝ≥0∞) y *
        (Nat.rec (fun z => if z = 1 then 1 else 0)
          (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) b : Γ → ℝ≥0∞) (y⁻¹ * x) := by
  induction b generalizing x with
  | zero => exact (conv_indicator_one _ x).symm
  | succ b ih =>
    change ∑' z, (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (a + b) : Γ → ℝ≥0∞) z * μ (z⁻¹ * x) = _
    simp_rw [ih]
    rw [conv_assoc]

open Classical in
/-- `μ^{*1} = μ`. -/
theorem convPow_one (x : Γ) :
    (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) 1 : Γ → ℝ≥0∞) x = μ x := by
  change ∑' y, (if y = 1 then (1 : ℝ≥0∞) else 0) * μ (y⁻¹ * x) = μ x
  rw [tsum_eq_single 1 fun y hy => by simp [hy]]
  simp

open Classical in
/-- The convolution powers of a symmetric `μ` are symmetric. -/
theorem convPow_inv (hμ : ∀ y, μ y⁻¹ = μ y) (n : ℕ) (x : Γ) :
    (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) n : Γ → ℝ≥0∞) x⁻¹ =
      (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) n : Γ → ℝ≥0∞) x := by
  induction n generalizing x with
  | zero =>
    change (if x⁻¹ = 1 then (1 : ℝ≥0∞) else 0) = if x = 1 then 1 else 0
    simp
  | succ n ih =>
    -- `μ^{*(n+1)} = μ ⋆ μ^{*n}` as well as `μ^{*n} ⋆ μ`.
    have hcomm : ∀ z, (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (n + 1) : Γ → ℝ≥0∞) z =
        ∑' y, μ y * (Nat.rec (fun z => if z = 1 then 1 else 0)
          (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) n : Γ → ℝ≥0∞) (y⁻¹ * z) := by
      intro z
      rw [show n + 1 = 1 + n by ring, convPow_add]
      simp_rw [convPow_one]
    rw [hcomm x]
    change ∑' y, (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) n : Γ → ℝ≥0∞) y * μ (y⁻¹ * x⁻¹) = _
    rw [← (Equiv.mulLeft x⁻¹).tsum_eq]
    refine tsum_congr fun w => ?_
    simp only [Equiv.coe_mulLeft]
    rw [mul_comm, ← hμ, ← ih]
    congr 2 <;> group

open Classical in
/-- **Return probabilities, second moment.** `∑ (μ^{*n})² = μ^{*2n}(1)`. -/
theorem tsum_sq_convPow (hμ : ∀ y, μ y⁻¹ = μ y) (n : ℕ) :
    ∑' x, (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) n : Γ → ℝ≥0∞) x ^ 2 =
      (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (2 * n) : Γ → ℝ≥0∞) 1 := by
  rw [two_mul, convPow_add]
  refine tsum_congr fun y => ?_
  rw [mul_one, convPow_inv μ hμ, sq]

open Classical in
/-- **Return probabilities, maximum at the identity.** `μ^{*2n}(x) ≤ μ^{*2n}(1)`. -/
theorem convPow_le_convPow_one (hμ : ∀ y, μ y⁻¹ = μ y) (n : ℕ) (x : Γ) :
    (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (2 * n) : Γ → ℝ≥0∞) x ≤
      (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (2 * n) : Γ → ℝ≥0∞) 1 := by
  rw [← tsum_sq_convPow μ hμ n, two_mul, convPow_add]
  refine (conv_le_sqrt_mul_sqrt _ _ x).trans (le_of_eq ?_)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← sq, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

end Powers

/-! ### Non-vacuity witnesses -/

/-- On `ℤ` (written multiplicatively), the indicator of `{0, 1}` convolved with itself takes
the value `2` at `1`. -/
example : ∑' y : Multiplicative ℤ,
    (if y = Multiplicative.ofAdd 0 ∨ y = Multiplicative.ofAdd 1 then (1 : ℝ≥0∞) else 0) *
      (if y⁻¹ * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 0 ∨
          y⁻¹ * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 1 then 1 else 0) = 2 := by
  rw [tsum_eq_sum (s := {Multiplicative.ofAdd 0, Multiplicative.ofAdd 1}) fun y hy => by
    have : ¬ (y = Multiplicative.ofAdd 0 ∨ y = Multiplicative.ofAdd 1) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
    rw [ite_eq_right this, zero_mul]]
  rw [Finset.sum_pair (by decide)]
  have h1 : (Multiplicative.ofAdd (0 : ℤ))⁻¹ * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 1 := by
    decide
  have h2 : (Multiplicative.ofAdd (1 : ℤ))⁻¹ * Multiplicative.ofAdd 1 = Multiplicative.ofAdd 0 := by
    decide
  simp only [h1, h2, true_or, or_true, ↓reduceIte, mul_one]
  norm_num

open Classical in
/-- Item 4 for the simple random walk `μ = ½(δ₁ + δ₋₁)` on `ℤ`: it is symmetric, so the
return probability bounds hold at `n = 1`. -/
example (x : Multiplicative ℤ) :
    let μ : Multiplicative ℤ → ℝ≥0∞ := fun y =>
      if y = Multiplicative.ofAdd 1 ∨ y = Multiplicative.ofAdd (-1) then 1 / 2 else 0
    (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (2 * 1) : Multiplicative ℤ → ℝ≥0∞) x ≤
      (Nat.rec (fun z => if z = 1 then 1 else 0)
        (fun _ ν z => ∑' y, ν y * μ (y⁻¹ * z)) (2 * 1) : Multiplicative ℤ → ℝ≥0∞) 1 := by
  intro μ
  have e1 : (Multiplicative.ofAdd (1 : ℤ))⁻¹ = Multiplicative.ofAdd (-1) := rfl
  have e2 : (Multiplicative.ofAdd (-1 : ℤ))⁻¹ = Multiplicative.ofAdd 1 := rfl
  have hsym : ∀ y, μ y⁻¹ = μ y := fun y => by
    simp only [μ, inv_eq_iff_eq_inv, e1, e2]
    congr 1
    exact propext or_comm
  convert convPow_le_convPow_one μ hsym 1 x

end PercLib.Analysis
