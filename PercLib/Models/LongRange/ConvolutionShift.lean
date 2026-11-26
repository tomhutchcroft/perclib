/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Translation kernels and the remainder of a spatial convolution on `ℤ^d`. New for this project
against pinned mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied.
Mathematical reference: Heydenreich and van der Hofstad, *Progress in High-Dimensional
Percolation and Random Graphs* (2017), the convolution lemma of the chapter on the spatial
two-point function.
-/
module

public import PercLib.Analysis.RpowExpansion

/-!
# Translations obstruct a convolution remainder

Write `⟨x⟩ = max 1 √(∑ᵢ xᵢ²)` on `ℤ^d`, `F(x) = ⟨x⟩^(-s)`, `e = eᵢ` a unit coordinate vector,
and `(F ⋆ g)(x) = ∑ y, F(x - y) g(y)`. Along the integers `R → ∞`,
`(F ⋆ δₑ)(R e) - F(R e) = s R^(-s-1) + O(R^(-s-2))` and, for the even kernel
`g = (δₑ + δ₋ₑ)/2`, `(F ⋆ g)(R e) - F(R e) = s(s+1)/2 R^(-s-2) + O(R^(-s-4))`. Hence a finitely
supported kernel need not preserve a remainder `O(R^(-s-ρ))` for `ρ > 1` (if `s ≠ 0`), and an
even one need not for `ρ > 2` (if `s (s + 1) ≠ 0`).

## Main results

* `hasSum_mul_single_one`, `tsum_mul_single_one`: convolution with a point mass is a
  translation.
* `isBigO_tsum_mul_single_sub`: the first-order expansion for `δₑ`.
* `isBigO_tsum_mul_smul_single_add_single_sub`: the second-order expansion for
  `(δₑ + δ₋ₑ)/2`.
* `not_isBigO_tsum_mul_single_sub`, `not_isBigO_tsum_mul_smul_single_add_single_sub`: the
  obstructions.
-/

@[expose] public section

noncomputable section

open Filter Asymptotics

namespace PercLib.Models.LongRange

open PercLib.Analysis

/-! ### Point masses -/

section PointMass

variable {G : Type*} [AddGroup G] [DecidableEq G]

/-- Convolution with a point mass at `z` is translation by `z`, as a `HasSum`. -/
theorem hasSum_mul_single_one (F : G → ℝ) (x z : G) :
    HasSum (fun y => F (x - y) * (Pi.single z (1 : ℝ) : G → ℝ) y) (F (x - z)) := by
  convert hasSum_ite_eq z (F (x - z)) using 1
  funext y
  by_cases hy : y = z
  · subst hy
    simp
  · simp [hy]

/-- Convolution with a point mass at `z` is translation by `z`. -/
theorem tsum_mul_single_one (F : G → ℝ) (x z : G) :
    ∑' y, F (x - y) * (Pi.single z (1 : ℝ) : G → ℝ) y = F (x - z) :=
  (hasSum_mul_single_one F x z).tsum_eq

/-- Convolution with `(δ_z + δ_{-z})/2` is the average of the two translations. -/
theorem tsum_mul_smul_single_add_single (F : G → ℝ) (x z : G) :
    ∑' y, F (x - y) *
        ((1 / 2 : ℝ) • ((Pi.single z (1 : ℝ) : G → ℝ) + Pi.single (-z) 1) : G → ℝ) y =
      (F (x - z) + F (x + z)) / 2 := by
  have h := ((hasSum_mul_single_one F x z).add (hasSum_mul_single_one F x (-z))).mul_left (1 / 2)
  rw [sub_neg_eq_add] at h
  convert h.tsum_eq using 1
  · congr 1
    funext y
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  · ring

end PointMass

/-! ### The Euclidean bracket along a coordinate axis -/

variable {d : ℕ}

/-- The Euclidean length of `n eᵢ` is `|n|`. -/
theorem sqrt_sum_sq_zsmul_single (i : Fin d) (n : ℤ) :
    √(∑ j, (((n • Pi.single i (1 : ℤ) : Fin d → ℤ) j : ℤ) : ℝ) ^ 2) = |(n : ℝ)| := by
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp [Real.sqrt_sq_eq_abs]

/-- Along the axis, `⟨n eᵢ⟩^(-s) = n^(-s)` for integers `n ≥ 1`. -/
theorem max_sqrt_sum_sq_zsmul_single_rpow (i : Fin d) {n : ℤ} (hn : 1 ≤ n) (s : ℝ) :
    (max 1 √(∑ j, (((n • Pi.single i (1 : ℤ) : Fin d → ℤ) j : ℤ) : ℝ) ^ 2)) ^ (-s) =
      (n : ℝ) ^ (-s) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [sqrt_sum_sq_zsmul_single, abs_of_nonneg (by linarith), max_eq_right hn']

/-! ### Expansions and obstructions -/

section Expansion

variable {s : ℝ} {F : (Fin d → ℤ) → ℝ}

/-- The values of `F = ⟨·⟩^(-s)` at `(R + k) eᵢ` for `R + k ≥ 1`. -/
theorem apply_natCast_add_zsmul_single (hF : ∀ x, F x = (max 1 √(∑ j, ((x j : ℝ)) ^ 2)) ^ (-s))
    (i : Fin d) {R : ℕ} {k : ℤ} (hRk : 1 ≤ (R : ℤ) + k) :
    F (((R : ℤ) + k) • Pi.single i (1 : ℤ)) = ((R : ℝ) + k) ^ (-s) := by
  rw [hF, max_sqrt_sum_sq_zsmul_single_rpow i hRk]
  push_cast
  rfl

/-- **First-order expansion for a point mass.** With `F = ⟨·⟩^(-s)` and `e = eᵢ`,
`(F ⋆ δₑ)(R e) - F(R e) = s R^(-s-1) + O(R^(-s-2))` along the integers. -/
theorem isBigO_tsum_mul_single_sub
    (hF : ∀ x, F x = (max 1 √(∑ j, ((x j : ℝ)) ^ 2)) ^ (-s)) (i : Fin d) :
    (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single i (1 : ℤ) - y) *
        (Pi.single (Pi.single i (1 : ℤ)) (1 : ℝ) : (Fin d → ℤ) → ℝ) y -
        F ((R : ℤ) • Pi.single i (1 : ℤ)) - s * (R : ℝ) ^ (-s - 1)) =O[atTop]
      fun R : ℕ => (R : ℝ) ^ (-s - 2) := by
  refine (isBigO_natCast_sub_one_rpow_neg_sub s).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with R hR
  have hR' : (2 : ℤ) ≤ R := by exact_mod_cast hR
  rw [tsum_mul_single_one]
  have e1 := apply_natCast_add_zsmul_single hF i (R := R) (k := -1) (by omega)
  have e0 := apply_natCast_add_zsmul_single hF i (R := R) (k := 0) (by omega)
  rw [add_zero] at e0
  rw [show ((R : ℤ) • Pi.single i (1 : ℤ) - Pi.single i (1 : ℤ) : Fin d → ℤ) =
      ((R : ℤ) + -1) • Pi.single i (1 : ℤ) by
    rw [add_smul, neg_one_smul, sub_eq_add_neg], e1, e0]
  push_cast
  ring_nf

/-- **Second-order expansion for the even two-point kernel.** With `F = ⟨·⟩^(-s)`, `e = eᵢ`
and `g = (δₑ + δ₋ₑ)/2`, `(F ⋆ g)(R e) - F(R e) = s(s+1)/2 R^(-s-2) + O(R^(-s-4))` along the
integers. -/
theorem isBigO_tsum_mul_smul_single_add_single_sub
    (hF : ∀ x, F x = (max 1 √(∑ j, ((x j : ℝ)) ^ 2)) ^ (-s)) (i : Fin d) :
    (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single i (1 : ℤ) - y) *
        ((1 / 2 : ℝ) • ((Pi.single (Pi.single i (1 : ℤ)) (1 : ℝ) : (Fin d → ℤ) → ℝ) +
          Pi.single (-Pi.single i (1 : ℤ)) 1) : (Fin d → ℤ) → ℝ) y -
        F ((R : ℤ) • Pi.single i (1 : ℤ)) - s * (s + 1) / 2 * (R : ℝ) ^ (-s - 2)) =O[atTop]
      fun R : ℕ => (R : ℝ) ^ (-s - 4) := by
  refine (isBigO_natCast_sub_one_add_add_one_rpow_neg_sub s).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with R hR
  have hR' : (2 : ℤ) ≤ R := by exact_mod_cast hR
  rw [tsum_mul_smul_single_add_single]
  have e1 := apply_natCast_add_zsmul_single hF i (R := R) (k := -1) (by omega)
  have e2 := apply_natCast_add_zsmul_single hF i (R := R) (k := 1) (by omega)
  have e0 := apply_natCast_add_zsmul_single hF i (R := R) (k := 0) (by omega)
  rw [add_zero] at e0
  rw [show ((R : ℤ) • Pi.single i (1 : ℤ) - Pi.single i (1 : ℤ) : Fin d → ℤ) =
      ((R : ℤ) + -1) • Pi.single i (1 : ℤ) by
      rw [add_smul, neg_one_smul, sub_eq_add_neg],
    show ((R : ℤ) • Pi.single i (1 : ℤ) + Pi.single i (1 : ℤ) : Fin d → ℤ) =
      ((R : ℤ) + 1) • Pi.single i (1 : ℤ) by
      rw [add_smul, one_smul], e1, e2, e0]
  push_cast
  ring_nf

/-- **Obstruction for a point mass.** If `s ≠ 0`, then `(F ⋆ δₑ)(R e) - F(R e)` is not
`O(R^(-s-ρ))` for any `ρ > 1`. -/
theorem not_isBigO_tsum_mul_single_sub (hs : s ≠ 0)
    (hF : ∀ x, F x = (max 1 √(∑ j, ((x j : ℝ)) ^ 2)) ^ (-s)) (i : Fin d) {ρ : ℝ} (hρ : 1 < ρ) :
    ¬ (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single i (1 : ℤ) - y) *
        (Pi.single (Pi.single i (1 : ℤ)) (1 : ℝ) : (Fin d → ℤ) → ℝ) y -
        F ((R : ℤ) • Pi.single i (1 : ℤ))) =O[atTop] fun R : ℕ => (R : ℝ) ^ (-s - ρ) :=
  not_isBigO_natCast_rpow_of_isBigO_sub hs (by linarith) (isBigO_tsum_mul_single_sub hF i)
    (by linarith)

/-- **Obstruction for the even two-point kernel.** If `s (s + 1) ≠ 0`, then
`(F ⋆ g)(R e) - F(R e)` with `g = (δₑ + δ₋ₑ)/2` is not `O(R^(-s-ρ))` for any `ρ > 2`. -/
theorem not_isBigO_tsum_mul_smul_single_add_single_sub (hs : s * (s + 1) ≠ 0)
    (hF : ∀ x, F x = (max 1 √(∑ j, ((x j : ℝ)) ^ 2)) ^ (-s)) (i : Fin d) {ρ : ℝ} (hρ : 2 < ρ) :
    ¬ (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single i (1 : ℤ) - y) *
        ((1 / 2 : ℝ) • ((Pi.single (Pi.single i (1 : ℤ)) (1 : ℝ) : (Fin d → ℤ) → ℝ) +
          Pi.single (-Pi.single i (1 : ℤ)) 1) : (Fin d → ℤ) → ℝ) y -
        F ((R : ℤ) • Pi.single i (1 : ℤ))) =O[atTop] fun R : ℕ => (R : ℝ) ^ (-s - ρ) :=
  not_isBigO_natCast_rpow_of_isBigO_sub (div_ne_zero hs two_ne_zero) (by linarith)
    (isBigO_tsum_mul_smul_single_add_single_sub hF i) (by linarith)

end Expansion

end PercLib.Models.LongRange
