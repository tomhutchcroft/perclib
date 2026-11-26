/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for power-law convolution bounds on `ℤ^d`. All mathematical inputs are
proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.ConvolutionLeadingTerm
public import PercLib.Models.LongRange.ConvolutionShift
public import PercLib.Models.LongRange.LatticeConvolution

/-!
# Power-law convolution bounds on `ℤ^d`: correspondence

Wiki correspondence for the power-law convolution bounds away from the logarithmic endpoints,
with `⟨x⟩ = max 1 √(∑ᵢ xᵢ²)` and `(f ⋆ g)(x) = ∑ y, f y g (x - y)`, and for the translation
obstructions and the transfer of a leading term, with `(F ⋆ g)(x) = ∑ y, F (x - y) g y`.

## Main results

* `abs_tsum_mul_sub_le_powerLaw`
* `isBigO_and_not_isBigO_tsum_mul_single_sub`
* `summable_abs_mul_and_isLittleO_tsum_mul_sub_powerLaw`
-/

@[expose] public section

noncomputable section

namespace PercLib.Models.LongRange

/-- **Power-law convolution bounds away from logarithmic endpoints.** For `a, b > 0` there is a
constant `C` depending only on `a`, `b`, `d` such that, whenever `|f x| ≤ A ⟨x⟩^(-a)` and
`|g x| ≤ B ⟨x⟩^(-b)` with `A, B ≥ 0`, the sum `(f ⋆ g)(x)` converges absolutely and
`|(f ⋆ g)(x)| ≤ C A B ⟨x⟩^(-min a b)` if `max a b > d`, and
`|(f ⋆ g)(x)| ≤ C A B ⟨x⟩^(-(a + b - d))` if `a, b < d < a + b`. -/
@[tag "IDIL"]
theorem abs_tsum_mul_sub_le_powerLaw (d : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((d : ℝ) < max a b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℝ) (f g : (Fin d → ℤ) → ℝ), 0 ≤ A → 0 ≤ B →
        (∀ x, |f x| ≤ A * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) →
        (∀ x, |g x| ≤ B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-b)) →
        ∀ x, Summable (fun y => |f y * g (x - y)|) ∧
          |∑' y, f y * g (x - y)| ≤
            C * A * B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-min a b)) ∧
    (a < d → b < d → (d : ℝ) < a + b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (A B : ℝ) (f g : (Fin d → ℤ) → ℝ), 0 ≤ A → 0 ≤ B →
        (∀ x, |f x| ≤ A * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) →
        (∀ x, |g x| ≤ B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-b)) →
        ∀ x, Summable (fun y => |f y * g (x - y)|) ∧
          |∑' y, f y * g (x - y)| ≤
            C * A * B * (max 1 √(∑ i, ((x i : ℝ)) ^ 2)) ^ (-(a + b - d))) :=
  ⟨exists_abs_tsum_mul_sub_le_of_lt_max d ha hb,
    exists_abs_tsum_mul_sub_le_of_lt_add d ha hb⟩

/-- **Translations obstruct a convolution remainder beyond its cancellation order.** Let
`d > 2`, `s = d - 2`, `F(x) = ⟨x⟩^(-s)` and `e = e₁`. Along the integers `R → ∞`,
`(F ⋆ δₑ)(R e) - F(R e) = s R^(-s-1) + O(R^(-s-2))`, and for `g = (δₑ + δ₋ₑ)/2`,
`(F ⋆ g)(R e) - F(R e) = s(s+1)/2 R^(-s-2) + O(R^(-s-4))`. Consequently the first difference
is not `O(R^(-s-ρ))` for any `ρ > 1`, and the second is not for any `ρ > 2`. -/
@[tag "UDUU"]
theorem isBigO_and_not_isBigO_tsum_mul_single_sub (d : ℕ) (hd : 2 < d)
    {F : (Fin d → ℤ) → ℝ}
    (hF : ∀ x, F x = (max 1 √(∑ j, ((x j : ℝ)) ^ 2)) ^ (-((d : ℝ) - 2))) :
    (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ) - y) *
        (Pi.single (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) (1 : ℝ) :
          (Fin d → ℤ) → ℝ) y -
        F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) -
        ((d : ℝ) - 2) * (R : ℝ) ^ (-((d : ℝ) - 2) - 1)) =O[Filter.atTop]
      (fun R : ℕ => (R : ℝ) ^ (-((d : ℝ) - 2) - 2)) ∧
    (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ) - y) *
        ((1 / 2 : ℝ) • ((Pi.single (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) (1 : ℝ) :
          (Fin d → ℤ) → ℝ) + Pi.single (-Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) 1) :
          (Fin d → ℤ) → ℝ) y -
        F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) -
        ((d : ℝ) - 2) * ((d : ℝ) - 2 + 1) / 2 * (R : ℝ) ^ (-((d : ℝ) - 2) - 2)) =O[Filter.atTop]
      (fun R : ℕ => (R : ℝ) ^ (-((d : ℝ) - 2) - 4)) ∧
    (∀ ρ : ℝ, 1 < ρ →
      ¬ (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ) - y) *
          (Pi.single (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) (1 : ℝ) :
            (Fin d → ℤ) → ℝ) y -
          F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ))) =O[Filter.atTop]
        (fun R : ℕ => (R : ℝ) ^ (-((d : ℝ) - 2) - ρ))) ∧
    (∀ ρ : ℝ, 2 < ρ →
      ¬ (fun R : ℕ => ∑' y, F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ) - y) *
          ((1 / 2 : ℝ) • ((Pi.single (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) (1 : ℝ) :
            (Fin d → ℤ) → ℝ) + Pi.single (-Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ)) 1) :
            (Fin d → ℤ) → ℝ) y -
          F ((R : ℤ) • Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℤ))) =O[Filter.atTop]
        (fun R : ℕ => (R : ℝ) ^ (-((d : ℝ) - 2) - ρ))) := by
  have hs : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (2 : ℝ) < d := by exact_mod_cast hd
    linarith
  exact ⟨isBigO_tsum_mul_single_sub hF _, isBigO_tsum_mul_smul_single_add_single_sub hF _,
    fun ρ hρ => not_isBigO_tsum_mul_single_sub hs.ne' hF _ hρ,
    fun ρ hρ => not_isBigO_tsum_mul_smul_single_add_single_sub
      (mul_pos hs (by linarith)).ne' hF _ hρ⟩

/-- **A signed summable kernel transfers a spatial power-law leading term.** Let `0 < a < d`,
`|x| = √(∑ᵢ xᵢ²)` and `⟨x⟩ = max 1 |x|`. If `f(x) = A |x|^(-a) + o(|x|^(-a))` as `|x| → ∞`,
`∑ |g| < ∞` and `|g(y)| ≤ K ⟨y⟩^(-d)`, then the convolution converges absolutely and
`(f ⋆ g)(x) = A (∑ g) |x|^(-a) + o(|x|^(-a))`. -/
@[tag "NIAD"]
theorem summable_abs_mul_and_isLittleO_tsum_mul_sub_powerLaw {d : ℕ} {a A K : ℝ} (ha : 0 < a)
    (had : a < d) {f g : (Fin d → ℤ) → ℝ}
    (hf : (fun x => f x - A * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a)) =o[Filter.comap
      (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) Filter.atTop] fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
    (hg : Summable fun y => |g y|)
    (hgK : ∀ y, |g y| ≤ K * (max 1 √(∑ i, ((y i : ℝ)) ^ 2)) ^ (-(d : ℝ))) :
    (∀ x, Summable fun y => |f (x - y) * g y|) ∧
      (fun x => ∑' y, f (x - y) * g y - A * (∑' y, g y) * (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a))
        =o[Filter.comap (fun x => √(∑ i, ((x i : ℝ)) ^ 2)) Filter.atTop]
          fun x => (√(∑ i, ((x i : ℝ)) ^ 2)) ^ (-a) :=
  summable_abs_mul_and_isLittleO_tsum_mul_sub ha had hf hg hgK

end PercLib.Models.LongRange
