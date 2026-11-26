/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the Fourier symbol of a lazy power-law step distribution.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.FourierSymbol

/-!
# Branching random walk: correspondence

Wiki correspondence for the Fourier symbol of a lazy power-law step distribution.

## Main results

* `fourierSymbol_properties`
-/

@[expose] public section
noncomputable section
open Real

namespace PercLib.Models.LongRange

/-- For a symmetric lazy step distribution `p` on `ℤ^d` (`d ≥ 1`, `p(0) ≥ 1/2`) with
`c |x|^{-d-α} ≤ p(x) ≤ C |x|^{-d-α}` off the origin, the symbol
`φ(k) = ∑ₓ p(x) cos(k·x)` lies in `[0,1]`, equals `1` on `[-π,π]^d` only at `k = 0`, and near
`k = 0` satisfies `1 - φ(k) ≍ |k|^α` for `α < 2`, `≍ |k|² log(1/|k|)` for `α = 2` and
`≍ |k|²` for `α > 2`. Symmetry and `c ≤ C` are part of the setting but are not used. -/
@[tag "VJCW"]
theorem fourierSymbol_properties {d : ℕ} (hd : 1 ≤ d) {p : (Fin d → ℤ) → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : HasSum p 1)
    (_hsymm : ∀ x, p (-x) = p x) (hlazy : 1 / 2 ≤ p 0) {c C α : ℝ} (hc : 0 < c)
    (_hcC : c ≤ C) (hα : 0 < α)
    (hlow : ∀ x, x ≠ 0 → c * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α)) ≤ p x)
    (hup : ∀ x, x ≠ 0 → p x ≤ C * √(∑ i, ((x i : ℝ)) ^ 2) ^ (-((d : ℝ) + α))) :
    (∀ k : Fin d → ℝ, 0 ≤ ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ 1) ∧
    (∀ k : Fin d → ℝ, (∀ i, |k i| ≤ π) → ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) = 1 →
      k = 0) ∧
    (α < 2 → ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin d → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * √(∑ i, k i ^ 2) ^ α ≤ 1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ b * √(∑ i, k i ^ 2) ^ α) ∧
    (α = 2 → ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin d → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * (√(∑ i, k i ^ 2) ^ 2 * Real.log (1 / √(∑ i, k i ^ 2))) ≤
        1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤
        b * (√(∑ i, k i ^ 2) ^ 2 * Real.log (1 / √(∑ i, k i ^ 2)))) ∧
    (2 < α → ∃ δ > 0, ∃ a > 0, ∃ b > 0, ∀ k : Fin d → ℝ, 0 < √(∑ i, k i ^ 2) →
      √(∑ i, k i ^ 2) ≤ δ →
      a * √(∑ i, k i ^ 2) ^ 2 ≤ 1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ∧
      1 - ∑' x, p x * cos (∑ i, k i * (x i : ℝ)) ≤ b * √(∑ i, k i ^ 2) ^ 2) := by
  refine ⟨fun k => ⟨fourierSymbol_nonneg hp0 hp hlazy k, fourierSymbol_le_one hp0 hp k⟩,
    fun k hk h1 => eq_zero_of_fourierSymbol_eq_one hp0 hp hc hlow hk h1,
    fun h2 => one_sub_fourierSymbol_asymp_of_lt_two hd hp0 hp hc hα h2 hlow hup,
    fun h2 => ?_, fun h2 => one_sub_fourierSymbol_asymp_of_two_lt hd hp0 hp hc h2 hlow hup⟩
  subst h2
  exact one_sub_fourierSymbol_asymp_of_eq_two hd hp0 hp hc hlow hup

end PercLib.Models.LongRange
