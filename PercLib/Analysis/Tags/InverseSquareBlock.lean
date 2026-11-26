/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the integrated-susceptibility assertion PAFY, proved from
`InverseSquareBlock.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.InverseSquareBlock

/-!
# Inverse-square block integral: correspondence

Wiki correspondence for the block integral and double-sum bound of
`PercLib/Analysis/InverseSquareBlock.lean`.

## Main results

* `inverse_square_block_bounds`
-/

@[expose] public section
noncomputable section

namespace PercLib.Analysis

/-- **PAFY.** For `a > 0` and `A ≥ 0`,
`∫₀^A ∫₀^A (a + x + y)⁻² dy dx = log ((a + A)² / (a (a + 2A)))`; and if `K, m ≥ 2` are
integers, `M = ⌊Km/2⌋` and `u, v ≥ M` are integers, then
`∑_{i=1}^u ∑_{j=1}^v (6K + i + j)⁻² ≥ log (m / 64)`. -/
@[tag "PAFY"]
theorem inverse_square_block_bounds :
    (∀ {a A : ℝ}, 0 < a → 0 ≤ A →
      ∫ x in (0 : ℝ)..A, ∫ y in (0 : ℝ)..A, 1 / (a + x + y) ^ 2 =
        Real.log ((a + A) ^ 2 / (a * (a + 2 * A)))) ∧
    (∀ {K m u v : ℕ}, 2 ≤ K → 2 ≤ m → K * m / 2 ≤ u → K * m / 2 ≤ v →
      Real.log (m / 64) ≤ ∑ i ∈ Finset.Icc 1 u, ∑ j ∈ Finset.Icc 1 v,
        1 / ((6 * K + i + j : ℕ) : ℝ) ^ 2) :=
  ⟨fun ha hA => integral_integral_one_div_add_add_sq ha hA,
    fun hK hm hu hv => log_div_le_sum_sum_one_div_sq hK hm hu hv⟩

end PercLib.Analysis
