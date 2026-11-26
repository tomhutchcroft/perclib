/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the integrated-lower-tail assertion QW2L, proved from
`SqrtLowerBound.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.SqrtLowerBound

/-!
# Pointwise lower bound with a logarithmic loss: correspondence

Wiki correspondence for the pointwise lower bound of `PercLib/Analysis/SqrtLowerBound.lean`.

## Main results

* `sqrt_lower_bound_pointwise`
-/

@[expose] public section
noncomputable section

namespace PercLib.Analysis

/-- **QW2L.** Let `(p n)_{n ≥ 1}` be nonnegative and nonincreasing, and let `c, C > 0`, `a ≥ 0`
and `N₀ ≥ 1` with `∑_{j=1}^N p j ≥ c √N` for `N ≥ N₀` and `p n ≤ C n^{-1/2} log^a (e n)` for
`n ≥ 1`. Then `p n ≥ c' n^{-1/2} log^{-a} (e n)` for `n ≥ N₀`, with `c' > 0` depending only on
`c`, `C` and `a`. -/
@[tag "QW2L"]
theorem sqrt_lower_bound_pointwise {c C a : ℝ} (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) :
    ∃ c' > 0, ∀ (p : ℕ → ℝ) (N₀ : ℕ), 1 ≤ N₀ → (∀ n, 1 ≤ n → 0 ≤ p n) →
      AntitoneOn p (Set.Ici 1) →
      (∀ N, N₀ ≤ N → c * Real.sqrt N ≤ ∑ j ∈ Finset.Icc 1 N, p j) →
      (∀ n, 1 ≤ n → p n ≤ C * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (Real.exp 1 * n) ^ a) →
      ∀ n, N₀ ≤ n →
        c' * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log (Real.exp 1 * n) ^ a)⁻¹ ≤ p n :=
  exists_pos_le_of_sqrt_le_sum_of_le_rpow_log hc hC ha

end PercLib.Analysis
