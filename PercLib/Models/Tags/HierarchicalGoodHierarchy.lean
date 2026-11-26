/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Statements restating this library's theorems on the choice of a good digit hierarchy. No
upstream code is copied and no definition is added. Mathematical reference: T. Hutchcroft,
*Sharp hierarchical upper bounds on the critical two-point function for long-range
percolation on ℤ^d*, arXiv:2202.07634v2, Section 2 (Proposition 2.2 and Lemma 2.3), with the
digit weight `L^{m-1}`.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.HierarchicalComparison.GoodHierarchy

/-!
# A good hierarchy through the origin (tagged statements)

Every statement is assembled from lemmas proved in the imported modules; no new mathematics.

## Main results

* `DigitHierarchy.exists_isAncestrallyGood_zero_and_le_two_mul_card_good`: below the critical
  intensity some digit hierarchy has the origin ancestrally good, and every block has at least
  half of its children good.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal
open MeasureTheory PercLib.Percolation.Bond

namespace PercLib.Models.DigitHierarchy

variable {d L : ℕ} [NeZero L]

open Classical in
/-- **A subcritical model admits an ancestrally good hierarchy through the origin.** Let
`d ≥ 1`, `L ≥ 2`, `α > 0`, `s = d + α`, `c ≥ 0`, and let `J` be a translation-invariant kernel
on `ℤ^d`. For every intensity `0 ≤ β < β_c` (`β_c = globalCriticalIntensity J`) there is a digit
hierarchy `σ` in which the singleton block `{0}` is ancestrally good
(`σ.IsAncestrallyGood J c s β 0 0`). Moreover, for every hierarchy, every level-`(n+1)` block has
at least `Q/2` good children (`Q = L^d`, children counted by block index). -/
@[tag "F2G0"]
theorem exists_isAncestrallyGood_zero_and_le_two_mul_card_good (hd : 1 ≤ d) (hL : 2 ≤ L)
    {α : ℝ} (hα : 0 < α) (c : ℝ≥0) (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ u v x : Fin d → ℤ, J s(u + x, v + x) = J s(u, v)) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity J) :
    (∃ σ : DigitHierarchy d L, σ.IsAncestrallyGood J c ((d : ℝ) + α) β 0 0) ∧
      ∀ (σ : DigitHierarchy d L) (n : ℕ) (z : Fin d → ℤ),
        L ^ d ≤ 2 * (((σ.block (n + 1) z).filter fun y =>
          σ.IsGoodBlock J c ((d : ℝ) + α) β n y).image (σ.blockIndex n)).card := by
  have hQ : 2 ≤ L ^ d := le_trans hL (Nat.le_self_pow (by omega) L)
  have hs : (0 : ℝ) < (d : ℝ) + α := by positivity
  exact ⟨exists_isAncestrallyGood_zero hL (by omega) hs hJ hβ, fun σ n z =>
    σ.card_le_two_mul_card_image_filter_isGoodBlock hQ J c _ β n z⟩

end PercLib.Models.DigitHierarchy
