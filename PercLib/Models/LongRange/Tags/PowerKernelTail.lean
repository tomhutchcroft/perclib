/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the omitted-row bounds of a Euclidean power-law intensity.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.LongRange.PowerLawTwoSided

/-!
# Omitted-row bounds for a power-law intensity: correspondence

Wiki correspondence for the two-sided strict tail bounds of a kernel on `ℤ^d` (sup norm)
comparable with `‖z‖^(-(d+α))`, finiteness of its row, and the omitted probability row
after closing all bonds longer than `R` in the exponential intensity family.

## Main results

* `powerKernel_omittedRow_bounds`
-/

@[expose] public section
noncomputable section
open PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

/-- On `ℤ^d` (`d ≥ 1`, sup norm), let `α > 0` and `c ‖z‖^{-d-α} ≤ k(z) ≤ C ‖z‖^{-d-α}` for
`z ≠ 0`, with `0 < c ≤ C`. For every real `R ≥ 1`,
`2dc/(α 2^α) R^{-α} ≤ ∑_{‖z‖ > R} k(z) ≤ 2d·3^{d-1}·C·2^α/α · R^{-α}`, the upper bound using
only the upper hypothesis. The off-diagonal row of `k` is finite, as is the intensity row at
every vertex of `J s(x,y) = k(y - x)` (such `J` exists exactly when `k` is inversion-even);
closing all bonds of length greater than `R` omits, in the exponential intensity family at `β`,
a probability row at most `β` times the upper bound. -/
@[tag "B2ZL"]
theorem powerKernel_omittedRow_bounds {d : ℕ} (hd : 1 ≤ d) {α c C : ℝ} (hα : 0 < α)
    (_hc : 0 < c) (_hcC : c ≤ C) {k : (Fin d → ℤ) → ℝ}
    (hlow : ∀ z, z ≠ 0 → c * ‖z‖ ^ (-((d : ℝ) + α)) ≤ k z)
    (hup : ∀ z, z ≠ 0 → k z ≤ C * ‖z‖ ^ (-((d : ℝ) + α))) :
    (∀ R : ℝ, 1 ≤ R →
      ENNReal.ofReal (2 * d * c / (α * 2 ^ α) * R ^ (-α)) ≤
        ∑' z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then k z else 0)) ∧
    (∀ R : ℝ, 1 ≤ R →
      ∑' z : Fin d → ℤ, ENNReal.ofReal (if R < ‖z‖ then k z else 0) ≤
        ENNReal.ofReal ((2 * d * 3 ^ (d - 1) : ℕ) * C * 2 ^ α / α * R ^ (-α))) ∧
    ∑' z : Fin d → ℤ, ENNReal.ofReal (if z = 0 then 0 else k z) < ∞ ∧
    (∀ J : Sym2 (Fin d → ℤ) → ℝ≥0, (∀ x y, (J s(x, y) : ℝ) = k (y - x)) →
      (∀ x, rowSum (fun e => (J e : ℝ≥0∞)) x < ∞) ∧
      ∀ (β : ℝ≥0) (R : ℝ), 1 ≤ R → ∀ x,
        ∑' y, (if R < ‖y - x‖ then unitInterval.toENNReal (intensityProfile J β s(x, y))
            else 0) ≤
          β * ENNReal.ofReal ((2 * d * 3 ^ (d - 1) : ℕ) * C * 2 ^ α / α * R ^ (-α))) :=
  ⟨fun _ hR => le_tsum_ofReal_kernel_tail hd hα hlow hR,
    fun _ hR => tsum_ofReal_kernel_tail_le hd hα hup hR,
    tsum_ofReal_kernel_lt_top hd hα hup,
    fun _ hJ => ⟨rowSum_kernel_lt_top hd hα hup hJ,
      fun β _ hR x => tsum_intensityProfile_tail_le hd hα hup hJ β hR x⟩⟩

end PercLib.Models.LongRange
