/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: Heydenreich and van der Hofstad (2017), equations (8.2.6)-(8.2.8).
-/
module

public import PercLib.Percolation.Bond.IntensityRowSum
public import PercLib.Percolation.Bond.SpatialMoments.FourierBootstrapContinuity

/-!
# Control and continuity of the complete Fourier bootstrap quantity

The first component is the actual off-diagonal open-edge mass. Its rooted intensity
row gives a Lipschitz bound, while finite susceptibility supplies the already proved
continuity of the Fourier-ratio and second-difference suprema.

## Main results

* `fourierBootstrap_le_iff`: the complete weak bound controls all three actual components.
* `toReal_rowSum_le_toReal_chi_sub_one`: susceptibility bounds the first component.
* `continuousAt_fourierBootstrap_intensity`: continuity of the complete actual bootstrap.
-/

@[expose] public section

noncomputable section

open PercLib.Models.Site
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Lace

variable {d : ℕ}

/-- A bound on the complete bootstrap quantity is exactly the three component bounds. -/
theorem fourierBootstrap_le_iff (q : Sym2 (Fin d → ℤ) → unitInterval) (K : ℝ) :
    fourierBootstrap q ≤ K ↔
      (rowSum (fun e => unitInterval.toENNReal (q e)) 0).toReal ≤ K ∧
        fourierRatioSup q ≤ K ∧ fourierDifferenceSup q ≤ K := by
  simp only [fourierBootstrap, max_le_iff]

/-- Finite susceptibility bounds the actual off-diagonal open-edge mass by `χ - 1`. -/
theorem toReal_rowSum_le_toReal_chi_sub_one {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (hchi : chi q o ≠ ⊤) :
    (rowSum (fun e => unitInterval.toENNReal (q e)) o).toReal ≤ (chi q o).toReal - 1 := by
  have h := one_add_rowSum_le_chi q o
  have hrow : rowSum (fun e => unitInterval.toENNReal (q e)) o ≠ ⊤ :=
    ne_top_of_le_ne_top hchi ((le_add_self :
      rowSum (fun e => unitInterval.toENNReal (q e)) o ≤
        1 + rowSum (fun e => unitInterval.toENNReal (q e)) o).trans h)
  have hr := ENNReal.toReal_mono hchi h
  rw [ENNReal.toReal_add ENNReal.one_ne_top hrow, ENNReal.toReal_one] at hr
  linarith

/-- The complete actual Fourier bootstrap is continuous at finite susceptibility
for a transitive finite-range intensity family with finite rooted intensity row. -/
theorem continuousAt_fourierBootstrap_intensity (hd : 0 < d)
    (J : Sym2 (LatticeSite d) → ℝ≥0)
    (hJ : ∀ x y : LatticeSite d, ∃ σ : LatticeSite d ≃ LatticeSite d,
      σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) 0 < ⊤)
    {R : ℝ} (hR : 0 ≤ R)
    (hrange : ∀ x y : LatticeSite d, R < ‖x - y‖ → J s(x, y) = 0)
    {β : ℝ≥0} (hchi : chi (intensityProfile J β) 0 ≠ ⊤) :
    ContinuousAt (fun b : ℝ≥0 => fourierBootstrap (intensityProfile J b)) β := by
  exact (continuous_toReal_rowSum_intensityProfile J 0 hL.ne).continuousAt.max
    ((continuousAt_fourierRatioSup_intensity hd J hJ hL hchi).max
      (continuousAt_fourierDifferenceSup_intensity hd J hJ hL hR hrange hchi))

end PercLib.Percolation.Bond.Lace
