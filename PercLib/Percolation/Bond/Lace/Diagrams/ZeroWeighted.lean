/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Diagrams.MarkedConnectorBounds

/-!
# The weighted zeroth lace coefficient

## Main results

BK and the actual first-step estimate bound the weighted zeroth coefficient
by the unshifted weighted continuation pair, with constant one. The weight
only needs to vanish at the root; translation invariance is not required.
-/

@[expose] public section
noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {G : Type*} [AddCommGroup G] [Countable G]

/-- The actual zeroth coefficient is controlled by the unshifted weighted pair,
using BK on its two connections and a first step on one weighted arm. -/
theorem tsum_weight_mul_piZero_le_weightedPair
    (q : Sym2 G → unitInterval) (w : G → ℝ≥0∞) (hw : w 0 = 0) :
    (∑' y, w y * piZero q 0 y) ≤ diagramWeightedPair q w 0 := by
  unfold diagramWeightedPair
  apply ENNReal.tsum_le_tsum
  intro y
  calc
    _ ≤ w y * tau q 0 y ^ 2 := mul_le_mul' le_rfl (piZero_le_tau_sq q 0 y)
    _ = (w y * tau q 0 y) * tau q 0 y := by rw [pow_two, mul_assoc]
    _ ≤ _ := by
      simpa only [add_zero] using
        mul_le_mul' (weight_mul_tau_le_weight_mul_continuation q w hw y) (le_refl (tau q 0 y))

end PercLib.Percolation.Bond.Lace
