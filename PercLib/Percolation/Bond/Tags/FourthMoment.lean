/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the fourth central moment of cluster power sums.
All mathematical inputs come from the imported modules; no source proof is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.FourthMoment

/-!
# Fourth central moment of cluster power sums: correspondence

Wiki correspondence for the fourth central moment bound of finite cluster power sums.

## Main results

* `finite_power_sum_fourth_central_moment_le`
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- For independent bond percolation on any finite graph (a finite vertex set with arbitrary
edge probabilities `q`, absent edges having probability zero) and real `p ≥ 1`, with
`S_p = ∑_C |C|^p` over the open clusters,
`E (S_p - E S_p)^4 ≤ E S_{4p} + 3 (E S_{2p})^2`. -/
@[tag "I2YU"]
theorem finite_power_sum_fourth_central_moment_le [Finite V] (q : Sym2 V → unitInterval)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫ ω, (∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ p -
        ∫ ω', ∑' C : (openGraph ω').ConnectedComponent, (C.supp.ncard : ℝ) ^ p ∂law q) ^ 4
        ∂law q ≤
      ∫ ω, ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ (4 * p) ∂law q +
        3 * (∫ ω, ∑' C : (openGraph ω).ConnectedComponent, (C.supp.ncard : ℝ) ^ (2 * p)
          ∂law q) ^ 2 :=
  integral_sub_pow_four_le q hp

end PercLib.Percolation.Bond
