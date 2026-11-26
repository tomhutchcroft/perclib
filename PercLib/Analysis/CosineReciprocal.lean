/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
Mathematical reference: Heydenreich and van der Hofstad (2017), Lemma 8.2,
with absolute reciprocal factors retained for signed kernels.
-/
module

public import PercLib.Analysis.CosineDifference
public import PercLib.Analysis.ReciprocalDifference

/-!
# Reciprocal differences of signed cosine transforms

## Main results

The absolute-value reciprocal estimate follows from actual sums of a signed
summable kernel. Neither positive reciprocal denominators nor assumed Fourier
difference estimates are needed.
-/

@[expose] public section

namespace PercLib.Analysis

/-- Absolute reciprocal bound for a signed summable cosine kernel. The local
names only abbreviate the three transforms and their absolute cosine moments. -/
theorem abs_cosine_reciprocal_second_difference_le {ι : Type*} {a : ι → ℝ}
    (ha : Summable a) (l k : ι → ℝ)
    (hm : 1 - (∑' i, a i * Real.cos (l i - k i)) ≠ 0)
    (h0 : 1 - (∑' i, a i * Real.cos (l i)) ≠ 0)
    (hp : 1 - (∑' i, a i * Real.cos (l i + k i)) ≠ 0) :
    let Am := (1 - (∑' i, a i * Real.cos (l i - k i)))⁻¹
    let A0 := (1 - (∑' i, a i * Real.cos (l i)))⁻¹
    let Ap := (1 - (∑' i, a i * Real.cos (l i + k i)))⁻¹
    let Ml := ∑' i, |a i| * (1 - Real.cos (l i))
    let Mk := ∑' i, |a i| * (1 - Real.cos (k i))
    |Am + Ap - 2 * A0| ≤ (|Am| + |Ap|) * |A0| * Mk +
      8 * |Am * A0 * Ap| * Ml * Mk :=
  abs_reciprocal_second_difference_le hm h0 hp
    (abs_tsum_cos_second_difference_le ha l k)
    (tsum_cos_antisymmetric_difference_sq_le ha l k)

end PercLib.Analysis
