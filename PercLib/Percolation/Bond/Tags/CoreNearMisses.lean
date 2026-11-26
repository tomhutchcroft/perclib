/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied. Mathematical reference:
the monotone product coupling combined with the loop-insensitivity of graph observables.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.IntensityScaling

/-!
# Kernel comparison off the diagonal: correspondence

Wiki correspondence for the comparison of two exponential-intensity kernels that are ordered
only on non-diagonal pairs. All mathematics is in
`PercLib/Percolation/Bond/IntensityScaling.lean`.

## Main results

* `kernel_comparison_offDiagonal`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- On a countable vertex set, if `J e ≤ J' e` for every non-diagonal pair `e` (diagonal
values unrestricted), then at every finite intensity `β` the two-point function, the
probability that the cluster of `x` is infinite, the probability that some cluster is
infinite and the (possibly infinite) susceptibility are all at most their values for `J'`;
consequently both the root and the global critical intensity of `J'` are at most those of
`J`. No summability is assumed. -/
@[tag "CKJQ"]
theorem kernel_comparison_offDiagonal [Countable V] {J J' : Sym2 V → ℝ≥0}
    (h : ∀ e : Sym2 V, ¬ e.IsDiag → J e ≤ J' e) :
    (∀ (β : ℝ≥0) (x y : V), tau (intensityProfile J β) x y ≤ tau (intensityProfile J' β) x y) ∧
    (∀ (β : ℝ≥0) (x : V), law (intensityProfile J β) {ω | (cluster ω x).Infinite} ≤
      law (intensityProfile J' β) {ω | (cluster ω x).Infinite}) ∧
    (∀ β : ℝ≥0, law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} ≤
      law (intensityProfile J' β) {ω | ∃ x, (cluster ω x).Infinite}) ∧
    (∀ (β : ℝ≥0) (x : V), chi (intensityProfile J β) x ≤ chi (intensityProfile J' β) x) ∧
    (∀ x : V, rootCriticalIntensity J' x ≤ rootCriticalIntensity J x) ∧
    globalCriticalIntensity J' ≤ globalCriticalIntensity J :=
  ⟨tau_le_of_le_offDiagonal h, law_cluster_infinite_le_of_le_offDiagonal h,
    law_exists_cluster_infinite_le_of_le_offDiagonal h, chi_le_of_le_offDiagonal h,
    rootCriticalIntensity_le_of_le_offDiagonal h, globalCriticalIntensity_le_of_le_offDiagonal h⟩

end PercLib.Percolation.Bond
