/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.TreeGraph.BranchPoint
public import PercLib.Percolation.Bond.Susceptibility

/-!
# Triangle bounds on weighted cluster moments

## Main results

The expected connection-weighted pair mass inside the actual root cluster is
bounded by susceptibility times a uniform diagonal triangle bound. The proof
uses the proved three-point tree-graph inequality and nonnegative sum exchange;
no finite-cluster assumption is needed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- Integrating the actual connection-weighted cluster pair mass gives its
joint-connection probability sum. -/
theorem lintegral_cluster_pair_tau_eq (q : Sym2 V → unitInterval) (o : V) :
    (∫⁻ ω, ∑' x, ∑' y,
      (conn o x ∩ conn o y).indicator (fun _ => tau q x y) ω ∂law q) =
      ∑' x, ∑' y, tau q x y * law q (conn o x ∩ conn o y) := by
  rw [lintegral_tsum fun x => Measurable.aemeasurable (Measurable.tsum fun y =>
    measurable_const.indicator ((measurableSet_conn o x).inter (measurableSet_conn o y)))]
  apply tsum_congr
  intro x
  rw [lintegral_tsum fun y => (measurable_const.indicator
    ((measurableSet_conn o x).inter (measurableSet_conn o y))).aemeasurable]
  apply tsum_congr
  intro y
  rw [lintegral_indicator_const ((measurableSet_conn o x).inter (measurableSet_conn o y))]

/-- The tree-graph inequality controls the actual weighted pair moment by
root-to-branch connections times the diagonal triangles at the branch points. -/
theorem lintegral_cluster_pair_tau_le_triangles (q : Sym2 V → unitInterval) (o : V) :
    (∫⁻ ω, ∑' x, ∑' y,
      (conn o x ∩ conn o y).indicator (fun _ => tau q x y) ω ∂law q) ≤
      ∑' z, tau q o z * ∑' x, ∑' y, tau q z x * tau q x y * tau q y z := by
  rw [lintegral_cluster_pair_tau_eq]
  calc
    _ ≤ ∑' x, ∑' y, tau q x y *
        ∑' z, tau q o z * tau q z x * tau q z y := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply ENNReal.tsum_le_tsum
      intro y
      exact mul_le_mul' le_rfl (treeGraphInequality V q o x y)
    _ = _ := by
      simp_rw [← ENNReal.tsum_mul_left]
      calc
        (∑' x, ∑' y, ∑' z,
          tau q x y * (tau q o z * tau q z x * tau q z y)) =
            ∑' x, ∑' z, ∑' y,
              tau q x y * (tau q o z * tau q z x * tau q z y) := by
          apply tsum_congr
          intro x
          exact ENNReal.tsum_comm
        _ = ∑' z, ∑' x, ∑' y,
            tau q x y * (tau q o z * tau q z x * tau q z y) := ENNReal.tsum_comm
        _ = _ := by
          apply tsum_congr
          intro z
          apply tsum_congr
          intro x
          apply tsum_congr
          intro y
          rw [tau_comm q z y]
          ac_rfl

/-- A uniform actual diagonal triangle bound controls the pair moment by
`chi * Delta`; infinities are retained, so no finiteness premise is implicit. -/
theorem lintegral_cluster_pair_tau_le_chi_mul (q : Sym2 V → unitInterval) (o : V)
    (Δ : ℝ≥0∞) (hΔ : ∀ z, (∑' x, ∑' y, tau q z x * tau q x y * tau q y z) ≤ Δ) :
    (∫⁻ ω, ∑' x, ∑' y,
      (conn o x ∩ conn o y).indicator (fun _ => tau q x y) ω ∂law q) ≤ chi q o * Δ := by
  refine (lintegral_cluster_pair_tau_le_triangles q o).trans ?_
  rw [chi_eq_tsum_tau, ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum (fun z => mul_le_mul' le_rfl (hΔ z))

end PercLib.Percolation.Bond
