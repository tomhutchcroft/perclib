/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the cluster moments from the tree-graph bound. All mathematical inputs
are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.TreeGraph.Moments

/-!
# Cluster moments from the tree-graph bound: correspondence

Wiki correspondence for the cluster moments under a uniform susceptibility bound.

## Main results

* `cluster_moments_le_susceptibility`
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal Nat

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- All cluster moments under uniform susceptibility: with `M = ⨆ x, χ(x)`,
`E|K_o|^m ≤ (2m-3)‼ χ(o) M^{2m-2} ≤ (2m-3)‼ M^{2m-1}` for `m ≥ 1`. Finiteness of `M`
is not needed. -/
@[tag "Y84V"]
theorem cluster_moments_le_susceptibility [Countable V] (q : Sym2 V → unitInterval)
    (m : ℕ) (hm : 1 ≤ m) (o : V) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ m ∂law q ≤
        (((2 * m - 3)‼ : ℕ) : ℝ≥0∞) * chi q o * (⨆ x, chi q x) ^ (2 * m - 2) ∧
    (((2 * m - 3)‼ : ℕ) : ℝ≥0∞) * chi q o * (⨆ x, chi q x) ^ (2 * m - 2) ≤
        (((2 * m - 3)‼ : ℕ) : ℝ≥0∞) * (⨆ x, chi q x) ^ (2 * m - 1) := by
  refine ⟨lintegral_encard_pow_le_iSup q m hm o, ?_⟩
  have he : 2 * m - 1 = (2 * m - 2) + 1 := by omega
  rw [he, pow_succ, mul_assoc, mul_comm ((⨆ x, chi q x) ^ (2 * m - 2)) (⨆ x, chi q x)]
  gcongr
  exact le_iSup (fun x => chi q x) o

end PercLib.Percolation.Bond
