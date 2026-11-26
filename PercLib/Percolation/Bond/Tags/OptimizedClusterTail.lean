/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the optimized exponential cluster-volume tail. All mathematical inputs
are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.OptimizedClusterTail

/-!
# Optimized exponential cluster tails: correspondence

Wiki correspondence for the optimized cluster-volume tail under a uniform susceptibility bound,
with its constant-susceptibility (transitive) form.

## Main results

* `law_encard_cluster_ge_le_optimized`
-/

@[expose] public section
noncomputable section
open MeasureTheory Real
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Optimized exponential cluster tail: with `M = ⨆ x, χ(x) < ∞`, for every real `k ≥ M²`,
`P(|K_o| ≥ k) ≤ (χ(o)/M) √(e/k) e^{-k/(2M²)}`; when `χ(x) = χ(o) < ∞` for every `x`
(transitive case, `M = χ(o)`), the prefactor is `√(e/k)` for every real `k ≥ χ(o)²`. -/
@[tag "4A0G"]
theorem law_encard_cluster_ge_le_optimized [Countable V] (q : Sym2 V → unitInterval) (o : V) :
    ((⨆ x, chi q x) ≠ ⊤ → ∀ k : ℝ, (⨆ x, chi q x).toReal ^ 2 ≤ k →
      law q {ω | ENNReal.ofReal k ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
        ENNReal.ofReal ((chi q o).toReal / (⨆ x, chi q x).toReal * sqrt (exp 1 / k) *
          exp (-(k / (2 * (⨆ x, chi q x).toReal ^ 2))))) ∧
    ((∀ x, chi q x = chi q o) → chi q o ≠ ⊤ → ∀ k : ℝ, (chi q o).toReal ^ 2 ≤ k →
      law q {ω | ENNReal.ofReal k ≤ ((cluster ω o).encard : ℝ≥0∞)} ≤
        ENNReal.ofReal (sqrt (exp 1 / k) * exp (-(k / (2 * (chi q o).toReal ^ 2))))) :=
  ⟨fun hM _ hk => law_encard_cluster_ge_le_div_mul_sqrt_exp_div q o hM hk,
    fun hconst hfin _ hk => law_encard_cluster_ge_le_sqrt_exp_div_of_chi_eq q o hconst hfin hk⟩

end PercLib.Percolation.Bond
