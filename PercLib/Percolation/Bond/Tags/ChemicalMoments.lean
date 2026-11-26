/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the chemical-distance moment bound.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ChemicalMoments

/-!
# Chemical-distance moments: correspondence

Wiki correspondence for the bound of every rooted chemical-distance moment by a power of
the susceptibility.

## Main results

* `lintegral_tsum_dist_pow_le_factorial_mul_chi_pow`
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal Nat

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- **Susceptibility bounds all rooted chemical-distance moments.** For an independent bond
law on a countable vertex set, invariant under a transitive group of vertex bijections, with
finite susceptibility `χ = E|K_o|`, and every integer `k ≥ 1`, the moment
`D_k = E ∑_{x ∈ K_o} d_ω(o,x)^k` (summed only over the cluster; equal to the unrestricted sum
since the distance vanishes off the cluster) is finite and at most `k! χ^(k+1)`. -/
@[tag "SBMG"]
theorem lintegral_tsum_dist_pow_le_factorial_mul_chi_pow [Countable V]
    (q : Sym2 V → unitInterval)
    (hq : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, q (Sym2.map σ e) = q e) (o : V)
    (hχ : chi q o ≠ ⊤) (k : ℕ) (hk : 1 ≤ k) :
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
        ∂law q =
      ∫⁻ ω, ∑' x, ((openGraph ω).dist o x : ℝ≥0∞) ^ k ∂law q ∧
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
        ∂law q < ⊤ ∧
    ∫⁻ ω, ∑' x, (cluster ω o).indicator (fun y => ((openGraph ω).dist o y : ℝ≥0∞) ^ k) x
        ∂law q ≤ k ! * chi q o ^ (k + 1) :=
  ⟨lintegral_tsum_indicator_cluster_dist_pow_eq q o hk,
    lintegral_tsum_indicator_cluster_dist_pow_lt_top_of_transitive q hq o hχ k,
    lintegral_tsum_indicator_cluster_dist_pow_le_of_transitive q hq o k⟩

end PercLib.Percolation.Bond
