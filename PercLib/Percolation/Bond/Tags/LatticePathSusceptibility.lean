/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for finite susceptibility below the inverse connective constant.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.PathCountSusceptibility

/-!
# Finite susceptibility below the inverse connective constant: correspondence

## Main results

* `chi_le_tsum_pathCount_and_inv_le_sInf`
-/

@[expose] public section

open MeasureTheory Filter Topology PercLib.Models.Site
open scoped ENNReal

namespace PercLib.Percolation.Bond

open Classical in
/-- On `ℤ^d` (`d ≥ 1`), let `q` vanish on non-loop pairs that are not nearest-neighbour bonds
and be at most `p` on the bonds. If `p μ_d < 1`, where `μ_d = lim c_n^{1/n}`, then
`χ_q(x) ≤ ∑_n c_n p^n < ∞` at every root and almost surely every open cluster is finite. For
homogeneous nearest-neighbour bond percolation,
`p_c = inf {p ∈ [0,1] : P_p(|K(0)| = ∞) > 0} ≥ μ_d⁻¹`. -/
@[tag "H35T"]
theorem chi_le_tsum_pathCount_and_inv_le_sInf :
    (∀ d : ℕ, 1 ≤ d → ∀ μ : ℝ,
      Tendsto (fun n : ℕ => (pathCount d 0 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) →
      ∀ (q : Sym2 (Fin d → ℤ) → unitInterval) (p : unitInterval),
        (∀ e, ¬ e.IsDiag → e ∉ (zdGraph d).edgeSet → q e = 0) →
        (∀ e ∈ (zdGraph d).edgeSet, q e ≤ p) → (p : ℝ) * μ < 1 →
        (∀ x, chi q x ≤
          ∑' n : ℕ, (pathCount d 0 n : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) ^ n) ∧
        ∑' n : ℕ, (pathCount d 0 n : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) ^ n < ∞ ∧
        ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ μ : ℝ,
      Tendsto (fun n : ℕ => (pathCount d 0 n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) →
      μ⁻¹ ≤ sInf {p : ℝ | ∃ h : p ∈ unitInterval,
        0 < law (fun e => if e ∈ (zdGraph d).edgeSet then (⟨p, h⟩ : unitInterval) else 0)
          {ω | (cluster ω (0 : Fin d → ℤ)).Infinite}}) :=
  ⟨fun _ _ _ hμ q p hoff hle hpμ =>
    ⟨chi_le_tsum_pathCount_mul_pow q p hoff hle, tsum_pathCount_mul_pow_lt_top hμ p hpμ,
      ae_cluster_finite_of_mul_lt_one hμ q p hoff hle hpμ⟩,
    fun _ hd _ hμ => inv_le_sInf_of_tendsto_pathCount hd hμ⟩

end PercLib.Percolation.Bond
