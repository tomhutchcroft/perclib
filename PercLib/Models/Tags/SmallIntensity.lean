/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for normalized intensity models at small intensity and for the
root-only second-moment counterexample. All mathematical inputs are proved in the imported
modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.NormalizedSmallIntensity
public import PercLib.Models.HeavySecondMoment

/-!
# Small-intensity normalized models and a heavy root cluster: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `normalized_small_intensity_chi`: susceptibility and triangle bounds, local Lipschitz
  continuity with `χ' ≤ (1 - β)⁻²`, and failure of the stronger triangle formula at small
  intensity, for a transitive intensity model whose off-diagonal rows sum to one.
* `exists_connected_chi_eq_two_lintegral_sq_eq_top`: a countable model on a connected support
  graph with `χ(o) = 2`, a.s. finite root cluster, `E|K_o|² = ∞`, infinite exponential
  moments and unbounded susceptibilities.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

open NormalizedSmallIntensity in
/-- For a transitive intensity `J` on a countable set whose off-diagonal rows sum to one,
at every root `o`: for `0 < β < 1`, `1 + β - β²/2 ≤ χ ≤ (1 - β)⁻¹` and
`1 ≤ Δ ≤ 1 + 3 m² + m³` with `m = β / (1 - β)` and `Δ = ∑' u v, τ(o,u) τ(u,v) τ(v,o)`; the
real susceptibility is locally Lipschitz on `(0, 1)` with `χ' ≤ (1 - β)⁻²` almost
everywhere; and for some `ε > 0`, almost every `β ∈ (0, ε)` has
`χ'(β) < χ (χ - Δ) / (3 β² Δ²)`, so the stronger triangle formula fails there. -/
@[tag "1EWX"]
theorem normalized_small_intensity_chi {V : Type*} [Countable V] (J : Sym2 V → ℝ≥0)
    (hJ : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1) (o : V) :
    (∀ β : ℝ≥0, 0 < β → β < 1 →
      (ENNReal.ofReal (1 + β - (β : ℝ) ^ 2 / 2) ≤ chi (intensityProfile J β) o ∧
        chi (intensityProfile J β) o ≤ (1 - (β : ℝ≥0∞))⁻¹) ∧
      (1 ≤ ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
          tau (intensityProfile J β) v o ∧
        ∑' u, ∑' v, tau (intensityProfile J β) o u * tau (intensityProfile J β) u v *
            tau (intensityProfile J β) v o ≤
          1 + 3 * ((β : ℝ≥0∞) / (1 - β)) ^ 2 + ((β : ℝ≥0∞) / (1 - β)) ^ 3)) ∧
    LocallyLipschitzOn (Ioo 0 1)
      (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) ∧
    (∀ᵐ β, β ∈ Ioo (0 : ℝ) 1 → ∃ D,
      HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) D β ∧
      D ≤ ((1 - β) ^ 2)⁻¹) ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ β, β ∈ Ioo (0 : ℝ) ε → ∃ D,
      HasDerivAt (fun u : ℝ => (chi (intensityProfile J u.toNNReal) o).toReal) D β ∧
      D < (chi (intensityProfile J β.toNNReal) o).toReal *
          ((chi (intensityProfile J β.toNNReal) o).toReal -
            (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) o u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v o).toReal) /
          (3 * β ^ 2 * (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) o u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v o).toReal ^ 2) :=
  ⟨fun β hβ0 hβ => ⟨chi_bounds_of_transitive J hrow hJ β hβ0 hβ o,
      triangle_bounds_of_transitive J hrow hJ β hβ0 hβ o⟩,
    locallyLipschitzOn_chi_Ioo_zero_one J hJ hrow o,
    ae_hasDerivAt_chi_le_inv_one_sub_sq J hJ hrow o,
    1 / 100, by norm_num, ae_hasDerivAt_chi_lt_triangle_formula J hJ hrow o⟩

/-- There is an independent bond model on a countable vertex set whose support graph
`{e | 0 < q e}` is connected, with a root `o` such that `χ(o) = E|K_o| = 2`, the root cluster
is finite almost surely, `E|K_o|² = ∞`, `E exp(t |K_o|) = ∞` for every `t > 0`, and
`sup_v χ(v) = ∞`. -/
@[tag "HRS7"]
theorem exists_connected_chi_eq_two_lintegral_sq_eq_top :
    ∃ (V : Type) (_ : Countable V) (q : Sym2 V → unitInterval) (o : V),
      (SimpleGraph.fromEdgeSet {e | 0 < q e}).Connected ∧ chi q o = 2 ∧
      (∀ᵐ ω ∂law q, (cluster ω o).Finite) ∧
      ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ 2 ∂law q = ⊤ ∧
      (∀ t : ℝ, 0 < t →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (t * (cluster ω o).ncard)) ∂law q = ⊤) ∧
      ⨆ v, chi q v = ⊤ := by
  obtain ⟨q, hpath, hroot, hsupp⟩ := exists_profile
  exact ⟨_, inferInstance, q, none, connected_fromEdgeSet_pos hpath hroot,
    chi_root_eq_two hpath hroot hsupp, ae_cluster_root_finite hpath hroot hsupp,
    lintegral_encard_sq_eq_top hpath hroot hsupp,
    fun _ ht => lintegral_exp_eq_top hpath hroot hsupp ht, iSup_chi_eq_top hpath⟩

end PercLib.Models
