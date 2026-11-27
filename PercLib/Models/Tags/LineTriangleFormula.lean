/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the nearest-neighbour model on `ℤ` at small intensity. All
mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.NormalizedSmallIntensityLineSymmetry

/-!
# The nearest-neighbour line and the stronger triangle formula: statement form

The theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `line_deriv_chi_lt_triangle_formula`: on `ℤ` with weight `1/2` on nearest-neighbour
  pairs, explicit formulas for `τ`, `χ`, `χ'` and the closed triangle `Δ`; the model is
  infinite, connected, invariant under a transitive action with the mass-transport
  property, and has finite susceptibility; and `χ' < χ (χ - Δ) / (3 β² Δ²)` for all
  sufficiently small `β > 0`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Topology PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

open NormalizedSmallIntensity in
/-- On `ℤ` with `J = 1/2` on nearest-neighbour pairs and `0` on every other pair, and
`p = 1 - e^{-β/2}`: every off-diagonal row of `J` sums to one; `τ(a,b) = p^{|b-a|}`;
`χ = (1 + p)/(1 - p) = 2 e^{β/2} - 1`; `χ' = e^{β/2}` at every `β > 0`;
`Δ = ∑' u v, τ(0,u) τ(u,v) τ(v,0) = 1 + 6 p² / (1 - p²)²`. The vertex set is infinite, the
graph of positive weights is connected, the weights are invariant under the translation
action of `Multiplicative ℤ`, which is transitive and has the mass-transport property, and
`χ < ∞` at every intensity. Nevertheless `χ' < χ (χ - Δ) / (3 β² Δ²)` for all sufficiently
small `β > 0` (with `χ`, `Δ` as real numbers at the root `0`). -/
@[tag "MTYL"]
theorem line_deriv_chi_lt_triangle_formula (J : Sym2 ℤ → ℝ≥0)
    (hJ : ∀ a b, J s(a, b) = if |b - a| = 1 then 1 / 2 else 0) :
    (∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v = 1) ∧
    (∀ (β : ℝ≥0) (a b : ℤ), tau (intensityProfile J β) a b =
      ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2))) ^ (b - a).natAbs) ∧
    (∀ (β : ℝ≥0) (a : ℤ), chi (intensityProfile J β) a =
      (1 + ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2)))) /
        (1 - ENNReal.ofReal (1 - Real.exp (-((β : ℝ) / 2))))) ∧
    (∀ (β : ℝ≥0) (a : ℤ),
      chi (intensityProfile J β) a = ENNReal.ofReal (2 * Real.exp ((β : ℝ) / 2) - 1)) ∧
    (∀ β : ℝ, 0 < β → ∀ a : ℤ,
      HasDerivAt (fun b : ℝ => (chi (intensityProfile J b.toNNReal) a).toReal)
        (Real.exp (β / 2)) β) ∧
    (∀ β : ℝ≥0, ∑' u, ∑' v, tau (intensityProfile J β) 0 u * tau (intensityProfile J β) u v *
        tau (intensityProfile J β) v 0 =
      ENNReal.ofReal (1 + 6 * (1 - Real.exp (-((β : ℝ) / 2))) ^ 2 /
        (1 - (1 - Real.exp (-((β : ℝ) / 2))) ^ 2) ^ 2)) ∧
    Infinite ℤ ∧ (SimpleGraph.fromEdgeSet {e | 0 < J e}).Connected ∧
    MulAction.IsPretransitive (Multiplicative ℤ) ℤ ∧ HasMassTransport (Multiplicative ℤ) ℤ ∧
    (∀ (g : Multiplicative ℤ) (e : Sym2 ℤ), J (Sym2.map (g • ·) e) = J e) ∧
    (∀ (β : ℝ≥0) (a : ℤ), chi (intensityProfile J β) a < ⊤) ∧
    ∀ᶠ β in 𝓝[>] (0 : ℝ),
      deriv (fun b : ℝ => (chi (intensityProfile J b.toNNReal) 0).toReal) β <
        (chi (intensityProfile J β.toNNReal) 0).toReal *
          ((chi (intensityProfile J β.toNNReal) 0).toReal -
            (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) 0 u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v 0).toReal) /
          (3 * β ^ 2 * (∑' u, ∑' v, tau (intensityProfile J β.toNNReal) 0 u *
              tau (intensityProfile J β.toNNReal) u v *
              tau (intensityProfile J β.toNNReal) v 0).toReal ^ 2) :=
  ⟨line_rowSum J hJ, line_tau_eq J hJ, line_chi_eq_div J hJ, line_chi_eq J hJ,
    fun _ hβ a => line_hasDerivAt_chi J hJ hβ a, line_triangle_eq J hJ, inferInstance,
    line_connected J hJ, inferInstance,
    hasMassTransport_multiplicative_self ℤ, line_map_smul_eq J hJ, line_chi_lt_top J hJ,
    line_eventually_deriv_chi_lt J hJ⟩

end PercLib.Models
