/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for finite open degrees under summable incident probabilities.
All mathematical inputs are proved in the imported modules.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.Degree
public import PercLib.Percolation.Bond.LocalFiniteness

/-!
# Summable incident probabilities give finite open degrees: correspondence

## Main results

* `lintegral_degree_lt_top_and_ae_finite_neighbors`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

open Classical in
/-- On a countable vertex set, with no local finiteness of the host, a finite sum of the
incident (non-loop) pair probabilities at `v` makes the expected open degree at `v` finite and
the open degree at `v` almost surely finite; finite sums at every vertex give one almost-sure
event on which every open degree is finite. -/
@[tag "I24D"]
theorem lintegral_degree_lt_top_and_ae_finite_neighbors {V : Type*} [Countable V]
    (q : Sym2 V → unitInterval) :
    (∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞ →
      ∫⁻ ω, ({w | (openGraph ω).Adj v w}.encard : ℝ≥0∞) ∂law q < ∞ ∧
      ∀ᵐ ω ∂law q, ((openGraph ω).neighborSet v).Finite) ∧
    ((∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞) →
      ∀ᵐ ω ∂law q, ∀ v, ((openGraph ω).neighborSet v).Finite) :=
  ⟨fun v h => ⟨lintegral_degree_lt_top_of_rowSum_lt_top q v h,
    ae_finite_neighbors_of_rowSum_lt_top q v h⟩,
    ae_all_finite_neighbors_of_rowSum_lt_top q⟩

end PercLib.Percolation.Bond
