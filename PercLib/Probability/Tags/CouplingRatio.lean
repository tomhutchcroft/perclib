/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the coupling ratio bound. Mathematical reference: the ratio step in
W. Conijn, arXiv:1502.04387v3, Proposition 10, (3.12)–(3.17). The statement is assembled from
lemmas proved in the imported module; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.CouplingRatio

/-!
# Coupling ratios: statement form

The rare-event ratio bound under a successful coupling, restated as one conjunction of results
proved under their own names in `PercLib.Probability.CouplingRatio`.

## Main results

* `coupling_ratio_bound`
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Probability

/-- If `X ∩ S = Y ∩ S` almost everywhere, `μ(Sᶜ) ≤ ε < 1`, `a, c, C > 0`,
`μ(X ∩ S) ≥ c a μ(S)` and `max (μ(X ∩ Sᶜ)) (μ(Y ∩ Sᶜ)) ≤ C a μ(Sᶜ)`, then `μ(Y) > 0` and
`|μ(X) / μ(Y) - 1| ≤ C ε / (c (1 - ε))`. -/
@[tag "KJWA"]
theorem coupling_ratio_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y S : Set Ω} (hS : NullMeasurableSet S μ)
    (hXY : (X ∩ S : Set Ω) =ᵐ[μ] (Y ∩ S : Set Ω)) {ε a c C : ℝ}
    (hε : μ.real Sᶜ ≤ ε) (hε1 : ε < 1) (ha : 0 < a) (hc : 0 < c) (hC : 0 < C)
    (hlow : c * a * μ.real S ≤ μ.real (X ∩ S))
    (hXc : μ.real (X ∩ Sᶜ) ≤ C * a * μ.real Sᶜ) (hYc : μ.real (Y ∩ Sᶜ) ≤ C * a * μ.real Sᶜ) :
    0 < μ.real Y ∧ |μ.real X / μ.real Y - 1| ≤ C * ε / (c * (1 - ε)) :=
  ⟨measureReal_pos_of_inter_ae_eq hS hXY hε hε1 ha hc hlow,
    abs_measureReal_div_sub_one_le_of_inter_ae_eq hS hXY hε hε1 ha hc hC.le hlow hXc hYc⟩

end PercLib.Probability
