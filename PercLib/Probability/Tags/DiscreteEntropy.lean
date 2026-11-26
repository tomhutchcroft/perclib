/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the chain rule and the data processing inequality for the relative
entropy of laws on countable sets. The statement is assembled from lemmas proved in the imported
module; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.DiscreteEntropy

/-!
# Discrete relative entropy: statement form

The theorem restates, as one conjunction, results proved under their own names in
`PercLib.Probability.DiscreteEntropy`. Relative entropy is mathlib's `InformationTheory.klDiv`;
a countable set carries a σ-algebra with measurable singletons, so every subset is measurable.

## Main results

* `klDiv_chain_rule_fst_and_map_le`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory InformationTheory
open scoped ENNReal

universe u v w

namespace PercLib.Probability

/-- Let `μ, ν` be laws on a product `X × Y` of two countable sets. If `μ.fst ≪ ν.fst`, then
`D(μ‖ν) = D(μ.fst‖ν.fst) + ∑_{x : μ.fst {x} > 0} μ.fst {x} D(μ(· | x)‖ν(· | x))`, where
`μ(· | x)` is the law of the second coordinate under `μ` conditioned on the first being `x`.
If `μ.fst` is not absolutely continuous with respect to `ν.fst`, then `D(μ‖ν) = ∞`. For every
map `g` from `X × Y` to a countable set, `D(g_*μ‖g_*ν) ≤ D(μ‖ν)`. -/
@[tag "JR0J"]
theorem klDiv_chain_rule_fst_and_map_le {X : Type u} {Y : Type v} [MeasurableSpace X]
    [MeasurableSpace Y] [Countable X] [Countable Y] [MeasurableSingletonClass X]
    [MeasurableSingletonClass Y] (μ ν : Measure (X × Y)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    (μ.fst ≪ ν.fst →
      klDiv μ ν = klDiv μ.fst ν.fst + ∑' x : {x : X // 0 < μ.fst {x}}, μ.fst {(x : X)} *
        klDiv ((μ[|Prod.fst ⁻¹' {(x : X)}]).map Prod.snd)
          ((ν[|Prod.fst ⁻¹' {(x : X)}]).map Prod.snd)) ∧
    (¬ μ.fst ≪ ν.fst → klDiv μ ν = ∞) ∧
    (∀ (T : Type w) [MeasurableSpace T] [Countable T] [MeasurableSingletonClass T]
      (g : X × Y → T), klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν) :=
  ⟨klDiv_eq_klDiv_fst_add_tsum_cond μ ν, klDiv_eq_top_of_not_absolutelyContinuous_fst,
    fun _ _ _ _ g => klDiv_map_le_of_countable μ ν g⟩

end PercLib.Probability
