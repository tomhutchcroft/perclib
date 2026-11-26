/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the fourth-moment bound of the exponential-moments article.
Every statement is assembled from lemmas proved in the imported modules; no new
definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.FiniteRangeDecay

/-!
# The fourth-moment bound: statement form

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `integral_pow_four_le_and_cluster`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Real PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models

universe u v

/-- If `X ≥ 0` on a probability space has `χ = E X ≥ 1` and
`E[X e^{X/(4χ²)}] ≤ √2 χ`, then `E X⁴ ≤ 1152 χ⁴ log²(2χ) E X²`. In particular this holds for
the root cluster volume of an independent bond model on a countable vertex set whose
susceptibility is finite and the same at every vertex. -/
@[tag "IXEZ"]
theorem integral_pow_four_le_and_cluster :
    (∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ},
      AEStronglyMeasurable X P → (∀ ω, 0 ≤ X ω) → Integrable X P → 1 ≤ ∫ ω, X ω ∂P →
      Integrable (fun ω => X ω * exp (X ω / (4 * (∫ ω, X ω ∂P) ^ 2))) P →
      ∫ ω, X ω * exp (X ω / (4 * (∫ ω, X ω ∂P) ^ 2)) ∂P ≤ √2 * ∫ ω, X ω ∂P →
      Integrable (fun ω => X ω ^ 4) P ∧ Integrable (fun ω => X ω ^ 2) P ∧
        ∫ ω, X ω ^ 4 ∂P ≤
          1152 * (∫ ω, X ω ∂P) ^ 4 * Real.log (2 * ∫ ω, X ω ∂P) ^ 2 * ∫ ω, X ω ^ 2 ∂P) ∧
    (∀ {V : Type v} [Countable V] (q : Sym2 V → unitInterval) (o : V),
      (∀ x, chi q x = chi q o) → chi q o < ⊤ →
      Integrable (fun ω => ((cluster ω o).encard.toNat : ℝ) ^ 4) (law q) ∧
      Integrable (fun ω => ((cluster ω o).encard.toNat : ℝ) ^ 2) (law q) ∧
      ∫ ω, ((cluster ω o).encard.toNat : ℝ) ^ 4 ∂law q ≤
        1152 * (chi q o).toReal ^ 4 * Real.log (2 * (chi q o).toReal) ^ 2 *
          ∫ ω, ((cluster ω o).encard.toNat : ℝ) ^ 2 ∂law q) :=
  ⟨fun hXm hX0 hXi hχ hexpi hexp => integral_pow_four_le hXm hX0 hXi hχ hexpi hexp,
    fun q o hconst hfin => integral_encard_cluster_pow_four_le q o hconst hfin⟩

end PercLib.Models
