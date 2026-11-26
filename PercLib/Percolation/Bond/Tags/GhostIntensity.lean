/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.GhostIntensity

/-!
# Ghost field and intensity: correspondence

Correspondence wrapper for the positive-field sprinkling bound, from
`PercLib/Percolation/Bond/GhostIntensity.lean`. No new definitions.

## Main results

* `ghost_intensity_sprinkling_and_ae_deriv`
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- **Positive-field sprinkling bound and almost-everywhere intensity derivative.** Let `J` be
preserved by a transitive group of bijections of the countable set `V`, with off-diagonal row
sum `L` at the root `o`, and let `M(β, h) = E_β[1 - e^{-h|K_o|}]` at bond probabilities
`1 - e^{-βJ}`. For `h > 0` and `β, ε ≥ 0`,
`0 ≤ M(β+ε,h) - M(β,h) ≤ ε L M(β+ε,h) ∂_h M(β,h)`; `β ↦ M(β,h)` is Lipschitz with constant
`L/(e h)`; and for almost every `β > 0` it is differentiable with
`0 ≤ ∂_β M(β,h) ≤ L M(β,h) ∂_h M(β,h)`. -/
@[tag "F7SW"]
theorem ghost_intensity_sprinkling_and_ae_deriv [Countable V] {J : Sym2 V → ℝ≥0}
    (hT : ∀ x y : V, ∃ φ : V ≃ V, φ x = y ∧ ∀ e, J (Sym2.map φ e) = J e) (o : V) {L : ℝ≥0}
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o = L) {h : ℝ} (hh : 0 < h) :
    (∀ β ε : ℝ≥0,
      0 ≤ (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J (β + ε)))).toReal -
        (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J β))).toReal ∧
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J (β + ε)))).toReal -
        (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J β))).toReal ≤
        ε * L * (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
            (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J (β + ε)))).toReal *
          deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
            (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J β))).toReal) h) ∧
    LipschitzWith (Real.toNNReal (L / (Real.exp 1 * h))) (fun β : ℝ≥0 =>
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
        ∂(law (intensityProfile J β))).toReal) ∧
    ∀ᵐ β : ℝ, 0 < β →
      DifferentiableAt ℝ (fun b : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J b.toNNReal))).toReal)
        β ∧
      0 ≤ deriv (fun b : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J b.toNNReal))).toReal)
        β ∧
      deriv (fun b : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
        (((cluster ω o).encard : ℝ≥0∞) : EReal)))) ∂(law (intensityProfile J b.toNNReal))).toReal)
        β ≤
        L * (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * (((cluster ω o).encard : ℝ≥0∞) : EReal))))
          ∂(law (intensityProfile J β.toNNReal))).toReal *
          deriv (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) *
            (((cluster ω o).encard : ℝ≥0∞) : EReal))))
              ∂(law (intensityProfile J β.toNNReal))).toReal) h :=
  ⟨fun β ε => ⟨ghost_intensity_add_sub_nonneg J o β ε hh, ghost_intensity_add_sub_le hT hL β ε hh⟩,
    lipschitzWith_ghost_intensity hT hL hh, ae_deriv_ghost_intensity_le hT hL hh⟩

end PercLib.Percolation.Bond
