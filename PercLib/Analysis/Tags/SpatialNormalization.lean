/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the spatial-normalization assertion 57FJ, proved from
`RegularVariation/Composition.lean`. No new definitions. Reference: Bingham–Goldie–Teugels,
*Regular Variation*, Proposition 1.5.7.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.RegularVariation.Composition

/-!
# Spatial normalization of regular-variation indices: correspondence

Wiki correspondence for the change of the regular-variation indices under the substitution of
a regularly varying radius `q`, from `PercLib/Analysis/RegularVariation/Composition.lean`.

## Main results

* `regularlyVarying_spatialNormalization`
-/

@[expose] public section

namespace PercLib.Analysis

/-- **57FJ.** Let `α > 0`, `γ = max 1 (α / 2)` and `β = α / γ`. Let `χ`, `m` be positive
measurable functions, regularly varying with indices `α` and `2α`, and let `q` be regularly
varying with index `1/γ`. Then `R ↦ 4 χ (q R) / m (q R)` and `R ↦ m (q R) / 4` are regularly
varying with indices `-β` and `2β`, their product is `χ (q R)`, and `β = 2` when `α > 2`. -/
@[tag "57FJ"]
theorem regularlyVarying_spatialNormalization {α γ β : ℝ} {χ m q : ℝ → ℝ} (_hα : 0 < α)
    (hγ : γ = max 1 (α / 2)) (hβ : β = α / γ) (_hχmeas : Measurable χ)
    (_hmmeas : Measurable m) (_hχpos : ∀ r, 0 < χ r) (hmpos : ∀ r, 0 < m r)
    (hχ : RegularlyVarying α χ) (hm : RegularlyVarying (2 * α) m)
    (hq : RegularlyVarying (1 / γ) q) :
    RegularlyVarying (-β) (fun R => 4 * χ (q R) / m (q R)) ∧
      RegularlyVarying (2 * β) (fun R => m (q R) / 4) ∧
      (∀ R, 4 * χ (q R) / m (q R) * (m (q R) / 4) = χ (q R)) ∧ (2 < α → β = 2) :=
  ⟨regularlyVarying_four_mul_comp_div_comp hγ hβ hχ hm hq,
    regularlyVarying_comp_div_four hγ hβ hm hq,
    four_mul_comp_div_comp_mul_comp_div_four fun r => (hmpos r).ne',
    eq_two_of_two_lt_of_eq_div_max hγ hβ⟩

end PercLib.Analysis
