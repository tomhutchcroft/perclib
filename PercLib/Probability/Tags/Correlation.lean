/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for complement duality, decreasing and mixed Harris inequalities,
layer-cake representations, function forms of Harris, and FKG. Every statement is
assembled from lemmas proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.HarrisDecreasing
public import PercLib.Probability.FKG

/-!
# Correlation inequalities: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `prodBernoulli_complement_duality`
* `prodBernoulli_harris_lower_and_mixed`
* `prodBernoulli_lintegral_harris`
* `prodBernoulli_integral_harris`
* `layer_cake_product_representations`
* `fkg_function_and_event_forms`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

section Configuration
variable {ι : Type*}

/-- Complement duality: complementation is a measurable involution carrying the law with
open probabilities `p` to the law with open probabilities `1 - p`. -/
@[tag "CW1V"]
theorem prodBernoulli_complement_duality (p : ι → unitInterval) :
    Measurable (compl : Set ι → Set ι) ∧ Function.Involutive (compl : Set ι → Set ι) ∧
    (prodBernoulli p).map compl = prodBernoulli (fun i => unitInterval.symm (p i)) ∧
    (∀ A : Set (Set ι), MeasurableSet A →
      prodBernoulli p {ω | ωᶜ ∈ A} = prodBernoulli (fun i => unitInterval.symm (p i)) A) ∧
    prodBernoulli p = (prodBernoulli (fun i => unitInterval.symm (p i))).map compl :=
  ⟨measurable_compl, compl_compl, prodBernoulli_map_compl p,
    fun _ hA => prodBernoulli_preimage_compl p hA, prodBernoulli_eq_map_compl p⟩

/-- Harris for two decreasing events, and negative correlation of an increasing and a
decreasing event. -/
@[tag "F4CV"]
theorem prodBernoulli_harris_lower_and_mixed (q : ι → unitInterval) {A B : Set (Set ι)}
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (IsLowerSet A → IsLowerSet B →
      prodBernoulli q A * prodBernoulli q B ≤ prodBernoulli q (A ∩ B)) ∧
    (IsUpperSet A → IsLowerSet B →
      prodBernoulli q (A ∩ B) ≤ prodBernoulli q A * prodBernoulli q B) :=
  ⟨fun hA hB => prodBernoulli_harris_of_isLowerSet q hA hB hAm hBm,
    fun hA hB => prodBernoulli_inter_le_of_isUpperSet_of_isLowerSet q hA hB hAm hBm⟩

/-- Harris inequalities for measurable `ℝ≥0∞`-valued functions: positive correlation for
two functions monotone in the same direction, negative correlation for opposite
directions. No integrability hypothesis is needed. -/
@[tag "E9HR"]
theorem prodBernoulli_lintegral_harris (q : ι → unitInterval) {f g : Set ι → ℝ≥0∞}
    (hfm : Measurable f) (hgm : Measurable g) :
    ((Monotone f ∧ Monotone g) ∨ (Antitone f ∧ Antitone g) →
      (∫⁻ ω, f ω ∂prodBernoulli q) * (∫⁻ ω, g ω ∂prodBernoulli q) ≤
        ∫⁻ ω, f ω * g ω ∂prodBernoulli q) ∧
    ((Monotone f ∧ Antitone g) ∨ (Antitone f ∧ Monotone g) →
      ∫⁻ ω, f ω * g ω ∂prodBernoulli q ≤
        (∫⁻ ω, f ω ∂prodBernoulli q) * (∫⁻ ω, g ω ∂prodBernoulli q)) := by
  refine ⟨?_, ?_⟩
  · rintro (⟨hf, hg⟩ | ⟨hf, hg⟩)
    · exact prodBernoulli_lintegral_mul_le q hf hg hfm hgm
    · exact prodBernoulli_lintegral_mul_le_of_antitone q hf hg hfm hgm
  · rintro (⟨hf, hg⟩ | ⟨hf, hg⟩)
    · exact prodBernoulli_lintegral_mul_le_of_monotone_of_antitone q hf hg hfm hgm
    · exact prodBernoulli_lintegral_mul_le_of_antitone_of_monotone q hf hg hfm hgm

/-- Harris inequalities for bounded measurable real functions, written as the sign of the
covariance. -/
@[tag "T6WJ"]
theorem prodBernoulli_integral_harris (q : ι → unitInterval) {f g : Set ι → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∃ C, ∀ ω, |f ω| ≤ C) (hgb : ∃ C, ∀ ω, |g ω| ≤ C) :
    ((Monotone f ∧ Monotone g) ∨ (Antitone f ∧ Antitone g) →
      0 ≤ (∫ ω, f ω * g ω ∂prodBernoulli q) -
        (∫ ω, f ω ∂prodBernoulli q) * (∫ ω, g ω ∂prodBernoulli q)) ∧
    ((Monotone f ∧ Antitone g) ∨ (Antitone f ∧ Monotone g) →
      (∫ ω, f ω * g ω ∂prodBernoulli q) -
        (∫ ω, f ω ∂prodBernoulli q) * (∫ ω, g ω ∂prodBernoulli q) ≤ 0) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hf' : ∀ ω, |f ω| ≤ max Cf Cg := fun ω => (hCf ω).trans (le_max_left _ _)
  have hg' : ∀ ω, |g ω| ≤ max Cf Cg := fun ω => (hCg ω).trans (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · rintro (⟨hf, hg⟩ | ⟨hf, hg⟩)
    · exact sub_nonneg.2 (prodBernoulli_integral_mul_le q hf hg hfm hgm hf' hg')
    · exact sub_nonneg.2 (prodBernoulli_integral_mul_le_of_antitone q hf hg hfm hgm hf' hg')
  · rintro (⟨hf, hg⟩ | ⟨hf, hg⟩)
    · exact sub_nonpos.2
        (prodBernoulli_integral_mul_le_of_monotone_of_antitone q hf hg hfm hgm hf' hg')
    · exact sub_nonpos.2
        (prodBernoulli_integral_mul_le_of_antitone_of_monotone q hf hg hfm hgm hf' hg')

end Configuration

section LayerCake
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Layer-cake representations of an integral, of the integral of a product, and of a
product of integrals, for any s-finite measure. -/
@[tag "KM1K"]
theorem layer_cake_product_representations (μ : Measure Ω) [SFinite μ]
    {f g : Ω → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ ω, f ω ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ {ω | ENNReal.ofReal t < f ω} ∧
    ∫⁻ ω, f ω * g ω ∂μ =
      ∫⁻ z, μ ({ω | ENNReal.ofReal z.1 < f ω} ∩ {ω | ENNReal.ofReal z.2 < g ω})
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) ∧
    (∫⁻ ω, f ω ∂μ) * (∫⁻ ω, g ω ∂μ) =
      ∫⁻ z, μ {ω | ENNReal.ofReal z.1 < f ω} * μ {ω | ENNReal.ofReal z.2 < g ω}
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
  ⟨lintegral_eq_setLIntegral_measure_ofReal_lt μ hf,
    lintegral_mul_eq_lintegral_measure_inter μ hf hg,
    lintegral_mul_lintegral_eq_lintegral_measure_mul μ hf hg⟩

end LayerCake

section FKG
variable {E : Type*} [Fintype E]

/-- FKG: under the lattice condition, nonnegative increasing functions and increasing
events are positively correlated. -/
@[tag "TKDC"]
theorem fkg_function_and_event_forms (μ : Measure (Set E)) [IsProbabilityMeasure μ]
    (hμ : ∀ ω η : Set E, μ {ω} * μ {η} ≤ μ {ω ∩ η} * μ {ω ∪ η}) :
    (∀ f g : Set E → ℝ, 0 ≤ f → 0 ≤ g → Monotone f → Monotone g →
      (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) ≤ ∫ ω, f ω * g ω ∂μ) ∧
    (∀ A B : Set (Set E), IsUpperSet A → IsUpperSet B → μ A * μ B ≤ μ (A ∩ B)) :=
  ⟨fun _ _ hf₀ hg₀ hf hg => integral_mul_integral_le_of_latticeCondition μ hμ hf₀ hg₀ hf hg,
    fun _ _ hA hB => measure_inter_ge_of_latticeCondition μ hμ hA hB⟩

end FKG

end PercLib.Probability
