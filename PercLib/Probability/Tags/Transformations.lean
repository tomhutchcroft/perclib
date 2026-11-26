/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrappers for deterministic endpoints and for transformations of Bernoulli
configurations: characterisation, pullback, deterministic modification, thinning and
superposition, and independence of determined events. Every statement is assembled from
lemmas proved in the imported modules; no new definition is introduced.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Probability.BKEndpoints
public import PercLib.Probability.Characterization
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.DeterministicModification
public import PercLib.Probability.Transport.Pullback

/-!
# Transformations of Bernoulli configurations: statement forms

Each theorem restates, as one conjunction, results proved under their own names in the
imported modules.

## Main results

* `prodBernoulli_deterministic_dirac`
* `prodBernoulli_characterization`
* `prodBernoulli_pullback_injective`
* `prodBernoulli_deterministic_modification`
* `prodBernoulli_thinning_superposition`
* `prodBernoulli_determined_events`
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

universe u

namespace PercLib.Probability

open scoped Classical in
/-- A deterministic zero/one profile is the Dirac law at its open coordinates: events have
indicator probabilities and integrable observables integrate to their value there. On a
finite index type the homogeneous expectations at `0` and `1` evaluate at the empty and
full configurations. -/
@[tag "E7K6"]
theorem prodBernoulli_deterministic_dirac {E : Type*} (u : Set E) :
    prodBernoulli (fun e => if e ∈ u then 1 else 0) = Measure.dirac u ∧
    (∀ A : Set (Set E), MeasurableSet A →
      prodBernoulli (fun e => if e ∈ u then 1 else 0) A =
        A.indicator (1 : Set E → ℝ≥0∞) u) ∧
    (∀ f : Set E → ℝ, Integrable f (prodBernoulli (fun e => if e ∈ u then 1 else 0)) →
      ∫ ω, f ω ∂prodBernoulli (fun e => if e ∈ u then 1 else 0) = f u) ∧
    (∀ [Fintype E], ∀ f : Set E → ℝ,
      finiteExpectation 0 f = f ∅ ∧ finiteExpectation 1 f = f Set.univ) :=
  ⟨prodBernoulli_deterministic u, fun _ hA => prodBernoulli_deterministic_apply u hA,
    fun _ hf => integral_prodBernoulli_deterministic u hf,
    fun f => ⟨finiteExpectation_zero f, finiteExpectation_one f⟩⟩

section Characterization
variable {ι κ : Type*}

/-- A probability law on configurations is determined by its all-open probabilities of
finite sets; in particular it is the Bernoulli law with matching all-open probabilities,
and a push-forward of a Bernoulli law is Bernoulli exactly when these probabilities match. -/
@[tag "NGWR"]
theorem prodBernoulli_characterization :
    (∀ (μ : Measure (Set ι)) [IsProbabilityMeasure μ] (q : ι → unitInterval),
      (∀ F : Finset ι, μ {ω | (F : Set ι) ⊆ ω} =
        ∏ i ∈ F, (unitInterval.toNNReal (q i) : ℝ≥0∞)) → μ = prodBernoulli q) ∧
    (∀ (μ ν : Measure (Set ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (∀ F : Finset ι, μ {ω | (F : Set ι) ⊆ ω} = ν {ω | (F : Set ι) ⊆ ω}) → μ = ν) ∧
    (∀ (q : ι → unitInterval) {f : Set ι → Set κ}, Measurable f → ∀ r : κ → unitInterval,
      ((prodBernoulli q).map f = prodBernoulli r ↔
        ∀ F : Finset κ, prodBernoulli q (f ⁻¹' {ω | (F : Set κ) ⊆ ω}) =
          ∏ i ∈ F, (unitInterval.toNNReal (r i) : ℝ≥0∞))) :=
  ⟨fun μ _ q h => eq_prodBernoulli_of_subset μ q h,
    fun μ ν _ _ h => measure_ext_of_finset_subset μ ν h,
    fun q _ hf r => map_prodBernoulli_eq_iff q hf r⟩

end Characterization

section Pullback
variable {I J : Type*}

/-- Pullback along an injective map of indices is measurable and carries the Bernoulli law
at `p` to the Bernoulli law at `p ∘ g`; the same holds for arbitrary product laws. -/
@[tag "YMHY"]
theorem prodBernoulli_pullback_injective (p : I → unitInterval) {g : J → I}
    (hg : Function.Injective g) :
    Measurable (fun ω : Set I => g ⁻¹' ω) ∧
    (prodBernoulli p).map (fun ω : Set I => g ⁻¹' ω) = prodBernoulli (p ∘ g) ∧
    (∀ A : Set (Set J), MeasurableSet A →
      prodBernoulli p {ω | g ⁻¹' ω ∈ A} = prodBernoulli (p ∘ g) A) ∧
    (∀ (X : Type u) [MeasurableSpace X] (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)],
      (Measure.infinitePi μ).map (fun P : I → X => fun j => P (g j)) =
        Measure.infinitePi fun j => μ (g j)) :=
  ⟨measurable_preimage_set g, prodBernoulli_map_preimage p hg,
    fun _ hA => prodBernoulli_preimage_preimage p hg hA,
    fun _ _ μ _ => infinitePi_map_comp_injective μ hg⟩

end Pullback

section Modification
variable {ι : Type*}

/-- Deterministic modification: closing, opening or deleting the coordinates of a set `E`
is measurable, yields the correspondingly modified Bernoulli profile, and moves every
measurable increasing event in the expected direction. -/
@[tag "6J1Y"]
theorem prodBernoulli_deterministic_modification (q : ι → unitInterval) (E : Set ι)
    [DecidablePred (· ∈ E)] :
    Measurable (· ∩ E : Set ι → Set ι) ∧ Measurable (· ∪ E : Set ι → Set ι) ∧
    Measurable (· \ E : Set ι → Set ι) ∧
    (prodBernoulli q).map (· ∩ E) = prodBernoulli (fun i => if i ∈ E then q i else 0) ∧
    (prodBernoulli q).map (· ∪ E) = prodBernoulli (fun i => if i ∈ E then 1 else q i) ∧
    (prodBernoulli q).map (· \ E) = prodBernoulli (fun i => if i ∈ E then 0 else q i) ∧
    ∀ A : Set (Set ι), IsUpperSet A → MeasurableSet A →
      prodBernoulli (fun i => if i ∈ E then q i else 0) A ≤ prodBernoulli q A ∧
      prodBernoulli q A ≤ prodBernoulli (fun i => if i ∈ E then 1 else q i) A ∧
      prodBernoulli (fun i => if i ∈ E then 0 else q i) A ≤ prodBernoulli q A :=
  ⟨measurable_id.inter measurable_const, measurable_id.union measurable_const,
    measurable_id.sdiff measurable_const, prodBernoulli_map_inter q E,
    prodBernoulli_map_union q E, prodBernoulli_map_sdiff q E, fun _ hA hm =>
      ⟨prodBernoulli_inter_profile_le q E hA hm, prodBernoulli_le_union_profile q E hA hm,
        prodBernoulli_sdiff_profile_le q E hA hm⟩⟩

/-- Thinning and superposition: the intersection of independent Bernoulli configurations
has profile `p r`, and their union has profile `1 - (1 - p)(1 - r)`. -/
@[tag "KDNA"]
theorem prodBernoulli_thinning_superposition (p r : ι → unitInterval) :
    ((prodBernoulli p).prod (prodBernoulli r)).map (fun ω => ω.1 ∩ ω.2) =
      prodBernoulli (fun i => p i * r i) ∧
    ((prodBernoulli p).prod (prodBernoulli r)).map (fun ω => ω.1 ∪ ω.2) =
      prodBernoulli (fun i => unitInterval.symm
        (unitInterval.symm (p i) * unitInterval.symm (r i))) :=
  ⟨prodBernoulli_prod_map_inter p r, prodBernoulli_prod_map_union p r⟩

/-- A measurable event determined by the coordinates in `S` is the preimage of a measurable
event on `S` under restriction, and measurable events determined by finitely many pairwise
disjoint sets of coordinates are mutually independent. -/
@[tag "FH29"]
theorem prodBernoulli_determined_events (p : ι → unitInterval) :
    (∀ (S : Set ι) (A : Set (Set ι)), MeasurableSet A →
      (∀ ω ω', ω ∩ S = ω' ∩ S → (ω ∈ A ↔ ω' ∈ A)) →
      ∃ A_S : Set (Set S), MeasurableSet A_S ∧ A = {ω | {i : S | (i : ι) ∈ ω} ∈ A_S}) ∧
    (∀ (m : ℕ) (S : Fin m → Set ι) (A : Fin m → Set (Set ι)),
      Pairwise (Function.onFun Disjoint S) → (∀ j, MeasurableSet (A j)) →
      (∀ j ω ω', ω ∩ S j = ω' ∩ S j → (ω ∈ A j ↔ ω' ∈ A j)) →
      prodBernoulli p (⋂ j, A j) = ∏ j, prodBernoulli p (A j)) :=
  ⟨fun _ _ hAm hAS => exists_measurableSet_eq_preimage_of_determined hAm hAS,
    fun _ _ _ hS hAm hA => prodBernoulli_iInter_fin_of_determined p hS hAm hA⟩

end Modification

end PercLib.Probability
