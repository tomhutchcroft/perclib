/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.FiniteSetCriterion
public import PercLib.Percolation.Bond.IntensityMonotone
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Percolation.Bond.PathComparison
public import PercLib.Percolation.Bond.RootIndependence

/-! Correspondence wrappers for intensity layers, kernel rescaling, root independence of the
critical intensity, and transitive thresholds.
All mathematical inputs are proved in the imported modules. -/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- The union of independent intensity layers `β₁`, `β₂` has the intensity law
`β₁ + β₂`; measurable increasing events are monotone in the intensity; on countable `V` the
rooted and global thresholds separate the regimes of zero and positive percolation
probability. -/
@[tag "TWLQ"]
theorem intensity_layers_threshold_separation (J : Sym2 V → ℝ≥0) :
    (∀ β₁ β₂ : ℝ≥0, law (intensityProfile J (β₁ + β₂)) =
      ((law (intensityProfile J β₁)).prod (law (intensityProfile J β₂))).map
        (fun ω => ω.1 ∪ ω.2)) ∧
    (∀ A : Set (Config V), IsUpperSet A → MeasurableSet A → ∀ β₁ β₂ : ℝ≥0, β₁ ≤ β₂ →
      law (intensityProfile J β₁) A ≤ law (intensityProfile J β₂) A) ∧
    (Countable V →
      (∀ (x : V) (β : ℝ≥0), (β : ℝ≥0∞) < rootCriticalIntensity J x →
        law (intensityProfile J β) {ω | (cluster ω x).Infinite} = 0) ∧
      (∀ (x : V) (β : ℝ≥0), rootCriticalIntensity J x < β →
        0 < law (intensityProfile J β) {ω | (cluster ω x).Infinite}) ∧
      (∀ β : ℝ≥0, (β : ℝ≥0∞) < globalCriticalIntensity J →
        law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0) ∧
      (∀ β : ℝ≥0, globalCriticalIntensity J < β →
        0 < law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite})) :=
  ⟨law_intensityProfile_add J, fun _ hA hAm _ _ h => law_intensityProfile_mono hA hAm J h,
    fun _ => ⟨fun x _ h => law_cluster_infinite_eq_zero_of_lt_rootCriticalIntensity J x h,
      fun x _ h => law_cluster_infinite_pos_of_rootCriticalIntensity_lt J x h,
      fun _ h => law_exists_cluster_infinite_eq_zero_of_lt_globalCriticalIntensity J h,
      fun _ h => law_exists_cluster_infinite_pos_of_globalCriticalIntensity_lt J h⟩⟩

/-- Rescaling the kernel by a finite `c > 0` rescales the intensity and divides both
critical intensities by `c`; for `c = 0` both thresholds are infinite on countable `V`. -/
@[tag "IJOB"]
theorem kernel_rescaling_critical_intensity (J : Sym2 V → ℝ≥0) :
    (∀ c : ℝ≥0, 0 < c →
      (∀ β : ℝ≥0, law (intensityProfile (c • J) β) = law (intensityProfile J (c * β))) ∧
      (∀ x : V, rootCriticalIntensity (c • J) x = rootCriticalIntensity J x / c) ∧
      globalCriticalIntensity (c • J) = globalCriticalIntensity J / c) ∧
    (Countable V →
      (∀ x : V, rootCriticalIntensity ((0 : ℝ≥0) • J) x = ⊤) ∧
      globalCriticalIntensity ((0 : ℝ≥0) • J) = ⊤) :=
  ⟨fun c hc => ⟨fun β => congrArg law (intensityProfile_smul J c β),
      fun x => rootCriticalIntensity_smul J hc x, globalCriticalIntensity_smul J hc⟩,
    fun _ => ⟨fun x => rootCriticalIntensity_zero_smul J x,
      globalCriticalIntensity_zero_smul J⟩⟩

/-- On countable `V`: `τ(x,y) θ(x) ≤ θ(y)`; positivity of the percolation probability is
constant on components of the support graph; a connected support graph of `J` makes every
rooted critical intensity equal to the global one. -/
@[tag "IYVA"]
theorem root_independence_of_percolation [Countable V] :
    (∀ (q : Sym2 V → unitInterval) (x y : V),
      tau q x y * law q {ω | (cluster ω x).Infinite} ≤ law q {ω | (cluster ω y).Infinite}) ∧
    (∀ (q : Sym2 V → unitInterval) (x y : V),
      (SimpleGraph.fromEdgeSet {e | 0 < q e}).Reachable x y →
      (0 < law q {ω | (cluster ω x).Infinite} ↔ 0 < law q {ω | (cluster ω y).Infinite})) ∧
    (∀ J : Sym2 V → ℝ≥0, (SimpleGraph.fromEdgeSet {e | 0 < J e}).Preconnected →
      ∀ x : V, rootCriticalIntensity J x = globalCriticalIntensity J) :=
  ⟨tau_mul_law_cluster_infinite_le, fun q _ _ h => law_cluster_infinite_pos_iff_of_reachable q h,
    fun J hJ x => rootCriticalIntensity_eq_globalCriticalIntensity J hJ x⟩

/-- Under a transitive intensity family the rooted percolation probabilities, and hence the
rooted critical intensities, agree. -/
@[tag "XONW"]
theorem root_thresholds_eq_of_transitive [Countable V] (J : Sym2 V → ℝ≥0)
    (hT : ∀ x y : V, ∃ σ : V ≃ V, σ x = y ∧ ∀ e, J (Sym2.map σ e) = J e) :
    (∀ (β : ℝ≥0) (x y : V), law (intensityProfile J β) {ω | (cluster ω x).Infinite} =
      law (intensityProfile J β) {ω | (cluster ω y).Infinite}) ∧
    (∀ x y : V, rootCriticalIntensity J x = rootCriticalIntensity J y) :=
  ⟨law_cluster_infinite_eq_of_transitive J hT, rootCriticalIntensity_eq_of_transitive J hT⟩

end PercLib.Percolation.Bond
