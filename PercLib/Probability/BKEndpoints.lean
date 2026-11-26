/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from NearCritical/BKEndpoints.lean at
https://github.com/tomhutchcroft/near-critical-diffusivity/tree/c820fea91a7482c1755de0ec94ecb9f59ccfcacc
under Tom Hutchcroft's reuse permission recorded in `docs/DECISIONS.md`. The native source has
no licence header; no upstream Apache licence is asserted. Canonical Set law
replaces Boolean finite weights. The mixed deterministic-profile result is new
PercLib glue from prodBernoulli_indicator, not an endpoint extension claimed upstream.
-/
module

public import PercLib.Probability.DisjointOccurrence
public import PercLib.Probability.FiniteExpectation

/-! # Deterministic Bernoulli endpoints
All-one and all-zero laws are deterministic. More generally a prescribed set
of probability-one coordinates and probability-zero complement give a Dirac law.
The finite-event BK consequence needs no increasingness assumption.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace PercLib.Probability
variable {E : Type*}

open Classical in
/-- A deterministic zero/one profile gives the Dirac law at its open coordinates. -/
theorem prodBernoulli_deterministic (u : Set E) :
    prodBernoulli (fun e => if e ∈ u then 1 else 0) = Measure.dirac u := by
  rw [prodBernoulli_indicator]
  simp

/-- An a.e. strongly measurable function integrates against a Dirac measure to its value at
the atom. No measurable-singleton assumption is needed. -/
theorem integral_dirac_of_aestronglyMeasurable {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : α → F} {a : α}
    (hf : AEStronglyMeasurable f (Measure.dirac a)) :
    ∫ x, f x ∂Measure.dirac a = f a := by
  rw [integral_congr_ae hf.ae_eq_mk, integral_dirac' _ _ hf.stronglyMeasurable_mk]
  by_contra hne
  have h0 : Measure.dirac a {x | f x ≠ hf.mk f x} = 0 := hf.ae_eq_mk
  rw [Measure.dirac_apply_of_mem (show a ∈ {x | f x ≠ hf.mk f x} from Ne.symm hne)] at h0
  exact one_ne_zero h0

open Classical in
/-- Under a deterministic zero/one profile a measurable event has indicator probability. -/
theorem prodBernoulli_deterministic_apply (u : Set E) {A : Set (Set E)} (hA : MeasurableSet A) :
    prodBernoulli (fun e => if e ∈ u then 1 else 0) A = A.indicator 1 u := by
  rw [prodBernoulli_deterministic, Measure.dirac_apply' _ hA]

open Classical in
/-- Under a deterministic zero/one profile an integrable observable integrates to its value
at the set of open coordinates. -/
theorem integral_prodBernoulli_deterministic (u : Set E) {f : Set E → ℝ}
    (hf : Integrable f (prodBernoulli (fun e => if e ∈ u then 1 else 0))) :
    ∫ ω, f ω ∂prodBernoulli (fun e => if e ∈ u then 1 else 0) = f u := by
  rw [prodBernoulli_deterministic] at hf ⊢
  exact integral_dirac_of_aestronglyMeasurable hf.aestronglyMeasurable

/-- Homogeneous expectation at one evaluates at the all-open configuration. -/
theorem finiteExpectation_one [Fintype E] (f : Set E → ℝ) :
    finiteExpectation 1 f = f Set.univ := by
  change finiteExpectation ((1 : unitInterval) : ℝ) f = _
  rw [finiteExpectation_eq_integral, prodBernoulli_const]
  simp

/-- Homogeneous expectation at zero evaluates at the all-closed configuration. -/
theorem finiteExpectation_zero [Fintype E] (f : Set E → ℝ) :
    finiteExpectation 0 f = f ∅ := by
  change finiteExpectation ((0 : unitInterval) : ℝ) f = _
  rw [finiteExpectation_eq_integral, prodBernoulli_const]
  simp

open Classical in
/-- Arbitrary finite events under a deterministic profile have indicator probabilities. -/
theorem prodBernoulli_deterministic_real [Fintype E] (u : Set E) (A : Set (Set E)) :
    (prodBernoulli (fun e => if e ∈ u then 1 else 0)).real A = if u ∈ A then 1 else 0 := by
  rw [prodBernoulli_deterministic]
  by_cases h : u ∈ A <;>
    simp [measureReal_def, Measure.dirac_apply' _ (Set.toFinite A).measurableSet, indicator, h]

open Classical in
/-- New mixed zero/one specialization: deterministic BK for arbitrary finite events. -/
@[tag "E7HI"]
theorem bk_deterministic [Fintype E] (u : Set E) (A B : Set (Set E)) :
    (prodBernoulli (fun e => if e ∈ u then 1 else 0)).real (disjointOccurrence A B) ≤
      (prodBernoulli (fun e => if e ∈ u then 1 else 0)).real A *
      (prodBernoulli (fun e => if e ∈ u then 1 else 0)).real B := by
  simp only [prodBernoulli_deterministic_real]
  by_cases h : u ∈ disjointOccurrence A B
  · have hm := disjointOccurrence_subset_inter A B h
    simp [h, hm.1, hm.2]
  · by_cases hA : u ∈ A <;> by_cases hB : u ∈ B <;> simp [h, hA, hB]

/-- BK at the homogeneous all-one endpoint, without increasingness. -/
theorem bk_at_one [Fintype E] (A B : Set (Set E)) :
    (prodBernoulli (fun _ : E => 1)).real (disjointOccurrence A B) ≤
      (prodBernoulli (fun _ : E => 1)).real A * (prodBernoulli (fun _ : E => 1)).real B := by
  simpa using bk_deterministic (Set.univ : Set E) A B

/-- BK at the homogeneous all-zero endpoint, without increasingness. -/
theorem bk_at_zero [Fintype E] (A B : Set (Set E)) :
    (prodBernoulli (fun _ : E => 0)).real (disjointOccurrence A B) ≤
      (prodBernoulli (fun _ : E => 0)).real A * (prodBernoulli (fun _ : E => 0)).real B := by
  simpa using bk_deterministic (∅ : Set E) A B

-- Mixed endpoints on Bool, for events that need not be increasing.
example (A B : Set (Set Bool)) :
    (prodBernoulli (fun e : Bool => if e ∈ ({true} : Set Bool) then 1 else 0)).real
      (disjointOccurrence A B) ≤
    (prodBernoulli (fun e : Bool => if e ∈ ({true} : Set Bool) then 1 else 0)).real A *
    (prodBernoulli (fun e : Bool => if e ∈ ({true} : Set Bool) then 1 else 0)).real B :=
  by simpa using bk_deterministic {true} A B

example (f : Set Empty → ℝ) : finiteExpectation 1 f = f ∅ := by
  rw [finiteExpectation_one]
  congr 1
  exact Subsingleton.elim _ _

end PercLib.Probability
