/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs using mathlib's product and Bernoulli measures, at the pinned revision
56a005855ea17e0b0958f73ec801ae140b0a1679. No upstream coupling theorem is copied.
The coordinate construction uses three states: both open, only the upper open,
and both closed. Thus it never assigns mass to an order-violating state.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Data.Sym.Sym2
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Monotone coupling of product Bernoulli laws

Ordered profiles admit a coupling of their product laws with ordered configurations, so increasing
events and nonnegative increasing observables are monotone in the profile.

## Main results

* `exists_bernoulli_order_coupling`
* `exists_prodBernoulli_monotone_coupling`
* `prodBernoulli_mono_event`
* `lintegral_prodBernoulli_mono`
* `exists_bond_monotone_coupling`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PercLib.Probability

/-- A three-state coordinate coupling of two ordered Bernoulli parameters. -/
theorem exists_bernoulli_order_coupling (p q : unitInterval) (hpq : p ≤ q) :
    ∃ ν : Measure (Fin 3), IsProbabilityMeasure ν ∧
      ν.map (fun j => j = 0) = bernoulliMeasure True False p ∧
      ν.map (fun j => j ≠ 2) = bernoulliMeasure True False q := by
  let a := unitInterval.toNNReal p
  let b := unitInterval.toNNReal q
  have hab : a ≤ b := hpq
  have hb : b ≤ 1 := q.2.2
  let ν : Measure (Fin 3) := a • Measure.dirac 0 +
    (b - a) • Measure.dirac 1 + (1 - b) • Measure.dirac 2
  have hp : unitInterval.toNNReal (unitInterval.symm p) = 1 - a := by
    ext
    simp [a, unitInterval.symm, NNReal.coe_sub (show a ≤ 1 from p.2.2)]
  have hq : unitInterval.toNNReal (unitInterval.symm q) = 1 - b := by
    ext
    simp [b, unitInterval.symm, NNReal.coe_sub hb]
  have hdiff : b - a + (1 - b) = 1 - a := by
    exact (add_comm _ _).trans (tsub_add_tsub_cancel hb hab)
  have hm₁ : Measurable (fun j : Fin 3 => j = 0) := by fun_prop
  have hm₂ : Measurable (fun j : Fin 3 => j ≠ 2) := by fun_prop
  have hmap₁ : ν.map (fun j => j = 0) = bernoulliMeasure True False p := by
    simp only [ν, Measure.map_add _ _ hm₁, Measure.map_smul _ hm₁.aemeasurable,
      Measure.map_dirac' hm₁]
    simp only [show ¬ (1 : Fin 3) = 0 by decide,
      show ¬ (2 : Fin 3) = 0 by decide, bernoulliMeasure_def, hp]
    rw [add_assoc, ← add_smul, hdiff]
  have hmap₂ : ν.map (fun j => j ≠ 2) = bernoulliMeasure True False q := by
    simp only [ν, Measure.map_add _ _ hm₂, Measure.map_smul _ hm₂.aemeasurable,
      Measure.map_dirac' hm₂]
    norm_num only [ne_eq, Fin.reduceEq, not_true_eq_false, not_false_eq_true,
      bernoulliMeasure_def, hq]
    rw [← add_smul, add_tsub_cancel_of_le hab]
  refine ⟨ν, ?_, hmap₁, hmap₂⟩
  apply (Measure.isProbabilityMeasure_map_iff hm₁.aemeasurable).mp
  rw [hmap₁]
  infer_instance

variable {ι : Type*} [Countable ι]

/-- Ordered profiles admit an ordered coupling of their canonical set laws. -/
theorem exists_prodBernoulli_monotone_coupling (p q : ι → unitInterval) (hpq : p ≤ q) :
    ∃ γ : Measure (Set ι × Set ι), IsProbabilityMeasure γ ∧
      γ.map Prod.fst = prodBernoulli p ∧ γ.map Prod.snd = prodBernoulli q ∧
      ∀ᵐ z ∂γ, z.1 ⊆ z.2 := by
  choose ν hν hν₁ hν₂ using fun i => exists_bernoulli_order_coupling (p i) (q i) (hpq i)
  let : ∀ i, IsProbabilityMeasure (ν i) := hν
  let μ := Measure.infinitePi ν
  let f : (ι → Fin 3) → Set ι × Set ι := fun x => ({i | x i = 0}, {i | x i ≠ 2})
  have hf : Measurable f := by fun_prop
  have h₁ : (μ.map f).map Prod.fst = prodBernoulli p := by
    rw [Measure.map_map measurable_fst hf, prodBernoulli_eq_map]
    have hpi := Measure.infinitePi_map_pi (μ := ν) (f := fun _ j => j = 0)
      (fun _ => by fun_prop)
    rw [show (fun i => (ν i).map (fun j => j = 0)) =
      (fun i => bernoulliMeasure True False (p i)) from funext hν₁] at hpi
    rw [← hpi, Measure.map_map measurable_setOfPred (by fun_prop)]
    rfl
  have h₂ : (μ.map f).map Prod.snd = prodBernoulli q := by
    rw [Measure.map_map measurable_snd hf, prodBernoulli_eq_map]
    have hpi := Measure.infinitePi_map_pi (μ := ν) (f := fun _ j => j ≠ 2)
      (fun _ => by fun_prop)
    rw [show (fun i => (ν i).map (fun j => j ≠ 2)) =
      (fun i => bernoulliMeasure True False (q i)) from funext hν₂] at hpi
    rw [← hpi, Measure.map_map measurable_setOfPred (by fun_prop)]
    rfl
  refine ⟨μ.map f, inferInstance, h₁, h₂, ?_⟩
  have hm : MeasurableSet {z : Set ι × Set ι | z.1 ⊆ z.2} := by
    change MeasurableSet {z : Set ι × Set ι | ∀ i, i ∈ z.1 → i ∈ z.2}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    convert ((measurableSet_mem i).preimage measurable_fst).compl.union
      ((measurableSet_mem i).preimage measurable_snd) using 1
    ext z
    simp [imp_iff_not_or]
  rw [ae_map_iff hf.aemeasurable hm]
  exact Filter.Eventually.of_forall fun x i hi => by
    change x i ≠ 2
    change x i = 0 at hi
    simp [hi]

/-- Every measurable increasing event is more likely under the larger profile. -/
theorem prodBernoulli_mono_event (p q : ι → unitInterval) (hpq : p ≤ q)
    {A : Set (Set ι)} (hA : MeasurableSet A) (hup : IsUpperSet A) :
    prodBernoulli p A ≤ prodBernoulli q A := by
  obtain ⟨γ, _, h₁, h₂, hord⟩ := exists_prodBernoulli_monotone_coupling p q hpq
  rw [← h₁, ← h₂, Measure.map_apply measurable_fst hA,
    Measure.map_apply measurable_snd hA]
  apply measure_mono_ae
  filter_upwards [hord] with z hz
  exact fun ha => hup hz ha

/-- The comparison includes nonnegative observables with infinite expectation. -/
theorem lintegral_prodBernoulli_mono (p q : ι → unitInterval) (hpq : p ≤ q)
    {F : Set ι → ℝ≥0∞} (hF : Measurable F) (hmono : Monotone F) :
    (∫⁻ ω, F ω ∂prodBernoulli p) ≤ ∫⁻ ω, F ω ∂prodBernoulli q := by
  obtain ⟨γ, _, h₁, h₂, hord⟩ := exists_prodBernoulli_monotone_coupling p q hpq
  rw [← h₁, ← h₂, lintegral_map hF measurable_fst, lintegral_map hF measurable_snd]
  apply lintegral_mono_ae
  filter_upwards [hord] with z hz using hmono hz

/-- The bond specialization retains every unordered pair, including diagonals. -/
theorem exists_bond_monotone_coupling {V : Type*} [Countable V]
    (p q : Sym2 V → unitInterval) (hpq : p ≤ q) :
    ∃ γ : Measure (Set (Sym2 V) × Set (Sym2 V)), IsProbabilityMeasure γ ∧
      γ.map Prod.fst = prodBernoulli p ∧ γ.map Prod.snd = prodBernoulli q ∧
      ∀ᵐ z ∂γ, z.1 ⊆ z.2 :=
  exists_prodBernoulli_monotone_coupling p q hpq

-- The extreme parameters are valid; the construction does not divide by p or 1-p.
example : ∃ γ : Measure (Set Bool × Set Bool), IsProbabilityMeasure γ ∧
    γ.map Prod.fst = prodBernoulli (fun _ => 0) ∧
    γ.map Prod.snd = prodBernoulli (fun _ => 1) ∧ ∀ᵐ z ∂γ, z.1 ⊆ z.2 :=
  exists_prodBernoulli_monotone_coupling _ _ (fun _ => bot_le)

-- Equal profiles are allowed, even for infinitely many coordinates.
example (p : ℕ → unitInterval) :
    ∃ γ : Measure (Set ℕ × Set ℕ), IsProbabilityMeasure γ ∧
      γ.map Prod.fst = prodBernoulli p ∧ γ.map Prod.snd = prodBernoulli p ∧
      ∀ᵐ z ∂γ, z.1 ⊆ z.2 :=
  exists_prodBernoulli_monotone_coupling p p le_rfl

-- A genuine increasing event: one specified coordinate is open.
example (p q : ι → unitInterval) (hpq : p ≤ q) (i : ι) :
    prodBernoulli p {ω | i ∈ ω} ≤ prodBernoulli q {ω | i ∈ ω} :=
  prodBernoulli_mono_event p q hpq (measurableSet_mem i) (fun _ _ h hi => h hi)

section Uniform

variable {E β : Type*}

/-- Thresholding a uniform variable at `p` gives a Bernoulli variable with parameter `p`. -/
theorem volume_map_le_eq_bernoulliMeasure (p : unitInterval) :
    (volume : Measure unitInterval).map (· ≤ p) = bernoulliMeasure True False p := by
  have hm : Measurable (· ≤ p : unitInterval → Prop) := measurableSet_Iic.mem
  refine eq_bernoulliMeasure (fun s hs h₁ h₂ => ?_) (fun s hs h₁ h₂ => ?_)
    (fun s hs h₁ h₂ => ?_) (fun s hs h₁ h₂ => ?_) <;> rw [Measure.map_apply hm hs]
  · have : (· ≤ p) ⁻¹' s = Set.univ := by
      ext u; by_cases h : u ≤ p <;> simp [h, h₁, h₂]
    simp [this]
  · have : (· ≤ p) ⁻¹' s = Set.Iic p := by
      ext u; by_cases h : u ≤ p <;> simp [h, h₁, h₂]
    rw [this, unitInterval.volume_Iic, ← ENNReal.ofReal_coe_nnreal]
    simp
  · have : (· ≤ p) ⁻¹' s = Set.Ioi p := by
      ext u
      rcases le_or_gt u p with h | h
      · simp [h, h.not_gt, h₁]
      · simp [h, h.not_ge, h₂]
    rw [this, unitInterval.volume_Ioi, ← ENNReal.ofReal_coe_nnreal]
    simp [unitInterval.coe_symm_eq]
  · have : (· ≤ p) ⁻¹' s = ∅ := by
      ext u; by_cases h : u ≤ p <;> simp [h, h₁, h₂]
    simp [this]

/-- Independent uniform variables thresholded at a profile `q` have the product law of `q`. -/
theorem infinitePi_volume_map_setOf_le_eq_prodBernoulli (q : E → unitInterval) :
    (Measure.infinitePi fun _ : E => (volume : Measure unitInterval)).map
      (fun U => {e | U e ≤ q e}) = prodBernoulli q := by
  rw [prodBernoulli_eq_map]
  have hpi := Measure.infinitePi_map_pi (μ := fun _ : E => (volume : Measure unitInterval))
    (f := fun e (u : unitInterval) => u ≤ q e) (fun e => measurableSet_Iic.mem)
  rw [show (fun e => (volume : Measure unitInterval).map (· ≤ q e)) =
    (fun e => bernoulliMeasure True False (q e)) from
      funext fun e => volume_map_le_eq_bernoulliMeasure (q e)] at hpi
  rw [← hpi, Measure.map_map measurable_setOfPred (by fun_prop)]
  rfl

/-- The threshold configurations of one family of variables increase with the profile. -/
theorem monotone_setOf_le_apply [Preorder β] (U : E → β) :
    Monotone fun q : E → β => {e | U e ≤ q e} :=
  fun _ _ hq _ he => le_trans he (hq _)

end Uniform

end PercLib.Probability
