/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs using mathlib (infinite product measures, unconditional products, the exponential
distribution). Reference: the clock construction of independent layers in T. Hutchcroft,
*Critical cluster volumes in hierarchical percolation*, arXiv:2211.05686.
-/
module

public import PercLib.Probability.ClosedProduct
public import PercLib.Probability.Characterization
public import PercLib.Probability.HarrisDecreasing
public import PercLib.Probability.TotalVariation
public import Mathlib.Probability.Distributions.Exponential

/-! # Countable superposition of Bernoulli coordinates

Let `ξ ~ prodBernoulli p` on a countable index set `ι`, let `g : ι → κ` and `S ⊆ ι`. The
configuration `g '' (ξ ∩ S)` on `κ` opens `k` when some coordinate of `S` over `k` is open.
Its law is again a product Bernoulli law, whose closed probability at `k` is the product of the
closed probabilities over the fibre `{j ∈ S | g j = k}`. Disjoint selections `S₁`, `S₂` give
independent superpositions. Exponential clocks realise product Bernoulli laws.

## Main results

* `prodBernoulli_map_image_inter`: the superposition law, with closed probabilities as
  countable products over fibres.
* `prodBernoulli_map_image_inter_of_hasSum`: the same for exponential profiles
  `p = 1 - exp(-β w)`, with the fibre sums of `w` as intensities.
* `prodBernoulli_map_image_inter_prod`: disjoint selections are independent.
* `infinitePi_expMeasure_map_setOf_le`: the open set `{i | T i ≤ t i}` of independent rate-one
  exponential clocks has the product law with open probabilities `1 - exp(-t i)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PercLib.Probability

variable {ι κ : Type*}

/-- Superposing the coordinates of `S` along `g` is measurable for countable `ι`. -/
theorem measurable_image_inter [Countable ι] (g : ι → κ) (S : Set ι) :
    Measurable (fun ξ : Set ι => g '' (ξ ∩ S)) := by
  refine measurable_set_iff.mpr fun k => ?_
  have : (fun ξ : Set ι => k ∈ g '' (ξ ∩ S)) =
      fun ξ => ∃ j : {j | j ∈ S ∧ g j = k}, (j : ι) ∈ ξ := by
    funext ξ
    apply propext
    constructor
    · rintro ⟨j, ⟨hj, hS⟩, rfl⟩
      exact ⟨⟨j, hS, rfl⟩, hj⟩
    · rintro ⟨⟨j, hS, hg⟩, hj⟩
      exact ⟨j, ⟨hj, hS⟩, hg⟩
  rw [this]
  exact Measurable.exists fun j => measurable_set_mem _

/-- **Countable superposition.** The superposition `g '' (ξ ∩ S)` of `ξ ~ prodBernoulli p` is
Bernoulli with closed probability at `k` the product of the closed probabilities over the
fibre `{j ∈ S | g j = k}`. -/
theorem prodBernoulli_map_image_inter [Countable ι] (p : ι → unitInterval) (g : ι → κ)
    (S : Set ι) (r : κ → unitInterval)
    (hr : ∀ k, (unitInterval.toNNReal (unitInterval.symm (r k)) : ℝ≥0∞) =
      ∏' j : {j | j ∈ S ∧ g j = k}, (unitInterval.toNNReal (unitInterval.symm (p j)) : ℝ≥0∞)) :
    (prodBernoulli p).map (fun ξ => g '' (ξ ∩ S)) = prodBernoulli r := by
  classical
  have hm := measurable_image_inter g S
  have hc : (prodBernoulli p).map (fun ξ => (g '' (ξ ∩ S))ᶜ) =
      prodBernoulli (fun k => unitInterval.symm (r k)) := by
    rw [map_prodBernoulli_eq_iff p
      (show Measurable (fun ξ : Set ι => (g '' (ξ ∩ S))ᶜ) from measurable_compl.comp hm)]
    intro F
    have hset : (fun ξ => (g '' (ξ ∩ S))ᶜ) ⁻¹' {ω | (F : Set κ) ⊆ ω} =
        {ξ | ∀ j : {j | j ∈ S ∧ g j ∈ F}, (j : ι) ∉ ξ} := by
      ext ξ
      simp only [mem_preimage, mem_ofPred_eq, subset_def, mem_compl_iff, mem_image, mem_inter_iff,
        not_exists, not_and, Subtype.forall, Finset.mem_coe]
      constructor
      · intro h j hS hF
        exact h _ hS.2 j ⟨hF, hS.1⟩ rfl
      · rintro h k hk j ⟨hj, hS⟩ rfl
        exact h j ⟨hS, hk⟩ hj
    rw [hset]
    clear hset
    induction F using Finset.induction_on with
    | empty => simp
    | insert k F hk ih =>
      set T₁ : Set ι := {j | j ∈ S ∧ g j = k}
      set T₂ : Set ι := {j | j ∈ S ∧ g j ∈ F}
      have hd : Disjoint T₁ T₂ := Set.disjoint_left.mpr fun j hj hj' => hk (hj.2 ▸ hj'.2)
      have hA : MeasurableSet {η : Set T₁ | ∀ i : T₁, i ∉ η} := by
        simpa only [Set.ofPred_forall, Set.compl_ofPred] using
          MeasurableSet.iInter (fun i : T₁ => (measurableSet_mem i).compl)
      have hB : MeasurableSet {η : Set T₂ | ∀ i : T₂, i ∉ η} := by
        simpa only [Set.ofPred_forall, Set.compl_ofPred] using
          MeasurableSet.iInter (fun i : T₂ => (measurableSet_mem i).compl)
      have hfac := prodBernoulli_block_inter p T₁ T₂ hd _ _ hA hB
      have he : {ξ : Set ι | ∀ j : {j | j ∈ S ∧ g j ∈ (insert k F : Finset κ)}, (j : ι) ∉ ξ} =
          {ξ | {i : T₁ | (i : ι) ∈ ξ} ∈ {η : Set T₁ | ∀ i : T₁, i ∉ η} ∧
            {i : T₂ | (i : ι) ∈ ξ} ∈ {η : Set T₂ | ∀ i : T₂, i ∉ η}} := by
        ext ξ
        simp only [Finset.mem_insert, Subtype.forall, mem_ofPred_eq, T₁, T₂]
        constructor
        · intro h
          exact ⟨fun j hj => h j ⟨hj.1, Or.inl hj.2⟩, fun j hj => h j ⟨hj.1, Or.inr hj.2⟩⟩
        · rintro ⟨h₁, h₂⟩ j ⟨hj, hj' | hj'⟩
          · exact h₁ j ⟨hj, hj'⟩
          · exact h₂ j ⟨hj, hj'⟩
      have h₁ : {ξ : Set ι | {i : T₁ | (i : ι) ∈ ξ} ∈ {η : Set T₁ | ∀ i : T₁, i ∉ η}} =
          {ξ | ∀ j : T₁, (j : ι) ∉ ξ} := by
        ext ξ
        simp
      have h₂ : {ξ : Set ι | {i : T₂ | (i : ι) ∈ ξ} ∈ {η : Set T₂ | ∀ i : T₂, i ∉ η}} =
          {ξ | ∀ j : T₂, (j : ι) ∉ ξ} := by
        ext ξ
        simp
      rw [he, hfac, h₁, h₂, ih, Finset.prod_insert hk,
        prodBernoulli_forall_notMem p (Subtype.val : T₁ → ι) Subtype.val_injective, hr k]
  have hcc : (fun ξ : Set ι => g '' (ξ ∩ S)) =
      compl ∘ fun ξ : Set ι => (g '' (ξ ∩ S))ᶜ := by
    funext ξ
    simp
  rw [hcc, ← Measure.map_map measurable_compl
    (show Measurable (fun ξ : Set ι => (g '' (ξ ∩ S))ᶜ) from measurable_compl.comp hm), hc,
    prodBernoulli_map_compl]
  simp

/-- **Exponential superposition.** If `p j = 1 - exp(-β w j)` and `W k` is the sum of `w` over
the fibre `{j ∈ S | g j = k}`, the superposition has the profile `1 - exp(-β W)`. -/
theorem prodBernoulli_map_image_inter_of_hasSum [Countable ι] (p : ι → unitInterval)
    (g : ι → κ) (S : Set ι) (r : κ → unitInterval) (β : ℝ≥0) (w : ι → ℝ≥0) (W : κ → ℝ≥0)
    (hp : ∀ j, (p j : ℝ) = 1 - Real.exp (-(β : ℝ) * w j))
    (hr : ∀ k, (r k : ℝ) = 1 - Real.exp (-(β : ℝ) * W k))
    (hW : ∀ k, HasSum (fun j : {j | j ∈ S ∧ g j = k} => (w j : ℝ)) (W k)) :
    (prodBernoulli p).map (fun ξ => g '' (ξ ∩ S)) = prodBernoulli r := by
  refine prodBernoulli_map_image_inter p g S r fun k => ?_
  have hsymm (x : unitInterval) (a : ℝ) (hx : (x : ℝ) = 1 - Real.exp a) :
      (unitInterval.toNNReal (unitInterval.symm x) : ℝ≥0∞) = ENNReal.ofReal (Real.exp a) := by
    rw [coe_toNNReal_eq_ofReal, unitInterval.coe_symm_eq, hx, sub_sub_cancel]
  rw [hsymm _ _ (hr k)]
  simp_rw [hsymm _ _ (hp _)]
  have ht := (Real.continuous_exp.tendsto _).comp ((hW k).mul_left (-(β : ℝ)))
  have ht' := (ENNReal.continuous_ofReal.tendsto _).comp ht
  have hP : HasProd (fun j : {j | j ∈ S ∧ g j = k} =>
      ENNReal.ofReal (Real.exp (-(β : ℝ) * w j))) (ENNReal.ofReal (Real.exp (-(β : ℝ) * W k))) := by
    unfold HasProd
    convert ht' using 1
    funext F
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le), ← Real.exp_sum]
    simp [Function.comp]
  exact hP.tprod_eq.symm

/-- **Independent selections.** Superpositions of disjoint selections are independent: their
joint law is the product of their laws. -/
theorem prodBernoulli_map_image_inter_prod [Countable ι] (p : ι → unitInterval) (g : ι → κ)
    {S₁ S₂ : Set ι} (hS : Disjoint S₁ S₂) :
    (prodBernoulli p).map (fun ξ => (g '' (ξ ∩ S₁), g '' (ξ ∩ S₂))) =
      ((prodBernoulli p).map (fun ξ => g '' (ξ ∩ S₁))).prod
        ((prodBernoulli p).map (fun ξ => g '' (ξ ∩ S₂))) := by
  have hval (S : Set ι) (ξ : Set ι) :
      g '' (ξ ∩ S) = (g ∘ Subtype.val) '' ({i : S | (i : ι) ∈ ξ} ∩ univ) := by
    rw [inter_univ, image_comp]
    congr 1
    ext j
    simp [and_comm]
  have hind := prodBernoulli_indepFun_block_observables p S₁ S₂ hS
    (fun η : Set S₁ => (g ∘ Subtype.val) '' (η ∩ univ))
    (fun η : Set S₂ => (g ∘ Subtype.val) '' (η ∩ univ))
    (measurable_image_inter _ _) (measurable_image_inter _ _)
  simp only [← hval] at hind
  exact (indepFun_iff_map_prod_eq_prod_map_map (measurable_image_inter g S₁).aemeasurable
    (measurable_image_inter g S₂).aemeasurable).mp hind

/-- Reading off which clocks of `C` ring by their times is measurable. -/
theorem measurable_setOf_mem_and_le (C : Set ι) (t : ι → ℝ) :
    Measurable (fun (T : ι → ℝ) => {i | i ∈ C ∧ T i ≤ t i}) := by
  refine measurable_set_iff.mpr fun i => ?_
  change Measurable fun T : ι → ℝ => i ∈ C ∧ T i ≤ t i
  by_cases hi : i ∈ C
  · simp only [hi, true_and]
    exact measurableSet_setOfPred.mp (measurableSet_le (measurable_pi_apply i) measurable_const)
  · simp only [hi, false_and]
    exact measurable_const

open Classical in
/-- **Exponential clocks.** For independent rate-one exponential clocks `T i`, a set `C` of
indices and times `t i`, the set `{i ∈ C | T i ≤ t i}` has the product Bernoulli law with open
probability `1 - exp(-t i)` at `i ∈ C` with `t i ≥ 0`, and `0` otherwise. -/
theorem infinitePi_expMeasure_map_setOf_le (C : Set ι) (t : ι → ℝ) (q : ι → unitInterval)
    (hq : ∀ i, (q i : ℝ) = if i ∈ C ∧ 0 ≤ t i then 1 - Real.exp (-t i) else 0) :
    (Measure.infinitePi fun _ : ι => expMeasure 1).map (fun T => {i | i ∈ C ∧ T i ≤ t i}) =
      prodBernoulli q := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hm := measurable_setOf_mem_and_le C t
  have : IsProbabilityMeasure
      ((Measure.infinitePi fun _ : ι => expMeasure 1).map
        (fun T => {i | i ∈ C ∧ T i ≤ t i})) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine eq_prodBernoulli_of_subset _ q fun F => ?_
  rw [Measure.map_apply hm (measurableSet_setOf_finset_coe_subset F)]
  have hset : (fun (T : ι → ℝ) => {i | i ∈ C ∧ T i ≤ t i}) ⁻¹' {ω | (F : Set ι) ⊆ ω} =
      Set.pi (F : Set ι) (fun i => {x | i ∈ C ∧ x ≤ t i}) := by
    ext T
    simp [subset_def, Set.mem_pi]
  have hmeas : ∀ i ∈ F, MeasurableSet {x : ℝ | i ∈ C ∧ x ≤ t i} := fun i _ => by
    by_cases hi : i ∈ C
    · have hI : {x : ℝ | i ∈ C ∧ x ≤ t i} = Iic (t i) := by ext x; simp [hi]
      rw [hI]
      exact measurableSet_Iic
    · simp [hi]
  rw [hset, Measure.infinitePi_pi (μ := fun _ : ι => expMeasure 1) hmeas]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [coe_toNNReal_eq_ofReal, hq]
  by_cases hi : i ∈ C
  · have hI : {x : ℝ | i ∈ C ∧ x ≤ t i} = Iic (t i) := by ext x; simp [hi]
    rw [hI, ← ofReal_cdf, cdf_expMeasure_eq one_pos, one_mul]
    by_cases ht : 0 ≤ t i <;> simp [hi, ht]
  · simp [hi]

end PercLib.Probability
