/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied and no definition is added.
Mathematical content: the chain rule and the data processing inequality for the
Kullback-Leibler divergence of laws on countable sets; standard arguments, reduced to mathlib's
`InformationTheory.klDiv_compProd_eq_add` and `InformationTheory.klDiv_map_le`.
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

/-!
# Relative entropy of laws on countable sets

Relative entropy is mathlib's `InformationTheory.klDiv`. For laws on a countable set with
measurable singletons it is the sum `∑ μ(s) log (μ(s)/ν(s))` with the usual conventions.

For laws `μ, ν` on a product `X × Y` of countable sets, the joint relative entropy splits into
the relative entropy of the first marginals plus the `μ.fst`-average of the relative entropies
of the elementary conditional laws `μ(· | X = x)`, `ν(· | X = x)` of the second coordinate.

## Main results

* `PercLib.Probability.klDiv_compProd_right_eq_lintegral`: over a countable base,
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ`.
* `PercLib.Probability.klDiv_compProd_right_eq_tsum`: the same as a sum over points.
* `PercLib.Probability.exists_isMarkovKernel_compProd_eq_cond`: a law on a product of
  countable sets is its first marginal composed with a Markov kernel given by the elementary
  conditional laws.
* `PercLib.Probability.klDiv_eq_klDiv_fst_add_tsum_cond`: the chain rule.
* `PercLib.Probability.klDiv_eq_top_of_not_absolutelyContinuous_fst`: infinite joint
  relative entropy when the first marginals are not absolutely continuous.
* `PercLib.Probability.klDiv_map_le_of_countable`: data processing for an arbitrary map on a
  countable set.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory InformationTheory
open scoped ENNReal

namespace PercLib.Probability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Over a countable base with measurable singletons, the relative entropy of two
composition-products with the same first law is the average of the relative entropies of the
kernels. -/
theorem klDiv_compProd_right_eq_lintegral [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (κ η : Kernel X Y) [IsMarkovKernel κ]
    [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  by_cases hac : μ ⊗ₘ κ ≪ μ ⊗ₘ η
  · have hae := Measure.absolutelyContinuous_compProd_right_iff.mp hac
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    calc ∫⁻ p, ENNReal.ofReal (klFun ((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ η)
        = ∫⁻ p, ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal) ∂(μ ⊗ₘ η) := by
          refine lintegral_congr_ae ?_
          filter_upwards [rnDeriv_measure_compProd_right μ κ η] with p hp
          rw [hp]
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (klFun (κ.rnDeriv η x y).toReal) ∂(η x) ∂μ := by
          rw [Measure.lintegral_compProd]
          exact ((measurable_klFun.comp
            (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal)
      _ = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [klDiv_eq_lintegral_klFun_of_ac hx]
          refine lintegral_congr_ae ?_
          filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := x)] with y hy
          rw [hy]
  · rw [klDiv_of_not_ac hac]
    rw [Measure.absolutelyContinuous_compProd_right_iff, ae_iff_of_countable] at hac
    push Not at hac
    obtain ⟨x, hx0, hx⟩ := hac
    rw [lintegral_countable']
    refine (top_unique ?_).symm
    calc (∞ : ℝ≥0∞) = klDiv (κ x) (η x) * μ {x} := by
          rw [klDiv_of_not_ac hx, ENNReal.top_mul hx0]
      _ ≤ ∑' x, klDiv (κ x) (η x) * μ {x} :=
        ENNReal.le_tsum (f := fun x => klDiv (κ x) (η x) * μ {x}) x

/-- `klDiv_compProd_right_eq_lintegral` as a sum over the points of the countable base. -/
theorem klDiv_compProd_right_eq_tsum [Countable X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (κ η : Kernel X Y) [IsMarkovKernel κ]
    [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∑' x, μ {x} * klDiv (κ x) (η x) := by
  rw [klDiv_compProd_right_eq_lintegral, lintegral_countable']
  exact tsum_congr fun x => mul_comm _ _

/-- A probability law on a product of countable sets with measurable singletons is its first
marginal composed with a Markov kernel, which at every atom of the marginal is the elementary
conditional law of the second coordinate. -/
theorem exists_isMarkovKernel_compProd_eq_cond [Countable X] [Countable Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] :
    ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ ∧
      ∀ x, μ.fst {x} ≠ 0 → κ x = (μ[|Prod.fst ⁻¹' {x}]).map Prod.snd := by
  classical
  obtain ⟨⟨_, y₀⟩⟩ : Nonempty (X × Y) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : μ univ = 0 := by simp [Set.univ_eq_empty_iff.mpr h]
    simp at h0
  let f : X → Measure Y := fun x =>
    if μ.fst {x} = 0 then Measure.dirac y₀ else (μ[|Prod.fst ⁻¹' {x}]).map Prod.snd
  have hf : ∀ x, IsProbabilityMeasure (f x) := by
    intro x
    by_cases hx : μ.fst {x} = 0
    · simp only [f, hx, ite_true]
      infer_instance
    · simp only [f, hx, ite_false]
      rw [Measure.fst_apply (measurableSet_singleton x)] at hx
      have := cond_isProbabilityMeasure (μ := μ) hx
      infer_instance
  let κ : Kernel X Y := Kernel.ofFunOfCountable f
  have hκ : ∀ x, κ x = f x := fun x => rfl
  have : IsMarkovKernel κ := ⟨fun x => by rw [hκ]; exact hf x⟩
  refine ⟨κ, inferInstance, ?_, fun x hx => by rw [hκ]; simp [f, hx]⟩
  refine Measure.ext_iff_singleton.mpr fun p => ?_
  obtain ⟨x, y⟩ := p
  rw [← Set.singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton x) (measurableSet_singleton y),
    lintegral_singleton, hκ]
  have hsub : ({x} ×ˢ {y} : Set (X × Y)) = Prod.fst ⁻¹' {x} ∩ Prod.snd ⁻¹' {y} := by
    ext ⟨a, b⟩
    simp
  by_cases hx : μ.fst {x} = 0
  · rw [hx, mul_zero]
    rw [Measure.fst_apply (measurableSet_singleton x)] at hx
    exact (measure_mono_null (hsub ▸ Set.inter_subset_left) hx).symm
  · simp only [f, hx, ite_false]
    rw [Measure.fst_apply (measurableSet_singleton x)] at hx ⊢
    rw [Measure.map_apply measurable_snd (measurableSet_singleton y),
      cond_apply (measurable_fst (measurableSet_singleton x)), ← hsub, mul_comm, ← mul_assoc,
      ENNReal.mul_inv_cancel hx (measure_ne_top _ _), one_mul]

/-- **Chain rule** for the relative entropy of laws on a product of countable sets: if the first
marginals are absolutely continuous, the joint relative entropy is the relative entropy of the
first marginals plus the average, over the atoms of `μ.fst`, of the relative entropies of the
elementary conditional laws of the second coordinate. -/
theorem klDiv_eq_klDiv_fst_add_tsum_cond [Countable X] [Countable Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ ν : Measure (X × Y)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ.fst ≪ ν.fst) :
    klDiv μ ν = klDiv μ.fst ν.fst + ∑' x : {x : X // 0 < μ.fst {x}}, μ.fst {(x : X)} *
      klDiv ((μ[|Prod.fst ⁻¹' {(x : X)}]).map Prod.snd)
        ((ν[|Prod.fst ⁻¹' {(x : X)}]).map Prod.snd) := by
  obtain ⟨κ, hκm, hμ, hκ⟩ := exists_isMarkovKernel_compProd_eq_cond μ
  obtain ⟨η, hηm, hν, hη⟩ := exists_isMarkovKernel_compProd_eq_cond ν
  have hsupp : Function.support (fun x => μ.fst {x} * klDiv (κ x) (η x)) ⊆
      {x | 0 < μ.fst {x}} := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    change 0 < μ.fst {x}
    exact pos_iff_ne_zero.mpr fun h0 => hx (by simp [h0])
  calc klDiv μ ν = klDiv (μ.fst ⊗ₘ κ) (ν.fst ⊗ₘ η) := by rw [hμ, hν]
    _ = klDiv μ.fst ν.fst + ∑' x, μ.fst {x} * klDiv (κ x) (η x) := by
      rw [klDiv_compProd_eq_add, klDiv_compProd_right_eq_tsum]
    _ = _ := by
      rw [← tsum_subtype_eq_of_support_subset hsupp]
      congr 1
      refine tsum_congr fun x => ?_
      have hx : μ.fst {(x : X)} ≠ 0 := (show 0 < μ.fst {(x : X)} from x.2).ne'
      rw [hκ _ hx, hη _ fun h0 => hx (h h0)]

/-- If the images of `μ` and `ν` under a measurable map are not absolutely continuous, the
relative entropy of `μ` and `ν` is infinite. -/
theorem klDiv_eq_top_of_not_absolutelyContinuous_map {Z W : Type*} [MeasurableSpace Z]
    [MeasurableSpace W] {μ ν : Measure Z} {g : Z → W} (hg : Measurable g)
    (h : ¬ μ.map g ≪ ν.map g) : klDiv μ ν = ∞ :=
  klDiv_of_not_ac fun hμν => h (hμν.map hg)

/-- If the first marginals are not absolutely continuous, the joint relative entropy is
infinite. -/
theorem klDiv_eq_top_of_not_absolutelyContinuous_fst {μ ν : Measure (X × Y)}
    (h : ¬ μ.fst ≪ ν.fst) : klDiv μ ν = ∞ :=
  klDiv_eq_top_of_not_absolutelyContinuous_map measurable_fst h

/-- **Data processing** for an arbitrary map on a countable set with measurable singletons. -/
theorem klDiv_map_le_of_countable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [Countable S] [MeasurableSingletonClass S] (μ ν : Measure S) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (g : S → T) : klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν :=
  klDiv_map_le μ ν (measurable_of_countable g)

end PercLib.Probability
