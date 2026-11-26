/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs using mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 (product measures, infinite
products, and summability of logarithms). The closed-product identity and the positivity
criterion were first proved in `PercLib/Models/LongRange/CutPoints.lean` and moved here.
-/
module

public import PercLib.Probability.ProdBernoulliIndependence
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Countable closed products

For a product Bernoulli law `prodBernoulli p` on `Set ι` and a countable, injectively indexed
family of coordinates `f : α → ι`, the probability that every coordinate of the family is closed
is the infinite product of the closed probabilities `1 - p (f a)`. That product is positive
exactly when no factor vanishes and the open probabilities are summable.

## Main results

* `prodBernoulli_forall_notMem`: `P(∀ a, f a ∉ ω) = ∏' a, (1 - p (f a))`.
* `tprod_symm_pos_iff`: `0 < ∏' a, (1 - p a) ↔ (∀ a, p a < 1) ∧ Summable p`.
* `prodBernoulli_forall_notMem_pos_iff`: the two combined.
* `coe_toNNReal_symm_eq_one_sub`: the factor `1 - p` in both spellings.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace PercLib.Probability

/-- The closed probability `1 - p` in `ℝ≥0∞`, written through `unitInterval.symm`. -/
theorem coe_toNNReal_symm_eq_one_sub (p : unitInterval) :
    (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) = 1 - unitInterval.toNNReal p :=
  ENNReal.eq_sub_of_add_eq ENNReal.coe_ne_top (by
    rw [← ENNReal.coe_add, unitInterval.toNNReal_symm_add_toNNReal, ENNReal.coe_one])

/-- Closed coordinates in a countable, injectively indexed family have the product law. -/
theorem prodBernoulli_forall_notMem {ι α : Type*} [Countable α]
    (p : ι → unitInterval) (f : α → ι) (hf : Function.Injective f) :
    prodBernoulli p {ω | ∀ a, f a ∉ ω} =
      ∏' a, (unitInterval.toNNReal (unitInterval.symm (p (f a))) : ℝ≥0∞) := by
  classical
  rw [prodBernoulli_eq_map, Measure.map_apply (show Measurable (fun q : ι → Prop => {i | q i}) from
      by fun_prop)
    (by simpa only [Set.ofPred_forall, Set.compl_ofPred] using
      MeasurableSet.iInter (fun a => (measurableSet_mem (f a)).compl))]
  have hset : (fun q : ι → Prop => {i | q i}) ⁻¹' {ω | ∀ a, f a ∉ ω} =
      Set.pi (Set.range f) (fun _ => {False}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_range,
      Set.mem_singleton_iff, forall_exists_index, forall_apply_eq_imp_iff]
    simp
  rw [hset]
  refine (Measure.infinitePi_pi_of_countable
    (μ := fun i => bernoulliMeasure True False (p i))
    (Set.countable_range f) (t := fun _ => {False}) (by measurability)).trans ?_
  rw [← (Equiv.ofInjective f hf).tprod_eq]
  apply tprod_congr
  intro a
  simp

/-- A closed product with summable open probabilities and no certain coordinate is
positive. -/
theorem tprod_symm_pos_of_summable {α : Type*} (p : α → unitInterval)
    (hs : Summable (fun a => (p a : ℝ))) (hlt : ∀ a, p a < 1) :
    0 < ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) := by
  classical
  have hnonneg (a) : 0 ≤ 1 - (p a : ℝ) := sub_nonneg.mpr (p a).property.2
  have hpos (a) : 0 < 1 - (p a : ℝ) := sub_pos.mpr (by exact_mod_cast hlt a)
  have hlog : Summable (fun a => Real.log (1 - (p a : ℝ))) := by
    simpa only [sub_eq_add_neg] using Real.summable_log_one_add_of_summable hs.neg
  have hp := Real.hasProd_of_hasSum_log hpos hlog.hasSum
  have hp' : HasProd (fun a => ENNReal.ofReal (1 - (p a : ℝ)))
      (ENNReal.ofReal (Real.exp (∑' a, Real.log (1 - (p a : ℝ))))) := by
    unfold HasProd at *
    convert (ENNReal.continuous_ofReal.tendsto _).comp hp using 1
    ext F
    simp [ENNReal.ofReal_prod_of_nonneg (fun a _ => hnonneg a)]
  have heq (a) : (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) =
      ENNReal.ofReal (1 - (p a : ℝ)) := by
    exact ENNReal.ofReal_coe_nnreal.symm
  simp_rw [heq]
  rw [hp'.tprod_eq]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- A positive closed product has summable open probabilities. -/
theorem summable_of_tprod_symm_pos {α : Type*} (p : α → unitInterval)
    (hpos : 0 < ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞)) :
    Summable (fun a => (p a : ℝ)) := by
  classical
  let P := ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞)
  have hle (a) : (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast (unitInterval.symm (p a)).property.2
  have hP : P ≤ 1 := tprod_le_one hle
  have hPr : 0 < P.toReal := ENNReal.toReal_pos (ne_of_gt hpos) (ne_top_of_le_ne_top (by simp) hP)
  apply summable_of_sum_le (fun a => (p a).property.1) (c := -Real.log P.toReal)
  intro F
  have hF : P ≤ ∏ a ∈ F, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) := by
    dsimp [P]
    rw [ENNReal.tprod_eq_iInf_prod hle]
    exact iInf_le _ F
  have hFr : P.toReal ≤ ∏ a ∈ F, (1 - (p a : ℝ)) := by
    have h := ENNReal.toReal_mono (ENNReal.prod_ne_top (fun _ _ => ENNReal.coe_ne_top)) hF
    simpa only [ENNReal.toReal_prod, ENNReal.coe_toReal, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq] using h
  have hexp : (∏ a ∈ F, (1 - (p a : ℝ))) ≤ Real.exp (-∑ a ∈ F, (p a : ℝ)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun a _ => sub_nonneg.mpr (p a).property.2)
      (fun a _ => Real.one_sub_le_exp_neg _)
  have hlog := Real.log_le_log hPr (hFr.trans hexp)
  rw [Real.log_exp] at hlog
  linarith

/-- A positive closed product has no certain coordinate. -/
theorem lt_one_of_tprod_symm_pos {α : Type*} (p : α → unitInterval)
    (hpos : 0 < ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞)) (a : α) :
    p a < 1 := by
  refine lt_of_le_of_ne (p a).property.2 fun h => hpos.ne' (tprod_of_exists_eq_zero ⟨a, ?_⟩)
  simp [h]

/-- **Positivity of a closed product.** `∏' a, (1 - p a)` is positive if and only if every
`p a < 1` and `∑ a, p a` converges. -/
theorem tprod_symm_pos_iff {α : Type*} (p : α → unitInterval) :
    0 < ∏' a, (unitInterval.toNNReal (unitInterval.symm (p a)) : ℝ≥0∞) ↔
      (∀ a, p a < 1) ∧ Summable (fun a => (p a : ℝ)) :=
  ⟨fun h => ⟨lt_one_of_tprod_symm_pos p h, summable_of_tprod_symm_pos p h⟩,
    fun h => tprod_symm_pos_of_summable p h.2 h.1⟩

/-- The probability that every coordinate of a countable injective family is closed is
positive if and only if no coordinate is certain and the open probabilities are summable. -/
theorem prodBernoulli_forall_notMem_pos_iff {ι α : Type*} [Countable α]
    (p : ι → unitInterval) (f : α → ι) (hf : Function.Injective f) :
    0 < prodBernoulli p {ω | ∀ a, f a ∉ ω} ↔
      (∀ a, p (f a) < 1) ∧ Summable (fun a => (p (f a) : ℝ)) := by
  rw [prodBernoulli_forall_notMem p f hf]
  exact tprod_symm_pos_iff (p ∘ f)

/-! ### Non-vacuity -/

/-- With all open probabilities zero the closed product is one, hence positive. -/
example {α : Type*} :
    0 < ∏' _a : α, (unitInterval.toNNReal (unitInterval.symm 0) : ℝ≥0∞) := by
  simp

/-- The open probabilities `2⁻ⁿ` are summable, so their closed product is positive. -/
example : 0 < ∏' n : ℕ, (unitInterval.toNNReal (unitInterval.symm
    ⟨(1 / 2 : ℝ) ^ (n + 1), by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩) : ℝ≥0∞) := by
  refine (tprod_symm_pos_iff _).2 ⟨fun n => ?_, ?_⟩
  · change (1 / 2 : ℝ) ^ (n + 1) < 1
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  · exact (summable_geometric_two.mul_left (1 / 2)).congr fun n => by
      change 1 / 2 * (1 / 2 : ℝ) ^ n = (1 / 2) ^ (n + 1)
      ring

end PercLib.Probability
