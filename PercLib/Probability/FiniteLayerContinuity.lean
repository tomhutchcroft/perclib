/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original continuity consequences of the existing Bernoulli cylinder formulas;
no upstream proof is copied.
-/
module

public import PercLib.Probability.FiniteContinuity
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Continuity of events in finitely many independent Bernoulli layers

## Main results

An event determined by a finite coordinate block in each of finitely many
independent layers has probability continuous in all layer profiles. The
ambient coordinate type is arbitrary, and the finite blocks may differ
between layers. The proof restricts each layer to its finite block and uses
the existing finite-event probability formulas.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Probability

variable {I E : Type*} [Fintype I]

/-- Probabilities on a finite product of finite Bernoulli configuration spaces
are continuous in the individual layer profiles. -/
theorem continuous_pi_prodBernoulli_finite_apply
    {K : I → Type*} [∀ i, Finite (K i)] (A : Set (∀ i, Set (K i))) :
    Continuous (fun p : ∀ i, K i → unitInterval =>
      (Measure.pi (fun i => prodBernoulli (p i))) A) := by
  classical
  let : ∀ i, Fintype (K i) := fun i => Fintype.ofFinite (K i)
  have heq (p : ∀ i, K i → unitInterval) :
      (Measure.pi (fun i => prodBernoulli (p i))) A =
        ∑ ω ∈ A.toFinset, ∏ i, prodBernoulli (p i) {ω i} := by
    simpa only [Measure.pi_singleton, Set.coe_toFinset] using
      (sum_measure_singleton (μ := Measure.pi (fun i => prodBernoulli (p i)))
        (s := A.toFinset)).symm
  simp_rw [heq]
  apply continuous_finsetSum
  intro ω _
  have hc (i : I) : Continuous (fun p : ∀ i, K i → unitInterval =>
      (prodBernoulli (p i) {ω i}).toNNReal) :=
    ENNReal.continuousOn_toNNReal.comp_continuous
      ((continuous_prodBernoulli_finite_apply {ω i}).comp (continuous_apply i))
      (fun p => measure_ne_top _ _)
  have hp := continuous_finsetProd Finset.univ (fun i _ => hc i)
  convert ENNReal.continuous_coe.comp hp using 1
  funext p
  simp only [Function.comp_apply, ENNReal.ofNNReal_finsetProd,
    ENNReal.coe_toNNReal (measure_ne_top _ _)]

/-- Restricting each independent layer gives the product of its restricted
Bernoulli laws, even when the ambient coordinate type is infinite. -/
theorem pi_prodBernoulli_cylinder_apply (p : I → E → unitInterval)
    (F : I → Finset E) (A : Set (∀ i, Set (F i))) :
    (Measure.pi (fun i => prodBernoulli (p i)))
        {ω | (fun i => (Subtype.val ⁻¹' ω i : Set (F i))) ∈ A} =
      (Measure.pi (fun i => prodBernoulli (fun e : F i => p i e))) A := by
  classical
  have hm (i : I) : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (F i))) := by
    apply Measurable.of_mem
    intro e
    exact (measurableSet_mem e.val).mem
  have hmap := Measure.pi_map_pi (μ := fun i => prodBernoulli (p i))
    (fun i => (hm i).aemeasurable)
  simp_rw [prodBernoulli_map_restrict] at hmap
  have hmAll : Measurable (fun ω : I → Set E =>
      fun i => (Subtype.val ⁻¹' ω i : Set (F i))) :=
    Measurable.of_eval (fun i => (hm i).comp (measurable_pi_apply i))
  rw [← hmap, Measure.map_apply hmAll (Set.toFinite A).measurableSet]
  rfl

/-- A finite family of arbitrary ambient Bernoulli spaces has continuous
probabilities for events determined by finite coordinate blocks. -/
theorem continuous_pi_prodBernoulli_of_determined (F : I → Finset E)
    {A : Set (I → Set E)}
    (hA : ∀ ω η, (∀ i, ω i ∩ (F i : Set E) = η i ∩ (F i : Set E)) →
      (ω ∈ A ↔ η ∈ A)) :
    Continuous (fun p : I → E → unitInterval =>
      (Measure.pi (fun i => prodBernoulli (p i))) A) := by
  classical
  let B : Set (∀ i, Set (F i)) := {η | (fun i => Subtype.val '' η i) ∈ A}
  have hset : A = {ω | (fun i => (Subtype.val ⁻¹' ω i : Set (F i))) ∈ B} := by
    ext ω
    apply hA
    intro i
    ext e
    simp only [mem_inter_iff, mem_image, mem_preimage, Subtype.exists, exists_and_right,
      exists_eq_right, Finset.mem_coe]
    tauto
  rw [hset]
  simp_rw [pi_prodBernoulli_cylinder_apply]
  exact (continuous_pi_prodBernoulli_finite_apply B).comp (by fun_prop)

end PercLib.Probability
