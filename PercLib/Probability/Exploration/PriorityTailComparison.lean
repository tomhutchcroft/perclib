/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original assembly of cluster-tail entropy comparison from the canonical stopped
exploration and its finite-transcript relative entropy. The constants retain
the exact Poisson factor and the coefficient-one weighted revealment bound.
-/
module

public import PercLib.Probability.Exploration.PriorityEntropy
public import PercLib.Percolation.Bond.VolumeTails
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Cluster-tail comparison from stopped-exploration entropy

## Main results

Finite answer events satisfy the entropy comparison with coefficient two in
front of KL. Increasing the exploration horizon then gives the actual cluster
tail bound, retaining its expected truncated volume. The unrestricted result
uses the complete host graph, with open loops still discarded by the canonical
open-graph interface.

The exact Poisson factor requires only positive intensity parameters. Ordering
the parameters gives a quadratic corollary with coefficient one. Susceptibility
may be infinite in all finite-threshold ENNReal statements. The several
parameters specify the exploration, laws, and a finite row cap; substantive
assumptions are a positive threshold, positive parameters, and the actual row
bound, with parameter order used only in the quadratic corollary.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Probability

/-- Event comparison with coefficient two in front of relative entropy.
The ENNReal statement also covers infinite divergence. -/
theorem measure_le_two_mul_add_two_mul_klDiv {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : Set Ω} (hT : MeasurableSet T) :
    ν T ≤ 2 * μ T + 2 * klDiv μ ν := by
  by_cases hD : klDiv μ ν = ⊤
  · simp [hD]
  have hs := sq_measureReal_sub_le_two_mul_max_mul_toReal_klDiv μ ν hT hD
  have hr : ν.real T ≤ 2 * μ.real T + 2 * (klDiv μ ν).toReal := by
    by_cases h : ν.real T ≤ 2 * μ.real T
    · exact h.trans (le_add_of_nonneg_right (by positivity))
    have huv : μ.real T ≤ ν.real T := by linarith [measureReal_nonneg (μ := μ) (s := T)]
    rw [max_eq_right huv] at hs
    by_contra hn
    have hv : 0 < ν.real T := by linarith [measureReal_nonneg (μ := μ) (s := T)]
    have hp : 0 < ν.real T * (ν.real T - 2 * μ.real T - 2 * (klDiv μ ν).toReal) :=
      mul_pos hv (by linarith)
    nlinarith [sq_nonneg (μ.real T)]
  have hμ : 2 * μ T ≠ ⊤ := ENNReal.mul_ne_top (by simp) (measure_ne_top μ T)
  have hkl : 2 * klDiv μ ν ≠ ⊤ := ENNReal.mul_ne_top (by simp) hD
  apply (ENNReal.toReal_le_toReal (measure_ne_top ν T) (ENNReal.add_ne_top.mpr ⟨hμ, hkl⟩)).mp
  simpa only [ENNReal.toReal_add hμ hkl, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    Measure.real] using hr

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- A finite-time discovered-volume event is determined by the actual answer
prefix. This does not assert configuration-monotonicity of the event. -/
theorem exists_priorityExploration_threshold_eq_prefix (G : SimpleGraph V)
    (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ) :
    ∃ T : Set (Fin m → Option Bool),
      {ω : Config V | (n : ℕ∞) ≤ (priorityExploration G ι o n ω m).discovered.encard} =
        {ω | (fun s : Fin m => priorityAnswer G ι o n ω s) ∈ T} := by
  refine ⟨{a | ∃ ω₀ : Config V, (fun s : Fin m => priorityAnswer G ι o n ω₀ s) = a ∧
    (n : ℕ∞) ≤ (priorityExploration G ι o n ω₀ m).discovered.encard}, ?_⟩
  ext ω
  constructor
  · intro hω
    exact ⟨ω, rfl, hω⟩
  · rintro ⟨ω₀, ha, hω₀⟩
    have hs := priorityExploration_eq_of_priorityAnswer_eq
      (fun s hs => congrFun ha ⟨s, hs⟩)
    change (n : ℕ∞) ≤ (priorityExploration G ι o n ω m).discovered.encard
    exact hs ▸ hω₀

section TranscriptEvent

variable [MeasurableSpace (Option Bool)] [MeasurableSingletonClass (Option Bool)]

/-- Every actual finite-transcript event obeys the exact-factor intensity
comparison. The same truncated-volume constant works for every horizon and
for arbitrary output events. -/
theorem law_priorityAnswer_prefix_intensity_le [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n m : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M)
    (T : Set (Fin m → Option Bool)) :
    law (intensityProfile J β₂)
      {ω : Config V | (fun s : Fin m => priorityAnswer G ι o n ω s) ∈ T} ≤
    2 * law (intensityProfile J β₁)
      {ω : Config V | (fun s : Fin m => priorityAnswer G ι o n ω s) ∈ T} +
      2 * ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) *
        (M : ℝ≥0∞) *
        ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
          ∂law (intensityProfile J β₁) := by
  have hA := measurable_priorityAnswer_prefix G ι o n m
  have hT : MeasurableSet T := T.to_countable.measurableSet
  have h := measure_le_two_mul_add_two_mul_klDiv
    ((law (intensityProfile J β₁)).map
      (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s))
    ((law (intensityProfile J β₂)).map
      (fun (ω : Config V) (s : Fin m) => priorityAnswer G ι o n ω s)) hT
  rw [Measure.map_apply hA hT, Measure.map_apply hA hT] at h
  refine h.trans ?_
  apply add_le_add_right
  simpa only [mul_assoc] using mul_le_mul_right
    (klDiv_priorityAnswer_prefix_intensity_le G ι o n m hn J β₁ β₂ h₁ h₂ M hrow) 2

end TranscriptEvent

/-- The actual cluster-tail event is the increasing union of finite-time
exploration outputs. Its exact entropy comparison retains the source-law
expected truncated cluster volume. -/
theorem law_le_encard_restricted_cluster_intensity_le_add [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    law (intensityProfile J β₂)
      {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} ≤
    2 * law (intensityProfile J β₁)
      {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} +
      2 * ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) *
        (M : ℝ≥0∞) *
        ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
          ∂law (intensityProfile J β₁) := by
  let : MeasurableSpace (Option Bool) := ⊤
  have : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩
  let C (t : ℕ) : Set (Config V) :=
    {ω | (n : ℕ∞) ≤ (priorityExploration G ι o n ω t).discovered.encard}
  have hmono : Monotone C := by
    intro s t hst ω hω
    exact hω.trans (encard_le_encard (priorityExploration_discovered_mono hst))
  have hE : {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} = ⋃ t, C t := by
    rw [setOf_le_encard_cluster_eq (ι := ι) hn]
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, ht.ge⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, le_antisymm (encard_priorityExploration_discovered_le hn t) ht⟩
  have hfinite (t : ℕ) : law (intensityProfile J β₂) (C t) ≤
      2 * law (intensityProfile J β₁) (C t) +
        2 * ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) *
          (M : ℝ≥0∞) *
          ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
            ∂law (intensityProfile J β₁) := by
    obtain ⟨T, hT⟩ := exists_priorityExploration_threshold_eq_prefix G ι o n t
    change law (intensityProfile J β₂) {ω | (n : ℕ∞) ≤
      (priorityExploration G ι o n ω t).discovered.encard} ≤ _
    rw [hT]
    simpa only [C, hT] using
      law_priorityAnswer_prefix_intensity_le G ι o n t hn J β₁ β₂ h₁ h₂ M hrow T
  calc
    _ = ⨆ t, law (intensityProfile J β₂) (C t) := by rw [hE, hmono.measure_iUnion]
    _ ≤ _ := by
      refine iSup_le fun t => (hfinite t).trans ?_
      apply add_le_add_left
      apply mul_le_mul_right
      apply measure_mono
      rw [hE]
      exact subset_iUnion C t

/-- Markov's inequality retains the expected truncated volume for the
restricted cluster. It does not require finite susceptibility. -/
theorem mul_law_le_encard_restricted_le_lintegral_min [Countable V]
    (G : SimpleGraph V) (q : Sym2 V → unitInterval) (o : V) (n : ℕ) :
    (n : ℝ≥0∞) * law q {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} ≤
      ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞) ∂law q := by
  have hK : Measurable (fun ω : Config V => (cluster (ω ∩ G.edgeSet) o).encard) :=
    (measurable_encard_cluster o).comp (measurable_id.inter measurable_const)
  have hm : Measurable (fun ω : Config V =>
      ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)) :=
    (Measurable.of_discrete (f := fun k : ℕ∞ => ((min k (n : ℕ∞)) : ℝ≥0∞))).comp hK
  have h := mul_meas_ge_le_lintegral₀ (μ := law q) hm.aemeasurable (n : ℝ≥0∞)
  have hset : {ω : Config V | (n : ℝ≥0∞) ≤
      ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)} =
      {ω | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} := by
    ext ω
    simp only [mem_ofPred_eq, ← ENat.toENNReal_min, ← ENat.toENNReal_coe,
      ENat.toENNReal_le, le_min_iff, le_refl, and_true]
  rwa [hset] at h

/-- The exact-factor cluster-tail bound with the actual truncated volume
retained on the right. -/
theorem law_le_encard_restricted_cluster_intensity_le_truncated [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    law (intensityProfile J β₂)
      {ω : Config V | (n : ℕ∞) ≤ (cluster (ω ∩ G.edgeSet) o).encard} ≤
      (2 / (n : ℝ≥0∞) + 2 * ENNReal.ofReal
        ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) * (M : ℝ≥0∞)) *
        ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
          ∂law (intensityProfile J β₁) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hb := mul_le_mul_right
    (mul_law_le_encard_restricted_le_lintegral_min G (intensityProfile J β₁) o n)
    (n : ℝ≥0∞)⁻¹
  rw [← mul_assoc, ENNReal.inv_mul_cancel hn0 (by simp), one_mul] at hb
  refine (law_le_encard_restricted_cluster_intensity_le_add G ι o n hn J β₁ β₂
    h₁ h₂ M hrow).trans ?_
  calc
    _ ≤ 2 * ((n : ℝ≥0∞)⁻¹ * ∫⁻ ω,
        ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
          ∂law (intensityProfile J β₁)) +
        2 * ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) *
          (M : ℝ≥0∞) * ∫⁻ ω,
            ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)
              ∂law (intensityProfile J β₁) := add_le_add_left (mul_le_mul_right hb 2) _
    _ = _ := by simp only [div_eq_mul_inv, add_mul, mul_assoc]

/-- Restricting a configuration to the complete host graph only removes
loops, which the canonical open graph already ignores. -/
theorem cluster_inter_edgeSet_top (ω : Config V) (o : V) :
    cluster (ω ∩ (⊤ : SimpleGraph V).edgeSet) o = cluster ω o := by
  simp only [cluster, openGraph, SimpleGraph.fromEdgeSet_inter,
    SimpleGraph.fromEdgeSet_edgeSet, inf_top_eq]

/-- Canonical unrestricted cluster-tail comparison retaining the expected
truncated volume. The temporary complete-graph edge order disappears from
the statement. -/
theorem law_le_encard_cluster_intensity_le_truncated [Countable V]
    (o : V) (n : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    law (intensityProfile J β₂)
      {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
      (2 / (n : ℝ≥0∞) + 2 * ENNReal.ofReal
        ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) * (M : ℝ≥0∞)) *
        ∫⁻ ω, ((min (cluster ω o).encard (n : ℕ∞)) : ℝ≥0∞)
          ∂law (intensityProfile J β₁) := by
  let : Encodable (⊤ : SimpleGraph V).edgeSet := Encodable.ofCountable _
  simpa only [cluster_inter_edgeSet_top] using
    law_le_encard_restricted_cluster_intensity_le_truncated (⊤ : SimpleGraph V)
      (Encodable.encode' _) o n hn J β₁ β₂ h₁ h₂ M hrow

/-- The canonical exact-factor susceptibility bound, in ENNReal so that
infinite susceptibility is included without a toReal conversion. -/
theorem law_le_encard_cluster_intensity_le_chi [Countable V]
    (o : V) (n : ℕ) (hn : 1 ≤ n)
    (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (h₂ : 0 < β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    law (intensityProfile J β₂)
      {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
      (2 / (n : ℝ≥0∞) + 2 * ENNReal.ofReal
        ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) * (M : ℝ≥0∞)) *
        chi (intensityProfile J β₁) o := by
  refine (law_le_encard_cluster_intensity_le_truncated o n hn J β₁ β₂ h₁ h₂ M hrow).trans ?_
  apply mul_le_mul_right
  have h := lintegral_truncated_restricted_cluster_le_min_chi
    (⊤ : SimpleGraph V) (intensityProfile J β₁) o n
  simpa only [cluster_inter_edgeSet_top] using h.trans (min_le_left _ _)

/-- Ordering the intensity parameters converts twice the exact Poisson
factor to the quadratic expression with coefficient one. -/
theorem two_mul_poissonFactor_mul_le_quadratic (β₁ β₂ M : ℝ≥0)
    (h₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    2 * ENNReal.ofReal ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) *
      (M : ℝ≥0∞) ≤ ENNReal.ofReal ((M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁) := by
  have h₁r : 0 < (β₁ : ℝ) := by exact_mod_cast h₁
  have hβr : (β₁ : ℝ) ≤ β₂ := by exact_mod_cast hβ
  have h₂r : 0 < (β₂ : ℝ) := h₁r.trans_le hβr
  have h := mul_poissonDivergence_le M.coe_nonneg h₁r h₂r
  rw [min_eq_left hβr] at h
  have hr : 2 * ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂) * (M : ℝ) ≤
      (M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁ := by
    calc
      _ = 2 * ((M : ℝ) * ((β₁ : ℝ) * Real.log ((β₁ : ℝ) / β₂) - β₁ + β₂)) := by ring
      _ ≤ 2 * ((M : ℝ) * ((β₁ : ℝ) - β₂) ^ 2 / (2 * β₁)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by field_simp [h₁r.ne']; ring
  simpa only [ENNReal.ofReal_mul' M.coe_nonneg,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr

/-- The canonical quadratic cluster-tail bound with coefficient one in the
intensity-error term. No finite susceptibility or critical-cluster hypothesis
is imposed. -/
theorem law_le_encard_cluster_intensity_le_chi_quadratic [Countable V]
    (o : V) (n : ℕ) (hn : 1 ≤ n) (J : Sym2 V → ℝ≥0)
    (β₁ β₂ : ℝ≥0) (h₁ : 0 < β₁) (hβ : β₁ ≤ β₂)
    (M : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M) :
    law (intensityProfile J β₂)
      {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard} ≤
      (2 / (n : ℝ≥0∞) + ENNReal.ofReal
        ((M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁)) * chi (intensityProfile J β₁) o :=
  (law_le_encard_cluster_intensity_le_chi o n hn J β₁ β₂ h₁ (h₁.trans_le hβ) M hrow).trans
    (mul_le_mul_left (add_le_add_right (two_mul_poissonFactor_mul_le_quadratic β₁ β₂ M h₁ hβ) _)
      (chi (intensityProfile J β₁) o))

end PercLib.Percolation.Bond
