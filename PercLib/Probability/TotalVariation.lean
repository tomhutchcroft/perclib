/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-15. No upstream proof is copied: the bound is derived from the merged
monotone coupling `PercLib.Probability.exists_prodBernoulli_monotone_coupling`, through the profile
`min q q'`.
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.Cylinder

/-!
# A total-variation bound between Bernoulli product laws

For every measurable event `A` and every pair of profiles on a countable index type,

`P_q(A) ≤ P_{q'}(A) + ∑' i, |q i - q' i|` (`prodBernoulli_le_add_tsum_dist`).

The proof couples each of `q` and `q'` monotonically with `min q q'`: under an ordered
coupling of `r ≤ q` the two configurations differ only where the upper one is open and the
lower one closed, which happens at `i` with probability `q i - r i`. The bond corollaries
bound the change of `τ` and `θ`. This file adds no definition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {ι : Type*}

/-- The open probability as an extended real. -/
theorem coe_toNNReal_eq_ofReal (x : unitInterval) :
    (unitInterval.toNNReal x : ℝ≥0∞) = ENNReal.ofReal (x : ℝ) := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg x.2.1]
  rfl

/-- **Comparison along an ordered pair of profiles.** If `r ≤ q`, then for every measurable
event, `P_q(A) ≤ P_r(A) + ∑' i, (q i - r i)` and `P_r(A) ≤ P_q(A) + ∑' i, (q i - r i)`. -/
theorem prodBernoulli_le_add_tsum_of_le [Countable ι] (r q : ι → unitInterval) (hrq : r ≤ q)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    prodBernoulli q A ≤ prodBernoulli r A + ∑' i, ENNReal.ofReal ((q i : ℝ) - r i) ∧
      prodBernoulli r A ≤ prodBernoulli q A + ∑' i, ENNReal.ofReal ((q i : ℝ) - r i) := by
  obtain ⟨γ, _, h₁, h₂, hord⟩ := exists_prodBernoulli_monotone_coupling r q hrq
  have hP₁ : ∀ B : Set (Set ι), MeasurableSet B → prodBernoulli r B = γ (Prod.fst ⁻¹' B) :=
    fun B hB => by rw [← h₁, Measure.map_apply measurable_fst hB]
  have hP₂ : ∀ B : Set (Set ι), MeasurableSet B → prodBernoulli q B = γ (Prod.snd ⁻¹' B) :=
    fun B hB => by rw [← h₂, Measure.map_apply measurable_snd hB]
  set D : ι → Set (Set ι × Set ι) := fun i => {z | i ∈ z.2 ∧ i ∉ z.1}
  have hDm : ∀ i, MeasurableSet (D i) := fun i =>
    ((measurableSet_mem i).preimage measurable_snd).inter
      ((measurableSet_mem i).preimage measurable_fst).compl
  have hD : ∀ i, γ (D i) = ENNReal.ofReal ((q i : ℝ) - r i) := by
    intro i
    have hsub : {z : Set ι × Set ι | i ∈ z.1} ≤ᵐ[γ] {z | i ∈ z.2} := by
      filter_upwards [hord] with z hz hi
      exact hz hi
    have hfst : γ {z : Set ι × Set ι | i ∈ z.1} = ENNReal.ofReal (r i) := by
      rw [show {z : Set ι × Set ι | i ∈ z.1} = Prod.fst ⁻¹' {ω | i ∈ ω} from rfl,
        ← hP₁ _ (measurableSet_mem i), prodBernoulli_setOf_mem, coe_toNNReal_eq_ofReal]
    have hsnd : γ {z : Set ι × Set ι | i ∈ z.2} = ENNReal.ofReal (q i) := by
      rw [show {z : Set ι × Set ι | i ∈ z.2} = Prod.snd ⁻¹' {ω | i ∈ ω} from rfl,
        ← hP₂ _ (measurableSet_mem i), prodBernoulli_setOf_mem, coe_toNNReal_eq_ofReal]
    have hsplit := measure_inter_add_sdiff (μ := γ) {z : Set ι × Set ι | i ∈ z.2}
      ((measurableSet_mem i).preimage measurable_fst)
    have hinter : γ ({z : Set ι × Set ι | i ∈ z.2} ∩ Prod.fst ⁻¹' {ω | i ∈ ω}) =
        γ {z : Set ι × Set ι | i ∈ z.1} := by
      refine measure_congr ?_
      filter_upwards [hord] with z hz
      refine propext ⟨fun h => h.2, fun h => ⟨hz h, h⟩⟩
    rw [hinter, hfst, hsnd] at hsplit
    have hle : (r i : ℝ) ≤ q i := hrq i
    rw [ENNReal.ofReal_sub _ (r i).2.1]
    refine ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top ?_
    rw [add_comm]
    exact hsplit
  have hdiff : {z : Set ι × Set ι | z.1 ≠ z.2} ≤ᵐ[γ] ⋃ i, D i := by
    filter_upwards [hord] with z hz hne
    obtain ⟨i, hi⟩ : ∃ i, i ∈ z.2 ∧ i ∉ z.1 := by
      by_contra h
      push Not at h
      exact hne (Set.Subset.antisymm hz fun i hi => h i hi)
    exact mem_iUnion.2 ⟨i, hi⟩
  have hbound : γ {z : Set ι × Set ι | z.1 ≠ z.2} ≤ ∑' i, ENNReal.ofReal ((q i : ℝ) - r i) := by
    calc γ {z : Set ι × Set ι | z.1 ≠ z.2} ≤ γ (⋃ i, D i) := measure_mono_ae hdiff
      _ ≤ ∑' i, γ (D i) := measure_iUnion_le _
      _ = _ := by simp_rw [hD]
  constructor
  · rw [hP₂ A hA, hP₁ A hA]
    calc γ (Prod.snd ⁻¹' A) ≤ γ (Prod.fst ⁻¹' A ∪ {z | z.1 ≠ z.2}) := by
          refine measure_mono fun z hz => ?_
          by_cases h : z.1 = z.2
          · left; simp only [mem_preimage]; rw [h]; exact hz
          · right; exact h
      _ ≤ γ (Prod.fst ⁻¹' A) + γ {z | z.1 ≠ z.2} := measure_union_le _ _
      _ ≤ _ := by gcongr
  · rw [hP₂ A hA, hP₁ A hA]
    calc γ (Prod.fst ⁻¹' A) ≤ γ (Prod.snd ⁻¹' A ∪ {z | z.1 ≠ z.2}) := by
          refine measure_mono fun z hz => ?_
          by_cases h : z.1 = z.2
          · left; simp only [mem_preimage]; rw [← h]; exact hz
          · right; exact h
      _ ≤ γ (Prod.snd ⁻¹' A) + γ {z | z.1 ≠ z.2} := measure_union_le _ _
      _ ≤ _ := by gcongr

/-- Through the minimum of two numbers, the two one-sided differences add up to the
distance. -/
theorem ofReal_sub_min_add (a b : unitInterval) :
    ENNReal.ofReal ((a : ℝ) - (min a b : unitInterval)) +
        ENNReal.ofReal ((b : ℝ) - (min a b : unitInterval)) =
      ENNReal.ofReal |(a : ℝ) - b| := by
  rcases le_total a b with h | h
  · have h' : (a : ℝ) ≤ b := h
    rw [min_eq_left h, sub_self, ENNReal.ofReal_zero, zero_add, abs_sub_comm,
      abs_of_nonneg (by linarith)]
  · have h' : (b : ℝ) ≤ a := h
    rw [min_eq_right h, sub_self, ENNReal.ofReal_zero, add_zero, abs_of_nonneg (by linarith)]

/-- **Total-variation bound between Bernoulli product laws.** For every measurable event on a
countable index type, `P_q(A) ≤ P_{q'}(A) + ∑' i, |q i - q' i|`. -/
theorem prodBernoulli_le_add_tsum_dist [Countable ι] (q q' : ι → unitInterval)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    prodBernoulli q A ≤ prodBernoulli q' A + ∑' i, ENNReal.ofReal |(q i : ℝ) - q' i| := by
  set r : ι → unitInterval := fun i => min (q i) (q' i)
  have h1 := (prodBernoulli_le_add_tsum_of_le r q (fun i => min_le_left _ _) hA).1
  have h2 := (prodBernoulli_le_add_tsum_of_le r q' (fun i => min_le_right _ _) hA).2
  calc prodBernoulli q A
      ≤ prodBernoulli r A + ∑' i, ENNReal.ofReal ((q i : ℝ) - r i) := h1
    _ ≤ prodBernoulli q' A + ∑' i, ENNReal.ofReal ((q' i : ℝ) - r i) +
          ∑' i, ENNReal.ofReal ((q i : ℝ) - r i) := by gcongr
    _ = prodBernoulli q' A + ∑' i, ENNReal.ofReal |(q i : ℝ) - q' i| := by
        rw [add_assoc, ← ENNReal.tsum_add]
        congr 1
        refine tsum_congr fun i => ?_
        rw [add_comm]
        exact ofReal_sub_min_add (q i) (q' i)

/-- The real form: `|P_q(A) - P_{q'}(A)| ≤ ∑' i, |q i - q' i|` when the sum is finite. -/
theorem abs_prodBernoulli_real_sub_le [Countable ι] (q q' : ι → unitInterval)
    {A : Set (Set ι)} (hA : MeasurableSet A)
    (hfin : ∑' i, ENNReal.ofReal |(q i : ℝ) - q' i| ≠ ∞) :
    |(prodBernoulli q).real A - (prodBernoulli q').real A| ≤
      (∑' i, ENNReal.ofReal |(q i : ℝ) - q' i|).toReal := by
  have h1 := prodBernoulli_le_add_tsum_dist q q' hA
  have h2 := prodBernoulli_le_add_tsum_dist q' q hA
  have hsym : (∑' i, ENNReal.ofReal |(q' i : ℝ) - q i|) = ∑' i,
      ENNReal.ofReal |(q i : ℝ) - q' i| := by
    simp_rw [abs_sub_comm]
  rw [hsym] at h2
  have r1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hfin⟩) h1
  have r2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hfin⟩) h2
  rw [ENNReal.toReal_add (measure_ne_top _ _) hfin] at r1 r2
  simp only [measureReal_def]
  rw [abs_le]
  constructor <;> linarith

/-! ### From events to bounded observables -/

/-- **Event bounds control bounded observables.** If two probability measures differ by at most
`c` on every measurable event, then for a measurable `f` with values in `[m, M]`,
`|∫ f dμ - ∫ f dν| ≤ (M - m) c`. The proof is the layer-cake formula. -/
theorem abs_integral_sub_integral_le_of_abs_measureReal_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ}
    (hc : ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ c) {f : Ω → ℝ} (hf : Measurable f)
    {m M : ℝ} (hm : ∀ ω, m ≤ f ω) (hM : ∀ ω, f ω ≤ M) :
    |∫ ω, f ω ∂μ - ∫ ω, f ω ∂ν| ≤ (M - m) * c := by
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hL : 0 ≤ M - m := sub_nonneg.2 ((hm ω₀).trans (hM ω₀))
  set g : Ω → ℝ := fun ω => f ω - m
  have hg : Measurable g := hf.sub_const m
  have hgint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → Integrable g ρ := fun ρ _ =>
    Integrable.of_bound hg.aestronglyMeasurable (M - m) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hm ω, hM ω])
  have hint : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ →
      ∫ ω, f ω ∂ρ = (∫ t in Ioc 0 (M - m), ρ.real {ω | t < g ω}) + m := by
    intro ρ _
    have h1 : ∫ ω, f ω ∂ρ = ∫ ω, g ω ∂ρ + m := by
      have hfint : Integrable f ρ := Integrable.of_bound hf.aestronglyMeasurable (|m| + |M|)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [hm ω, hM ω, neg_abs_le m, le_abs_self M, abs_nonneg m,
            abs_nonneg M])
      rw [integral_sub hfint (integrable_const m)]
      simp
    rw [h1, Integrable.integral_eq_integral_meas_lt (hgint ρ inferInstance)
      (Filter.Eventually.of_forall fun ω => sub_nonneg.2 (hm ω))]
    congr 1
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun t ht => ?_
    have htL : M - m < t := by
      rcases ht with ⟨ht0, ht1⟩
      simp only [mem_Ioc, not_and, not_le] at ht1
      exact ht1 ht0
    have : {ω | t < g ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, g]
      linarith [hM ω]
    simp [this]
  have hanti : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ →
      IntegrableOn (fun t => ρ.real {ω | t < g ω}) (Ioc 0 (M - m)) := by
    intro ρ _
    have hA : Antitone fun t => ρ.real {ω | t < g ω} := fun s t hst =>
      measureReal_mono fun ω (hω : t < g ω) => lt_of_le_of_lt hst hω
    exact ((hA.antitoneOn _).integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [hint μ inferInstance, hint ν inferInstance]
  convert_to |∫ t in Ioc 0 (M - m), (μ.real {ω | t < g ω} - ν.real {ω | t < g ω})| ≤ _ using 2
  · rw [integral_sub (hanti μ inferInstance) (hanti ν inferInstance)]
    ring
  rw [← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (C := c) measure_Ioc_lt_top
    fun t _ => ?_).trans_eq ?_
  · rw [Real.norm_eq_abs]
    exact hc _ (measurableSet_lt measurable_const hg)
  · rw [Real.volume_real_Ioc_of_le hL, sub_zero, mul_comm]

/-- Two probability measures differ by at most `1` on every event. -/
theorem abs_measureReal_sub_le_one {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set Ω) :
    |μ.real A - ν.real A| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [measureReal_nonneg (μ := μ) (s := A),
    measureReal_nonneg (μ := ν) (s := A), measureReal_le_one (μ := μ) (s := A),
    measureReal_le_one (μ := ν) (s := A)]

/-- **Capped total-variation bound.** For every measurable event on a countable index type,
`|P_q(A) - P_{q'}(A)| ≤ min {1, ∑' i, |q i - q' i|}`; the sum may be infinite. -/
theorem abs_prodBernoulli_real_sub_le_min [Countable ι] (q q' : ι → unitInterval)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    |(prodBernoulli q).real A - (prodBernoulli q').real A| ≤
      (min 1 (∑' i, ENNReal.ofReal |(q i : ℝ) - q' i|)).toReal := by
  by_cases hfin : ∑' i, ENNReal.ofReal |(q i : ℝ) - q' i| = ∞
  · rw [hfin, min_eq_left le_top, ENNReal.toReal_one]
    exact abs_measureReal_sub_le_one _ _ A
  · rw [ENNReal.toReal_min ENNReal.one_ne_top hfin, ENNReal.toReal_one]
    exact le_min (abs_measureReal_sub_le_one _ _ A) (abs_prodBernoulli_real_sub_le q q' hA hfin)

/-- **Bounded observables under a profile perturbation.** For a bounded measurable `f` on
configurations of a countable index type, `|E_q f - E_{q'} f| ≤ osc(f) · min {1, ∑' |q i - q' i|}`
with `osc(f) = sup f - inf f`. -/
theorem abs_integral_prodBernoulli_sub_le [Countable ι] (q q' : ι → unitInterval)
    {f : Set ι → ℝ} (hf : Measurable f) (hfa : BddAbove (range f)) (hfb : BddBelow (range f)) :
    |∫ ω, f ω ∂prodBernoulli q - ∫ ω, f ω ∂prodBernoulli q'| ≤
      ((⨆ ω, f ω) - ⨅ ω, f ω) * (min 1 (∑' i, ENNReal.ofReal |(q i : ℝ) - q' i|)).toReal :=
  abs_integral_sub_integral_le_of_abs_measureReal_sub_le
    (fun _ hA => abs_prodBernoulli_real_sub_le_min q q' hA) hf (fun ω => ciInf_le hfb ω)
    (fun ω => le_ciSup hfa ω)

/-! ### Non-vacuity -/

/-- One coordinate: the bound is the difference of the two open probabilities. -/
example (q q' : Unit → unitInterval) :
    prodBernoulli q {ω | () ∈ ω} ≤
      prodBernoulli q' {ω | () ∈ ω} + ENNReal.ofReal |(q () : ℝ) - q' ()| := by
  simpa using prodBernoulli_le_add_tsum_dist q q' (measurableSet_mem ())

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- **The two-point function is Lipschitz in the profile.** -/
theorem tau_le_add_tsum_dist [Countable V] (q q' : Sym2 V → unitInterval) (x y : V) :
    tau q x y ≤ tau q' x y + ∑' e, ENNReal.ofReal |(q e : ℝ) - q' e| :=
  prodBernoulli_le_add_tsum_dist q q' (measurableSet_conn x y)

/-- **Percolation probabilities are Lipschitz in the profile.** -/
theorem law_cluster_infinite_le_add_tsum_dist [Countable V] (q q' : Sym2 V → unitInterval)
    (x : V) :
    law q {ω | (cluster ω x).Infinite} ≤
      law q' {ω | (cluster ω x).Infinite} + ∑' e, ENNReal.ofReal |(q e : ℝ) - q' e| :=
  prodBernoulli_le_add_tsum_dist q q' (measurableSet_cluster_infinite x)

/-- Profiles that agree give the same probabilities: the bound is `0`. -/
example [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    tau q x y ≤ tau q x y + ∑' e, ENNReal.ofReal |(q e : ℝ) - q e| :=
  tau_le_add_tsum_dist q q x y

end PercLib.Percolation.Bond
