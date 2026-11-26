/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Conditioning the three-function correlation. New for this project against pinned mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679; no upstream code is copied. Mathematical reference:
D. St. P. Richards, *Algebraic methods toward higher-order probability inequalities, II*,
Ann. Probab. 32 (2004), (2.6)–(2.13).
-/
module

public import PercLib.Probability.HigherCorrelation
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Probability.Distributions.Uniform

/-!
# Conditioning a three-function correlation

For bounded real random variables `f 0, f 1, f 2` and a sub-σ-algebra `m`, write
`M i = μ[f i | m]` and `c i j = μ[f i * f j | m] - M i * M j`, and let `L` be the conditional
version of the expression defining `E_3`. Then
`E_3(f) = ∫ L + E_3(M) + cov(c 0 1, M 2) + cov(c 0 2, M 1) + cov(c 1 2, M 0)`.

## Main results

* `PercLib.higherCorrelation_fin_three_eq_condExp`: the conditioning identity.
* `PercLib.condExp_comap_snd_fairBits`: conditional expectations given the second of two
  independent fair bits.
* `PercLib.covariance_sum_fairBits_eq`: on two independent fair bits the covariance sum
  of the identity is `-1/16` for the nonnegative increasing functions `X ∨ Z, X ∨ Z, Z`,
  conditioning on `Z`.
* `PercLib.exists_covariance_sum_neg_fairBits`: hence the covariance sum can be negative for
  nonnegative increasing functions of independent fair bits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace PercLib

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Products of a.e. bounded, a.e. strongly measurable functions are again such. -/
private theorem aebdd_mul {g h : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ ∧ ∃ C, ∀ᵐ ω ∂μ, |g ω| ≤ C)
    (hh : AEStronglyMeasurable h μ ∧ ∃ C, ∀ᵐ ω ∂μ, |h ω| ≤ C) :
    AEStronglyMeasurable (g * h) μ ∧ ∃ C, ∀ᵐ ω ∂μ, |(g * h) ω| ≤ C := by
  obtain ⟨C, hC⟩ := hg.2
  obtain ⟨D, hD⟩ := hh.2
  refine ⟨hg.1.mul hh.1, C * D, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- Conditional expectations of a.e. bounded functions are a.e. bounded. -/
private theorem aebdd_condExp (hm : m ≤ mΩ) {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ ∧ ∃ C, ∀ᵐ ω ∂μ, |g ω| ≤ C) :
    AEStronglyMeasurable (μ[g | m]) μ ∧ ∃ C, ∀ᵐ ω ∂μ, |(μ[g | m]) ω| ≤ C := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨(stronglyMeasurable_condExp.mono hm).aestronglyMeasurable, C,
    ae_bdd_abs_condExp_of_ae_bdd_abs hC⟩

private theorem aebdd_integrable [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ ∧ ∃ C, ∀ᵐ ω ∂μ, |g ω| ≤ C) : Integrable g μ := by
  obtain ⟨C, hC⟩ := hg.2
  exact Integrable.of_bound hg.1 C (by simpa using hC)

private theorem aebdd_memLp [IsFiniteMeasure μ] {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ ∧ ∃ C, ∀ᵐ ω ∂μ, |g ω| ≤ C) : MemLp g 2 μ := by
  obtain ⟨C, hC⟩ := hg.2
  exact MemLp.of_bound hg.1 C (by simpa using hC)

private theorem aebdd_sub {g h : Ω → ℝ}
    (hg : AEStronglyMeasurable g μ ∧ ∃ C, ∀ᵐ ω ∂μ, |g ω| ≤ C)
    (hh : AEStronglyMeasurable h μ ∧ ∃ C, ∀ᵐ ω ∂μ, |h ω| ≤ C) :
    AEStronglyMeasurable (g - h) μ ∧ ∃ C, ∀ᵐ ω ∂μ, |(g - h) ω| ≤ C := by
  obtain ⟨C, hC⟩ := hg.2
  obtain ⟨D, hD⟩ := hh.2
  refine ⟨hg.1.sub hh.1, C + D, ?_⟩
  filter_upwards [hC, hD] with ω h1 h2
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- **Conditioning a three-function correlation.** Let `f 0, f 1, f 2` be bounded real random
variables on a probability space and `m` a sub-σ-algebra. With `M i = μ[f i | m]`,
`c i j = μ[f i * f j | m] - M i * M j` and
`L = 2 μ[f 0 f 1 f 2 | m] - μ[f 0 f 1 | m] M 2 - μ[f 0 f 2 | m] M 1 - μ[f 1 f 2 | m] M 0`
`+ M 0 M 1 M 2` (the expression defining `E_3` with conditional expectations),
`E_3(f) = ∫ L + E_3(M) + cov(c 0 1, M 2) + cov(c 0 2, M 1) + cov(c 1 2, M 0)`. -/
theorem higherCorrelation_fin_three_eq_condExp [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (f : Fin 3 → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hb : ∀ i, ∃ C, ∀ ω, |f i ω| ≤ C) :
    higherCorrelation μ univ f =
      ∫ ω, (2 * (μ[f 0 * f 1 * f 2 | m]) ω -
          ((μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω + (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω +
            (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω) +
          (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω) ∂μ +
        higherCorrelation μ univ (fun i ↦ μ[f i | m]) +
        (cov[μ[f 0 * f 1 | m] - μ[f 0 | m] * μ[f 1 | m], μ[f 2 | m]; μ] +
          cov[μ[f 0 * f 2 | m] - μ[f 0 | m] * μ[f 2 | m], μ[f 1 | m]; μ] +
          cov[μ[f 1 * f 2 | m] - μ[f 1 | m] * μ[f 2 | m], μ[f 0 | m]; μ]) := by
  have hF : ∀ i, AEStronglyMeasurable (f i) μ ∧ ∃ C, ∀ᵐ ω ∂μ, |f i ω| ≤ C := fun i ↦
    ⟨(hf i).aestronglyMeasurable, (hb i).imp fun _ h ↦ Filter.Eventually.of_forall h⟩
  -- Boundedness of every function that occurs.
  have hM := fun i ↦ aebdd_condExp hm (hF i)
  have hP := fun i j ↦ aebdd_condExp hm (aebdd_mul (hF i) (hF j))
  have hq := aebdd_condExp hm (aebdd_mul (aebdd_mul (hF 0) (hF 1)) (hF 2))
  have hI := fun {g : Ω → ℝ} (h : AEStronglyMeasurable g μ ∧ ∃ C, ∀ᵐ ω ∂μ, |g ω| ≤ C) ↦
    aebdd_integrable h
  -- Integrals of conditional expectations.
  have hE : ∀ g : Ω → ℝ, ∫ ω, (μ[g | m]) ω ∂μ = ∫ ω, g ω ∂μ := fun g ↦ integral_condExp hm
  -- The covariances.
  have hcov : ∀ i j k, cov[μ[f i * f j | m] - μ[f i | m] * μ[f j | m], μ[f k | m]; μ] =
      ∫ ω, (μ[f i * f j | m]) ω * (μ[f k | m]) ω ∂μ -
        ∫ ω, (μ[f i | m]) ω * (μ[f j | m]) ω * (μ[f k | m]) ω ∂μ -
        ((∫ ω, f i ω * f j ω ∂μ) - ∫ ω, (μ[f i | m]) ω * (μ[f j | m]) ω ∂μ) *
          ∫ ω, f k ω ∂μ := by
    intro i j k
    rw [covariance_eq_sub (aebdd_memLp (aebdd_sub (hP i j) (aebdd_mul (hM i) (hM j))))
      (aebdd_memLp (hM k))]
    have i1 : Integrable (fun ω ↦ (μ[f i * f j | m]) ω * (μ[f k | m]) ω) μ :=
      hI (aebdd_mul (hP i j) (hM k))
    have i2 : Integrable (fun ω ↦ (μ[f i | m]) ω * (μ[f j | m]) ω * (μ[f k | m]) ω) μ :=
      hI (aebdd_mul (aebdd_mul (hM i) (hM j)) (hM k))
    have i3 : Integrable (fun ω ↦ (μ[f i * f j | m]) ω) μ := hI (hP i j)
    have i4 : Integrable (fun ω ↦ (μ[f i | m]) ω * (μ[f j | m]) ω) μ :=
      hI (aebdd_mul (hM i) (hM j))
    simp only [Pi.mul_apply, Pi.sub_apply, sub_mul]
    rw [integral_sub i1 i2, integral_sub i3 i4, hE, hE]
    simp only [Pi.mul_apply]
    ring
  -- The conditional expression `L`.
  have hL : ∫ ω, (2 * (μ[f 0 * f 1 * f 2 | m]) ω -
          ((μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω + (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω +
            (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω) +
          (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω) ∂μ =
      2 * ∫ ω, f 0 ω * f 1 ω * f 2 ω ∂μ -
        (∫ ω, (μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω ∂μ +
          ∫ ω, (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω ∂μ +
          ∫ ω, (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω ∂μ) +
        ∫ ω, (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω ∂μ := by
    have i1 : Integrable (fun ω ↦ (μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω) μ :=
      hI (aebdd_mul (hP 0 1) (hM 2))
    have i2 : Integrable (fun ω ↦ (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω) μ :=
      hI (aebdd_mul (hP 0 2) (hM 1))
    have i3 : Integrable (fun ω ↦ (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω) μ :=
      hI (aebdd_mul (hP 1 2) (hM 0))
    have i4 : Integrable (fun ω ↦ (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω) μ :=
      hI (aebdd_mul (aebdd_mul (hM 0) (hM 1)) (hM 2))
    have i5 : Integrable (fun ω ↦ 2 * (μ[f 0 * f 1 * f 2 | m]) ω) μ := (hI hq).const_mul 2
    have i12 : Integrable (fun ω ↦ (μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω +
        (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω) μ := i1.add i2
    have i123 : Integrable (fun ω ↦ (μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω +
        (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω + (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω) μ :=
      i12.add i3
    have i5123 : Integrable (fun ω ↦ 2 * (μ[f 0 * f 1 * f 2 | m]) ω -
        ((μ[f 0 * f 1 | m]) ω * (μ[f 2 | m]) ω + (μ[f 0 * f 2 | m]) ω * (μ[f 1 | m]) ω +
          (μ[f 1 * f 2 | m]) ω * (μ[f 0 | m]) ω)) μ := i5.sub i123
    rw [integral_add i5123 i4, integral_sub i5 i123, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, hE]
    rfl
  -- Collect terms.
  rw [higherCorrelation_fin_three, higherCorrelation_fin_three, hL, hcov 0 1 2, hcov 0 2 1,
    hcov 1 2 0, hE, hE, hE]
  have e1 : ∫ ω, (μ[f 0 | m]) ω * (μ[f 2 | m]) ω * (μ[f 1 | m]) ω ∂μ =
      ∫ ω, (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
  have e2 : ∫ ω, (μ[f 1 | m]) ω * (μ[f 2 | m]) ω * (μ[f 0 | m]) ω ∂μ =
      ∫ ω, (μ[f 0 | m]) ω * (μ[f 1 | m]) ω * (μ[f 2 | m]) ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp only; ring)
  rw [e1, e2]
  ring

/-! ### Two independent fair bits -/

private theorem isProbabilityMeasure_uniformOfFinset_univ :
    IsProbabilityMeasure (Measure.uniformOfFinset (univ : Finset (Bool × Bool))) :=
  ⟨by simp [Measure.uniformOfFinset_apply, ENNReal.div_self]⟩

/-- Under the uniform law on `Bool × Bool` (two independent fair bits), the integral is the
average of the four values. -/
theorem integral_uniformOfFintype_bool_prod (F : Bool × Bool → ℝ) :
    ∫ ω, F ω ∂Measure.uniformOfFinset (univ : Finset (Bool × Bool)) =
      (F (false, false) + F (false, true) + F (true, false) + F (true, true)) / 4 := by
  have : IsProbabilityMeasure (Measure.uniformOfFinset (univ : Finset (Bool × Bool))) :=
    isProbabilityMeasure_uniformOfFinset_univ
  rw [integral_fintype Integrable.of_finite]
  simp [measureReal_def, Fintype.sum_prod_type]
  ring

/-- Under two independent fair bits, the conditional expectation given the second bit averages
over the first. -/
theorem condExp_comap_snd_fairBits (F : Bool × Bool → ℝ) :
    condExp (MeasurableSpace.comap Prod.snd ⊤)
        (Measure.uniformOfFinset (univ : Finset (Bool × Bool))) F =
      fun ω ↦ (F (false, ω.2) + F (true, ω.2)) / 2 := by
  set μ := Measure.uniformOfFinset (univ : Finset (Bool × Bool))
  have : IsProbabilityMeasure μ := isProbabilityMeasure_uniformOfFinset_univ
  have hm : MeasurableSpace.comap Prod.snd ⊤ ≤ (inferInstance : MeasurableSpace (Bool × Bool)) :=
    measurable_snd.comap_le.trans (by rfl)
  set G : Bool × Bool → ℝ := fun ω ↦ (F (false, ω.2) + F (true, ω.2)) / 2
  have hae : G =ᵐ[μ] μ[F | MeasurableSpace.comap Prod.snd ⊤] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm Integrable.of_finite
      (fun _ _ _ ↦ Integrable.of_finite.integrableOn) ?_ ?_
    · rintro s ⟨B, -, rfl⟩ -
      rw [← integral_indicator (measurable_snd ((Set.to_countable B).measurableSet)),
        ← integral_indicator (measurable_snd ((Set.to_countable B).measurableSet)),
        integral_uniformOfFintype_bool_prod, integral_uniformOfFintype_bool_prod]
      by_cases h1 : true ∈ B <;> by_cases h0 : false ∈ B
      all_goals simp [h1, h0, G]
      all_goals ring
    · refine Measurable.aestronglyMeasurable ?_
      exact (measurable_of_countable (fun b : Bool ↦ (F (false, b) + F (true, b)) / 2)).comp
        (Measurable.of_comap_le le_rfl)
  funext ω
  by_contra hω
  have h0 : μ {ω' | G ω' ≠ μ[F | MeasurableSpace.comap Prod.snd ⊤] ω'} = 0 := ae_iff.1 hae
  have hpos : μ {ω} ≠ 0 := by
    simp [μ]
  exact hpos (measure_mono_null (Set.singleton_subset_iff.2 (Ne.symm hω)) h0)

/-- **The covariance sum can be negative.** For two independent fair bits `X, Z` (the uniform
law on `Bool × Bool`), conditioning on `Z`, the nonnegative increasing functions
`f 0 = f 1 = X ∨ Z` and `f 2 = Z` give covariance sum `-1/16`. -/
theorem covariance_sum_fairBits_eq :
    let μ := Measure.uniformOfFinset (univ : Finset (Bool × Bool))
    let m := MeasurableSpace.comap (Prod.snd : Bool × Bool → Bool) ⊤
    let f : Fin 3 → Bool × Bool → ℝ :=
      ![fun ω ↦ if ω.1 || ω.2 then 1 else 0, fun ω ↦ if ω.1 || ω.2 then 1 else 0,
        fun ω ↦ if ω.2 then 1 else 0]
    cov[μ[f 0 * f 1 | m] - μ[f 0 | m] * μ[f 1 | m], μ[f 2 | m]; μ] +
      cov[μ[f 0 * f 2 | m] - μ[f 0 | m] * μ[f 2 | m], μ[f 1 | m]; μ] +
      cov[μ[f 1 * f 2 | m] - μ[f 1 | m] * μ[f 2 | m], μ[f 0 | m]; μ] = -1 / 16 := by
  intro μ m f
  simp only [μ, m, condExp_comap_snd_fairBits, covariance, integral_uniformOfFintype_bool_prod]
  simp [f]
  norm_num

/-- **The covariance sum can be negative for nonnegative increasing functions of independent
fair bits.** Under the uniform law on `Bool × Bool` and conditioning on the second bit, there
are nonnegative coordinatewise increasing `f 0, f 1, f 2` whose covariance sum in
`higherCorrelation_fin_three_eq_condExp` is negative. -/
theorem exists_covariance_sum_neg_fairBits :
    ∃ f : Fin 3 → Bool × Bool → ℝ, (∀ i, 0 ≤ f i) ∧ (∀ i, Monotone (f i)) ∧
      cov[condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0 * f 1) -
            condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0) *
              condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1),
          condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 2);
          Measure.uniformOfFinset univ] +
        cov[condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0 * f 2) -
            condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0) *
              condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 2),
          condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1);
          Measure.uniformOfFinset univ] +
        cov[condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1 * f 2) -
            condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 1) *
              condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 2),
          condExp (MeasurableSpace.comap Prod.snd ⊤) (Measure.uniformOfFinset univ) (f 0);
          Measure.uniformOfFinset univ] < 0 := by
  refine ⟨![fun ω ↦ if ω.1 || ω.2 then 1 else 0, fun ω ↦ if ω.1 || ω.2 then 1 else 0,
    fun ω ↦ if ω.2 then 1 else 0], ?_, ?_, ?_⟩
  · intro i ω
    obtain ⟨a, b⟩ := ω
    fin_cases i <;> cases a <;> cases b <;> simp
  · intro i
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨h1, h2⟩
    fin_cases i <;> cases a1 <;> cases a2 <;> cases b1 <;> cases b2
    all_goals first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | simp
  · rw [covariance_sum_fairBits_eq]
    norm_num

end PercLib
