/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-21. No upstream proof is copied and no definition is added.
Mathematical content: the second-moment truncation bound for the mean, the layer-cake formula
and the intermediate value theorem; standard arguments.
-/
module

public import PercLib.Probability.SizeBias
public import PercLib.Probability.LayerCake
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Integrated lower tails from cubic moments

Let `X t`, for `t` in an interval `I` with least element `t₀`, be nonnegative random variables
whose means `m t` are positive, finite, continuous and unbounded on `I`, with
`E (X t)² ≤ C (m t)³`. If an extended random variable `Xs` stochastically dominates every
`X t`, then `E[Xs ∧ N] ≥ √N / (2 √(2C))` for every real `N ≥ 2 C (m t₀)²`; for an
`ℕ∞`-valued `T` the same bound holds for the tail sum `∑_{n=1}^N P(T ≥ n)`.

## Main results

* `lintegral_le_lintegral_of_meas_lt_le`: stochastic domination in the form
  `μ {x < f} ≤ μ {x < g}` for all `x` gives `∫⁻ f ≤ ∫⁻ g`.
* `lintegral_min_le_lintegral_min_of_meas_lt_le`: the same for truncations `min f c`.
* `exists_mem_eq_of_not_bddAbove`: intermediate values above the value at a point of
  a preconnected set are attained by a continuous function unbounded above on it.
* `le_lintegral_min_of_lintegral_sq_le`: the integrated lower bound `E[Xs ∧ N]`.
* `le_sum_meas_le_of_lintegral_sq_le`: the tail-sum lower bound for `ℕ∞`-valued `T`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Stochastic domination and expectations -/

/-- Stochastic domination `μ {x < f} ≤ μ {x < g}` for every `x` passes to truncations. -/
theorem meas_lt_min_le_meas_lt_min (μ : Measure Ω) {f g : Ω → ℝ≥0∞}
    (h : ∀ x : ℝ≥0∞, μ {ω | x < f ω} ≤ μ {ω | x < g ω}) (c x : ℝ≥0∞) :
    μ {ω | x < min (f ω) c} ≤ μ {ω | x < min (g ω) c} := by
  simp only [lt_min_iff]
  by_cases hx : x < c
  · simpa [hx] using h x
  · simp [hx]

/-- **Stochastic domination bounds expectations.** If `μ {x < f} ≤ μ {x < g}` for every
`x`, then `∫⁻ f ≤ ∫⁻ g`. -/
theorem lintegral_le_lintegral_of_meas_lt_le (μ : Measure Ω) {f g : Ω → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x : ℝ≥0∞, μ {ω | x < f ω} ≤ μ {ω | x < g ω}) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
  -- Layer cake for a truncation at a finite level.
  have key : ∀ F : Ω → ℝ≥0∞, Measurable F → ∀ c : ℝ≥0∞, c ≠ ∞ →
      ∫⁻ ω, min (F ω) c ∂μ = ∫⁻ t in Ioi 0, μ {ω | ENNReal.ofReal t < min (F ω) c} := by
    intro F hF c hc
    have hne : ∀ ω, min (F ω) c ≠ ∞ := fun ω => ne_top_of_le_ne_top hc (min_le_right _ _)
    calc ∫⁻ ω, min (F ω) c ∂μ = ∫⁻ ω, ENNReal.ofReal (min (F ω) c).toReal ∂μ := by
          simp_rw [ENNReal.ofReal_toReal (hne _)]
      _ = ∫⁻ t in Ioi 0, μ {ω | t < (min (F ω) c).toReal} :=
          lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall fun _ => by positivity)
            (hF.min measurable_const).ennreal_toReal.aemeasurable
      _ = ∫⁻ t in Ioi 0, μ {ω | ENNReal.ofReal t < min (F ω) c} := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          congr 1
          ext ω
          exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hne ω)).symm
  have htrunc : ∀ n : ℕ, ∫⁻ ω, min (f ω) n ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
    intro n
    rw [key f hf n (ENNReal.natCast_ne_top n)]
    calc ∫⁻ t in Ioi 0, μ {ω | ENNReal.ofReal t < min (f ω) n}
        ≤ ∫⁻ t in Ioi 0, μ {ω | ENNReal.ofReal t < min (g ω) n} :=
          lintegral_mono fun t => meas_lt_min_le_meas_lt_min μ h _ _
      _ = ∫⁻ ω, min (g ω) n ∂μ := (key g hg n (ENNReal.natCast_ne_top n)).symm
      _ ≤ ∫⁻ ω, g ω ∂μ := lintegral_mono fun ω => min_le_left _ _
  have hsup : (fun ω => f ω) = fun ω => ⨆ n : ℕ, min (f ω) n := by
    funext ω
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  rw [hsup, lintegral_iSup (fun n => hf.min measurable_const)
    fun m n hmn ω => min_le_min_left _ (by exact_mod_cast hmn)]
  exact iSup_le htrunc

/-- **Stochastic domination bounds truncated expectations.** If `μ {x < f} ≤ μ {x < g}` for
every `x`, then `∫⁻ min f c ≤ ∫⁻ min g c` for every level `c`. -/
theorem lintegral_min_le_lintegral_min_of_meas_lt_le (μ : Measure Ω) {f g : Ω → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ x : ℝ≥0∞, μ {ω | x < f ω} ≤ μ {ω | x < g ω}) (c : ℝ≥0∞) :
    ∫⁻ ω, min (f ω) c ∂μ ≤ ∫⁻ ω, min (g ω) c ∂μ :=
  lintegral_le_lintegral_of_meas_lt_le μ (hf.min measurable_const) (hg.min measurable_const)
    (meas_lt_min_le_meas_lt_min μ h c)

/-! ### Choosing the parameter -/

/-- On a preconnected set, a function continuous and unbounded above attains every value
above its value at a point of the set. -/
theorem exists_mem_eq_of_not_bddAbove {I : Set ℝ} (hI : IsPreconnected I) {f : ℝ → ℝ}
    (hf : ContinuousOn f I) (hunb : ¬BddAbove (f '' I)) {a : ℝ} (ha : a ∈ I) {y : ℝ}
    (hy : f a ≤ y) : ∃ t ∈ I, f t = y := by
  obtain ⟨_, ⟨b, hb, rfl⟩, hyb⟩ := not_bddAbove_iff.mp hunb y
  obtain ⟨t, ht, hft⟩ := hI.intermediate_value ha hb hf ⟨hy, hyb.le⟩
  exact ⟨t, ht, hft⟩

/-! ### The integrated lower bound -/

/-- **Integrated square-root lower bound.** Let `X t`, for `t` in an order-connected set `I`
with least element `t₀`, be nonnegative random variables with means `m t ∈ (0, ∞)`,
continuous and unbounded above on `I`, and `E (X t)² ≤ C (m t)³`. If `Xs` stochastically
dominates every `X t`, then `E[Xs ∧ N] ≥ √N / (2 √(2C))` for every real `N ≥ 2 C (m t₀)²`. -/
theorem le_lintegral_min_of_lintegral_sq_le (P : Measure Ω) {I : Set ℝ} {t₀ : ℝ}
    (hI : IsLeast I t₀) (hIc : I.OrdConnected) {X : ℝ → Ω → ℝ}
    (hXm : ∀ t ∈ I, Measurable (X t)) {m : ℝ → ℝ≥0∞}
    (hm : ∀ t ∈ I, m t = ∫⁻ ω, ENNReal.ofReal (X t ω) ∂P)
    (hpos : ∀ t ∈ I, 0 < m t) (hfin : ∀ t ∈ I, m t < ∞) {C : ℝ} (hC : 0 < C)
    (hsq : ∀ t ∈ I, ∫⁻ ω, ENNReal.ofReal (X t ω) ^ 2 ∂P ≤ ENNReal.ofReal C * m t ^ 3)
    (hcont : ContinuousOn (fun t => (m t).toReal) I)
    (hunb : ¬BddAbove ((fun t => (m t).toReal) '' I))
    {Xs : Ω → ℝ≥0∞} (hXs : Measurable Xs)
    (hdom : ∀ t ∈ I, ∀ x : ℝ≥0∞, P {ω | x < ENNReal.ofReal (X t ω)} ≤ P {ω | x < Xs ω})
    {N : ℝ} (hN : 2 * C * (m t₀).toReal ^ 2 ≤ N) :
    ENNReal.ofReal (Real.sqrt N / (2 * Real.sqrt (2 * C))) ≤
      ∫⁻ ω, min (Xs ω) (ENNReal.ofReal N) ∂P := by
  have h2C : 0 < 2 * C := by positivity
  have hm0' : 0 < (m t₀).toReal :=
    ENNReal.toReal_pos (hpos t₀ hI.1).ne' (hfin t₀ hI.1).ne
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  set s := Real.sqrt (N / (2 * C)) with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr (div_pos hNpos h2C)
  have hss : s ^ 2 = N / (2 * C) := Real.sq_sqrt (div_pos hNpos h2C).le
  have hys : (m t₀).toReal ≤ s := by
    rw [hs_def]
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ h2C]
    linarith
  obtain ⟨t, ht, hts⟩ :=
    exists_mem_eq_of_not_bddAbove hIc.isPreconnected hcont hunb hI.1 hys
  have hmt : m t = ENNReal.ofReal s := by
    rw [← hts, ENNReal.ofReal_toReal (hfin t ht).ne]
  -- The truncation bound with `l = 2` at the parameter `t`.
  have hμ : ∫⁻ ω, ENNReal.ofReal (X t ω) ∂P ≠ ∞ := by rw [← hm t ht]; exact (hfin t ht).ne
  have hthr : 2 * (∫⁻ ω, ENNReal.ofReal (X t ω) ^ 2 ∂P) / (∫⁻ ω, ENNReal.ofReal (X t ω) ∂P) ≤
      ENNReal.ofReal N := by
    rw [← hm t ht]
    refine ENNReal.div_le_of_le_mul ?_
    calc 2 * ∫⁻ ω, ENNReal.ofReal (X t ω) ^ 2 ∂P ≤ 2 * (ENNReal.ofReal C * m t ^ 3) := by
          gcongr; exact hsq t ht
      _ = ENNReal.ofReal (2 * C * s ^ 2) * m t := by
          rw [ENNReal.ofReal_mul h2C.le, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow
            hs0.le, ← hmt, ENNReal.ofReal_ofNat]
          ring
      _ = ENNReal.ofReal N * m t := by
          rw [hss, mul_div_cancel₀ _ h2C.ne']
  have htr := le_lintegral_min P (hXm t ht).ennreal_ofReal hμ (l := 2) ENNReal.one_lt_two hthr
  have hval : (1 - (2 : ℝ≥0∞)⁻¹) * ∫⁻ ω, ENNReal.ofReal (X t ω) ∂P =
      ENNReal.ofReal (Real.sqrt N / (2 * Real.sqrt (2 * C))) := by
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
    rw [← hm t ht, hmt, ENNReal.one_sub_inv_two, h2, ← ENNReal.ofReal_mul (by norm_num), hs_def,
      Real.sqrt_div' _ h2C.le]
    congr 1
    field_simp
  rw [← hval]
  exact htr.trans (lintegral_min_le_lintegral_min_of_meas_lt_le P
    (hXm t ht).ennreal_ofReal hXs (hdom t ht) _)

/-- **Integrated square-root lower bound for an `ℕ∞`-valued variable.** Under the hypotheses
of `le_lintegral_min_of_lintegral_sq_le`, if `T : Ω → ℕ∞` stochastically dominates every
`X t`, then `∑_{n=1}^N P(T ≥ n) ≥ √N / (2 √(2C))` for every integer `N ≥ 2 C (m t₀)²`. -/
theorem le_sum_meas_le_of_lintegral_sq_le (P : Measure Ω) {I : Set ℝ} {t₀ : ℝ}
    (hI : IsLeast I t₀) (hIc : I.OrdConnected) {X : ℝ → Ω → ℝ}
    (hXm : ∀ t ∈ I, Measurable (X t)) {m : ℝ → ℝ≥0∞}
    (hm : ∀ t ∈ I, m t = ∫⁻ ω, ENNReal.ofReal (X t ω) ∂P)
    (hpos : ∀ t ∈ I, 0 < m t) (hfin : ∀ t ∈ I, m t < ∞) {C : ℝ} (hC : 0 < C)
    (hsq : ∀ t ∈ I, ∫⁻ ω, ENNReal.ofReal (X t ω) ^ 2 ∂P ≤ ENNReal.ofReal C * m t ^ 3)
    (hcont : ContinuousOn (fun t => (m t).toReal) I)
    (hunb : ¬BddAbove ((fun t => (m t).toReal) '' I))
    {T : Ω → ℕ∞} (hT : Measurable T)
    (hdom : ∀ t ∈ I, ∀ x : ℝ≥0∞,
      P {ω | x < ENNReal.ofReal (X t ω)} ≤ P {ω | x < (T ω : ℝ≥0∞)})
    {N : ℕ} (hN : 2 * C * (m t₀).toReal ^ 2 ≤ N) :
    ENNReal.ofReal (Real.sqrt N / (2 * Real.sqrt (2 * C))) ≤
      ∑ n ∈ Finset.Icc 1 N, P {ω | (n : ℕ∞) ≤ T ω} := by
  have hTm : Measurable fun ω => (T ω : ℝ≥0∞) := (measurable_of_countable _).comp hT
  have h := le_lintegral_min_of_lintegral_sq_le P hI hIc hXm hm hpos hfin hC hsq hcont hunb
    hTm hdom hN
  have hmin : ∀ ω, min (T ω : ℝ≥0∞) (ENNReal.ofReal N) = ((min (T ω) N : ℕ∞) : ℝ≥0∞) :=
    fun ω => by rw [ENat.toENNReal_min, ENNReal.ofReal_natCast, ENat.toENNReal_coe]
  simp_rw [hmin] at h
  rw [lintegral_min_eq_sum hT] at h
  refine h.trans_eq ?_
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n : ℕ => P {ω | (n : ℕ∞) ≤ T ω}) 0 N 1,
    zero_add, Finset.Ico_add_one_right_eq_Icc]

end PercLib.Probability
