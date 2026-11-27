/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the Galton–Watson interface of `PercLib.Probability.GaltonWatson.Defs`. No
source text or code is copied. Mathematical reference: the total progeny of a critical
branching process; Athreya and Ney, *Branching Processes*, Chapter I.13.
-/
module

public import PercLib.Probability.GaltonWatsonTotalProgeny
public import PercLib.Probability.LaplaceTail
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# The tail of the total progeny of a critical Galton–Watson process

For mean one and variance `σ² ∈ (0, ∞)`, `P(T ≥ n)` has order `n^{-1/2}`. The Laplace
deficit `G(t) = E[1 - e^{-tT}]` equals `1 - F(e^{-t})`, where `F(s) = E[s^T]`; the transform
asymptotic gives `G(t)/√t → √(2/σ²)`, and `exists_tail_bounds_of_laplace` turns this into
two-sided tail bounds.

## Main results

* `exists_enat_totalProgeny`: the total progeny as a measurable `ℕ∞`-valued variable.
* `tendsto_laplace_totalProgeny_div_sqrt`: `G(t)/√t → √(2/σ²)` as `t ↓ 0`.
* `exists_measure_totalProgeny_ge_bounds`: there are `c, C > 0` and `N` with
  `c/√n ≤ P(T ≥ n) ≤ C/√n` for `n ≥ N`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace PercLib.Probability

variable (p : PMF ℕ)

/-- The total progeny is the `ℝ≥0∞`-image of a measurable `ℕ∞`-valued variable. -/
theorem exists_enat_totalProgeny :
    ∃ T : (ℕ → ℕ → ℕ) → ℕ∞, Measurable T ∧ ∀ ω, (T ω : ℝ≥0∞) = totalProgeny ω := by
  set T : (ℕ → ℕ → ℕ) → ℕ∞ :=
    fun ω => ⨆ n, ((∑ i ∈ Finset.range n, generationSize i ω : ℕ) : ℕ∞) with hTdef
  have hc : ∀ ω, (T ω : ℝ≥0∞) = totalProgeny ω := fun ω => by
    rw [hTdef]
    dsimp only
    rw [ENat.toENNReal_iSup, totalProgeny_def, ENNReal.tsum_eq_iSup_nat]
    congr 1
    funext n
    rw [ENat.toENNReal_coe, Nat.cast_sum]
  refine ⟨T, measurable_to_countable' fun x => ?_, hc⟩
  have : T ⁻¹' {x} = totalProgeny ⁻¹' {(x : ℝ≥0∞)} := by
    ext ω
    simp [← hc ω, ENat.toENNReal_inj]
  rw [this]
  exact measurable_totalProgeny (measurableSet_singleton _)

/-- **Laplace deficit.** If `m = 1` and the variance `σ²` is finite and positive, then
`E[1 - e^{-tT}]/√t → √(2/σ²)` as `t ↓ 0`. -/
theorem tendsto_laplace_totalProgeny_div_sqrt (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2)
    {T : (ℕ → ℕ → ℕ) → ℕ∞} (hTm : Measurable T) (hTc : ∀ ω, (T ω : ℝ≥0∞) = totalProgeny ω) :
    Tendsto (fun t : ℝ =>
      (∫⁻ ω, (1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal))))
        ∂galtonWatsonMeasure p).toReal / Real.sqrt t) (𝓝[>] 0) (𝓝 (Real.sqrt (2 / σ2))) := by
  set μ := galtonWatsonMeasure p
  set F : ℝ → ℝ := fun s =>
    ∑' k : ℕ, (μ {ω | totalProgeny ω = k}).toReal * s ^ k with hFdef
  have hmeasT : ∀ k : ℕ, MeasurableSet {ω : ℕ → ℕ → ℕ | totalProgeny ω = k} := fun k =>
    measurableSet_eq_fun measurable_totalProgeny measurable_const
  -- the Laplace deficit is `1 - F(e^{-t})`
  have hG : ∀ t : ℝ, 0 < t →
      (∫⁻ ω, (1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal =
        1 - F (Real.exp (-t)) := by
    intro t ht
    set E : (ℕ → ℕ → ℕ) → ℝ≥0∞ :=
      fun ω => EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal))) with hEdef
    have hval : ∀ ω, E ω = ∑' k : ℕ, {ω' | totalProgeny ω' = k}.indicator
        (fun _ => ENNReal.ofReal (Real.exp (-t)) ^ k) ω ∧ E ω ≤ 1 := by
      intro ω
      by_cases h : T ω = ⊤
      · have hE : E ω = 0 := by
          rw [hEdef]
          dsimp only
          rw [h, ENat.toENNReal_top, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos ht,
            EReal.neg_top, EReal.exp_bot]
        refine ⟨hE.trans (ENNReal.tsum_eq_zero.2 fun k => ?_).symm, hE ▸ zero_le⟩
        simp [← hTc ω, h]
      · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
        have hE : E ω = ENNReal.ofReal (Real.exp (-t)) ^ m := by
          rw [hEdef]
          dsimp only
          rw [← hm, laplace_exp_natCast, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
            ← Real.exp_nat_mul]
          congr 2
          ring
        refine ⟨?_, hE ▸ pow_le_one₀ zero_le (ENNReal.ofReal_le_one.2
          (Real.exp_le_one_iff.2 (by linarith)))⟩
        rw [hE, tsum_eq_single m fun j hj => ?_]
        · rw [indicator_of_mem]
          change totalProgeny ω = m
          rw [← hTc ω, ← hm, ENat.toENNReal_coe]
        · rw [indicator_of_notMem]
          change ¬ totalProgeny ω = j
          rw [← hTc ω, ← hm, ENat.toENNReal_coe, Nat.cast_inj]
          exact Ne.symm hj
    have hEm : Measurable E :=
      (measurable_of_countable (fun T : ℕ∞ => EReal.exp (-((t : EReal) *
        ((T : ℝ≥0∞) : EReal))))).comp hTm
    have hint : ∫⁻ ω, E ω ∂μ =
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-t)) ^ k * μ {ω | totalProgeny ω = k} := by
      rw [lintegral_congr fun ω => (hval ω).1,
        lintegral_tsum fun k => (measurable_const.indicator (hmeasT k)).aemeasurable]
      exact tsum_congr fun k => lintegral_indicator_const (hmeasT k) _
    have hle : ∫⁻ ω, E ω ∂μ ≤ 1 :=
      (lintegral_mono fun ω => (hval ω).2).trans_eq (by simp)
    have hsub : ∫⁻ ω, (1 - E ω) ∂μ = 1 - ∫⁻ ω, E ω ∂μ := by
      rw [lintegral_sub hEm (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
        (Eventually.of_forall fun ω => (hval ω).2)]
      simp
    change (∫⁻ ω, (1 - E ω) ∂μ).toReal = _
    rw [hsub, ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one, hint,
      ENNReal.tsum_toReal_eq fun k => ENNReal.mul_ne_top
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (measure_ne_top _ _)]
    congr 1
    exact tsum_congr fun k => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.exp_pos _).le,
        mul_comm]
  -- the analytic limit
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (Real.continuous_exp.comp continuous_neg).tendsto (0 : ℝ)
      simp only [Function.comp_apply, neg_zero, Real.exp_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact Real.exp_lt_one_iff.2 (by linarith)
  have h1 := (isEquivalent_one_sub_tsum_measureReal_totalProgeny p hm hσ hσ0).comp_tendsto hexp
  have h1' := h1.div (IsEquivalent.refl (u := fun t : ℝ => Real.sqrt t))
  have h2 : Tendsto (fun t : ℝ => Real.sqrt (2 * (1 - Real.exp (-t)) / σ2) / Real.sqrt t)
      (𝓝[>] 0) (𝓝 (Real.sqrt (2 / σ2))) := by
    have := ((tendsto_one_sub_exp_neg_div).const_mul (2 / σ2)).sqrt
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [← Real.sqrt_div' _ ht.le]
    congr 1
    field_simp
  have h3 := h1'.symm.tendsto_nhds h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [Pi.div_apply, Function.comp_apply]
  rw [hG t ht]

/-- **Critical total-progeny tail.** If `m = 1` and the variance `σ²` is finite and
positive, there are `c, C > 0` and `N` such that `c/√n ≤ P(T ≥ n) ≤ C/√n` for all `n ≥ N`. -/
theorem exists_measure_totalProgeny_ge_bounds (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1)
    {σ2 : ℝ} (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2)
    (hσ0 : 0 < σ2) :
    ∃ c > 0, ∃ C > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c / Real.sqrt n ≤ (galtonWatsonMeasure p {ω | (n : ℝ≥0∞) ≤ totalProgeny ω}).toReal ∧
        (galtonWatsonMeasure p {ω | (n : ℝ≥0∞) ≤ totalProgeny ω}).toReal ≤
          C / Real.sqrt n := by
  obtain ⟨T, hTm, hTc⟩ := exists_enat_totalProgeny
  obtain ⟨C, hC, c, hc, N, hup, hlow⟩ := exists_tail_bounds_of_laplace hTm
    (Real.sqrt_pos.2 (by positivity)) (tendsto_laplace_totalProgeny_div_sqrt p hm hσ hσ0 hTm hTc)
  have hev : ∀ n : ℕ, {ω | (n : ℝ≥0∞) ≤ totalProgeny ω} = {ω | (n : ℕ∞) ≤ T ω} := fun n => by
    ext ω
    change (n : ℝ≥0∞) ≤ totalProgeny ω ↔ (n : ℕ∞) ≤ T ω
    rw [← hTc ω, ← ENat.toENNReal_coe, ENat.toENNReal_le]
  refine ⟨c, hc, C, hC, max N 1, fun n hn => ?_⟩
  rw [hev]
  exact ⟨hlow n (le_of_max_le_left hn), hup n (le_of_max_le_right hn)⟩

end PercLib.Probability
