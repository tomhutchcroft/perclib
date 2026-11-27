/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the Galton–Watson interface of `PercLib.Probability.GaltonWatson.Defs`. No
source text or code is copied. Mathematical reference: Kolmogorov's estimate for critical
branching processes; Athreya and Ney, *Branching Processes*, Chapter I.9.
-/
module

public import PercLib.Probability.GaltonWatson
public import PercLib.Probability.OffspringTransform
public import PercLib.Analysis.QuadraticRecursion

/-!
# Survival of a critical Galton–Watson process to generation `n`

Let `p : PMF ℕ` have mean `m = 1` and variance `σ² ∈ (0, ∞)`, and let
`φ(s) = ∑ₖ p(k) sᵏ`. Then `rₙ = P(Zₙ > 0) = 1 - φⁿ(0)` satisfies `rₙ₊₁ = 1 - φ(1 - rₙ)`,
`rₙ > 0` and `rₙ → 0`, so the quadratic recursion lemma gives `n rₙ → 2/σ²`.

## Main results

* `hasSum_mul_sub_one_of_hasSum_variance`: for mean one, the variance equals the second
  factorial moment `∑ k(k-1) p(k)`.
* `genFun_lt_one`: `φ(s) < 1` for `0 ≤ s < 1` when `p(0) ≠ 1`.
* `measureReal_generationSize_pos`: `P(Zₙ > 0) = 1 - φⁿ(0)`.
* `tendsto_natCast_mul_measureReal_generationSize_pos`: `n P(Zₙ > 0) → 2/σ²`.
* `isEquivalent_measureReal_generationSize_pos`: `P(Zₙ > 0) ~ 2/(σ² n)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal

namespace PercLib.Probability

variable (p : PMF ℕ)

/-- For an offspring law of mean one, the variance `∑ (k-1)² p(k)` equals the second factorial
moment `∑ k(k-1) p(k)`. -/
theorem hasSum_mul_sub_one_of_hasSum_variance (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) σ2 := by
  have h1 := hasSum_mean_one p hm
  have h0 := (summable_pmf_toReal p).hasSum
  rw [tsum_pmf_toReal] at h0
  convert (hσ.add h1).sub h0 using 1
  · funext k
    ring
  · ring

/-- An offspring law with nonzero mean charges some `k ≠ 0`. -/
theorem exists_ne_zero_apply_ne_zero (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k ≠ 0) :
    ∃ k, k ≠ 0 ∧ p k ≠ 0 := by
  by_contra h
  push Not at h
  refine hm (ENNReal.tsum_eq_zero.2 fun k => ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [h k hk]

/-- If `p` charges some `k ≠ 0`, then `φ(s) < 1` for `0 ≤ s < 1`. -/
theorem genFun_lt_one {k : ℕ} (hk : k ≠ 0) (hpk : p k ≠ 0) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : ∑' j, (p j).toReal * s ^ j < 1 := by
  rw [← genFun_one p]
  refine Summable.tsum_lt_tsum (i := k) (fun j => ?_) ?_ (summable_genFun p ⟨hs0, hs1.le⟩)
    (summable_genFun p ⟨zero_le_one, le_rfl⟩)
  · exact mul_le_mul_of_nonneg_left (by rw [one_pow]; exact pow_le_one₀ hs0 hs1.le)
      ENNReal.toReal_nonneg
  · rw [one_pow, mul_one]
    exact mul_lt_of_lt_one_right (ENNReal.toReal_pos hpk (PMF.apply_ne_top p k))
      (pow_lt_one₀ hs0 hs1 hk)

/-- If `p` charges some `k ≠ 0`, every iterate `φⁿ(0)` lies in `[0, 1)`. -/
theorem iterate_genFun_zero_mem_Ico {k : ℕ} (hk : k ≠ 0) (hpk : p k ≠ 0) (n : ℕ) :
    (fun s : ℝ => ∑' j, (p j).toReal * s ^ j)^[n] 0 ∈ Ico (0 : ℝ) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨genFun_nonneg p ih.1, genFun_lt_one p hk hpk ih.1 ih.2⟩

/-- **`P(Zₙ > 0) = 1 - φⁿ(0)`.** -/
theorem measureReal_generationSize_pos (n : ℕ) :
    (galtonWatsonMeasure p {ω | 0 < generationSize n ω}).toReal =
      1 - (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0 := by
  have hE : MeasurableSet {ω : ℕ → ℕ → ℕ | generationSize n ω = 0} :=
    measurableSet_eq_fun (measurable_generationSize n) measurable_const
  have hc : {ω : ℕ → ℕ → ℕ | 0 < generationSize n ω} =
      {ω | generationSize n ω = 0}ᶜ := by
    ext ω
    simp [Nat.pos_iff_ne_zero]
  rw [hc, prob_compl_eq_one_sub hE, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, measureReal_generationSize_eq_zero]

/-- If `m = 1` and `p(1) ≠ 1`, then `φⁿ(0) → 1`. -/
theorem tendsto_iterate_genFun_zero_one (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) (h1 : p 1 ≠ 1) :
    Tendsto (fun n => (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := galtonWatsonMeasure p)
    (monotone_setOf_generationSize_eq_zero)
  have hU : (⋃ n, {ω : ℕ → ℕ → ℕ | generationSize n ω = 0}) =
      {ω | ∃ n, generationSize n ω = 0} := by
    ext ω
    simp
  rw [hU, galtonWatsonMeasure_extinction_eq_one_of_mean_eq_one p hm h1] at h
  have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  rw [ENNReal.toReal_one] at h'
  refine h'.congr fun n => ?_
  simp only [Function.comp_apply]
  exact measureReal_generationSize_eq_zero p n

/-- **Kolmogorov's estimate.** If `m = 1` and the variance `σ²` is finite and positive, then
`n P(Zₙ > 0) → 2/σ²`. -/
theorem tendsto_natCast_mul_measureReal_generationSize_pos
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    Tendsto (fun n : ℕ => (n : ℝ) * (galtonWatsonMeasure p {ω | 0 < generationSize n ω}).toReal)
      atTop (𝓝 (2 / σ2)) := by
  have hσ' := hasSum_mul_sub_one_of_hasSum_variance p hm hσ
  obtain ⟨k, hk, hpk⟩ := exists_ne_zero_apply_ne_zero p (by rw [hm]; exact one_ne_zero)
  have h := PercLib.Analysis.tendsto_mul_of_quadratic_recursion (a := σ2 / 2)
    (ψ := fun u => 1 - ∑' k, (p k).toReal * (1 - u) ^ k) (by positivity)
    (tendsto_one_sub_genFun_expansion p hm hσ')
    (r := fun n => (galtonWatsonMeasure p {ω | 0 < generationSize n ω}).toReal)
    (fun n => by
      rw [measureReal_generationSize_pos]
      linarith [(iterate_genFun_zero_mem_Ico p hk hpk n).2])
    (fun n => by
      simp only [measureReal_generationSize_pos, sub_sub_cancel, Function.iterate_succ_apply'])
    (by
      have := (tendsto_iterate_genFun_zero_one p hm
        (apply_one_ne_one_of_hasSum p hσ' hσ0)).const_sub 1
      rw [sub_self] at this
      exact this.congr fun n => (measureReal_generationSize_pos p n).symm)
  rwa [one_div_div] at h

/-- **Kolmogorov's estimate, asymptotic form.** If `m = 1` and the variance `σ²` is finite
and positive, then `P(Zₙ > 0) ~ 2/(σ² n)`. -/
theorem isEquivalent_measureReal_generationSize_pos
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    (fun n : ℕ => (galtonWatsonMeasure p {ω | 0 < generationSize n ω}).toReal) ~[atTop]
      fun n : ℕ => 2 / (σ2 * n) := by
  refine isEquivalent_of_tendsto_one ?_
  have h := (tendsto_natCast_mul_measureReal_generationSize_pos p hm hσ hσ0).mul_const
    (σ2 / 2)
  rw [div_mul_div_comm, mul_comm 2 σ2, div_self (by positivity)] at h
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp only [Pi.div_apply]
  field_simp

end PercLib.Probability
