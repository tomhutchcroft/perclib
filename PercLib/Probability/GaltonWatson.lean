/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. Reference: K. B. Athreya and P. E. Ney, *Branching
Processes*, Springer, 1972, Chapter I, §§2–5. No upstream proof is copied.
-/
module

public import PercLib.Probability.GaltonWatson.Defs
public import PercLib.Probability.GeneratingFunction
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Generation means and extinction of the Galton–Watson process

For an offspring law `p : PMF ℕ` write `φ(s) = ∑ₖ p(k) sᵏ` and `m = ∑ₖ k p(k) ∈ [0, ∞]`.
The generation size `Zₙ` depends only on the offspring variables of generations `< n`, which
are independent of those of generation `n`; this gives the one-step identity
`E g(Z_{n+1}) = E ∫ g(∑_{j < Zₙ} yⱼ) dp^{⊗ℕ}(y)` (`lintegral_comp_generationSize_succ`).

## Main results

* `lintegral_pow_generationSize`: `E s^{Zₙ} = φⁿ(s)` for `s ∈ [0, ∞]`.
* `galtonWatsonMeasure_generationSize_eq_zero`: `P(Zₙ = 0) = φⁿ(0)`.
* `isLeast_galtonWatsonMeasure_extinction`: the extinction probability
  `q = P(∃ n, Zₙ = 0)` is the least solution of `φ(s) = s` in `[0, 1]`.
* `galtonWatsonMeasure_extinction_eq_one_iff`: extinction is almost sure exactly when `m ≤ 1`
  and `p(1) ≠ 1`; if `p(1) = 1` then `Zₙ = 1` for all `n` almost surely
  (`ae_forall_generationSize_eq_one`); if `m > 1` survival has positive probability
  (`galtonWatsonMeasure_extinction_lt_one_of_one_lt_mean`).
* `lintegral_generationSize`: `E Zₙ = mⁿ`.
* `lintegral_totalProgeny`: `E T = (1 - m)⁻¹` in `[0, ∞]`, and
  `lintegral_totalProgeny_eq_ite`: `E T = (1 - m)⁻¹` if `m < 1` and `E T = ∞` if `m ≥ 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace PercLib.Probability

variable (p : PMF ℕ)

/-! ### Independence of a generation from its offspring variables -/

/-- The offspring variables of generation `n` have the product law `p^{⊗ℕ}`. -/
theorem measurePreserving_eval_galtonWatsonMeasure (n : ℕ) :
    MeasurePreserving (fun ω : ℕ → ℕ → ℕ => ω n) (galtonWatsonMeasure p)
      (Measure.infinitePi fun _ : ℕ => p.toMeasure) :=
  measurePreserving_eval_infinitePi _ n

/-- The generations of offspring variables are independent. -/
theorem iIndepFun_eval_galtonWatsonMeasure :
    iIndepFun (fun (n : ℕ) (ω : ℕ → ℕ → ℕ) => ω n) (galtonWatsonMeasure p) :=
  iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id

/-- **`Zₙ` is independent of the offspring variables of generation `n`.** -/
theorem indepFun_generationSize_eval (n : ℕ) :
    IndepFun (generationSize n) (fun ω : ℕ → ℕ → ℕ => ω n) (galtonWatsonMeasure p) := by
  classical
  have h := (iIndepFun_eval_galtonWatsonMeasure p).indepFun_finset (Finset.range n) {n}
    (by simp) fun i => measurable_pi_apply i
  let ext : (Finset.range n → ℕ → ℕ) → ℕ → ℕ → ℕ := fun r i =>
    if hi : i ∈ Finset.range n then r ⟨i, hi⟩ else 0
  have hext : Measurable ext := by
    refine measurable_pi_iff.2 fun i => ?_
    by_cases hi : i ∈ Finset.range n
    · simp only [ext, hi, dite_true]; exact measurable_pi_apply _
    · simp only [ext, hi, dite_false]; exact measurable_const
  have h' := h.comp ((measurable_generationSize n).comp hext)
    (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  refine h'.congr (Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => rfl)
  refine generationSize_congr fun i hi => ?_
  simp [ext, hi]

/-- **One-step identity.** For every `g : ℕ → [0, ∞]`,
`E g(Z_{n+1}) = E ∫ g(∑_{j < Zₙ} yⱼ) dp^{⊗ℕ}(y)`. -/
theorem lintegral_comp_generationSize_succ (g : ℕ → ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, g (generationSize (n + 1) ω) ∂galtonWatsonMeasure p =
      ∫⁻ ω, ∫⁻ y, g (∑ j ∈ Finset.range (generationSize n ω), y j)
        ∂Measure.infinitePi (fun _ : ℕ => p.toMeasure) ∂galtonWatsonMeasure p := by
  set μ := galtonWatsonMeasure p
  set ν := Measure.infinitePi fun _ : ℕ => p.toMeasure
  set F : ℕ × (ℕ → ℕ) → ℝ≥0∞ := fun x => g (∑ j ∈ Finset.range x.1, x.2 j) with hF
  have hFm : Measurable F := measurable_from_prod_countable_right fun k =>
    show Measurable fun y : ℕ → ℕ => g (∑ j ∈ Finset.range k, y j) from
      (measurable_from_nat (f := g)).comp
        (Finset.measurable_sum (Finset.range k) fun j _ => measurable_pi_apply j)
  have hZ := measurable_generationSize n
  have hrow : Measurable fun ω : ℕ → ℕ → ℕ => ω n := measurable_pi_apply n
  have hmap := (indepFun_generationSize_eval p n).map_prod_eq_prod_map_map hZ.aemeasurable
    hrow.aemeasurable
  rw [(measurePreserving_eval_galtonWatsonMeasure p n).map_eq] at hmap
  have hL : ∫⁻ ω, g (generationSize (n + 1) ω) ∂μ =
      ∫⁻ x, F x ∂μ.map fun ω => (generationSize n ω, ω n) := by
    rw [lintegral_map hFm (hZ.prodMk hrow)]
    rfl
  rw [hL, hmap, lintegral_prod _ hFm.aemeasurable, lintegral_map _ hZ]
  exact measurable_from_nat

/-- `∫ s^x dp(x) = φ(s)`. -/
theorem lintegral_pow_pmf (s : ℝ≥0∞) : ∫⁻ x, s ^ x ∂p.toMeasure = ∑' k, p k * s ^ k := by
  rw [lintegral_countable']
  exact tsum_congr fun k => by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k), mul_comm]

/-- `∫ x dp(x) = m`. -/
theorem lintegral_natCast_pmf : ∫⁻ x, (x : ℝ≥0∞) ∂p.toMeasure = ∑' k : ℕ, (k : ℝ≥0∞) * p k := by
  rw [lintegral_countable']
  exact tsum_congr fun k => by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]

/-! ### Generating functions and extinction -/

/-- `E s^{Z_{n+1}} = E φ(s)^{Zₙ}`. -/
theorem lintegral_pow_generationSize_succ (s : ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, s ^ generationSize (n + 1) ω ∂galtonWatsonMeasure p =
      ∫⁻ ω, (∑' k, p k * s ^ k) ^ generationSize n ω ∂galtonWatsonMeasure p := by
  rw [lintegral_comp_generationSize_succ p (fun k => s ^ k) n]
  refine lintegral_congr fun ω => ?_
  set ν := Measure.infinitePi fun _ : ℕ => p.toMeasure
  have hind : iIndepFun (fun (j : ℕ) (y : ℕ → ℕ) => s ^ y j) ν :=
    iIndepFun_infinitePi (X := fun _ x => s ^ x) fun _ => measurable_from_nat
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind
    fun j => measurable_from_nat.comp (measurable_pi_apply j)]
  have hj : ∀ j, ∫⁻ y, s ^ y j ∂ν = ∑' k, p k * s ^ k := fun j => by
    rw [← lintegral_pow_pmf p s,
      ← (measurePreserving_eval_infinitePi (fun _ : ℕ => p.toMeasure) j).map_eq,
      lintegral_map measurable_from_nat (measurable_pi_apply j)]
  simp [hj]

/-- **`E s^{Zₙ} = φⁿ(s)`** for every `s ∈ [0, ∞]`. -/
theorem lintegral_pow_generationSize (n : ℕ) (s : ℝ≥0∞) :
    ∫⁻ ω, s ^ generationSize n ω ∂galtonWatsonMeasure p =
      (fun t : ℝ≥0∞ => ∑' k, p k * t ^ k)^[n] s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih => rw [lintegral_pow_generationSize_succ, ih, Function.iterate_succ_apply]

/-- **`P(Zₙ = 0) = φⁿ(0)`.** -/
theorem galtonWatsonMeasure_generationSize_eq_zero (n : ℕ) :
    galtonWatsonMeasure p {ω | generationSize n ω = 0} =
      (fun t : ℝ≥0∞ => ∑' k, p k * t ^ k)^[n] 0 := by
  rw [← lintegral_pow_generationSize, ← lintegral_indicator_one
    (s := {ω | generationSize n ω = 0})
    (measurableSet_eq_fun (measurable_generationSize n) measurable_const)]
  refine lintegral_congr fun ω => ?_
  by_cases h : generationSize n ω = 0 <;> simp [h]

/-- On `[0, 1]` the extended generating function takes values in `[0, 1]`. -/
theorem genFun_ennreal_le_one {s : ℝ≥0∞} (hs : s ≤ 1) : ∑' k, p k * s ^ k ≤ 1 :=
  (ENNReal.tsum_le_tsum fun _ => mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hs)
    ).trans_eq p.tsum_coe

/-- On `[0, 1]` the extended generating function agrees with the real one. -/
theorem toReal_genFun_ennreal {s : ℝ≥0∞} (hs : s ≤ 1) :
    (∑' k, p k * s ^ k).toReal = ∑' k, (p k).toReal * s.toReal ^ k := by
  have hs' : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
  rw [ENNReal.tsum_toReal_eq fun k => ENNReal.mul_ne_top (PMF.apply_ne_top p k)
    (ENNReal.pow_ne_top hs')]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

/-- `P(Zₙ = 0) = φⁿ(0)` with the real generating function. -/
theorem measureReal_generationSize_eq_zero (n : ℕ) :
    (galtonWatsonMeasure p {ω | generationSize n ω = 0}).toReal =
      (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0 := by
  rw [galtonWatsonMeasure_generationSize_eq_zero]
  have key : ∀ n, (fun t : ℝ≥0∞ => ∑' k, p k * t ^ k)^[n] 0 ≤ 1 ∧
      ((fun t : ℝ≥0∞ => ∑' k, p k * t ^ k)^[n] 0).toReal =
        (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨genFun_ennreal_le_one p ih.1, by rw [toReal_genFun_ennreal p ih.1, ih.2]⟩
  exact (key n).2

/-- **The extinction probability is the least fixed point of the generating function.**
`q = P(∃ n, Zₙ = 0)` is the least solution of `φ(s) = s` in `[0, 1]`. -/
theorem isLeast_galtonWatsonMeasure_extinction :
    IsLeast {r | r ∈ Icc (0 : ℝ) 1 ∧ ∑' k, (p k).toReal * r ^ k = r}
      (galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0}).toReal := by
  have hU : {ω : ℕ → ℕ → ℕ | ∃ n, generationSize n ω = 0} =
      ⋃ n, {ω | generationSize n ω = 0} := by
    ext ω; simp
  have ht := tendsto_measure_iUnion_atTop (μ := galtonWatsonMeasure p)
    monotone_setOf_generationSize_eq_zero
  rw [← hU] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hq : (galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0}).toReal =
      ⨆ n, (fun s : ℝ => ∑' k, (p k).toReal * s ^ k)^[n] 0 := by
    refine tendsto_nhds_unique ht' ((tendsto_iterate_genFun p).congr fun n => ?_)
    simp only [Function.comp_apply]
    exact (measureReal_generationSize_eq_zero p n).symm
  rw [hq]
  exact isLeast_iSup_iterate_genFun p

/-! ### Generation means and expected total progeny -/

omit p in
theorem measurable_natCast_generationSize (n : ℕ) :
    Measurable fun ω : ℕ → ℕ → ℕ => (generationSize n ω : ℝ≥0∞) :=
  (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp (measurable_generationSize n)

/-- `E Z_{n+1} = m E Zₙ`. -/
theorem lintegral_generationSize_succ (n : ℕ) :
    ∫⁻ ω, (generationSize (n + 1) ω : ℝ≥0∞) ∂galtonWatsonMeasure p =
      (∑' k : ℕ, (k : ℝ≥0∞) * p k) * ∫⁻ ω, (generationSize n ω : ℝ≥0∞) ∂galtonWatsonMeasure p := by
  rw [lintegral_comp_generationSize_succ p (fun k => (k : ℝ≥0∞)) n,
    ← lintegral_const_mul _ (measurable_natCast_generationSize n)]
  refine lintegral_congr fun ω => ?_
  set ν := Measure.infinitePi fun _ : ℕ => p.toMeasure
  have hj : ∀ j, ∫⁻ y, (y j : ℝ≥0∞) ∂ν = ∑' k : ℕ, (k : ℝ≥0∞) * p k := fun j => by
    rw [← lintegral_natCast_pmf p,
      ← (measurePreserving_eval_infinitePi (fun _ : ℕ => p.toMeasure) j).map_eq,
      lintegral_map measurable_from_nat (measurable_pi_apply j)]
  simp only [Nat.cast_sum]
  rw [lintegral_finsetSum _ fun j _ =>
    show Measurable fun y : ℕ → ℕ => (y j : ℝ≥0∞) from
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp (measurable_pi_apply j)]
  simp [hj, mul_comm]

/-- **Generation means**: `E Zₙ = mⁿ`. -/
theorem lintegral_generationSize (n : ℕ) :
    ∫⁻ ω, (generationSize n ω : ℝ≥0∞) ∂galtonWatsonMeasure p =
      (∑' k : ℕ, (k : ℝ≥0∞) * p k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [lintegral_generationSize_succ, ih, pow_succ, mul_comm]

/-- **Expected total progeny**: `E T = ∑ₙ mⁿ = (1 - m)⁻¹` in `[0, ∞]`. -/
theorem lintegral_totalProgeny :
    ∫⁻ ω, totalProgeny ω ∂galtonWatsonMeasure p = (1 - ∑' k : ℕ, (k : ℝ≥0∞) * p k)⁻¹ := by
  simp_rw [totalProgeny_def]
  rw [lintegral_tsum fun n => (measurable_natCast_generationSize n).aemeasurable]
  simp_rw [lintegral_generationSize]
  exact ENNReal.tsum_geometric _

/-- **Expected total progeny**, by cases: `E T = (1 - m)⁻¹` if `m < 1`, and `E T = ∞` if
`m ≥ 1`. -/
theorem lintegral_totalProgeny_eq_ite :
    ∫⁻ ω, totalProgeny ω ∂galtonWatsonMeasure p =
      if ∑' k : ℕ, (k : ℝ≥0∞) * p k < 1 then (1 - ∑' k : ℕ, (k : ℝ≥0∞) * p k)⁻¹ else ⊤ := by
  rw [lintegral_totalProgeny]
  split_ifs with h
  · rfl
  · rw [tsub_eq_zero_of_le (not_lt.1 h), ENNReal.inv_zero]

/-! ### The extinction criterion -/

/-- **Extinction is almost sure exactly when `m ≤ 1` and `p(1) ≠ 1`.** -/
theorem galtonWatsonMeasure_extinction_eq_one_iff :
    galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 1 ↔
      ∑' k : ℕ, (k : ℝ≥0∞) * p k ≤ 1 ∧ p 1 ≠ 1 := by
  rw [← genFun_least_fixedPoint_eq_one_iff p (isLeast_galtonWatsonMeasure_extinction p),
    ENNReal.toReal_eq_one_iff]

omit p in
/-- If `p(1) = 1` then `m ≥ 1`. -/
theorem one_le_mean_of_apply_one {p : PMF ℕ} (h : p 1 = 1) : 1 ≤ ∑' k : ℕ, (k : ℝ≥0∞) * p k :=
  le_of_eq_of_le (by simp [h]) (ENNReal.le_tsum (f := fun k : ℕ => (k : ℝ≥0∞) * p k) 1)

/-- **Subcritical extinction**: if `m < 1`, extinction is almost sure. -/
theorem galtonWatsonMeasure_extinction_eq_one_of_mean_lt_one
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k < 1) :
    galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 1 :=
  (galtonWatsonMeasure_extinction_eq_one_iff p).2
    ⟨hm.le, fun h => (one_le_mean_of_apply_one h).not_gt hm⟩

/-- **Critical extinction**: if `m = 1` and `p(1) ≠ 1`, extinction is almost sure. -/
theorem galtonWatsonMeasure_extinction_eq_one_of_mean_eq_one
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) (h1 : p 1 ≠ 1) :
    galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 1 :=
  (galtonWatsonMeasure_extinction_eq_one_iff p).2 ⟨hm.le, h1⟩

/-- **Supercritical survival**: if `m > 1` (possibly `m = ∞`), survival has positive
probability. -/
theorem galtonWatsonMeasure_extinction_lt_one_of_one_lt_mean
    (hm : 1 < ∑' k : ℕ, (k : ℝ≥0∞) * p k) :
    galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} < 1 := by
  have h := genFun_least_fixedPoint_lt_one p hm (isLeast_galtonWatsonMeasure_extinction p)
  refine lt_of_le_of_ne prob_le_one fun h1 => ?_
  rw [h1, ENNReal.toReal_one] at h
  exact lt_irrefl _ h

/-- **Supercritical survival**: if `m > 1` (possibly `m = ∞`), the survival event
`{∀ n, Zₙ ≠ 0}` has positive probability. -/
theorem galtonWatsonMeasure_survival_pos_of_one_lt_mean
    (hm : 1 < ∑' k : ℕ, (k : ℝ≥0∞) * p k) :
    0 < galtonWatsonMeasure p {ω | ∀ n, generationSize n ω ≠ 0} := by
  have hE : MeasurableSet {ω : ℕ → ℕ → ℕ | ∃ n, generationSize n ω = 0} := by
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_eq_fun (measurable_generationSize n) measurable_const
  have hc : {ω : ℕ → ℕ → ℕ | ∀ n, generationSize n ω ≠ 0} =
      {ω | ∃ n, generationSize n ω = 0}ᶜ := by
    ext ω; simp
  rw [hc, prob_compl_eq_one_sub hE]
  exact tsub_pos_of_lt (galtonWatsonMeasure_extinction_lt_one_of_one_lt_mean p hm)

/-- **The deterministic exception**: if `p(1) = 1`, then almost surely `Zₙ = 1` for every
`n`. -/
theorem ae_forall_generationSize_eq_one (h : p 1 = 1) :
    ∀ᵐ ω ∂galtonWatsonMeasure p, ∀ n, generationSize n ω = 1 := by
  have hp : p = PMF.pure 1 := PMF.ext fun k => by
    by_cases hk : k = 1
    · subst hk; simp [h]
    · simp [PMF.pure_apply, hk, pmf_apply_eq_zero_of_apply_one p h hk]
  have hcoord : ∀ n j, ∀ᵐ ω ∂galtonWatsonMeasure p, ω n j = 1 := fun n j => by
    have hmp := (measurePreserving_eval_infinitePi (fun _ : ℕ => p.toMeasure) j).comp
      (measurePreserving_eval_galtonWatsonMeasure p n)
    refine ae_of_ae_map (p := fun k : ℕ => k = 1) hmp.measurable.aemeasurable ?_
    rw [hmp.map_eq, hp, PMF.toMeasure_pure, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun j => hcoord n j] with ω hω n
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, hω]

/-- **The deterministic exception**: if `p(1) = 1`, extinction never occurs. -/
theorem galtonWatsonMeasure_extinction_eq_zero_of_apply_one (h : p 1 = 1) :
    galtonWatsonMeasure p {ω | ∃ n, generationSize n ω = 0} = 0 :=
  measure_mono_null (t := {ω | ¬ ∀ n, generationSize n ω = 1})
    (fun _ hω hall => hω.elim fun n hn => one_ne_zero ((hall n).symm.trans hn))
    (ae_iff.1 (ae_forall_generationSize_eq_one p h))

end PercLib.Probability
