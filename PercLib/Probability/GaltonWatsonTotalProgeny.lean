/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs on the Galton–Watson interface of `PercLib.Probability.GaltonWatson.Defs`. No
source text or code is copied. Mathematical reference: the total-progeny generating function
of a branching process; Athreya and Ney, *Branching Processes*, Chapter I.13.
-/
module

public import PercLib.Probability.GaltonWatsonCriticalSurvival

/-!
# The generating function of the total progeny

Write `Tₙ = ∑_{i < n} Zᵢ` for the partial progeny, `T = ∑ᵢ Zᵢ` for the total progeny and
`φ(t) = ∑ₖ p(k) tᵏ`. The pair `(Tₙ₊₁, Zₙ)` depends only on the offspring variables of
generations `< n`, which gives `E[s^{Tₙ} t^{Zₙ}] = hⁿ(t)` with `h(t) = s φ(t)`. Letting
`n → ∞` with `t = 1`, the generating function `F(s) = E[s^T] = ∑ₖ P(T = k) sᵏ` (`0 ≤ s < 1`)
is a solution in `[0, 1)` of `F(s) = s φ(F(s))`. With the analytic part of
`OffspringTransform.lean` this gives `1 - F(s) ~ √(2(1-s)/σ²)` at criticality.

## Main results

* `indepFun_eval_of_forall_eq`: a measurable function of the offspring variables of
  generations `< n` is independent of those of generation `n`.
* `lintegral_comp_prod_generationSize_succ`: the one-step identity with a past variable.
* `lintegral_pow_partialProgeny_mul_pow`: `E[s^{Tₙ} t^{Zₙ}] = hⁿ(t)`.
* `tsum_measure_totalProgeny_mul_pow`: `∑ₖ P(T = k) sᵏ = ⨅ₙ hⁿ(1)` for `s < 1`.
* `tsum_measureReal_totalProgeny_mul_pow_transform`: `F(s) ∈ [0, 1)` and `F(s) = s φ(F(s))`.
* `isEquivalent_one_sub_tsum_measureReal_totalProgeny`: for mean one and variance
  `σ² ∈ (0, ∞)`, `1 - F(s) ~ √(2(1-s)/σ²)` as `s ↑ 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Asymptotics Finset
open scoped ENNReal

namespace PercLib.Probability

variable (p : PMF ℕ)

/-- A measurable function of the offspring variables of generations `< n` is independent of
the offspring variables of generation `n`. -/
theorem indepFun_eval_of_forall_eq {β : Type*} [MeasurableSpace β] (n : ℕ)
    {X : (ℕ → ℕ → ℕ) → β} (hX : Measurable X)
    (hc : ∀ ω ω' : ℕ → ℕ → ℕ, (∀ i < n, ω i = ω' i) → X ω = X ω') :
    IndepFun X (fun ω : ℕ → ℕ → ℕ => ω n) (galtonWatsonMeasure p) := by
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
  have h' := h.comp (hX.comp hext)
    (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  refine h'.congr (Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => rfl)
  refine hc _ _ fun i hi => ?_
  simp [ext, hi]

/-- **One-step identity with a past variable.** If `X` is a measurable function of the
offspring variables of generations `< n`, then for every `g : ℕ × ℕ → [0, ∞]`,
`E g(X, Z_{n+1}) = E ∫ g(X, ∑_{j < Zₙ} yⱼ) dp^{⊗ℕ}(y)`. -/
theorem lintegral_comp_prod_generationSize_succ (g : ℕ × ℕ → ℝ≥0∞) (n : ℕ)
    {X : (ℕ → ℕ → ℕ) → ℕ} (hX : Measurable X)
    (hc : ∀ ω ω' : ℕ → ℕ → ℕ, (∀ i < n, ω i = ω' i) → X ω = X ω') :
    ∫⁻ ω, g (X ω, generationSize (n + 1) ω) ∂galtonWatsonMeasure p =
      ∫⁻ ω, ∫⁻ y, g (X ω, ∑ j ∈ Finset.range (generationSize n ω), y j)
        ∂Measure.infinitePi (fun _ : ℕ => p.toMeasure) ∂galtonWatsonMeasure p := by
  set μ := galtonWatsonMeasure p
  set ν := Measure.infinitePi fun _ : ℕ => p.toMeasure
  set Y : (ℕ → ℕ → ℕ) → ℕ × ℕ := fun ω => (X ω, generationSize n ω) with hYdef
  have hY : Measurable Y := hX.prodMk (measurable_generationSize n)
  have hind : IndepFun Y (fun ω : ℕ → ℕ → ℕ => ω n) μ :=
    indepFun_eval_of_forall_eq p n hY fun ω ω' h => by
      simp only [hYdef, Prod.mk.injEq]
      exact ⟨hc ω ω' h, generationSize_congr h⟩
  set F : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞ := fun x => g (x.1.1, ∑ j ∈ Finset.range x.1.2, x.2 j)
  have hFm : Measurable F := measurable_from_prod_countable_right fun k =>
    show Measurable fun y : ℕ → ℕ => g (k.1, ∑ j ∈ Finset.range k.2, y j) from
      (measurable_from_nat (f := fun m => g (k.1, m))).comp
        (Finset.measurable_sum (Finset.range k.2) fun j _ => measurable_pi_apply j)
  have hrow : Measurable fun ω : ℕ → ℕ → ℕ => ω n := measurable_pi_apply n
  have hmap := hind.map_prod_eq_prod_map_map hY.aemeasurable hrow.aemeasurable
  rw [(measurePreserving_eval_galtonWatsonMeasure p n).map_eq] at hmap
  have hL : ∫⁻ ω, g (X ω, generationSize (n + 1) ω) ∂μ =
      ∫⁻ x, F x ∂μ.map fun ω => (Y ω, ω n) := by
    rw [lintegral_map hFm (hY.prodMk hrow)]
    rfl
  rw [hL, hmap, lintegral_prod _ hFm.aemeasurable, lintegral_map _ hY]
  exact measurable_of_countable _

/-- `∫ t^{y₀ + ⋯ + y_{k-1}} dp^{⊗ℕ}(y) = φ(t)^k`. -/
theorem lintegral_pow_sum_eval (t : ℝ≥0∞) (k : ℕ) :
    ∫⁻ y, t ^ (∑ j ∈ Finset.range k, y j) ∂Measure.infinitePi (fun _ : ℕ => p.toMeasure) =
      (∑' i, p i * t ^ i) ^ k := by
  set ν := Measure.infinitePi fun _ : ℕ => p.toMeasure
  have hind : iIndepFun (fun (j : ℕ) (y : ℕ → ℕ) => t ^ y j) ν :=
    iIndepFun_infinitePi (X := fun _ x => t ^ x) fun _ => measurable_from_nat
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind
    fun j => measurable_from_nat.comp (measurable_pi_apply j)]
  have hj : ∀ j, ∫⁻ y, t ^ y j ∂ν = ∑' i, p i * t ^ i := fun j => by
    rw [← lintegral_pow_pmf p t,
      ← (measurePreserving_eval_infinitePi (fun _ : ℕ => p.toMeasure) j).map_eq,
      lintegral_map measurable_from_nat (measurable_pi_apply j)]
  simp [hj]

/-- **`E[s^{Tₙ} t^{Zₙ}] = hⁿ(t)`** with `Tₙ = ∑_{i<n} Zᵢ` and `h(x) = s φ(x)`. -/
theorem lintegral_pow_partialProgeny_mul_pow (s t : ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, s ^ (∑ i ∈ Finset.range n, generationSize i ω) * t ^ generationSize n ω
        ∂galtonWatsonMeasure p =
      (fun x => s * ∑' k, p k * x ^ k)^[n] t := by
  induction n generalizing t with
  | zero => simp [generationSize_zero]
  | succ n ih =>
    have hX : Measurable fun ω : ℕ → ℕ → ℕ => ∑ i ∈ Finset.range (n + 1), generationSize i ω :=
      Finset.measurable_sum _ fun i _ => measurable_generationSize i
    rw [lintegral_comp_prod_generationSize_succ p (fun x => s ^ x.1 * t ^ x.2) n hX
      (fun ω ω' h => Finset.sum_congr rfl fun i hi => generationSize_congr fun j hj =>
        h j (by rw [Finset.mem_range] at hi; omega)),
      Function.iterate_succ_apply, ← ih]
    refine lintegral_congr fun ω => ?_
    dsimp only
    have hmeas : Measurable fun y : ℕ → ℕ =>
        t ^ (∑ j ∈ Finset.range (generationSize n ω), y j) :=
      (measurable_from_nat (f := fun m => t ^ m)).comp
        (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)
    rw [lintegral_const_mul _ hmeas, lintegral_pow_sum_eval, Finset.sum_range_succ, pow_add,
      mul_pow, mul_assoc]

/-- For `s < 1`, `infₙ s^{Tₙ} = s^T`, with `s^∞ = 0`, written as `∑ₖ 1{T = k} sᵏ`. -/
theorem iInf_pow_partialProgeny_eq_tsum {s : ℝ≥0∞} (hs : s < 1) (ω : ℕ → ℕ → ℕ) :
    ⨅ n, s ^ (∑ i ∈ Finset.range n, generationSize i ω) =
      ∑' k : ℕ, {ω' | totalProgeny ω' = k}.indicator (fun _ => s ^ k) ω := by
  set a : ℕ → ℕ := fun n => ∑ i ∈ Finset.range n, generationSize i ω with hadef
  have hT : totalProgeny ω = ⨆ n, (a n : ℝ≥0∞) := by
    rw [totalProgeny_def, ENNReal.tsum_eq_iSup_nat]
    simp [hadef]
  by_cases hk : ∃ k : ℕ, totalProgeny ω = k
  · obtain ⟨k, hk⟩ := hk
    have hle : ∀ n, a n ≤ k := fun n => by
      have := le_iSup (fun n => (a n : ℝ≥0∞)) n
      rw [← hT, hk] at this
      exact_mod_cast this
    obtain ⟨N, hN⟩ : ∃ N, a N = k := by
      by_contra h
      push Not at h
      have hlt : ∀ n, a n < k := fun n => lt_of_le_of_ne (hle n) (h n)
      have hsup : (k : ℝ≥0∞) ≤ ((k - 1 : ℕ) : ℝ≥0∞) := by
        rw [← hk, hT]
        exact iSup_le fun n => by exact_mod_cast (by have := hlt n; omega : a n ≤ k - 1)
      have h0 := hlt 0
      norm_cast at hsup
      omega
    rw [tsum_eq_single k fun j hj => by simp [hk, Ne.symm hj]]
    rw [indicator_of_mem (show ω ∈ {ω' | totalProgeny ω' = k} from hk)]
    exact le_antisymm (iInf_le_of_le N (by change s ^ a N ≤ s ^ k; rw [hN]))
      (le_iInf fun n => pow_le_pow_of_le_one zero_le hs.le (hle n))
  · push Not at hk
    rw [ENNReal.tsum_eq_zero.2 fun j => by simp [hk j]]
    refine le_antisymm ?_ zero_le
    have hunb : ∀ M : ℕ, ∃ n, M ≤ a n := by
      intro M
      by_contra h
      push Not at h
      have hbdd : BddAbove (range a) := ⟨M, by rintro _ ⟨n, rfl⟩; exact (h n).le⟩
      obtain ⟨N, hN⟩ := Nat.sSup_mem (range_nonempty a) hbdd
      refine hk (sSup (range a)) (le_antisymm ?_ ?_)
      · rw [hT]
        exact iSup_le fun n => by exact_mod_cast le_csSup hbdd (mem_range_self n)
      · rw [hT, ← hN]
        exact le_iSup (fun n => (a n : ℝ≥0∞)) N
    have hle : ∀ M : ℕ, ⨅ n, s ^ a n ≤ s ^ M := fun M => by
      obtain ⟨n, hn⟩ := hunb M
      exact (iInf_le _ n).trans (pow_le_pow_of_le_one zero_le hs.le hn)
    exact ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_iff.2 hs) hle

/-- **`E[s^T] = ⨅ₙ hⁿ(1)`** for `s < 1`, where `E[s^T] = ∑ₖ P(T = k) sᵏ` and
`h(x) = s φ(x)`. -/
theorem tsum_measure_totalProgeny_mul_pow {s : ℝ≥0∞} (hs : s < 1) :
    ∑' k : ℕ, galtonWatsonMeasure p {ω | totalProgeny ω = k} * s ^ k =
      ⨅ n, (fun x => s * ∑' k, p k * x ^ k)^[n] 1 := by
  have hmeasT : ∀ k : ℕ, MeasurableSet {ω : ℕ → ℕ → ℕ | totalProgeny ω = k} := fun k =>
    measurableSet_eq_fun measurable_totalProgeny measurable_const
  have hf : ∀ n, Measurable fun ω : ℕ → ℕ → ℕ =>
      s ^ (∑ i ∈ Finset.range n, generationSize i ω) := fun n =>
    (measurable_from_nat (f := fun m => s ^ m)).comp
      (Finset.measurable_sum _ fun i _ => measurable_generationSize i)
  have hanti : Antitone fun n (ω : ℕ → ℕ → ℕ) =>
      s ^ (∑ i ∈ Finset.range n, generationSize i ω) := fun m n h ω =>
    pow_le_pow_of_le_one zero_le hs.le (Finset.sum_le_sum_of_subset (Finset.range_mono h))
  calc ∑' k : ℕ, galtonWatsonMeasure p {ω | totalProgeny ω = k} * s ^ k
      = ∫⁻ ω, ∑' k : ℕ, {ω' | totalProgeny ω' = k}.indicator (fun _ => s ^ k) ω
          ∂galtonWatsonMeasure p := by
        rw [lintegral_tsum fun k => (measurable_const.indicator (hmeasT k)).aemeasurable]
        exact tsum_congr fun k => by rw [lintegral_indicator_const (hmeasT k), mul_comm]
    _ = ∫⁻ ω, ⨅ n, s ^ (∑ i ∈ Finset.range n, generationSize i ω) ∂galtonWatsonMeasure p :=
        lintegral_congr fun ω => (iInf_pow_partialProgeny_eq_tsum hs ω).symm
    _ = ⨅ n, ∫⁻ ω, s ^ (∑ i ∈ Finset.range n, generationSize i ω) ∂galtonWatsonMeasure p :=
        lintegral_iInf hf hanti (by simp)
    _ = ⨅ n, (fun x => s * ∑' k, p k * x ^ k)^[n] 1 := by
        congr 1
        funext n
        rw [← lintegral_pow_partialProgeny_mul_pow]
        simp

/-- **Transform equation.** For `0 ≤ s < 1`, `F(s) = ∑ₖ P(T = k) sᵏ` lies in `[0, 1)` and
solves `F(s) = s φ(F(s))`. -/
theorem tsum_measureReal_totalProgeny_mul_pow_transform {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    ∑' k : ℕ, (galtonWatsonMeasure p {ω | totalProgeny ω = k}).toReal * s ^ k ∈
        Ico (0 : ℝ) 1 ∧
      s * ∑' j, (p j).toReal *
          (∑' k : ℕ, (galtonWatsonMeasure p {ω | totalProgeny ω = k}).toReal * s ^ k) ^ j =
        ∑' k : ℕ, (galtonWatsonMeasure p {ω | totalProgeny ω = k}).toReal * s ^ k := by
  set F := ∑' k : ℕ, (galtonWatsonMeasure p {ω | totalProgeny ω = k}).toReal * s ^ k with hFdef
  set S := ENNReal.ofReal s with hSdef
  have hS : S < 1 := ENNReal.ofReal_lt_one.2 hs.2
  set h : ℝ≥0∞ → ℝ≥0∞ := fun x => S * ∑' k, p k * x ^ k with hdef
  set hR : ℝ → ℝ := fun x => s * ∑' k, (p k).toReal * x ^ k with hRdef
  have key : ∀ n, h^[n] 1 ≤ 1 ∧ (h^[n] 1).toReal = hR^[n] 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      refine ⟨mul_le_one' hS.le (genFun_ennreal_le_one p ih.1), ?_⟩
      simp only [hdef, hRdef]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.1, toReal_genFun_ennreal p ih.1, ih.2]
  have hFeq : F = (⨅ n, h^[n] 1).toReal := by
    rw [← tsum_measure_totalProgeny_mul_pow p hS, ENNReal.tsum_toReal_eq fun k =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    exact tsum_congr fun k => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hs.1]
  have hrep : ∀ n, h^[n] 1 =
      ∫⁻ ω, S ^ (∑ i ∈ Finset.range n, generationSize i ω) ∂galtonWatsonMeasure p := fun n => by
    rw [← lintegral_pow_partialProgeny_mul_pow]
    simp
  have hanti : Antitone fun n => h^[n] 1 := fun m n hmn => by
    change h^[n] 1 ≤ h^[m] 1
    rw [hrep, hrep]
    exact lintegral_mono fun ω => pow_le_pow_of_le_one zero_le hS.le
      (Finset.sum_le_sum_of_subset (Finset.range_mono hmn))
  have hlimR : Tendsto (fun n => hR^[n] 1) atTop (𝓝 F) := by
    rw [hFeq]
    exact ((ENNReal.tendsto_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      ((iInf_le _ 0).trans (key 0).1))).comp (tendsto_atTop_iInf hanti)).congr
        fun n => (key n).2
  have hmem : ∀ n, hR^[n] 1 ∈ Icc (0 : ℝ) 1 := fun n => by
    rw [← (key n).2]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact (key n).1)⟩
  have hFmem : F ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hlimR (Eventually.of_forall hmem)
  have hcont : Tendsto (fun n => hR (hR^[n] 1)) atTop (𝓝 (hR F)) :=
    (((continuousOn_genFun p).continuousWithinAt hFmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlimR, Eventually.of_forall hmem⟩)).const_mul s
  have h2 : Tendsto (fun n => hR (hR^[n] 1)) atTop (𝓝 F) :=
    (hlimR.comp (tendsto_add_atTop_nat 1)).congr fun n => by
      simp only [Function.comp_apply, Function.iterate_succ_apply']
  have hfix : hR F = F := tendsto_nhds_unique hcont h2
  have hφ : ∑' k, (p k).toReal * F ^ k ≤ 1 :=
    (monotoneOn_genFun p hFmem ⟨zero_le_one, le_rfl⟩ hFmem.2).trans_eq (genFun_one p)
  refine ⟨⟨hFmem.1, ?_⟩, hfix⟩
  calc F = hR F := hfix.symm
    _ ≤ s * 1 := mul_le_mul_of_nonneg_left hφ hs.1
    _ < 1 := by linarith [hs.2]

/-- **Critical total-progeny transform.** If `m = 1` and the variance `σ²` is finite and
positive, then `F(s) = E[s^T] = ∑ₖ P(T = k) sᵏ` satisfies `1 - F(s) ~ √(2(1-s)/σ²)` as
`s ↑ 1`. -/
theorem isEquivalent_one_sub_tsum_measureReal_totalProgeny
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => ((k : ℝ) - 1) ^ 2 * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    (fun s => 1 - ∑' k : ℕ, (galtonWatsonMeasure p {ω | totalProgeny ω = k}).toReal * s ^ k)
      ~[𝓝[<] 1] fun s => Real.sqrt (2 * (1 - s) / σ2) :=
  isEquivalent_one_sub_transform_root p hm (hasSum_mul_sub_one_of_hasSum_variance p hm hσ) hσ0
    fun _ hs => tsum_measureReal_totalProgeny_mul_pow_transform p hs

end PercLib.Probability
