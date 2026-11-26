/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied; no Tauberian
theorem is used.
-/
module

public import PercLib.Analysis.Elementary
public import PercLib.Probability.ExponentialMoments
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A square-root Laplace deficit gives tails of order `n^{-1/2}`

Let `T : Ω → ℕ∞` be measurable on a probability space. For `t > 0` and `T : ℕ∞`, write
`e^{-tT}` for `EReal.exp (-(t * T))`, so that `e^{-t·⊤} = 0`, and put
`G(t) = (∫⁻ (1 - e^{-tT}) dμ).toReal`.

* `measure_le_div_sqrt_of_bound` (**upper bound**). If `√n G(1/n) ≤ C(1 - e^{-1})` for all
  `n ≥ 1`, then `P(T ≥ n) ≤ C/√n` for all `n ≥ 1`. The proof is Markov's inequality at
  `t = 1/n`.
* `exists_tail_bounds_of_laplace` (**MIFH, analytic**). If `G(t)/√t → a > 0` as `t ↓ 0`,
  there are `C, c > 0` and `N` such that `P(T ≥ n) ≤ C/√n` for `n ≥ 1` and
  `P(T ≥ n) ≥ c/√n` for `n ≥ N`. For the lower bound:
  * `G(t) ≤ t ∑_{k=1}^n P(T ≥ k) + P(T ≥ n)` (`laplace_le_sum_add`);
  * `∑_{k ≤ n} k^{-1/2} ≤ 2√n`;
  * take `t = 1/(Ln)` with `√L > 4C/a`.

The hypothesis `T < ⊤` almost surely is not needed. No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace PercLib.Probability

/-! ### The exponential of an extended integer -/

theorem laplace_exp_natCast (t : ℝ) (m : ℕ) :
    EReal.exp (-((t : EReal) * (((m : ℕ∞) : ℝ≥0∞) : EReal))) =
      ENNReal.ofReal (Real.exp (-(t * m))) := by
  have : (((m : ℕ∞) : ℝ≥0∞) : EReal) = ((m : ℝ) : EReal) := by simp
  rw [this, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]

/-- `1 - e^{-tT} ≥ 1 - e^{-1}` when `T ≥ 1/t`, here `t = 1/n` and `T ≥ n`. -/
theorem one_sub_exp_ge_of_le {n : ℕ} (hn : 1 ≤ n) {T : ℕ∞} (hT : (n : ℕ∞) ≤ T) :
    ENNReal.ofReal (1 - Real.exp (-1)) ≤
      1 - EReal.exp (-(((1 / (n : ℝ) : ℝ) : EReal) * ((T : ℝ≥0∞) : EReal))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  induction T using ENat.recTopCoe with
  | top =>
    rw [PercLib.Analysis.exp_neg_mul_top (by positivity), tsub_zero]
    exact ENNReal.ofReal_le_one.2 (by linarith [Real.exp_pos (-1)])
  | coe m =>
    rw [laplace_exp_natCast, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm : (n : ℝ) ≤ m := by exact_mod_cast hT
    have : 1 ≤ 1 / (n : ℝ) * m := by rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hn']; linarith
    have := Real.exp_le_exp.2 (neg_le_neg this)
    linarith

/-- `1 - e^{-tT} ≤ t ∑_{k=1}^m 1{T ≥ k} + 1{T ≥ m+1}`. -/
theorem one_sub_exp_le_sum_add {t : ℝ} (ht : 0 < t) (m : ℕ) (T : ℕ∞) :
    1 - EReal.exp (-((t : EReal) * ((T : ℝ≥0∞) : EReal))) ≤
      ENNReal.ofReal t * ∑ k ∈ Icc 1 m, (if (k : ℕ∞) ≤ T then (1 : ℝ≥0∞) else 0) +
        if ((m + 1 : ℕ) : ℕ∞) ≤ T then 1 else 0 := by
  by_cases hT : ((m + 1 : ℕ) : ℕ∞) ≤ T
  · simp only [hT, ↓reduceIte]
    exact tsub_le_self.trans le_add_self
  · simp only [hT, ↓reduceIte, add_zero]
    have hT' : T ≠ ⊤ := by rintro rfl; exact hT le_top
    obtain ⟨j, rfl⟩ := ENat.ne_top_iff_exists.1 hT'
    have hjm : j ≤ m := by
      by_contra h
      exact hT (by exact_mod_cast (Nat.succ_le_of_lt (not_le.1 h)))
    have hsum : ∑ k ∈ Icc 1 m, (if (k : ℕ∞) ≤ (j : ℕ∞) then (1 : ℝ≥0∞) else 0) = j := by
      rw [Finset.sum_boole]
      have : (Icc 1 m).filter (fun k : ℕ => (k : ℕ∞) ≤ (j : ℕ∞)) = Icc 1 j := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.cast_le]
        omega
      rw [this, Nat.card_Icc, Nat.add_sub_cancel]
    rw [hsum, laplace_exp_natCast, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (Real.exp_pos _).le, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul ht.le]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [Real.add_one_le_exp (-(t * j))]

/-! ### Tail bounds -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

theorem measurable_one_sub_exp (hT : Measurable T) (t : ℝ) :
    Measurable fun ω => 1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal))) :=
  (measurable_of_countable (fun T : ℕ∞ => 1 - EReal.exp (-((t : EReal) *
    ((T : ℝ≥0∞) : EReal))))).comp hT

theorem measurableSet_le (hT : Measurable T) (n : ℕ∞) : MeasurableSet {ω | n ≤ T ω} :=
  hT (Set.to_countable _).measurableSet

/-- **Markov at `t = 1/n`.** `(1 - e^{-1}) P(T ≥ n) ≤ ∫ (1 - e^{-T/n})`. -/
theorem mul_measure_le_laplace (hT : Measurable T) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (1 - Real.exp (-1)) * μ {ω | (n : ℕ∞) ≤ T ω} ≤
      ∫⁻ ω, (1 - EReal.exp (-(((1 / (n : ℝ) : ℝ) : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ :=
  (mul_le_mul_of_nonneg_left (measure_mono fun _ hω => one_sub_exp_ge_of_le hn hω) bot_le).trans
    (mul_meas_ge_le_lintegral₀ (measurable_one_sub_exp hT _).aemeasurable _)

/-- `G(t) ≤ t ∑_{k=1}^m P(T ≥ k) + P(T ≥ m+1)`. -/
theorem laplace_le_sum_add (hT : Measurable T) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∫⁻ ω, (1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ ≤
      ENNReal.ofReal t * ∑ k ∈ Icc 1 m, μ {ω | (k : ℕ∞) ≤ T ω} +
        μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ T ω} := by
  have hpt : ∀ ω, 1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal))) ≤
      ENNReal.ofReal t * ∑ k ∈ Icc 1 m, {ω | (k : ℕ∞) ≤ T ω}.indicator 1 ω +
        {ω | ((m + 1 : ℕ) : ℕ∞) ≤ T ω}.indicator 1 ω := by
    intro ω
    convert one_sub_exp_le_sum_add ht m (T ω) using 3
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [Set.indicator]
    · simp [Set.indicator]
  refine (lintegral_mono hpt).trans_eq ?_
  have hmeas : Measurable fun ω => ENNReal.ofReal t *
      ∑ k ∈ Icc 1 m, {ω | (k : ℕ∞) ≤ T ω}.indicator (1 : Ω → ℝ≥0∞) ω :=
    (Finset.measurable_sum
      (f := fun (k : ℕ) ω => {ω | (k : ℕ∞) ≤ T ω}.indicator (1 : Ω → ℝ≥0∞) ω) (Icc 1 m)
      fun k _ => (measurable_one.indicator (measurableSet_le hT k))).const_mul _
  have hsm : Measurable fun ω => ∑ k ∈ Icc 1 m, {ω | (k : ℕ∞) ≤ T ω}.indicator (1 : Ω → ℝ≥0∞) ω :=
    Finset.measurable_sum
      (f := fun (k : ℕ) ω => {ω | (k : ℕ∞) ≤ T ω}.indicator (1 : Ω → ℝ≥0∞) ω) (Icc 1 m)
      fun k _ => (measurable_one.indicator (measurableSet_le hT k))
  rw [lintegral_add_left hmeas, lintegral_const_mul _ hsm,
    lintegral_finsetSum (f := fun (k : ℕ) ω => {ω | (k : ℕ∞) ≤ T ω}.indicator (1 : Ω → ℝ≥0∞) ω) _
      fun k _ => (measurable_one.indicator (measurableSet_le hT k)),
    lintegral_indicator_one (measurableSet_le hT _)]
  congr 2
  exact Finset.sum_congr rfl fun k _ => lintegral_indicator_one (measurableSet_le hT _)

variable [IsProbabilityMeasure μ]

theorem laplace_ne_top (t : ℝ) :
    ∫⁻ ω, (1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    ((lintegral_mono fun _ => tsub_le_self).trans_eq (by simp))

/-- **Upper bound.** If `√n G(1/n) ≤ C(1 - e^{-1})` for all `n ≥ 1`, then
`P(T ≥ n) ≤ C/√n` for all `n ≥ 1`. -/
theorem measure_le_div_sqrt_of_bound (hT : Measurable T) {C : ℝ}
    (hC : ∀ n : ℕ, 1 ≤ n → Real.sqrt n *
      (∫⁻ ω, (1 - EReal.exp (-(((1 / (n : ℝ) : ℝ) : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal
        ≤ C * (1 - Real.exp (-1)))
    {n : ℕ} (hn : 1 ≤ n) : (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤ C / Real.sqrt n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < 1 - Real.exp (-1) := by
    have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    linarith
  have hM := ENNReal.toReal_mono (laplace_ne_top _) (mul_measure_le_laplace (μ := μ) hT hn)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal he.le] at hM
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  rw [le_div_iff₀ hs]
  have := hC n hn
  nlinarith

/-- **Analytic.** If `G(t)/√t → a > 0` as `t ↓ 0`, then `P(T ≥ n) ≍ n^{-1/2}`: there
are `C, c > 0` and `N` with `P(T ≥ n) ≤ C/√n` for `n ≥ 1` and `P(T ≥ n) ≥ c/√n` for
`n ≥ N`. -/
theorem exists_tail_bounds_of_laplace (hT : Measurable T) {a : ℝ} (ha : 0 < a)
    (hG : Tendsto (fun t : ℝ =>
      (∫⁻ ω, (1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal /
        Real.sqrt t) (𝓝[>] 0) (𝓝 a)) :
    ∃ C > 0, ∃ c > 0, ∃ N : ℕ, (∀ n : ℕ, 1 ≤ n → (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤
      C / Real.sqrt n) ∧ ∀ n : ℕ, N ≤ n → c / Real.sqrt n ≤ (μ {ω | (n : ℕ∞) ≤ T ω}).toReal := by
  set G : ℝ → ℝ := fun t =>
    (∫⁻ ω, (1 - EReal.exp (-((t : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal with hGdef
  have he : 0 < 1 - Real.exp (-1) := by
    have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    linarith
  -- `√n G(1/n) → a`, hence bounded
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
  have hseq := hG.comp hinv
  obtain ⟨B, hB⟩ := hseq.bddAbove_range
  set C := max B 1 / (1 - Real.exp (-1)) with hCdef
  have hC0 : 0 < C := div_pos (lt_max_of_lt_right one_pos) he
  have hCn : ∀ n : ℕ, 1 ≤ n → Real.sqrt n * G (1 / (n : ℝ)) ≤ C * (1 - Real.exp (-1)) := by
    intro n hn
    rw [hCdef, div_mul_cancel₀ _ he.ne']
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hk := hB ⟨k, rfl⟩
    simp only [Function.comp_apply] at hk
    have e1 : Real.sqrt ((k + 1 : ℕ) : ℝ) * G (1 / ((k + 1 : ℕ) : ℝ)) =
        G (1 / ((k : ℝ) + 1)) / Real.sqrt (1 / ((k : ℝ) + 1)) := by
      push_cast
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, div_div_eq_mul_div, div_one, mul_comm]
    rw [e1]
    exact hk.trans (le_max_left _ _)
  have hup := fun n (hn : 1 ≤ n) => measure_le_div_sqrt_of_bound (μ := μ) hT hCn hn
  -- the lower bound
  set L : ℝ := (4 * C / a + 1) ^ 2 with hL
  have hL1 : 1 ≤ L := by
    rw [hL]
    nlinarith [div_pos (mul_pos four_pos hC0) ha]
  have hsL : Real.sqrt L = 4 * C / a + 1 := Real.sqrt_sq (by positivity)
  set c := 1 / Real.sqrt L * (a / 2 - 2 * C / Real.sqrt L) with hc
  have hc0 : 0 < c := by
    rw [hc, hsL]
    refine mul_pos (by positivity) ?_
    rw [sub_pos, div_lt_iff₀ (by positivity)]
    have : 0 < 4 * C / a := by positivity
    nlinarith [div_mul_cancel₀ (4 * C) ha.ne']
  -- `√(Ln) G(1/(Ln)) ≥ a/2` eventually
  have hinvL : Tendsto (fun n : ℕ => 1 / (L * ((n : ℝ) + 1))) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨?_, Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / L)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    field_simp
  have hev := (hG.comp hinvL).eventually (eventually_ge_nhds (half_lt_self ha))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  refine ⟨C, hC0, c, hc0, N0 + 1, hup, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (le_trans (Nat.le_add_left 1 N0) hn)
  have hk : N0 ≤ k := by omega
  have hGk := hN0 k hk
  simp only [Function.comp_apply] at hGk
  set n := k + 1 with hn'
  have hnpos : (0 : ℝ) < n := by positivity
  have hnr : ((k : ℝ) + 1) = (n : ℝ) := by rw [hn']; push_cast; ring
  rw [hnr] at hGk
  set t := 1 / (L * (n : ℝ)) with ht
  have ht0 : 0 < t := by positivity
  -- `G(t) ≤ t ∑_{j ≤ n} P(T ≥ j) + P(T ≥ n)`
  have hsum := laplace_le_sum_add (μ := μ) hT ht0 n
  have hmono : μ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} ≤ μ {ω | (n : ℕ∞) ≤ T ω} :=
    measure_mono fun ω (hω : ((n + 1 : ℕ) : ℕ∞) ≤ T ω) =>
      show (n : ℕ∞) ≤ T ω from le_trans (by exact_mod_cast Nat.le_succ n) hω
  have hfin : ∀ j : ℕ, μ {ω | (j : ℕ∞) ≤ T ω} ≠ ⊤ := fun j => measure_ne_top μ _
  have hGle : G t ≤ t * ∑ j ∈ Icc 1 n, (μ {ω | (j : ℕ∞) ≤ T ω}).toReal +
      (μ {ω | (n : ℕ∞) ≤ T ω}).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 fun j _ => hfin j), hfin _⟩) (hsum.trans (add_le_add le_rfl hmono))
    rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.sum_ne_top.2 fun j _ => hfin j)) (hfin _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ht0.le, ENNReal.toReal_sum fun j _ => hfin j] at this
  -- `∑_{j ≤ n} P(T ≥ j) ≤ 2C√n`
  have hsum2 : ∑ j ∈ Icc 1 n, (μ {ω | (j : ℕ∞) ≤ T ω}).toReal ≤ C * (2 * Real.sqrt n) := by
    calc ∑ j ∈ Icc 1 n, (μ {ω | (j : ℕ∞) ≤ T ω}).toReal
        ≤ ∑ j ∈ Icc 1 n, C * (1 / Real.sqrt j) := Finset.sum_le_sum fun j hj => by
          rw [mul_one_div]
          exact hup j (Finset.mem_Icc.1 hj).1
      _ = C * ∑ j ∈ Icc 1 n, 1 / Real.sqrt j := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (2 * Real.sqrt n) := mul_le_mul_of_nonneg_left
          (PercLib.Analysis.sum_Icc_one_div_sqrt_le_two_mul n) hC0.le
  -- `G(t) ≥ (a/2) √t`
  have hsqt : Real.sqrt t = 1 / (Real.sqrt L * Real.sqrt n) := by
    rw [ht, Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_mul (by linarith)]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsL0 : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hGt : a / 2 * Real.sqrt t ≤ G t := by
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have := (le_div_iff₀ hst).1 (show a / 2 ≤ G t / Real.sqrt t by
      simpa [ht, hGdef] using hGk)
    linarith
  -- assembling
  have htn : t * (C * (2 * Real.sqrt n)) = 2 * C / (Real.sqrt L * Real.sqrt L) / Real.sqrt n := by
    have hLL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
    have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    rw [hLL, ht]
    field_simp
    exact Real.sq_sqrt hnpos.le
  have h1 : t * ∑ j ∈ Icc 1 n, (μ {ω | (j : ℕ∞) ≤ T ω}).toReal ≤
      2 * C / (Real.sqrt L * Real.sqrt L) / Real.sqrt n :=
    (mul_le_mul_of_nonneg_left hsum2 ht0.le).trans_eq htn
  have hcn : c / Real.sqrt n =
      a / 2 * Real.sqrt t - 2 * C / (Real.sqrt L * Real.sqrt L) / Real.sqrt n := by
    rw [hc, hsqt]
    field_simp
  rw [hcn]
  linarith

/-! ### Non-vacuity -/

section Witness

/-- The coefficients of `1 - √(1 - z) = ∑_{n ≥ 0} c_n z^{n+1}` sum to one. -/
theorem hasSum_sqrt_coeff_one :
    HasSum (fun n : ℕ => (Nat.doubleFactorial (2 * n - 1) : ℝ) /
      ((n + 1).factorial * 2 ^ (n + 1))) 1 := by
  set c : ℕ → ℝ := fun n => (Nat.doubleFactorial (2 * n - 1) : ℝ) /
    ((n + 1).factorial * 2 ^ (n + 1)) with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => by positivity
  have hpart : ∀ N, ∑ n ∈ range N, c n ≤ 1 := by
    intro N
    have := sum_range_le_one_sub_sqrt (z := 1) zero_le_one le_rfl N
    simpa [hc] using this
  have hs : Summable c := summable_of_sum_range_le hc0 hpart
  have hle : ∑' n, c n ≤ 1 := Real.tsum_le_of_sum_range_le hc0 hpart
  have hge : 1 ≤ ∑' n, c n := by
    have hz : ∀ z ∈ Set.Ico (0 : ℝ) 1, 1 - Real.sqrt (1 - z) ≤ ∑' n, c n := by
      intro z hz
      refine hasSum_le (fun n => ?_) (hasSum_one_sub_sqrt_one_sub hz.1 hz.2) hs.hasSum
      exact mul_le_of_le_one_right (hc0 n) (pow_le_one₀ hz.1 hz.2.le)
    have hlim : Tendsto (fun z : ℝ => 1 - Real.sqrt (1 - z)) (𝓝[<] 1) (𝓝 1) := by
      have : Tendsto (fun z : ℝ => 1 - Real.sqrt (1 - z)) (𝓝 1) (𝓝 (1 - Real.sqrt (1 - 1))) :=
        (continuous_const.sub (Real.continuous_sqrt.comp
          (continuous_const.sub continuous_id))).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with z hzz
    exact hz z ⟨hzz.1.le, hzz.2⟩
  have := hs.hasSum
  rwa [le_antisymm hle hge] at this

/-- `(1 - e^{-t})/t → 1` as `t ↓ 0`. -/
theorem tendsto_one_sub_exp_neg_div :
    Tendsto (fun t : ℝ => (1 - Real.exp (-t)) / t) (𝓝[>] 0) (𝓝 1) := by
  have hu : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlow : Tendsto (fun t : ℝ => 1 / (1 + t)) (𝓝[>] 0) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div
      ((tendsto_const_nhds (x := (1 : ℝ))).add hu) (by norm_num)
    rw [add_zero, div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [div_le_div_iff₀ (by linarith) ht, one_mul]
    have h1 := Real.add_one_le_exp t
    have h2 : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos (-t)]
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [div_le_one ht]
    linarith [Real.add_one_le_exp (-t)]

/-- **Non-vacuity witness.** On `ℕ` put mass `c_n = (2n-1)!!/((n+1)! 2^{n+1})` at `n` and let
`T(n) = n + 1`, so that `E[s^T] = 1 - √(1 - s)`. Then `G(t) = √(1 - e^{-t})`,
`G(t)/√t → 1`, and the tail bounds hold. -/
example : ∃ C > 0, ∃ c > 0, ∃ N : ℕ, (∀ n : ℕ, 1 ≤ n →
    ((Measure.sum fun k : ℕ => ENNReal.ofReal ((Nat.doubleFactorial (2 * k - 1) : ℝ) /
      ((k + 1).factorial * 2 ^ (k + 1))) • Measure.dirac k)
        {k : ℕ | (n : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞)}).toReal ≤ C / Real.sqrt n) ∧
    ∀ n : ℕ, N ≤ n → c / Real.sqrt n ≤
      ((Measure.sum fun k : ℕ => ENNReal.ofReal ((Nat.doubleFactorial (2 * k - 1) : ℝ) /
        ((k + 1).factorial * 2 ^ (k + 1))) • Measure.dirac k)
          {k : ℕ | (n : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞)}).toReal := by
  set c : ℕ → ℝ := fun k => (Nat.doubleFactorial (2 * k - 1) : ℝ) /
    ((k + 1).factorial * 2 ^ (k + 1)) with hc
  set μ : Measure ℕ := Measure.sum fun k : ℕ => ENNReal.ofReal (c k) • Measure.dirac k
  have hc0 : ∀ k, 0 ≤ c k := fun k => by positivity
  have hsum : HasSum c 1 := hasSum_sqrt_coeff_one
  have hlint : ∀ f : ℕ → ℝ≥0∞, ∫⁻ k, f k ∂μ = ∑' k, ENNReal.ofReal (c k) * f k := by
    intro f
    rw [lintegral_sum_measure]
    refine tsum_congr fun k => ?_
    rw [lintegral_smul_measure, lintegral_dirac]
    rfl
  have hprob : IsProbabilityMeasure μ := by
    constructor
    have := hlint fun _ => 1
    rw [lintegral_one] at this
    rw [this]
    simp only [mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hc0 hsum.summable, hsum.tsum_eq, ENNReal.ofReal_one]
  -- the Laplace deficit
  have hG : ∀ t : ℝ, 0 < t →
      (∫⁻ k, (1 - EReal.exp (-((t : EReal) * ((((k + 1 : ℕ) : ℕ∞) : ℝ≥0∞) : EReal)))) ∂μ).toReal =
        Real.sqrt (1 - Real.exp (-t)) := by
    intro t ht
    have hz0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hz1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    have hser : HasSum (fun k : ℕ => c k * (1 - Real.exp (-(t * ((k + 1 : ℕ) : ℝ)))))
        (Real.sqrt (1 - Real.exp (-t))) := by
      have h := hsum.sub (hasSum_one_sub_sqrt_one_sub hz0 hz1)
      rw [sub_sub_cancel] at h
      convert h using 1
      funext k
      rw [← Real.exp_nat_mul]
      simp only [hc]
      push_cast
      ring_nf
    rw [hlint]
    have hnn : ∀ k : ℕ, 0 ≤ c k * (1 - Real.exp (-(t * ((k + 1 : ℕ) : ℝ)))) := by
      intro k
      refine mul_nonneg (hc0 k) ?_
      have : 0 ≤ t * ((k + 1 : ℕ) : ℝ) := by positivity
      linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 this)]
    have hpt : ∀ k : ℕ, ENNReal.ofReal (c k) *
        (1 - EReal.exp (-((t : EReal) * ((((k + 1 : ℕ) : ℕ∞) : ℝ≥0∞) : EReal)))) =
        ENNReal.ofReal (c k * (1 - Real.exp (-(t * ((k + 1 : ℕ) : ℝ))))) := by
      intro k
      rw [laplace_exp_natCast, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (hc0 k)]
    simp_rw [hpt]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hser.summable, hser.tsum_eq,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hlim : Tendsto (fun t : ℝ =>
      (∫⁻ k, (1 - EReal.exp (-((t : EReal) * ((((k + 1 : ℕ) : ℕ∞) : ℝ≥0∞) : EReal)))) ∂μ).toReal /
        Real.sqrt t) (𝓝[>] 0) (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp tendsto_one_sub_exp_neg_div
    rw [Real.sqrt_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Function.comp_apply, hG t ht, Real.sqrt_div' _ ht.le]
  exact exists_tail_bounds_of_laplace (μ := μ) (T := fun k => ((k + 1 : ℕ) : ℕ∞))
    (measurable_of_countable _) one_pos hlim

end Witness

end PercLib.Probability
