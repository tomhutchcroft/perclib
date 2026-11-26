/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16. No upstream proof is copied and no definition is added.
-/
module

public import PercLib.Probability.LaplaceTail
public import PercLib.Percolation.Bond.IndependentLayer
public import PercLib.Analysis.ReciprocalODE
public import PercLib.Percolation.Bond.Tightness.Hyperscaling
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Ghost-field transforms of `ℕ∞`-valued variables (8B62, 0NVH, 3C2F, CVCN)

Let `T : Ω → ℕ∞` be measurable on a probability space and, for `h > 0`,
`M(h) = ∫⁻ (1 - e^{-hT})` with `e^{-hT}` written `EReal.exp (-(h * T))`, so that
`e^{-h·⊤} = 0` (the convention of `LaplaceTail.lean`).

* **0NVH** (`lintegral_ghost_eq_tsum`, `mul_measure_le_lintegral_ghost`,
  `lintegral_ghost_le`): `M(h) = (1 - e^{-h}) ∑_{n ≥ 1} e^{-h(n-1)} P(T ≥ n)` and
  `(1 - e^{-hN}) P(T ≥ N) ≤ M(h) ≤ h E[min(T, N)] + P(T ≥ N)`.
* **8B62** (`tendsto_lintegral_ghost`, `tendsto_lintegral_ghost_div`): as `h ↓ 0`,
  `M(h) → P(T = ⊤)` and `M(h)/h → E T` in `ℝ≥0∞`.
* **3C2F** (`tail_asymp_iff_ghost_asymp`): for `0 < α < 1`, `P(T ≥ n) ≍ n^{-α}` as
  `n → ∞` if and only if `M(h) ≍ h^α` as `h ↓ 0`.
* **CVCN** (`min_le_of_ghost_ode`): a nondecreasing locally absolutely continuous
  `m : (0, ∞) → [0, 1]` with `A m^r m' ≥ 1 - m^q` a.e. satisfies
  `m(h) ≥ min(a, ((r+1)(1 - a^q) h / A)^{1/(r+1)})` for `a ∈ (0, 1)` and `h > 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Finset Set
open scoped ENNReal Topology

namespace PercLib.Probability

/-! ### Pointwise facts about `1 - e^{-hT}` -/

/-- `e^{-hm}` for finite `m`, as a power of `e^{-h}`. -/
theorem ghost_exp_natCast (h : ℝ) (m : ℕ) :
    EReal.exp (-((h : EReal) * (((m : ℕ∞) : ℝ≥0∞) : EReal))) =
      ENNReal.ofReal (Real.exp (-h)) ^ m :=
  PercLib.Percolation.Bond.exp_neg_mul_natCast h m

/-- **Pointwise.** `1 - e^{-hT} = (1 - e^{-h}) ∑_{n ≥ 0} e^{-hn} 1{T ≥ n + 1}`. -/
theorem one_sub_ghost_eq_tsum {h : ℝ} (hh : 0 < h) (T : ℕ∞) :
    1 - EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) =
      ENNReal.ofReal (1 - Real.exp (-h)) * ∑' n : ℕ,
        ENNReal.ofReal (Real.exp (-h)) ^ n * (if ((n + 1 : ℕ) : ℕ∞) ≤ T then 1 else 0) := by
  set x := ENNReal.ofReal (Real.exp (-h)) with hx
  have hx1 : x < 1 := by
    rw [hx, ENNReal.ofReal_lt_one]; exact Real.exp_lt_one_iff.2 (by linarith)
  have h1x : ENNReal.ofReal (1 - Real.exp (-h)) = 1 - x := by
    rw [hx, ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  rw [h1x]
  induction T using ENat.recTopCoe with
  | top =>
    rw [PercLib.Analysis.exp_neg_mul_top hh, tsub_zero]
    simp only [le_top, ↓reduceIte, mul_one]
    rw [ENNReal.tsum_geometric, ENNReal.mul_inv_cancel (tsub_pos_of_lt hx1).ne'
      (ENNReal.sub_ne_top ENNReal.one_ne_top)]
  | coe m =>
    rw [ghost_exp_natCast, ← hx]
    rw [tsum_eq_sum (s := range m) fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      have : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        rw [Nat.cast_le]; omega
      rw [ite_eq_right this, mul_zero]]
    have hs : ∑ n ∈ range m, x ^ n * (if ((n + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) then 1 else 0) =
        ∑ n ∈ range m, x ^ n := Finset.sum_congr rfl fun n hn => by
      have : ((n + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := by
        rw [Nat.cast_le]; have := Finset.mem_range.1 hn; omega
      rw [ite_eq_left this, mul_one]
    rw [hs]
    -- `1 - x^m = (1 - x) ∑_{n<m} x^n`, through real numbers.
    have hxr : x = ENNReal.ofReal (Real.exp (-h)) := hx
    rw [hxr, ← ENNReal.ofReal_pow (Real.exp_pos _).le]
    simp_rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by linarith [Real.exp_le_one_iff.2 (show -h ≤ 0 by linarith)])]
    congr 1
    have := geom_sum_mul (Real.exp (-h)) m
    linarith

/-- `1 - e^{-hT} ≥ (1 - e^{-hN}) 1{T ≥ N}`. -/
theorem one_sub_exp_ge_of_natCast_le {h : ℝ} (hh : 0 < h) {N : ℕ} {T : ℕ∞}
    (hT : (N : ℕ∞) ≤ T) :
    ENNReal.ofReal (1 - Real.exp (-(h * N))) ≤
      1 - EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) := by
  induction T using ENat.recTopCoe with
  | top =>
    rw [PercLib.Analysis.exp_neg_mul_top hh, tsub_zero]
    exact ENNReal.ofReal_le_one.2 (by linarith [Real.exp_pos (-(h * N))])
  | coe m =>
    rw [PercLib.Percolation.Bond.exp_neg_mul_natCast_eq, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm : (N : ℝ) ≤ m := by exact_mod_cast hT
    have := Real.exp_le_exp.2 (show -(h * m) ≤ -(h * N) by nlinarith)
    linarith

/-- `1 - e^{-hT} ≤ h min(T, N) + 1{T ≥ N}`. -/
theorem one_sub_exp_le_mul_min_add {h : ℝ} (hh : 0 < h) (N : ℕ) (T : ℕ∞) :
    1 - EReal.exp (-((h : EReal) * ((T : ℝ≥0∞) : EReal))) ≤
      ENNReal.ofReal h * ((min T N : ℕ∞) : ℝ≥0∞) + if (N : ℕ∞) ≤ T then 1 else 0 := by
  by_cases hT : (N : ℕ∞) ≤ T
  · simp only [hT, ↓reduceIte]
    exact tsub_le_self.trans le_add_self
  · simp only [hT, ↓reduceIte, add_zero]
    rw [min_eq_left (not_le.1 hT).le]
    exact PercLib.Percolation.Bond.one_sub_exp_le_mul hh T

/-! ### 0NVH -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- **The series.** `M(h) = (1 - e^{-h}) ∑_{n ≥ 1} e^{-h(n-1)} P(T ≥ n)`, written with
`n + 1` in place of `n`. -/
theorem lintegral_ghost_eq_tsum (hT : Measurable T) {h : ℝ} (hh : 0 < h) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ =
      ENNReal.ofReal (1 - Real.exp (-h)) * ∑' n : ℕ,
        ENNReal.ofReal (Real.exp (-h)) ^ n * μ {ω | ((n + 1 : ℕ) : ℕ∞) ≤ T ω} := by
  simp_rw [one_sub_ghost_eq_tsum hh]
  have hm : ∀ n : ℕ, Measurable fun ω => ENNReal.ofReal (Real.exp (-h)) ^ n *
      (if ((n + 1 : ℕ) : ℕ∞) ≤ T ω then (1 : ℝ≥0∞) else 0) := fun n =>
    (measurable_of_countable (fun t : ℕ∞ => ENNReal.ofReal (Real.exp (-h)) ^ n *
      (if ((n + 1 : ℕ) : ℕ∞) ≤ t then (1 : ℝ≥0∞) else 0))).comp hT
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_tsum fun n => (hm n).aemeasurable]
  congr 1
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  congr 1
  rw [← lintegral_indicator_one (measurableSet_le hT _)]
  refine lintegral_congr fun ω => ?_
  simp [Set.indicator]

/-- **Lower bound.** `(1 - e^{-hN}) P(T ≥ N) ≤ M(h)`. -/
theorem mul_measure_le_lintegral_ghost (hT : Measurable T) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    ENNReal.ofReal (1 - Real.exp (-(h * N))) * μ {ω | (N : ℕ∞) ≤ T ω} ≤
      ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ :=
  (mul_le_mul_of_nonneg_left (measure_mono fun _ hω => one_sub_exp_ge_of_natCast_le hh hω)
    bot_le).trans (mul_meas_ge_le_lintegral₀ (measurable_one_sub_exp hT _).aemeasurable _)

/-- **Upper bound.** `M(h) ≤ h E[min(T, N)] + P(T ≥ N)`. -/
theorem lintegral_ghost_le (hT : Measurable T) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ ≤
      ENNReal.ofReal h * ∫⁻ ω, ((min (T ω) N : ℕ∞) : ℝ≥0∞) ∂μ +
        μ {ω | (N : ℕ∞) ≤ T ω} := by
  have hmin : Measurable fun ω => ((min (T ω) N : ℕ∞) : ℝ≥0∞) :=
    (measurable_of_countable (fun t : ℕ∞ => ((min t N : ℕ∞) : ℝ≥0∞))).comp hT
  refine (lintegral_mono fun ω => one_sub_exp_le_mul_min_add hh N (T ω)).trans_eq ?_
  rw [lintegral_add_left (hmin.const_mul _), lintegral_const_mul _ hmin,
    ← lintegral_indicator_one (measurableSet_le hT _)]
  congr 1
  refine lintegral_congr fun ω => ?_
  simp [Set.indicator]

/-! ### 8B62 -/

/-- `e^{-hT}` is antitone in `h > 0`. -/
theorem ghost_exp_antitone {h₁ h₂ : ℝ} (h₁0 : 0 < h₁) (h12 : h₁ ≤ h₂) (t : ℕ∞) :
    EReal.exp (-((h₂ : EReal) * ((t : ℝ≥0∞) : EReal))) ≤
      EReal.exp (-((h₁ : EReal) * ((t : ℝ≥0∞) : EReal))) := by
  induction t using ENat.recTopCoe with
  | top => rw [PercLib.Analysis.exp_neg_mul_top (h₁0.trans_le h12)]; exact bot_le
  | coe m =>
    rw [PercLib.Percolation.Bond.exp_neg_mul_natCast_eq,
      PercLib.Percolation.Bond.exp_neg_mul_natCast_eq]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

/-- `1 - e^{-hT} → 1{T = ⊤}` as `h ↓ 0`. -/
theorem tendsto_one_sub_ghost (t : ℕ∞) :
    Tendsto (fun h : ℝ => 1 - EReal.exp (-((h : EReal) * ((t : ℝ≥0∞) : EReal)))) (𝓝[>] 0)
      (𝓝 (({⊤} : Set ℕ∞).indicator 1 t)) := by
  induction t using ENat.recTopCoe with
  | top =>
    simp only [Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    rw [PercLib.Analysis.exp_neg_mul_top hh, tsub_zero]
  | coe m =>
    rw [Set.indicator_of_notMem (by simp)]
    have hlim : Tendsto (fun h : ℝ => ENNReal.ofReal h * ((m : ℕ∞) : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun h : ℝ => ENNReal.ofReal h) (𝓝[>] 0) (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const this (Or.inr (by simp))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact PercLib.Percolation.Bond.one_sub_exp_le_mul hh _

variable [IsProbabilityMeasure μ]

/-- **First limit.** `M(h) → P(T = ⊤)` as `h ↓ 0`. -/
theorem tendsto_lintegral_ghost (hT : Measurable T) :
    Tendsto (fun h : ℝ => ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ)
      (𝓝[>] 0) (𝓝 (μ {ω | T ω = ⊤})) := by
  have hset : MeasurableSet {ω | T ω = ⊤} := hT (measurableSet_singleton _)
  have hf : μ {ω | T ω = ⊤} = ∫⁻ ω, ({⊤} : Set ℕ∞).indicator 1 (T ω) ∂μ := by
    rw [← lintegral_indicator_one hset]
    refine lintegral_congr fun ω => ?_
    by_cases h : T ω = ⊤ <;> simp [Set.indicator, h]
  rw [hf]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun h => measurable_one_sub_exp hT h)
    (Eventually.of_forall fun h => Eventually.of_forall fun ω => tsub_le_self)
    (by simp) (Eventually.of_forall fun ω => tendsto_one_sub_ghost (T ω))

omit [IsProbabilityMeasure μ] in
/-- **Second limit.** `M(h)/h → E T` in `ℝ≥0∞` as `h ↓ 0`. -/
theorem tendsto_lintegral_ghost_div (hT : Measurable T) :
    Tendsto (fun h : ℝ => (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal))))
      ∂μ) / ENNReal.ofReal h) (𝓝[>] 0) (𝓝 (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ)) := by
  have hTm : Measurable fun ω => (T ω : ℝ≥0∞) :=
    (measurable_of_countable (fun t : ℕ∞ => (t : ℝ≥0∞))).comp hT
  set M : ℝ → ℝ≥0∞ := fun h =>
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ with hM
  -- Upper bound `M(h)/h ≤ E T`.
  have hup : ∀ᶠ h in 𝓝[>] (0 : ℝ), M h / ENNReal.ofReal h ≤ ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_comm, ← lintegral_const_mul _ hTm]
    exact lintegral_mono fun ω => PercLib.Percolation.Bond.one_sub_exp_le_mul hh _
  by_cases htop : μ {ω | T ω = ⊤} = 0
  · -- `T < ⊤` almost surely: squeeze with `E[T e^{-hT}]`.
    have hae : ∀ᵐ ω ∂μ, T ω ≠ ⊤ := by
      rw [ae_iff]; simpa using htop
    set G : ℝ → ℝ≥0∞ := fun h => ∫⁻ ω, (T ω : ℝ≥0∞) *
      EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal))) ∂μ with hG
    have hlow : ∀ᶠ h in 𝓝[>] (0 : ℝ), G h ≤ M h / ENNReal.ofReal h := by
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hh).ne')
        (Or.inl ENNReal.ofReal_ne_top), mul_comm, hG]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun ω => PercLib.Percolation.Bond.mul_mul_exp_le_one_sub hh _
    have hanti : AntitoneOn G (Set.Ioi 0) := by
      intro h₁ (h₁0 : 0 < h₁) h₂ _ h12
      exact lintegral_mono fun ω => mul_le_mul' le_rfl (ghost_exp_antitone h₁0 h12 _)
    have hGlim := hanti.tendsto_nhdsGT (OrderTop.bddAbove _)
    have hsup : sSup (G '' Set.Ioi 0) = ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
      refine le_antisymm (sSup_le ?_) ?_
      · rintro _ ⟨h, hh, rfl⟩
        exact lintegral_mono fun ω => PercLib.Percolation.Bond.mul_exp_le_self
          (le_of_lt hh) _
      · -- monotone convergence along `h = 1/(n+1)`
        set f : ℕ → Ω → ℝ≥0∞ := fun n ω => (T ω : ℝ≥0∞) *
          EReal.exp (-(((1 / ((n : ℝ) + 1) : ℝ) : EReal) * ((T ω : ℝ≥0∞) : EReal))) with hf
        have hfm : ∀ n, Measurable (f n) := fun n =>
          (measurable_of_countable (fun t : ℕ∞ => (t : ℝ≥0∞) *
            EReal.exp (-(((1 / ((n : ℝ) + 1) : ℝ) : EReal) * ((t : ℝ≥0∞) : EReal))))).comp hT
        have hfmono : Monotone f := fun a b hab ω => mul_le_mul' le_rfl
          (ghost_exp_antitone (by positivity) (one_div_le_one_div_of_le (by positivity)
            (by exact_mod_cast Nat.add_le_add_right hab 1)) _)
        have hlim : ∀ᵐ ω ∂μ, ⨆ n, f n ω = (T ω : ℝ≥0∞) := by
          filter_upwards [hae] with ω hω
          obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hω
          have := PercLib.Percolation.Bond.tendsto_mul_exp_neg_div m
          rw [hm] at this
          exact iSup_eq_of_tendsto (fun a b hab => hfmono hab ω) this
        calc ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ∫⁻ ω, ⨆ n, f n ω ∂μ :=
              lintegral_congr_ae (hlim.mono fun ω h => h.symm)
          _ = ⨆ n, ∫⁻ ω, f n ω ∂μ := lintegral_iSup hfm hfmono
          _ ≤ sSup (G '' Set.Ioi 0) := iSup_le fun n =>
              le_sSup ⟨1 / ((n : ℝ) + 1), by simp only [Set.mem_Ioi]; positivity, rfl⟩
    rw [hsup] at hGlim
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hGlim tendsto_const_nhds hlow hup
  · -- `P(T = ⊤) > 0`: both sides are `⊤`.
    have hET : ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ⊤ := by
      refine eq_top_iff.2 ?_
      calc (⊤ : ℝ≥0∞) = ⊤ * μ {ω | T ω = ⊤} := (ENNReal.top_mul htop).symm
        _ = ∫⁻ ω, {ω | T ω = ⊤}.indicator (fun _ => ⊤) ω ∂μ :=
            (lintegral_indicator_const (hT (measurableSet_singleton _)) _).symm
        _ ≤ ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := lintegral_mono fun ω => by
            by_cases h : T ω = ⊤ <;> simp [Set.indicator, h]
    rw [hET]
    have hlowM : ∀ᶠ h in 𝓝[>] (0 : ℝ),
        μ {ω | T ω = ⊤} / ENNReal.ofReal h ≤ M h / ENNReal.ofReal h := by
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      refine ENNReal.div_le_div_right ?_ _
      refine le_of_eq_of_le (lintegral_indicator_one
        (μ := μ) (hT (measurableSet_singleton ⊤))).symm (lintegral_mono fun ω => ?_)
      by_cases hω : T ω = ⊤
      · have h0 := PercLib.Analysis.exp_neg_mul_top hh
        rw [hω, h0, tsub_zero]
        exact Set.indicator_le_self' (fun _ _ => bot_le) ω
      · simp [Set.indicator, hω]
    have hdiv : Tendsto (fun h : ℝ => μ {ω | T ω = ⊤} / ENNReal.ofReal h) (𝓝[>] 0) (𝓝 ⊤) := by
      have h0 : Tendsto (fun h : ℝ => ENNReal.ofReal h) (𝓝[>] 0) (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal nhdsWithin_le_nhds
      have := ENNReal.Tendsto.div (tendsto_const_nhds (x := μ {ω | T ω = ⊤})) (Or.inl htop) h0
        (Or.inl ENNReal.zero_ne_top)
      rwa [ENNReal.div_zero htop] at this
    exact tendsto_nhds_top_mono hdiv hlowM

/-! ### 3C2F -/

/-- The ghost transform of a probability law is finite. -/
theorem lintegral_ghost_ne_top (h : ℝ) :
    ∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ ≠ ⊤ :=
  laplace_ne_top h

/-- `∑_{k=1}^m f(k) = ∑_{k<m} f(k+1)`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ k ∈ Icc 1 m, f k = ∑ k ∈ range m, f (k + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- **Real form of `laplace_le_sum_add`.** `M(h) ≤ h ∑_{k<m} P(T ≥ k+1) + P(T ≥ m+1)`. -/
theorem ghost_toReal_le (hT : Measurable T) {h : ℝ} (hh : 0 < h) (m : ℕ) :
    (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal ≤
      h * ∑ k ∈ range m, (μ {ω | ((k + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal +
        (μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal := by
  have hfin : ∀ j : ℕ, μ {ω | (j : ℕ∞) ≤ T ω} ≠ ⊤ := fun j => measure_ne_top μ _
  have hs := laplace_le_sum_add (μ := μ) hT hh m
  rw [sum_Icc_one_eq_sum_range (fun k => μ {ω | (k : ℕ∞) ≤ T ω})] at hs
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.sum_ne_top.2 fun j _ => hfin _), hfin _⟩) hs
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.sum_ne_top.2 fun j _ => hfin _)) (hfin _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hh.le, ENNReal.toReal_sum fun j _ => hfin _] at this

/-- **Real form of the lower bound.** `(1 - e^{-hN}) P(T ≥ N) ≤ M(h)`. -/
theorem le_ghost_toReal (hT : Measurable T) {h : ℝ} (hh : 0 < h) (N : ℕ) :
    (1 - Real.exp (-(h * N))) * (μ {ω | (N : ℕ∞) ≤ T ω}).toReal ≤
      (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal := by
  have h0 : 0 ≤ 1 - Real.exp (-(h * N)) := by
    have : -(h * N) ≤ 0 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; nlinarith
    linarith [Real.exp_le_one_iff.2 this]
  have := ENNReal.toReal_mono (lintegral_ghost_ne_top h)
    (mul_measure_le_lintegral_ghost (μ := μ) hT hh N)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0] at this

/-- A tail bound for `n ≥ N` extends to every `n ≥ 1` with the constant `max C N^α`. -/
theorem tail_le_of_ge {α C : ℝ} (hα : 0 < α) {N : ℕ}
    (h : ∀ n : ℕ, N ≤ n → 1 ≤ n → (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤ C * (n : ℝ) ^ (-α))
    (n : ℕ) (hn : 1 ≤ n) :
    (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤ max C ((N : ℝ) ^ α) * (n : ℝ) ^ (-α) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ) ^ (-α) := Real.rpow_pos_of_pos hnpos _
  rcases le_or_gt N n with hN | hN
  · exact (h n hN hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le)
  · have h1 : (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤ 1 := by
      have := prob_le_one (μ := μ) (s := {ω | (n : ℕ∞) ≤ T ω})
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    refine h1.trans ?_
    calc (1 : ℝ) = (n : ℝ) ^ α * (n : ℝ) ^ (-α) := by
          rw [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero]
      _ ≤ (N : ℝ) ^ α * (n : ℝ) ^ (-α) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hnpos.le (by exact_mod_cast hN.le) hα.le) hpow.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le

omit [IsProbabilityMeasure μ] in
/-- `∑_{k<m} P(T ≥ k+1) ≤ C m^{1-α}/(1-α)` under `P(T ≥ n) ≤ C n^{-α}` for `n ≥ 1`. -/
theorem sum_tail_le {α C : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 1 ≤ n → (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤ C * (n : ℝ) ^ (-α)) (m : ℕ) :
    ∑ k ∈ range m, (μ {ω | ((k + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal ≤
      C * ((m : ℝ) ^ (1 - α) / (1 - α)) := by
  calc ∑ k ∈ range m, (μ {ω | ((k + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal
      ≤ ∑ k ∈ range m, C * ((k : ℝ) + 1) ^ (-α) := Finset.sum_le_sum fun k _ => by
        have := h (k + 1) (by omega)
        push_cast at this
        exact this
    _ = C * ∑ k ∈ range m, ((k : ℝ) + 1) ^ (-α) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ((m : ℝ) ^ (1 - α) / (1 - α)) := mul_le_mul_of_nonneg_left
        (PercLib.Percolation.Bond.sum_rpow_neg_le m hα.le hα1) hC

/-- `⌈1/h⌉` for `0 < h ≤ 1`: `1/h ≤ m ≤ 2/h`. -/
theorem ceil_one_div_bounds {h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) :
    1 / h ≤ (⌈1 / h⌉₊ : ℝ) ∧ (⌈1 / h⌉₊ : ℝ) ≤ 2 / h ∧ 1 ≤ ⌈1 / h⌉₊ := by
  have hge : 1 ≤ 1 / h := by rw [le_div_iff₀ hh]; linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1 / h by positivity)
  refine ⟨Nat.le_ceil _, ?_, ?_⟩
  · have : 2 / h = 1 / h + 1 / h := by ring
    linarith
  · exact_mod_cast hge.trans (Nat.le_ceil (1 / h))

/-- **3C2F.** For `0 < α < 1`, `P(T ≥ n) ≍ n^{-α}` as `n → ∞` if and only if
`M(h) ≍ h^α` as `h ↓ 0` (two-sided bounds by positive constants). -/
@[tag "3C2F"]
theorem tail_asymp_iff_ghost_asymp (hT : Measurable T) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    (∃ c > 0, ∃ C > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n →
      c * (n : ℝ) ^ (-α) ≤ (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ∧
        (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤ C * (n : ℝ) ^ (-α)) ↔
    (∃ c > 0, ∃ C > 0, ∃ h₀ > 0, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      c * h ^ α ≤ (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal ∧
        (∫⁻ ω, (1 - EReal.exp (-((h : EReal) * ((T ω : ℝ≥0∞) : EReal)))) ∂μ).toReal ≤
          C * h ^ α) := by
  have he : 0 < 1 - Real.exp (-1) := by
    have := Real.exp_lt_one_iff.2 (show (-1 : ℝ) < 0 by norm_num)
    linarith
  have h1α : 0 < 1 - α := by linarith
  constructor
  · rintro ⟨c, hc, C, hC, N, hN⟩
    set C' := max C ((N : ℝ) ^ α) with hC'
    have hC'0 : 0 < C' := lt_max_of_lt_left hC
    have hall := tail_le_of_ge (μ := μ) hα (fun n h1 h2 => (hN n h1 h2).2)
    refine ⟨(1 - Real.exp (-1)) * c * 2 ^ (-α), by positivity,
      C' * (2 ^ (1 - α) / (1 - α) + 1), by positivity, 1 / ((N : ℝ) + 1), by positivity, ?_⟩
    intro h hh hh₀
    have hh1 : h ≤ 1 := hh₀.trans (by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
    obtain ⟨hm1, hm2, hm0⟩ := ceil_one_div_bounds hh hh1
    set m := ⌈1 / h⌉₊ with hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
    have hNm : N ≤ m := by
      have : (N : ℝ) + 1 ≤ 1 / h := by
        rw [le_div_iff₀ hh]; rw [le_div_iff₀ (by positivity)] at hh₀; linarith
      exact_mod_cast (show (N : ℝ) ≤ m by linarith)
    constructor
    · -- lower bound
      have hL := le_ghost_toReal (μ := μ) hT hh m
      have hhm : 1 ≤ h * m := by rw [div_le_iff₀ hh] at hm1; linarith
      have hexp : 1 - Real.exp (-1) ≤ 1 - Real.exp (-(h * m)) := by
        linarith [Real.exp_le_exp.2 (show -(h * m) ≤ -1 by linarith)]
      have hPm := (hN m hNm hm0).1
      have hmα : 2 ^ (-α) * h ^ α ≤ (m : ℝ) ^ (-α) := by
        have : (m : ℝ) ^ (-α) ≥ (2 / h) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hmpos hm2 (by linarith)
        rw [div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity),
          Real.inv_rpow hh.le, Real.rpow_neg hh.le, inv_inv] at this
        linarith
      have hP0 : 0 ≤ (μ {ω | (m : ℕ∞) ≤ T ω}).toReal := ENNReal.toReal_nonneg
      calc (1 - Real.exp (-1)) * c * 2 ^ (-α) * h ^ α
          = (1 - Real.exp (-1)) * (c * (2 ^ (-α) * h ^ α)) := by ring
        _ ≤ (1 - Real.exp (-(h * m))) * (μ {ω | (m : ℕ∞) ≤ T ω}).toReal :=
            mul_le_mul hexp ((mul_le_mul_of_nonneg_left hmα hc.le).trans hPm) (by positivity)
              (by linarith)
        _ ≤ _ := hL
    · -- upper bound
      have hU := ghost_toReal_le (μ := μ) hT hh m
      have hS := sum_tail_le (μ := μ) hα hα1 hC'0.le hall m
      have hP := hall (m + 1) (by omega)
      have hpow1 : h * (m : ℝ) ^ (1 - α) ≤ 2 ^ (1 - α) * h ^ α := by
        have : (m : ℝ) ^ (1 - α) ≤ (2 / h) ^ (1 - α) := Real.rpow_le_rpow hmpos.le hm2 h1α.le
        rw [Real.div_rpow (by norm_num) hh.le] at this
        calc h * (m : ℝ) ^ (1 - α) ≤ h * (2 ^ (1 - α) / h ^ (1 - α)) :=
              mul_le_mul_of_nonneg_left this hh.le
          _ = 2 ^ (1 - α) * (h / h ^ (1 - α)) := by ring
          _ = 2 ^ (1 - α) * h ^ α := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hh.le, ← Real.rpow_one_add' hh.le
                (by linarith)]
              congr 2; ring
      have hpow2 : ((m + 1 : ℕ) : ℝ) ^ (-α) ≤ h ^ α := by
        have : (1 / h : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
        have := Real.rpow_le_rpow_of_nonpos (by positivity) this (show -α ≤ 0 by linarith)
        rwa [one_div, Real.inv_rpow hh.le, ← Real.rpow_neg hh.le, neg_neg] at this
      calc _ ≤ h * ∑ k ∈ range m, (μ {ω | ((k + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal +
            (μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal := hU
        _ ≤ h * (C' * ((m : ℝ) ^ (1 - α) / (1 - α))) + C' * ((m + 1 : ℕ) : ℝ) ^ (-α) :=
            add_le_add (mul_le_mul_of_nonneg_left hS hh.le) hP
        _ = C' / (1 - α) * (h * (m : ℝ) ^ (1 - α)) + C' * ((m + 1 : ℕ) : ℝ) ^ (-α) := by ring
        _ ≤ C' / (1 - α) * (2 ^ (1 - α) * h ^ α) + C' * h ^ α :=
            add_le_add (mul_le_mul_of_nonneg_left hpow1 (by positivity))
              (mul_le_mul_of_nonneg_left hpow2 hC'0.le)
        _ = _ := by ring
  · rintro ⟨c, hc, C, hC, h₀, hh₀, hM⟩
    set N₀ := ⌈1 / h₀⌉₊ with hN₀
    -- Upper tail for `n ≥ N₀`, then for every `n ≥ 1`.
    have hup0 : ∀ n : ℕ, N₀ ≤ n → 1 ≤ n → (μ {ω | (n : ℕ∞) ≤ T ω}).toReal ≤
        C / (1 - Real.exp (-1)) * (n : ℝ) ^ (-α) := by
      intro n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hle : 1 / (n : ℝ) ≤ h₀ := by
        rw [div_le_iff₀ hnpos]
        have := (Nat.ceil_le).1 hn
        rw [div_le_iff₀ hh₀] at this
        linarith
      have hL := le_ghost_toReal (μ := μ) hT (show 0 < 1 / (n : ℝ) by positivity) n
      rw [one_div_mul_cancel hnpos.ne'] at hL
      have hU := (hM (1 / (n : ℝ)) (by positivity) hle).2
      have hpow : (1 / (n : ℝ)) ^ α = (n : ℝ) ^ (-α) := by
        rw [one_div, Real.inv_rpow hnpos.le, ← Real.rpow_neg hnpos.le]
      rw [hpow] at hU
      rw [div_mul_eq_mul_div, le_div_iff₀ he]
      nlinarith
    set C₁ := max (C / (1 - Real.exp (-1))) ((N₀ : ℝ) ^ α) with hC₁
    have hC₁0 : 0 < C₁ := lt_max_of_lt_left (by positivity)
    have hall := tail_le_of_ge (μ := μ) hα hup0
    -- The scale factor `L`.
    set L : ℝ := max 1 ((2 * C₁ / (c * (1 - α))) ^ (1 / (1 - α))) with hL
    have hL1 : 1 ≤ L := le_max_left _ _
    have hL0 : 0 < L := by linarith
    have hLpow : 2 * C₁ / (c * (1 - α)) ≤ L ^ (1 - α) := by
      calc 2 * C₁ / (c * (1 - α)) = ((2 * C₁ / (c * (1 - α))) ^ (1 / (1 - α))) ^ (1 - α) := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1α.ne', Real.rpow_one]
        _ ≤ L ^ (1 - α) := Real.rpow_le_rpow (by positivity) (le_max_right _ _) h1α.le
    have hkey : C₁ / ((1 - α) * L) ≤ c * L ^ (-α) / 2 := by
      have hLα : L ^ (-α) = L ^ (1 - α) / L := by
        rw [Real.rpow_sub hL0, Real.rpow_one, Real.rpow_neg hL0.le]
        field_simp
      rw [hLα, div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_le_iff₀ (by positivity)] at hLpow
      have : c * (L ^ (1 - α) / L) * ((1 - α) * L) = L ^ (1 - α) * (c * (1 - α)) := by
        field_simp
      linarith
    refine ⟨c * L ^ (-α) / 2 * 2 ^ (-α), by positivity, C₁, hC₁0, N₀ + 2, fun n hn hn1 => ?_⟩
    refine ⟨?_, hall n hn1⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    set t := 1 / (L * m) with ht
    have ht0 : 0 < t := by positivity
    have htle : t ≤ h₀ := by
      rw [ht, div_le_iff₀ (by positivity)]
      have h1 : 1 / h₀ ≤ (N₀ : ℝ) := Nat.le_ceil _
      have h2 : (N₀ : ℝ) ≤ m := by exact_mod_cast (show N₀ ≤ m by omega)
      rw [div_le_iff₀ hh₀] at h1
      calc (1 : ℝ) ≤ N₀ * h₀ := h1
        _ ≤ m * h₀ := mul_le_mul_of_nonneg_right h2 hh₀.le
        _ ≤ (L * m) * h₀ := mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_left hmpos.le hL1) hh₀.le
        _ = h₀ * (L * m) := by ring
    have hlow := (hM t ht0 htle).1
    have hU := ghost_toReal_le (μ := μ) hT ht0 m
    have hS := sum_tail_le (μ := μ) hα hα1 hC₁0.le hall m
    have htα : t ^ α = L ^ (-α) * (m : ℝ) ^ (-α) := by
      rw [ht, one_div, Real.inv_rpow (by positivity), Real.mul_rpow hL0.le hmpos.le,
        Real.rpow_neg hL0.le, Real.rpow_neg hmpos.le, mul_inv]
    have htm : t * ((m : ℝ) ^ (1 - α) / (1 - α)) = 1 / ((1 - α) * L) * (m : ℝ) ^ (-α) := by
      rw [ht, Real.rpow_sub hmpos, Real.rpow_one, Real.rpow_neg hmpos.le]
      field_simp
    -- `P(T ≥ m+1) ≥ (c L^{-α}/2) m^{-α}`
    have hPm : c * L ^ (-α) / 2 * (m : ℝ) ^ (-α) ≤
        (μ {ω | ((m + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal := by
      have h1 : t * ∑ k ∈ range m, (μ {ω | ((k + 1 : ℕ) : ℕ∞) ≤ T ω}).toReal ≤
          C₁ / ((1 - α) * L) * (m : ℝ) ^ (-α) := by
        calc _ ≤ t * (C₁ * ((m : ℝ) ^ (1 - α) / (1 - α))) := mul_le_mul_of_nonneg_left hS ht0.le
          _ = C₁ * (t * ((m : ℝ) ^ (1 - α) / (1 - α))) := by ring
          _ = C₁ / ((1 - α) * L) * (m : ℝ) ^ (-α) := by rw [htm]; ring
      have h2 : C₁ / ((1 - α) * L) * (m : ℝ) ^ (-α) ≤ c * L ^ (-α) / 2 * (m : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      rw [htα] at hlow
      nlinarith
    have hmm : (2 : ℝ) ^ (-α) * ((m + 1 : ℕ) : ℝ) ^ (-α) ≤ (m : ℝ) ^ (-α) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      refine Real.rpow_le_rpow_of_nonpos hmpos ?_ (by linarith)
      push_cast; linarith
    calc c * L ^ (-α) / 2 * 2 ^ (-α) * ((m + 1 : ℕ) : ℝ) ^ (-α)
        = c * L ^ (-α) / 2 * (2 ^ (-α) * ((m + 1 : ℕ) : ℝ) ^ (-α)) := by ring
      _ ≤ c * L ^ (-α) / 2 * (m : ℝ) ^ (-α) := mul_le_mul_of_nonneg_left hmm (by positivity)
      _ ≤ _ := hPm

/-! ### CVCN -/

/-- `x ↦ x^p` is `p`-Lipschitz on `[0, 1]` for `p ≥ 1`. -/
theorem lipschitzOnWith_rpow_Icc {p : ℝ} (hp : 1 ≤ p) :
    LipschitzOnWith (Real.toNNReal p) (fun x : ℝ => x ^ p) (Icc 0 1) := by
  refine (convex_Icc 0 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x => p * x ^ (p - 1)) (fun x _ =>
      (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt) fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by linarith), Real.norm_eq_abs,
    abs_of_nonneg (by have := Real.rpow_nonneg hx.1 (p - 1); positivity)]
  exact mul_le_of_le_one_right (by linarith)
    (Real.rpow_le_one hx.1 hx.2 (by linarith))

/-- **CVCN.** Let `m : (0, ∞) → [0, 1]` be nondecreasing and absolutely continuous on every
`[a, b] ⊆ (0, ∞)`, with `A m^r m' ≥ 1 - m^q` almost everywhere (`A, r, q > 0`). Then for
every `a ∈ (0, 1)` and `h > 0`, `m(h) ≥ min(a, ((r+1)(1 - a^q) h / A)^{1/(r+1)})`. -/
@[tag "CVCN"]
theorem min_le_of_ghost_ode {m : ℝ → ℝ} {A r q : ℝ} (hA : 0 < A) (hr : 0 < r) (hq : 0 < q)
    (hm01 : ∀ s, 0 < s → 0 ≤ m s ∧ m s ≤ 1) (hmono : MonotoneOn m (Ioi 0))
    (hac : ∀ a b, 0 < a → a ≤ b → AbsolutelyContinuousOnInterval m a b)
    (hode : ∀ᵐ s, 0 < s → 1 - m s ^ q ≤ A * m s ^ r * deriv m s)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℝ} (hh : 0 < h) :
    min a (((r + 1) * (1 - a ^ q) * h / A) ^ (1 / (r + 1))) ≤ m h := by
  by_cases hmh : a ≤ m h
  · exact (min_le_left _ _).trans hmh
  rw [not_le] at hmh
  refine (min_le_right _ _).trans ?_
  set K : ℝ := (r + 1) * (1 - a ^ q) / A with hK
  have haq : a ^ q < 1 := Real.rpow_lt_one ha0.le ha1 hq
  have hK0 : 0 ≤ K := by rw [hK]; exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hA.le
  have hr1 : 1 ≤ r + 1 := by linarith
  -- `m(h)^{r+1} ≥ K (h - ε)` for every `ε ∈ (0, h)`.
  have hstep : ∀ ε, 0 < ε → ε < h → K * (h - ε) ≤ m h ^ (r + 1) := by
    intro ε hε hεh
    have hacε := hac ε h hε hεh.le
    have hmaps : MapsTo m (uIcc ε h) (Icc 0 1) := fun s hs => by
      rw [uIcc_of_le hεh.le] at hs
      exact hm01 s (hε.trans_le hs.1)
    have hF : AbsolutelyContinuousOnInterval (fun s => m s ^ (r + 1)) ε h :=
      (lipschitzOnWith_rpow_Icc hr1).comp_absolutelyContinuousOnInterval hmaps hacε
    have hder : ∀ᵐ s, s ∈ Icc ε h → K ≤ deriv (fun s => m s ^ (r + 1)) s := by
      filter_upwards [hacε.ae_differentiableAt, hode] with s hd hs hsI
      have hs0 : 0 < s := hε.trans_le hsI.1
      have hdm := (hd (by rwa [uIcc_of_le hεh.le])).hasDerivAt
      have hD := hdm.rpow_const (p := r + 1) (Or.inr hr1)
      rw [hD.deriv, show r + 1 - 1 = r by ring]
      have hms := hm01 s hs0
      have hmsh : m s ≤ m h := hmono (Set.mem_Ioi.2 hs0) (Set.mem_Ioi.2 hh) hsI.2
      have hmq : m s ^ q ≤ a ^ q :=
        Real.rpow_le_rpow hms.1 (hmsh.trans hmh.le) hq.le
      have hode' := hs hs0
      rw [hK, div_le_iff₀ hA]
      have : 1 - a ^ q ≤ A * m s ^ r * deriv m s := by linarith
      nlinarith
    have hint := PercLib.Analysis.integral_le_sub_of_ae_le_deriv hεh.le hF
      intervalIntegrable_const hder
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hint
    have hε0 : 0 ≤ m ε ^ (r + 1) := Real.rpow_nonneg (hm01 ε hε).1 _
    linarith
  -- Let `ε ↓ 0`.
  have hKh : K * h ≤ m h ^ (r + 1) := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    by_cases hK0' : K = 0
    · rw [hK0', zero_mul]; exact (Real.rpow_nonneg (hm01 h hh).1 _).trans
        (le_add_of_nonneg_right hδ.le)
    have hKpos : 0 < K := lt_of_le_of_ne hK0 (Ne.symm hK0')
    set ε := min (h / 2) (δ / K) with hε
    have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
    have hεh : ε < h := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have := hstep ε hε0 hεh
    have hKε : K * ε ≤ δ := by
      calc K * ε ≤ K * (δ / K) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK0
        _ = δ := by field_simp
    linarith
  have hmh0 := (hm01 h hh).1
  calc ((r + 1) * (1 - a ^ q) * h / A) ^ (1 / (r + 1)) = (K * h) ^ (1 / (r + 1)) := by
        rw [hK]; ring_nf
    _ ≤ (m h ^ (r + 1)) ^ (1 / (r + 1)) :=
        Real.rpow_le_rpow (mul_nonneg hK0 hh.le) hKh (by positivity)
    _ = m h := by
        rw [← Real.rpow_mul hmh0, mul_one_div_cancel (by linarith), Real.rpow_one]

/-! ### Non-vacuity witnesses -/

section Witness

/-- Item 1 with `T = ⊤` almost surely: `M(h) → 1`. -/
example : Tendsto (fun h : ℝ => ∫⁻ _ω, (1 - EReal.exp (-((h : EReal) *
    (((⊤ : ℕ∞) : ℝ≥0∞) : EReal)))) ∂(Measure.dirac ())) (𝓝[>] 0) (𝓝 1) := by
  have := tendsto_lintegral_ghost (μ := Measure.dirac ()) (T := fun _ : Unit => (⊤ : ℕ∞))
    measurable_const
  simpa using this

/-- Item 1 with `T = ⊤` almost surely: `M(h)/h → E T = ⊤`. -/
example : Tendsto (fun h : ℝ => (∫⁻ _ω, (1 - EReal.exp (-((h : EReal) *
    (((⊤ : ℕ∞) : ℝ≥0∞) : EReal)))) ∂(Measure.dirac ())) / ENNReal.ofReal h) (𝓝[>] 0)
    (𝓝 ⊤) := by
  have := tendsto_lintegral_ghost_div (μ := Measure.dirac ()) (T := fun _ : Unit => (⊤ : ℕ∞))
    measurable_const
  simpa using this

/-- The variable `T(u) = ⌊u^{-2}⌋` under the uniform law on `(0, 1]` has
`P(T ≥ n) = n^{-1/2}` for `n ≥ 1`. -/
theorem measure_floor_inv_sq_ge {n : ℕ} (hn : 1 ≤ n) :
    ((volume.restrict (Ioc (0 : ℝ) 1)) {u : ℝ | (n : ℕ∞) ≤ (⌊u⁻¹ ^ 2⌋₊ : ℕ∞)}).toReal =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsn1 : 1 ≤ √(n : ℝ) := by rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hset : {u : ℝ | (n : ℕ∞) ≤ (⌊u⁻¹ ^ 2⌋₊ : ℕ∞)} ∩ Ioc 0 1 = Ioc 0 (1 / √(n : ℝ)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioc, Nat.cast_le]
    constructor
    · rintro ⟨h1, hu0, -⟩
      refine ⟨hu0, ?_⟩
      have h2 : (n : ℝ) ≤ u⁻¹ ^ 2 := (Nat.le_floor_iff (by positivity)).1 h1
      have h3 : √(n : ℝ) ≤ u⁻¹ := by
        rw [Real.sqrt_le_left (by positivity)]; exact h2
      rw [le_div_iff₀ hsn]
      rw [le_inv_comm₀ hsn hu0] at h3
      calc u * √(n : ℝ) ≤ (√(n : ℝ))⁻¹ * √(n : ℝ) := mul_le_mul_of_nonneg_right h3 hsn.le
        _ = 1 := inv_mul_cancel₀ hsn.ne'
    · rintro ⟨hu0, hu⟩
      refine ⟨?_, hu0, hu.trans (by rw [div_le_one hsn]; exact hsn1)⟩
      refine (Nat.le_floor_iff (by positivity)).2 ?_
      have h3 : √(n : ℝ) ≤ u⁻¹ := by
        rw [le_inv_comm₀ hsn hu0]; rwa [one_div] at hu
      calc (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt hnpos.le).symm
        _ ≤ u⁻¹ ^ 2 := pow_le_pow_left₀ hsn.le h3 2
  rw [Measure.restrict_apply' measurableSet_Ioc, hset, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal (by positivity), Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow,
    one_div]

/-- Item 3 at `α = 1/2`: for `T(u) = ⌊u^{-2}⌋` under the uniform law on `(0, 1]`,
`P(T ≥ n) = n^{-1/2}`, so `M(h) ≍ h^{1/2}`. -/
example : ∃ c > 0, ∃ C > 0, ∃ h₀ > 0, ∀ h : ℝ, 0 < h → h ≤ h₀ →
    c * h ^ (1 / 2 : ℝ) ≤ (∫⁻ u, (1 - EReal.exp (-((h : EReal) *
      (((⌊u⁻¹ ^ 2⌋₊ : ℕ∞) : ℝ≥0∞) : EReal)))) ∂(volume.restrict (Ioc (0 : ℝ) 1))).toReal ∧
    (∫⁻ u, (1 - EReal.exp (-((h : EReal) *
      (((⌊u⁻¹ ^ 2⌋₊ : ℕ∞) : ℝ≥0∞) : EReal)))) ∂(volume.restrict (Ioc (0 : ℝ) 1))).toReal ≤
      C * h ^ (1 / 2 : ℝ) := by
  have : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; simp⟩
  have hT : Measurable fun u : ℝ => (⌊u⁻¹ ^ 2⌋₊ : ℕ∞) :=
    (measurable_of_countable (fun k : ℕ => (k : ℕ∞))).comp
      (Nat.measurable_floor.comp ((measurable_inv).pow_const 2))
  refine (tail_asymp_iff_ghost_asymp (μ := volume.restrict (Ioc (0 : ℝ) 1)) hT
    (by norm_num) (by norm_num)).1 ⟨1, one_pos, 1, one_pos, 1, fun n _ hn => ?_⟩
  rw [measure_floor_inv_sq_ge hn, one_mul]
  exact ⟨le_rfl, le_rfl⟩

/-- Item 4 with `m(s) = √(1 - e^{-2s})`, `A = r = 1`, `q = 2`: here `m m' = 1 - m²`
exactly, and every hypothesis holds. -/
example {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℝ} (hh : 0 < h) :
    min a (((1 + 1) * (1 - a ^ (2 : ℝ)) * h / 1) ^ (1 / (1 + 1 : ℝ))) ≤
      √(1 - Real.exp (-(2 * h))) := by
  have hpos : ∀ s : ℝ, 0 < s → 0 < 1 - Real.exp (-(2 * s)) := fun s hs => by
    have := Real.exp_lt_one_iff.2 (show -(2 * s) < 0 by linarith)
    linarith
  have hderiv : ∀ s : ℝ, 0 < s → HasDerivAt (fun s => √(1 - Real.exp (-(2 * s))))
      (-(Real.exp (-(2 * s)) * -2) / (2 * √(1 - Real.exp (-(2 * s))))) s := fun s hs => by
    have h1 : HasDerivAt (fun s : ℝ => -(2 * s)) (-2) s := by
      have := ((hasDerivAt_id s).const_mul (2 : ℝ)).neg
      simp only [id, mul_one] at this
      exact this
    exact (h1.exp.const_sub 1).sqrt (hpos s hs).ne'
  refine min_le_of_ghost_ode (m := fun s => √(1 - Real.exp (-(2 * s)))) one_pos one_pos
    two_pos (fun s hs => ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.2 (by
      linarith [Real.exp_pos (-(2 * s))])⟩) ?_ ?_ ?_ ha0 ha1 hh
  · intro s _ t _ hst
    exact Real.sqrt_le_sqrt (by linarith [Real.exp_le_exp.2 (show -(2 * t) ≤ -(2 * s) by
      linarith)])
  · intro x y hx hxy
    refine ContDiffOn.absolutelyContinuousOnInterval ?_
    intro s hs
    have hs0 : 0 < s := by
      rw [uIcc_of_le hxy] at hs; exact hx.trans_le hs.1
    refine ContDiffAt.contDiffWithinAt ?_
    refine ContDiffAt.sqrt ?_ (hpos s hs0).ne'
    fun_prop
  · refine Eventually.of_forall fun s hs => ?_
    rw [(hderiv s hs).deriv, Real.rpow_one, Real.rpow_two, Real.sq_sqrt (hpos s hs).le]
    have hsq := Real.sqrt_pos.2 (hpos s hs)
    field_simp
    ring_nf
    exact le_rfl

end Witness

end PercLib.Probability
