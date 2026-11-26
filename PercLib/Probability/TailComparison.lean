/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Analysis.Elementary
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Tail bounds from escape probabilities and window means; square-root lower tails

1. **HPE6.** Let `K` be a random subset of a countable set `V`, `Λ_r` deterministic finite
   sets (`r ≥ 1` an integer), `a > 0`, `b ≥ 0`, `C₁, C₂ ≥ 0`. Suppose
   `P(K ⊄ Λ_r) ≤ C₁ r^{-a}` and `E|K ∩ Λ_r| ≤ C₂ r^b`. Then:
   * `ae_finite_of_escape`: `K` is finite a.s.;
   * `measure_le_encard_le`: `P(|K| ≥ n) ≤ (2^a C₁ + C₂) n^{-a/(a+b)}`, taking
     `r = ⌊n^{1/(a+b)}⌋`;
   * `le_of_log_tail_exponent`: if `log P(|K| ≥ n)/log n → -1/δ` with `δ > 0`, then
     `δ ≤ (a+b)/a`.
2. **MBV2** (`le_of_sum_ge_sqrt`). Let `p_n ≥ 0` be nonincreasing on `n ≥ 1`, with
   `∑_{k=1}^N p_k ≥ c√N` for `N ≥ N₀` and `p_n ≤ C n^{-1/2}`. For an integer `A ≥ 2` with
   `c√A ≥ 4C`, `p_n ≥ c/(2√A) · n^{-1/2}` for `n ≥ N₀`.

No definition is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Finset
open scoped ENNReal Topology

namespace PercLib.Probability

/-! ### 1. HPE6 -/

section HPE6

variable {Ω V : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {K : Ω → Set V}

theorem measurableSet_not_subset [Countable V] (hK : ∀ x, MeasurableSet {ω | x ∈ K ω})
    (Λ : Finset V) :
    MeasurableSet {ω | ¬ K ω ⊆ Λ} := by
  have : {ω | ¬ K ω ⊆ Λ} = ⋃ x ∈ (Λ : Set V)ᶜ, {ω | x ∈ K ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.subset_def, not_forall, Set.mem_iUnion, Set.mem_compl_iff,
      Finset.mem_coe, exists_prop]
    constructor <;> rintro ⟨x, h1, h2⟩ <;> exact ⟨x, h2, h1⟩
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun x _ => hK x

theorem measurable_encard_inter (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (Λ : Finset V) :
    Measurable fun ω => ((K ω ∩ Λ).encard : ℝ≥0∞) := by
  classical
  have : (fun ω => ((K ω ∩ Λ).encard : ℝ≥0∞)) =
      fun ω => ∑ x ∈ Λ, {ω | x ∈ K ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    funext ω
    have hfin : (K ω ∩ Λ).Finite := (Λ.finite_toSet).subset Set.inter_subset_right
    rw [hfin.encard_eq_coe_toFinset_card]
    have : hfin.toFinset = Λ.filter (fun x => x ∈ K ω) := by
      ext x
      simp [and_comm]
    rw [this, Finset.card_filter]
    simp [Set.indicator]
  rw [this]
  exact Finset.measurable_sum
    (f := fun x ω => {ω | x ∈ K ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) _
    fun x _ => measurable_const.indicator (hK x)

/-- **Finiteness.** `K` is finite almost surely. -/
theorem ae_finite_of_escape (Λ : ℕ → Finset V) {a C₁ : ℝ} (ha : 0 < a)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ¬ K ω ⊆ Λ r} ≤ ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a))) :
    ∀ᵐ ω ∂μ, (K ω).Finite := by
  rw [ae_iff]
  have hlim : Tendsto (fun r : ℕ => ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero, ← mul_zero C₁]
    refine ENNReal.tendsto_ofReal (Tendsto.const_mul C₁ ?_)
    exact (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
  filter_upwards [eventually_ge_atTop 1] with r hr
  refine le_trans (measure_mono fun ω hω => ?_) (h1 r hr)
  intro hsub
  exact hω ((Λ r).finite_toSet.subset hsub)


/-- `⌊t⌋ ≥ t/2` for `t ≥ 1`. -/
theorem half_le_floor {t : ℝ} (ht : 1 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h1 : t - 1 < ⌊t⌋₊ := by
    have := Nat.lt_floor_add_one t
    linarith
  have h2 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.one_le_floor_iff t |>.2 ht
  rcases le_total t 2 with h | h <;> linarith

/-- **Tail bound.** `P(|K| ≥ n) ≤ (2^a C₁ + C₂) n^{-a/(a+b)}` for `n ≥ 1`. -/
theorem measure_le_encard_le (hK : ∀ x, MeasurableSet {ω | x ∈ K ω}) (Λ : ℕ → Finset V)
    {a b C₁ C₂ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ¬ K ω ⊆ Λ r} ≤ ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a)))
    (h2 : ∀ r : ℕ, 1 ≤ r →
      ∫⁻ ω, ((K ω ∩ Λ r).encard : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (C₂ * (r : ℝ) ^ b))
    {n : ℕ} (hn : 1 ≤ n) :
    μ {ω | (n : ℕ∞) ≤ (K ω).encard} ≤
      ENNReal.ofReal ((2 ^ a * C₁ + C₂) * (n : ℝ) ^ (-a / (a + b))) := by
  have hab : 0 < a + b := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set t := (n : ℝ) ^ (1 / (a + b)) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hn' (by positivity)
  set r := ⌊t⌋₊ with hr
  have hr1 : 1 ≤ r := Nat.one_le_floor_iff t |>.2 ht1
  have hrt : t / 2 ≤ (r : ℝ) := half_le_floor ht1
  have hrt' : (r : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  -- the two events
  have hsub : {ω | (n : ℕ∞) ≤ (K ω).encard} ⊆
      {ω | ¬ K ω ⊆ Λ r} ∪ {ω | (n : ℝ≥0∞) ≤ ((K ω ∩ Λ r).encard : ℝ≥0∞)} := by
    intro ω hω
    by_cases hs : K ω ⊆ Λ r
    · right
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [Set.inter_eq_left.2 hs]
      exact_mod_cast hω
    · exact Or.inl hs
  have hmarkov : μ {ω | (n : ℝ≥0∞) ≤ ((K ω ∩ Λ r).encard : ℝ≥0∞)} ≤
      ENNReal.ofReal (C₂ * (r : ℝ) ^ b) / n := by
    refine (meas_ge_le_lintegral_div (measurable_encard_inter hK (Λ r)).aemeasurable
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)) (ENNReal.natCast_ne_top n)).trans ?_
    gcongr
    exact h2 r hr1
  -- the arithmetic
  have hA : C₁ * (r : ℝ) ^ (-a) ≤ 2 ^ a * C₁ * (n : ℝ) ^ (-a / (a + b)) := by
    have : (r : ℝ) ^ (-a) ≤ (t / 2) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hrt (by linarith)
    have e : (t / 2) ^ (-a) = 2 ^ a * (n : ℝ) ^ (-a / (a + b)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ht, ← Real.rpow_mul (by linarith),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    nlinarith
  have hB : C₂ * (r : ℝ) ^ b / n ≤ C₂ * (n : ℝ) ^ (-a / (a + b)) := by
    have : (r : ℝ) ^ b ≤ t ^ b := Real.rpow_le_rpow hr0.le hrt' hb
    have e : t ^ b / n = (n : ℝ) ^ (-a / (a + b)) := by
      rw [ht, ← Real.rpow_mul (by linarith), div_eq_mul_inv, ← Real.rpow_neg_one,
        ← Real.rpow_add (by linarith)]
      congr 1
      field_simp
      ring
    rw [mul_div_assoc, ← e]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this (by linarith)) hC₂
  calc μ {ω | (n : ℕ∞) ≤ (K ω).encard}
      ≤ μ {ω | ¬ K ω ⊆ Λ r} + μ {ω | (n : ℝ≥0∞) ≤ ((K ω ∩ Λ r).encard : ℝ≥0∞)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a)) + ENNReal.ofReal (C₂ * (r : ℝ) ^ b) / n :=
        add_le_add (h1 r hr1) hmarkov
    _ = ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a) + C₂ * (r : ℝ) ^ b / n) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_div_of_pos
          (by linarith), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((2 ^ a * C₁ + C₂) * (n : ℝ) ^ (-a / (a + b))) :=
        ENNReal.ofReal_le_ofReal (by nlinarith)

/-- **Exponent.** If `log P(|K| ≥ n)/log n → -1/δ` with `δ > 0`, then
`δ ≤ (a+b)/a`. -/
theorem le_of_log_tail_exponent [IsProbabilityMeasure μ] (hK : ∀ x, MeasurableSet {ω | x ∈ K ω})
    (Λ : ℕ → Finset V) {a b C₁ C₂ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ r : ℕ, 1 ≤ r → μ {ω | ¬ K ω ⊆ Λ r} ≤ ENNReal.ofReal (C₁ * (r : ℝ) ^ (-a)))
    (h2 : ∀ r : ℕ, 1 ≤ r →
      ∫⁻ ω, ((K ω ∩ Λ r).encard : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (C₂ * (r : ℝ) ^ b))
    {δ : ℝ} (hδ : 0 < δ)
    (hlim : Tendsto (fun n : ℕ => Real.log (μ {ω | (n : ℕ∞) ≤ (K ω).encard}).toReal /
      Real.log n) atTop (𝓝 (-1 / δ))) :
    δ ≤ (a + b) / a := by
  have hab : 0 < a + b := by linarith
  set D := 2 ^ a * C₁ + C₂
  -- `log P ≤ log D' - (a/(a+b)) log n` with `D' = max D 1`
  have hbound : ∀ᶠ n : ℕ in atTop, Real.log (μ {ω | (n : ℕ∞) ≤ (K ω).encard}).toReal /
      Real.log n ≤ Real.log (max D 1) / Real.log n - a / (a + b) := by
    have hneg : ∀ᶠ n : ℕ in atTop, Real.log (μ {ω | (n : ℕ∞) ≤ (K ω).encard}).toReal /
        Real.log n < 0 := hlim.eventually (gt_mem_nhds (by
          rw [neg_div]
          exact neg_neg_of_pos (by positivity)))
    filter_upwards [hneg, eventually_ge_atTop 2] with n hneg hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hPle0 := measure_le_encard_le hK Λ ha hb hC₁ hC₂ h1 h2 (n := n) (by omega)
    generalize hPg : (μ {ω | (n : ℕ∞) ≤ (K ω).encard}) = PP at hneg hPle0 ⊢
    set P := PP.toReal
    have hP0 : 0 < P := by
      rcases (ENNReal.toReal_nonneg : 0 ≤ P).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [show P = 0 from h.symm, Real.log_zero, zero_div] at hneg
        exact lt_irrefl 0 hneg
    have hPle : P ≤ max D 1 * (n : ℝ) ^ (-a / (a + b)) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPle0
      rw [ENNReal.toReal_ofReal (by positivity)] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hlog := Real.log_le_log hP0 hPle
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by linarith)] at hlog
    rw [div_le_iff₀ hlogn, sub_mul, div_mul_cancel₀ _ hlogn.ne']
    have : -a / (a + b) * Real.log n = -(a / (a + b) * Real.log n) := by ring
    linarith
  have hlim2 : Tendsto (fun n : ℕ => Real.log (max D 1) / Real.log n - a / (a + b)) atTop
      (𝓝 (0 - a / (a + b))) :=
    (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).sub tendsto_const_nhds
  have := le_of_tendsto_of_tendsto hlim hlim2 hbound
  rw [zero_sub, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) hδ] at this
  rw [le_div_iff₀ ha]
  linarith

end HPE6

/-! ### 2. MBV2 -/

/-- **MBV2.** Let `p_n ≥ 0` be nonincreasing on `n ≥ 1`, `∑_{k=1}^N p_k ≥ c√N` for `N ≥ N₀`,
and `p_n ≤ C/√n` for `n ≥ 1`. For an integer `A ≥ 2` with `c√A ≥ 4C`,
`p_n ≥ c/(2√A) · n^{-1/2}` for every `n ≥ N₀`. -/
@[tag "MBV2"]
theorem le_of_sum_ge_sqrt {p : ℕ → ℝ} {c C : ℝ} {N₀ A : ℕ} (hN₀ : 1 ≤ N₀)
    (hp0 : ∀ n, 0 ≤ p n) (hmono : ∀ m n, 1 ≤ m → m ≤ n → p n ≤ p m)
    (hsum : ∀ N, N₀ ≤ N → c * Real.sqrt N ≤ ∑ k ∈ Icc 1 N, p k)
    (hup : ∀ n, 1 ≤ n → p n ≤ C / Real.sqrt n) (hA : 2 ≤ A)
    (hcA : 4 * C ≤ c * Real.sqrt A) {n : ℕ} (hn : N₀ ≤ n) :
    c / (2 * Real.sqrt A) / Real.sqrt n ≤ p n := by
  have hn1 : 1 ≤ n := hN₀.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.2 hA0
  have hAn : N₀ ≤ A * n := hn.trans (Nat.le_mul_of_pos_left n (by omega))
  have hS := hsum (A * n) hAn
  -- split the sum at `n`
  have hIcc : ∀ N : ℕ, Icc 1 N = Ioc 0 N := fun N => by ext k; simp; omega
  have hsplit : ∑ k ∈ Icc 1 (A * n), p k = ∑ k ∈ Icc 1 n, p k + ∑ k ∈ Ioc n (A * n), p k := by
    rw [hIcc, hIcc, Finset.sum_Ioc_consecutive _ (Nat.zero_le n)
      (Nat.le_mul_of_pos_left n (by omega))]
  have hfirst : ∑ k ∈ Icc 1 n, p k ≤ C * (2 * Real.sqrt n) := by
    calc ∑ k ∈ Icc 1 n, p k ≤ ∑ k ∈ Icc 1 n, C * (1 / Real.sqrt k) :=
          Finset.sum_le_sum fun k hk => by
            rw [mul_one_div]
            exact hup k (Finset.mem_Icc.1 hk).1
      _ = C * ∑ k ∈ Icc 1 n, 1 / Real.sqrt k := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (2 * Real.sqrt n) := by
          refine mul_le_mul_of_nonneg_left (PercLib.Analysis.sum_Icc_one_div_sqrt_le_two_mul n) ?_
          have h := (hp0 n).trans (hup n hn1)
          exact (div_nonneg_iff.1 h).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hsn)
  have hsecond : ∑ k ∈ Ioc n (A * n), p k ≤ ((A : ℝ) - 1) * n * p n := by
    calc ∑ k ∈ Ioc n (A * n), p k ≤ ∑ _k ∈ Ioc n (A * n), p n :=
          Finset.sum_le_sum fun k hk => hmono n k hn1 (Finset.mem_Ioc.1 hk).1.le
      _ = ((A : ℝ) - 1) * n * p n := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
          rw [Nat.cast_sub (Nat.le_mul_of_pos_left n (by omega))]
          push_cast
          ring
  have hsqrt : Real.sqrt ((A * n : ℕ) : ℝ) = Real.sqrt A * Real.sqrt n := by
    push_cast
    exact Real.sqrt_mul hA0.le _
  rw [hsplit, hsqrt] at hS
  -- `(A - 1) n p_n ≥ (c√A/2) √n`
  have hkey : c * Real.sqrt A / 2 * Real.sqrt n ≤ ((A : ℝ) - 1) * n * p n := by
    nlinarith
  have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  rw [div_div, div_le_iff₀ (by positivity)]
  have hpn := hp0 n
  have hsAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0.le
  have h3 : c * (Real.sqrt A * Real.sqrt n) ≤
      p n * (2 * Real.sqrt A * Real.sqrt n) * (Real.sqrt A * Real.sqrt n) := by
    have e : p n * (2 * Real.sqrt A * Real.sqrt n) * (Real.sqrt A * Real.sqrt n) =
        2 * ((A : ℝ) * n * p n) := by
      rw [show p n * (2 * Real.sqrt A * Real.sqrt n) * (Real.sqrt A * Real.sqrt n) =
        2 * ((Real.sqrt A * Real.sqrt A) * (Real.sqrt n * Real.sqrt n) * p n) by ring, hsAA, hnn]
    rw [e]
    have : ((A : ℝ) - 1) * n * p n ≤ A * n * p n := by
      have := mul_nonneg hn0.le hpn
      nlinarith
    nlinarith
  exact le_of_mul_le_mul_right h3 (by positivity)

/-! ### Non-vacuity -/

/-- `le_of_sum_ge_sqrt` with `p_n = n^{-1/2}`, `c = C = 1`, `N₀ = 1`, `A = 16`. -/
example (n : ℕ) (hn : 1 ≤ n) :
    1 / (2 * Real.sqrt (16 : ℕ)) / Real.sqrt n ≤ 1 / Real.sqrt n := by
  refine le_of_sum_ge_sqrt (p := fun k => 1 / Real.sqrt k) (c := 1) (C := 1) (N₀ := 1)
    le_rfl (fun k => by positivity) (fun m k hm hmk => ?_) (fun N hN => ?_) (fun k _ => le_rfl)
    (by norm_num)
    ?_ hn
  · have : (0 : ℝ) < m := by exact_mod_cast hm
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 this)
      (Real.sqrt_le_sqrt (by exact_mod_cast hmk))
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    calc 1 * Real.sqrt N = ∑ _k ∈ Icc 1 N, 1 / Real.sqrt N := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          field_simp
          rw [Real.sq_sqrt hN0.le]
      _ ≤ ∑ k ∈ Icc 1 N, 1 / Real.sqrt k := Finset.sum_le_sum fun k hk => by
          have hk := Finset.mem_Icc.1 hk
          have : (0 : ℝ) < k := by exact_mod_cast hk.1
          exact one_div_le_one_div_of_le (Real.sqrt_pos.2 this)
            (Real.sqrt_le_sqrt (by exact_mod_cast hk.2))
  · have : Real.sqrt ((16 : ℕ) : ℝ) = 4 := by
      rw [show ((16 : ℕ) : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
    norm_num

/-- The random-set tail comparison with `K = {o}` deterministic, `Λ_r = {o}`, `C₁ = 0`, `C₂ = 1`,
`b = 0`. -/
example (μ : Measure Unit) [IsProbabilityMeasure μ] (n : ℕ) (hn : 1 ≤ n) :
    μ {_ω | (n : ℕ∞) ≤ (({()} : Set Unit)).encard} ≤
      ENNReal.ofReal ((2 ^ (1 : ℝ) * 0 + 1) * (n : ℝ) ^ (-(1 : ℝ) / (1 + 0))) := by
  refine measure_le_encard_le (μ := μ) (K := fun _ => ({()} : Set Unit))
    (fun _ => MeasurableSet.const _)
    (fun _ => {()}) one_pos le_rfl le_rfl zero_le_one (fun r _ => ?_) (fun r _ => ?_) hn
  · simp
  · simp

end PercLib.Probability
