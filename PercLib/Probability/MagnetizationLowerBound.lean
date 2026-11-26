/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-22. No upstream proof is copied and no definition is added.
Mathematical reference: the square-root lower bound for the magnetization obtained by
integrating the Aizenman–Barsky differential inequality from the positive-field limit
(Aizenman–Barsky 1987; Heydenreich–van der Hofstad, *Progress in high-dimensional
percolation and random graphs*, Ch. 4).
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Basic.Real.ENatENNReal

/-!
# A magnetization lower bound from a differential inequality

Let `T` be an `ℕ∞`-valued random variable with `T ≥ 1` (a cluster volume) and, for
`0 < γ < 1`, let `m(γ) = P(T = ∞) + ∑_{k ≥ 1} (1 - (1 - γ)^k) P(T = k)` be its magnetization.
If `m ≤ γ m' + m² + A m² m'` on `(0, 1)` for some `A ≥ 0`, then with `K = A + 1` and
`u = 1 / E[T; T < ∞]`,
`m(γ) ≥ √(γ / K + (u / (2K))²) - u / (2K)`.

The proof does not invert `m`: the function `γ / m(γ) - γ - A m(γ)` is nonincreasing on
`(0, 1)`, and `γ / m(γ)` has limit inferior at most `u` as `γ ↓ 0`.

## Main results

* `le_mul_add_mul_sq_of_le_deriv`: the analytic core, for any differentiable `m`.
* `sqrt_sub_le_of_le_mul_add_mul_sq`: solving the quadratic inequality `γ ≤ u m + K m²`.
* `hasDerivAt_magnetizationSeries`, `le_magnetizationSeries`,
  `eventually_le_mul_magnetizationSeries`: properties of the series
  `θ + ∑ (1 - (1 - γ)^k) p_k`.
* `lintegral_ne_top_eq_tsum`: `E[T; T < ∞] = ∑ k P(T = k)`.
* `sqrt_sub_le_magnetization_of_le_deriv`: the magnetization lower bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal Topology

namespace PercLib.Probability

/-! ### The analytic core -/

/-- If `m ≤ γ m' + m² + A m² m'` and `γ ≤ m` on `(0, 1)`, with `m` differentiable there and
`γ ≤ v m(γ)` near `0⁺` for every `v > u`, then `γ ≤ u m(γ) + (A + 1) m(γ)²` on `(0, 1)`. -/
theorem le_mul_add_mul_sq_of_le_deriv {m : ℝ → ℝ} {A u : ℝ} (hA : 0 ≤ A)
    (hdiff : DifferentiableOn ℝ m (Ioo 0 1)) (hle : ∀ γ ∈ Ioo (0 : ℝ) 1, γ ≤ m γ)
    (hineq : ∀ γ ∈ Ioo (0 : ℝ) 1,
      m γ ≤ γ * deriv m γ + m γ ^ 2 + A * m γ ^ 2 * deriv m γ)
    (hlim : ∀ v, u < v → ∀ᶠ γ in 𝓝[>] 0, γ ≤ v * m γ) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    γ ≤ u * m γ + (A + 1) * m γ ^ 2 := by
  have hpos : ∀ x ∈ Ioo (0 : ℝ) 1, 0 < m x := fun x hx => hx.1.trans_le (hle x hx)
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun y => y / m y - y - A * m y)
      ((1 * m x - x * deriv m x) / m x ^ 2 - 1 - A * deriv m x) x := by
    intro x hx
    have hm : HasDerivAt m (deriv m x) x :=
      (hdiff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    exact HasDerivAt.sub (HasDerivAt.sub (HasDerivAt.div (hasDerivAt_id' x) hm (hpos x hx).ne')
      (hasDerivAt_id' x)) (HasDerivAt.const_mul A hm)
  have hanti : AntitoneOn (fun y => y / m y - y - A * m y) (Ioo 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_ <;> rw [interior_Ioo]
    · exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x hx).deriv]
      have h1 := hineq x hx
      have hm2 : 0 < m x ^ 2 := pow_pos (hpos x hx) 2
      rw [sub_sub, sub_nonpos, div_le_iff₀ hm2]
      nlinarith [h1]
  have hbound : γ / m γ - γ - A * m γ ≤ u := by
    refine le_of_forall_gt_imp_ge_of_dense fun v hv => ?_
    obtain ⟨x, hxv, hx0, hxγ⟩ := ((hlim v hv).and (Ioo_mem_nhdsGT hγ.1)).exists
    have hx : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hxγ.trans hγ.2⟩
    have hmx := hpos x hx
    calc γ / m γ - γ - A * m γ ≤ x / m x - x - A * m x := hanti hx hγ hxγ.le
      _ ≤ x / m x := by nlinarith [mul_nonneg hA hmx.le, hx0]
      _ ≤ v := (div_le_iff₀ hmx).2 hxv
  have hmγ := hpos γ hγ
  have hγm := hle γ hγ
  have h1 : γ / m γ ≤ u + (A + 1) * m γ := by linarith
  rw [div_le_iff₀ hmγ] at h1
  linarith [h1, show (u + (A + 1) * m γ) * m γ = u * m γ + (A + 1) * m γ ^ 2 by ring]

/-- Solving the quadratic inequality: if `γ ≤ u m + K m²` with `K > 0`, `u, m ≥ 0`, then
`m ≥ √(γ / K + (u / (2K))²) - u / (2K)`. -/
theorem sqrt_sub_le_of_le_mul_add_mul_sq {K u m γ : ℝ} (hK : 0 < K) (hu : 0 ≤ u) (hm : 0 ≤ m)
    (h : γ ≤ u * m + K * m ^ 2) :
    √(γ / K + (u / (2 * K)) ^ 2) - u / (2 * K) ≤ m := by
  rw [sub_le_iff_le_add]
  have h2 : 0 ≤ m + u / (2 * K) := by positivity
  have h3 : γ / K ≤ (u * m + K * m ^ 2) / K := div_le_div_of_nonneg_right h hK.le
  have e1 : (u * m + K * m ^ 2) / K = m ^ 2 + u * m / K := by field_simp; ring
  have e2 : (m + u / (2 * K)) ^ 2 = m ^ 2 + u * m / K + (u / (2 * K)) ^ 2 := by
    field_simp; ring
  calc √(γ / K + (u / (2 * K)) ^ 2) ≤ √((m + u / (2 * K)) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [e2]; linarith)
    _ = m + u / (2 * K) := Real.sqrt_sq h2

/-! ### The magnetization series -/

section Series

variable {θ : ℝ} {p : ℕ → ℝ}

/-- `∑ k r^{k-1}` converges for `0 ≤ r < 1`. -/
theorem summable_mul_pow_sub_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ => (k : ℝ) * r ^ (k - 1) := by
  rcases hr0.eq_or_lt with rfl | hr
  · refine summable_of_ne_finset_zero (s := {1}) fun k hk => ?_
    rcases k with _ | _ | k <;> simp_all
  refine ((summable_pow_mul_geometric_of_norm_lt_one 1
    (by rwa [Real.norm_of_nonneg hr0])).mul_left r⁻¹).congr fun k => ?_
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

/-- Termwise differentiation of `θ + ∑ (1 - (1 - γ)^k) p_k` on `(0, 1)`. -/
theorem hasDerivAt_magnetizationSeries (hp0 : ∀ k, 0 ≤ p k) (hps : Summable p) {γ : ℝ}
    (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => θ + ∑' k, (1 - (1 - x) ^ k) * p k)
      (∑' k : ℕ, (k : ℝ) * (1 - γ) ^ (k - 1) * p k) γ := by
  refine HasDerivAt.const_add (f := fun x : ℝ => ∑' k, (1 - (1 - x) ^ k) * p k) θ ?_
  have hS : ∀ k, p k ≤ ∑' j, p j := fun k => hps.le_tsum k fun j _ => hp0 j
  refine hasDerivAt_tsum_of_isPreconnected (t := Ioo (γ / 2) 1)
    (g := fun k (x : ℝ) => (1 - (1 - x) ^ k) * p k)
    (g' := fun k (x : ℝ) => (k : ℝ) * (1 - x) ^ (k - 1) * p k)
    (u := fun k : ℕ => (k : ℝ) * (1 - γ / 2) ^ (k - 1) * ∑' j, p j)
    ((summable_mul_pow_sub_one (r := 1 - γ / 2) (by linarith [hγ.2])
      (by linarith [hγ.1])).mul_right _)
    isOpen_Ioo isPreconnected_Ioo (fun k y _ => ?_) (fun k y hy => ?_)
    (y₀ := γ) ⟨by linarith [hγ.1], hγ.2⟩ ?_ ⟨by linarith [hγ.1], hγ.2⟩
  · have := (((hasDerivAt_id' y).const_sub 1).pow k).const_sub 1 |>.mul_const (p k)
    convert this using 1
    ring
  · have hy0 : 0 ≤ 1 - y := by linarith [hy.2]
    rw [Real.norm_of_nonneg (by have := hp0 k; positivity), mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ hy0 (by linarith [hy.1]) _)
      (hS k) (hp0 k) (pow_nonneg (by linarith [hγ.2]) _)) (Nat.cast_nonneg k)
  · refine (hps.of_nonneg_of_le (fun k => ?_) fun k => ?_)
    · have : (1 - γ) ^ k ≤ 1 := pow_le_one₀ (by linarith [hγ.2]) (by linarith [hγ.1])
      exact mul_nonneg (by linarith) (hp0 k)
    · have : 0 ≤ (1 - γ) ^ k := pow_nonneg (by linarith [hγ.2]) k
      nlinarith [hp0 k]

/-- `0 ≤ 1 - (1 - γ)^k` for `γ ∈ [0, 1]`. -/
theorem one_sub_one_sub_pow_nonneg {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    0 ≤ 1 - (1 - γ) ^ k :=
  sub_nonneg.2 (pow_le_one₀ (by linarith) (by linarith))

/-- Summability of `(1 - (1 - γ)^k) p_k` for `γ ∈ [0, 1]`. -/
theorem summable_magnetizationSeries (hp0 : ∀ k, 0 ≤ p k) (hps : Summable p) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) : Summable fun k => (1 - (1 - γ) ^ k) * p k :=
  hps.of_nonneg_of_le
    (fun k => mul_nonneg (one_sub_one_sub_pow_nonneg hγ0 hγ1 k) (hp0 k))
    fun k => by nlinarith [hp0 k, pow_nonneg (by linarith : 0 ≤ 1 - γ) k]

/-- If `p_0 = 0` and `θ + ∑ p_k = 1`, then `γ ≤ θ + ∑ (1 - (1 - γ)^k) p_k` on `[0, 1]`. -/
theorem le_magnetizationSeries (hθ : 0 ≤ θ) (hp0 : ∀ k, 0 ≤ p k) (hps : Summable p)
    (hzero : p 0 = 0) (htot : θ + ∑' k, p k = 1) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    γ ≤ θ + ∑' k, (1 - (1 - γ) ^ k) * p k := by
  have hterm : ∀ k, γ * p k ≤ (1 - (1 - γ) ^ k) * p k := fun k => by
    rcases k with _ | k
    · simp [hzero]
    · have : (1 - γ) ^ (k + 1) ≤ 1 - γ :=
        pow_le_of_le_one (by linarith) (by linarith) (Nat.succ_ne_zero k)
      exact mul_le_mul_of_nonneg_right (by linarith) (hp0 _)
  have hsum := (hps.mul_left γ).tsum_le_tsum hterm
    (summable_magnetizationSeries hp0 hps hγ0 hγ1)
  rw [tsum_mul_left] at hsum
  nlinarith [mul_le_mul_of_nonneg_right hγ1 hθ]

/-- If `1 / v < ∑_{k < N} k p_k` with `v > 0`, then `γ ≤ v (θ + ∑ (1 - (1 - γ)^k) p_k)` for
all small `γ > 0`. -/
theorem eventually_le_mul_magnetizationSeries (hθ : 0 ≤ θ) (hp0 : ∀ k, 0 ≤ p k)
    (hps : Summable p) {v : ℝ} (hv : 0 < v) {N : ℕ}
    (hN : 1 / v < ∑ k ∈ range N, (k : ℝ) * p k) :
    ∀ᶠ γ in 𝓝[>] 0, γ ≤ v * (θ + ∑' k, (1 - (1 - γ) ^ k) * p k) := by
  set G : ℝ → ℝ := fun γ => ∑ k ∈ range N, (∑ j ∈ range k, (1 - γ) ^ j) * p k with hG
  have hG0 : G 0 = ∑ k ∈ range N, (k : ℝ) * p k := by simp [hG]
  have hcont : Continuous G := by fun_prop
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), 1 / v < G γ :=
    (hcont.continuousWithinAt.tendsto).eventually (lt_mem_nhds (hG0 ▸ hN))
  filter_upwards [hev, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with γ hγ hγ01
  have hid : ∀ k, (1 - (1 - γ) ^ k) * p k = γ * ((∑ j ∈ range k, (1 - γ) ^ j) * p k) :=
    fun k => by
      have := geom_sum_mul_neg (1 - γ) k
      rw [← this]; ring
  have hfin : γ * G γ ≤ ∑' k, (1 - (1 - γ) ^ k) * p k := by
    rw [hG, Finset.mul_sum]
    simp_rw [← hid]
    exact (summable_magnetizationSeries hp0 hps hγ01.1.le hγ01.2.le).sum_le_tsum _
      fun k _ => mul_nonneg (one_sub_one_sub_pow_nonneg hγ01.1.le hγ01.2.le k) (hp0 k)
  have h1 : γ * (1 / v) ≤ γ * G γ := mul_le_mul_of_nonneg_left hγ.le hγ01.1.le
  rw [mul_one_div, div_le_iff₀ hv] at h1
  calc γ ≤ γ * G γ * v := h1
    _ ≤ (∑' k, (1 - (1 - γ) ^ k) * p k) * v := mul_le_mul_of_nonneg_right hfin hv.le
    _ ≤ v * (θ + ∑' k, (1 - (1 - γ) ^ k) * p k) := by nlinarith [mul_nonneg hv.le hθ]

end Series

/-! ### From the random variable to the series -/

section RandomVariable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- Splitting a sum over `ℕ∞` into its value at `⊤` and its values at the naturals. -/
theorem ENat.tsum_eq_top_add_tsum_coe (f : ℕ∞ → ℝ≥0∞) :
    ∑' t, f t = f ⊤ + ∑' n : ℕ, f n := by
  rw [ENNReal.tsum_eq_add_tsum_ite ⊤]
  congr 1
  rw [← (Nat.cast_injective (R := ℕ∞)).tsum_eq]
  · simp
  · intro b hb
    have hb' : b ≠ ⊤ := fun h => hb (by simp [h])
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hb'
    exact ⟨n, rfl⟩

/-- `P(T = ∞) + ∑_k P(T = k) = μ(Ω)`. -/
theorem measure_eq_top_add_tsum (hT : Measurable T) :
    μ {ω | T ω = ⊤} + ∑' n : ℕ, μ {ω | T ω = n} = μ univ := by
  rw [← ENat.tsum_eq_top_add_tsum_coe (fun t => μ {ω | T ω = t}),
    ← measure_iUnion (f := fun t : ℕ∞ => {ω | T ω = t})
      (fun i j hij => Set.disjoint_left.2 fun ω h1 h2 => hij (h1.symm.trans h2))
      (fun t => hT (measurableSet_singleton t))]
  congr 1
  exact Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨T ω, rfl⟩

/-- `E[T; T < ∞] = ∑_k k P(T = k)`. -/
theorem lintegral_ne_top_eq_tsum (hT : Measurable T) :
    ∫⁻ ω in {ω | T ω ≠ ⊤}, (T ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, (n : ℝ≥0∞) * μ {ω | T ω = n} := by
  set g : ℕ∞ → ℝ≥0∞ := fun t => if t = ⊤ then 0 else (t : ℝ≥0∞) with hg
  have hS : MeasurableSet {ω | T ω ≠ ⊤} := (measurableSet_singleton ⊤).compl.preimage hT
  rw [← lintegral_indicator hS]
  have hfun : ({ω | T ω ≠ ⊤}.indicator fun ω => (T ω : ℝ≥0∞)) = fun ω => g (T ω) := by
    funext ω
    by_cases h : T ω = ⊤ <;> simp [Set.indicator, hg, h]
  rw [hfun, ← lintegral_map (measurable_of_countable g) hT, lintegral_countable',
    ENat.tsum_eq_top_add_tsum_coe]
  simp [hg, Measure.map_apply hT (measurableSet_singleton _), Set.preimage]

end RandomVariable

/-! ### The magnetization lower bound -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → ℕ∞}

/-- **Magnetization lower bound.** Let `T ≥ 1` be an `ℕ∞`-valued random variable with
`P(T < ∞) > 0`, and let `m(γ) = P(T = ∞) + ∑_k (1 - (1 - γ)^k) P(T = k)` for `0 < γ < 1`.
If `m ≤ γ m' + m² + A m² m'` on `(0, 1)` with `A ≥ 0`, then, with `K = A + 1` and
`u = 1 / E[T; T < ∞]` (`1 / ∞ = 0`), `m(γ) ≥ √(γ / K + (u / (2K))²) - u / (2K)`. -/
theorem sqrt_sub_le_magnetization_of_le_deriv [IsProbabilityMeasure μ] (hT : Measurable T)
    (hT1 : ∀ ω, 1 ≤ T ω) (hfin : 0 < μ {ω | T ω ≠ ⊤}) {m : ℝ → ℝ}
    (hm : ∀ γ ∈ Ioo (0 : ℝ) 1,
      m γ = μ.real {ω | T ω = ⊤} + ∑' k : ℕ, (1 - (1 - γ) ^ k) * μ.real {ω | T ω = k})
    {A : ℝ} (hA : 0 ≤ A)
    (hineq : ∀ γ ∈ Ioo (0 : ℝ) 1,
      m γ ≤ γ * deriv m γ + m γ ^ 2 + A * m γ ^ 2 * deriv m γ)
    {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    √(γ / (A + 1) + ((∫⁻ ω in {ω | T ω ≠ ⊤}, (T ω : ℝ≥0∞) ∂μ)⁻¹.toReal / (2 * (A + 1))) ^ 2) -
        (∫⁻ ω in {ω | T ω ≠ ⊤}, (T ω : ℝ≥0∞) ∂μ)⁻¹.toReal / (2 * (A + 1)) ≤ m γ := by
  set χ := ∫⁻ ω in {ω | T ω ≠ ⊤}, (T ω : ℝ≥0∞) ∂μ with hχ
  set u := χ⁻¹.toReal with hu
  set p : ℕ → ℝ := fun k => μ.real {ω | T ω = k} with hp
  set θ := μ.real {ω | T ω = ⊤} with hθ
  have hp0 : ∀ k, 0 ≤ p k := fun k => ENNReal.toReal_nonneg
  have hsumE := measure_eq_top_add_tsum (μ := μ) hT
  rw [measure_univ] at hsumE
  have hne : ∑' n : ℕ, μ {ω | T ω = n} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hsumE ▸ le_add_self)
  have hps : Summable p := ENNReal.summable_toReal hne
  have htot : θ + ∑' k, p k = 1 := by
    have := congrArg ENNReal.toReal hsumE
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hne,
      ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _, ENNReal.toReal_one] at this
  have hempty : {ω | T ω = 0} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h
    have := hT1 ω
    rw [h] at this
    exact absurd this (by decide)
  have hzero : p 0 = 0 := by
    simp only [hp, Nat.cast_zero, hempty, measureReal_empty]
  -- `E[T; T < ∞] ≠ 0`
  have hχ0 : χ ≠ 0 := by
    intro h0
    rw [hχ, lintegral_ne_top_eq_tsum hT, ENNReal.tsum_eq_zero] at h0
    have hnull : ∀ n : ℕ, μ {ω | T ω = n} = 0 := fun n => by
      rcases n with _ | n
      · simp only [Nat.cast_zero, hempty, measure_empty]
      · simpa using h0 (n + 1)
    refine hfin.ne' (measure_mono_null (fun ω (hω : T ω ≠ ⊤) => ?_)
      (measure_iUnion_null hnull))
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hω
    exact Set.mem_iUnion.2 ⟨n, hn.symm⟩
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  -- the hypotheses of the analytic core
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt m
      (∑' k : ℕ, (k : ℝ) * (1 - x) ^ (k - 1) * p k) x := fun x hx =>
    (hasDerivAt_magnetizationSeries (θ := θ) hp0 hps hx).congr_of_eventuallyEq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun y hy => hm y hy)
  have hdiff : DifferentiableOn ℝ m (Ioo 0 1) := fun x hx =>
    (hderiv x hx).differentiableAt.differentiableWithinAt
  have hle : ∀ x ∈ Ioo (0 : ℝ) 1, x ≤ m x := fun x hx => by
    rw [hm x hx]
    exact le_magnetizationSeries ENNReal.toReal_nonneg hp0 hps hzero htot hx.1.le hx.2.le
  have hlim : ∀ v, u < v → ∀ᶠ x in 𝓝[>] 0, x ≤ v * m x := by
    intro v hv
    have hv0 : 0 < v := hu0.trans_lt hv
    have hlt : ENNReal.ofReal (1 / v) < χ := by
      by_cases htop : χ = ⊤
      · rw [htop]; exact ENNReal.ofReal_lt_top
      · rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop]
        have hχpos : 0 < χ.toReal := ENNReal.toReal_pos hχ0 htop
        rw [hu, ENNReal.toReal_inv] at hv
        rw [one_div]
        exact (inv_lt_comm₀ hv0 hχpos).2 hv
    rw [hχ, lintegral_ne_top_eq_tsum hT, ENNReal.tsum_eq_iSup_nat] at hlt
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 hlt
    have hfinN : ∑ k ∈ range N, (k : ℝ≥0∞) * μ {ω | T ω = k} ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun k _ =>
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (measure_ne_top _ _)
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfinN, ENNReal.toReal_sum
      fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (measure_ne_top _ _)] at hN
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hN
    filter_upwards [eventually_le_mul_magnetizationSeries ENNReal.toReal_nonneg hp0 hps hv0 hN,
      Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx hx01
    rw [hm x hx01]
    exact hx
  exact sqrt_sub_le_of_le_mul_add_mul_sq (by linarith) hu0 (hγ.1.le.trans (hle γ hγ))
    (le_mul_add_mul_sq_of_le_deriv hA hdiff hle hineq hlim hγ)

end PercLib.Probability
