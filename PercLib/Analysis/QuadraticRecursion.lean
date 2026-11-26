/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied.
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quadratic recursions near a fixed point

Let `ψ : ℝ → ℝ` and `a > 0` with `ψ(u) = u - a u² + o(u²)` as `u → 0⁺`, written
`Tendsto (fun u => (ψ u - u + a u²) / u²) (𝓝[>] 0) (𝓝 0)`.

* `tendsto_inv_sub_inv` : `1/ψ(u) - 1/u → a` as `u → 0⁺`.
* **Survival core** (`tendsto_mul_of_quadratic_recursion`, wiki 8WO7). If `r_n > 0`,
  `r_{n+1} = ψ(r_n)` and `r_n → 0`, then `n r_n → 1/a`.
* **Yaglom core** (`tendsto_mul_yaglom`, wiki AYHV). Fix `λ > 0` and, for `n ≥ 1`, start
  from `u_{0,n} = 1 - e^{-λ/n}`, with `u_{k+1,n} = ψ(u_{k,n})` and
  `0 < u_{k,n} ≤ u_{0,n}` for `k ≤ n`. Then `n u_{n,n} → λ/(1 + aλ)`.
* `tendsto_one_sub_div_yaglom`. If moreover `n Q_n → 1/a`, then
  `1 - u_{n,n}/Q_n → 1/(1 + aλ)`.

No definition is introduced.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace PercLib.Analysis

variable {ψ : ℝ → ℝ} {a : ℝ}

/-- The reciprocal increment of the recursion tends to `a`. -/
theorem tendsto_inv_sub_inv
    (hψ : Tendsto (fun u => (ψ u - u + a * u ^ 2) / u ^ 2) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun u => 1 / ψ u - 1 / u) (𝓝[>] 0) (𝓝 a) := by
  set ε : ℝ → ℝ := fun u => (ψ u - u + a * u ^ 2) / u ^ 2 with hε
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hden : Tendsto (fun u => 1 - a * u + ε u * u) (𝓝[>] 0) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hu.const_mul a)).add (hψ.mul hu)
    simpa using this
  have hnum : Tendsto (fun u => a - ε u) (𝓝[>] 0) (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).sub hψ
  have hlim := hnum.div hden one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden.eventually (eventually_ne_nhds one_ne_zero)]
    with u (hu0 : 0 < u) hd
  have hu2 : u ^ 2 ≠ 0 := by positivity
  have hψu : ψ u = u * (1 - a * u + ε u * u) := by
    simp only [hε]
    field_simp
    ring
  have hψ0 : ψ u ≠ 0 := by rw [hψu]; exact mul_ne_zero hu0.ne' hd
  change (a - ε u) / (1 - a * u + ε u * u) = 1 / ψ u - 1 / u
  rw [hψu]
  field_simp
  ring

/-- A positive sequence tending to `0` tends to `0` within `(0, ∞)`. -/
theorem tendsto_nhdsWithin_Ioi_of_pos {r : ℕ → ℝ} (hpos : ∀ n, 0 < r n)
    (hr : Tendsto r atTop (𝓝 0)) : Tendsto r atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨hr, Eventually.of_forall hpos⟩

/-- **Survival core.** If `r_n > 0`, `r_{n+1} = ψ(r_n)` and `r_n → 0`, then
`n r_n → 1/a`. -/
theorem tendsto_mul_of_quadratic_recursion (ha : 0 < a)
    (hψ : Tendsto (fun u => (ψ u - u + a * u ^ 2) / u ^ 2) (𝓝[>] 0) (𝓝 0)) {r : ℕ → ℝ}
    (hpos : ∀ n, 0 < r n) (hrec : ∀ n, r (n + 1) = ψ (r n)) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * r n) atTop (𝓝 (1 / a)) := by
  have hd : Tendsto (fun n => 1 / r (n + 1) - 1 / r n) atTop (𝓝 a) := by
    simp_rw [hrec]
    exact (tendsto_inv_sub_inv hψ).comp (tendsto_nhdsWithin_Ioi_of_pos hpos hr)
  have hc := hd.cesaro
  have htel : ∀ n : ℕ, ∑ i ∈ range n, (1 / r (i + 1) - 1 / r i) = 1 / r n - 1 / r 0 :=
    fun n => sum_range_sub (fun i => 1 / r i) n
  simp_rw [htel] at hc
  have h0 : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * (1 / r 0)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (1 / r 0)
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) * r n)⁻¹) atTop (𝓝 a) := by
    have := hc.add h0
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : r n ≠ 0 := (hpos n).ne'
    field_simp
    ring
  have := hinv.inv₀ ha.ne'
  simpa [one_div] using this

/-- `n (1 - e^{-λ/n}) → λ`. -/
theorem tendsto_mul_one_sub_exp_neg_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - Real.exp (-(lam / n)))) atTop (𝓝 lam) := by
  have hlow : Tendsto (fun n : ℕ => lam / (1 + lam * (n : ℝ)⁻¹)) atTop (𝓝 lam) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul lam))
    rw [mul_zero, add_zero] at this
    have h := (tendsto_const_nhds (x := lam)).div this one_ne_zero
    rw [div_one] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hx : 0 < lam / n := div_pos hlam hn'
    have hexp : Real.exp (-(lam / n)) * (1 + lam / n) ≤ 1 := by
      have h1 := Real.add_one_le_exp (lam / n)
      have h2 : Real.exp (-(lam / n)) * Real.exp (lam / n) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos (-(lam / n))]
    rw [div_le_iff₀ (by positivity)]
    have : lam * (n : ℝ)⁻¹ = lam / n := by rw [div_eq_mul_inv]
    rw [this]
    have e : (n : ℝ) * (lam / n) = lam := by field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := Real.add_one_le_exp (-(lam / n))
    have e : (n : ℝ) * (lam / n) = lam := by field_simp
    nlinarith

/-- **Yaglom core.** Fix `λ > 0`. For `n ≥ 1` let `u_{0,n} = 1 - e^{-λ/n}`,
`u_{k+1,n} = ψ(u_{k,n})` and assume `0 < u_{k,n} ≤ u_{0,n}` for `k ≤ n`. Then
`n u_{n,n} → λ/(1 + aλ)`. -/
theorem tendsto_mul_yaglom (ha : 0 < a)
    (hψ : Tendsto (fun u => (ψ u - u + a * u ^ 2) / u ^ 2) (𝓝[>] 0) (𝓝 0)) {lam : ℝ}
    (hlam : 0 < lam) {u : ℕ → ℕ → ℝ} (hu0 : ∀ n, 1 ≤ n → u 0 n = 1 - Real.exp (-(lam / n)))
    (hrec : ∀ k n, u (k + 1) n = ψ (u k n))
    (hbd : ∀ n, 1 ≤ n → ∀ k ≤ n, 0 < u k n ∧ u k n ≤ u 0 n) :
    Tendsto (fun n : ℕ => (n : ℝ) * u n n) atTop (𝓝 (lam / (1 + a * lam))) := by
  have hg := tendsto_inv_sub_inv hψ
  -- `n u_{0,n} → λ`, so `u_{0,n} → 0`
  have hm0 : Tendsto (fun n : ℕ => (n : ℝ) * u 0 n) atTop (𝓝 lam) := by
    refine (tendsto_mul_one_sub_exp_neg_div hlam).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hu0 n hn]
  have hu00 : Tendsto (fun n => u 0 n) atTop (𝓝 0) := by
    have := hm0.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  -- the averaged reciprocal increments
  have hsum : ∀ n, 1 ≤ n → 1 / u n n - 1 / u 0 n =
      ∑ k ∈ range n, (1 / ψ (u k n) - 1 / u k n) := by
    intro n _
    rw [← sum_range_sub (fun k => 1 / u k n) n]
    refine sum_congr rfl fun k _ => ?_
    rw [hrec]
  have hdev : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (1 / u n n - 1 / u 0 n) - a) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1
      (hg (Metric.ball_mem_nhds a (half_pos hε)))
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu00 δ hδ
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnN : N ≤ n := le_of_max_le_left hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsmall : ∀ k ∈ range n, |(1 / ψ (u k n) - 1 / u k n) - a| < ε / 2 := by
      intro k hk
      have hk' : k ≤ n := (mem_range.1 hk).le
      obtain ⟨hpos, hle⟩ := hbd n hn1 k hk'
      have hδk : u k n ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi 0 := by
        refine ⟨?_, hpos⟩
        have h0 := hN n hnN
        rw [Real.dist_eq, sub_zero] at h0
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hpos]
        exact lt_of_le_of_lt hle ((le_abs_self _).trans_lt h0)
      have := hball hδk
      rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at this
    rw [Real.dist_eq, sub_zero, hsum n hn1]
    have hrw : (n : ℝ)⁻¹ * ∑ k ∈ range n, (1 / ψ (u k n) - 1 / u k n) - a =
        (n : ℝ)⁻¹ * ∑ k ∈ range n, ((1 / ψ (u k n) - 1 / u k n) - a) := by
      simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [hrw, abs_mul, abs_inv, abs_of_pos hn']
    calc (n : ℝ)⁻¹ * |∑ k ∈ range n, ((1 / ψ (u k n) - 1 / u k n) - a)|
        ≤ (n : ℝ)⁻¹ * ∑ k ∈ range n, |(1 / ψ (u k n) - 1 / u k n) - a| := by
          gcongr
          exact abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ _k ∈ range n, ε / 2 := by
          gcongr with k hk
          exact (hsmall k hk).le
      _ = ε / 2 := by
          rw [sum_const, card_range, nsmul_eq_mul]
          field_simp
      _ < ε := half_lt_self hε
  -- assembling
  have hinv0 : Tendsto (fun n : ℕ => ((n : ℝ) * u 0 n)⁻¹) atTop (𝓝 lam⁻¹) :=
    hm0.inv₀ hlam.ne'
  have hrecip : Tendsto (fun n : ℕ => ((n : ℝ) * u n n)⁻¹) atTop (𝓝 (lam⁻¹ + a)) := by
    have := (hdev.add hinv0).add (tendsto_const_nhds (x := a))
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h1 : u n n ≠ 0 := (hbd n hn n le_rfl).1.ne'
    have h2 : u 0 n ≠ 0 := (hbd n hn 0 (Nat.zero_le n)).1.ne'
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
    field_simp
    ring
  have hpos : lam⁻¹ + a ≠ 0 := (add_pos (inv_pos.2 hlam) ha).ne'
  have := hrecip.inv₀ hpos
  simp only [inv_inv] at this
  convert this using 2
  field_simp

/-- If moreover `n Q_n → 1/a`, then `1 - u_{n,n}/Q_n → 1/(1 + aλ)`. -/
theorem tendsto_one_sub_div_yaglom (ha : 0 < a)
    (hψ : Tendsto (fun u => (ψ u - u + a * u ^ 2) / u ^ 2) (𝓝[>] 0) (𝓝 0)) {lam : ℝ}
    (hlam : 0 < lam) {u : ℕ → ℕ → ℝ} (hu0 : ∀ n, 1 ≤ n → u 0 n = 1 - Real.exp (-(lam / n)))
    (hrec : ∀ k n, u (k + 1) n = ψ (u k n))
    (hbd : ∀ n, 1 ≤ n → ∀ k ≤ n, 0 < u k n ∧ u k n ≤ u 0 n) {Q : ℕ → ℝ}
    (hQ : Tendsto (fun n : ℕ => (n : ℝ) * Q n) atTop (𝓝 (1 / a))) :
    Tendsto (fun n => 1 - u n n / Q n) atTop (𝓝 (1 / (1 + a * lam))) := by
  have hY := tendsto_mul_yaglom ha hψ hlam hu0 hrec hbd
  have hdiv := hY.div hQ (one_div_ne_zero ha.ne')
  have hlim : 1 - lam / (1 + a * lam) / (1 / a) = 1 / (1 + a * lam) := by
    have : 1 + a * lam ≠ 0 := by positivity
    field_simp
    ring
  rw [← hlim]
  refine ((tendsto_const_nhds (x := (1 : ℝ))).sub hdiv).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Pi.div_apply]
  rw [mul_div_mul_left _ _ hn']

/-! ### Non-vacuity: `ψ(u) = u/(1 + a u)` -/

/-- `ψ(u) = u/(1 + au)` has the expansion `u - a u² + o(u²)`. -/
theorem tendsto_expansion_div_one_add {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun u => (u / (1 + a * u) - u + a * u ^ 2) / u ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun u : ℝ => a ^ 2 * u / (1 + a * u)) (𝓝[>] 0) (𝓝 0) := by
    have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    have := (hu.const_mul (a ^ 2)).div ((tendsto_const_nhds (x := (1 : ℝ))).add (hu.const_mul a))
      (by simp)
    rw [mul_zero, mul_zero, add_zero, zero_div] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  have : 1 + a * u ≠ 0 := by positivity
  field_simp
  ring

/-- The explicit orbit `r_n = r_0/(1 + n a r_0)` satisfies the hypotheses of the survival
core, so `n r_n → 1/a`. -/
example {a r₀ : ℝ} (ha : 0 < a) (hr₀ : 0 < r₀) :
    Tendsto (fun n : ℕ => (n : ℝ) * (r₀ / (1 + n * a * r₀))) atTop (𝓝 (1 / a)) := by
  refine tendsto_mul_of_quadratic_recursion (ψ := fun u => u / (1 + a * u)) ha
    (tendsto_expansion_div_one_add ha.le) (fun n => by positivity) (fun n => ?_) ?_
  · have h1 : 1 + n * a * r₀ ≠ 0 := by positivity
    have h2 : 1 + ((n + 1 : ℕ) : ℝ) * a * r₀ ≠ 0 := by positivity
    have h3 : 1 + a * (r₀ / (1 + n * a * r₀)) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · have h1 : Tendsto (fun n : ℕ => 1 + (n : ℝ) * a * r₀) atTop atTop := by
      refine tendsto_atTop_add_const_left _ 1 ?_
      simpa [mul_assoc] using tendsto_natCast_atTop_atTop.atTop_mul_const (mul_pos ha hr₀)
    exact (tendsto_const_nhds (x := r₀)).div_atTop h1

/-- The explicit Yaglom array `u_{k,n} = u_{0,n}/(1 + k a u_{0,n})` satisfies the hypotheses
of the Yaglom core. -/
example {a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * ((1 - Real.exp (-(lam / n))) /
      (1 + n * a * (1 - Real.exp (-(lam / n)))))) atTop (𝓝 (lam / (1 + a * lam))) := by
  have hu0pos : ∀ n : ℕ, 1 ≤ n → 0 < 1 - Real.exp (-(lam / n)) := by
    intro n hn
    have : (0 : ℝ) < lam / n := div_pos hlam (by exact_mod_cast hn)
    simpa using Real.exp_lt_one_iff.2 (neg_lt_zero.2 this)
  refine tendsto_mul_yaglom (ψ := fun u => u / (1 + a * u)) ha
    (tendsto_expansion_div_one_add ha.le) hlam
    (u := fun k n => (1 - Real.exp (-(lam / n))) / (1 + k * a * (1 - Real.exp (-(lam / n)))))
    (fun n _ => by simp) (fun k n => ?_) (fun n hn k _ => ⟨?_, ?_⟩)
  · have hw : 0 ≤ 1 - Real.exp (-(lam / n)) := by
      have : 0 ≤ lam / n := div_nonneg hlam.le (Nat.cast_nonneg n)
      simpa using Real.exp_le_one_iff.2 (neg_nonpos.2 this)
    set w := 1 - Real.exp (-(lam / n))
    have h1 : 1 + k * a * w ≠ 0 := by positivity
    have h2 : 1 + a * (w / (1 + k * a * w)) ≠ 0 := by positivity
    have h3 : 1 + ((k + 1 : ℕ) : ℝ) * a * w ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · have := hu0pos n hn
    positivity
  · have := hu0pos n hn
    simp only [Nat.cast_zero, zero_mul, add_zero, div_one]
    have hk : 0 ≤ (k : ℝ) * a * (1 - Real.exp (-(lam / n))) := by positivity
    exact div_le_self this.le (by linarith)

end PercLib.Analysis
