/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proofs, written on 2026-11-16, against pinned mathlib. No upstream proof is copied. Reuses
`PercLib/Probability/GeneratingFunction.lean`.
-/
module

public import PercLib.Probability.GeneratingFunction
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Critical generating functions: second-order expansion and the total-progeny transform

Let `p : PMF ℕ` be an offspring law with mean `1`, written `∑' k, k p(k) = 1` in `ℝ≥0∞` as in
`GeneratingFunction.lean`. Let `σ² = ∑ k(k-1) p(k) ∈ (0, ∞)` and
`φ(x) = ∑' k, p(k) x^k`.

1. **Expansion** (`tendsto_one_sub_genFun_expansion`). `φ(1-u) = 1 - u + (σ²/2) u² + o(u²)` as
   `u → 0⁺`. It is stated in the form used by `PercLib/Analysis/QuadraticRecursion.lean` for
   `ψ(u) = 1 - φ(1-u)` and `a = σ²/2`.
2. **Transform equation.** Fix `0 ≤ s < 1`.
   * `x ↦ s φ(x) - x` is strictly decreasing on `[0,1]`.
   * `existsUnique_transform_root`: it has exactly one zero `F(s)` in `[0,1)`.
   * `isLeast_transform_root`: that zero is the least zero in `[0,1]`.
   * `monotoneOn_transform_root`: `F` is nondecreasing.
   * `tendsto_transform_root`: `F(s) → 1` as `s ↑ 1`, when `σ² > 0`.
3. **OVG9, analytic** (`isEquivalent_one_sub_transform_root`). `1 - F(s) ~ √(2(1-s)/σ²)` as
   `s ↑ 1`.

`F` enters the statements as any function solving the equation on `[0,1)`. The
identification `F(s) = E[s^T]` with the total progeny `T` needs the process interface and is
not part of this file. No definition is introduced.
-/

@[expose] public section

noncomputable section

open Set Filter Finset Asymptotics
open scoped ENNReal Topology

namespace PercLib.Probability

/-! ### Polynomial bounds on `(1 - u)^k` -/

theorem natCast_mul_sub_one_nonneg (k : ℕ) : (0 : ℝ) ≤ k * (k - 1) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ k := by exact_mod_cast h
    nlinarith

theorem natCast_mul_sub_one_mul_sub_two_nonneg (k : ℕ) : (0 : ℝ) ≤ k * (k - 1) * (k - 2) := by
  rcases k with _ | _ | k
  · simp
  · simp
  · push_cast
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (0 : ℝ) ≤ (k + 2) * (k + 1) * k := by positivity
    nlinarith

/-- `(1 - u)^k ≤ 1 - ku + k(k-1)/2 u²` on `[0,1]`. -/
theorem one_sub_pow_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    (1 - u) ^ k ≤ 1 - k * u + (k * (k - 1) / 2) * u ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ 1 - u := by linarith
    have hc := natCast_mul_sub_one_nonneg k
    calc (1 - u) ^ (k + 1) = (1 - u) * (1 - u) ^ k := by ring
      _ ≤ (1 - u) * (1 - k * u + (k * (k - 1) / 2) * u ^ 2) := mul_le_mul_of_nonneg_left ih h1
      _ ≤ _ := by
        push_cast
        nlinarith [mul_nonneg hc (pow_nonneg hu0 3)]

/-- `(1 - u)^k ≥ 1 - ku + k(k-1)/2 u² - k(k-1)(k-2)/6 u³` on `[0,1]`. -/
theorem one_sub_pow_ge {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    1 - k * u + (k * (k - 1) / 2) * u ^ 2 - (k * (k - 1) * (k - 2) / 6) * u ^ 3 ≤
      (1 - u) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ 1 - u := by linarith
    have hd := natCast_mul_sub_one_mul_sub_two_nonneg k
    calc _ ≤ (1 - u) * (1 - k * u + (k * (k - 1) / 2) * u ^ 2 -
          (k * (k - 1) * (k - 2) / 6) * u ^ 3) := by
          push_cast
          nlinarith [mul_nonneg hd (pow_nonneg hu0 4)]
      _ ≤ (1 - u) * (1 - u) ^ k := mul_le_mul_of_nonneg_left ih h1
      _ = (1 - u) ^ (k + 1) := by ring

/-- `((1-u)^k - 1 + ku)/u² → k(k-1)/2` as `u → 0⁺`. -/
theorem tendsto_one_sub_pow_quotient (k : ℕ) :
    Tendsto (fun u : ℝ => ((1 - u) ^ k - 1 + k * u) / u ^ 2) (𝓝[>] 0)
      (𝓝 ((k : ℝ) * (k - 1) / 2)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlow : Tendsto (fun u : ℝ => (k : ℝ) * (k - 1) / 2 - (k * (k - 1) * (k - 2) / 6) * u)
      (𝓝[>] 0) (𝓝 ((k : ℝ) * (k - 1) / 2)) := by
    simpa using (tendsto_const_nhds (x := (k : ℝ) * (k - 1) / 2)).sub
      (hu.const_mul ((k : ℝ) * (k - 1) * (k - 2) / 6))
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev] with u hu
    rw [le_div_iff₀ (by nlinarith [hu.1])]
    nlinarith [one_sub_pow_ge hu.1.le hu.2.le k]
  · filter_upwards [hev] with u hu
    rw [div_le_iff₀ (by nlinarith [hu.1])]
    nlinarith [one_sub_pow_le hu.1.le hu.2.le k]

/-- `0 ≤ ((1-u)^k - 1 + ku)/u² ≤ k(k-1)/2` on `(0,1]`. -/
theorem one_sub_pow_quotient_mem {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (k : ℕ) :
    0 ≤ ((1 - u) ^ k - 1 + k * u) / u ^ 2 ∧
      ((1 - u) ^ k - 1 + k * u) / u ^ 2 ≤ (k : ℝ) * (k - 1) / 2 := by
  have hu2 : 0 < u ^ 2 := by positivity
  refine ⟨div_nonneg ?_ hu2.le, (div_le_iff₀ hu2).2 ?_⟩
  · have := one_add_mul_le_pow (a := -u) (by linarith) k
    rw [← sub_eq_add_neg, mul_neg] at this
    linarith
  · nlinarith [one_sub_pow_le hu0.le hu1 k]

variable (p : PMF ℕ)

/-- The mean hypothesis in real form. -/
theorem hasSum_mean_one (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) :
    HasSum (fun k : ℕ => (k : ℝ) * (p k).toReal) 1 := by
  have := hasSum_mean_toReal p (by rw [hm]; exact ENNReal.one_ne_top)
  rwa [hm, ENNReal.toReal_one] at this

/-! ### 1. The second-order expansion at one -/

/-- **Expansion.** `ψ(u) = 1 - φ(1-u)` satisfies `ψ(u) = u - (σ²/2) u² + o(u²)`, in the form used by
`PercLib/Analysis/QuadraticRecursion.lean`. -/
theorem tendsto_one_sub_genFun_expansion (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) σ2) :
    Tendsto (fun u => ((1 - ∑' k, (p k).toReal * (1 - u) ^ k) - u + σ2 / 2 * u ^ 2) / u ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hC := hasSum_mean_one p hm
  have hB := (summable_pmf_toReal p).hasSum
  rw [tsum_pmf_toReal] at hB
  have hD : HasSum (fun k : ℕ => (k : ℝ) * (k - 1) / 2 * (p k).toReal) (σ2 / 2) := by
    convert hσ.div_const 2 using 1
    funext k
    ring
  set g : ℝ → ℕ → ℝ := fun u k =>
    (p k).toReal * (((1 - u) ^ k - 1 + k * u) / u ^ 2 - (k : ℝ) * (k - 1) / 2) with hg
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), u ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hT : Tendsto (fun u => ∑' k, g u k) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := g) (g := fun _ => (0 : ℝ))
      (bound := fun k => (k : ℝ) * (k - 1) / 2 * (p k).toReal) hD.summable
      (fun k => by
        have := ((tendsto_one_sub_pow_quotient k).sub_const ((k : ℝ) * (k - 1) / 2)).const_mul
          (p k).toReal
        simpa using this)
      (by
        filter_upwards [hev] with u hu k
        obtain ⟨h0, h1⟩ := one_sub_pow_quotient_mem hu.1 hu.2.le k
        simp only [hg, Real.norm_eq_abs, abs_mul, ENNReal.abs_toReal]
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
        rw [abs_le]
        constructor <;> linarith)
    simpa using this
  have := hT.neg
  rw [neg_zero] at this
  refine this.congr' ?_
  filter_upwards [hev] with u hu
  have hu0 : u ≠ 0 := hu.1.ne'
  have hu2 : u ^ 2 ≠ 0 := by positivity
  have hA := (summable_genFun p (s := 1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).hasSum
  have hsum : HasSum (g u) ((∑' k, (p k).toReal * (1 - u) ^ k - 1 + u * 1 -
      u ^ 2 * (σ2 / 2)) / u ^ 2) := by
    convert (((hA.sub hB).add (hC.mul_left u)).sub (hD.mul_left (u ^ 2))).div_const (u ^ 2)
      using 1
    funext k
    simp only [hg]
    field_simp
  rw [hsum.tsum_eq]
  field_simp
  ring

/-! ### 2. The transform equation -/

/-- `y^k - x^k ≤ k (y - x)` on `0 ≤ x ≤ y ≤ 1`. -/
theorem pow_sub_pow_le_mul {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) (k : ℕ) :
    y ^ k - x ^ k ≤ k * (y - x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : x ^ k ≤ y ^ k := pow_le_pow_left₀ hx hxy k
    have h2 : x ^ k ≤ 1 := pow_le_one₀ hx (hxy.trans hy)
    have hy0 : 0 ≤ y := hx.trans hxy
    push_cast
    calc y ^ (k + 1) - x ^ (k + 1) = y * (y ^ k - x ^ k) + x ^ k * (y - x) := by ring
      _ ≤ 1 * (y ^ k - x ^ k) + 1 * (y - x) := by
          gcongr
      _ ≤ _ := by linarith

/-- With mean one, `φ(y) - φ(x) ≤ y - x` on `0 ≤ x ≤ y ≤ 1`. -/
theorem genFun_sub_le (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {x y : ℝ} (hx : 0 ≤ x)
    (hxy : x ≤ y) (hy : y ≤ 1) :
    ∑' k, (p k).toReal * y ^ k - ∑' k, (p k).toReal * x ^ k ≤ y - x := by
  have hφx := (summable_genFun p (s := x) ⟨hx, hxy.trans hy⟩).hasSum
  have hφy := (summable_genFun p (s := y) ⟨hx.trans hxy, hy⟩).hasSum
  have hC := (hasSum_mean_one p hm).mul_right (y - x)
  rw [one_mul] at hC
  refine hasSum_le (fun k => ?_) (hφy.sub hφx) hC
  rw [← mul_sub, mul_comm (k : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left (pow_sub_pow_le_mul hx hxy hy k) ENNReal.toReal_nonneg

/-- For `0 ≤ s < 1`, `x ↦ s φ(x) - x` is strictly decreasing on `[0,1]`. -/
theorem transform_strictAntiOn (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    StrictAntiOn (fun x => s * ∑' k, (p k).toReal * x ^ k - x) (Icc 0 1) := by
  intro x hx y hy hxy
  have h := genFun_sub_le p hm hx.1 hxy.le hy.2
  have : s * (∑' k, (p k).toReal * y ^ k - ∑' k, (p k).toReal * x ^ k) ≤ s * (y - x) :=
    mul_le_mul_of_nonneg_left h hs.1
  simp only
  nlinarith [hs.2]

/-- **Transform equation.** For `0 ≤ s < 1`, `s φ(x) = x` has exactly one solution in
`[0,1)`. -/
theorem existsUnique_transform_root (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    ∃! x, x ∈ Ico (0 : ℝ) 1 ∧ s * ∑' k, (p k).toReal * x ^ k = x := by
  have hcont : ContinuousOn (fun x => s * ∑' k, (p k).toReal * x ^ k - x) (Icc 0 1) :=
    (continuousOn_const.mul (continuousOn_genFun p)).sub continuousOn_id
  have h0 : 0 ≤ s * ∑' k, (p k).toReal * (0 : ℝ) ^ k - 0 := by
    rw [sub_zero]
    exact mul_nonneg hs.1 (genFun_nonneg p le_rfl)
  have h1 : s * ∑' k, (p k).toReal * (1 : ℝ) ^ k - 1 < 0 := by
    rw [genFun_one]
    linarith [hs.2]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' zero_le_one hcont ⟨h1.le, h0⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp only at hfx
    linarith
  refine ⟨x, ⟨⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩, by simp only at hfx; linarith⟩, ?_⟩
  rintro y ⟨hy, hfy⟩
  by_contra hne
  have hanti := transform_strictAntiOn p hm hs
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti ⟨hy.1, hy.2.le⟩ hx h
    simp only at this hfx
    linarith
  · have := hanti hx ⟨hy.1, hy.2.le⟩ h
    simp only at this hfx
    linarith

/-- The solution in `[0,1)` is the least solution in `[0,1]`. -/
theorem isLeast_transform_root (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {s x : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (hx : x ∈ Ico (0 : ℝ) 1)
    (hfx : s * ∑' k, (p k).toReal * x ^ k = x) :
    IsLeast {y | y ∈ Icc (0 : ℝ) 1 ∧ s * ∑' k, (p k).toReal * y ^ k = y} x := by
  refine ⟨⟨⟨hx.1, hx.2.le⟩, hfx⟩, fun y ⟨hy, hfy⟩ => ?_⟩
  by_contra hlt
  push Not at hlt
  have := transform_strictAntiOn p hm hs hy ⟨hx.1, hx.2.le⟩ hlt
  simp only at this
  linarith

/-- **Monotonicity.** A solution `F` of the transform equation on `[0,1)` is nondecreasing. -/
theorem monotoneOn_transform_root (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {F : ℝ → ℝ}
    (hF : ∀ s ∈ Ico (0 : ℝ) 1, F s ∈ Ico (0 : ℝ) 1 ∧
      s * ∑' k, (p k).toReal * F s ^ k = F s) :
    MonotoneOn F (Ico 0 1) := by
  intro s hs t ht hst
  by_contra hlt
  push Not at hlt
  obtain ⟨hFs, hs'⟩ := hF s hs
  obtain ⟨hFt, ht'⟩ := hF t ht
  have := transform_strictAntiOn p hm ht ⟨hFt.1, hFt.2.le⟩ ⟨hFs.1, hFs.2.le⟩ hlt
  simp only at this
  have hφ : 0 ≤ ∑' k, (p k).toReal * F s ^ k := genFun_nonneg p hFs.1
  nlinarith [mul_le_mul_of_nonneg_right hst hφ]

/-- `σ² > 0` rules out the degenerate law `p(1) = 1`. -/
theorem apply_one_ne_one_of_hasSum {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) σ2) (hσ0 : 0 < σ2) :
    p 1 ≠ 1 := by
  intro h1
  have : σ2 = 0 := by
    refine hσ.unique ?_
    convert hasSum_zero with k
    rcases eq_or_ne k 1 with rfl | hk
    · simp
    · simp [pmf_apply_eq_zero_of_apply_one p h1 hk]
  linarith

/-- **`F(s) → 1` as `s ↑ 1`.** -/
theorem tendsto_transform_root (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) (h1 : p 1 ≠ 1)
    {F : ℝ → ℝ} (hF : ∀ s ∈ Ico (0 : ℝ) 1, F s ∈ Ico (0 : ℝ) 1 ∧
      s * ∑' k, (p k).toReal * F s ^ k = F s) :
    Tendsto F (𝓝[<] 1) (𝓝 1) := by
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ico (0 : ℝ) 1 :=
    mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Ioo_subset_Ico_self
  have h0 := pmf_zero_pos_of_mean_le_one p hm.le h1
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set x := max a 0
    have hx : x ∈ Ico (0 : ℝ) 1 := ⟨le_max_right a 0, max_lt ha zero_lt_one⟩
    have hgt := genFun_gt_self p hm.le h0 hx
    set φx := ∑' k, (p k).toReal * x ^ k
    have hφx : 0 < φx := lt_of_le_of_lt hx.1 hgt
    have hq : x / φx < 1 := (div_lt_one hφx).2 hgt
    filter_upwards [hev, Ioo_mem_nhdsLT hq] with s hs hs'
    obtain ⟨hFs, hfs⟩ := hF s hs
    have hpos : 0 < s * φx - x := by
      have := (div_lt_iff₀ hφx).1 hs'.1
      linarith
    by_contra hle
    push Not at hle
    have hle' : F s ≤ x := hle.trans (le_max_left a 0)
    rcases eq_or_lt_of_le hle' with heq | hlt
    · rw [heq] at hfs
      linarith
    · have := transform_strictAntiOn p hm hs ⟨hFs.1, hFs.2.le⟩ ⟨hx.1, hx.2.le⟩ hlt
      simp only at this
      linarith
  · filter_upwards [hev] with s hs
    exact (hF s hs).1.2.trans hb

/-! ### 3. OVG9: `1 - F(s) ~ √(2(1 - s)/σ²)` -/

/-- **Analytic.** If the offspring law has mean one and `σ² ∈ (0, ∞)`, and `F` solves
the transform equation on `[0,1)`, then `1 - F(s) ~ √(2(1 - s)/σ²)` as `s ↑ 1`. -/
theorem isEquivalent_one_sub_transform_root (hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1) {σ2 : ℝ}
    (hσ : HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) σ2) (hσ0 : 0 < σ2)
    {F : ℝ → ℝ} (hF : ∀ s ∈ Ico (0 : ℝ) 1, F s ∈ Ico (0 : ℝ) 1 ∧
      s * ∑' k, (p k).toReal * F s ^ k = F s) :
    (fun s => 1 - F s) ~[𝓝[<] 1] fun s => Real.sqrt (2 * (1 - s) / σ2) := by
  set a := σ2 / 2 with ha
  have ha0 : 0 < a := by positivity
  have hev : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  -- `v(s) = 1 - F(s) → 0⁺`
  have hFt := tendsto_transform_root p hm (apply_one_ne_one_of_hasSum p hσ hσ0) hF
  have hv : Tendsto (fun s => 1 - F s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hFt
    · filter_upwards [hev] with s hs
      have := (hF s ⟨hs.1.le, hs.2⟩).1.2
      simp only [Set.mem_Ioi]
      linarith
  -- `ε(v) → 0`
  have hε := (tendsto_one_sub_genFun_expansion p hm hσ).comp hv
  set ε : ℝ → ℝ := fun s => ((1 - ∑' k, (p k).toReal * (1 - (1 - F s)) ^ k) - (1 - F s) +
    σ2 / 2 * (1 - F s) ^ 2) / (1 - F s) ^ 2 with hεeq
  have hε' : Tendsto ε (𝓝[<] 1) (𝓝 0) := hε
  -- `v² / (1 - s) → 1/a`
  have hden : Tendsto (fun s => s * (a - ε s)) (𝓝[<] 1) (𝓝 a) := by
    have h1 : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
    simpa using h1.mul ((tendsto_const_nhds (x := a)).sub hε')
  have hnum : Tendsto (fun s => 1 - (1 - F s)) (𝓝[<] 1) (𝓝 1) := by
    simpa using hFt
  have hratio : Tendsto (fun s => (1 - F s) ^ 2 / (1 - s)) (𝓝[<] 1) (𝓝 (1 / a)) := by
    refine (hnum.div hden ha0.ne').congr' ?_
    filter_upwards [hev, hden.eventually (eventually_ne_nhds ha0.ne')] with s hs hd
    obtain ⟨hFs, hfs⟩ := hF s ⟨hs.1.le, hs.2⟩
    have hv0 : 1 - F s ≠ 0 := by linarith [hFs.2]
    have h1s : 1 - s ≠ 0 := by linarith [hs.2]
    -- the equation `F = s φ(F)` in the variable `v`
    have hφ : ∑' k, (p k).toReal * (1 - (1 - F s)) ^ k =
        1 - (1 - F s) + a * (1 - F s) ^ 2 - ε s * (1 - F s) ^ 2 := by
      simp only [hεeq, ha]
      field_simp
      ring
    have hfs' : s * (1 - (1 - F s) + a * (1 - F s) ^ 2 - ε s * (1 - F s) ^ 2) = F s := by
      rw [← hφ]
      simpa using hfs
    change (1 - (1 - F s)) / (s * (a - ε s)) = (1 - F s) ^ 2 / (1 - s)
    rw [div_eq_div_iff hd h1s]
    linear_combination (-1 : ℝ) * hfs'
  -- the square root
  refine isEquivalent_of_tendsto_one ?_
  have hlim : Tendsto (fun s => Real.sqrt (a * ((1 - F s) ^ 2 / (1 - s)))) (𝓝[<] 1) (𝓝 1) := by
    have := (hratio.const_mul a).sqrt
    rwa [mul_one_div_cancel ha0.ne', Real.sqrt_one] at this
  refine hlim.congr' ?_
  filter_upwards [hev] with s hs
  obtain ⟨hFs, _⟩ := hF s ⟨hs.1.le, hs.2⟩
  have hv : 0 ≤ 1 - F s := by linarith [hFs.2]
  have h1s : 0 < 1 - s := by linarith [hs.2]
  simp only [Pi.div_apply]
  have e1 : a * ((1 - F s) ^ 2 / (1 - s)) = (1 - F s) ^ 2 / (2 * (1 - s) / σ2) := by
    rw [ha]
    field_simp
  rw [e1, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hv]

/-! ### Non-vacuity: the critical binary law -/

/-- The critical binary law `p(0) = p(2) = 1/2` has mean one and `σ² = 1`. Its transform root
is `F(s) = (1 - √(1 - s²))/s` (with `F(0) = 0`), and `isEquivalent_one_sub_transform_root` gives
`1 - F(s) ~ √(2(1 - s))`. -/
example : ∃ p : PMF ℕ, ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1 ∧
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) 1 ∧
    (∀ s ∈ Ico (0 : ℝ) 1, (1 - Real.sqrt (1 - s ^ 2)) / s ∈ Ico (0 : ℝ) 1 ∧
      s * ∑' k, (p k).toReal * ((1 - Real.sqrt (1 - s ^ 2)) / s) ^ k =
        (1 - Real.sqrt (1 - s ^ 2)) / s) ∧
    (fun s => 1 - (1 - Real.sqrt (1 - s ^ 2)) / s) ~[𝓝[<] 1]
      fun s => Real.sqrt (2 * (1 - s) / 1) := by
  let r : ℕ → ℝ := fun k => if k = 0 then 1 / 2 else if k = 2 then 1 / 2 else 0
  have hr : ∀ k, 0 ≤ r k := fun k => by
    simp only [r]
    split_ifs <;> norm_num
  have hr0 : ∀ k ∉ range 3, r k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [r]
    split_ifs <;> first | rfl | omega
  have hf : ∑ k ∈ range 3, ENNReal.ofReal (r k) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hr k]
    simp [Finset.sum_range_succ, r]
    norm_num
  let p : PMF ℕ := PMF.ofFinset (fun k => ENNReal.ofReal (r k)) (range 3) hf
    (fun k hk => by simp [hr0 k hk])
  have hp : ∀ k, (p k).toReal = r k := fun k => ENNReal.toReal_ofReal (hr k)
  have hφ : ∀ x : ℝ, ∑' k, (p k).toReal * x ^ k = 1 / 2 + 1 / 2 * x ^ 2 := by
    intro x
    simp_rw [hp]
    rw [tsum_eq_sum (s := range 3) fun k hk => by simp [hr0 k hk]]
    simp [Finset.sum_range_succ, r]
  have hm : ∑' k : ℕ, (k : ℝ≥0∞) * p k = 1 := by
    have hm : ∀ k : ℕ, (k : ℝ≥0∞) * p k = ENNReal.ofReal (k * r k) := fun k => by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
      rfl
    simp_rw [hm]
    rw [tsum_eq_sum (s := range 3) fun k hk => by simp [hr0 k hk],
      ← ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (hr k),
      ENNReal.ofReal_eq_one]
    simp [Finset.sum_range_succ, r]
  have hσ : HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) 1 := by
    have : HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal)
        (∑ k ∈ range 3, (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp [hp, hr0 k hk]
    have e : ∑ k ∈ range 3, (k : ℝ) * ((k : ℝ) - 1) * (p k).toReal = 1 := by
      simp [Finset.sum_range_succ, hp, r]
      norm_num
    rwa [e] at this
  have hF : ∀ s ∈ Ico (0 : ℝ) 1, (1 - Real.sqrt (1 - s ^ 2)) / s ∈ Ico (0 : ℝ) 1 ∧
      s * ∑' k, (p k).toReal * ((1 - Real.sqrt (1 - s ^ 2)) / s) ^ k =
        (1 - Real.sqrt (1 - s ^ 2)) / s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0
      simp
    have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith [hs.2]
    have hsq := Real.sq_sqrt h1
    have hsqrt1 : Real.sqrt (1 - s ^ 2) ≤ 1 := by
      rw [Real.sqrt_le_one]
      nlinarith
    have hlt : 1 - s < Real.sqrt (1 - s ^ 2) := by
      rw [Real.lt_sqrt (by linarith [hs.2])]
      nlinarith [hs.2]
    refine ⟨⟨div_nonneg (by linarith) hpos.le, (div_lt_one hpos).2 (by linarith)⟩, ?_⟩
    rw [hφ]
    field_simp
    nlinarith [hsq]
  refine ⟨p, hm, hσ, hF, ?_⟩
  exact isEquivalent_one_sub_transform_root p hm hσ one_pos
    (F := fun s => (1 - Real.sqrt (1 - s ^ 2)) / s) hF

end PercLib.Probability
