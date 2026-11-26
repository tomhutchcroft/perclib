/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Level selections for a regularly varying function of positive index (the scale-selection step
of Proposition I.3.2 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, §I.3.2, pp. 30-32) and the comparison of level selections from
Potter's bounds (Bingham–Goldie–Teugels, *Regular Variation*, Theorems 1.5.6 and 1.5.12).

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/RVInverseMonotone.lean` and
`PercLib/CriticalLRP/Analysis/RVInversePotter.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f ρ` becomes `RegularlyVarying ρ f` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the source's choice-built inverse `levelInverse`
is replaced by `genInv` of the same file, and every statement about it is restated and
re-proved for `genInv`; monotonicity on `[X, ∞)` is written as `MonotoneOn f (Ici X)`;
hypotheses that the proofs no longer use are removed; `exists_level_point`,
`eventually_level_ge` and the demonstration examples are not ported; declarations are renamed;
`import Mathlib`, `autoImplicit` and disabled linters are removed.
-/
module

public import PercLib.Analysis.RegularVariation.GeneralInverse

/-! # Level selections of a regularly varying function

A *level selection* for `f` along a running factor `g → 0⁺` is a function `u` with
`g · f (u) → c ∈ (0, ∞)`. For `f` regularly varying of index `ρ > 0` the ratio of two level
selections is determined by the levels: `u / v → (c₁ / c₂) ^ (1 / ρ)`. This is the form in
which the regular variation of the inverse (BGT Theorem 1.5.12) enters the cutoff choice
`r = f⁻¹ (λ / (A₂ h))` of Proposition I.3.2. Two versions are proved: one for `f` monotone
above a threshold, with no hypothesis on `u` and `v` beyond the levels, and one from Potter's
bounds alone, for level selections that tend to infinity.

For `f` continuous on `[x₀, ∞)` the generalized inverse `genInv f x₀` of `Defs.lean` is an
exact level selection (`apply_genInv_of_continuousOn`), so the cutoff fills its level exactly.

## Main results

* `RegularlyVarying.const_mul`: a positive multiple of a regularly varying function.
* `RegularlyVarying.potterBounds`, `RegularlyVarying.tendsto_atTop'`: Potter's bounds and
  divergence from regular variation alone (measurability on a tail suffices).
* `RegularlyVarying.tendsto_div_of_monotoneOn`: scale selection for monotone `f`.
* `tendsto_div_of_potter`, `RegularlyVarying.tendsto_div_of_tendsto_atTop`: scale selection
  from Potter's bounds.
* `apply_genInv_of_continuousOn`, `tendsto_genInv_atTop_of_continuousOn`,
  `RegularlyVarying.regularlyVarying_genInv_of_continuousOn`: the generalized inverse of a
  continuous function.
* `RegularlyVarying.tendsto_rpow_div_rpow_of_level_eq`,
  `RegularlyVarying.tendsto_genInv_rpow_div_rpow_of_continuousOn` and their normalized forms:
  the scaling law `(r h) ^ α / (τ h) ^ α → λ ^ (1 / a) / A₂ ^ (1 / a)` of (I.3.7).
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

variable {f : ℝ → ℝ} {ρ : ℝ}

/-! ## Regular variation without global measurability -/

/-- A positive multiple of a regularly varying function is regularly varying with the same
index. -/
theorem RegularlyVarying.const_mul {c : ℝ} (hc : 0 < c) (hf : RegularlyVarying ρ f) :
    RegularlyVarying ρ (fun x => c * f x) := by
  obtain ⟨a, ha⟩ := hf.measurable_tail
  refine ⟨⟨a, ha.const_mul c⟩, hf.eventually_pos.mono fun x hx => mul_pos hc hx,
    fun l hl => (hf.tendsto hl).congr' ?_⟩
  filter_upwards with x
  rw [mul_div_mul_left _ _ hc.ne']

/-- A regularly varying function agrees on a tail with a globally measurable regularly varying
function. -/
theorem RegularlyVarying.exists_measurable_eqOn (hf : RegularlyVarying ρ f) :
    ∃ a : ℝ, ∃ F : ℝ → ℝ, Measurable F ∧ (∀ x, a ≤ x → F x = f x) ∧ RegularlyVarying ρ F := by
  obtain ⟨a, ha⟩ := hf.measurable_tail
  obtain ⟨F, hF, hFf⟩ := exists_measurable_eqOn_Ici ha
  exact ⟨a, F, hF, hFf, hf.congr' (eventually_atTop.2 ⟨a, fun x hx => (hFf x hx).symm⟩)⟩

/-- **Potter's bounds** (BGT Theorem 1.5.6) for a regularly varying function: measurability on
a tail, which `RegularlyVarying` includes, suffices. -/
theorem RegularlyVarying.potterBounds (hf : RegularlyVarying ρ f) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y| := by
  obtain ⟨a, F, hF, hFf, hFrv⟩ := hf.exists_measurable_eqOn
  intro ε hε
  obtain ⟨X, hX1, hX⟩ := potterBounds_of_regularlyVarying hF hFrv ε hε
  refine ⟨max X a, le_trans hX1 (le_max_left _ _), fun x y hy hyx => ?_⟩
  have hya : a ≤ y := le_trans (le_max_right _ _) hy
  rw [← hFf x (le_trans hya hyx), ← hFf y hya]
  exact hX x y (le_trans (le_max_left _ _) hy) hyx

/-- **A regularly varying function of positive index tends to `∞`.** This is
`RegularlyVarying.tendsto_atTop` without its global measurability hypothesis; no monotonicity
is used. -/
theorem RegularlyVarying.tendsto_atTop' (hρ : 0 < ρ) (hf : RegularlyVarying ρ f) :
    Tendsto f atTop atTop := by
  obtain ⟨a, F, hF, hFf, hFrv⟩ := hf.exists_measurable_eqOn
  exact (hFrv.tendsto_atTop hρ hF).congr' (eventually_atTop.2 ⟨a, hFf⟩)

/-! ## A reciprocal multiplicative limit forces divergence -/

/-- If `g → 0` with `g > 0` and `g x * a x → c > 0`, then `a x → ∞`. -/
theorem tendsto_atTop_of_mul_tendsto_zero {ι : Type*} {l : Filter ι} {a g : ι → ℝ} {c : ℝ}
    (hc : 0 < c) (hg0 : Tendsto g l (𝓝 0)) (hg : ∀ᶠ x in l, 0 < g x)
    (ha : Tendsto (fun x => g x * a x) l (𝓝 c)) : Tendsto a l atTop := by
  have hinv : Tendsto (fun x => (g x)⁻¹) l atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hg0, hg⟩)
  refine hinv.num hc (ha.congr' ?_)
  filter_upwards with x
  rw [div_inv_eq_mul, mul_comm]

/-! ## Scale selection for a monotone regularly varying function -/

/-- **Scale selection for a monotone regularly varying function.** Let `f` be nondecreasing and
positive on `[X, ∞)` and regularly varying of index `ρ > 0`. If `g → 0⁺` and `u`, `v` (eventually
`≥ X`) select the levels `g · f (u) → c₁`, `g · f (v) → c₂` with `c₁, c₂ > 0`, then
`u / v → (c₁ / c₂) ^ (1 / ρ)`. -/
theorem RegularlyVarying.tendsto_div_of_monotoneOn {c₁ c₂ X : ℝ}
    (hρ : 0 < ρ) (hX : 0 < X) (hrv : RegularlyVarying ρ f) (hmono : MonotoneOn f (Ici X))
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {ι : Type*} {l : Filter ι} {g u v : ι → ℝ}
    (hg0 : Tendsto g l (𝓝 0)) (hg : ∀ᶠ h in l, 0 < g h)
    (hu : ∀ᶠ h in l, X ≤ u h) (hv : ∀ᶠ h in l, X ≤ v h)
    (hfu : Tendsto (fun h => g h * f (u h)) l (𝓝 c₁))
    (hfv : Tendsto (fun h => g h * f (v h)) l (𝓝 c₂))
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) :
    Tendsto (fun h => u h / v h) l (𝓝 ((c₁ / c₂) ^ (1 / ρ))) := by
  have hm : ∀ x y : ℝ, X ≤ x → x ≤ y → f x ≤ f y := fun x y hx hxy =>
    hmono (mem_Ici.2 hx) (mem_Ici.2 (le_trans hx hxy)) hxy
  have hc : 0 < c₁ / c₂ := div_pos hc1 hc2
  have habspos : 0 < (c₁ / c₂) ^ (1 / ρ) := Real.rpow_pos_of_pos hc _
  have hbase : ((c₁ / c₂) ^ (1 / ρ)) ^ ρ = c₁ / c₂ := by
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hρ.ne', Real.rpow_one]
  -- `f ∘ v → ∞`
  have hfvtop : Tendsto (fun h => f (v h)) l atTop :=
      tendsto_atTop_of_mul_tendsto_zero hc2 hg0 hg hfv
  -- hence `v → ∞`
  have hvtop : Tendsto v l atTop := by
    rw [Filter.tendsto_atTop]
    intro Y
    rcases le_or_gt Y X with hY | hY
    · filter_upwards [hv] with h hh using le_trans hY hh
    · filter_upwards [hfvtop.eventually (eventually_gt_atTop (f Y)), hv] with h hh hvh
      by_contra hcon
      exact absurd hh (not_lt.2 (hm _ _ hvh (le_of_lt (not_le.1 hcon))))
  -- the two `f`-values are comparable, with ratio `c₁/c₂`
  have hratio : Tendsto (fun h => f (u h) / f (v h)) l (𝓝 (c₁ / c₂)) := by
    refine (hfu.div hfv hc2.ne').congr' ?_
    filter_upwards [hg] with h hh
    exact mul_div_mul_left _ _ hh.ne'
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bounds
    intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [hu, hv] with h huu hvv
      have hpos' : 0 < u h / v h := div_pos (lt_of_lt_of_le hX huu) (lt_of_lt_of_le hX hvv)
      linarith
    · obtain ⟨t, hbt, hta⟩ : ∃ t : ℝ, b < t ∧ t < (c₁ / c₂) ^ (1 / ρ) :=
        ⟨(b + (c₁ / c₂) ^ (1 / ρ)) / 2, by linarith, by linarith⟩
      have htpos : 0 < t := lt_trans hb0 hbt
      have htpow : t ^ ρ < c₁ / c₂ := by
        rw [← hbase]
        exact Real.rpow_lt_rpow htpos.le hta hρ
      obtain ⟨e, hte, hec⟩ : ∃ e : ℝ, t ^ ρ < e ∧ e < c₁ / c₂ :=
        ⟨(t ^ ρ + c₁ / c₂) / 2, by linarith, by linarith⟩
      have hev1 : ∀ᶠ h in l, e < f (u h) / f (v h) :=
        hratio.eventually (eventually_gt_nhds hec)
      have hev2 : ∀ᶠ h in l, f (t * v h) / f (v h) < e :=
        ((hrv.tendsto htpos).comp hvtop).eventually (eventually_lt_nhds hte)
      filter_upwards [hev1, hev2, hu, hv] with h h1 h2 huu hvv
      have hfvpos : 0 < f (v h) := hpos _ hvv
      have hvpos : 0 < v h := lt_of_lt_of_le hX hvv
      have key : f (t * v h) < f (u h) :=
        (div_lt_div_iff_of_pos_right hfvpos).1 (lt_trans h2 h1)
      have htle : t * v h ≤ u h := by
        by_contra hcon
        exact absurd key (not_lt.2 (hm _ _ huu (le_of_lt (not_le.1 hcon))))
      rw [lt_div_iff₀ hvpos]
      nlinarith [mul_lt_mul_of_pos_right hbt hvpos, htle]
  · -- upper bounds
    intro b hb
    have hbpos : 0 < b := by linarith [habspos]
    have hbpow : c₁ / c₂ < b ^ ρ := by
      rw [← hbase]
      exact Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hb hρ
    obtain ⟨e, hce, heb⟩ : ∃ e : ℝ, c₁ / c₂ < e ∧ e < b ^ ρ :=
      ⟨(c₁ / c₂ + b ^ ρ) / 2, by linarith, by linarith⟩
    have hev1 : ∀ᶠ h in l, f (u h) / f (v h) < e :=
      hratio.eventually (eventually_lt_nhds hce)
    have hev2 : ∀ᶠ h in l, e < f (b * v h) / f (v h) :=
      ((hrv.tendsto hbpos).comp hvtop).eventually (eventually_gt_nhds heb)
    filter_upwards [hev1, hev2, hu, hv, hvtop.eventually (eventually_ge_atTop (X / b))]
      with h h1 h2 huu hvv htv
    have hfvpos : 0 < f (v h) := hpos _ hvv
    have hvpos : 0 < v h := lt_of_lt_of_le hX hvv
    have key : f (u h) < f (b * v h) :=
      (div_lt_div_iff_of_pos_right hfvpos).1 (lt_trans h1 h2)
    have hbX : X ≤ b * v h := by
      have hbx : b * (X / b) = X := by field_simp
      rw [← hbx]
      exact mul_le_mul_of_nonneg_left htv hbpos.le
    have hlt : u h < b * v h := by
      by_contra hcon
      exact absurd key (not_lt.2 (hm _ _ hbX (not_lt.1 hcon)))
    rw [div_lt_iff₀ hvpos]
    linarith

/-! ## Potter's bounds in symmetric form and scale selection without monotonicity -/

/-- **Potter's bounds for an arbitrary ordered pair**, in symmetric form: from the ordered
bounds above `X > 0` with `0 < ε ≤ 1/2`, for all `x, y ≥ X`,
`(1-ε) · min ((x/y)^{ρ-ε}) ((x/y)^{ρ+ε}) · |f y| ≤ |f x|` and
`|f x| ≤ (1+2ε) · max ((x/y)^{ρ-ε}) ((x/y)^{ρ+ε}) · |f y|`. -/
theorem potter_symmetric {ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hX0 : 0 < X)
    (hX : ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y|)
    {x y : ℝ} (hx : X ≤ x) (hy : X ≤ y) :
    (1 - ε) * min ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) * |f y| ≤ |f x| ∧
      |f x| ≤ (1 + 2 * ε) * max ((x / y) ^ (ρ - ε)) ((x / y) ^ (ρ + ε)) * |f y| := by
  have hxpos : 0 < x := lt_of_lt_of_le hX0 hx
  have hypos : 0 < y := lt_of_lt_of_le hX0 hy
  have hxy : 0 < x / y := div_pos hxpos hypos
  have hyx : y / x = (x / y)⁻¹ := by rw [inv_div]
  rcases le_or_gt y x with hle | hlt
  · -- case `y ≤ x`: the ordered Potter bound applies directly
    obtain ⟨hlo, hhi⟩ := hX x y hy hle
    have ht1 : (1 : ℝ) ≤ x / y := (one_le_div hypos).2 hle
    have hle1 : (x / y) ^ (ρ - ε) ≤ (x / y) ^ (ρ + ε) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    rw [min_eq_left hle1, max_eq_right hle1]
    refine ⟨hlo, le_trans hhi ?_⟩
    have h0 : (0 : ℝ) ≤ (x / y) ^ (ρ + ε) * |f y| := by positivity
    nlinarith [h0]
  · -- case `x < y`: apply the ordered bound to `(y, x)` and invert
    obtain ⟨hlo, hhi⟩ := hX y x hx hlt.le
    have hxy1 : x / y < 1 := by
      rw [div_lt_one hypos]; exact hlt
    have hle1 : (x / y) ^ (ρ + ε) ≤ (x / y) ^ (ρ - ε) :=
      Real.rpow_le_rpow_of_exponent_ge hxy hxy1.le (by linarith)
    rw [min_eq_right hle1, max_eq_left hle1]
    have hpx : ∀ q : ℝ, (0 : ℝ) < (x / y) ^ q := fun q => Real.rpow_pos_of_pos hxy q
    constructor
    · -- lower bound, from `|f y| ≤ (1+ε) (y/x)^{ρ+ε} |f x|`
      have hmul := mul_le_mul_of_nonneg_left hhi (le_of_lt (hpx (ρ + ε)))
      rw [hyx, Real.inv_rpow hxy.le] at hmul
      have heq : (x / y) ^ (ρ + ε) * ((1 + ε) * ((x / y) ^ (ρ + ε))⁻¹ * |f x|)
          = (1 + ε) * |f x| := by
        have := (hpx (ρ + ε)).ne'
        field_simp
      rw [heq] at hmul
      have h2 := mul_le_mul_of_nonneg_left hmul (by linarith : (0 : ℝ) ≤ 1 - ε)
      have h3 : (0 : ℝ) ≤ ε ^ 2 * |f x| := by positivity
      nlinarith [h2, h3]
    · -- upper bound, from `(1-ε) (y/x)^{ρ-ε} |f x| ≤ |f y|`
      have hmul := mul_le_mul_of_nonneg_left hlo (le_of_lt (hpx (ρ - ε)))
      rw [hyx, Real.inv_rpow hxy.le] at hmul
      have heq : (x / y) ^ (ρ - ε) * ((1 - ε) * ((x / y) ^ (ρ - ε))⁻¹ * |f x|)
          = (1 - ε) * |f x| := by
        have := (hpx (ρ - ε)).ne'
        field_simp
      rw [heq] at hmul
      have h2 := mul_le_mul_of_nonneg_left hmul (by linarith : (0 : ℝ) ≤ 1 + 2 * ε)
      have h3 : (0 : ℝ) ≤ ε * (1 - 2 * ε) * |f x| :=
        mul_nonneg (mul_nonneg hε.le (by linarith)) (abs_nonneg _)
      nlinarith [h2, h3]

/-- For `0 < b` and `b ^ ρ < c` there is `ε ∈ (0, 1/2]`, `ε < ρ`, with
`(1+2ε) · max (b^{ρ-ε}) (b^{ρ+ε}) < c`. -/
private theorem exists_small_eps_max {b c : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hbc : b ^ ρ < c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε < ρ ∧
      (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) < c := by
  have hcont : ContinuousAt (fun e : ℝ => (1 + 2 * e) * max (b ^ (ρ - e)) (b ^ (ρ + e))) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => b ^ (ρ - e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ - 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ - e) 0)
    have h2 : ContinuousAt (fun e : ℝ => b ^ (ρ + e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ + 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ + e) 0)
    have hlin : ContinuousAt (fun e : ℝ => 1 + 2 * e) 0 := by fun_prop
    exact hlin.mul (h1.max h2)
  have hev : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), (1 + 2 * e) * max (b ^ (ρ - e)) (b ^ (ρ + e)) < c := by
    have hlt : (1 + 2 * (0:ℝ)) * max (b ^ (ρ - 0)) (b ^ (ρ + 0)) < c := by simpa using hbc
    exact (hcont.eventually (Iio_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), e < min (1 / 2) ρ :=
    (eventually_lt_nhds (lt_min (by norm_num) hρ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hε1, hε2⟩, hε0⟩ :=
    ((hev.and hev2).and (self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioi 0)).exists
  exact ⟨ε, hε0, le_of_lt (lt_of_lt_of_le hε2 (min_le_left _ _)),
    lt_of_lt_of_le hε2 (min_le_right _ _), hε1⟩

/-- For `0 < b` and `c < b ^ ρ` there is `ε ∈ (0, 1/2]`, `ε < ρ`, with
`c < (1-ε) · min (b^{ρ-ε}) (b^{ρ+ε})`. -/
private theorem exists_small_eps_min {b c : ℝ} (hb : 0 < b) (hρ : 0 < ρ) (hbc : c < b ^ ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ ε < ρ ∧
      c < (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) := by
  have hcont : ContinuousAt (fun e : ℝ => (1 - e) * min (b ^ (ρ - e)) (b ^ (ρ + e))) 0 := by
    have h1 : ContinuousAt (fun e : ℝ => b ^ (ρ - e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ - 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ - e) 0)
    have h2 : ContinuousAt (fun e : ℝ => b ^ (ρ + e)) 0 :=
      (Real.continuousAt_const_rpow (a := b) (b := ρ + 0) (ne_of_gt hb)).comp
        (by fun_prop : ContinuousAt (fun e : ℝ => ρ + e) 0)
    have hlin : ContinuousAt (fun e : ℝ => 1 - e) 0 := by fun_prop
    exact hlin.mul (h1.min h2)
  have hev : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), c < (1 - e) * min (b ^ (ρ - e)) (b ^ (ρ + e)) := by
    have hlt : c < (1 - (0:ℝ)) * min (b ^ (ρ - 0)) (b ^ (ρ + 0)) := by simpa using hbc
    exact (hcont.eventually (Ioi_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds
  have hev2 : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), e < min (1 / 2) ρ :=
    (eventually_lt_nhds (lt_min (by norm_num) hρ)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ε, ⟨hε1, hε2⟩, hε0⟩ :=
    ((hev.and hev2).and (self_mem_nhdsWithin : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ), e ∈ Ioi 0)).exists
  exact ⟨ε, hε0, le_of_lt (lt_of_lt_of_le hε2 (min_le_left _ _)),
    lt_of_lt_of_le hε2 (min_le_right _ _), hε1⟩

/-- **Scale selection from Potter's bounds.** No monotonicity of `f` is assumed: if `f`
satisfies Potter's bounds with index `ρ > 0`, is positive on `[X, ∞)`, and the level selections
`u, v → ∞` satisfy `g · f (u) → c₁`, `g · f (v) → c₂` with `c₁, c₂ > 0`, then
`u / v → (c₁ / c₂) ^ (1 / ρ)`. -/
theorem tendsto_div_of_potter {c₁ c₂ X : ℝ} (hρ : 0 < ρ) (hX0 : 0 < X)
    (hpot : ∀ ε : ℝ, 0 < ε → ∃ X' : ℝ, 1 ≤ X' ∧ ∀ x y : ℝ, X' ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y|)
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {ι : Type*} {l : Filter ι} {g u v : ι → ℝ}
    (hg : ∀ᶠ h in l, 0 < g h)
    (huT : Tendsto u l atTop) (hvT : Tendsto v l atTop)
    (hfu : Tendsto (fun h => g h * f (u h)) l (𝓝 c₁))
    (hfv : Tendsto (fun h => g h * f (v h)) l (𝓝 c₂))
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) :
    Tendsto (fun h => u h / v h) l (𝓝 ((c₁ / c₂) ^ (1 / ρ))) := by
  have hu : ∀ᶠ h in l, X ≤ u h := huT.eventually (eventually_ge_atTop X)
  have hv : ∀ᶠ h in l, X ≤ v h := hvT.eventually (eventually_ge_atTop X)
  have hc : 0 < c₁ / c₂ := div_pos hc1 hc2
  have habspos : 0 < (c₁ / c₂) ^ (1 / ρ) := Real.rpow_pos_of_pos hc _
  have hbase : ((c₁ / c₂) ^ (1 / ρ)) ^ ρ = c₁ / c₂ := by
    rw [← Real.rpow_mul hc.le, one_div_mul_cancel hρ.ne', Real.rpow_one]
  have hratio : Tendsto (fun h => f (u h) / f (v h)) l (𝓝 (c₁ / c₂)) := by
    refine (hfu.div hfv hc2.ne').congr' ?_
    filter_upwards [hg] with h hh
    exact mul_div_mul_left _ _ hh.ne'
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower bounds: eventually `b < u h / v h`
    intro b hb
    rcases le_or_gt b 0 with hb0 | hb0
    · filter_upwards [hu, hv] with h h1 h2
      have hpos' : 0 < u h / v h := div_pos (lt_of_lt_of_le hX0 h1) (lt_of_lt_of_le hX0 h2)
      linarith
    · have hbρ : b ^ ρ < c₁ / c₂ := by
        rw [← hbase]
        exact Real.rpow_lt_rpow hb0.le hb hρ
      obtain ⟨ε, hε0, hε2, hερ, hεc⟩ := exists_small_eps_max hb0 hρ hbρ
      obtain ⟨Xε, hXε1, hXε⟩ := hpot ε hε0
      filter_upwards [huT.eventually (eventually_ge_atTop Xε),
        hvT.eventually (eventually_ge_atTop Xε),
        hratio.eventually (eventually_gt_nhds hεc), hu, hv] with h huε hvε hrat huu hvv
      by_contra hle
      have hle : u h / v h ≤ b := not_lt.1 hle
      have hcomp := potter_symmetric hε0 hε2 (by linarith) hXε huε hvε
      have hupos : 0 < f (u h) := hpos _ huu
      have hvpos : 0 < f (v h) := hpos _ hvv
      have hq : 0 ≤ u h / v h :=
        div_nonneg (by linarith [hX0, huu]) (by linarith [hX0, hvv])
      have hmaxle : max ((u h / v h) ^ (ρ - ε)) ((u h / v h) ^ (ρ + ε))
          ≤ max (b ^ (ρ - ε)) (b ^ (ρ + ε)) := by
        apply max_le_max
        · exact Real.rpow_le_rpow hq hle (le_of_lt (by linarith : (0:ℝ) < ρ - ε))
        · exact Real.rpow_le_rpow hq hle (le_of_lt (by linarith : (0:ℝ) < ρ + ε))
      have hsmall : f (u h) ≤ (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) * f (v h) := by
        have h1 := hcomp.2
        rw [abs_of_pos hupos, abs_of_pos hvpos] at h1
        have h0 : (0 : ℝ) ≤ 1 + 2 * ε := by linarith
        have hstep := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmaxle h0) hvpos.le
        linarith [hstep, h1]
      have hdiv : f (u h) / f (v h) ≤ (1 + 2 * ε) * max (b ^ (ρ - ε)) (b ^ (ρ + ε)) := by
        rw [div_le_iff₀ hvpos]
        linarith [hsmall]
      linarith [hdiv, hrat]
  · -- upper bounds: eventually `u h / v h < b`
    intro b hb
    have hb0 : 0 < b := lt_trans habspos hb
    have hbρ : c₁ / c₂ < b ^ ρ := by
      rw [← hbase]
      exact Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hb hρ
    obtain ⟨ε, hε0, hε2, hερ, hεc⟩ := exists_small_eps_min hb0 hρ hbρ
    obtain ⟨Xε, hXε1, hXε⟩ := hpot ε hε0
    filter_upwards [huT.eventually (eventually_ge_atTop Xε),
      hvT.eventually (eventually_ge_atTop Xε),
      hratio.eventually (eventually_lt_nhds hεc), hu, hv] with h huε hvε hrat huu hvv
    by_contra hge
    have hge : b ≤ u h / v h := not_lt.1 hge
    have hcomp := potter_symmetric hε0 hε2 (by linarith) hXε huε hvε
    have hupos : 0 < f (u h) := hpos _ huu
    have hvpos : 0 < f (v h) := hpos _ hvv
    have hminle : min (b ^ (ρ - ε)) (b ^ (ρ + ε))
        ≤ min ((u h / v h) ^ (ρ - ε)) ((u h / v h) ^ (ρ + ε)) := by
      apply min_le_min
      · exact Real.rpow_le_rpow hb0.le hge (le_of_lt (by linarith : (0:ℝ) < ρ - ε))
      · exact Real.rpow_le_rpow hb0.le hge (le_of_lt (by linarith : (0:ℝ) < ρ + ε))
    have hbig : (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) * f (v h) ≤ f (u h) := by
      have h1 := hcomp.1
      rw [abs_of_pos hupos, abs_of_pos hvpos] at h1
      have h0 : (0 : ℝ) ≤ 1 - ε := by linarith
      have hstep := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hminle h0) hvpos.le
      linarith [hstep, h1]
    have hdiv : (1 - ε) * min (b ^ (ρ - ε)) (b ^ (ρ + ε)) ≤ f (u h) / f (v h) := by
      rw [le_div_iff₀ hvpos]
      linarith [hbig]
    linarith [hdiv, hrat]

/-- **Level comparison from regular variation alone.** For `f` regularly varying of index
`ρ > 0` and level selections `u, v → ∞` with `g · f (u) → c₁`, `g · f (v) → c₂`
(`c₁, c₂ > 0`), `u / v → (c₁ / c₂) ^ (1 / ρ)`. Potter's bounds and positivity come from
`RegularlyVarying`. -/
theorem RegularlyVarying.tendsto_div_of_tendsto_atTop {c₁ c₂ : ℝ} (hρ : 0 < ρ)
    (hrv : RegularlyVarying ρ f) {ι : Type*} {l : Filter ι} {g u v : ι → ℝ}
    (hg : ∀ᶠ h in l, 0 < g h) (huT : Tendsto u l atTop) (hvT : Tendsto v l atTop)
    (hfu : Tendsto (fun h => g h * f (u h)) l (𝓝 c₁))
    (hfv : Tendsto (fun h => g h * f (v h)) l (𝓝 c₂))
    (hc1 : 0 < c₁) (hc2 : 0 < c₂) :
    Tendsto (fun h => u h / v h) l (𝓝 ((c₁ / c₂) ^ (1 / ρ))) := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 hrv.eventually_pos
  exact tendsto_div_of_potter hρ (lt_of_lt_of_le one_pos (le_max_right X 1)) hrv.potterBounds
    (fun x hx => hX x (le_trans (le_max_left _ _) hx)) hg huT hvT hfu hfv hc1 hc2

/-! ## The generalized inverse of a continuous function -/

/-- The generalized inverse depends only on the values of `f` above the threshold. -/
theorem genInv_congr {g : ℝ → ℝ} {x₀ : ℝ} (hfg : ∀ x, x₀ ≤ x → f x = g x) :
    genInv f x₀ = genInv g x₀ := by
  funext y
  simp only [genInv_def]
  congr 1
  ext x
  exact and_congr_right fun h => by rw [hfg x h]

/-- **The generalized inverse of a continuous function is an exact level selection**: if `f` is
continuous on `[x₀, ∞)`, `f x₀ ≤ y` and the level `y` is reached above `x₀`, then
`f (genInv f x₀ y) = y`. -/
theorem apply_genInv_of_continuousOn {x₀ y : ℝ} (hcont : ContinuousOn f (Ici x₀))
    (hne : ∃ x, x₀ ≤ x ∧ y ≤ f x) (hy : f x₀ ≤ y) : f (genInv f x₀ y) = y := by
  have hS : IsClosed {x | x₀ ≤ x ∧ y ≤ f x} :=
    hcont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Ici
  have hmem : x₀ ≤ genInv f x₀ y ∧ y ≤ f (genInv f x₀ y) :=
    hS.csInf_mem hne (bddBelow_levelSet f x₀ y)
  refine le_antisymm ?_ hmem.2
  rcases eq_or_lt_of_le hmem.1 with h | h
  · rw [← h]; exact hy
  · have hc : Tendsto f (𝓝[<] (genInv f x₀ y)) (𝓝 (f (genInv f x₀ y))) :=
      ((hcont _ hmem.1).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsLT h) (Ioo_subset_Ioi_self.trans
            Ioi_subset_Ici_self))).tendsto
    refine le_of_tendsto hc ?_
    filter_upwards [Ioo_mem_nhdsLT h] with x hx
    by_contra hlt
    exact absurd (genInv_le hx.1.le (le_of_lt (not_le.1 hlt))) (not_le.2 hx.2)

/-- A function continuous on `[x₀, ∞)` is bounded above on every `[x₀, M]`. -/
private theorem exists_bound_of_continuousOn {x₀ : ℝ} (hcont : ContinuousOn f (Ici x₀))
    (M : ℝ) : ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hcont.mono Icc_subset_Ici_self)
  exact ⟨C, fun x h1 h2 => hC ⟨x, ⟨h1, h2⟩, rfl⟩⟩

/-- A function tending to `∞` reaches every level above every threshold. -/
private theorem exists_le_of_tendsto_atTop (htop : Tendsto f atTop atTop) (x₀ y : ℝ) :
    ∃ x, x₀ ≤ x ∧ y ≤ f x := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 (htop.eventually (eventually_ge_atTop y))
  exact ⟨max X x₀, le_max_right _ _, hX _ (le_max_left _ _)⟩

/-- **The generalized inverse of a continuous function tending to `∞` diverges.** -/
theorem tendsto_genInv_atTop_of_continuousOn {x₀ : ℝ} (hcont : ContinuousOn f (Ici x₀))
    (htop : Tendsto f atTop atTop) : Tendsto (genInv f x₀) atTop atTop := by
  refine Filter.tendsto_atTop.2 fun M => ?_
  obtain ⟨C, hC⟩ := exists_bound_of_continuousOn hcont M
  filter_upwards [eventually_gt_atTop C] with y hy
  refine le_csInf (exists_le_of_tendsto_atTop htop x₀ y) fun x hx => ?_
  by_contra hcon
  exact absurd (hC x hx.1 (le_of_lt (not_le.1 hcon))) (not_le.2 (lt_of_lt_of_le hy hx.2))

/-- Reduction to a globally measurable function: a regularly varying `f`, continuous and
positive on `[x₀, ∞)`, agrees above `x₀` with a measurable regularly varying `F` that has the
same generalized inverse and is bounded on every `[x₀, M]`. -/
private theorem RegularlyVarying.exists_measurable_of_continuousOn {x₀ : ℝ}
    (hf : RegularlyVarying ρ f) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici x₀)) :
    ∃ F : ℝ → ℝ, Measurable F ∧ RegularlyVarying ρ F ∧ genInv F x₀ = genInv f x₀ ∧
      (∀ x, x₀ ≤ x → 0 < F x) ∧ ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → F x ≤ C := by
  classical
  have hFf : ∀ x, x₀ ≤ x → (Ici x₀).piecewise f 0 x = f x := fun x hx =>
    piecewise_eq_of_mem _ _ _ (mem_Ici.2 hx)
  refine ⟨(Ici x₀).piecewise f 0,
    hcont.measurable_piecewise continuousOn_const measurableSet_Ici,
    hf.congr' (eventually_atTop.2 ⟨x₀, fun x hx => (hFf x hx).symm⟩),
    genInv_congr hFf, fun x hx => (hFf x hx).symm ▸ hpos x hx, fun M => ?_⟩
  obtain ⟨C, hC⟩ := exists_bound_of_continuousOn hcont M
  exact ⟨C, fun x h1 h2 => (hFf x h1).symm ▸ hC x h1 h2⟩

/-- **The generalized inverse of a continuous regularly varying function is regularly varying
of index `1 / ρ`** (BGT Theorem 1.5.12, continuous case). -/
theorem RegularlyVarying.regularlyVarying_genInv_of_continuousOn {x₀ : ℝ} (hρ : 0 < ρ)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici x₀)) : RegularlyVarying (1 / ρ) (genInv f x₀) := by
  obtain ⟨F, hF, hFrv, hFg, hFpos, hFbdd⟩ := hf.exists_measurable_of_continuousOn hpos hcont
  rw [← hFg]
  exact hFrv.regularlyVarying_genInv hρ hF hx₀ hFpos hFbdd

/-! ## The cutoff choice `r = f⁻¹ (λ / (A₂ h))` of Proposition I.3.2 -/

/-- **The chosen cutoff fills the level exactly**: for `f` continuous on `[x₀, ∞)` and tending
to `∞`, `h · (A₂ · f (genInv f x₀ (λ / (A₂ h)))) = λ` whenever `f x₀ ≤ λ / (A₂ h)`. -/
theorem level_filled_eq_of_continuousOn {x₀ A₂ lam h : ℝ} (hcont : ContinuousOn f (Ici x₀))
    (htop : Tendsto f atTop atTop) (hA₂ : A₂ ≠ 0) (hh : h ≠ 0)
    (hy : f x₀ ≤ lam / (A₂ * h)) :
    h * (A₂ * f (genInv f x₀ (lam / (A₂ * h)))) = lam := by
  rw [apply_genInv_of_continuousOn hcont (exists_le_of_tendsto_atTop htop _ _) hy]
  field_simp

/-- **The scaling law for arbitrary exact level selections.** Let `f` be nondecreasing,
positive and regularly varying of index `ρ = a α > 0` on `[X, ∞)`, and let `σ₁ h, σ₂ h ≥ X` reach
the levels `f (σ₁ h) = λ / (A₂ h)` and `f (σ₂ h) = 1 / h` for small `h > 0`. Then
`(σ₁ h) ^ α / (σ₂ h) ^ α → λ ^ (1 / a) / A₂ ^ (1 / a)` as `h ↓ 0`. -/
theorem RegularlyVarying.tendsto_rpow_div_rpow_of_level_eq {a α A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVarying ρ f) (hmono : MonotoneOn f (Ici X))
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {σ₁ σ₂ : ℝ → ℝ}
    (hσ1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₁ h) = lam / (A₂ * h))
    (hσ2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₂ h) = 1 / h)
    (hX1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₁ h)
    (hX2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₂ h) :
    Tendsto (fun h : ℝ => (σ₁ h) ^ α / (σ₂ h) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (lam ^ (1 / a) / A₂ ^ (1 / a))) := by
  have hqe : 0 < lam / A₂ := div_pos hlam hA₂
  have hexp : ((lam / A₂) ^ (1 / ρ)) ^ α = lam ^ (1 / a) / A₂ ^ (1 / a) := by
    rw [← Real.rpow_mul hqe.le, show (1 / ρ) * α = 1 / a by rw [hρα]; field_simp,
      Real.div_rpow hlam.le hA₂.le]
  have hfv1 : Tendsto (fun h : ℝ => h * f (σ₁ h)) (𝓝[>] (0 : ℝ)) (𝓝 (lam / A₂)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hσ1] with h hh hlev
    rw [hlev]
    have : h ≠ 0 := ne_of_gt hh
    field_simp
  have hfv2 : Tendsto (fun h : ℝ => h * f (σ₂ h)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hσ2] with h hh hlev
    rw [hlev]
    have : h ≠ 0 := ne_of_gt hh
    field_simp
  have hbase := hrv.tendsto_div_of_monotoneOn (c₁ := lam / A₂) (c₂ := 1) hρ hX hmono hpos
    (g := fun h : ℝ => h) (tendsto_id.mono_left nhdsWithin_le_nhds)
    self_mem_nhdsWithin hX1 hX2 hfv1 hfv2 hqe one_pos
  rw [div_one] at hbase
  have hcontpow : Tendsto (fun t : ℝ => t ^ α) (𝓝 ((lam / A₂) ^ (1 / ρ)))
      (𝓝 (((lam / A₂) ^ (1 / ρ)) ^ α)) :=
    (Real.continuousAt_rpow_const _ α (Or.inr hα.le)).tendsto
  rw [hexp] at hcontpow
  refine (hcontpow.comp hbase).congr' ?_
  filter_upwards [hX1, hX2] with h h1 h2
  exact Real.div_rpow (le_trans hX.le h1) (le_trans hX.le h2) α

/-- **The scaling law at the paper's cutoff.** For `f` regularly varying of index `ρ = a α > 0`,
continuous and positive on `[X, ∞)` with `X > 0`, `r h = genInv f X (λ / (A₂ h))` and
`τ h = genInv f X (1 / h)` satisfy `(r h) ^ α / (τ h) ^ α → λ ^ (1 / a) / A₂ ^ (1 / a)` as
`h ↓ 0`. -/
theorem RegularlyVarying.tendsto_genInv_rpow_div_rpow_of_continuousOn {a α A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVarying ρ f) (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici X)) :
    Tendsto (fun h : ℝ => (genInv f X (lam / (A₂ * h))) ^ α / (genInv f X (1 / h)) ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (lam ^ (1 / a) / A₂ ^ (1 / a))) := by
  obtain ⟨F, hF, hFrv, hFg, hFpos, hFbdd⟩ := hrv.exists_measurable_of_continuousOn hpos hcont
  rw [← hFg, ← Real.div_rpow hlam.le hA₂.le]
  exact hFrv.tendsto_level_normalization hρ hF hX hFpos hFbdd ha hα hρα hA₂ hlam

/-- The normalization step shared by the two forms of (I.3.7). -/
private theorem tendsto_normalized_of_tendsto_rpow_div_rpow {α A₁ lam L : ℝ} (hlam : 0 < lam)
    {σ₁ σ₂ : ℝ → ℝ} (hσ2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < σ₂ h)
    (hlim : Tendsto (fun h : ℝ => (σ₁ h) ^ α / (σ₂ h) ^ α) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun h : ℝ => (A₁ * (σ₁ h) ^ α * h / lam) / ((σ₂ h) ^ α * h))
      (𝓝[>] (0 : ℝ)) (𝓝 (A₁ / lam * L)) := by
  refine (tendsto_const_nhds.mul hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hσ2] with h hh h2
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hpow : (σ₂ h) ^ α ≠ 0 := (Real.rpow_pos_of_pos h2 α).ne'
  have hl : lam ≠ 0 := hlam.ne'
  field_simp

/-- **(I.3.7) for exact level selections**: with `σ₁, σ₂` as in
`RegularlyVarying.tendsto_rpow_div_rpow_of_level_eq`,
`(A₁ (σ₁ h) ^ α h / λ) / ((σ₂ h) ^ α h) → (A₁ / λ) (λ ^ (1 / a) / A₂ ^ (1 / a))`. -/
theorem RegularlyVarying.tendsto_normalized_of_level_eq {a α A₁ A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVarying ρ f) (hmono : MonotoneOn f (Ici X))
    (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    {σ₁ σ₂ : ℝ → ℝ}
    (hσ1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₁ h) = lam / (A₂ * h))
    (hσ2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), f (σ₂ h) = 1 / h)
    (hX1 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₁ h)
    (hX2 : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), X ≤ σ₂ h) :
    Tendsto (fun h : ℝ => (A₁ * (σ₁ h) ^ α * h / lam) / ((σ₂ h) ^ α * h))
      (𝓝[>] (0 : ℝ)) (𝓝 (A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)))) :=
  tendsto_normalized_of_tendsto_rpow_div_rpow hlam
    (hX2.mono fun _ h2 => lt_of_lt_of_le hX h2)
    (hrv.tendsto_rpow_div_rpow_of_level_eq hρ hρα ha hα hX hA₂ hlam hmono hpos hσ1 hσ2 hX1 hX2)

/-- **(I.3.7) at the paper's cutoff** `r h = genInv f X (λ / (A₂ h))`,
`τ h = genInv f X (1 / h)`, for `f` continuous and positive on `[X, ∞)`. -/
theorem RegularlyVarying.tendsto_genInv_normalized_of_continuousOn {a α A₁ A₂ X lam : ℝ}
    (hρ : 0 < ρ) (hρα : ρ = a * α) (ha : 0 < a) (hα : 0 < α)
    (hX : 0 < X) (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (hrv : RegularlyVarying ρ f) (hpos : ∀ x : ℝ, X ≤ x → 0 < f x)
    (hcont : ContinuousOn f (Ici X)) :
    Tendsto (fun h : ℝ =>
        (A₁ * (genInv f X (lam / (A₂ * h))) ^ α * h / lam) / ((genInv f X (1 / h)) ^ α * h))
      (𝓝[>] (0 : ℝ)) (𝓝 (A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)))) := by
  refine tendsto_normalized_of_tendsto_rpow_div_rpow hlam (Eventually.of_forall fun h => ?_)
    (hrv.tendsto_genInv_rpow_div_rpow_of_continuousOn hρ hρα ha hα hX hA₂ hlam hpos hcont)
  obtain ⟨F, hF, hFrv, hFg, -, -⟩ := hrv.exists_measurable_of_continuousOn hpos hcont
  rw [← hFg]
  exact hFrv.genInv_pos hρ hF hX _

/-- The constant of (I.3.7) in the paper's displayed form:
`(A₁ / λ) (λ ^ (1 / a) / A₂ ^ (1 / a)) = A₁ / (A₂ ^ (1 / a) λ ^ (1 - 1 / a))`. -/
theorem div_mul_rpow_div_rpow_eq {A₁ A₂ lam a : ℝ} (hA₂ : 0 < A₂) (hlam : 0 < lam) :
    A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)) = A₁ / (A₂ ^ (1 / a) * lam ^ (1 - 1 / a)) := by
  rw [Real.rpow_sub hlam, Real.rpow_one]
  have hA2p : A₂ ^ (1 / a) ≠ 0 := (Real.rpow_pos_of_pos hA₂ _).ne'
  have hlp : lam ^ (1 / a) ≠ 0 := (Real.rpow_pos_of_pos hlam _).ne'
  have hl : lam ≠ 0 := hlam.ne'
  field_simp

/-- The constant of (I.3.7) as the factor in the definition of `A₃`:
`(A₁ / λ) (λ ^ (1 / a) / A₂ ^ (1 / a)) = (A₁ / A₂ ^ (1 / a)) λ ^ (-((a - 1) / a))`. -/
theorem div_mul_rpow_div_rpow_eq_mul_rpow_neg {A₁ A₂ lam a : ℝ} (hA₂ : 0 < A₂) (hlam : 0 < lam)
    (ha : a ≠ 0) :
    A₁ / lam * (lam ^ (1 / a) / A₂ ^ (1 / a)) = A₁ / A₂ ^ (1 / a) * lam ^ (-((a - 1) / a)) := by
  have hexp : -((a - 1) / a) = 1 / a - 1 := by field_simp; ring
  rw [hexp, Real.rpow_sub hlam, Real.rpow_one]
  have hA2p : A₂ ^ (1 / a) ≠ 0 := (Real.rpow_pos_of_pos hA₂ _).ne'
  have hl : lam ≠ 0 := hlam.ne'
  field_simp

/-! ## Witnesses -/

/-- `x ↦ x²` is continuous on `[1, ∞)`. -/
private theorem continuousOn_sq_Ici_one : ContinuousOn (fun x : ℝ => x ^ (2 : ℝ)) (Ici 1) :=
  ContinuousOn.rpow_const continuousOn_id (fun _ _ => Or.inr (by norm_num))

example : RegularlyVarying (1 / 2) (genInv (fun x : ℝ => x ^ (2 : ℝ)) 1) :=
  (regularlyVarying_rpow 2).regularlyVarying_genInv_of_continuousOn two_pos one_pos
    (fun x hx => Real.rpow_pos_of_pos (by linarith) 2) continuousOn_sq_Ici_one

/-- The scaling law at `f x = x²`, `ρ = a = 2`, `α = 1`, `A₂ = 1`, `λ = 4`, `X = 1`: the limit
`4 ^ (1/2) / 1 ^ (1/2) = 2` is not trivial. -/
example : Tendsto (fun h : ℝ =>
    (genInv (fun x : ℝ => x ^ (2 : ℝ)) 1 (4 / (1 * h))) ^ (1 : ℝ) /
      (genInv (fun x : ℝ => x ^ (2 : ℝ)) 1 (1 / h)) ^ (1 : ℝ))
    (𝓝[>] (0 : ℝ)) (𝓝 2) := by
  have h := (regularlyVarying_rpow 2).tendsto_genInv_rpow_div_rpow_of_continuousOn
    (a := 2) (α := 1) (A₂ := 1) (lam := 4) two_pos (by norm_num) two_pos one_pos one_pos one_pos
    (by norm_num) (fun x hx => Real.rpow_pos_of_pos (by linarith) 2)
    continuousOn_sq_Ici_one
  have h2 : (4 : ℝ) ^ ((1 : ℝ) / 2) / (1 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [Real.one_rpow, div_one, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
        ← Real.rpow_mul (by norm_num)]
    norm_num
  rwa [h2] at h

/-- Level comparison at the identity: the levels `2 y` and `y` have ratio `2`. -/
example : Tendsto (fun y : ℝ => (2 * y) / y) atTop (𝓝 ((2 / 1 : ℝ) ^ (1 / (1 : ℝ)))) := by
  refine (regularlyVarying_rpow 1).tendsto_div_of_tendsto_atTop (c₁ := 2) (c₂ := 1)
    (f := fun x : ℝ => x ^ (1 : ℝ)) one_pos (g := fun y : ℝ => y⁻¹)
    ((eventually_gt_atTop (0 : ℝ)).mono fun y hy => inv_pos.2 hy)
    (tendsto_id.const_mul_atTop two_pos) tendsto_id ?_ ?_
    two_pos one_pos
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simp only [Real.rpow_one]
    field_simp
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    simp only [Real.rpow_one]
    field_simp

end PercLib.Analysis
