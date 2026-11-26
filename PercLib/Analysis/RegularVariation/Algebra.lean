/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Algebra of regular variation, of Potter's bounds, and doubling, from T. Hutchcroft, *Critical
long-range percolation I*, arXiv:2508.18807v1, §I.2.2, pp. 25-28.

Ported from the work of contributor `yujinhkim`: repository `yujinhkim/lrp`, branch
`critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/RVAlgebra.lean` and `PercLib/CriticalLRP/Analysis/MonotoneRV.lean`;
licence Apache-2.0 as declared in that commit's file headers and
`third_party/critical-lrp/NOTICE.md`; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Modified: `RegularlyVaryingAtTop f α` becomes
`RegularlyVarying α f` of `PercLib/Analysis/RegularVariation/Defs.lean`, so the closure lemmas also
carry measurability on a tail and eventual positivity (re-proved here); the source's
`HasPotterBounds` is written out, and its two lemmas are renamed `potterBounds_mul_rpow` and
`potterBounds_const_mul` accordingly; `import Mathlib`, `autoImplicit`, disabled linters and
`#print` lines are removed.
-/
module

public import PercLib.Analysis.RegularVariation.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Algebra of regular variation, Potter's bounds and doubling -/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### Products, reciprocals and powers of regularly varying functions -/

/-- The product of regularly varying functions is regularly varying, with the
sum of the indices. -/
theorem RegularlyVarying.mul {f g : ℝ → ℝ} {α β : ℝ}
    (hf : RegularlyVarying α f) (hg : RegularlyVarying β g) :
    RegularlyVarying (α + β) (fun x => f x * g x) := by
  obtain ⟨a, ha⟩ := hf.measurable_tail
  obtain ⟨b, hb⟩ := hg.measurable_tail
  refine ⟨⟨max a b, (measurable_restrict_Ici_mono ha (le_max_left a b)).mul
    (measurable_restrict_Ici_mono hb (le_max_right a b))⟩, ?_, fun l hl => ?_⟩
  · filter_upwards [hf.eventually_pos, hg.eventually_pos] with x hx hy
    exact mul_pos hx hy
  · have h3 : Tendsto (fun x => f (l * x) / f x * (g (l * x) / g x)) atTop
        (𝓝 (l ^ α * l ^ β)) := (hf.tendsto hl).mul (hg.tendsto hl)
    rw [← Real.rpow_add hl] at h3
    refine h3.congr' ?_
    filter_upwards [hf.eventually_pos, hg.eventually_pos] with x hx hy
    field_simp

/-- The pointwise reciprocal of a regularly varying function is regularly varying
with negated index. -/
theorem RegularlyVarying.inv {f : ℝ → ℝ} {α : ℝ} (hf : RegularlyVarying α f) :
    RegularlyVarying (-α) (fun x => (f x)⁻¹) := by
  obtain ⟨b, hb⟩ := hf.measurable_tail
  refine ⟨⟨b, hb.inv⟩, ?_, fun l hl => ?_⟩
  · filter_upwards [hf.eventually_pos] with x hx
    exact inv_pos.2 hx
  · have h1 : Tendsto (fun x => (f (l * x) / f x)⁻¹) atTop (𝓝 (l ^ (-α))) := by
      have h0 : Tendsto (fun x => (f (l * x) / f x)⁻¹) atTop (𝓝 ((l ^ α)⁻¹)) :=
        (hf.tendsto hl).inv₀ (by positivity)
      rw [← Real.rpow_neg hl.le α] at h0
      exact h0
    refine h1.congr' ?_
    filter_upwards [hf.eventually_pos] with x hx
    field_simp

/-- `x ↦ x ^ a` is regularly varying of index `a`. -/
theorem regularlyVarying_rpow (a : ℝ) : RegularlyVarying a (fun x : ℝ => x ^ a) := by
  refine ⟨⟨0, measurable_restrict_Ici_of_measurable (measurable_id.pow_const a) 0⟩, ?_,
    fun l hl => ?_⟩
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact Real.rpow_pos_of_pos hx a
  · have h : (fun x : ℝ => (l * x) ^ a / x ^ a) =ᶠ[atTop] fun _ => l ^ a := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [Real.mul_rpow hl.le hx.le,
        mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos hx a))]
    exact tendsto_const_nhds.congr' h.symm

/-- Powers of regularly varying functions are regularly varying, with the index
multiplied by the exponent. -/
theorem RegularlyVarying.rpow {f : ℝ → ℝ} {ρ a : ℝ}
    (hf : RegularlyVarying ρ f) (hp : ∀ᶠ x in atTop, 0 < f x) :
    RegularlyVarying (ρ * a) (fun x => (f x) ^ a) := by
  obtain ⟨b, hb⟩ := hf.measurable_tail
  refine ⟨⟨b, hb.pow_const a⟩, ?_, fun l hl => ?_⟩
  · filter_upwards [hp] with x hx
    exact Real.rpow_pos_of_pos hx a
  · have hpow : ContinuousAt (fun y : ℝ => y ^ a) (l ^ ρ) :=
      Real.continuousAt_rpow_const _ _ (Or.inl (Real.rpow_pos_of_pos hl ρ).ne')
    have hlim := hpow.tendsto.comp (hf.tendsto hl)
    rw [← Real.rpow_mul hl.le] at hlim
    have hscale : Tendsto (fun x : ℝ => l * x) atTop atTop := tendsto_id.const_mul_atTop hl
    refine hlim.congr' ?_
    filter_upwards [hp, hscale.eventually hp] with x hx hlhx
    exact Real.div_rpow hlhx.le hx.le a

/-! ### Algebra of Potter's bounds -/

/-- Potter's bounds (written out as in `lemma_I_2_10`) are preserved when multiplying by an exact
power `x ^ a` (the index shifts by `a`).  This is the step by which `lemma_I_2_10` is applied
to an integrand of the form "power of `r` times a regularly varying `h`". -/
theorem potterBounds_mul_rpow {f : ℝ → ℝ} {α : ℝ}
    (hpot : (∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|)) (a : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α + a - ε) * |y ^ a * f y| ≤ |x ^ a * f x| ∧
        |x ^ a * f x| ≤ (1 + ε) * (x / y) ^ (α + a + ε) * |y ^ a * f y| := by
  intro ε hε
  obtain ⟨X, hX1, hX⟩ := hpot ε hε
  refine ⟨max X 1, le_trans hX1 (le_max_left _ _), fun x y hy hyx => ?_⟩
  have hXy : X ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hypos : 0 < y := lt_of_lt_of_le one_pos hy1
  have hxpos : 0 < x := lt_of_lt_of_le hypos hyx
  obtain ⟨hlo, hhi⟩ := hX x y hXy hyx
  have hyn : |y ^ a * f y| = y ^ a * |f y| := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hypos.le a)]
  have hxn : |x ^ a * f x| = x ^ a * |f x| := by
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hxpos.le a)]
  have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hxpos.le a
  have hya : 0 ≤ y ^ a := Real.rpow_nonneg hypos.le a
  have hdiv : 0 < x / y := div_pos hxpos hypos
  have hkey2 : x ^ a = (x / y) ^ a * y ^ a := by
    rw [Real.div_rpow hxpos.le hypos.le,
      div_mul_cancel₀ _ (ne_of_gt (Real.rpow_pos_of_pos hypos a))]
  have hkey3 : (x / y) ^ (α - ε) * x ^ a = (x / y) ^ (α + a - ε) * y ^ a := by
    rw [hkey2, ← mul_assoc, ← Real.rpow_add hdiv, show α - ε + a = α + a - ε by ring]
  have hkey4 : (x / y) ^ (α + ε) * x ^ a = (x / y) ^ (α + a + ε) * y ^ a := by
    rw [hkey2, ← mul_assoc, ← Real.rpow_add hdiv, show α + ε + a = α + a + ε by ring]
  constructor
  · rw [hyn, hxn]
    have hshape : (1 - ε) * (x / y) ^ (α + a - ε) * (y ^ a * |f y|)
        = (1 - ε) * ((x / y) ^ (α - ε) * x ^ a) * |f y| := by
      rw [hkey3]
      ring
    rw [hshape]
    calc (1 - ε) * ((x / y) ^ (α - ε) * x ^ a) * |f y|
        = (1 - ε) * (x / y) ^ (α - ε) * |f y| * x ^ a := by ring
      _ ≤ |f x| * x ^ a := mul_le_mul_of_nonneg_right hlo hxa
      _ = x ^ a * |f x| := by ring
  · rw [hxn, hyn]
    calc x ^ a * |f x|
        ≤ x ^ a * ((1 + ε) * (x / y) ^ (α + ε) * |f y|) :=
          mul_le_mul_of_nonneg_left hhi hxa
      _ = (1 + ε) * ((x / y) ^ (α + ε) * x ^ a) * |f y| := by ring
      _ = (1 + ε) * (x / y) ^ (α + a + ε) * (y ^ a * |f y|) := by
          rw [hkey4]; ring

/-- Potter's bounds (written out as in `lemma_I_2_10`) are preserved when multiplying by a nonzero
constant. -/
theorem potterBounds_const_mul {f : ℝ → ℝ} {α c : ℝ}
    (hpot : (∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |f y|))
    (hc : c ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, 1 ≤ X ∧ ∀ x y : ℝ, X ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (α - ε) * |c * f y| ≤ |c * f x| ∧
        |c * f x| ≤ (1 + ε) * (x / y) ^ (α + ε) * |c * f y| := by
  intro ε hε
  obtain ⟨X, hX1, hX⟩ := hpot ε hε
  refine ⟨max X 1, le_trans hX1 (le_max_left _ _), fun x y hy hyx => ?_⟩
  obtain ⟨hlo, hhi⟩ := hX x y (le_trans (le_max_left _ _) hy) hyx
  have hcabs : 0 < |c| := abs_pos.2 hc
  constructor
  · rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_left hlo hcabs.le
    linarith [this]
  · rw [abs_mul, abs_mul]
    have := mul_le_mul_of_nonneg_left hhi hcabs.le
    linarith [this]


/-- **Increasing functions of regular variation are doubling** (paper, p. 27):
if `f` is regularly varying of index `ρ` and eventually positive, then
`f (2 x) ≤ C f x` for all large `x`. -/
theorem doubling_of_regularlyVarying {f : ℝ → ℝ} {ρ : ℝ}
    (hrv : RegularlyVarying ρ f) (hp : ∀ᶠ x in atTop, 0 < f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop, f (2 * x) ≤ C * f x := by
  refine ⟨2 ^ ρ + 1, by positivity, ?_⟩
  have h2 : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 (2 ^ ρ)) := hrv.2.2 2 (by norm_num)
  have hev : ∀ᶠ x in atTop, f (2 * x) / f x < 2 ^ ρ + 1 :=
    h2.eventually (eventually_lt_nhds (lt_add_one (2 ^ ρ)))
  filter_upwards [hev, hp] with x hx hxpos
  rw [div_lt_iff₀ hxpos] at hx
  linarith

/-- **Positive-index regularly varying functions are reverse doubling**
(paper, p. 27): there is `C > 0` with `2 f x ≤ f (C x)` for all large `x`. -/
theorem reverse_doubling_of_regularlyVarying {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hrv : RegularlyVarying ρ f) (hp : ∀ᶠ x in atTop, 0 < f x) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x in atTop, 2 * f x ≤ f (C * x) := by
  obtain ⟨C, hC1, hC2⟩ : ∃ C : ℝ, 1 ≤ C ∧ (3 : ℝ) ≤ C ^ ρ := by
    refine ⟨max 2 ((3 : ℝ) ^ (1 / ρ) + 1), le_trans (by norm_num) (le_max_left _ _), ?_⟩
    have h3 : (0:ℝ) ≤ 3 := by norm_num
    have hbase : (3 : ℝ) ^ (1 / ρ) ≤ max 2 ((3 : ℝ) ^ (1 / ρ) + 1) := by
      linarith [le_max_right (2:ℝ) ((3 : ℝ) ^ (1 / ρ) + 1)]
    have hmono : ((3 : ℝ) ^ (1 / ρ)) ^ ρ ≤ (max 2 ((3 : ℝ) ^ (1 / ρ) + 1)) ^ ρ :=
      Real.rpow_le_rpow (Real.rpow_nonneg h3 _) hbase hρ.le
    have hval : ((3 : ℝ) ^ (1 / ρ)) ^ ρ = 3 := by
      rw [← Real.rpow_mul h3, one_div_mul_cancel hρ.ne', Real.rpow_one]
    linarith
  refine ⟨C, hC1, ?_⟩
  have h2 : Tendsto (fun x => f (C * x) / f x) atTop (𝓝 (C ^ ρ)) :=
    hrv.2.2 C (lt_of_lt_of_le one_pos hC1)
  have hev : ∀ᶠ x in atTop, (2:ℝ) < f (C * x) / f x :=
    h2.eventually (eventually_gt_nhds (by linarith : (2:ℝ) < C ^ ρ))
  filter_upwards [hev, hp] with x hx hxpos
  rw [lt_div_iff₀ hxpos] at hx
  linarith

/-! ### Witnesses -/

example : RegularlyVarying (2 + -1) (fun x : ℝ => x ^ (2 : ℝ) * (x ^ (1 : ℝ))⁻¹) :=
  (regularlyVarying_rpow 2).mul (regularlyVarying_rpow 1).inv

example : ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x in atTop, 2 * (x ^ (1 : ℝ)) ≤ (C * x) ^ (1 : ℝ) :=
  reverse_doubling_of_regularlyVarying one_pos (regularlyVarying_rpow 1)
    (regularlyVarying_rpow 1).eventually_pos

end PercLib.Analysis
