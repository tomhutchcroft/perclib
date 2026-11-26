/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Lemma I.4.13 (second half) of T. Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1: the transform `r ↦ r^{-a} ∫_1^r s^{a-1} h(s) ds` of a logarithmically
integrable error function `h` is again a logarithmically integrable error function.
-/
module

public import PercLib.Analysis.RegularVariation.LogErrorTransforms
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! # The second logarithmic error transform for tail-measurable functions

`PercLib.Analysis.lemma_I_4_13_second` asks for a globally measurable `h`. Here the second
transform `r ↦ r^{-a} ∫_{(r₀, r]} s^{a-1} h(s) ds` is treated for `h` with
`IsLogErrorFunction h` only, whose measurability is only on a tail.

## Main results

* `isLogErrorFunction_rpow_neg_mul_setIntegral_Ioc_of_measurable_Ici`: the transform from
  any `r₀ > 0` beyond a measurability tail point of `h`, with `|h s| / s` integrable on
  `(r₀, ∞)`, is a log-error function;
* `IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_of_integrableOn`: the transform from any
  `r₀`, when `s^{a-1} h(s)` is integrable on every `(r₀, r]`;
* `IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_one`: the paper's form (lower limit `1`)
  under local integrability of `h` on `(1, r]` for every `r`;
* `not_integrableOn_rpow_mul_indicator_sub_inv`: local integrability does not follow from
  `IsLogErrorFunction`: `h = 𝟙_{(1,2)} (s - 1)⁻¹` is a log-error function for which
  `s^{a-1} h(s)` is integrable on no `(1, r]`, `r > 1`;
* `IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc`: with no premise, by the convention
  that a non-integrable function has integral `0` (the transform is then eventually `0`).
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

variable {h F : ℝ → ℝ} {a b r₀ : ℝ}

/-- The second transform only sees `h` on `(r₀, r]`, so it is unchanged when `h` is replaced
by a function agreeing with it on `[b, ∞)`, `b ≤ r₀`. -/
theorem rpow_neg_mul_setIntegral_Ioc_eq_of_eqOn_Ici (hFeq : ∀ x, b ≤ x → F x = h x)
    (hbr : b ≤ r₀) (r : ℝ) :
    r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * F s
      = r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s := by
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [hFeq s (hbr.trans hs.1.le)]

/-- **Lemma I.4.13, second half, for tail-measurable `h`.** If `h` is a log-error function
measurable on `[b, ∞)`, `0 < r₀`, `b ≤ r₀` and `|h s| / s` is integrable on `(r₀, ∞)`, then
`r ↦ r^{-a} ∫_{(r₀, r]} s^{a-1} h(s) ds` is a log-error function. -/
theorem isLogErrorFunction_rpow_neg_mul_setIntegral_Ioc_of_measurable_Ici
    (hlog : IsLogErrorFunction h) (ha : 0 < a) (hr₀ : 0 < r₀)
    (hb : Measurable ((Ici b).domRestrict h)) (hbr : b ≤ r₀)
    (hint : IntegrableOn (fun s => |h s| / s) (Ioi r₀)) :
    IsLogErrorFunction (fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s) := by
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_eqOn_Ici hb
  have hintF : IntegrableOn (fun s => |F s| / s) (Ioi r₀) := by
    refine hint.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only
    rw [hFeq s (hbr.trans (le_of_lt hs))]
  have hF0 : Tendsto F atTop (𝓝 0) :=
    hlog.2.congr' (eventually_atTop.2 ⟨b, fun x hx => (hFeq x hx).symm⟩)
  have hfun : (fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s)
      = fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * F s :=
    funext fun r => (rpow_neg_mul_setIntegral_Ioc_eq_of_eqOn_Ici hFeq hbr r).symm
  rw [hfun]
  exact lemma_I_4_13_second ha hr₀ hF hintF hF0

/-- **Lemma I.4.13, second half, from an arbitrary lower limit.** If `h` is a log-error
function and `s^{a-1} h(s)` is integrable on `(r₀, r]` for every `r`, then
`r ↦ r^{-a} ∫_{(r₀, r]} s^{a-1} h(s) ds` is a log-error function. -/
theorem IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_of_integrableOn
    (hlog : IsLogErrorFunction h) (ha : 0 < a)
    (hloc : ∀ r, IntegrableOn (fun s => s ^ (a - 1) * h s) (Ioc r₀ r)) :
    IsLogErrorFunction (fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s) := by
  obtain ⟨⟨⟨b, hb⟩, c, hc, hint⟩, h0⟩ := hlog
  have hlog : IsLogErrorFunction h := ⟨⟨⟨b, hb⟩, c, hc, hint⟩, h0⟩
  set r₁ := max (max b c) r₀ with hr₁
  have hbr₁ : b ≤ r₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hcr₁ : c ≤ r₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hr₀r₁ : r₀ ≤ r₁ := le_max_right _ _
  have hr₁0 : 0 < r₁ := hc.trans_le hcr₁
  set K := ∫ s in Ioc r₀ r₁, s ^ (a - 1) * h s with hK
  have htail := isLogErrorFunction_rpow_neg_mul_setIntegral_Ioc_of_measurable_Ici hlog ha hr₁0
    hb hbr₁ (hint.mono_set (Ioi_subset_Ioi hcr₁))
  have hsum := isLogErrorFunction_add (isLogErrorFunction_const_rpow_neg (c := K) ha hr₁0) htail
  have heq : ∀ r, r₁ ≤ r → K * r ^ (-a) + r ^ (-a) * ∫ s in Ioc r₁ r, s ^ (a - 1) * h s
      = r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s := by
    intro r hr
    rw [← Ioc_union_Ioc_eq_Ioc hr₀r₁ hr,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        ((hloc r).mono_set (Ioc_subset_Ioc_right hr))
        ((hloc r).mono_set (Ioc_subset_Ioc_left hr₀r₁))]
    ring
  refine isLogErrorFunction_congr hsum (eventually_atTop.2 ⟨r₁, heq⟩) ⟨r₁, ?_⟩
  obtain ⟨G, hG, hGeq⟩ := exists_measurable_eqOn_Ici hb
  have hfun : (Ici r₁).domRestrict
        (fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s)
      = (Ici r₁).domRestrict
        (fun r : ℝ => K * r ^ (-a) + r ^ (-a) * ∫ s in Ioc r₁ r, s ^ (a - 1) * G s) := by
    funext r
    simp only [domRestrict_apply]
    rw [rpow_neg_mul_setIntegral_Ioc_eq_of_eqOn_Ici hGeq hbr₁, heq r r.2]
  rw [hfun]
  exact measurable_restrict_Ici_of_measurable
    ((by fun_prop : Measurable fun r : ℝ => K * r ^ (-a)).add
      (measurable_logTransformSecond hG)) r₁

/-- **Lemma I.4.13, second half, in the paper's form** (lower limit `1`), under local
integrability of `h` on `(1, r]` for every `r`. The premise cannot be dropped as a
consequence of `IsLogErrorFunction h`: see `not_integrableOn_rpow_mul_indicator_sub_inv`. -/
theorem IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_one (hlog : IsLogErrorFunction h)
    (ha : 0 < a) (hloc : ∀ r, IntegrableOn h (Ioc 1 r)) :
    IsLogErrorFunction (fun r : ℝ => r ^ (-a) * ∫ s in Ioc 1 r, s ^ (a - 1) * h s) := by
  refine hlog.rpow_neg_mul_setIntegral_Ioc_of_integrableOn ha fun r => ?_
  have hcont : ContinuousOn (fun s : ℝ => s ^ (a - 1)) (Icc 1 r) := fun s hs =>
    (Real.continuousAt_rpow_const s (a - 1)
      (Or.inl (zero_lt_one.trans_le hs.1).ne')).continuousWithinAt
  exact (hloc r).continuousOn_mul_of_subset hcont isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self

/-- The function `𝟙_{(1,2)}(s) (s - 1)⁻¹` is a log-error function. -/
theorem isLogErrorFunction_indicator_sub_inv :
    IsLogErrorFunction ((Ioo (1 : ℝ) 2).indicator fun s => (s - 1)⁻¹) := by
  have hmeas : Measurable ((Ioo (1 : ℝ) 2).indicator fun s => (s - 1)⁻¹) :=
    (by fun_prop : Measurable fun s : ℝ => (s - 1)⁻¹).indicator measurableSet_Ioo
  have hzero : ∀ s : ℝ, 2 ≤ s → (Ioo (1 : ℝ) 2).indicator (fun s => (s - 1)⁻¹) s = 0 :=
    fun s hs => indicator_of_notMem (fun hm : s ∈ Ioo (1 : ℝ) 2 => (not_lt.2 hs) hm.2) _
  refine ⟨⟨⟨0, measurable_restrict_Ici_of_measurable hmeas 0⟩, 2, two_pos, ?_⟩, ?_⟩
  · refine (integrableOn_zero (μ := volume) (s := Ioi (2 : ℝ))).congr_fun (fun s hs => ?_)
      measurableSet_Ioi
    simp [hzero s (le_of_lt hs)]
  · exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨2, fun s hs => (hzero s hs).symm⟩)

/-- Local integrability near `1` does not follow from `IsLogErrorFunction`: for
`h = 𝟙_{(1,2)}(s) (s - 1)⁻¹` (a log-error function, `isLogErrorFunction_indicator_sub_inv`)
the integrand `s^{a-1} h(s)` of the paper's `∫_1^r` is integrable on no `(1, r]`, `r > 1`. -/
theorem not_integrableOn_rpow_mul_indicator_sub_inv (a : ℝ) {r : ℝ} (hr : 1 < r) :
    ¬ IntegrableOn
      (fun s => s ^ (a - 1) * (Ioo (1 : ℝ) 2).indicator (fun s => (s - 1)⁻¹) s) (Ioc 1 r) := by
  intro hint
  set u := min r (3 / 2) with hu
  have h1u : 1 < u := lt_min hr (by norm_num)
  have hu2 : u < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hint' := hint.mono_set (Ioc_subset_Ioc_right (min_le_left r (3 / 2)))
  have hcont : ContinuousOn (fun s : ℝ => s ^ (1 - a)) (Icc 1 u) := fun s hs =>
    (Real.continuousAt_rpow_const s (1 - a)
      (Or.inl (zero_lt_one.trans_le hs.1).ne')).continuousWithinAt
  have hprod := hint'.continuousOn_mul_of_subset hcont isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self
  have hinv : IntegrableOn (fun s : ℝ => (s - 1)⁻¹) (Ioc 1 u) := by
    refine hprod.congr_fun (fun s hs => ?_) measurableSet_Ioc
    have hs0 : 0 < s := zero_lt_one.trans hs.1
    simp only
    have hmem : s ∈ Ioo (1 : ℝ) 2 := ⟨hs.1, hs.2.trans_lt hu2⟩
    rw [indicator_of_mem hmem, ← mul_assoc, ← Real.rpow_add hs0]
    simp
  have hII : IntervalIntegrable (fun s : ℝ => (s - 1)⁻¹) volume 1 u :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h1u.le).2 hinv
  rw [intervalIntegrable_sub_inv_iff] at hII
  rcases hII with h | h
  · exact h1u.ne h
  · exact h (left_mem_uIcc)

/-- **The second transform with no premise.** For every lower limit `r₀`, the transform
`r ↦ r^{-a} ∫_{(r₀, r]} s^{a-1} h(s) ds` of a log-error function is a log-error function.
This relies on the convention that the integral of a non-integrable function is `0`: if
`s^{a-1} h(s)` fails to be integrable on some `(r₀, T]`, the transform vanishes on
`[T, ∞)`. For the paper's integral to be defined, use
`IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_of_integrableOn`. -/
theorem IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc (hlog : IsLogErrorFunction h)
    (ha : 0 < a) (r₀ : ℝ) :
    IsLogErrorFunction (fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s) := by
  by_cases hloc : ∀ r, IntegrableOn (fun s => s ^ (a - 1) * h s) (Ioc r₀ r)
  · exact hlog.rpow_neg_mul_setIntegral_Ioc_of_integrableOn ha hloc
  push Not at hloc
  obtain ⟨T, hT⟩ := hloc
  have hzero : ∀ r, T ≤ r → r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s = 0 := by
    intro r hr
    have hni : ¬ IntegrableOn (fun s => s ^ (a - 1) * h s) (Ioc r₀ r) := fun hi =>
      hT (hi.mono_set (Ioc_subset_Ioc_right hr))
    rw [integral_undef hni, mul_zero]
  refine isLogErrorFunction_congr (isLogErrorFunction_const_rpow_neg (c := 0) ha one_pos)
    (eventually_atTop.2 ⟨T, fun r hr => by simp only; rw [hzero r hr, zero_mul]⟩) ⟨T, ?_⟩
  have hfun : (Ici T).domRestrict
        (fun r : ℝ => r ^ (-a) * ∫ s in Ioc r₀ r, s ^ (a - 1) * h s) = fun _ => 0 := by
    funext r
    exact hzero r r.2
  rw [hfun]
  exact measurable_const

end PercLib.Analysis
