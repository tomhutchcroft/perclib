/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The Karamata primitive `∫_{r₀}^r h s / s ds ∼ h r / b` of a regularly varying function of
index `b > 0`, the divergence of the primitive of a regularly varying function of index
`> -1`, and the shift `f + λ ∫ h s / s ds` used in the proof of Lemma I.5.26 of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.

Ported from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/KaramataPrimitive.lean` and
`PercLib/CriticalLRP/Analysis/KaramataDivergence.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop h b` becomes `RegularlyVarying b h` of
`PercLib/Analysis/RegularVariation/Defs.lean`, which contains eventual positivity, so the
separate positivity hypotheses are dropped; `RegularlyVaryingAtTop.congr_fun` is
`RegularlyVarying.congr'`; `intervalIntegrable_of_locallyIntegrableOn` is replaced by mathlib's
`LocallyIntegrableOn.integrableOn_compact_subset`; the algebraic steps are stated for an
arbitrary function in place of the primitive; descriptive names replace `karamataShift_*` and
`lemma_I_5_26_asymptotic*`; the two files are merged; `import Mathlib`, `autoImplicit`,
disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.RegularVariation.GeneralInverse
public import PercLib.Analysis.RegularVariation.LevelInverse

/-! # The Karamata primitive

For `h` measurable and regularly varying of index `b > 0`, Karamata's integral theorem applied to
`s ↦ h s / s` (regularly varying of index `b - 1`) gives the asymptotics of the primitive
`∫_{r₀}^r h s / s ds`. The proof of Lemma I.5.26 of *Critical long-range percolation I* uses it
to shift a signed function `f` to `f + λ ∫ h s / s ds`, which is eventually positive for `λ`
large, and to remove the shift again at the end.

## Main results

* `RegularlyVarying.div_id`: `s ↦ h s / s` is regularly varying of index `b - 1`;
* `tendsto_integral_atTop_of_regularlyVarying`: the primitive of a regularly varying function
  of index `> -1` diverges;
* `tendsto_karamataPrimitive_tail`, `tendsto_karamataPrimitive`,
  `tendsto_karamataPrimitive_of_locallyBounded`: `(∫_{r₀}^r h s / s ds) / h r → 1 / b`;
* `isLittleO_karamataPrimitive`: the same as `∫_{r₀}^r h s / s ds - h r / b = o(h)`;
* `regularlyVarying_karamataPrimitive`: the primitive is regularly varying of index `b`;
* `eventually_pos_add_const_mul_karamataPrimitive`: the shifted function is eventually
  positive once `C b < λ`, where `|f| ≤ C h`;
* `tendsto_div_of_tendsto_add_const_mul_karamataPrimitive`: `f_λ / h → c` gives
  `f / h → c - λ / b`;
* `tendsto_div_of_tendsto_shift_div_karamataPrimitive`: the conclusion
  `f / h → A / (b - a)` of Lemma I.5.26 from the output of Lemma I.4.21 for the shifted
  function;
* `hasDerivAt_add_const_mul_karamataPrimitive`: `f_λ' = f' + λ h / r`.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-! ### Preparatory lemmas -/

/-- **Dividing by the identity lowers the index by one.** If `h` is regularly varying of index
`b`, then `s ↦ h s / s` is regularly varying of index `b - 1`. -/
theorem RegularlyVarying.div_id {h : ℝ → ℝ} {b : ℝ} (hrv : RegularlyVarying b h) :
    RegularlyVarying (b - 1) (fun s => h s / s) := by
  have hmul := hrv.mul (regularlyVarying_rpow (-1))
  rw [show b + (-1 : ℝ) = b - 1 by ring] at hmul
  refine hmul.congr' (Eventually.of_forall fun s => ?_)
  simp only [div_eq_mul_inv, Real.rpow_neg_one]

/-- **Interval integrability on a tail from local boundedness**: a measurable function bounded
on every compact subinterval of `[r₀, ∞)`, with `r₀ > 0`, has `s ↦ h s / s` interval integrable
on every interval of that tail. -/
theorem intervalIntegrable_div_of_locallyBounded_tail {h : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hbdd : ∀ R, r₀ ≤ R → ∃ C, ∀ s, r₀ ≤ s → s ≤ R → |h s| ≤ C) :
    ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y := by
  intro x y hx hxy
  obtain ⟨C, hC⟩ := hbdd y (le_trans hx hxy)
  have hxpos : 0 < x := lt_of_lt_of_le hr₀ hx
  refine IntegrableOn.intervalIntegrable (IntegrableOn.of_bound
    (isCompact_uIcc (a := x) (b := y)).measure_lt_top ?_ (|C| / x) ?_)
  · exact (hmeas.div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
    rw [uIcc_of_le hxy] at hs
    have hspos : 0 < s := lt_of_lt_of_le hxpos hs.1
    have h1 : |h s| ≤ |C| := le_trans (hC s (le_trans hx hs.1) hs.2) (le_abs_self C)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hspos, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul h1 (by simpa [one_div] using one_div_le_one_div_of_le hxpos hs.1)
      (by positivity) (abs_nonneg C)

/-- A primitive `r ↦ ∫_{r₀}^r g` of a function integrable on every interval of the tail
`[r₀, ∞)` is measurable on that tail. -/
theorem measurable_restrict_Ici_primitive {g : ℝ → ℝ} {r₀ : ℝ}
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y) :
    Measurable ((Ici r₀).domRestrict fun r => ∫ s in r₀..r, g s) := by
  have hcont : ContinuousOn (fun r => ∫ s in r₀..r, g s) (Ici r₀) := by
    intro x hx
    have hx' : r₀ ≤ x := hx
    have hI := intervalIntegral.continuousOn_primitive_interval' (hloc r₀ (x + 1) le_rfl
      (by linarith)) (left_mem_uIcc (a := r₀) (b := x + 1))
    rw [uIcc_of_le (by linarith : r₀ ≤ x + 1)] at hI
    refine (hI x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (continuousOn_iff_continuous_domRestrict.1 hcont).measurable

/-! ### Divergence of the primitive -/

/-- **The primitive of a regularly varying function of index `> -1` diverges**, in both the
positive- and the negative-index case. -/
theorem tendsto_integral_atTop_of_regularlyVarying {φ : ℝ → ℝ} {ρ : ℝ}
    (hρ : -1 < ρ) (hφm : Measurable φ) (hφrv : RegularlyVarying ρ φ)
    (hloc : ∀ x y : ℝ, 1 ≤ x → x ≤ y → IntervalIntegrable φ volume x y) :
    Tendsto (fun r => ∫ s in 1..r, φ s) atTop atTop := by
  set T : ℝ → ℝ := (Ioi 1).indicator φ with hTdef
  have hTm : Measurable T := hφm.indicator measurableSet_Ioi
  have hTrv : RegularlyVarying ρ T := regularlyVarying_indicator_Ioi hφrv
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hloc
  have hK : Tendsto (fun r => (∫ s in 1..r, T s) / (r * T r)) atTop (𝓝 (1 / (ρ + 1))) :=
    lemma_I_2_10_of_regularlyVarying hρ hTm hTloc hTrv.eventually_pos hTrv
  have hden : Tendsto (fun r => r * T r) atTop atTop :=
    tendsto_r_mul_of_potter hρ hTrv.eventually_pos (potterBounds_of_regularlyVarying hTm hTrv)
  have hleft : Tendsto (fun r => ∫ s in 1..r, T s) atTop atTop :=
    Filter.Tendsto.num hden (one_div_pos.mpr (by linarith)) hK
  refine hleft.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with r hr
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [uIoc_of_le hr.le] at hx
  exact Set.indicator_of_mem hx.1 φ

/-! ### The Karamata primitive -/

/-- **Karamata's theorem for the primitive `∫ h s / s ds`, cut at `r₁ ≥ 1`.** The integrand is
extended by zero below `r₁`, which preserves regular variation of index `b - 1` and makes it
locally integrable on `(0, ∞)`; Karamata's integral theorem then applies. -/
theorem tendsto_karamataPrimitive_of_one_le {h : ℝ → ℝ} {b r₁ : ℝ}
    (hb : 0 < b) (hr₁ : 1 ≤ r₁) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₁ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y) :
    Tendsto (fun r => (∫ s in r₁..r, h s / s) / h r) atTop (𝓝 (1 / b)) := by
  have hr₁pos : 0 < r₁ := lt_of_lt_of_le one_pos hr₁
  set g : ℝ → ℝ := fun s => h s / s with hgdef
  set T : ℝ → ℝ := (Ioi r₁).indicator g with hTdef
  have hTm : Measurable T := (hmeas.div measurable_id).indicator measurableSet_Ioi
  have hTrv : RegularlyVarying (b - 1) T := regularlyVarying_indicator_Ioi hrv.div_id
  have hTloc : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hloc
  have hbase := lemma_I_2_10_of_regularlyVarying (f := T) (α := b - 1) (by linarith)
    hTm hTloc hTrv.eventually_pos hTrv
  rw [show (b - 1) + 1 = b by ring] at hbase
  have hTint : ∀ a c : ℝ, 0 < a → a ≤ c → IntervalIntegrable T volume a c := fun a c ha hac =>
    (hTloc.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le ha (by
      rw [uIcc_of_le hac] at hz; exact hz.1)) isCompact_uIcc).intervalIntegrable
  have hnum : ∀ᶠ r in atTop, (∫ s in 1..r, T s) = ∫ s in r₁..r, g s := by
    filter_upwards [eventually_ge_atTop r₁] with r hr
    have hzero : (∫ s in 1..r₁, T s) = 0 := by
      have hz : EqOn T (fun _ => 0) (uIcc 1 r₁) := by
        intro x hx
        rw [uIcc_of_le hr₁] at hx
        exact Set.indicator_of_notMem (fun hm => not_lt_of_ge hx.2 (Set.mem_Ioi.1 hm)) g
      rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hTint 1 r₁ one_pos hr₁) (hTint r₁ r hr₁pos hr)
    have hcongr : (∫ s in r₁..r, T s) = ∫ s in r₁..r, g s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with x hx
      rw [uIoc_of_le hr] at hx
      exact Set.indicator_of_mem (Set.mem_Ioi.2 hx.1) g
    rw [← hadd, hzero, zero_add, hcongr]
  have hden : ∀ᶠ r in atTop, r * T r = h r := by
    filter_upwards [eventually_gt_atTop r₁] with r hr
    have hrne : r ≠ 0 := ne_of_gt (lt_trans hr₁pos hr)
    rw [hTdef, Set.indicator_of_mem (Set.mem_Ioi.2 hr), hgdef]
    field_simp
  refine hbase.congr' ?_
  filter_upwards [hnum, hden] with r hrn hrd
  rw [hrn, hrd]

/-- **The Karamata primitive** (the analytic input to Lemma I.5.26): if `h` is measurable and
regularly varying of index `b > 0`, and `s ↦ h s / s` is interval integrable on the tail
`[r₀, ∞)`, then `(∫_{r₀}^r h s / s ds) / h r → 1 / b`. No sign of `r₀` is needed. -/
theorem tendsto_karamataPrimitive_tail {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y) :
    Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)) := by
  set r₁ := max 1 r₀ with hr₁def
  have hr₀r₁ : r₀ ≤ r₁ := le_max_right _ _
  have hbase := tendsto_karamataPrimitive_of_one_le hb (le_max_left 1 r₀) hmeas hrv
    (fun x y hx hxy => hloc x y (le_trans hr₀r₁ hx) hxy)
  set K : ℝ := ∫ s in r₀..r₁, h s / s with hKdef
  have hshift : ∀ᶠ r in atTop, (∫ s in r₀..r, h s / s) = (∫ s in r₁..r, h s / s) + K := by
    filter_upwards [eventually_ge_atTop r₁] with r hr
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hloc r₀ r₁ le_rfl hr₀r₁) (hloc r₁ r hr₀r₁ hr)
    linarith
  have hK0 : Tendsto (fun r => K / h r) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (hrv.tendsto_atTop hb hmeas).inv_tendsto_atTop.const_mul K
  have hsum := hbase.add hK0
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hshift] with r hr
  rw [hr, add_div]

/-- **The Karamata primitive, local-integrability form**: it suffices that `s ↦ h s / s` be
locally integrable on `(0, ∞)` and `r₀ > 0`. -/
theorem tendsto_karamataPrimitive {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0)) :
    Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)) :=
  tendsto_karamataPrimitive_tail hb hmeas hrv fun x y hx hxy =>
    (hloc.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le (lt_of_lt_of_le hr₀ hx) (by
      rw [uIcc_of_le hxy] at hz; exact hz.1)) isCompact_uIcc).intervalIntegrable

/-- **The Karamata primitive with no integrability side condition**: a measurable regularly
varying `h` of index `b > 0` that is bounded on compact subintervals of `[r₀, ∞)`, `r₀ > 0`,
satisfies the primitive asymptotics. -/
theorem tendsto_karamataPrimitive_of_locallyBounded {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hbdd : ∀ R, r₀ ≤ R → ∃ C, ∀ s, r₀ ≤ s → s ≤ R → |h s| ≤ C) :
    Tendsto (fun r => (∫ s in r₀..r, h s / s) / h r) atTop (𝓝 (1 / b)) :=
  tendsto_karamataPrimitive_tail hb hmeas hrv
    (intervalIntegrable_div_of_locallyBounded_tail hr₀ hmeas hbdd)

/-! ### The primitive as a little-`o` perturbation, and its regular variation -/

/-- If `u / h → c` along a filter on which `h` is eventually non-zero, then `u - c h = o(h)`. -/
theorem isLittleO_sub_const_mul_of_tendsto_div {α : Type*} {l : Filter α} {u h : α → ℝ} {c : ℝ}
    (hne : ∀ᶠ x in l, h x ≠ 0) (hK : Tendsto (fun x => u x / h x) l (𝓝 c)) :
    (fun x => u x - c * h x) =o[l] h := by
  rw [Asymptotics.isLittleO_iff_tendsto' (hne.mono fun x hx h0 => absurd h0 hx)]
  have h2 := hK.sub_const c
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [hne] with x hx
  field_simp

/-- The Karamata primitive differs from `h / b` by `o(h)`: the form
`∫_{r₀}^r h s / s ds = (1 ± o(1)) (1/b) h r` used in the proof of Lemma I.5.26. -/
theorem isLittleO_karamataPrimitive {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0)) :
    (fun r => (∫ s in r₀..r, h s / s) - (1 / b) * h r) =o[atTop] h :=
  isLittleO_sub_const_mul_of_tendsto_div (hrv.eventually_pos.mono fun _ hx => hx.ne')
    (tendsto_karamataPrimitive hb hr₀ hmeas hrv hloc)

/-- **The Karamata primitive is regularly varying of the same index `b`** (tail-integrability
form), because it is asymptotic to `h / b`. -/
theorem regularlyVarying_karamataPrimitive_of_tail {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y) :
    RegularlyVarying b (fun r => ∫ s in r₀..r, h s / s) := by
  refine (hrv.const_mul (one_div_pos.2 hb)).of_tendsto_div ?_
    ⟨r₀, measurable_restrict_Ici_primitive hloc⟩
  have hmul := (tendsto_karamataPrimitive_tail hb hmeas hrv hloc).const_mul b
  rw [mul_one_div_cancel hb.ne'] at hmul
  refine hmul.congr' ?_
  filter_upwards [hrv.eventually_pos] with r hr
  field_simp

/-- **The Karamata primitive is regularly varying of the same index `b`**
(local-integrability form). -/
theorem regularlyVarying_karamataPrimitive {h : ℝ → ℝ} {b r₀ : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0)) :
    RegularlyVarying b (fun r => ∫ s in r₀..r, h s / s) :=
  regularlyVarying_karamataPrimitive_of_tail hb hmeas hrv fun x y hx hxy =>
    (hloc.integrableOn_compact_subset (fun z hz => lt_of_lt_of_le (lt_of_lt_of_le hr₀ hx) (by
      rw [uIcc_of_le hxy] at hz; exact hz.1)) isCompact_uIcc).intervalIntegrable

/-! ### The shift `f_λ = f + λ P` -/

/-- **Positivity of a shifted function**: if `P / h → κ` with `h` eventually positive,
`|f| ≤ C h` eventually and `C < λ κ`, then `f + λ P` is eventually positive. -/
theorem eventually_pos_add_const_mul_of_tendsto_div {α : Type*} {l : Filter α}
    {f h P : α → ℝ} {κ C lam : ℝ} (hC : C < lam * κ) (hpos : ∀ᶠ x in l, 0 < h x)
    (hK : Tendsto (fun x => P x / h x) l (𝓝 κ)) (hf : ∀ᶠ x in l, |f x| ≤ C * h x) :
    ∀ᶠ x in l, 0 < f x + lam * P x := by
  have hev : ∀ᶠ x in l, C < lam * (P x / h x) :=
    (hK.const_mul lam).eventually (eventually_gt_nhds hC)
  filter_upwards [hev, hpos, hf] with x hx hhx hfx
  have hshift : C * h x < lam * P x := by
    have := mul_lt_mul_of_pos_right hx hhx
    rwa [mul_assoc, div_mul_cancel₀ _ hhx.ne'] at this
  linarith [neg_abs_le (f x)]

/-- **Removing the shift**: if `P / h → κ` and `(f + λ P) / h → c`, then `f / h → c - λ κ`. -/
theorem tendsto_div_of_tendsto_add_const_mul_div {α : Type*} {l : Filter α}
    {f h P : α → ℝ} {κ lam c : ℝ}
    (hK : Tendsto (fun x => P x / h x) l (𝓝 κ))
    (hf : Tendsto (fun x => (f x + lam * P x) / h x) l (𝓝 c)) :
    Tendsto (fun x => f x / h x) l (𝓝 (c - lam * κ)) := by
  refine (hf.sub (hK.const_mul lam)).congr fun x => ?_
  rw [add_div, mul_div_assoc]
  ring

/-- **Positivity of the shifted function** (the choice of `λ` in the proof of Lemma I.5.26,
tail-integrability form): if `|f| ≤ C h` eventually and `C b < λ`, then
`f + λ ∫_{r₀}^r h s / s ds` is eventually positive. -/
theorem eventually_pos_add_const_mul_karamataPrimitive_of_tail {f h : ℝ → ℝ} {b r₀ C lam : ℝ}
    (hb : 0 < b) (hC : C * b < lam) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r) :
    ∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s :=
  eventually_pos_add_const_mul_of_tendsto_div (κ := 1 / b)
    (by rw [mul_one_div, lt_div_iff₀ hb]; exact hC) hrv.eventually_pos
    (tendsto_karamataPrimitive_tail hb hmeas hrv hloc) hf

/-- **Positivity of the shifted function** (local-integrability form). -/
theorem eventually_pos_add_const_mul_karamataPrimitive {f h : ℝ → ℝ} {b r₀ C lam : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hC : C * b < lam) (hmeas : Measurable h)
    (hrv : RegularlyVarying b h) (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r) :
    ∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s :=
  eventually_pos_add_const_mul_of_tendsto_div (κ := 1 / b)
    (by rw [mul_one_div, lt_div_iff₀ hb]; exact hC) hrv.eventually_pos
    (tendsto_karamataPrimitive hb hr₀ hmeas hrv hloc) hf

/-- **Removing the shift** (the final algebraic step of Lemma I.5.26, tail-integrability
form): if `(f + λ ∫_{r₀}^r h s / s ds) / h → c`, then `f / h → c - λ / b`. -/
theorem tendsto_div_of_tendsto_add_const_mul_karamataPrimitive_of_tail {f h : ℝ → ℝ}
    {b r₀ lam c : ℝ} (hb : 0 < b) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hf : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) := by
  simpa [div_eq_mul_inv] using
    tendsto_div_of_tendsto_add_const_mul_div (tendsto_karamataPrimitive_tail hb hmeas hrv hloc) hf

/-- **Removing the shift** (local-integrability form). -/
theorem tendsto_div_of_tendsto_add_const_mul_karamataPrimitive {f h : ℝ → ℝ} {b r₀ lam c : ℝ}
    (hb : 0 < b) (hr₀ : 0 < r₀) (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hf : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) := by
  simpa [div_eq_mul_inv] using
    tendsto_div_of_tendsto_add_const_mul_div (tendsto_karamataPrimitive hb hr₀ hmeas hrv hloc) hf

/-- **The Karamata step of Lemma I.5.26** (local-integrability form): for `|f| ≤ C h` with
`C b < λ`, the shifted function `f_λ = f + λ ∫ h s / s ds` is eventually positive, and if
`f_λ / h → c` then `f / h → c - λ / b`. -/
theorem eventually_pos_and_tendsto_div_of_tendsto_add_const_mul_karamataPrimitive
    {f h : ℝ → ℝ} {b r₀ C lam c : ℝ} (hb : 0 < b) (hr₀ : 0 < r₀) (hC : C * b < lam)
    (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hflam : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    (∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s) ∧
      Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) :=
  ⟨eventually_pos_add_const_mul_karamataPrimitive hb hr₀ hC hmeas hrv hloc hf,
    tendsto_div_of_tendsto_add_const_mul_karamataPrimitive hb hr₀ hmeas hrv hloc hflam⟩

/-- **The Karamata step of Lemma I.5.26** (tail-integrability form). -/
theorem eventually_pos_and_tendsto_div_of_tendsto_add_const_mul_karamataPrimitive_of_tail
    {f h : ℝ → ℝ} {b r₀ C lam c : ℝ} (hb : 0 < b) (hC : C * b < lam)
    (hmeas : Measurable h) (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hf : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hflam : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop (𝓝 c)) :
    (∀ᶠ r in atTop, 0 < f r + lam * ∫ s in r₀..r, h s / s) ∧
      Tendsto (fun r => f r / h r) atTop (𝓝 (c - lam / b)) :=
  ⟨eventually_pos_add_const_mul_karamataPrimitive_of_tail hb hC hmeas hrv hloc hf,
    tendsto_div_of_tendsto_add_const_mul_karamataPrimitive_of_tail hb hmeas hrv hloc hflam⟩

/-- **The arithmetic identity behind the choice of `λ`** in Lemma I.5.26:
`(1/(b-a)) (A + (b-a) λ / b) - λ / b = A / (b-a)`, independently of `λ`. -/
theorem one_div_sub_mul_add_mul_div_sub_div_eq {a b A lam : ℝ} (hb : b ≠ 0) (hab : a ≠ b) :
    (1 / (b - a)) * (A + (b - a) * lam / b) - lam / b = A / (b - a) := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  field_simp
  ring

/-- **The conclusion of Lemma I.5.26**, `f r = (A/(b-a) + o(1)) h r`, from the output of the
positive ODE Lemma I.4.21 for the shifted function `f_λ = f + λ ∫ h s / s ds`
(local-integrability form). `hI421` is that output, taken as a hypothesis:
`f_λ / h → (1/(b-a)) (A + (b-a) λ / b)`. -/
theorem tendsto_div_of_tendsto_shift_div_karamataPrimitive {f h : ℝ → ℝ} {a b A r₀ lam : ℝ}
    (ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀) (hmeas : Measurable h)
    (hrv : RegularlyVarying b h) (hloc : LocallyIntegrableOn (fun s => h s / s) (Ioi 0))
    (hI421 : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop
      (𝓝 ((1 / (b - a)) * (A + (b - a) * lam / b)))) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hb : 0 < b := ha.trans hab
  have h := tendsto_div_of_tendsto_add_const_mul_karamataPrimitive hb hr₀ hmeas hrv hloc hI421
  rwa [one_div_sub_mul_add_mul_div_sub_div_eq hb.ne' hab.ne] at h

/-- **The conclusion of Lemma I.5.26** (tail-integrability form), with the output of
Lemma I.4.21 for the shifted function as a hypothesis. -/
theorem tendsto_div_of_tendsto_shift_div_karamataPrimitive_of_tail {f h : ℝ → ℝ}
    {a b A r₀ lam : ℝ} (ha : 0 < a) (hab : a < b) (hmeas : Measurable h)
    (hrv : RegularlyVarying b h)
    (hloc : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable (fun s => h s / s) volume x y)
    (hI421 : Tendsto (fun r => (f r + lam * ∫ s in r₀..r, h s / s) / h r) atTop
      (𝓝 ((1 / (b - a)) * (A + (b - a) * lam / b)))) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a))) := by
  have hb : 0 < b := ha.trans hab
  have h := tendsto_div_of_tendsto_add_const_mul_karamataPrimitive_of_tail hb hmeas hrv hloc
    hI421
  rwa [one_div_sub_mul_add_mul_div_sub_div_eq hb.ne' hab.ne] at h

/-- **The shift `f_λ = f + λ ∫_{r₀}^r h s / s ds` is differentiable**, with derivative
`f' + λ h r / r`; only continuity of `h` at the evaluation point is needed. -/
theorem hasDerivAt_add_const_mul_karamataPrimitive {f f' h : ℝ → ℝ} {r₀ lam r : ℝ}
    (hf : HasDerivAt f (f' r) r) (hint : IntervalIntegrable (fun s => h s / s) volume r₀ r)
    (hmeas : Measurable h) (hcont : ContinuousAt h r) (hr : r ≠ 0) :
    HasDerivAt (fun x => f x + lam * ∫ s in r₀..x, h s / s) (f' r + lam * (h r / r)) r := by
  have hc : ContinuousAt (fun s : ℝ => h s / s) r := hcont.div continuousAt_id hr
  have hsm : StronglyMeasurableAtFilter (fun s : ℝ => h s / s) (𝓝 r) volume :=
    (hmeas.div measurable_id).stronglyMeasurable.stronglyMeasurableAtFilter
  exact hf.add ((intervalIntegral.integral_hasDerivAt_right hint hsm hc).const_mul lam)

end PercLib.Analysis
