/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The tail event `P(X ≥ x)` of Theorem I.2.11 of T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1, p. 26 (citing Feller XIII.5.2).

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/TauberianEndpoints.lean` and
`PercLib/CriticalLRP/Analysis/LaplaceUnique.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f (-α)` becomes `RegularlyVarying (-α) f` of
`PercLib/Analysis/RegularVariation/Defs.lean` (which also asks measurability on a tail and
eventual positivity); the endpoint bridges are proved for an arbitrary finite measure and an
arbitrary regularly varying comparison function, the source statements being corollaries;
hypotheses the proofs do not use are removed; the source lemmas `tendsto_rv_ratio_mul`
(`RegularlyVarying.tendsto`) and `toReal_le_toReal_of_subset` (mathlib's `measureReal_mono`)
are dropped; the non-strict Laplace–tail identity is derived from the strict one with
mathlib's `meas_le_ae_eq_meas_lt`, so the source helper
`one_sub_exp_eq_setIntegral_indicator_Iic` and the second proof
`laplace_tail_asymptotic_of_tail_ge'` are dropped; the rescaling identity is derived from
`integral_exp_sigma_mul_div`. The content of `LaplaceUnique.lean` is in
`PercLib/Analysis/LaplaceUniqueness.lean`; nothing of it is repeated here. `import Mathlib`,
`autoImplicit` and disabled linters are removed.
-/
module

public import PercLib.Analysis.Tauberian.Converse
public import PercLib.Analysis.RegularVariation.Algebra
public import PercLib.Analysis.RegularVariation.GeneralInverse
public import Mathlib.MeasureTheory.Integral.Layercake

/-! # The non-strict tail in Theorem I.2.11

Theorem I.2.11 is printed for the tail `P(X ≥ x) = μ([x, ∞))`, while the Laplace–tail identity
and the Abelian direction in `PercLib.Analysis.Tauberian.Laplace` use the strict tail
`μ((x, ∞))`. This file shows that the two tail asymptotics are equivalent and transfers the
Abelian direction and the assembly of the two directions to the printed form.

## Main results

* `RegularlyVarying.tendsto_div`: `f (x / c) / f x → c ^ (-ρ)` for `f` of index `ρ`;
* `tendsto_measure_Ici_div_iff_Ioi`: for a finite measure `μ` and a regularly varying `g`,
  `μ([x,∞)) / g x → 1` if and only if `μ((x,∞)) / g x → 1`; the source form is
  `tendsto_tail_ge_iff_tail_gt`;
* `integral_one_sub_exp_eq_laplace_tail_ge`: `E_μ[1 - e^{-hX}] = h ∫_0^∞ e^{-hx} μ([x,∞)) dx`;
* `laplace_tail_asymptotic_of_tail_ge`: the Abelian direction of Theorem I.2.11 for the tail
  `μ([x,∞))`;
* `laplace_asymptotic_iff_tail_ge_of_strict_converse`,
  `tail_ge_asymptotic_of_antitone_converse`, `tail_ge_asymptotic_of_antitone_kernel_converse`:
  Theorem I.2.11 in the printed form, conditional on the strict-tail Tauberian direction,
  which is an explicit hypothesis `hconv`;
* `tendsto_kernel_form_iff`: the two forms `∫ e^{-u} F(u/h)` and `h ∫ e^{-hx} F(x)` of the
  Laplace hypothesis are equivalent.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.Analysis

/-! ### The endpoint limit `c ↑ 1` of `c ↦ c ^ β` -/

/-- For every real `β`, `c ↦ c ^ β` tends to `1` as `c` tends to `1` from below. -/
theorem tendsto_rpow_nhdsLT_one (β : ℝ) :
    Tendsto (fun c : ℝ => c ^ β) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  have h : Tendsto (fun c : ℝ => c ^ β) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) ^ β)) :=
    (Real.continuousAt_rpow_const 1 β (Or.inl one_ne_zero)).tendsto
  rw [Real.one_rpow] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Points of `(0, 1)` close to `1` satisfy every eventual property along `𝓝[<] 1`. -/
private theorem exists_mem_Ioo_of_eventually_nhdsLT_one {p : ℝ → Prop}
    (h : ∀ᶠ c in 𝓝[<] (1 : ℝ), p c) : ∃ c : ℝ, 0 < c ∧ c < 1 ∧ p c := by
  have h2 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), 0 < c :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ c : ℝ in 𝓝[<] (1 : ℝ), c < 1 := self_mem_nhdsWithin
  obtain ⟨c, hc1, hc2, hc3⟩ := (h.and (h2.and h3)).exists
  exact ⟨c, hc2, hc3, hc1⟩

/-- For `a < 1` and every real `β` there is `c ∈ (0,1)` with `a < c ^ β`. -/
theorem exists_lt_rpow_of_lt_one {a β : ℝ} (ha1 : a < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ a < c ^ β :=
  exists_mem_Ioo_of_eventually_nhdsLT_one
    ((tendsto_rpow_nhdsLT_one β).eventually (eventually_gt_nhds ha1))

/-- For `1 < b` and every real `β` there is `c ∈ (0,1)` with `c ^ β < b`. -/
theorem exists_rpow_lt_of_one_lt {b β : ℝ} (hb : 1 < b) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ c ^ β < b :=
  exists_mem_Ioo_of_eventually_nhdsLT_one
    ((tendsto_rpow_nhdsLT_one β).eventually (eventually_lt_nhds hb))

/-! ### Ratio limits and positivity -/

/-- **Ratio limit, quotient form.** If `f` is regularly varying of index `ρ` and `c > 0`, then
`f (x / c) / f x → c ^ (-ρ)`. -/
theorem RegularlyVarying.tendsto_div {f : ℝ → ℝ} {ρ c : ℝ} (hf : RegularlyVarying ρ f)
    (hc : 0 < c) : Tendsto (fun x : ℝ => f (x / c) / f x) atTop (𝓝 (c ^ (-ρ))) := by
  have h := hf.tendsto (inv_pos.2 hc)
  rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le] at h
  simpa only [inv_mul_eq_div] using h

/-- **The ratio hypothesis forces `f` to be eventually positive.** If
`g x / (f x / Γ(1-α)) → 1` with `g ≥ 0` and `α < 1`, then `f x > 0` eventually. -/
theorem eventually_pos_of_ratio_tendsto_one {f g : ℝ → ℝ} {α : ℝ}
    (hα1 : α < 1) (hg : ∀ x, 0 ≤ g x)
    (h : Tendsto (fun x => g x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1)) :
    ∀ᶠ x : ℝ in atTop, 0 < f x := by
  have hΓ : 0 < (Real.Gamma (1 - α))⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos (by linarith))
  refine eventually_pos_of_tendsto_div hΓ (Eventually.of_forall hg) ?_
  simpa only [div_eq_mul_inv, mul_comm (f _)] using h

/-- `f / Γ(1-α)` is regularly varying of index `-α` when `f` is and `α < 1`. -/
private theorem regularlyVarying_div_Gamma {f : ℝ → ℝ} {α : ℝ} (hα1 : α < 1)
    (hrv : RegularlyVarying (-α) f) :
    RegularlyVarying (-α) (fun x => f x / Real.Gamma (1 - α)) := by
  have hΓ : 0 < (Real.Gamma (1 - α))⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos (by linarith))
  have h := hrv.mul (slowlyVarying_iff_regularlyVarying_zero.1 (slowlyVarying_const hΓ))
  simpa only [add_zero, ← div_eq_mul_inv] using h

/-! ### The endpoint bridges for a finite measure -/

/-- **The non-strict tail asymptotic implies the strict one.** For a finite measure `μ` on `ℝ`
and `g` regularly varying, `μ([x,∞)) / g x → 1` implies `μ((x,∞)) / g x → 1`. The comparison is
`[x/c, ∞) ⊆ (x, ∞)` for `0 < c < 1`, then `c ↑ 1`; no atom hypothesis on `μ` is used. -/
theorem tendsto_measure_Ioi_div_of_Ici (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ → ℝ}
    {ρ : ℝ} (hg : RegularlyVarying ρ g)
    (htail : Tendsto (fun x => (μ (Ici x)).toReal / g x) atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Ioi x)).toReal / g x) atTop (𝓝 1) := by
  have hgpos := hg.eventually_pos
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨c, hc0, hc1, hca⟩ := exists_lt_rpow_of_lt_one (β := -ρ) ha
    have hxc : Tendsto (fun x : ℝ => x / c) atTop atTop :=
      tendsto_id.atTop_div_const hc0
    have hprod : Tendsto (fun x : ℝ => (μ (Ici (x / c))).toReal / g (x / c) * (g (x / c) / g x))
        atTop (𝓝 (c ^ (-ρ))) := by
      simpa only [one_mul, Function.comp_def] using (htail.comp hxc).mul (hg.tendsto_div hc0)
    filter_upwards [hprod.eventually (eventually_gt_nhds hca), hgpos, hxc.eventually hgpos,
      eventually_gt_atTop (0 : ℝ)] with x h1 hgx hgcx hx
    have hsub : Ici (x / c) ⊆ Ioi x := Ici_subset_Ioi.2 ((lt_div_iff₀ hc0).2 (by nlinarith))
    have hle : (μ (Ici (x / c))).toReal ≤ (μ (Ioi x)).toReal := measureReal_mono hsub
    calc a < (μ (Ici (x / c))).toReal / g (x / c) * (g (x / c) / g x) := h1
      _ = (μ (Ici (x / c))).toReal / g x := by field_simp
      _ ≤ (μ (Ioi x)).toReal / g x := div_le_div_of_nonneg_right hle hgx.le
  · filter_upwards [htail.eventually (eventually_lt_nhds hb), hgpos] with x h1 hgx
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (measureReal_mono Ioi_subset_Ici_self)
      hgx.le) h1

/-- **The strict tail asymptotic implies the non-strict one.** For a finite measure `μ` on `ℝ`
and `g` regularly varying, `μ((x,∞)) / g x → 1` implies `μ([x,∞)) / g x → 1`. The comparison is
`[x, ∞) ⊆ (c x, ∞)` for `0 < c < 1`, then `c ↑ 1`. -/
theorem tendsto_measure_Ici_div_of_Ioi (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ → ℝ}
    {ρ : ℝ} (hg : RegularlyVarying ρ g)
    (htail : Tendsto (fun x => (μ (Ioi x)).toReal / g x) atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Ici x)).toReal / g x) atTop (𝓝 1) := by
  have hgpos := hg.eventually_pos
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [htail.eventually (eventually_gt_nhds ha), hgpos] with x h1 hgx
    exact lt_of_lt_of_le h1 (div_le_div_of_nonneg_right (measureReal_mono Ioi_subset_Ici_self)
      hgx.le)
  · obtain ⟨c, hc0, hc1, hcb⟩ := exists_rpow_lt_of_one_lt (β := ρ) hb
    have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc0
    have hprod : Tendsto (fun x : ℝ => (μ (Ioi (c * x))).toReal / g (c * x) * (g (c * x) / g x))
        atTop (𝓝 (c ^ ρ)) := by
      simpa only [one_mul, Function.comp_def] using (htail.comp hcx).mul (hg.tendsto hc0)
    filter_upwards [hprod.eventually (eventually_lt_nhds hcb), hgpos, hcx.eventually hgpos,
      eventually_gt_atTop (0 : ℝ)] with x h1 hgx hgcx hx
    have hsub : Ici x ⊆ Ioi (c * x) := Ici_subset_Ioi.2 (by nlinarith)
    have hle : (μ (Ici x)).toReal ≤ (μ (Ioi (c * x))).toReal := measureReal_mono hsub
    calc (μ (Ici x)).toReal / g x ≤ (μ (Ioi (c * x))).toReal / g x :=
          div_le_div_of_nonneg_right hle hgx.le
      _ = (μ (Ioi (c * x))).toReal / g (c * x) * (g (c * x) / g x) := by field_simp
      _ < b := h1

/-- **The strict and non-strict tail asymptotics are equivalent** for a finite measure on `ℝ`
and a regularly varying comparison function. -/
theorem tendsto_measure_Ici_div_iff_Ioi (μ : Measure ℝ) [IsFiniteMeasure μ] {g : ℝ → ℝ}
    {ρ : ℝ} (hg : RegularlyVarying ρ g) :
    Tendsto (fun x => (μ (Ici x)).toReal / g x) atTop (𝓝 1) ↔
      Tendsto (fun x => (μ (Ioi x)).toReal / g x) atTop (𝓝 1) :=
  ⟨tendsto_measure_Ioi_div_of_Ici μ hg, tendsto_measure_Ici_div_of_Ioi μ hg⟩

/-! ### The endpoint bridges in the form of Theorem I.2.11 -/

/-- **The non-strict tail asymptotic implies the strict one**, in the normalisation of
Theorem I.2.11: if `μ([x,∞)) ~ f x / Γ(1-α)` then `μ((x,∞)) ~ f x / Γ(1-α)`. -/
theorem tendsto_tail_gt_of_tail_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {α : ℝ} (hα1 : α < 1) (hrv : RegularlyVarying (-α) f)
    (htail : Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Ioi x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  tendsto_measure_Ioi_div_of_Ici μ (regularlyVarying_div_Gamma hα1 hrv) htail

/-- **The strict tail asymptotic implies the non-strict one**, in the normalisation of
Theorem I.2.11: if `μ((x,∞)) ~ f x / Γ(1-α)` then `μ([x,∞)) ~ f x / Γ(1-α)`. -/
theorem tendsto_tail_ge_of_tail_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {α : ℝ} (hα1 : α < 1) (hrv : RegularlyVarying (-α) f)
    (htail : Tendsto (fun x => (μ (Ioi x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  tendsto_measure_Ici_div_of_Ioi μ (regularlyVarying_div_Gamma hα1 hrv) htail

/-- **The strict and non-strict tail asymptotics are equivalent**, in the normalisation of
Theorem I.2.11; so the strict-tail form of `PercLib.Analysis.Tauberian.Laplace` loses
nothing. -/
theorem tendsto_tail_ge_iff_tail_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} {α : ℝ} (hα1 : α < 1) (hrv : RegularlyVarying (-α) f) :
    Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) ↔
      Tendsto (fun x => (μ (Ioi x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  tendsto_measure_Ici_div_iff_Ioi μ (regularlyVarying_div_Gamma hα1 hrv)

/-! ### The Laplace–tail identity with the non-strict tail -/

/-- Integrals against the non-strict and the strict tail of a measure on `ℝ` agree: the two
tails differ only at the countably many atoms. -/
theorem setIntegral_mul_toReal_measure_Ici_eq_Ioi (μ : Measure ℝ) (w : ℝ → ℝ) (s : Set ℝ) :
    ∫ x in s, w x * (μ (Ici x)).toReal = ∫ x in s, w x * (μ (Ioi x)).toReal := by
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [meas_le_ae_eq_meas_lt μ volume (id : ℝ → ℝ)] with x hx
  change w x * (μ {a | x ≤ id a}).toReal = w x * (μ {a | x < id a}).toReal
  rw [hx]

/-- **The Laplace–tail identity, non-strict form.** For a probability measure `μ` on `ℝ`
carried by `[0,∞)` and `h > 0`, `E_μ[1 - e^{-hX}] = h ∫_0^∞ e^{-hx} μ([x,∞)) dx`. -/
theorem integral_one_sub_exp_eq_laplace_tail_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0) {h : ℝ} (hh : 0 < h) :
    ∫ s, (1 - Real.exp (-(h * s))) ∂μ
      = h * ∫ x in Ioi (0 : ℝ), Real.exp (-(h * x)) * (μ (Ici x)).toReal := by
  rw [setIntegral_mul_toReal_measure_Ici_eq_Ioi, integral_one_sub_exp_eq_laplace_tail μ hμ hh]

/-! ### Theorem I.2.11 for the tail event `P(X ≥ x)` -/

/-- **Theorem I.2.11, Abelian direction, for the tail event `P(X ≥ x)`.** Let `μ` be a
probability measure on `ℝ` carried by `[0,∞)` and `f` regularly varying of index `-α`,
`0 ≤ α < 1`. If `μ([x,∞)) ~ f x / Γ(1-α)` then `E_μ[1 - e^{-hX}] ~ f (1/h)` as `h ↓ 0`. -/
theorem laplace_tail_asymptotic_of_tail_ge
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVarying (-α) f)
    (htail : Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  laplace_tail_asymptotic_of_tail μ hμ hα0 hα1 hfmeas hrv
    (tendsto_tail_gt_of_tail_ge μ hα1 hrv htail)

/-- **Both directions of Theorem I.2.11 for the tail `P(X ≥ x)`, conditional on the
strict-tail Tauberian direction.** If Laplace asymptotics force `μ((x,∞)) ~ f x / Γ(1-α)` (the
explicit hypothesis `hconv`), then Laplace asymptotics are equivalent to
`μ([x,∞)) ~ f x / Γ(1-α)`. The forward direction does not use `hconv`. -/
theorem laplace_asymptotic_iff_tail_ge_of_strict_converse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hfmeas : Measurable f) (hrv : RegularlyVarying (-α) f)
    (hconv : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) →
      Tendsto (fun x => (μ (Ioi x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1)) :
    Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) ↔
      Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  ⟨laplace_tail_asymptotic_of_tail_ge μ hμ hα0 hα1 hfmeas hrv,
    fun hL => tendsto_tail_ge_of_tail_gt μ hα1 hrv (hconv hL)⟩

/-! ### The rescaled form of the Laplace hypothesis -/

/-- **Rescaling identity.** For `h > 0`, `h ∫_0^∞ e^{-hx} F x dx = ∫_0^∞ e^{-u} F (u/h) du`. -/
theorem integral_comp_laplace_rescale {F : ℝ → ℝ} {h : ℝ} (hh : 0 < h) :
    h * (∫ x in Ioi (0 : ℝ), Real.exp (-(h * x)) * F x)
      = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h) := by
  have hσ := integral_exp_sigma_mul_div F (h := 1) hh
  simp only [div_one, mul_one] at hσ
  rw [hσ, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]

/-- **The two forms of the Laplace hypothesis are equivalent**:
`(∫_0^∞ e^{-u} F (u/h) du) / f (1/h) → 1` iff `(h ∫_0^∞ e^{-hx} F x dx) / f (1/h) → 1` as
`h ↓ 0`. -/
theorem tendsto_kernel_form_iff {F f : ℝ → ℝ} :
    Tendsto (fun h : ℝ => (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun h : ℝ => (h * ∫ x in Ioi (0 : ℝ), Real.exp (-(h * x)) * F x) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine tendsto_congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [integral_comp_laplace_rescale hh]

/-! ### Lifting an antitone-function converse to the tail `P(X ≥ x)` -/

/-- **From an antitone-function Tauberian converse to the tail `P(X ≥ x)`.** If, for every
measurable antitone `F` with values in `[0,1]`, `(h ∫_0^∞ e^{-hx} F x dx) / f (1/h) → 1` implies
`F x ~ f x / Γ(1-α)` (the explicit hypothesis `hconv`), then `E_μ[1 - e^{-hX}] ~ f (1/h)`
implies `μ([x,∞)) ~ f x / Γ(1-α)` for every probability measure `μ` carried by `[0,∞)`. -/
theorem tail_ge_asymptotic_of_antitone_converse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα1 : α < 1) (hrv : RegularlyVarying (-α) f)
    (hconv : ∀ F : ℝ → ℝ, Measurable F → Antitone F → (∀ x, 0 ≤ F x) → (∀ x, F x ≤ 1) →
      Tendsto (fun h : ℝ => (h * ∫ x in Ioi (0 : ℝ), Real.exp (-(h * x)) * F x)
        / f (1 / h)) (𝓝[>] (0 : ℝ)) (𝓝 1) →
      Tendsto (fun x => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1))
    (hL : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) := by
  have hanti : Antitone fun x : ℝ => (μ (Ioi x)).toReal :=
    fun a b hab => measureReal_mono (Ioi_subset_Ioi hab)
  have hle_one : ∀ x : ℝ, (μ (Ioi x)).toReal ≤ 1 := fun x => measureReal_le_one
  have hstep : Tendsto (fun h : ℝ =>
      (h * ∫ x in Ioi (0 : ℝ), Real.exp (-(h * x)) * (μ (Ioi x)).toReal) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [integral_one_sub_exp_eq_laplace_tail μ hμ hh]
  exact tendsto_tail_ge_of_tail_gt μ hα1 hrv
    (hconv _ hanti.measurable hanti (fun _ => ENNReal.toReal_nonneg) hle_one hstep)

/-- **The same, with the converse in the kernel form** `(∫_0^∞ e^{-u} F (u/h) du) / f (1/h) → 1`
(convertible into the form of `tail_ge_asymptotic_of_antitone_converse` by
`tendsto_kernel_form_iff`). -/
theorem tail_ge_asymptotic_of_antitone_kernel_converse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {f : ℝ → ℝ} {α : ℝ} (hα1 : α < 1) (hrv : RegularlyVarying (-α) f)
    (hconv : ∀ F : ℝ → ℝ, Measurable F → Antitone F → (∀ x, 0 ≤ F x) → (∀ x, F x ≤ 1) →
      Tendsto (fun h : ℝ => (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) →
      Tendsto (fun x => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1))
    (hL : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  tail_ge_asymptotic_of_antitone_converse μ hμ hα1 hrv
    (fun F hFm hanti h0 h1 hk => hconv F hFm hanti h0 h1 (tendsto_kernel_form_iff.2 hk)) hL

/-! ### The power law `f x = x ^ (-α)` -/

/-- The endpoint equivalence for the power law `f x = x ^ (-α)`. -/
theorem tendsto_tail_ge_iff_tail_gt_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α : ℝ} (hα1 : α < 1) :
    Tendsto (fun x => (μ (Ici x)).toReal / (x ^ (-α) / Real.Gamma (1 - α))) atTop (𝓝 1) ↔
      Tendsto (fun x => (μ (Ioi x)).toReal / (x ^ (-α) / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  tendsto_tail_ge_iff_tail_gt μ hα1 (regularlyVarying_rpow (-α))

/-- The Abelian direction of Theorem I.2.11 for the tail `P(X ≥ x)` and the power law: if
`P(X ≥ x) ~ x ^ (-α) / Γ(1-α)` then `E[1 - e^{-hX}] ~ (1/h) ^ (-α)` as `h ↓ 0`. -/
theorem laplace_tail_asymptotic_of_tail_ge_rpow
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (htail : Tendsto (fun x => (μ (Ici x)).toReal / (x ^ (-α) / Real.Gamma (1 - α)))
      atTop (𝓝 1)) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / ((1 / h) ^ (-α)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  laplace_tail_asymptotic_of_tail_ge μ hμ hα0 hα1 (measurable_id.pow_const (-α))
    (regularlyVarying_rpow (-α)) htail

end PercLib.Analysis
