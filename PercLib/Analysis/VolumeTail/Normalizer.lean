/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The passage from the Laplace (MGF) asymptotic (I.3.2) to the volume-tail asymptotic (I.3.3) in
Proposition I.3.2 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, through Theorem I.2.11.

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, file
`PercLib/CriticalLRP/Analysis/VolumeTail.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop g ρ` becomes `RegularlyVarying ρ g` of
`PercLib/Analysis/RegularVariation/Defs.lean`, which includes eventual positivity, so the
normalizer lemma assumes `0 < A₃` in place of `A₃ ≠ 0`, while the tail theorem keeps `A₃ ≠ 0`
and derives the sign from the Laplace asymptotic; the hypotheses `Measurable g` and
`∀ᶠ x in atTop, 0 < g x` are removed (the second is part of `RegularlyVarying`, the first is
not needed by `laplace_asymptotic_iff_tail_ge`); the definition `normalizer` is written out and
`normalizer_inv` is dropped (one line of algebra, done inline); declarations are
renamed; `import Mathlib`, `autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.Tauberian.Complete
public import PercLib.Analysis.RegularVariation.KaramataPrimitive

/-! # From the Laplace asymptotic to the volume tail

Let `g` be regularly varying of index `1 / (a α)` with `a, α > 0`. The normalizer
`x ↦ A₃ (g x ^ α / x)` of Proposition I.3.2 is then regularly varying of index `1 / a - 1`,
so for `1 / a ≤ 1` Theorem I.2.11 (`laplace_asymptotic_iff_tail_ge`) converts the Laplace
asymptotic `E[1 - e^{-hX}] ~ A₃ h g(1/h)^α` into the tail asymptotic
`P(X ≥ x) ~ (A₃ / Γ(1/a)) g(x)^α / x`.

## Main results

* `RegularlyVarying.const_mul_rpow_div`: the index of the normalizer.
* `tendsto_measure_Ici_div_of_tendsto_laplace_div`: the tail conclusion (I.3.3) of
  Proposition I.3.2 from its Laplace asymptotic (I.3.2) and the regular variation of the
  inverse scale.

This is the Tauberian step of the proof of Proposition I.3.2, not that proposition.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-- **The normalizer of Proposition I.3.2 is regularly varying.** If `g` is regularly varying
of index `ρ`, then `x ↦ A (g x ^ α / x)` is regularly varying of index `ρ α - 1` for `A > 0`. -/
theorem RegularlyVarying.const_mul_rpow_div {g : ℝ → ℝ} {ρ α A : ℝ} (hA : 0 < A)
    (hg : RegularlyVarying ρ g) :
    RegularlyVarying (ρ * α - 1) (fun x => A * (g x ^ α / x)) :=
  ((hg.rpow hg.eventually_pos (a := α)).div_id).const_mul hA

/-- The normalizer `x ↦ A₃ (g x ^ α / x)` has index `1 / a - 1` when `g` has index
`1 / (a α)`. -/
theorem regularlyVarying_const_mul_rpow_div_of_regularlyVarying_one_div {g : ℝ → ℝ}
    {a α A₃ : ℝ} (ha : 0 < a) (hα : 0 < α) (hA₃ : 0 < A₃)
    (hg : RegularlyVarying (1 / (a * α)) g) :
    RegularlyVarying (1 / a - 1) (fun x => A₃ * (g x ^ α / x)) := by
  have h := hg.const_mul_rpow_div (α := α) hA₃
  rwa [show 1 / (a * α) * α - 1 = 1 / a - 1 by field_simp] at h

/-- **Tail conclusion (I.3.3) of Proposition I.3.2 from its Laplace asymptotic (I.3.2).** Let
`μ` be a probability law on `[0, ∞)`, `a, α > 0` with `1 / a ≤ 1`, and `g` regularly varying of
index `1 / (a α)`. If `A₃ ≠ 0` and `E_μ[1 - e^{-hX}] / (A₃ g(1/h)^α h) → 1` as `h ↓ 0`, then
`μ([x, ∞)) / ((A₃ / Γ(1/a)) g(x)^α / x) → 1` as `x → ∞`. The Laplace asymptotic forces
`A₃ > 0`. -/
theorem tendsto_measure_Ici_div_of_tendsto_laplace_div (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {a α A₃ : ℝ} (ha : 0 < a) (hα : 0 < α) (ha1 : 1 / a ≤ 1)
    {g : ℝ → ℝ} (hg : RegularlyVarying (1 / (a * α)) g) (hA₃ : A₃ ≠ 0)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / (A₃ * (g (1 / h) ^ α * h)))
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x : ℝ => (μ (Ici x)).toReal /
      ((A₃ / Real.Gamma (1 / a)) * (g x ^ α / x))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun h : ℝ => 1 / h) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  -- the Laplace asymptotic forces `A₃ > 0`
  have hA₃pos : 0 < A₃ := by
    rcases lt_or_gt_of_ne hA₃ with hneg | hpos
    · exfalso
      have hev : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
          (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / (A₃ * (g (1 / h) ^ α * h)) ≤ 0 := by
        filter_upwards [hinv.eventually hg.eventually_pos, self_mem_nhdsWithin] with h hg' hh
        have hh0 : 0 < h := hh
        refine div_nonpos_of_nonneg_of_nonpos ?_ ?_
        · have hsup : ∀ᵐ s ∂μ, 0 ≤ s :=
            ae_iff.2 (measure_mono_null (fun y hy => by simpa using hy) hμ)
          refine integral_nonneg_of_ae ?_
          filter_upwards [hsup] with s hs
          have : Real.exp (-(h * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
          exact sub_nonneg.2 this
        · exact (mul_neg_of_neg_of_pos hneg
            (mul_pos (Real.rpow_pos_of_pos hg' α) hh0)).le
      have hpos := hmain.eventually (eventually_gt_nhds zero_lt_one)
      obtain ⟨h, h1, h2⟩ := (hev.and hpos).exists
      exact lt_irrefl _ (lt_of_lt_of_le h2 h1)
    · exact hpos
  have hrv : RegularlyVarying (-(1 - 1 / a)) (fun x => A₃ * (g x ^ α / x)) := by
    have h := regularlyVarying_const_mul_rpow_div_of_regularlyVarying_one_div ha hα hA₃pos hg
    rwa [show 1 / a - 1 = -(1 - 1 / a) by ring] at h
  have h0 : 0 ≤ 1 - 1 / a := by linarith
  have h1 : 1 - 1 / a < 1 := by linarith [one_div_pos.mpr ha]
  have hmain' : Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) /
      (A₃ * (g (1 / h) ^ α / (1 / h)))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    refine hmain.congr' (Eventually.of_forall fun h => ?_)
    simp only [one_div, div_inv_eq_mul]
  have htail := (laplace_asymptotic_iff_tail_ge μ hμ h0 h1 hrv).1 hmain'
  rw [sub_sub_cancel] at htail
  refine htail.congr' (Eventually.of_forall fun x => ?_)
  rw [mul_div_right_comm]

end PercLib.Analysis
