/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The generalized inverse of a measurable regularly varying
function of positive index (Bingham–Goldie–Teugels, Theorem 1.5.12), the inverse/scale layer
of Proposition I.3.2, and Karamata integration on a positive tail, for T. Hutchcroft,
*Critical long-range percolation I*, arXiv:2508.18807v1.

Ported from the repository `yujinhkim/lrp`, branch
`critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/GeneralInverse.lean` (all of it except `genInv`, `genInv_def`,
which are in `PercLib/Analysis/RegularVariation/Defs.lean`) and
`PercLib/CriticalLRP/Analysis/KaramataTail.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f ρ` becomes `RegularlyVarying ρ f` of
`PercLib/Analysis/RegularVariation/Defs.lean`; the structure `RVPosData` is unbundled into the
hypotheses listed below and its constructors `RVPosData.of`, `RVPosData.of_moment` become
existence statements; `levelSet f x₀ y` is written out as `{x | x₀ ≤ x ∧ y ≤ f x}`;
`RVPosData.genInv` is `genInv f x₀`; `RVPosData.genInv_le` is `genInv_le` and
`RVPosData.le_genInv`, `RVPosData.genInv_mono` are `le_genInv`, `genInv_mono` of `Defs.lean`
(with `RegularlyVarying.levelSet_nonempty`); the two files are merged; `import Mathlib`,
`autoImplicit`, disabled linters and `#print` lines are removed.
-/
module

public import PercLib.Analysis.RegularVariation.UniformConvergence

/-! # The generalized inverse of a regularly varying function

## The unbundled form of `RVPosData`

The source bundles "regular variation data of positive index" in a structure `RVPosData f ρ`
(index `ρ > 0`, `f` measurable and regularly varying of index `ρ`, a threshold `x₀ ≥ 1` above
which `f` is positive and satisfies Potter's bounds with some `ε ∈ (0, min ρ (1/2)]`). Here it
is written out, and throughout this file (and in the packages that consume it) a threshold
`x₀` for `f` is described by the hypotheses

* `hρ : 0 < ρ`, `hmeas : Measurable f`, `hf : RegularlyVarying ρ f` (the function);
* `hx₀ : 0 < x₀` (the threshold is positive);
* `hpos : ∀ x, x₀ ≤ x → 0 < f x` (positivity above the threshold);
* `hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C` (local boundedness above the threshold).

Each lemma takes only those it uses. The source's Potter field is used for nothing but local
boundedness (`RVPosData.bddAbove_Icc`), and that is what `hbdd` states; Potter's bounds at the
threshold give it (`bddAbove_Icc_of_potter`). Such a threshold exists
(`RegularlyVarying.exists_threshold`, from `RegularlyVarying.exists_potter_threshold`, the
port of `RVPosData.nonempty`). Without `hbdd` the inverse can stay bounded: a measurable `f`
that blows up at a point above `x₀` has `genInv f x₀ y` below that point for every level.

## Main statements

* `RegularlyVarying.tendsto_atTop`: `f → ∞`.
* `RegularlyVarying.tendsto_genInv_atTop`: the inverse diverges.
* `RegularlyVarying.tendsto_comp_genInv`: `f (genInv f x₀ y) / y → 1`.
* `RegularlyVarying.regularlyVarying_genInv`: the inverse is regularly varying of index `1/ρ`.
* `prop_I_3_2_inverse_layer`: the inverse/scale layer of Proposition I.3.2.
* `tendsto_mul_one_sub_karamata_integral_tail`: Karamata integration on a tail.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

variable {f : ℝ → ℝ} {ρ x₀ : ℝ}

/-! ## Eventual positivity from the moment comparison -/

/-- **Eventual positivity of `f` from the moment asymptotics.** If `ψ ≥ 0`, `A₂ > 0` and
`ψ r / (A₂ * f r) → 1`, then `f` is eventually positive. -/
theorem eventually_pos_of_tendsto_div {ψ f : ℝ → ℝ} {A₂ : ℝ} (hA₂ : 0 < A₂)
    (hψ : ∀ᶠ r in atTop, 0 ≤ ψ r)
    (h : Tendsto (fun r => ψ r / (A₂ * f r)) atTop (𝓝 1)) : ∀ᶠ r in atTop, 0 < f r := by
  have h1 : ∀ᶠ r in atTop, 0 < ψ r / (A₂ * f r) :=
    h.eventually (eventually_gt_nhds zero_lt_one)
  filter_upwards [h1, hψ] with r hr hψr
  rcases div_pos_iff.1 hr with ⟨-, h2⟩ | ⟨h1', -⟩
  · by_contra hcon
    push Not at hcon
    exact absurd h2 (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hA₂.le hcon))
  · exact absurd h1' (not_lt.mpr hψr)

/-! ## A regularly varying function of positive index diverges -/

/-- **A measurable regularly varying function of positive index tends to `∞`.** No
monotonicity is used: the lower Potter bound gives `f x ≥ c x ^ (ρ - ε)` with `ρ - ε > 0`. -/
theorem RegularlyVarying.tendsto_atTop (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) : Tendsto f atTop atTop := by
  set e := ρ / 2 with he_def
  have he : 0 < e := by positivity
  obtain ⟨Xp, hXp1, hpot⟩ := potterBounds_of_regularlyVarying hmeas hf (min e (1 / 2))
    (lt_min he (by norm_num))
  obtain ⟨Xq, hXq⟩ := eventually_atTop.1 hf.eventually_pos
  set X := max Xp Xq with hX
  set ε := min e (1 / 2) with hε_def
  have hε0 : 0 < ε := lt_min he (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hερ : ε < ρ := lt_of_le_of_lt (min_le_left _ _) (by rw [he_def]; linarith)
  have hX1 : 1 ≤ X := le_trans hXp1 (le_max_left _ _)
  have hXpos : 0 < X := by linarith
  have hfX : 0 < f X := hXq X (le_max_right _ _)
  have hcoef : 0 < (1 - ε) * f X := mul_pos (by linarith) hfX
  have hlow : ∀ᶠ x : ℝ in atTop, (1 - ε) * f X * (x / X) ^ (ρ - ε) ≤ f x := by
    filter_upwards [eventually_ge_atTop X] with x hx
    have hp := (hpot x X (le_max_left _ _) hx).1
    rw [abs_of_pos hfX, abs_of_pos (hXq x (le_trans (le_max_right _ _) hx))] at hp
    linarith
  have hbase : Tendsto (fun x : ℝ => x / X) atTop atTop := tendsto_id.atTop_div_const hXpos
  have hrpow : Tendsto (fun x : ℝ => (x / X) ^ (ρ - ε)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < ρ - ε)).comp hbase
  exact tendsto_atTop_mono' atTop hlow (hrpow.const_mul_atTop hcoef)

/-! ## Thresholds -/

/-- **A uniform bound above the threshold** (the source's `RVPosData.bddAbove_Icc`): positivity
and Potter's upper bound above `x₀` bound `f` on every `[x₀, M]`. -/
theorem bddAbove_Icc_of_potter {ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hx₀ : 0 < x₀)
    (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hpot : ∀ x y : ℝ, x₀ ≤ y → y ≤ x →
      (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
        |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y|) (M : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, x₀ ≤ x → x ≤ M → f x ≤ C := by
  refine ⟨(1 + ε) * (max M x₀ / x₀) ^ (ρ + ε) * f x₀, fun x hx1 hx2 => ?_⟩
  have hp := (hpot x x₀ le_rfl hx1).2
  rw [abs_of_pos (hpos x hx1), abs_of_pos (hpos _ le_rfl)] at hp
  have hxM : x ≤ max M x₀ := le_trans hx2 (le_max_left _ _)
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx1
  have hmono : (x / x₀) ^ (ρ + ε) ≤ (max M x₀ / x₀) ^ (ρ + ε) :=
    Real.rpow_le_rpow (le_of_lt (div_pos hxpos hx₀))
      (by rw [div_le_div_iff_of_pos_right hx₀]; exact hxM) (by linarith)
  calc f x ≤ (1 + ε) * (x / x₀) ^ (ρ + ε) * f x₀ := hp
    _ ≤ (1 + ε) * (max M x₀ / x₀) ^ (ρ + ε) * f x₀ := by
        apply mul_le_mul_of_nonneg_right _ (hpos _ le_rfl).le
        exact mul_le_mul_of_nonneg_left hmono (by linarith)

/-- **Existence of the regular variation data** (the source's `RVPosData.nonempty`): for a
measurable regularly varying `f` of positive index there are a threshold `x₀ ≥ 1` and a Potter
exponent `ε ∈ (0, ρ)`, `ε ≤ 1/2`, such that `f` is positive above `x₀` and satisfies Potter's
bounds there. -/
theorem RegularlyVarying.exists_potter_threshold (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) :
    ∃ x₀ ε : ℝ, 1 ≤ x₀ ∧ (∀ x, x₀ ≤ x → 0 < f x) ∧ 0 < ε ∧ ε < ρ ∧ ε ≤ 1 / 2 ∧
      ∀ x y : ℝ, x₀ ≤ y → y ≤ x →
        (1 - ε) * (x / y) ^ (ρ - ε) * |f y| ≤ |f x| ∧
          |f x| ≤ (1 + ε) * (x / y) ^ (ρ + ε) * |f y| := by
  obtain ⟨e, he, heρ, heh⟩ : ∃ e : ℝ, 0 < e ∧ e < ρ ∧ e ≤ 1 / 2 :=
    ⟨min (ρ / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), min_le_right _ _⟩
  obtain ⟨Xp, hXp1, hpot⟩ := potterBounds_of_regularlyVarying hmeas hf e he
  obtain ⟨Xq, hXq⟩ := eventually_atTop.1 hf.eventually_pos
  refine ⟨max Xp Xq, e, le_trans hXp1 (le_max_left _ _),
    fun x hx => hXq x (le_trans (le_max_right _ _) hx), he, heρ, heh,
    fun x y hy hyx => hpot x y (le_trans (le_max_left _ _) hy) hyx⟩

/-- **Existence of a threshold** in the unbundled form used in this file: `x₀ ≥ 1`, `f` positive
above `x₀` and bounded on every `[x₀, M]` (the analogue of the source's `RVPosData.of`). -/
theorem RegularlyVarying.exists_threshold (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ (∀ x, x₀ ≤ x → 0 < f x) ∧
      ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C := by
  obtain ⟨x₀, ε, hx₀, hpos, hε, -, -, hpot⟩ := hf.exists_potter_threshold hρ hmeas
  exact ⟨x₀, hx₀, hpos, bddAbove_Icc_of_potter hρ hε (by linarith) hpos hpot⟩

/-! ## Level sets and the generalized inverse -/

/-- Level sets above a threshold are bounded below. -/
theorem bddBelow_levelSet (f : ℝ → ℝ) (x₀ y : ℝ) : BddBelow {x | x₀ ≤ x ∧ y ≤ f x} :=
  ⟨x₀, fun _ hx => hx.1⟩

/-- **Every level set is nonempty**: `f` diverges. -/
theorem RegularlyVarying.levelSet_nonempty (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (x₀ y : ℝ) : {x | x₀ ≤ x ∧ y ≤ f x}.Nonempty := by
  obtain ⟨X, hX⟩ := eventually_atTop.1
    ((hf.tendsto_atTop hρ hmeas).eventually (eventually_ge_atTop y))
  exact ⟨max X x₀, le_max_right _ _, hX _ (le_max_left _ _)⟩

/-- **The inverse is positive** for a positive threshold. -/
theorem RegularlyVarying.genInv_pos (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (y : ℝ) : 0 < genInv f x₀ y :=
  lt_of_lt_of_le hx₀ (le_genInv (hf.levelSet_nonempty hρ hmeas x₀ y))

/-- **Infimum approximation**: points of the level set come arbitrarily close to the inverse
from above. -/
theorem RegularlyVarying.exists_lt_genInv_add (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) {y ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, x₀ ≤ x ∧ y ≤ f x ∧ x < genInv f x₀ y + ε := by
  have hlt : genInv f x₀ y < genInv f x₀ y + ε := by linarith
  obtain ⟨x, hx⟩ := exists_lt_of_csInf_lt (hf.levelSet_nonempty hρ hmeas x₀ y) hlt
  exact ⟨x, hx.1.1, hx.1.2, hx.2⟩

/-- **The inverse is monotone** (all level sets are nonempty). -/
theorem RegularlyVarying.monotone_genInv (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) : Monotone (genInv f x₀) :=
  fun _ _ h => genInv_mono (hf.levelSet_nonempty hρ hmeas x₀ _) h

/-- **The inverse is measurable** (as a monotone function). -/
theorem RegularlyVarying.measurable_genInv (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) : Measurable (genInv f x₀) :=
  (hf.monotone_genInv hρ hmeas).measurable

/-- **The inverse diverges.** Above a level exceeding the bound of `f` on `[x₀, M]` every point
of the level set is larger than `M`. -/
theorem RegularlyVarying.tendsto_genInv_atTop (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) :
    Tendsto (genInv f x₀) atTop atTop := by
  refine Filter.tendsto_atTop.mpr fun M => ?_
  rcases le_or_gt M x₀ with hM | hM
  · exact Eventually.of_forall fun y =>
      le_trans hM (le_genInv (hf.levelSet_nonempty hρ hmeas x₀ y))
  obtain ⟨C, hC⟩ := hbdd M
  filter_upwards [eventually_gt_atTop C] with y hy
  refine le_csInf (hf.levelSet_nonempty hρ hmeas x₀ y) ?_
  intro x hx
  by_contra hcon
  push Not at hcon
  exact absurd (hC x hx.1 (le_of_lt hcon)) (not_le.mpr (lt_of_lt_of_le hy hx.2))

/-! ## The uniform ratio bound -/

/-- **The uniform convergence theorem** (BGT 1.2.1) in the two-sided form used below: on a
compact ratio range `[a,b] ⊂ (0,∞)`, `f (l x) / f x` is uniformly close to `l ^ ρ`, from a point
above the threshold on. -/
theorem RegularlyVarying.uniform_ratio (hmeas : Measurable f) (hf : RegularlyVarying ρ f)
    (hpos : ∀ x, x₀ ≤ x → 0 < f x) {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    ∃ Y : ℝ, x₀ ≤ Y ∧ ∀ x : ℝ, Y ≤ x → ∀ l ∈ Icc a b,
      |f (l * x)| ≤ (l ^ ρ + η) * |f x| ∧ (l ^ ρ - η) * |f x| ≤ |f (l * x)| := by
  obtain ⟨Y₀, -, hY₀⟩ := tendsto_uniformly_abs_ratio_of_regularlyVarying hmeas hf ha hab hη
  refine ⟨max Y₀ x₀, le_max_right _ _, fun x hx l hl => ?_⟩
  have hfx : 0 < f x := hpos x (le_trans (le_max_right _ _) hx)
  have h := hY₀ x (le_trans (le_max_left _ _) hx) l hl
  rw [abs_of_pos hfx] at h
  have h2 := abs_le.1 h
  rw [abs_of_pos hfx]
  constructor
  · have h3 : |f (l * x)| / f x ≤ l ^ ρ + η := by linarith [h2.2]
    exact (div_le_iff₀ hfx).1 h3
  · have h3 : l ^ ρ - η ≤ |f (l * x)| / f x := by linarith [h2.1]
    exact (le_div_iff₀ hfx).1 h3

/-! ## The asymptotic composition law `f (genInv y) ∼ y` -/

/-- **Upper half of the composition law**: `f (genInv f x₀ y) ≤ (1 + η) y` eventually. -/
theorem RegularlyVarying.eventually_comp_le (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y in atTop, f (genInv f x₀ y) ≤ (1 + η) * y := by
  have hg := hf.tendsto_genInv_atTop hρ hmeas hbdd
  -- a small `δ ∈ (0,1)` with `(1 - δ) ^ (-ρ) < 1 + η`
  obtain ⟨δ, hδ0, hδ1, hδratio⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ (1 - δ) ^ (-ρ) < 1 + η := by
    have hB : 0 < (1 + η / 2) ^ (1 / ρ) := Real.rpow_pos_of_pos (by linarith) _
    have hB1 : 1 < (1 + η / 2) ^ (1 / ρ) := Real.one_lt_rpow (by linarith) (by positivity)
    have hinv1 : ((1 + η / 2) ^ (1 / ρ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hB1
    have hinv0 : 0 < ((1 + η / 2) ^ (1 / ρ))⁻¹ := inv_pos.2 hB
    refine ⟨1 - ((1 + η / 2) ^ (1 / ρ))⁻¹, by linarith, by linarith, ?_⟩
    have h1 : (1 : ℝ) - (1 - ((1 + η / 2) ^ (1 / ρ))⁻¹) = ((1 + η / 2) ^ (1 / ρ))⁻¹ := by ring
    rw [h1, Real.inv_rpow hB.le, Real.rpow_neg hB.le, inv_inv,
      ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + η / 2), one_div_mul_cancel hρ.ne',
      Real.rpow_one]
    linarith
  set L := (1 - δ) ^ (-ρ) with hL
  have hLlt : L < 1 + η := hδratio
  have hbig : ∀ᶠ y in atTop, x₀ ≤ (1 - δ) * genInv f x₀ y := by
    filter_upwards [hg.eventually (eventually_ge_atTop (x₀ / (1 - δ)))] with y hy
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - δ)] at hy
    linarith
  have hbelow : ∀ᶠ y in atTop, f ((1 - δ) * genInv f x₀ y) < y := by
    filter_upwards [hbig] with y hy
    by_contra hcon
    push Not at hcon
    have h1 : genInv f x₀ y ≤ (1 - δ) * genInv f x₀ y := genInv_le hy hcon
    have h2 : 0 < genInv f x₀ y := hf.genInv_pos hρ hmeas hx₀ y
    nlinarith [mul_pos hδ0 h2]
  have hratio : Tendsto (fun y => f (genInv f x₀ y) / f ((1 - δ) * genInv f x₀ y)) atTop
      (𝓝 L) := by
    have hscale : Tendsto (fun y : ℝ => (1 - δ) * genInv f x₀ y) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (show (0:ℝ) < 1 - δ by linarith) hg
    have hinvpos : (0:ℝ) < (1 - δ)⁻¹ := by rw [inv_pos]; linarith
    have hcomp := (hf.tendsto hinvpos).comp hscale
    have hval : ((1 - δ)⁻¹) ^ ρ = L := by
      rw [hL, Real.inv_rpow (by linarith : (0:ℝ) ≤ 1 - δ),
        Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - δ)]
    rw [hval] at hcomp
    refine hcomp.congr' ?_
    filter_upwards with y
    change f ((1 - δ)⁻¹ * ((1 - δ) * genInv f x₀ y)) / f ((1 - δ) * genInv f x₀ y)
      = f (genInv f x₀ y) / f ((1 - δ) * genInv f x₀ y)
    rw [show (1 - δ)⁻¹ * ((1 - δ) * genInv f x₀ y) = genInv f x₀ y by
      field_simp [show (1 - δ) ≠ 0 by linarith]]
  filter_upwards [hbelow, hratio.eventually (eventually_lt_nhds hLlt), hbig,
    eventually_gt_atTop (0 : ℝ)] with y hbelow_y hratio_y hbig_y hypos
  have hfpos : 0 < f ((1 - δ) * genInv f x₀ y) := hpos _ hbig_y
  have h3 : f (genInv f x₀ y) / f ((1 - δ) * genInv f x₀ y) * f ((1 - δ) * genInv f x₀ y)
      = f (genInv f x₀ y) := div_mul_cancel₀ _ hfpos.ne'
  rw [← h3]
  exact mul_le_mul (le_of_lt hratio_y) (le_of_lt hbelow_y) hfpos.le (by linarith)

/-- **Lower half of the composition law**: `(1 - η) y ≤ f (genInv f x₀ y)` eventually. -/
theorem RegularlyVarying.eventually_le_comp (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ y in atTop, (1 - η) * y ≤ f (genInv f x₀ y) := by
  set ζ := η / (2 * (1 - η)) with hζ
  have hη1' : 0 < 1 - η := by linarith
  have hζ0 : 0 < ζ := by rw [hζ]; positivity
  have hkey : 1 + 2 * ζ = 1 / (1 - η) := by
    rw [hζ]; field_simp; ring
  obtain ⟨δ, hδ0, hδρ⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ ρ = 1 + ζ := by
    refine ⟨(1 + ζ) ^ (1 / ρ) - 1, ?_, ?_⟩
    · have h1 : 1 < (1 + ζ) ^ (1 / ρ) := Real.one_lt_rpow (by linarith) (by positivity)
      linarith
    · have h1 : (1 : ℝ) + ((1 + ζ) ^ (1 / ρ) - 1) = (1 + ζ) ^ (1 / ρ) := by ring
      rw [h1, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + ζ), one_div_mul_cancel hρ.ne',
        Real.rpow_one]
  obtain ⟨Y, -, hY⟩ := hf.uniform_ratio hmeas hpos (a := 1) (b := 1 + δ) one_pos
    (by linarith) hζ0
  filter_upwards [(hf.tendsto_genInv_atTop hρ hmeas hbdd).eventually (eventually_ge_atTop Y),
    eventually_gt_atTop (0 : ℝ)] with y hYle hypos
  have hthrle : x₀ ≤ genInv f x₀ y := le_genInv (hf.levelSet_nonempty hρ hmeas x₀ y)
  have hgpos : 0 < genInv f x₀ y := hf.genInv_pos hρ hmeas hx₀ y
  obtain ⟨x, hxthr, hxf, hxlt⟩ :=
    hf.exists_lt_genInv_add hρ hmeas (x₀ := x₀) (y := y) (ε := δ * genInv f x₀ y)
      (by positivity)
  have hxge : genInv f x₀ y ≤ x := genInv_le hxthr hxf
  have hl1 : 1 ≤ x / genInv f x₀ y := (le_div_iff₀ hgpos).2 (by linarith)
  have hl2 : x / genInv f x₀ y ≤ 1 + δ := by
    rw [div_le_iff₀ hgpos]
    linarith
  have hxeq : x / genInv f x₀ y * genInv f x₀ y = x := div_mul_cancel₀ _ hgpos.ne'
  have hbound := (hY (genInv f x₀ y) hYle (x / genInv f x₀ y) ⟨hl1, hl2⟩).1
  have hlr : (x / genInv f x₀ y) ^ ρ ≤ 1 + ζ := by
    calc (x / genInv f x₀ y) ^ ρ ≤ (1 + δ) ^ ρ :=
          Real.rpow_le_rpow (by linarith) hl2 (le_of_lt hρ)
      _ = 1 + ζ := hδρ
  have hxpos : 0 < f x := hpos x hxthr
  have hfg : 0 < f (genInv f x₀ y) := hpos _ hthrle
  have hfx : f x ≤ (1 + 2 * ζ) * f (genInv f x₀ y) := by
    rw [hxeq, abs_of_pos hxpos, abs_of_pos hfg] at hbound
    refine le_trans hbound ?_
    apply mul_le_mul_of_nonneg_right _ hfg.le
    linarith
  rw [hkey] at hfx
  have h1 : y ≤ (1 / (1 - η)) * f (genInv f x₀ y) := le_trans hxf hfx
  have h2 : (1 - η) * (1 / (1 - η)) = 1 := by field_simp
  calc (1 - η) * y ≤ (1 - η) * ((1 / (1 - η)) * f (genInv f x₀ y)) :=
        mul_le_mul_of_nonneg_left h1 hη1'.le
    _ = ((1 - η) * (1 / (1 - η))) * f (genInv f x₀ y) := by ring
    _ = f (genInv f x₀ y) := by rw [h2, one_mul]

/-- **The composition law `f (genInv f x₀ y) ∼ y`.** No exact inverse is asserted: `genInv` is
an asymptotic inverse. -/
theorem RegularlyVarying.tendsto_comp_genInv (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) :
    Tendsto (fun y => f (genInv f x₀ y) / y) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hη : 0 < min ((1 - b) / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hη1 : min ((1 - b) / 2) (1 / 2) < 1 :=
      lt_of_le_of_lt (min_le_right _ _) one_half_lt_one
    have hb2 : b < 1 - min ((1 - b) / 2) (1 / 2) := by
      rcases le_or_gt ((1 - b) / 2) (1 / 2) with hle | hgt
      · rw [min_eq_left hle]; linarith
      · rw [min_eq_right (le_of_lt hgt)]; linarith
    filter_upwards [hf.eventually_le_comp hρ hmeas hx₀ hpos hbdd hη hη1,
      eventually_gt_atTop (0 : ℝ)] with y h1 h2
    rw [lt_div_iff₀ h2]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hb2 h2) h1
  · have hη : 0 < (b - 1) / 2 := by linarith
    filter_upwards [hf.eventually_comp_le hρ hmeas hx₀ hpos hbdd hη,
      eventually_gt_atTop (0 : ℝ)] with y h1 h2
    rw [div_lt_iff₀ h2]
    exact lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right (by linarith) h2)

/-! ## Upper and lower comparability of the inverse at two levels -/

/-- **Upper comparability**: if `lam < M ^ ρ` then eventually
`genInv f x₀ (lam * y) ≤ M * genInv f x₀ y`. -/
theorem RegularlyVarying.eventually_genInv_mul_le (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {lam M : ℝ} (hlam : 0 < lam)
    (hM : 0 < M) (hMlam : lam < M ^ ρ) :
    ∀ᶠ y in atTop, genInv f x₀ (lam * y) ≤ M * genInv f x₀ y := by
  have hg := hf.tendsto_genInv_atTop hρ hmeas hbdd
  obtain ⟨L, hL1, hL2⟩ : ∃ L : ℝ, lam < L ∧ L < M ^ ρ :=
    ⟨(lam + M ^ ρ) / 2, by linarith, by linarith⟩
  have hLpos : 0 < L := lt_trans hlam hL1
  have hθ : 0 < (L - lam) / (2 * L) := by
    have : 0 < L - lam := by linarith
    positivity
  have hθ1 : (L - lam) / (2 * L) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hθkey : lam < L * (1 - (L - lam) / (2 * L)) := by
    have h4 : L * (1 - (L - lam) / (2 * L)) = (L + lam) / 2 := by
      field_simp; ring
    rw [h4]; linarith
  have hfy : ∀ᶠ y in atTop, lam * y < L * f (genInv f x₀ y) := by
    filter_upwards [hf.eventually_le_comp hρ hmeas hx₀ hpos hbdd hθ hθ1,
      eventually_gt_atTop (0 : ℝ)] with y hy hypos
    have h1 : lam * y < (L * (1 - (L - lam) / (2 * L))) * y :=
      mul_lt_mul_of_pos_right hθkey hypos
    have h2 : L * ((1 - (L - lam) / (2 * L)) * y) ≤ L * f (genInv f x₀ y) :=
      mul_le_mul_of_nonneg_left hy hLpos.le
    nlinarith
  have hratio : ∀ᶠ y in atTop, L < f (M * genInv f x₀ y) / f (genInv f x₀ y) :=
    ((hf.tendsto hM).comp hg).eventually (eventually_gt_nhds hL2)
  have hthr : ∀ᶠ y in atTop, x₀ ≤ M * genInv f x₀ y := by
    filter_upwards [hg.eventually (eventually_ge_atTop (x₀ / M))] with y hy
    rw [div_le_iff₀ hM] at hy
    linarith
  filter_upwards [hfy, hratio, hthr] with y hfy' hratio' hthr'
  refine genInv_le hthr' ?_
  have hfpos : 0 < f (genInv f x₀ y) := hpos _ (le_genInv (hf.levelSet_nonempty hρ hmeas x₀ y))
  have h2 : L * f (genInv f x₀ y) < f (M * genInv f x₀ y) := by
    rw [lt_div_iff₀ hfpos] at hratio'
    linarith
  linarith

/-- **Lower comparability**: if `m ^ ρ < lam` then eventually
`m * genInv f x₀ y ≤ genInv f x₀ (lam * y)`. -/
theorem RegularlyVarying.eventually_mul_genInv_le (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {lam m : ℝ} (hlam : 0 < lam)
    (hm : 0 < m) (hmlam : m ^ ρ < lam) :
    ∀ᶠ y in atTop, m * genInv f x₀ y ≤ genInv f x₀ (lam * y) := by
  have h1 : (0:ℝ) < 1 / lam := by positivity
  have h2 : (0:ℝ) < 1 / m := by positivity
  have h3 : 1 / lam < (1 / m) ^ ρ := by
    rw [one_div, one_div, Real.inv_rpow (le_of_lt hm),
      inv_lt_inv₀ hlam (Real.rpow_pos_of_pos hm ρ)]
    exact hmlam
  have h := hf.eventually_genInv_mul_le hρ hmeas hx₀ hpos hbdd h1 h2 h3
  have hscale : Tendsto (fun y : ℝ => lam * y) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hlam).2 tendsto_id
  filter_upwards [hscale.eventually h] with y hy
  rw [show 1 / lam * (lam * y) = y by field_simp] at hy
  calc m * genInv f x₀ y ≤ m * (1 / m * genInv f x₀ (lam * y)) :=
        mul_le_mul_of_nonneg_left hy hm.le
    _ = genInv f x₀ (lam * y) := by field_simp

/-! ## `genInv` is regularly varying of index `1 / ρ` -/

/-- **The inverse ratio law**: `genInv f x₀ (lam * y) / genInv f x₀ y → lam ^ (1 / ρ)`. -/
theorem RegularlyVarying.tendsto_genInv_ratio (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun y => genInv f x₀ (lam * y) / genInv f x₀ y) atTop (𝓝 (lam ^ (1 / ρ))) := by
  have hgp := hf.genInv_pos hρ hmeas hx₀
  set c := lam ^ (1 / ρ) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hlam _
  have hcpow : c ^ ρ = lam := by
    rw [hc, ← Real.rpow_mul hlam.le, one_div_mul_cancel hρ.ne', Real.rpow_one]
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · set m := max ((b + c) / 2) (c / 2) with hm
    have hmpos : 0 < m := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hbm : b < m := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hmc : m < c := max_lt (by linarith) (by linarith)
    have hmpow : m ^ ρ < lam := by
      rw [← hcpow]
      exact Real.rpow_lt_rpow (le_of_lt hmpos) hmc hρ
    filter_upwards [hf.eventually_mul_genInv_le hρ hmeas hx₀ hpos hbdd hlam hmpos hmpow]
      with y h1
    rw [lt_div_iff₀ (hgp y)]
    have h3 : b * genInv f x₀ y < m * genInv f x₀ y := mul_lt_mul_of_pos_right hbm (hgp y)
    linarith
  · obtain ⟨M, hcM, hMb⟩ : ∃ M : ℝ, c < M ∧ M < b := ⟨(c + b) / 2, by linarith, by linarith⟩
    have hMpos : 0 < M := lt_trans hcpos hcM
    have hMpow : lam < M ^ ρ := by
      rw [← hcpow]
      exact Real.rpow_lt_rpow (le_of_lt hcpos) hcM hρ
    filter_upwards [hf.eventually_genInv_mul_le hρ hmeas hx₀ hpos hbdd hlam hMpos hMpow]
      with y h1
    rw [div_lt_iff₀ (hgp y)]
    have h3 : M * genInv f x₀ y < b * genInv f x₀ y := mul_lt_mul_of_pos_right hMb (hgp y)
    linarith

/-- **The generalized inverse is regularly varying of index `1 / ρ`** (BGT Theorem 1.5.12, for
measurable `f` of positive index; no monotonicity or continuity of `f` is used). -/
theorem RegularlyVarying.regularlyVarying_genInv (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) :
    RegularlyVarying (1 / ρ) (genInv f x₀) :=
  ⟨⟨0, measurable_restrict_Ici_of_measurable (hf.measurable_genInv hρ hmeas) 0⟩,
    Eventually.of_forall fun y => hf.genInv_pos hρ hmeas hx₀ y,
    fun _ hl => hf.tendsto_genInv_ratio hρ hmeas hx₀ hpos hbdd hl⟩

/-- **Assembly interface for the volume-tail step**: the generalized inverse is measurable,
eventually positive, and regularly varying of index `1 / (a α)` when `ρ = a α`. -/
theorem RegularlyVarying.genInv_volumeTail_data (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {a α : ℝ} (hρα : ρ = a * α) :
    Measurable (genInv f x₀) ∧ (∀ᶠ x in atTop, 0 < genInv f x₀ x) ∧
      RegularlyVarying (1 / (a * α)) (genInv f x₀) := by
  refine ⟨hf.measurable_genInv hρ hmeas,
    Eventually.of_forall fun x => hf.genInv_pos hρ hmeas hx₀ x, ?_⟩
  rw [← hρα]
  exact hf.regularlyVarying_genInv hρ hmeas hx₀ hpos hbdd

/-- **The power form of the level ratio law**:
`(genInv f x₀ (lam y)) ^ α / (genInv f x₀ y) ^ α → lam ^ (α / ρ)`. -/
theorem RegularlyVarying.tendsto_genInv_rpow_ratio (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) :
    Tendsto (fun y => (genInv f x₀ (lam * y)) ^ α / (genInv f x₀ y) ^ α) atTop
      (𝓝 (lam ^ (α / ρ))) := by
  have hbase := hf.tendsto_genInv_ratio hρ hmeas hx₀ hpos hbdd hlam
  have hval : (lam ^ (1 / ρ)) ^ α = lam ^ (α / ρ) := by
    rw [← Real.rpow_mul hlam.le]
    ring_nf
  have hcont : Tendsto (fun t : ℝ => t ^ α) (𝓝 (lam ^ (1 / ρ))) (𝓝 (lam ^ (α / ρ))) := by
    have h := (Real.continuousAt_rpow_const (lam ^ (1 / ρ)) α (Or.inr hα.le)).tendsto
    rwa [hval] at h
  refine (hcont.comp hbase).congr' ?_
  filter_upwards with y
  change (genInv f x₀ (lam * y) / genInv f x₀ y) ^ α
    = (genInv f x₀ (lam * y)) ^ α / (genInv f x₀ y) ^ α
  rw [Real.div_rpow (hf.genInv_pos hρ hmeas hx₀ _).le (hf.genInv_pos hρ hmeas hx₀ _).le]

/-- **Level selections with a bounded ratio obey the same law.** If `v → ∞`, `u / v` is
eventually in a compact `[a,b] ⊂ (0,∞)` and `f (u h) / f (v h) → c > 0`, then
`u h / v h → c ^ (1/ρ)`. -/
theorem RegularlyVarying.tendsto_div_of_bounded_ratio (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x) {ι : Type*}
    {l : Filter ι} {u v : ι → ℝ} {c a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hmem : ∀ᶠ h in l, u h / v h ∈ Icc a b) (hv : Tendsto v l atTop)
    (hratio : Tendsto (fun h => f (u h) / f (v h)) l (𝓝 c)) (hc : 0 < c) :
    Tendsto (fun h => u h / v h) l (𝓝 (c ^ (1 / ρ))) := by
  have hpow : Tendsto (fun h => (u h / v h) ^ ρ) l (𝓝 c) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Y, -, hY⟩ := hf.uniform_ratio hmeas hpos (a := a) (b := b) ha hab
      (by linarith : 0 < ε / 2)
    have hev1 : ∀ᶠ h in l, Y ≤ v h := hv.eventually (eventually_ge_atTop Y)
    have hev2 : ∀ᶠ h in l, x₀ ≤ v h := hv.eventually (eventually_ge_atTop x₀)
    have hev3 : ∀ᶠ h in l, f (u h) / f (v h) ∈ Ioo (c - ε / 2) (c + ε / 2) :=
      hratio.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have hev4 : ∀ᶠ h in l, 0 < f (u h) / f (v h) :=
      hratio.eventually (eventually_gt_nhds hc)
    filter_upwards [hmem, hev1, hev2, hev3, hev4] with h hmem' hYle hthr hrat hratpos
    have hvpos : 0 < f (v h) := hpos _ hthr
    have hv0 : v h ≠ 0 := (lt_of_lt_of_le hx₀ hthr).ne'
    have huval : (u h / v h) * v h = u h := div_mul_cancel₀ _ hv0
    have hfu : 0 < f (u h) := by
      have := mul_pos hratpos hvpos
      rwa [div_mul_cancel₀ _ hvpos.ne'] at this
    obtain ⟨hb1, hb2⟩ := hY (v h) hYle (u h / v h) hmem'
    rw [huval, abs_of_pos hfu, abs_of_pos hvpos] at hb1 hb2
    have hi1 : f (u h) / f (v h) ≤ (u h / v h) ^ ρ + ε / 2 := by
      rw [div_le_iff₀ hvpos]; linarith
    have hi2 : (u h / v h) ^ ρ - ε / 2 ≤ f (u h) / f (v h) := by
      rw [le_div_iff₀ hvpos]; linarith
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hrat.1, hrat.2]
  have hcont : Tendsto (fun t : ℝ => t ^ (1 / ρ)) (𝓝 c) (𝓝 (c ^ (1 / ρ))) :=
    (Real.continuousAt_rpow_const c (1 / ρ) (Or.inl hc.ne')).tendsto
  refine (hcont.comp hpow).congr' ?_
  filter_upwards [hmem] with h hhmem
  have hlpos : 0 < u h / v h := lt_of_lt_of_le ha hhmem.1
  change ((u h / v h) ^ ρ) ^ (1 / ρ) = u h / v h
  rw [← Real.rpow_mul (le_of_lt hlpos), mul_one_div_cancel hρ.ne', Real.rpow_one]

/-! ## The level laws in the intensity variable `h ↓ 0⁺` -/

/-- **Level ratio law in the intensity variable**:
`genInv f x₀ (λ / h) / genInv f x₀ (1 / h) → λ ^ (1 / ρ)` as `h ↓ 0⁺`. -/
theorem RegularlyVarying.tendsto_genInv_levelRatio (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => genInv f x₀ (lam / h) / genInv f x₀ (1 / h)) (𝓝[>] 0)
      (𝓝 (lam ^ (1 / ρ))) := by
  refine ((hf.tendsto_genInv_ratio hρ hmeas hx₀ hpos hbdd hlam).comp
    tendsto_inv_nhdsGT_zero).congr' ?_
  filter_upwards with h
  change genInv f x₀ (lam * h⁻¹) / genInv f x₀ h⁻¹ = genInv f x₀ (lam / h) / genInv f x₀ (1 / h)
  rw [← div_eq_mul_inv, one_div]

/-- The level argument `λ / (A₂ h)` tends to `∞` as `h ↓ 0⁺`. -/
theorem tendsto_level_arg {A₂ lam : ℝ} (hA₂ : 0 < A₂) (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => lam / (A₂ * h)) (𝓝[>] 0) atTop := by
  have hA : 0 < lam / A₂ := div_pos hlam hA₂
  have h1 : Tendsto (fun h : ℝ => (lam / A₂) * h⁻¹) (𝓝[>] (0:ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos hA).2 tendsto_inv_nhdsGT_zero
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hA₂0 : A₂ ≠ 0 := hA₂.ne'
  field_simp

/-- **The level is filled**: with the cutoff `r h = genInv f x₀ (λ / (A₂ h))`,
`h · (A₂ · f (r h)) → λ`. -/
theorem RegularlyVarying.tendsto_level_filled (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {A₂ lam : ℝ} (hA₂ : 0 < A₂)
    (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => h * (A₂ * f (genInv f x₀ (lam / (A₂ * h))))) (𝓝[>] 0)
      (𝓝 lam) := by
  have hcomp := (hf.tendsto_comp_genInv hρ hmeas hx₀ hpos hbdd).comp (tendsto_level_arg hA₂ hlam)
  have h2 : Tendsto (fun h : ℝ =>
      lam * (f (genInv f x₀ (lam / (A₂ * h))) / (lam / (A₂ * h)))) (𝓝[>] (0:ℝ))
      (𝓝 (lam * 1)) := hcomp.const_mul lam
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hA₂0 : A₂ ≠ 0 := hA₂.ne'
  have hlam0 : lam ≠ 0 := hlam.ne'
  field_simp

/-- **The level is filled for the moment function itself**: if `ψ r / f r → A₂` then with the
cutoff `r h = genInv f x₀ (λ / (A₂ h))`, `h · ψ (r h) → λ`. -/
theorem RegularlyVarying.tendsto_level_filled_of_tendsto_div (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {ψ : ℝ → ℝ} {A₂ lam : ℝ} (hA₂ : 0 < A₂)
    (hlam : 0 < lam) (hψ : Tendsto (fun r => ψ r / f r) atTop (𝓝 A₂)) :
    Tendsto (fun h : ℝ => h * ψ (genInv f x₀ (lam / (A₂ * h)))) (𝓝[>] 0) (𝓝 lam) := by
  have hfne : ∀ h : ℝ, f (genInv f x₀ (lam / (A₂ * h))) ≠ 0 := fun h =>
    (hpos _ (le_genInv (hf.levelSet_nonempty hρ hmeas x₀ _))).ne'
  have hfilled := hf.tendsto_level_filled hρ hmeas hx₀ hpos hbdd hA₂ hlam
  have harg : Tendsto (fun h : ℝ => genInv f x₀ (lam / (A₂ * h))) (𝓝[>] 0) atTop :=
    (hf.tendsto_genInv_atTop hρ hmeas hbdd).comp (tendsto_level_arg hA₂ hlam)
  have hratio : Tendsto (fun h : ℝ =>
      ψ (genInv f x₀ (lam / (A₂ * h))) / (A₂ * f (genInv f x₀ (lam / (A₂ * h)))))
      (𝓝[>] 0) (𝓝 1) := by
    have h2 : Tendsto (fun h : ℝ =>
        ψ (genInv f x₀ (lam / (A₂ * h))) / f (genInv f x₀ (lam / (A₂ * h))) / A₂)
        (𝓝[>] 0) (𝓝 (A₂ / A₂)) := (hψ.comp harg).div_const A₂
    rw [div_self hA₂.ne'] at h2
    refine h2.congr' (Eventually.of_forall fun h => ?_)
    change ψ (genInv f x₀ (lam / (A₂ * h))) / f (genInv f x₀ (lam / (A₂ * h))) / A₂
      = ψ (genInv f x₀ (lam / (A₂ * h))) / (A₂ * f (genInv f x₀ (lam / (A₂ * h))))
    rw [div_div, mul_comm (f _)]
  have hprod := hfilled.mul hratio
  rw [mul_one] at hprod
  refine hprod.congr' (Eventually.of_forall fun h => ?_)
  have hzero : A₂ * f (genInv f x₀ (lam / (A₂ * h))) ≠ 0 := mul_ne_zero hA₂.ne' (hfne h)
  change (h * (A₂ * f (genInv f x₀ (lam / (A₂ * h))))) *
        (ψ (genInv f x₀ (lam / (A₂ * h))) / (A₂ * f (genInv f x₀ (lam / (A₂ * h)))))
      = h * ψ (genInv f x₀ (lam / (A₂ * h)))
  rw [mul_assoc, mul_div_cancel₀ _ hzero]

/-- **The Proposition I.3.2 normalising ratio**: with `r h = genInv f x₀ (λ / (A₂ h))`,
`τ h = genInv f x₀ (1 / h)` and `ρ = a α`, `(r h) ^ α / (τ h) ^ α → (λ / A₂) ^ (1 / a)` as
`h ↓ 0⁺`. -/
theorem RegularlyVarying.tendsto_level_normalization (hρ : 0 < ρ) (hmeas : Measurable f)
    (hf : RegularlyVarying ρ f) (hx₀ : 0 < x₀) (hpos : ∀ x, x₀ ≤ x → 0 < f x)
    (hbdd : ∀ M, ∃ C, ∀ x, x₀ ≤ x → x ≤ M → f x ≤ C) {a α A₂ lam : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hρα : ρ = a * α) (hA₂ : 0 < A₂) (hlam : 0 < lam) :
    Tendsto (fun h : ℝ => (genInv f x₀ (lam / (A₂ * h))) ^ α / (genInv f x₀ (1 / h)) ^ α)
      (𝓝[>] 0) (𝓝 ((lam / A₂) ^ (1 / a))) := by
  have hA : 0 < lam / A₂ := div_pos hlam hA₂
  have hbase : Tendsto (fun h : ℝ => genInv f x₀ (lam / (A₂ * h)) / genInv f x₀ (1 / h))
      (𝓝[>] 0) (𝓝 ((lam / A₂) ^ (1 / ρ))) := by
    refine (hf.tendsto_genInv_levelRatio hρ hmeas hx₀ hpos hbdd hA).congr' ?_
    filter_upwards with h
    rw [div_div]
  have hcont : Tendsto (fun t : ℝ => t ^ α) (𝓝 ((lam / A₂) ^ (1 / ρ)))
      (𝓝 (((lam / A₂) ^ (1 / ρ)) ^ α)) :=
    (Real.continuousAt_rpow_const _ α (Or.inr hα.le)).tendsto
  have hexp : (1 / ρ) * α = 1 / a := by
    rw [hρα]
    field_simp
  rw [← Real.rpow_mul hA.le, hexp] at hcont
  refine (hcont.comp hbase).congr' (Eventually.of_forall fun h => ?_)
  change (genInv f x₀ (lam / (A₂ * h)) / genInv f x₀ (1 / h)) ^ α
    = (genInv f x₀ (lam / (A₂ * h))) ^ α / (genInv f x₀ (1 / h)) ^ α
  rw [Real.div_rpow (hf.genInv_pos hρ hmeas hx₀ _).le (hf.genInv_pos hρ hmeas hx₀ _).le]

/-- **Proposition I.3.2, inverse/scale layer, end to end.** Let `f` be measurable and regularly
varying of index `a α` (`a, α > 0`), with no monotonicity or continuity, and let `ψ` satisfy
`ψ r / (A₂ f r) → 1` with `A₂ > 0`. Then there is a threshold `x₀ ≥ 1` such that the
generalized inverse `g = genInv f x₀` provides the cutoff `r h = g (λ / (A₂ h))` with
`h · ψ (r h) → λ` and `(r h) ^ α / (g (1 / h)) ^ α → (λ / A₂) ^ (1 / a)`, and `g` is
measurable, eventually positive and regularly varying of index `1/(a α)`. -/
theorem prop_I_3_2_inverse_layer {f ψ : ℝ → ℝ} {a α A₂ lam : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hmeas : Measurable f)
    (hrv : RegularlyVarying (a * α) f) (hA₂ : 0 < A₂)
    (hψ2 : Tendsto (fun r => ψ r / (A₂ * f r)) atTop (𝓝 1)) (hlam : 0 < lam) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧
      (Measurable (genInv f x₀) ∧ (∀ᶠ x in atTop, 0 < genInv f x₀ x) ∧
        RegularlyVarying (1 / (a * α)) (genInv f x₀)) ∧
      Tendsto (fun h : ℝ => h * ψ (genInv f x₀ (lam / (A₂ * h)))) (𝓝[>] 0) (𝓝 lam) ∧
      Tendsto (fun h : ℝ => (genInv f x₀ (lam / (A₂ * h))) ^ α / (genInv f x₀ (1 / h)) ^ α)
        (𝓝[>] 0) (𝓝 ((lam / A₂) ^ (1 / a))) := by
  have hρ : 0 < a * α := mul_pos ha hα
  obtain ⟨x₀, hx₀1, hpos, hbdd⟩ := hrv.exists_threshold hρ hmeas
  have hx₀ : 0 < x₀ := by linarith
  have hψdiv : Tendsto (fun r => ψ r / f r) atTop (𝓝 A₂) := by
    have h := hψ2.const_mul A₂
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hrv.eventually_pos] with r hfr
    field_simp
  exact ⟨x₀, hx₀1, hrv.genInv_volumeTail_data hρ hmeas hx₀ hpos hbdd rfl,
    hrv.tendsto_level_filled_of_tendsto_div hρ hmeas hx₀ hpos hbdd hA₂ hlam hψdiv,
    hrv.tendsto_level_normalization hρ hmeas hx₀ hpos hbdd ha hα rfl hA₂ hlam⟩

/-! ## Karamata integration on a positive tail (source `KaramataTail.lean`) -/

/-- A zero extension of a function integrable on all intervals to the right of a cut is
interval integrable. -/
theorem intervalIntegrable_indicator_Ioi_of_intervalIntegrable {g : ℝ → ℝ} {r₀ : ℝ}
    (h : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntegrableOn g (Ioc x y) volume)
    (a b : ℝ) : IntervalIntegrable ((Ioi r₀).indicator g) volume a b := by
  have fragment : ∀ a b : ℝ, IntegrableOn ((Ioi r₀).indicator g) (Ioc a b) volume := by
    intro a b
    have hset : Ioc a b ∩ Ioi r₀ = Ioc (max a r₀) b := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨hax, hxb⟩, hr₀x⟩
        exact ⟨max_lt hax hr₀x, hxb⟩
      · rintro ⟨hx, hxb⟩
        exact ⟨⟨(le_max_left _ _).trans_lt hx, hxb⟩, (le_max_right _ _).trans_lt hx⟩
    have hg : IntegrableOn ((Ioi r₀).indicator g) (Ioc a b ∩ Ioi r₀) volume := by
      rw [hset]
      by_cases hb : max a r₀ ≤ b
      · have hi := h (max a r₀) b (le_max_right _ _) hb
        exact (integrableOn_congr_fun (fun x hx => Set.indicator_of_mem
          (Set.mem_Ioi.2 ((le_max_right _ _).trans_lt hx.1)) g) measurableSet_Ioc).mpr hi
      · have hempty : Ioc (max a r₀) b = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          exact hb (le_trans hx.1.le hx.2)
        rw [hempty]
        exact integrableOn_empty
    have hzero : IntegrableOn ((Ioi r₀).indicator g) (Ioc a b ∩ (Ioi r₀)ᶜ) volume := by
      apply (integrableOn_congr_fun (f := fun _ : ℝ => (0 : ℝ)) ?_
        (measurableSet_Ioc.inter measurableSet_Ioi.compl)).mp integrableOn_zero
      intro x hx
      simp only [Set.indicator_of_notMem (fun hmem => hx.2 (Set.mem_Ioi.1 hmem)) g]
    rw [show Ioc a b = (Ioc a b ∩ Ioi r₀) ∪ (Ioc a b ∩ (Ioi r₀)ᶜ) from
      (inter_union_compl _ _).symm]
    exact hg.union hzero
  exact ⟨fragment a b, fragment b a⟩

/-- The zero extension is locally integrable on the positive axis. -/
theorem locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable {g : ℝ → ℝ} {r₀ : ℝ}
    (h : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y) :
    LocallyIntegrableOn ((Ioi r₀).indicator g) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isLocallyClosed_Ioi]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hKn
  · exact integrableOn_empty
  obtain ⟨m, hm⟩ := hKc.bddBelow
  obtain ⟨M, hM⟩ := hKc.bddAbove
  obtain ⟨x, hx⟩ := hKn
  have hmM : m ≤ M := le_trans (hm hx) (hM hx)
  have hsub : K ⊆ Icc m M := fun y hy => ⟨hm hy, hM hy⟩
  have hInt : IntegrableOn ((Ioi r₀).indicator g) (Icc m M) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hmM (by simp)).1
      (intervalIntegrable_indicator_Ioi_of_intervalIntegrable
        (fun x y hx hxy => (h x y hx hxy).1) m M)
  exact hInt.mono_set hsub

/-- Regular variation is unchanged by zero-extension below a fixed cut. -/
theorem regularlyVarying_indicator_Ioi {g : ℝ → ℝ} {r₀ ρ : ℝ}
    (hrv : RegularlyVarying ρ g) : RegularlyVarying ρ ((Ioi r₀).indicator g) :=
  hrv.congr' (by
    filter_upwards [eventually_gt_atTop r₀] with x hx
    rw [Set.indicator_of_mem (Set.mem_Ioi.2 hx) g])

/-- Locally integrable positive tails for measurable regularly varying functions of positive
index. -/
theorem exists_intervalIntegrable_tail_of_regularlyVarying {g : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hgm : Measurable g) (hrv : RegularlyVarying ρ g) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : ℝ, R ≤ x → x ≤ y → IntervalIntegrable g volume x y := by
  obtain ⟨R, hR1, hpos, hbdd⟩ := hrv.exists_threshold hρ hgm
  refine ⟨R, by linarith, fun x y hx hxy => ?_⟩
  obtain ⟨C, hC⟩ := hbdd y
  refine IntegrableOn.intervalIntegrable (IntegrableOn.of_bound
    (isCompact_uIcc (a := x) (b := y)).measure_lt_top hgm.aestronglyMeasurable C ?_)
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with s hs
  rw [uIcc_of_le hxy] at hs
  rw [Real.norm_eq_abs, abs_of_pos (hpos s (le_trans hx hs.1))]
  exact hC s (le_trans hx hs.1) hs.2

/-- **Karamata integration on a positive tail, with a multiplier converging to one**:
`(∫_{r₀}^r (1 - δ) g) / (r g r) → 1 / (c + 1)` when `g` is regularly varying of index
`c > -1`, `δ → 0` and `|δ| ≤ 1` above `r₀`. -/
theorem tendsto_mul_one_sub_karamata_integral_tail {g δ : ℝ → ℝ} {r₀ c : ℝ}
    (hc : -1 < c) (hr₀ : 0 < r₀) (hr₀1 : 1 ≤ r₀) (hgm : Measurable g)
    (hrv : RegularlyVarying c g)
    (hlocal : ∀ x y : ℝ, r₀ ≤ x → x ≤ y → IntervalIntegrable g volume x y)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1) :
    Tendsto (fun r => (∫ s in r₀..r, (1 - δ s) * g s) / (r * g r))
      atTop (𝓝 (1 / (c + 1))) := by
  have hpos := hrv.eventually_pos
  let T : ℝ → ℝ := (Ioi r₀).indicator g
  let F : ℝ → ℝ := fun s => (1 - δ s) * T s
  have hTm : Measurable T := hgm.indicator measurableSet_Ioi
  have hTpos : ∀ᶠ x in atTop, 0 < T x := by
    filter_upwards [hpos, eventually_gt_atTop r₀] with x hx hx₀
    simp only [T, Set.indicator_of_mem (Set.mem_Ioi.2 hx₀) g]
    exact hx
  have hTrv : RegularlyVarying c T := regularlyVarying_indicator_Ioi hrv
  have hTlocal : LocallyIntegrableOn T (Ioi 0) :=
    locallyIntegrableOn_indicator_Ioi_of_intervalIntegrable hlocal
  have hFm : Measurable F := (measurable_const.sub hδm).mul hTm
  have hbase : LocallyIntegrableOn (fun x => 2 * ‖T x‖) (Ioi 0) := by
    intro x hx
    rcases hTlocal.norm x hx with ⟨U, hU, hi⟩
    exact ⟨U, hU, hi.const_mul 2⟩
  have hFbound : ∀ x, ‖F x‖ ≤ ‖2 * ‖T x‖‖ := by
    intro x
    by_cases hx : r₀ < x
    · have hδ := hδ1 x hx.le
      have hfac : |1 - δ x| ≤ 2 := by
        calc |1 - δ x| ≤ |1| + |δ x| := abs_sub _ _
          _ ≤ 2 := by rw [abs_one]; linarith
      calc ‖F x‖ = |1 - δ x| * |T x| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 2 * |T x| := mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
        _ = ‖2 * ‖T x‖‖ := by
          simp only [Real.norm_eq_abs, abs_mul,
            abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg (abs_nonneg _)]
    · have hTx : T x = 0 := by
        simp [T, Set.indicator_of_notMem (fun hm => hx (Set.mem_Ioi.1 hm)) g]
      simp [F, hTx]
  have hFlocal : LocallyIntegrableOn F (Ioi 0) :=
    hbase.mono hFm.aestronglyMeasurable (Eventually.of_forall hFbound)
  have hfac : Tendsto (fun x => 1 - δ x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hδ0
  have hfacpos : ∀ᶠ x in atTop, 0 < 1 - δ x :=
    hfac.eventually (eventually_gt_nhds zero_lt_one)
  have hFT : Tendsto (fun x => F x / T x) atTop (𝓝 1) := by
    apply hfac.congr'
    filter_upwards [hTpos] with x hx
    symm
    exact div_eq_iff hx.ne' |>.mpr rfl
  have hFrv : RegularlyVarying c F :=
    RegularlyVarying.of_tendsto_div hTrv hFT ⟨0, measurable_restrict_Ici_of_measurable hFm 0⟩
  have hFpos : ∀ᶠ x in atTop, 0 < F x := by
    filter_upwards [hfacpos, hTpos] with x hx hxT
    exact mul_pos hx hxT
  have hFint : ∀ x y : ℝ, 0 < x → x ≤ y → IntervalIntegrable F volume x y := by
    intro x y hx hxy
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hxy (by simp)]
    exact (locallyIntegrableOn_iff isLocallyClosed_Ioi).1 hFlocal (Icc x y)
      (fun z hz => lt_of_lt_of_le hx hz.1) isCompact_Icc
  have hK : Tendsto (fun r => (∫ s in 1..r, F s) / (r * F r))
      atTop (𝓝 (1 / (c + 1))) :=
    lemma_I_2_10_of_regularlyVarying hc hFm hFlocal hFpos hFrv
  have hFTg : Tendsto (fun r => F r / g r) atTop (𝓝 1) := by
    apply hFT.congr'
    filter_upwards [hpos, eventually_gt_atTop r₀] with r hr hr₀r
    rw [show T r = g r by simp [T, Set.indicator_of_mem (Set.mem_Ioi.2 hr₀r) g]]
  have hden : Tendsto (fun r => (r * F r) / (r * g r)) atTop (𝓝 1) := by
    apply hFTg.congr'
    filter_upwards [hpos, eventually_gt_atTop (0 : ℝ), hFpos] with r hr hr0 hrF
    rw [mul_div_mul_left _ _ hr0.ne']
  have hnormalized : Tendsto (fun r => (∫ s in 1..r, F s) / (r * g r))
      atTop (𝓝 (1 / (c + 1))) := by
    have hm := hK.mul hden
    rw [mul_one] at hm
    apply hm.congr'
    filter_upwards [hFpos, hpos, eventually_gt_atTop (0 : ℝ)] with r hrF hr hr0
    have h1 : r * F r ≠ 0 := mul_ne_zero hr0.ne' hrF.ne'
    rw [div_mul_div_cancel₀ h1]
  apply hnormalized.congr'
  filter_upwards [eventually_ge_atTop r₀, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  have hzero : (∫ s in 1..r₀, F s) = 0 := by
    have hz : EqOn F (fun _ => 0) (uIcc 1 r₀) := by
      intro x hx
      rw [uIcc_of_le hr₀1] at hx
      by_cases hxr : r₀ < x
      · exact (not_le.2 hxr hx.2).elim
      · simp [F, T, Set.indicator_of_notMem (fun hm => hxr (Set.mem_Ioi.1 hm)) g]
    calc (∫ s in 1..r₀, F s) = ∫ _s in 1..r₀, (0 : ℝ) := intervalIntegral.integral_congr hz
      _ = 0 := intervalIntegral.integral_zero
  have hFint' : ∀ x y : ℝ, 0 < x → 0 < y → IntervalIntegrable F volume x y := by
    intro x y hx hy
    rcases le_total x y with hxy | hyx
    · exact hFint x y hx hxy
    · exact (hFint y x hy hyx).symm
  have hsplit : (∫ s in 1..r, F s) = ∫ s in r₀..r, F s := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hFint' 1 r₀ one_pos hr₀) (hFint' r₀ r hr₀ (lt_of_lt_of_le zero_lt_one hr1))
    rw [hzero, zero_add] at hadd
    exact hadd.symm
  rw [hsplit]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x hx
  rw [uIoc_of_le hr] at hx
  simp [F, T, Set.indicator_of_mem (Set.mem_Ioi.2 hx.1) g]

end PercLib.Analysis
