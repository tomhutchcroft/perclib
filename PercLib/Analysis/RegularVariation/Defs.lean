/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Slow and regular variation at infinity (wiki tag 3491), following Bingham–Goldie–Teugels, *Regular
Variation*, §1.1–1.4, and the wiki article `regular-variation`. Mathlib at the pinned revision has
no such notion. New definitions and proofs; nothing is copied for them. The definitions
`LogarithmicallyIntegrable`, `IsLogErrorFunction` and `genInv` are adapted from the work of
contributor `yujinhkim`: repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/RegularVariation.lean` (`LogarithmicallyIntegrable`,
`IsLogErrorFunction`) and `PercLib/CriticalLRP/Analysis/GeneralInverse.lean` (`genInv`); licence
Apache-2.0 as declared in those file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. The
section header before `LogarithmicallyIntegrable` records what was changed. That repository has a
variant `RegularlyVaryingAtTop` that asks only for eventual non-vanishing and no measurability; it
is not used here.
-/
module

public import PercLib.Meta.Tag
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Slow and regular variation at infinity

For `f : ℝ → ℝ`, only the values of `f` at large positive arguments matter, and, as in
Bingham–Goldie–Teugels, measurability is asked only on a tail:
`∃ a, Measurable ((Set.Ici a).domRestrict f)`. A globally measurable function qualifies
(`measurable_restrict_Ici_of_measurable`), a later tail qualifies
(`measurable_restrict_Ici_mono`), and a tail-measurable function agrees on its tail with a
globally measurable one (`exists_measurable_eqOn_Ici`).
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.Analysis

/-- `L` is **slowly varying at infinity**: `L` is measurable on some tail `[a, ∞)`, eventually
positive, and `L (c x) / L x → 1` as `x → ∞` for every fixed `c > 0` (BGT §1.2). -/
def SlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∃ a, Measurable ((Ici a).domRestrict L)) ∧ (∀ᶠ x in atTop, 0 < L x) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- `f` is **regularly varying at infinity with index `ρ`**: `f` is measurable on some tail
`[a, ∞)`, eventually positive, and `f (c x) / f x → c ^ ρ` as `x → ∞` for every fixed `c > 0`
(BGT §1.4). The equivalent form `f x = x ^ ρ L x` with `L` slowly varying is
`regularlyVarying_iff_slowlyVarying_div_rpow`. -/
def RegularlyVarying (ρ : ℝ) (f : ℝ → ℝ) : Prop :=
  (∃ a, Measurable ((Ici a).domRestrict f)) ∧ (∀ᶠ x in atTop, 0 < f x) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ))

variable {ρ : ℝ} {f g L : ℝ → ℝ}

/-! ### Measurability on a tail -/

/-- A globally measurable function is measurable on every tail. -/
theorem measurable_restrict_Ici_of_measurable (hf : Measurable f) (a : ℝ) :
    Measurable ((Ici a).domRestrict f) :=
  hf.comp measurable_subtype_coe

/-- Measurability on a tail passes to every later tail. -/
theorem measurable_restrict_Ici_mono {a b : ℝ} (h : Measurable ((Ici a).domRestrict f))
    (hab : a ≤ b) : Measurable ((Ici b).domRestrict f) := by
  have : (Ici b).domRestrict f =
      (Ici a).domRestrict f ∘ fun x : Ici b => (⟨x.1, Ici_subset_Ici.2 hab x.2⟩ : Ici a) := rfl
  rw [this]
  exact h.comp (measurable_subtype_coe.subtype_mk)

/-- A function measurable on `[a, ∞)` agrees there with a globally measurable function. -/
theorem exists_measurable_eqOn_Ici {a : ℝ} (h : Measurable ((Ici a).domRestrict f)) :
    ∃ F : ℝ → ℝ, Measurable F ∧ ∀ x, a ≤ x → F x = f x := by
  classical
  refine ⟨(Ici a).piecewise f 0, ?_, fun x hx => piecewise_eq_of_mem _ _ _ hx⟩
  refine measurable_of_restrict_of_restrict_compl (s := Ici a) measurableSet_Ici ?_ ?_
  · convert h using 1
    funext x
    exact piecewise_eq_of_mem _ _ _ x.2
  · convert (measurable_const : Measurable fun _ : ↥(Ici a)ᶜ => (0 : ℝ)) using 1
    funext x
    exact piecewise_eq_of_notMem _ _ _ x.2

/-! ### API -/

theorem slowlyVarying_def :
    SlowlyVarying L ↔ (∃ a, Measurable ((Ici a).domRestrict L)) ∧ (∀ᶠ x in atTop, 0 < L x) ∧
      ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1) := Iff.rfl

theorem regularlyVarying_def :
    RegularlyVarying ρ f ↔ (∃ a, Measurable ((Ici a).domRestrict f)) ∧ (∀ᶠ x in atTop, 0 < f x) ∧
      ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ)) := Iff.rfl

theorem SlowlyVarying.measurable_tail (h : SlowlyVarying L) :
    ∃ a, Measurable ((Ici a).domRestrict L) := h.1

theorem SlowlyVarying.eventually_pos (h : SlowlyVarying L) : ∀ᶠ x in atTop, 0 < L x := h.2.1

theorem SlowlyVarying.tendsto (h : SlowlyVarying L) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1) := h.2.2 c hc

theorem RegularlyVarying.measurable_tail (h : RegularlyVarying ρ f) :
    ∃ a, Measurable ((Ici a).domRestrict f) := h.1

theorem RegularlyVarying.eventually_pos (h : RegularlyVarying ρ f) :
    ∀ᶠ x in atTop, 0 < f x := h.2.1

theorem RegularlyVarying.tendsto (h : RegularlyVarying ρ f) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ ρ)) := h.2.2 c hc

/-- Regular variation depends only on the values at large arguments. -/
theorem RegularlyVarying.congr' (h : RegularlyVarying ρ f) (hfg : f =ᶠ[atTop] g) :
    RegularlyVarying ρ g := by
  obtain ⟨⟨a, ha⟩, hp, ht⟩ := h
  obtain ⟨A, hA⟩ := eventually_atTop.1 hfg
  refine ⟨⟨max a A, ?_⟩, (hp.and hfg).mono fun x hx => hx.2 ▸ hx.1, fun c hc => ?_⟩
  · have : (Ici (max a A)).domRestrict g = (Ici (max a A)).domRestrict f := by
      funext x
      exact (hA x.1 (le_trans (le_max_right _ _) x.2)).symm
    rw [this]
    exact measurable_restrict_Ici_mono ha (le_max_left _ _)
  · refine (ht c hc).congr' ?_
    filter_upwards [hfg, (tendsto_id.const_mul_atTop hc).eventually hfg] with x hx hcx
    dsimp only [id] at hcx
    rw [hx, hcx]

/-- Slow variation is regular variation of index `0`. -/
theorem slowlyVarying_iff_regularlyVarying_zero : SlowlyVarying L ↔ RegularlyVarying 0 L := by
  simp only [SlowlyVarying, RegularlyVarying, Real.rpow_zero]

/-- The ratio identity behind the representation `f x = x ^ ρ L x`. -/
private theorem ratio_div_rpow {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (a b : ℝ) :
    a / (c * x) ^ ρ / (b / x ^ ρ) = a / b / c ^ ρ := by
  have hcρ : c ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hc ρ).ne'
  have hxρ : x ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hx ρ).ne'
  rw [Real.mul_rpow hc.le hx.le, div_div_eq_mul_div, div_mul_eq_mul_div,
    mul_div_mul_right _ _ hxρ, div_right_comm]

/-- **Representation of regular variation** (wiki tag 3491): `f` is regularly varying with
index `ρ` if and only if `x ↦ f x / x ^ ρ` is slowly varying. -/
@[tag "3491"]
theorem regularlyVarying_iff_slowlyVarying_div_rpow :
    RegularlyVarying ρ f ↔ SlowlyVarying (fun x => f x / x ^ ρ) := by
  have hev : ∀ c : ℝ, 0 < c → ∀ᶠ x in atTop,
      f (c * x) / (c * x) ^ ρ / (f x / x ^ ρ) = f (c * x) / f x / c ^ ρ :=
    fun c hc => (eventually_gt_atTop 0).mono fun x hx => ratio_div_rpow hc hx _ _
  have hpos : ∀ᶠ x in atTop, (0 < f x / x ^ ρ ↔ 0 < f x) :=
    (eventually_gt_atTop 0).mono fun x hx => div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hx ρ)
  have hpow : Measurable fun x : Ici (1 : ℝ) => (x : ℝ) ^ ρ :=
    (measurable_id.pow_const ρ).comp measurable_subtype_coe
  constructor
  · rintro ⟨⟨a, ha⟩, hp, ht⟩
    refine ⟨⟨a, ha.div ((measurable_id.pow_const ρ).comp measurable_subtype_coe)⟩,
      (hp.and hpos).mono fun x hx => hx.2.2 hx.1, ?_⟩
    intro c hc
    have hcρ : c ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hc ρ).ne'
    have := (ht c hc).div_const (c ^ ρ)
    rw [div_self hcρ] at this
    exact this.congr' (EventuallyEq.symm (hev c hc))
  · rintro ⟨⟨a, ha⟩, hp, ht⟩
    refine ⟨⟨max a 1, ?_⟩, (hp.and hpos).mono fun x hx => hx.2.1 hx.1, ?_⟩
    · have hm := measurable_restrict_Ici_mono ha (le_max_left a 1)
      have : (Ici (max a 1)).domRestrict f =
          fun x => (Ici (max a 1)).domRestrict (fun x => f x / x ^ ρ) x * (x : ℝ) ^ ρ := by
        funext x
        have hx : (0 : ℝ) < x := lt_of_lt_of_le one_pos (le_trans (le_max_right a 1) x.2)
        exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos hx ρ).ne').symm
      rw [this]
      exact hm.mul ((measurable_id.pow_const ρ).comp measurable_subtype_coe)
    intro c hc
    have hcρ : c ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hc ρ).ne'
    have := (ht c hc).const_mul (c ^ ρ)
    rw [mul_one] at this
    refine this.congr' ((hev c hc).mono fun x hx => ?_)
    rw [hx, mul_div_cancel₀ _ hcρ]

/-- A slowly varying function times `x ^ ρ` is regularly varying with index `ρ`. -/
theorem SlowlyVarying.rpow_mul (h : SlowlyVarying L) (ρ : ℝ) :
    RegularlyVarying ρ (fun x => x ^ ρ * L x) := by
  obtain ⟨a, ha⟩ := h.measurable_tail
  refine ⟨⟨a, ((measurable_id.pow_const ρ).comp measurable_subtype_coe).mul ha⟩,
    ((eventually_gt_atTop 0).and h.eventually_pos).mono fun x hx =>
      mul_pos (Real.rpow_pos_of_pos hx.1 ρ) hx.2, fun c hc => ?_⟩
  have := (h.tendsto hc).const_mul (c ^ ρ)
  rw [mul_one] at this
  refine this.congr' ((eventually_gt_atTop 0).mono fun x hx => ?_)
  have hxρ : x ^ ρ ≠ 0 := (Real.rpow_pos_of_pos hx ρ).ne'
  dsimp only
  rw [Real.mul_rpow hc.le hx.le, mul_assoc, mul_div_assoc, mul_div_mul_left _ _ hxρ]

/-! ### Witnesses -/

/-- A positive constant is slowly varying. -/
theorem slowlyVarying_const {a : ℝ} (ha : 0 < a) : SlowlyVarying (fun _ => a) :=
  ⟨⟨0, measurable_const⟩, Eventually.of_forall fun _ => ha, fun _ _ => by
    simp [div_self ha.ne']⟩

/-- The logarithm is slowly varying. -/
theorem slowlyVarying_log : SlowlyVarying Real.log := by
  refine ⟨⟨0, measurable_restrict_Ici_of_measurable Real.measurable_log 0⟩,
    (eventually_gt_atTop 1).mono fun x hx => Real.log_pos hx,
    fun c hc => ?_⟩
  have h0 : Tendsto (fun x => Real.log c / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have := h0.const_add 1
  rw [add_zero] at this
  refine this.congr' ((eventually_gt_atTop 1).mono fun x hx => ?_)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  dsimp only
  rw [Real.log_mul hc.ne' (by linarith), add_div, div_self hlog, add_comm]

/-- `x ^ ρ log x` is regularly varying with index `ρ`. -/
theorem regularlyVarying_rpow_mul_log (ρ : ℝ) :
    RegularlyVarying ρ (fun x => x ^ ρ * Real.log x) :=
  slowlyVarying_log.rpow_mul ρ

example : SlowlyVarying Real.log := slowlyVarying_log

example : RegularlyVarying 2 (fun x => x ^ (2 : ℝ) * Real.log x) :=
  regularlyVarying_rpow_mul_log 2

/-! ### Logarithmic integrability, log-error functions and the generalized inverse

The next three definitions are adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`,
commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/RegularVariation.lean` (`LogarithmicallyIntegrable`,
`IsLogErrorFunction`) and `PercLib/CriticalLRP/Analysis/GeneralInverse.lean` (`genInv`, there
written through an auxiliary `levelSet`, which is inlined here); licence Apache-2.0 as declared in
those file headers; upstream `yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. The statements are unchanged; the API lemmas and
witnesses below are new. -/

/-- `h` is **logarithmically integrable**: `h` is measurable on some tail `[a, ∞)` (as for
`RegularlyVarying`) and `∫_{r₀}^∞ |h r| dr / r < ∞` for some `r₀ > 0` (Hutchcroft, *Critical
long-range percolation I*, arXiv:2508.18807v1, §I.2.2, p. 26). -/
def LogarithmicallyIntegrable (h : ℝ → ℝ) : Prop :=
  (∃ a, Measurable ((Ici a).domRestrict h)) ∧ ∃ r₀ > 0, IntegrableOn (fun r => |h r| / r) (Ioi r₀)

/-- `h` is a **logarithmically integrable error function**: it is logarithmically integrable
and `h r → 0` as `r → ∞` (*Critical long-range percolation I*, §I.2.2, p. 26). -/
def IsLogErrorFunction (h : ℝ → ℝ) : Prop :=
  LogarithmicallyIntegrable h ∧ Tendsto h atTop (𝓝 0)

/-- The **generalized inverse of `f` above the threshold `x₀`** at level `y`: the infimum of
`{x | x₀ ≤ x ∧ y ≤ f x}`. It inverts a measurable regularly varying `f` of positive index,
which need not be monotone or continuous (*Critical long-range percolation I*, scale of
Proposition I.3.2). When the level set is empty, `sInf ∅ = 0` in `ℝ` gives the junk value
`0` (`genInv_eq_zero_of_forall_lt`); the API lemmas assume the level set is nonempty. -/
noncomputable def genInv (f : ℝ → ℝ) (x₀ y : ℝ) : ℝ :=
  sInf {x | x₀ ≤ x ∧ y ≤ f x}

section Q140

variable {h h' f : ℝ → ℝ} {x₀ x y y' : ℝ}

theorem logarithmicallyIntegrable_def :
    LogarithmicallyIntegrable h ↔ (∃ a, Measurable ((Ici a).domRestrict h)) ∧
      ∃ r₀ > 0, IntegrableOn (fun r => |h r| / r) (Ioi r₀) := Iff.rfl

theorem isLogErrorFunction_def :
    IsLogErrorFunction h ↔ LogarithmicallyIntegrable h ∧ Tendsto h atTop (𝓝 0) := Iff.rfl

theorem genInv_def (f : ℝ → ℝ) (x₀ y : ℝ) :
    genInv f x₀ y = sInf {x | x₀ ≤ x ∧ y ≤ f x} := rfl

/-- Monotonicity: a function measurable on a tail and eventually dominated in absolute value
by a logarithmically integrable one is logarithmically integrable. -/
theorem LogarithmicallyIntegrable.mono (hh : LogarithmicallyIntegrable h)
    (hm : ∃ a, Measurable ((Ici a).domRestrict h')) (hb : ∀ᶠ r in atTop, |h' r| ≤ |h r|) :
    LogarithmicallyIntegrable h' := by
  obtain ⟨-, r₀, hr₀, hint⟩ := hh
  obtain ⟨R, hR⟩ := eventually_atTop.1 hb
  obtain ⟨a, ha⟩ := hm
  obtain ⟨F, hF, hFeq⟩ := exists_measurable_eqOn_Ici ha
  refine ⟨⟨a, ha⟩, max (max r₀ R) a, lt_max_of_lt_left (lt_max_of_lt_left hr₀), ?_⟩
  have hmeas : AEStronglyMeasurable (fun r => |h' r| / r)
      (volume.restrict (Ioi (max (max r₀ R) a))) :=
    (((continuous_abs.measurable.comp hF).div measurable_id).aestronglyMeasurable).congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
        change |F r| / r = |h' r| / r
        rw [hFeq r ((le_max_right _ _).trans hr.le)])
  refine (hint.mono_set (Ioi_subset_Ioi ((le_max_left _ _).trans (le_max_left _ _)))).mono'
    hmeas (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  have hr0 : 0 < r := hr₀.trans_le (((le_max_left _ _).trans (le_max_left _ _)).trans hr.le)
  rw [Real.norm_of_nonneg (div_nonneg (abs_nonneg _) hr0.le)]
  exact div_le_div_of_nonneg_right
    (hR r (((le_max_right _ _).trans (le_max_left _ _)).trans hr.le)) hr0.le

/-- Monotonicity for log-error functions. -/
theorem IsLogErrorFunction.mono (hh : IsLogErrorFunction h)
    (hm : ∃ a, Measurable ((Ici a).domRestrict h'))
    (hb : ∀ᶠ r in atTop, |h' r| ≤ |h r|) : IsLogErrorFunction h' := by
  refine ⟨hh.1.mono hm hb, tendsto_zero_iff_abs_tendsto_zero _ |>.2 ?_⟩
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb
    ((tendsto_zero_iff_abs_tendsto_zero _).1 hh.2)

/-- The generalized inverse is at most every point of the level set. -/
theorem genInv_le (hx : x₀ ≤ x) (hy : y ≤ f x) : genInv f x₀ y ≤ x :=
  csInf_le ⟨x₀, fun _ hz => hz.1⟩ ⟨hx, hy⟩

/-- The generalized inverse is at least the threshold when the level set is nonempty. -/
theorem le_genInv (hne : ∃ x, x₀ ≤ x ∧ y ≤ f x) : x₀ ≤ genInv f x₀ y :=
  le_csInf hne fun _ hz => hz.1

/-- Monotonicity: the generalized inverse is nondecreasing in the level, as long as the
level set at the larger level is nonempty. -/
theorem genInv_mono (hne : ∃ x, x₀ ≤ x ∧ y' ≤ f x) (hyy : y ≤ y') :
    genInv f x₀ y ≤ genInv f x₀ y' :=
  csInf_le_csInf ⟨x₀, fun _ hz => hz.1⟩ hne fun _ hz => ⟨hz.1, hyy.trans hz.2⟩

/-- The junk value: if `f < y` everywhere above `x₀`, the generalized inverse is `0`. -/
theorem genInv_eq_zero_of_forall_lt (hlt : ∀ x, x₀ ≤ x → f x < y) : genInv f x₀ y = 0 := by
  rw [genInv_def, show {x | x₀ ≤ x ∧ y ≤ f x} = ∅ from
    eq_empty_of_forall_notMem fun x hx => (hlt x hx.1).not_ge hx.2, Real.sInf_empty]

/-! #### Witnesses -/

theorem isLogErrorFunction_zero : IsLogErrorFunction (fun _ => 0) :=
  ⟨⟨⟨0, measurable_const⟩, 1, one_pos, by simp⟩, tendsto_const_nhds⟩

/-- `r ↦ 1 / (log r)²`, which decays slower than every power, is a log-error function. -/
theorem isLogErrorFunction_inv_log_sq : IsLogErrorFunction (fun r => 1 / Real.log r ^ 2) := by
  refine ⟨⟨⟨0, measurable_restrict_Ici_of_measurable (by fun_prop) 0⟩, 2, two_pos, ?_⟩, ?_⟩
  · have hlog : ∀ r ∈ Ici (2 : ℝ), 0 < Real.log r := fun r hr =>
      Real.log_pos (by linarith [mem_Ici.1 hr])
    have hderiv : ∀ r ∈ Ici (2 : ℝ), HasDerivAt (fun r => -(Real.log r)⁻¹)
        (|1 / Real.log r ^ 2| / r) r := by
      intro r hr
      have hr0 : r ≠ 0 := by linarith [mem_Ici.1 hr]
      have := ((Real.hasDerivAt_log hr0).inv (hlog r hr).ne').neg
      convert this using 1
      rw [abs_of_pos (by have := hlog r hr; positivity)]
      field_simp
    refine integrableOn_Ioi_deriv_of_nonneg' (l := 0) hderiv
      (fun r _ => div_nonneg (abs_nonneg _) (by linarith [mem_Ioi.1 ‹r ∈ Ioi 2›])) ?_
    simpa using (Real.tendsto_log_atTop.inv_tendsto_atTop).neg
  · have := ((tendsto_pow_atTop two_ne_zero).comp Real.tendsto_log_atTop).inv_tendsto_atTop
    simpa [Function.comp_def, one_div, Pi.inv_def] using this

/-- At the identity with threshold `0`, the generalized inverse is `max y 0`. -/
theorem genInv_id_zero (y : ℝ) : genInv id 0 y = max y 0 := by
  rw [genInv_def, show {x : ℝ | 0 ≤ x ∧ y ≤ id x} = Ici (max y 0) by
    ext x; simp [and_comm], csInf_Ici]

end Q140

end PercLib.Analysis
