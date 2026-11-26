/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
The Tauberian converse and the full statement of Theorem I.2.11 of T. Hutchcroft, *Critical
long-range percolation I*, arXiv:2508.18807v1, p. 26 (citing Feller, *An Introduction to
Probability Theory and Its Applications*, Vol. II, XIII.5, Theorem 2).

Adapted from the repository `yujinhkim/lrp`, branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, files
`PercLib/CriticalLRP/Analysis/TauberianConverseComplete.lean` and
`PercLib/CriticalLRP/Analysis/TauberianPointwise.lean`; licence Apache-2.0 as declared in that
commit's file headers and `third_party/critical-lrp/NOTICE.md`; upstream
`yujinhkim/Critical-Long-range-percolation` at `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`.
Modified: `RegularlyVaryingAtTop f (-α)` becomes `RegularlyVarying (-α) f` of
`PercLib/Analysis/RegularVariation/Defs.lean` (which also asks measurability on a tail and
eventual positivity); the source definitions `Phi`, `profileBound` and `limitProfile` are
written out in the statements; hypotheses the proofs do not use are removed, among them every
measurability hypothesis on `F` and `f`; the truncation, density and squeeze lemmas are stated
for an arbitrary measure, set, filter and continuous comparison function; the source lemmas
`integrableOn_exp_mul_rpow_neg`, `exists_good_below`, `exists_good_above`,
`tendsto_one_of_antitone_squeeze`, `tendsto_Gamma_mul_div_of_tail`, `tendsto_Phi_subseq_one`,
`tendsto_Phi_subseq_at`, `limitProfile_eq_rpow_ae_of_all` and
`exists_limitProfile_eq_rpow_ae_and_tendsto_one` are dropped in favour of mathlib or of the
general forms here; the weighted Laplace uniqueness is derived from
`PercLib/Analysis/LaplaceUniqueness.lean`; the converse direction of Theorem I.2.11 is assembled
from `PercLib/Analysis/Tauberian/Endpoints.lean`; the slowly varying form and the strict-tail
form are new; the non-vacuity theorem becomes an `example`; `autoImplicit` and disabled linters
are removed.
-/
module

public import PercLib.Analysis.Tauberian.Endpoints
public import PercLib.Analysis.LaplaceUniqueness
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Theorem I.2.11: the Tauberian converse and the Laplace–tail equivalence

Let `F ≥ 0` be antitone, `f` regularly varying of index `-α` with `0 ≤ α < 1`, and suppose
`∫_0^∞ e^{-u} F(u/h) du ~ f(1/h)` as `h ↓ 0`. Write `Φ_h(u) = Γ(1-α) F(u/h) / f(1/h)` for the
normalised profile (spelled out in the statements). This file proves `F x ~ f x / Γ(1 - α)` and
hence the equivalence of Theorem I.2.11 for a probability measure on `[0, ∞)`.

The compactness step (`exists_rational_limit`, `ae_tendsto_limitProfile`) is in
`PercLib.Analysis.Tauberian.Converse`. Here the limit profile
`u ↦ sup {L q : q ∈ ℚ, q > u}` is shown to have Laplace transform `Γ(1 - α) σ^{α-1}`, hence to be
`u ↦ u^{-α}`, and a squeeze between nearby good points gives the limit at every point.

`PercLib.Probability.GhostTransform.tail_asymp_iff_ghost_asymp` is a different statement: a
two-sided up-to-constants equivalence for an `ℕ∞`-valued variable, with no regular variation.

## Main results

* `integral_exp_mul_limitProfile`: the Laplace transform of the limit profile;
* `ae_eq_rpow_of_laplace`: a profile with these Laplace transforms is `u ↦ u^{-α}` a.e.;
* `tendsto_of_antitone_of_ae_tendsto`: antitone functions converging a.e. to a function
  continuous at `u` converge at `u`;
* `tendsto_Phi_one`, `tendsto_Phi_at`: `Φ_h(u) → u^{-α}` as `h ↓ 0`, for every `u > 0`;
* `tendsto_tail_of_laplace`: the strict converse `F x / (f x / Γ(1 - α)) → 1`;
* `limitProfile_eq_rpow_all`, `exists_limitProfile_eq_rpow_and_tendsto_one`: the limit profile
  is `u ↦ u^{-α}` at every point of `(0, ∞)`;
* `laplace_asymptotic_iff_tail_ge`, `laplace_asymptotic_iff_tail_gt` and their `_rpow` forms:
  Theorem I.2.11 for a probability measure on `[0, ∞)`, with no further hypothesis;
* `SlowlyVarying.tail_asymptotic_iff_laplace_asymptotic`: for a random variable `X ≥ 0` and
  `L` slowly varying, `P(X > t) ~ t^{-α} L(t)` iff `E[1 - e^{-hX}] ~ Γ(1 - α) h^α L(1 / h)`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace PercLib.Analysis

/-! ### Integrability of the comparison function -/

/-- `u ↦ e^{-σu} Γ(1 - α)·((3 / 2)·e·u^{-α})` is integrable on `(0,∞)` when `α < 1` and `σ > 0`. -/
theorem integrableOn_exp_mul_profileBound {α σ : ℝ} (hα : α < 1) (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) *
      (Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * u ^ (-α)))) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -α) (b := σ)
    (by linarith) one_pos hσ).const_mul (Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1))
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]
  ring

/-! ### The normalised profile: monotonicity, positivity, near mass, domination -/

/-- The normalised profile `u ↦ Γ(1 - α) F(u / h)/f(1 / h)` is antitone when `f (1 / h) > 0`. -/
theorem Phi_antitone {F f : ℝ → ℝ} {α h : ℝ} (hα1 : α < 1) (hanti : Antitone F)
    (hh : 0 < h) (hf : 0 < f (1 / h)) :
    Antitone fun u : ℝ => Real.Gamma (1 - α) * F (u / h) / f (1 / h) := by
  intro u v huv
  have hF : F (v/h) ≤ F (u / h) := hanti (div_le_div_of_nonneg_right huv hh.le)
  have hΓ : (0 : ℝ) ≤ Real.Gamma (1 - α) := (Real.Gamma_pos_of_pos (by linarith)).le
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF hΓ) hf.le

/-- The normalised profile is nonnegative when `F ≥ 0` and `f (1 / h) > 0`. -/
theorem Phi_nonneg {F f : ℝ → ℝ} {α h : ℝ} (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x)
    (hf : 0 < f (1 / h)) :
    ∀ u : ℝ, 0 ≤ Real.Gamma (1 - α) * F (u / h) / f (1 / h) := fun _ =>
  div_nonneg (mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (hF0 _)) hf.le

/-- **Near-zero mass of the normalised profile.** For every `δ > 0`, eventually
`∫_0^δ Γ(1 - α) F(u / h)/f(1 / h) du ≤ Γ(1 - α)·2e·δ^{1-α}`. -/
theorem near_mass_Phi_eventually_le {F f : ℝ → ℝ} {α : ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F) (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hα1 : α < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∫ u in Ioo (0 : ℝ) δ, Real.Gamma (1 - α) * F (u / h) / f (1 / h)
        ≤ Real.Gamma (1 - α) * (2 * Real.exp 1 * δ ^ (1 - α)) := by
  have hΓ : (0 : ℝ) ≤ Real.Gamma (1 - α) := (Real.Gamma_pos_of_pos (by linarith)).le
  filter_upwards [near_mass_eventually_le hF0 hanti hrv hmain hδ] with h hb
  have h1 : ∫ u in Ioo (0 : ℝ) δ, Real.Gamma (1 - α) * F (u / h) / f (1 / h)
      = Real.Gamma (1 - α) * ∫ u in Ioo (0 : ℝ) δ, F (u / h) / f (1 / h) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo (fun u _ => by ring)
  rw [h1]
  exact mul_le_mul_of_nonneg_left hb hΓ

/-- **Far-field domination.** For every `δ > 0`, eventually in `h`,
`Γ(1 - α) F(u / h)/f(1 / h) ≤ Γ(1 - α)·((3 / 2)·e·δ^{-α})` for all `u ≥ δ`. -/
theorem eventually_Phi_le_profileBound_of_le {F f : ℝ → ℝ} {α : ℝ}
    (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F) (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hα1 : α < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ u : ℝ, δ ≤ u →
      Real.Gamma (1 - α) * F (u / h) / f (1 / h)
        ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * δ ^ (-α)) := by
  filter_upwards [eventually_profile_bound hF0 hanti hrv hmain hα1 hδ,
    eventually_pos_of_tendsto_laplace hF0 hmain, self_mem_nhdsWithin] with h hb hf hh u hu
  exact (Phi_antitone hα1 hanti hh hf hu).trans hb.2

/-! ### Truncating an integral at the left endpoint -/

/-- For `g` integrable on `(a,∞)`, the integrals over `(δ,∞)` tend to the integral over
`(a,∞)` as `δ ↓ a`. -/
theorem tendsto_setIntegral_Ioi_nhdsGT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {g : ℝ → E} {a : ℝ} (hg : IntegrableOn g (Ioi a) μ) :
    Tendsto (fun δ : ℝ => ∫ u in Ioi δ, g u ∂μ) (𝓝[>] a) (𝓝 (∫ u in Ioi a, g u ∂μ)) := by
  have hlim : ∀ᵐ u ∂(μ.restrict (Ioi a)),
      Tendsto (fun δ : ℝ => (Ioi δ).indicator g u) (𝓝[>] a) (𝓝 (g u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_lt_nhds hu).filter_mono nhdsWithin_le_nhds] with δ hδ
    exact (indicator_of_mem (show u ∈ Ioi δ from hδ) g).symm
  have h := tendsto_integral_filter_of_dominated_convergence (fun u => ‖g u‖)
    (Eventually.of_forall fun δ => hg.aestronglyMeasurable.indicator measurableSet_Ioi)
    (Eventually.of_forall fun δ => Eventually.of_forall fun u => norm_indicator_le_norm_self _ _)
    hg.norm hlim
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : a < δ)
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi hδ.le)]

/-! ### Good points are dense -/

/-- A property that holds almost everywhere on a set `s ⊆ ℝ` holds somewhere in every
nonempty open interval contained in `s`. -/
theorem exists_mem_of_ae_restrict {P : ℝ → Prop} {s : Set ℝ}
    (hP : ∀ᵐ u ∂(volume.restrict s), P u) {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ s) :
    ∃ u : ℝ, a < u ∧ u < b ∧ P u := by
  have h1 : ∀ᵐ u ∂(volume.restrict (Ioo a b)), P u :=
    ae_restrict_of_ae_restrict_of_subset hsub hP
  have : (ae (volume.restrict (Ioo a b))).NeBot := ae_restrict_neBot.2 (by simp [hab])
  obtain ⟨u, hPu, hu⟩ := (h1.and (ae_restrict_mem measurableSet_Ioo)).exists
  exact ⟨u, hu.1, hu.2, hPu⟩

/-- **Good points just below `u`.** If `P` holds a.e. on `(0,∞)` and `g` is continuous at
`u > 0`, there is a point `a ∈ (0,u)` with `P a` and `g a < g u + ε`. -/
theorem exists_good_lt {P : ℝ → Prop} {g : ℝ → ℝ}
    (hP : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), P v) {u : ℝ} (hu : 0 < u)
    (hg : ContinuousAt g u) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < u ∧ P a ∧ g a < g u + ε := by
  obtain ⟨l, r, ⟨hlu, hur⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((hg.eventually (eventually_lt_nhds (lt_add_of_pos_right (g u) hε))).and
      (eventually_gt_nhds hu))
  have hmem : ∀ v, l < v → v < u → g v < g u + ε ∧ 0 < v := fun v hlv hvu =>
    hsub ⟨hlv, hvu.trans hur⟩
  obtain ⟨a, hla, hau, haP⟩ := exists_mem_of_ae_restrict hP hlu
    (fun v hv => (hmem v hv.1 hv.2).2)
  exact ⟨a, (hmem a hla hau).2, hau, haP, (hmem a hla hau).1⟩

/-- **Good points just above `u`.** If `P` holds a.e. on `(0,∞)` and `g` is continuous at
`u > 0`, there is a point `b > u` with `P b` and `g u < g b + ε`. -/
theorem exists_good_gt {P : ℝ → Prop} {g : ℝ → ℝ}
    (hP : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), P v) {u : ℝ} (hu : 0 < u)
    (hg : ContinuousAt g u) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, u < b ∧ P b ∧ g u < g b + ε := by
  obtain ⟨l, r, ⟨hlu, hur⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (hg.eventually (eventually_gt_nhds (sub_lt_self (g u) hε)))
  obtain ⟨b, hub, hbr, hbP⟩ := exists_mem_of_ae_restrict hP hur
    (fun v hv => (hu.trans hv.1 : 0 < v))
  have hb : g u - ε < g b := hsub ⟨hlu.trans hub, hbr⟩
  exact ⟨b, hub, hbP, by linarith⟩

/-! ### The Laplace transform of the normalised profile -/

/-- The Laplace transform of the normalised profile is `Γ(1 - α)` times the Laplace transform
of `u ↦ F(u / h)`, divided by `f (1 / h)`. -/
theorem integral_exp_mul_Phi_eq {F f : ℝ → ℝ} {α σ h : ℝ} :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * (Real.Gamma (1 - α) * F (u / h) / f (1 / h))
      = Real.Gamma (1 - α) *
          ((∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * F (u / h)) / f (1 / h)) := by
  have h1 : ∀ u : ℝ, Real.exp (-(σ * u)) * (Real.Gamma (1 - α) * F (u / h) / f (1 / h))
      = Real.Gamma (1 - α) * (Real.exp (-(σ * u)) * F (u / h)) / f (1 / h) := fun u => by ring
  simp_rw [h1]
  rw [integral_div, integral_const_mul]
  ring

/-- **The Laplace family of the normalised profile at every rate `σ > 0`.** -/
theorem tendsto_integral_exp_mul_Phi {F f : ℝ → ℝ} {α : ℝ} (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun h : ℝ =>
        ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * (Real.Gamma (1 - α) * F (u / h) / f (1 / h)))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.Gamma (1 - α) * σ ^ (α - 1))) :=
  ((tendsto_laplace_family hrv hmain hσ).const_mul _).congr fun _ =>
    integral_exp_mul_Phi_eq.symm

/-! ### Dominated convergence on `(δ,∞)` -/

/-- **Far-field convergence.** For every `δ > 0`, the Laplace transforms over `(δ,∞)` of the
normalised profiles along `hseq` converge to that of the limit profile
`u ↦ sup {L q : q > u}`. -/
theorem tendsto_integral_exp_mul_Phi_Ioi
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hantiPhi : ∀ k, Antitone fun u : ℝ =>
      Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k))
    (hseq_mem : Tendsto hseq atTop (𝓝[>] (0 : ℝ)))
    (hLb : ∀ q : {q : ℚ // 0 < q},
      L q ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * (q : ℝ) ^ (-α)))
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Real.Gamma (1 - α) * F ((q : ℝ) / hseq k) / f (1 / hseq k))
        atTop (𝓝 (L q)))
    {σ : ℝ} (hσ : 0 < σ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => ∫ u in Ioi δ,
        Real.exp (-(σ * u)) * (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k))) atTop
      (𝓝 (∫ u in Ioi δ, Real.exp (-(σ * u)) *
        sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x})) := by
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-(σ * u))) (Ioi δ) := by
    simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -σ) (by linarith) δ
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp (-(σ * u)) * (Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * δ ^ (-α))))
    (Eventually.of_forall fun k =>
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable.mul
        (hantiPhi k).measurable.aestronglyMeasurable) ?_ (hexp.mul_const _) ?_
  · filter_upwards [hseq_mem.eventually
      (eventually_Phi_le_profileBound_of_le hF0 hanti hrv hmain hα1 hδ),
      hseq_mem.eventually (eventually_pos_of_tendsto_laplace hF0 hmain)] with k hk hfk
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : δ < u)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (Phi_nonneg hα1 hF0 hfk u))]
    exact mul_le_mul_of_nonneg_left (hk u hu.le) (Real.exp_pos _).le
  · filter_upwards [ae_tendsto_limitProfile_ge hα0 hα1 hantiPhi hLb hconv hδ] with u hu
    exact hu.const_mul _

/-! ### The Laplace identity for the limit profile -/

/-- **The Laplace transform of the limit profile.** For every `σ > 0`,
`∫₀^∞ e^{-σu} ψ(u) du = Γ(1 - α) σ^{α-1}`, where `ψ u = sup {L q : q > u}` is the limit profile
attached to rational limit values `L` of the normalised profiles along `hseq`. -/
theorem integral_exp_mul_limitProfile
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ k, 0 < f (1 / hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q},
      L q ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * (q : ℝ) ^ (-α)))
    (hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Real.Gamma (1 - α) * F ((q : ℝ) / hseq k) / f (1 / hseq k))
        atTop (𝓝 (L q)))
    {σ : ℝ} (hσ : 0 < σ) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) *
        sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x}
      = Real.Gamma (1 - α) * σ ^ (α - 1) := by
  have hantiPhi : ∀ k, Antitone fun u : ℝ =>
      Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k) :=
    fun k => Phi_antitone hα1 hanti (hpos k) (hfpos k)
  have hnnPhi : ∀ k u, 0 ≤ Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k) :=
    fun k => Phi_nonneg hα1 hF0 (hfpos k)
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall hpos⟩
  have hfull := (tendsto_integral_exp_mul_Phi hrv hmain hσ).comp hseq_mem
  have hint_full : ∀ k, IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) *
      (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k))) (Ioi (0 : ℝ)) := fun k =>
    IntegrableOn.congr_fun
      (((integrableOn_exp_sigma_mul_div_of_antitone hσ hanti hF0 (hpos k)).const_mul
        (Real.Gamma (1 - α))).div_const (f (1 / hseq k))) (fun u _ => by ring)
      measurableSet_Ioi
  -- the two-sided bound for every radius `δ`
  have key : ∀ δ : ℝ, 0 < δ →
      (∫ u in Ioi δ, Real.exp (-(σ * u)) *
          sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x})
        ≤ Real.Gamma (1 - α) * σ ^ (α - 1) ∧
      Real.Gamma (1 - α) * σ ^ (α - 1) - Real.Gamma (1 - α) * (2 * Real.exp 1 * δ ^ (1 - α))
        ≤ ∫ u in Ioi δ, Real.exp (-(σ * u)) *
          sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x} := by
    intro δ hδ
    have hnear : ∀ᶠ k in atTop, ∫ u in Ioc (0 : ℝ) δ, Real.exp (-(σ * u)) *
          (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k))
        ≤ Real.Gamma (1 - α) * (2 * Real.exp 1 * δ ^ (1 - α)) := by
      filter_upwards [hseq_mem.eventually
        (near_mass_Phi_eventually_le hF0 hanti hrv hmain hα1 hδ)] with k hk
      rw [integral_Ioc_eq_integral_Ioo]
      refine le_trans (setIntegral_mono_on ((hint_full k).mono_set Ioo_subset_Ioi_self) ?_
        measurableSet_Ioo fun u hu => ?_) hk
      · refine (integrableOn_const (C := Real.Gamma (1 - α) * F 0 / f (1 / hseq k))
          (by simp)).mono' (hantiPhi k).measurable.aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg (hnnPhi k u)]
        have h0 := hantiPhi k hu.1.le
        simp only [zero_div] at h0
        exact h0
      · have hexp : Real.exp (-(σ * u)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [hu.1])
        exact mul_le_of_le_one_left (hnnPhi k u) hexp
    have hsplit : ∀ k, ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) *
          (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k))
        = (∫ u in Ioc (0 : ℝ) δ, Real.exp (-(σ * u)) *
            (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)))
          + ∫ u in Ioi δ, Real.exp (-(σ * u)) *
            (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)) := fun k => by
      rw [← Ioc_union_Ioi_eq_Ioi hδ.le, setIntegral_union Ioc_disjoint_Ioi_same
        measurableSet_Ioi ((hint_full k).mono_set Ioc_subset_Ioi_self)
        ((hint_full k).mono_set (Ioi_subset_Ioi hδ.le))]
    have hfar := tendsto_integral_exp_mul_Phi_Ioi hα0 hα1 hF0 hanti hrv hmain hantiPhi
      hseq_mem hLb hconv hσ hδ
    constructor
    · refine le_of_tendsto_of_tendsto hfar hfull (Eventually.of_forall fun k => ?_)
      have h1 : 0 ≤ ∫ u in Ioc (0 : ℝ) δ, Real.exp (-(σ * u)) *
          (Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k)) :=
        setIntegral_nonneg measurableSet_Ioc fun u _ =>
          mul_nonneg (Real.exp_pos _).le (hnnPhi k u)
      simp only [Function.comp_apply, hsplit k]
      linarith
    · have hle : _ ≤ Real.Gamma (1 - α) * (2 * Real.exp 1 * δ ^ (1 - α)) :=
        le_of_tendsto (hfull.sub hfar) (by
        filter_upwards [hnear] with k hk
        simp only [Function.comp_apply, hsplit k]
        linarith)
      linarith
  -- measurability and integrability of the limit profile against the exponential weight
  have hψmeas : AEStronglyMeasurable
      (fun u : ℝ => sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x})
      (volume.restrict (Ioi (0 : ℝ))) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hantiPhi k).measurable.aestronglyMeasurable)
      (ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv)
  have hψexpmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (-(σ * u)) *
      sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x})
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable.mul
      hψmeas
  have hψint : IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) *
      sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x}) (Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_mul_profileBound hα1 hσ).mono' hψexpmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (limitProfile_nonneg hα0 hα1 hLb hLnn hu))]
    exact mul_le_mul_of_nonneg_left (limitProfile_le_bound hα0 hα1 hLb hu) (Real.exp_pos _).le
  -- pass to `δ ↓ 0`
  have hlimδ := tendsto_setIntegral_Ioi_nhdsGT hψint
  have hpow : Tendsto (fun δ : ℝ => Real.Gamma (1 - α) * σ ^ (α - 1)
      - Real.Gamma (1 - α) * (2 * Real.exp 1 * δ ^ (1 - α))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.Gamma (1 - α) * σ ^ (α - 1))) := by
    have h0 : Tendsto (fun δ : ℝ => δ ^ (1 - α)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 (1 - α) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith)] at h
      exact h.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.sub ((h0.const_mul (2 * Real.exp 1)).const_mul
      (Real.Gamma (1 - α)))
  refine le_antisymm (le_of_tendsto hlimδ ?_) (le_of_tendsto_of_tendsto hpow hlimδ ?_)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (key δ hδ).1
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (key δ hδ).2

/-! ### Identifying the limit profile with `u^{-α}` -/

/-- **Weighted Laplace uniqueness.** If `u ↦ e^{-σu} D u` is integrable on `(0,∞)` and has
integral `0` for every `σ > 0`, then `D = 0` a.e. on `(0,∞)`. This is
`eq_zero_ae_of_forall_laplace_eq_zero` applied to `u ↦ e^{-u} D u`. -/
theorem eq_zero_ae_of_forall_laplace_weighted {D : ℝ → ℝ}
    (hint : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * D u) (Ioi (0 : ℝ)))
    (hlaplace : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * D u = 0) :
    D =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hGint : IntegrableOn (fun u : ℝ => Real.exp (-u) * D u) (Ioi (0 : ℝ)) := by
    simpa only [one_mul] using hint 1 one_pos
  have hGlap : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * (Real.exp (-u) * D u) = 0 := by
    intro σ hσ
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * (Real.exp (-u) * D u))
        = fun u : ℝ => Real.exp (-((σ+1)*u)) * D u := by
      funext u
      rw [← mul_assoc, ← Real.exp_add, show -(σ * u) + -u = -((σ+1)*u) by ring]
    rw [hcongr, hlaplace (σ + 1) (by linarith)]
  filter_upwards [eq_zero_ae_of_forall_laplace_eq_zero hGint hGlap] with u hu
  exact (mul_eq_zero.1 hu).resolve_left (Real.exp_pos _).ne'

/-- **Laplace uniqueness identifies the limit profile.** A nonnegative function bounded by
`u ↦ Γ(1 - α)·((3 / 2)·e·u^{-α})` whose Laplace transforms are `Γ(1 - α)σ^{α-1}` at every rate
coincides a.e. on `(0,∞)` with `u ↦ u^{-α}`. -/
theorem ae_eq_rpow_of_laplace {ψ : ℝ → ℝ} {α : ℝ} (hα1 : α < 1)
    (hψmeas : AEStronglyMeasurable ψ (volume.restrict (Ioi (0 : ℝ))))
    (hψnn : ∀ u, 0 < u → 0 ≤ ψ u)
    (hψle : ∀ u, 0 < u → ψ u ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * u ^ (-α)))
    (hlaplace : ∀ σ : ℝ, 0 < σ →
      ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * ψ u = Real.Gamma (1 - α) * σ ^ (α - 1)) :
    ψ =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => u ^ (-α) := by
  have hrpow : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * u ^ (-α)) (Ioi (0 : ℝ)) := by
    intro σ hσ
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -α) (b := σ)
      (by linarith) one_pos hσ).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul]
    ring
  have hψint : ∀ σ : ℝ, 0 < σ →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * ψ u) (Ioi (0 : ℝ)) := by
    intro σ hσ
    refine (integrableOn_exp_mul_profileBound hα1 hσ).mono'
      ((Real.measurable_exp.comp
        ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable.mul hψmeas) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hψnn u hu))]
    exact mul_le_mul_of_nonneg_left (hψle u hu) (Real.exp_pos _).le
  have hD := eq_zero_ae_of_forall_laplace_weighted (D := fun u => ψ u - u ^ (-α))
    (fun σ hσ => IntegrableOn.congr_fun ((hψint σ hσ).sub (hrpow σ hσ))
      (fun u _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi)
    (fun σ hσ => by
      have heq : (fun u : ℝ => Real.exp (-(σ * u)) * (ψ u - u ^ (-α)))
          = fun u : ℝ => Real.exp (-(σ * u)) * ψ u - Real.exp (-(σ * u)) * u ^ (-α) := by
        funext u
        ring
      have hgamma : ∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * u ^ (-α)
          = Real.Gamma (1 - α) * σ ^ (α - 1) := by
        have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 - α) (r := σ)
          (by linarith) hσ
        rw [show (1 - α) - 1 = -α by ring, one_div, Real.inv_rpow hσ.le,
          ← Real.rpow_neg hσ.le, neg_sub] at h
        rw [mul_comm, ← h]
        exact setIntegral_congr_fun measurableSet_Ioi fun u _ => by ring
      rw [heq, integral_sub (hψint σ hσ) (hrpow σ hσ), hlaplace σ hσ, hgamma, sub_self])
  filter_upwards [hD] with u hu
  exact sub_eq_zero.1 hu

/-! ### The squeeze -/

/-- **Squeezing antitone functions.** If antitone functions `Φ k` converge a.e. on `(0,∞)` to
`g`, and `g` is continuous at `u > 0`, then `Φ k u → g u`. The proof traps `Φ k u` between
`Φ k b` and `Φ k a` for good points `a < u < b` close to `u`. -/
theorem tendsto_of_antitone_of_ae_tendsto {ι : Type*} {l : Filter ι} {Φ : ι → ℝ → ℝ}
    {g : ℝ → ℝ} (hanti : ∀ k, Antitone (Φ k))
    (hae : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))), Tendsto (fun k => Φ k v) l (𝓝 (g v)))
    {u : ℝ} (hu : 0 < u) (hg : ContinuousAt g u) :
    Tendsto (fun k => Φ k u) l (𝓝 (g u)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨b, hub, hb, hgb⟩ := exists_good_gt hae hu hg (sub_pos.2 hc)
    filter_upwards [hb.eventually (lt_mem_nhds (by linarith : c < g b))] with k hk
    exact hk.trans_le (hanti k hub.le)
  · obtain ⟨a, -, hau, ha, hga⟩ := exists_good_lt hae hu hg (sub_pos.2 hc)
    filter_upwards [ha.eventually (gt_mem_nhds (by linarith : g a < c))] with k hk
    exact (hanti k hau.le).trans_lt hk

/-! ### The limit profile along a sequence of rational limit values -/

/-- **The limit profile is the power law almost everywhere.** For any sequence `hseq ↓ 0` and
any rational limit values `L` of the normalised profiles along it, the limit profile
`u ↦ sup {L q : q > u}` coincides a.e. on `(0,∞)` with `u ↦ u^{-α}`. -/
theorem limitProfile_eq_rpow_ae
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ k, 0 < f (1 / hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q},
      L q ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * (q : ℝ) ^ (-α)))
    (hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Real.Gamma (1 - α) * F ((q : ℝ) / hseq k) / f (1 / hseq k))
        atTop (𝓝 (L q))) :
    (fun u : ℝ => sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x})
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u : ℝ => u ^ (-α) := by
  have hantiPhi : ∀ k, Antitone fun u : ℝ =>
      Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k) :=
    fun k => Phi_antitone hα1 hanti (hpos k) (hfpos k)
  exact ae_eq_rpow_of_laplace hα1
    (aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (hantiPhi k).measurable.aestronglyMeasurable)
      (ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv))
    (fun u hu => limitProfile_nonneg hα0 hα1 hLb hLnn hu)
    (fun u hu => limitProfile_le_bound hα0 hα1 hLb hu)
    (fun σ hσ => integral_exp_mul_limitProfile hα0 hα1 hF0 hanti hrv hmain hpos htend hfpos
      hLb hLnn hconv hσ)

/-- **The squeeze at `u = 1` along a sequence of rational limit values.** For any `hseq ↓ 0`
and any rational limit values `L` of the normalised profiles along it,
`Γ(1 - α) F(1/hseq k)/f(1/hseq k) → 1`. -/
theorem tendsto_Phi_one_of_rational_limit
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ k, 0 < f (1 / hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q},
      L q ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * (q : ℝ) ^ (-α)))
    (hLnn : ∀ q : {q : ℚ // 0 < q}, 0 ≤ L q)
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Real.Gamma (1 - α) * F ((q : ℝ) / hseq k) / f (1 / hseq k))
        atTop (𝓝 (L q))) :
    Tendsto (fun k => Real.Gamma (1 - α) * F (1 / hseq k) / f (1 / hseq k)) atTop (𝓝 1) := by
  have hantiPhi : ∀ k, Antitone fun u : ℝ =>
      Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k) :=
    fun k => Phi_antitone hα1 hanti (hpos k) (hfpos k)
  have hae := (ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv).and
    (limitProfile_eq_rpow_ae hα0 hα1 hF0 hanti hrv hmain hpos htend hfpos hLb hLnn hconv)
  have h := tendsto_of_antitone_of_ae_tendsto (g := fun v => v ^ (-α)) hantiPhi
    (hae.mono fun v hv => by beta_reduce at hv; rw [← hv.2]; exact hv.1) one_pos
    (Real.continuousAt_rpow_const 1 (-α) (Or.inl one_ne_zero))
  simpa only [Real.one_rpow] using h

/-! ### The strict Tauberian converse -/

/-- **Every sequence has a subsequence along which the profile converges at `1`.** -/
theorem exists_subseq_tendsto_Phi_one {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hfpos : ∀ n, 0 < f (1 / hseq n)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun k => Real.Gamma (1 - α) * F (1 / hseq (ns k)) / f (1 / hseq (ns k)))
        atTop (𝓝 1) := by
  obtain ⟨L, ns, hns, hL, hconv⟩ :=
    exists_rational_limit hα1 hF0 hanti hrv hmain hpos htend
  exact ⟨ns, hns, tendsto_Phi_one_of_rational_limit hα0 hα1 hF0 hanti hrv hmain
    (fun k => hpos (ns k)) (htend.comp hns.tendsto_atTop) (fun k => hfpos (ns k))
    (fun q => (hL q).2) (fun q => (hL q).1) hconv⟩

/-- **The strict Tauberian converse, normalised form.** Under the Laplace hypothesis,
`Γ(1 - α) F(1 / h)/f(1 / h) → 1` as `h ↓ 0`. -/
theorem tendsto_Phi_one {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun h : ℝ => Real.Gamma (1 - α) * F (1 / h) / f (1 / h)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine tendsto_of_subseq_tendsto fun y hy => ?_
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hy.eventually self_mem_nhdsWithin).and
    (hy.eventually (eventually_pos_of_tendsto_laplace hF0 hmain)))
  obtain ⟨ns, -, hns⟩ := exists_subseq_tendsto_Phi_one hα0 hα1 hF0 hanti hrv hmain
    (hseq := fun n => y (n + K)) (fun n => (hK (n + K) le_add_self).1)
    ((hy.comp (tendsto_add_atTop_nat K)).mono_right nhdsWithin_le_nhds)
    (fun n => (hK (n + K) le_add_self).2)
  exact ⟨fun n => ns n + K, hns⟩

/-- **Pointwise convergence of the normalised profile.** For every `u > 0`,
`Γ(1 - α) F(u / h)/f(1 / h) → u^{-α}` as `h ↓ 0`. -/
theorem tendsto_Phi_at {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    {u : ℝ} (hu : 0 < u) :
    Tendsto (fun h : ℝ => Real.Gamma (1 - α) * F (u / h) / f (1 / h)) (𝓝[>] (0 : ℝ))
      (𝓝 (u ^ (-α))) := by
  have hinv : Tendsto (fun h : ℝ => 1/h) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  have hdiv : Tendsto (fun h : ℝ => h / u) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const u).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      exact div_pos hh hu
  have h3 := ((tendsto_Phi_one hα0 hα1 hF0 hanti hrv hmain).comp hdiv).mul
    ((hrv.tendsto hu).comp hinv)
  rw [one_mul] at h3
  refine h3.congr' ?_
  filter_upwards [(hinv.const_mul_atTop hu).eventually hrv.eventually_pos,
    hinv.eventually hrv.eventually_pos] with h h1 h2
  simp only [Function.comp_apply, one_div_div, mul_one_div] at h1 ⊢
  field_simp

/-- **The strict Tauberian converse** (the converse half of Theorem I.2.11 for an antitone
function). Under the Laplace hypothesis, `F(x)/(f(x)/Γ(1 - α)) → 1` as `x → ∞`. -/
theorem tendsto_tail_of_laplace {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun x : ℝ => F x / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun x : ℝ => 1/x) atTop (𝓝[>] (0 : ℝ)) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero
  refine ((tendsto_Phi_one hα0 hα1 hF0 hanti hrv hmain).comp hinv).congr fun x => ?_
  simp only [Function.comp_apply, one_div_one_div]
  rw [div_div_eq_mul_div, mul_comm]

/-! ### The limit profile is the power law at every point -/

/-- **The limit profile equals `u ↦ u^{-α}` at every point of `(0,∞)`.** -/
theorem limitProfile_eq_rpow_all
    {F f : ℝ → ℝ} {α : ℝ} {hseq : ℕ → ℝ} {L : {q : ℚ // 0 < q} → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0))
    (hantiPhi : ∀ k, Antitone fun u : ℝ =>
      Real.Gamma (1 - α) * F (u / hseq k) / f (1 / hseq k))
    (hLb : ∀ q : {q : ℚ // 0 < q},
      L q ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * (q : ℝ) ^ (-α)))
    (hconv : ∀ q : {q : ℚ // 0 < q},
      Tendsto (fun k => Real.Gamma (1 - α) * F ((q : ℝ) / hseq k) / f (1 / hseq k))
        atTop (𝓝 (L q))) :
    ∀ u : ℝ, 0 < u →
      sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x} = u ^ (-α) := by
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall hpos⟩
  have hgood : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, v < (q : ℝ) ∧ L q = x} = v ^ (-α) := by
    filter_upwards [ae_tendsto_limitProfile hα0 hα1 hantiPhi hLb hconv,
      ae_restrict_mem measurableSet_Ioi] with v hv (hv0 : 0 < v)
    exact tendsto_nhds_unique hv ((tendsto_Phi_at hα0 hα1 hF0 hanti hrv hmain hv0).comp hseq_mem)
  intro u hu
  have hcont := Real.continuousAt_rpow_const u (-α) (Or.inl hu.ne')
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_of_forall_pos_le_add fun ε hε => ?_)
  · obtain ⟨a, ha0, hau, haP, haε⟩ := exists_good_lt hgood hu hcont hε
    have h1 := limitProfile_antitone hα0 hα1 hLb a u ha0 hau.le
    rw [haP] at h1
    linarith
  · obtain ⟨b, hbu, hbP, hbε⟩ := exists_good_gt hgood hu hcont hε
    have h1 := limitProfile_antitone hα0 hα1 hLb u b hu hbu.le
    rw [hbP] at h1
    linarith

/-- **The Tauberian converse, complete form.** Under the hypotheses of Theorem I.2.11 and for
any positive sequence `hseq → 0`, there are rational limit values `L` of the normalised profiles
and a renumbering `ns` such that the limit profile `u ↦ sup {L q : q > u}` is `u ↦ u^{-α}` at
every point of `(0,∞)` (hence a.e.), and `Γ(1 - α) F(1/hseq (ns n))/f(1/hseq (ns n)) → 1`. -/
theorem exists_limitProfile_eq_rpow_and_tendsto_one {F f : ℝ → ℝ} {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hF0 : ∀ x, 0 ≤ F x) (hanti : Antitone F)
    (hrv : RegularlyVarying (-α) f)
    (hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * F (u / h)) / f (1 / h)) (𝓝[>] 0) (𝓝 1))
    {hseq : ℕ → ℝ} (hpos : ∀ n, 0 < hseq n) (htend : Tendsto hseq atTop (𝓝 0)) :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ q : {q : ℚ // 0 < q},
        0 ≤ L q ∧ L q ≤ Real.Gamma (1 - α) * ((3 / 2) * Real.exp 1 * (q : ℝ) ^ (-α))) ∧
      (∀ q : {q : ℚ // 0 < q},
        Tendsto (fun k => Real.Gamma (1 - α) * F ((q : ℝ) / hseq (ns k)) / f (1 / hseq (ns k)))
          atTop (𝓝 (L q))) ∧
      (∀ u : ℝ, 0 < u →
        sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x} = u ^ (-α)) ∧
      ((fun u : ℝ => sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x})
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u : ℝ => u ^ (-α)) ∧
      Tendsto (fun n => Real.Gamma (1 - α) * F (1 / hseq (ns n)) / f (1 / hseq (ns n)))
        atTop (𝓝 1) := by
  have hseq_mem : Tendsto hseq atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall hpos⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1
    (hseq_mem.eventually (eventually_pos_of_tendsto_laplace hF0 hmain))
  obtain ⟨L, ns, hns, hL, hconv⟩ := exists_rational_limit hα1 hF0 hanti hrv hmain
    (hseq := fun n => hseq (n + K)) (fun n => hpos (n + K)) (htend.comp (tendsto_add_atTop_nat K))
  have hns' : StrictMono fun n => ns n + K := fun a b hab => Nat.add_lt_add_right (hns hab) K
  have hall := limitProfile_eq_rpow_all hα0 hα1 hF0 hanti hrv hmain
    (hseq := fun n => hseq (ns n + K)) (fun n => hpos (ns n + K))
    (htend.comp hns'.tendsto_atTop)
    (fun k => Phi_antitone hα1 hanti (hpos _) (hK (ns k + K) le_add_self))
    (fun q => (hL q).2) hconv
  refine ⟨L, fun n => ns n + K, hns', hL, hconv, hall, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hall u hu
  · exact (tendsto_Phi_one hα0 hα1 hF0 hanti hrv hmain).comp
      (hseq_mem.comp hns'.tendsto_atTop)

/-- The hypotheses of `exists_limitProfile_eq_rpow_and_tendsto_one` are satisfiable:
`α = 0`, `F ≡ 1`, `f ≡ 1`, `hseq n = 1/(n+1)`. -/
example :
    ∃ (L : {q : ℚ // 0 < q} → ℝ) (ns : ℕ → ℕ),
      (∀ u : ℝ, 0 < u →
        sSup {x : ℝ | ∃ q : {q : ℚ // 0 < q}, u < (q : ℝ) ∧ L q = x} = u ^ (-(0 : ℝ))) ∧
      Tendsto (fun n => Real.Gamma (1 - 0) * (fun _ : ℝ => (1 : ℝ)) (1 / (1 / ((ns n : ℝ) + 1)))
        / (fun _ : ℝ => (1 : ℝ)) (1 / (1 / ((ns n : ℝ) + 1)))) atTop (𝓝 1) := by
  have hrv : RegularlyVarying (-(0 : ℝ)) (fun _ : ℝ => (1 : ℝ)) := by
    simpa only [neg_zero] using
      slowlyVarying_iff_regularlyVarying_zero.1 (slowlyVarying_const one_pos)
  have hmain : Tendsto (fun h : ℝ =>
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * (fun _ : ℝ => (1 : ℝ)) (u / h))
        / (fun _ : ℝ => (1 : ℝ)) (1 / h)) (𝓝[>] 0) (𝓝 1) := by
    simp only [mul_one, div_one, integral_exp_neg_Ioi_zero]
    exact tendsto_const_nhds
  obtain ⟨L, ns, -, -, -, hall, -, hlim⟩ :=
    exists_limitProfile_eq_rpow_and_tendsto_one le_rfl zero_lt_one (fun _ => zero_le_one)
      antitone_const hrv hmain (hseq := fun n : ℕ => 1 / ((n:ℝ) + 1))
      (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨L, ns, hall, hlim⟩

/-! ### Theorem I.2.11 -/

/-- **Theorem I.2.11** (Feller XIII.5.2; Hutchcroft, arXiv:2508.18807v1, p. 26). For a
probability measure `μ` on `ℝ` carried by `[0,∞)` and `f` regularly varying of index `-α`,
`0 ≤ α < 1`: `E_μ[1 - e^{-hX}] ~ f(1 / h)` as `h ↓ 0` if and only if
`μ([x,∞)) ~ f(x)/Γ(1 - α)` as `x → ∞`. -/
theorem laplace_asymptotic_iff_tail_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVarying (-α) f) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x => (μ (Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) := by
  refine ⟨tail_ge_asymptotic_of_antitone_kernel_converse μ hμ hα1 hrv
    (fun F _ hanti hF0 _ hk => tendsto_tail_of_laplace hα0 hα1 hF0 hanti hrv hk),
    fun htail => ?_⟩
  -- the Abelian direction, for a globally measurable function agreeing with `f` on a tail
  obtain ⟨a, ha⟩ := hrv.measurable_tail
  obtain ⟨g, hg, hgf⟩ := exists_measurable_eqOn_Ici ha
  have hfg : f =ᶠ[atTop] g := (eventually_ge_atTop a).mono fun x hx => (hgf x hx).symm
  have hinv : Tendsto (fun h : ℝ => 1 / h) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div] using tendsto_inv_nhdsGT_zero
  have h := laplace_tail_asymptotic_of_tail_ge μ hμ hα0 hα1 hg (hrv.congr' hfg)
    (htail.congr' (hfg.mono fun x hx => by simp only [hx]))
  exact h.congr' ((hinv.eventually hfg).mono fun h hh => by simp only [hh])

/-- **Theorem I.2.11 for the power law** `f x = x^{-α}`. -/
theorem laplace_asymptotic_iff_tail_ge_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / ((1 / h) ^ (-α)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x => (μ (Ici x)).toReal / (x ^ (-α) / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  laplace_asymptotic_iff_tail_ge μ hμ hα0 hα1 (regularlyVarying_rpow (-α))

/-- **Theorem I.2.11 with the strict tail** `μ((x,∞))`. -/
theorem laplace_asymptotic_iff_tail_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrv : RegularlyVarying (-α) f) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x => (μ (Ioi x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  (laplace_asymptotic_iff_tail_ge μ hμ hα0 hα1 hrv).trans (tendsto_tail_ge_iff_tail_gt μ hα1 hrv)

/-- **Theorem I.2.11 with the strict tail, for the power law** `f x = x^{-α}`. -/
theorem laplace_asymptotic_iff_tail_gt_rpow (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun h : ℝ => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / ((1 / h) ^ (-α)))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
      Tendsto (fun x => (μ (Ioi x)).toReal / (x ^ (-α) / Real.Gamma (1 - α))) atTop (𝓝 1) :=
  laplace_asymptotic_iff_tail_gt μ hμ hα0 hα1 (regularlyVarying_rpow (-α))

/-- **Karamata's Laplace–tail equivalence** (Theorem I.2.11 with a slowly varying function).
Let `X ≥ 0` be a real random variable on a probability space, `0 ≤ α < 1` and `L` slowly
varying. Then `P(X > t) ~ t^{-α} L(t)` as `t → ∞` if and only if
`E[1 - e^{-hX}] ~ Γ(1 - α) h^α L(1 / h)` as `h ↓ 0`. -/
theorem SlowlyVarying.tail_asymptotic_iff_laplace_asymptotic {Ω : Type*} [MeasurableSpace Ω]
    {L : ℝ → ℝ} (hL : SlowlyVarying L) (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) (hX0 : ∀ᵐ ω ∂P, 0 ≤ X ω) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Tendsto (fun t : ℝ => (P {ω | t < X ω}).toReal / (t ^ (-α) * L t)) atTop (𝓝 1) ↔
      Tendsto (fun h : ℝ => (∫ ω, (1 - Real.exp (-(h * X ω))) ∂P) /
        (Real.Gamma (1 - α) * h ^ α * L (1 / h))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hΓ : 0 < Real.Gamma (1 - α) := Real.Gamma_pos_of_pos (by linarith)
  have hμ : P.map X (Iio 0) = 0 := by
    rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iio]
    exact measure_eq_zero_iff_ae_notMem.2 (hX0.mono fun ω h => not_lt.2 h)
  have hrv : RegularlyVarying (-α) (fun x => x ^ (-α) * L x * Real.Gamma (1 - α)) := by
    simpa only [add_zero] using (hL.rpow_mul (-α)).mul
      (slowlyVarying_iff_regularlyVarying_zero.1 (slowlyVarying_const hΓ))
  have h := laplace_asymptotic_iff_tail_gt (P.map X) hμ hα0 hα1 hrv
  refine (tendsto_congr fun t => ?_).trans (h.symm.trans (tendsto_congr' ?_))
  · rw [Measure.map_apply_of_aemeasurable hX measurableSet_Ioi,
      mul_div_cancel_right₀ _ hΓ.ne']
    rfl
  · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    rw [integral_map hX (by fun_prop : Continuous fun s : ℝ =>
      1 - Real.exp (-(h * s))).aestronglyMeasurable, one_div, Real.inv_rpow hh.le,
      Real.rpow_neg hh.le, inv_inv]
    ring

end PercLib.Analysis
