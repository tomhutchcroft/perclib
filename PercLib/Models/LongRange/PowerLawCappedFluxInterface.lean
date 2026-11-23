/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied. Mathematical reference:
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1, for the
bounded cut-off derivative formula that is passed to the cap limit here.
-/
module

public import PercLib.Models.LongRange.PowerLawCapMoment
public import PercLib.Models.LongRange.PowerLawPivotalContinuity
public import PercLib.Analysis.MonotoneDerivLimit
public import PercLib.Models.LongRange.InfiniteVolumeRusso

/-!
# The capped-flux interface at the power law

This file records, at the concrete sup-norm power law, the three bounded-input facts that any
derivative-level cap removal (`B → ∞` of the cap) has to stand on, and then performs the
interchange with the general monotone-convergence engine of
`PercLib.Analysis.hasDerivAt_of_monotone_tendsto_deriv`.

* `continuousOn_cappedFlux_powerLaw`: for each cap `B` the capped `p`-th pivotal flux is
  continuous in the cut-off scale on every corner-free window of positive radii. This is the
  bounded-envelope instance of production's `continuousOn_flux_cutoff`; it is the *fixed-cap*
  summability/continuity half, with `2 * B ^ p * M` as the uniform dominator.
* `hasDerivAt_cappedMoment_powerLaw`: for each cap `B` the capped `p`-th cluster moment is
  differentiable in the scale at every scale of the window, with the capped pivotal flux as
  derivative (production's `hasDerivAt_integral_cutoff` at the bounded envelope
  `k ↦ ((k ⊓ B).toNat : ℝ) ^ p`).
* `tendsto_cappedMoment_powerLaw`: the capped moments converge, as `B → ∞`, to the honest
  extended moment `(∫⁻ |K_o| ^ p).toReal` at every positive scale
  (`PercLib.Probability.tendsto_integral_capToNat_pow`).
* `hasDerivAt_uncappedMoment_powerLaw_of_flux`: the resulting **reduction**. If at every scale of
  a corner-free high-temperature window the capped fluxes are monotone in the cap, converge
  pointwise to the uncapped flux, and that uncapped flux is continuous on the window, then the
  uncapped `p`-th moment is differentiable at every scale of the window with derivative the
  uncapped flux. No uniform-in-cap tail estimate is used: the only analytic input is Dini's
  theorem.

## What is *not* claimed

The monotonicity in the cap of the capped fluxes, their pointwise convergence to the uncapped
flux, and the continuity of the uncapped flux are hypotheses of the reduction, not theorems here.
The first two are pointwise monotone convergence of the integrands of a series with a
`B`-independent summable majorant (each capped increment is at most the uncapped one), and the
third is the small-tail (`htail`) input of the programme. No differentiation of the capped limit
is asserted beyond what the reduction states, and no statement is made about natural-number
scales, which are exactly the corners excluded by `hI`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-! ### Fixed-cap continuity of the pivotal flux -/

/-- **The capped pivotal flux is continuous in the scale on a corner-free window.** For the
sup-norm power law `K t = t ^ (-(d + α))`, high temperature `β M < 1`, every order `p`, every root
`o`, every cap `B` and every corner-free window `(u, v)` inside `(0, R)` with finite
susceptibility at `R`, the capped `p`-th pivotal flux is continuous on `(u, v)`.

The proof is production's `continuousOn_flux_cutoff` with the bounded, eventually constant
envelope `F k = ((k ⊓ B).toNat : ℝ) ^ p` and `m = B ^ p`; the dominator is
`2 * B ^ p * ((β * L) * radialKernel_v e * P_v e)`, summable in `e`. -/
theorem continuousOn_cappedFlux_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (o : Fin d → ℤ) {u v R : ℝ} (hu : 0 < u) (huv : u < v) (hvR : v ≤ R)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (B : ℕ) :
    ContinuousOn (fun r => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
          (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v) := by
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hda : 0 ≤ (d : ℝ) + α := by linarith
  have hR : 0 < R := lt_of_lt_of_le (lt_trans hu huv) hvR
  have hcoef : ∀ r : ℝ, -(1 * (-((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1))) =
      ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := fun r => by ring
  have hFm : ∀ n : ℕ∞, |(((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)| ≤ (B : ℝ) ^ p := by
    intro n
    have hle : ((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ≤ (B : ℝ) := by
      have h := ENat.toNat_le_toNat (inf_le_right : n ⊓ (B : ℕ∞) ≤ (B : ℕ∞)) (by simp)
      exact_mod_cast h
    have h0 : (0 : ℝ) ≤ ((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) := by positivity
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 hle p
  have hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n →
      (((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p) = (((⊤ ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p) :=
    ⟨B, fun n hn => by rw [cap_toNat_eq_top B hn]⟩
  have h := continuousOn_flux_cutoff (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one hda)
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add (d := d) 1 α)
    β hFm hF o
    (chi_cutoffKernel_powerLaw_ne_top hd hα hβ hR o) hu hvR
    (corner_free_of_forall_nat_notMem (d := d) hI)
  refine h.congr ?_
  intro r _
  refine tsum_congr fun e => ?_
  simp only [hcoef r, ModelNorm.toSeminorm_ofNorm]

/-! ### The capped derivative at one scale -/

/-- **The capped `p`-th moment is differentiable in the scale with the capped flux as
derivative.** This is production's `hasDerivAt_integral_cutoff` at the bounded, eventually
constant envelope `F k = ((k ⊓ B).toNat : ℝ) ^ p` over the sup-norm power law, on any
corner-free window of positive radii inside `(0, R)` with finite susceptibility at `R`. -/
theorem hasDerivAt_cappedMoment_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (o : Fin d → ℤ) {u v R r₀ : ℝ} (hu : 0 < u) (huv : u < v) (hvR : v ≤ R)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (hr₀ : r₀ ∈ Ioo u v) (B : ℕ) :
    HasDerivAt (fun r => ∫ ω,
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r₀ then 1 else 0) e : ℝ) *
          ((β : ℝ) * (((d : ℝ) + α) * r₀ ^ (-((d : ℝ) + α) - 1)) *
            Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀ e : ℝ))) *
          ∫ ω, ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β))) r₀ := by
  have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hda : 0 ≤ (d : ℝ) + α := by linarith
  have hR : 0 < R := lt_of_lt_of_le (lt_trans hu huv) hvR
  have hcoef : ∀ r : ℝ, -(1 * (-((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1))) =
      ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := fun r => by ring
  have hFm : ∀ n : ℕ∞, |(((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)| ≤ (B : ℝ) ^ p := by
    intro n
    have hle : ((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ≤ (B : ℝ) := by
      have h := ENat.toNat_le_toNat (inf_le_right : n ⊓ (B : ℕ∞) ≤ (B : ℕ∞)) (by simp)
      exact_mod_cast h
    have h0 : (0 : ℝ) ≤ ((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) := by positivity
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ h0 hle p
  have hF : ∃ n₀ : ℕ, ∀ n : ℕ∞, (n₀ : ℕ∞) ≤ n →
      (((n ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p) = (((⊤ ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p) :=
    ⟨B, fun n hn => by rw [cap_toNat_eq_top B hn]⟩
  have h := hasDerivAt_integral_cutoff (N := ModelNorm.ofNorm (Fin d → ℝ))
    (K := powerLawProfile 1 ((d : ℝ) + α))
    (K' := fun t => 1 * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1)))
    (antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one hda)
    (fun t ht => hasDerivAt_powerLawProfile_add 1 α ht)
    (continuousOn_powerLawProfile_deriv_add (d := d) 1 α)
    β hFm hF o
    (chi_cutoffKernel_powerLaw_ne_top hd hα hβ hR o) (lt_trans hu hr₀.1) (hr₀.2.trans_le hvR)
    (fun z hz => by
      obtain ⟨n, hn⟩ := exists_nat_eq_norm z
      rw [ModelNorm.coe_ofNorm, norm_intCast_comp, hn] at hz
      exact hI n (by rw [hz]; exact hr₀))
  simpa only [hcoef, ModelNorm.toSeminorm_ofNorm] using h

/-! ### Cap convergence of the moment at one scale -/

/-- **Cap convergence of the `p`-th power-law cluster moment at a fixed scale.** At every positive
cut-off scale in the high-temperature region `β M < 1`, the real capped `p`-th moments converge as
the cap grows to the honest real moment `(∫⁻ |K_o| ^ p).toReal`. This is
`PercLib.Probability.tendsto_integral_capToNat_pow` with the finite `p`-th moment supplied by
`lintegral_cutoffKernel_powerLaw_pow_ne_top`. -/
theorem tendsto_cappedMoment_powerLaw {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (o : Fin d → ℤ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun B : ℕ => ∫ ω,
        (((cluster ω o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 ((∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal)) :=
  PercLib.Probability.tendsto_integral_capToNat_pow _
    (measurable_encard_cluster o) p
    (lintegral_cutoffKernel_powerLaw_pow_ne_top hd hα hβ hr o p)

/-! ### The derivative-level cap reduction -/

/-- **Derivative-level cap removal at the power law.** Let `(u, v)` be a window of positive
radii inside `(0, R)` containing no value of the sup norm on `ℤ^d` (so no "corner"), and let
`r₀ ∈ (u, v)`.
Assume that at every scale of the window

* the capped `p`-th pivotal fluxes increase with the cap `B`;
* they converge, as `B → ∞`, to the uncapped pivotal flux;
* the uncapped pivotal flux is continuous on the window.

Then the uncapped `p`-th cluster moment is differentiable at `r₀` with derivative the uncapped
pivotal flux. The bounded inputs are proved in this file (`continuousOn_cappedFlux_powerLaw`,
`hasDerivAt_cappedMoment_powerLaw`, `tendsto_cappedMoment_powerLaw`); the analytic upgrade is
Dini's theorem plus `hasDerivAt_of_tendstoLocallyUniformlyOn`, so *no uniform-in-cap tail estimate
of the fluxes is used*. -/
theorem hasDerivAt_uncappedMoment_powerLaw_of_flux {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (o : Fin d → ℤ) {u v R r₀ : ℝ} (hu : 0 < u) (huv : u < v) (hvR : v ≤ R)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (hr₀ : r₀ ∈ Ioo u v)
    (hflux_mono : ∀ r ∈ Ioo u v, Monotone fun B : ℕ =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
    (hflux_lim : ∀ r ∈ Ioo u v, Tendsto (fun B : ℕ =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)))))
    (hflux_cont : ContinuousOn (fun r =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v)) :
    HasDerivAt (fun r => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal)
      (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r₀ then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r₀ ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r₀ e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β))) r₀ :=
  hasDerivAt_of_monotone_tendsto_deriv isOpen_Ioo
    (fun B => continuousOn_cappedFlux_powerLaw hd hα hβ p o hu huv hvR hI B)
    hflux_mono hflux_cont hflux_lim
    (fun B _r hr => hasDerivAt_cappedMoment_powerLaw hd hα hβ p o hu huv hvR hI hr B)
    (fun _r hr => tendsto_cappedMoment_powerLaw hd hα hβ p o (lt_trans hu hr.1)) hr₀

/-- **Derivative-level cap removal at `r₀ = 5/2`.** The nondegenerate scale `5/2` lies in the
corner-free window `(2, 3)`, on which production has finite susceptibility. The hypotheses are the
same three flux inputs, now on `(2, 3)`. -/
theorem hasDerivAt_uncappedMoment_powerLaw_five_halves_of_flux {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (p : ℕ) (o : Fin d → ℤ)
    (hflux_mono : ∀ r ∈ Ioo (2 : ℝ) 3, Monotone fun B : ℕ =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
    (hflux_lim : ∀ r ∈ Ioo (2 : ℝ) 3, Tendsto (fun B : ℕ =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, ((((cluster (insert e ω) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p -
            (((cluster (ω \ {e}) o).encard ⊓ (B : ℕ∞) : ℕ∞).toNat : ℝ) ^ p)
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) atTop
      (𝓝 (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β)))))
    (hflux_cont : ContinuousOn (fun r =>
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo (2 : ℝ) 3)) :
    HasDerivAt (fun r => (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal)
      (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < (5 / 2 : ℝ) then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * (5 / 2 : ℝ) ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) (5 / 2 : ℝ) e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (5 / 2 : ℝ)) β))) (5 / 2) :=
  hasDerivAt_uncappedMoment_powerLaw_of_flux (R := 3) hd hα hβ p o (by norm_num) (by norm_num)
    (by norm_num) (fun k hk => by
      have h3 : 2 < k := by exact_mod_cast hk.1
      have h4 : k < 3 := by exact_mod_cast hk.2
      have h5 : k ≤ 2 := by omega
      have h6 : (k : ℝ) ≤ 2 := by exact_mod_cast h5
      exact absurd hk.1 (not_lt.mpr h6))
    ⟨by norm_num, by norm_num⟩ hflux_mono hflux_lim hflux_cont

end PercLib.Models.LongRange
