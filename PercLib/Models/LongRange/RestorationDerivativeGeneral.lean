/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only result; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1. The cutoff moment derivative is proved below at strictly subcritical parameters
and corner-free scales. These restrictions are not asserted for the source lemma.
-/
module

public import PercLib.Models.LongRange.RestorationDerivative
public import PercLib.Models.LongRange.CutoffExhaustion.Moments
public import PercLib.Percolation.Bond.ZeroIntensityGap
public import PercLib.Models.LongRange.PowerLawCappedFluxInterface
public import PercLib.Analysis.CapFlux.Convergence

/-!
# The restoration/flux derivative at an arbitrary corner-free power-law scale

The published base proves the uncapped binomial derivative of the sup-norm power-law cut-off
moment at `r₀ = 3/2` only, because the restoration-majorant window is stated on `(5/4, 8/5)`.
This file extends the restoration/flux argument to an arbitrary positive, corner-free scale,
and its power-law applications now use strict subcriticality of the uncut law.

Main results:

* `exists_pos_corner_free_interval` — `exists_corner_free_interval` with a positive left endpoint;
* `exists_powerLaw_rate_bound_of_pos` — the rate `|β J'|` on `Ioi u` is bounded by its value at `u`;
* `exists_nhds_htail_powerLaw_of_restoration_general` — the literal local small-tail estimate on
  an arbitrary bounded interval `(u, v)`, from one uniform window at the top scale `v`;
* `continuousOn_flux_powerLaw_of_restoration_general[_of_nat]` — continuity of the whole pivotal
  flux series on an arbitrary bounded corner-free interval, i.e. the `hflux_cont` premise of the
  Dini/cap interface, with no gap factorisation;
* `corner_of_nat_ne_normSeminorm` — a scale that is not a natural number is corner-free;
* `hasDerivAt_powerLaw_of_corner_free` — **the main result**: at every `r₀ > 0` that is not a value
  of the sup norm on `ℤ^d`, the `p`-th cut-off root moment (`p ≥ 1`) is differentiable at `r₀` with
  the full uncapped binomial derivative.  Every other input of production's
  `hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_local_tail` is discharged: no
  `hfac`, no `hwin`, no `hflux_cont`, no root-moment or corner-free-interval hypothesis;
* `hasDerivAt_powerLaw_of_nat_ne`, `hasDerivAt_powerLaw_of_corner_free_interval` — the arithmetic
  and interval forms;
* `hasDerivAt_powerLaw_five_halves` — the instance at `r₀ = 5/2`, a scale not covered by the
  published base;
* `hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval` — the same derivative through the
  independent Dini/cap route: every hypothesis of `hasDerivAt_uncappedMoment_powerLaw_of_flux`
  (`hflux_mono`, `hflux_lim`, `hflux_cont`) is discharged, giving the value-level derivative of
  `ψ(r) = (∫⁻ |K_o| ^ p dμ_r).toReal` on an arbitrary valid corner-free interval;
* `integral_toReal_encard_pow_eq` and `binomial_eq_flux_powerLaw_of_corner_free_interval` — the
  finite-moment bridge between the ordinary-integral and `lintegral`-`toReal` moments, and the
  resulting equality of the binomial and unrestricted-flux derivative values.

## What this file does not claim

The power-law results assume strict subcriticality of the uncut law. Nothing is asserted at
criticality, about all natural scales (a natural `r₀` is a sup-norm corner and remains
excluded), about uniform-in-`r` sharpness, or about the paper's Lemma I.4.1 in full.
-/

@[expose] public section

noncomputable section

open PercLib.Models.LongRange.CutoffExhaustion

open Filter Set MeasureTheory
open PercLib.Percolation.Bond
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

variable {d : ℕ}

/-- **A positive corner-free interval around a corner-free scale.** From production
`exists_corner_free_interval` we keep only the interval and shrink it so that its left endpoint
stays positive. -/
theorem exists_pos_corner_free_interval (N : ModelNorm (Fin d → ℝ)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hcorner : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r₀) :
    ∃ u v : ℝ, 0 < u ∧ u < r₀ ∧ r₀ < v ∧ ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ∉ Ioo u v := by
  obtain ⟨δ, hδ, -, hI⟩ := exists_corner_free_interval N (r₀ := r₀) (R := r₀ + 1) hr₀
    (by linarith) hcorner
  have he0 : 0 < min δ (r₀ / 2) := lt_min hδ (half_pos hr₀)
  have heδ : min δ (r₀ / 2) ≤ δ := min_le_left _ _
  have he2 : min δ (r₀ / 2) ≤ r₀ / 2 := min_le_right _ _
  refine ⟨r₀ - min δ (r₀ / 2), r₀ + min δ (r₀ / 2), by linarith, by linarith, by linarith, ?_⟩
  intro z hz
  exact hI (N (Int.cast ∘ z)) ⟨by linarith [hz.1], by linarith [hz.2]⟩ z rfl

/-- **The rate bound at the power law, from any positive left endpoint.** On `Ioi u` the rate
`|β J'|` is dominated by its value at `u`, because `t ↦ t ^ (-(d+α)-1)` is decreasing. -/
theorem exists_powerLaw_rate_bound_of_pos {α : ℝ} (hα : 0 < α) (β : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∀ r ∈ Ioi u,
      |(β : ℝ) * -((fun t : ℝ => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r)| ≤
        (β : ℝ) * ((d : ℝ) + α) * u ^ (-((d : ℝ) + α) - 1) := by
  intro r hr
  have hdr : (0 : ℝ) < (d : ℝ) + α := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hr0 : (0 : ℝ) < r := lt_trans hu hr
  have hle : r ^ (-((d : ℝ) + α) - 1) ≤ u ^ (-((d : ℝ) + α) - 1) :=
    Real.rpow_le_rpow_of_nonpos hu hr.le (by linarith)
  have hval : (β : ℝ) * -((fun t : ℝ => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) =
      (β : ℝ) * ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := by
    have : -((fun t : ℝ => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) =
        ((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1) := by
      ring
    rw [this, mul_assoc]
  rw [hval, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hle (by positivity)


open Classical in
/-- **The local small-tail estimate at the sup-norm power law on an arbitrary bounded interval.**

For `1 ≤ d`, `α > 0`, strict subcriticality of the uncut law, every order `p ≥ 1`,
every root `o` and every `r₀` in a positive interval `(u, v)`, the real-norm tail of the cut-off
pivotal series outside one finite pair set is arbitrarily small on a neighbourhood of `r₀` inside
`(u, v)`.  This is the published `exists_nhds_htail_powerLaw_of_restoration` with `(5/4, 8/5)`
replaced by `(u, v)`: the finite range set is read at the top scale `v`, the uniform window comes
from `exists_window_uniform_hwin`, and the rate is bounded by its value at the left endpoint `u`.
No corner hypothesis is needed for the tail alone. -/
theorem exists_nhds_htail_powerLaw_of_restoration_general {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) (o : Fin d → ℤ) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (r₀ : ℝ) (hr₀ : r₀ ∈ Ioo u v) (ε : ℝ) (hε : 0 < ε) :
    ∃ U ∈ 𝓝 r₀, ∃ F : Finset (Sym2 (Fin d → ℤ)),
      ∀ r ∈ U ∩ Ioo u v, ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖((radialKernel (normSeminorm ℝ (Fin d → ℝ))
              (fun s => if s < r then 1 else 0) e.1 : ℝ) *
            ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
                (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
              Real.exp (-(β : ℝ) *
                (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                  (powerLawProfile 1 ((d : ℝ) + α)) r e.1 : ℝ)))) *
          ∫ ω, (((cluster (insert e.1 ω) o).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) o).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖ ≤ ε := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  have hK : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hvpos : (0 : ℝ) < v := lt_trans hu huv
  obtain ⟨M, hM, hroot⟩ := exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ o p
    (u := u) (v := v) (R := v) hu hvpos
  have hmomv : rootMoment (law (intensityProfile (cutoffKernel (d := d) N K v) β)) o p
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top hM (le_trans (rootMoment_le_of_le _ o (Nat.le_succ p)) ?_)
    simpa only [rootMoment, N, K, ModelNorm.toSeminorm_ofNorm] using hroot v (Or.inr rfl)
  obtain ⟨S, hS⟩ := exists_finset_norm_lt (N := N) v
  have hS' : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) < v → z ∈ S := by
    intro z hz
    exact hS z (by simpa only [N, ModelNorm.toSeminorm_ofNorm] using hz)
  have hε'pos : 0 < ε / ((β : ℝ) * ((d : ℝ) + α) * u ^ (-((d : ℝ) + α) - 1) + 1) :=
    div_pos hε (by positivity)
  set Λ : ℝ := (β : ℝ) * ((d : ℝ) + α) * u ^ (-((d : ℝ) + α) - 1) with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  obtain ⟨W, hW⟩ := exists_window_uniform_hwin (N := N) (K := K) hK S hS' o p hp hmomv
    (δ := ENNReal.ofReal (ε / (Λ + 1))) (ENNReal.ofReal_pos.2 hε'pos)
  have hins : ∀ r ∈ Iio v ∩ Ioo u v, ∀ e : Sym2 (Fin d → ℤ),
      (∫⁻ ω, ((cluster (insert e ω) o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
    intro r hr e
    have hrv : r ∈ Ioo u v := hr.2
    have h1 : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hM (le_trans (rootMoment_le_of_le _ o (Nat.le_succ p)) ?_)
      simpa only [rootMoment, N, K, ModelNorm.toSeminorm_ofNorm] using hroot r (Or.inl hrv)
    have h10 : (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ := by
      have hrootind := lintegral_encard_pow_cutoffKernel_eq (d := d) (N := N.toSeminorm)
        (K := K) r β p o 0
      rw [← hrootind]
      exact h1
    have h3 : ∀ y : Fin d → ℤ, (∫⁻ ω, ((cluster ω y).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≠ ⊤ :=
      fun y => vertex_moment_ne_top_of_root_moment (N := N) (K := K) β r p y h10
    exact insert_moments_of_vertex_moments (N := N.toSeminorm) (K := K) β p r o h3 e
  refine exists_nhds_window_htail_of_uniform_lintegral_window_tail (N := N) (K := K) (K' := K')
    β p hp o _ (fun _ _ => rfl) W hr₀ (Iio v) (isOpen_Iio.mem_nhds hr₀.2) ε
    (fun _ => ENNReal.ofReal (ε / (Λ + 1))) ?_ hins ?_ ?_
  · intro r hr
    exact ENNReal.ofReal_ne_top
  · intro r hr
    have hrv : r ∈ Ioo u v := hr.2
    have h := hW r (le_of_lt hrv.2)
    simpa only [indicatorPairWeight_def, N, K, ModelNorm.toSeminorm_ofNorm] using h
  · intro r hr
    have hrv : r ∈ Ioo u v := hr.2
    have hle : |(β : ℝ) * -K' r| ≤ Λ := by
      rw [hΛdef]
      simpa only [K'] using exists_powerLaw_rate_bound_of_pos (d := d) hα β hu r hrv.1
    have hE : (ENNReal.ofReal (ε / (Λ + 1))).toReal = ε / (Λ + 1) :=
      ENNReal.toReal_ofReal hε'pos.le
    rw [hE]
    calc |(β : ℝ) * -K' r| * (ε / (Λ + 1)) ≤ Λ * (ε / (Λ + 1)) :=
          mul_le_mul_of_nonneg_right hle hε'pos.le
      _ = ε * (Λ / (Λ + 1)) := by field_simp
      _ ≤ ε * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hε.le
          exact (div_lt_one (by linarith : (0 : ℝ) < Λ + 1)).2 (by linarith) |>.le
      _ = ε := mul_one ε


/-- **Corner-freeness at a scale that is not a natural number.** Since every sup-norm value on
`ℤ^d` is a natural number, the arithmetic condition `∀ n : ℕ, (n : ℝ) ≠ r₀` discharges the
corner hypothesis of the derivative interface at the single scale `r₀`. -/
theorem corner_of_nat_ne_normSeminorm {d : ℕ} {r₀ : ℝ} (hne : ∀ n : ℕ, (n : ℝ) ≠ r₀) :
    ∀ z : Fin d → ℤ, normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) ≠ r₀ := by
  intro z
  obtain ⟨n, hn⟩ := exists_nat_eq_norm z
  rw [normSeminorm_intCast, hn]
  exact hne n

open Classical in
/-- **The uncapped binomial derivative of the power-law cut-off moment at an arbitrary positive
corner-free scale.**

For `1 ≤ d`, `α > 0`, strict subcriticality of the uncut law, every order `p ≥ 1` and
every `r₀ > 0` that is *not* a value of the sup norm on `ℤ^d`, the `p`-th cut-off root moment is
differentiable at `r₀`, with the full binomial derivative.  Every hypothesis of
`hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_local_tail` is discharged here:

* the corner-free interval comes from `exists_corner_free_interval` (shrunk to keep `u > 0`);
* the uniform root `(p+1)`-st moment bound comes from
  `exists_uniform_root_succ_moment_bound_of_lt_globalCritical`;
* pointwise absolute summability of the weighted pivotal flux comes from
  `summable_norm_cutoff_flux_of_root_succ_moment`;
* the local small-tail estimate comes from
  `exists_nhds_htail_powerLaw_of_restoration_general`.

No `hfac`, `hwin`, or `hflux_cont` and no corner-free-interval hypothesis is left in the statement;
the single-scale corner-freeness hypothesis `hfree` remains explicit. -/
theorem hasDerivAt_powerLaw_of_corner_free {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hfree : ∀ z : Fin d → ℤ, normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) ≠ r₀) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r₀) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ r₀ then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β)))
      r₀ := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  have hKa : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t :=
    fun t ht => hasDerivAt_powerLawProfile_add 1 α ht
  have hK'c : ContinuousOn K' (Ioi 0) := continuousOn_powerLawProfile_deriv_add 1 α
  have hfreeN : ∀ z : Fin d → ℤ, N (Int.cast ∘ z) ≠ r₀ := by
    intro z
    exact hfree z
  obtain ⟨u, v, hu, hur, hrv, hcorner⟩ :=
    exists_pos_corner_free_interval N hr₀ hfreeN
  obtain ⟨M, hM, hroot⟩ := exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := u) (v := v) (R := v) hu (lt_trans hu (lt_trans hur hrv))
  have hroot' : ∀ r ∈ (Ioo u v ∪ {v} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
    intro r hr
    simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot r hr
  let cw : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun r e =>
    (radialKernel (ModelNorm.ofNorm (Fin d → ℝ))
        (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * -K' r *
        Real.exp (-(β : ℝ) * (cutoffKernel (ModelNorm.ofNorm (Fin d → ℝ)) K r e : ℝ)))
  have hcw : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)), cw r e =
      (radialKernel (ModelNorm.ofNorm (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -K' r *
          Real.exp (-(β : ℝ) * (cutoffKernel (d := d)
            (ModelNorm.ofNorm (Fin d → ℝ)) K r e : ℝ))) := fun _ _ => rfl
  have habs : ∀ r ∈ Ioo u v, Summable fun e => ‖cw r e *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) K r) β))‖ :=
    summable_norm_cutoff_flux_of_root_succ_moment
      (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := K) (K' := K') β p hp M hM cw hcw
      hcorner (fun r hr => hroot' r (Or.inl hr))
  exact hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_local_tail
    (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := K) (K' := K') (R := v) (u := u) (v := v)
    (r₀ := r₀) hKa hK' hK'c β p hp M hM cw hcw hu hur hrv le_rfl hcorner hroot' habs
    (fun r₀' hr₀' ε hε =>
      exists_nhds_htail_powerLaw_of_restoration_general hd hα hβ p hp 0 hu
        (lt_trans hur hrv) r₀' hr₀' ε hε)


open Classical in
/-- **The uncapped binomial derivative at any positive scale that is not a natural number.**
The corner hypothesis is discharged arithmetically: sup-norm values on `ℤ^d` are natural
numbers. -/
theorem hasDerivAt_powerLaw_of_nat_ne {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hne : ∀ n : ℕ, (n : ℝ) ≠ r₀) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r₀) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ r₀ then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β)))
      r₀ :=
  hasDerivAt_powerLaw_of_corner_free hd hα hβ p hp hr₀ (corner_of_nat_ne_normSeminorm hne)

open Classical in
/-- **The uncapped binomial derivative at `r₀ = 5/2`.** The published base proves the small-tail
estimate only on `(5/4, 8/5)`, so this scale is not covered there; it is an instance of
`hasDerivAt_powerLaw_of_corner_free`.  `5/2` is not a sup-norm value on `ℤ^d`. -/
theorem hasDerivAt_powerLaw_five_halves {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) (5 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (5 / 2) then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (5 / 2)) β)))
      (5 / 2) := by
  refine hasDerivAt_powerLaw_of_nat_ne hd hα hβ p hp (by norm_num) ?_
  intro n hn
  have h2 : (2 * n : ℝ) = 5 := by rw [hn]; norm_num
  have h3 : 2 * n = 5 := by exact_mod_cast h2
  omega


open Classical in
/-- **Continuity of the whole pivotal flux series on an arbitrary bounded corner-free interval.**

This is production's `continuousOn_flux_powerLaw_of_restoration` with `(5/4, 8/5)` replaced by
`(u, v)`: every input of `continuousOn_flux_cutoff_of_root_succ_moment_of_local_tail` is
constructed from the restoration bounds, with the local small tail taken from
`exists_nhds_htail_powerLaw_of_restoration_general`.  This is the `hflux_cont` premise of
`hasDerivAt_uncappedMoment_powerLaw_of_flux` on that interval. -/
theorem continuousOn_flux_powerLaw_of_restoration_general {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hcorner : ∀ z : Fin d → ℤ, normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) ∉ Ioo u v) :
    ContinuousOn (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(β : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v) := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
  let N : ModelNorm (Fin d → ℝ) := ModelNorm.ofNorm (Fin d → ℝ)
  have hKa : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t :=
    fun t ht => hasDerivAt_powerLawProfile_add 1 α ht
  have hK'c : ContinuousOn K' (Ioi 0) := continuousOn_powerLawProfile_deriv_add (d := d) 1 α
  obtain ⟨M, hM, hroot⟩ := exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := u) (v := v) (R := v) hu (lt_trans hu huv)
  have hroot' : ∀ r ∈ (Ioo u v ∪ {v} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂(law (intensityProfile (cutoffKernel (d := d) N K r) β))) ≤ M := by
    intro r hr
    simpa only [N, K, ModelNorm.toSeminorm_ofNorm] using hroot r hr
  exact continuousOn_flux_cutoff_of_root_succ_moment_of_small_tail (N := N) (K := K) (K' := K')
    hKa hK' hK'c β p hp M hM _ (fun _ _ => rfl) (u := u) (v := v) (R := v)
    hu le_rfl hcorner hroot'
    (fun r₀ hr₀ ε hε => exists_nhds_htail_powerLaw_of_restoration_general hd hα hβ p hp 0 hu
      huv r₀ hr₀ ε hε)

/-- The arithmetic form: an interval containing no natural number is corner-free, so the flux is
continuous there.  Matches the `hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v` shape of
`hasDerivAt_uncappedMoment_powerLaw_of_flux`. -/
theorem continuousOn_flux_powerLaw_of_restoration_general_of_nat {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {u v : ℝ} (hu : 0 < u) (huv : u < v)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) :
    ContinuousOn (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      ((radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r then 1 else 0) e : ℝ) *
        ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
            (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
          Real.exp (-(β : ℝ) *
            (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ)))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v) :=
  continuousOn_flux_powerLaw_of_restoration_general hd hα hβ p hp hu huv
    (corner_free_of_forall_nat_notMem (d := d) hI)


open Classical in
/-- **The uncapped binomial derivative on an arbitrary valid corner-free scale interval.**

`(u, v)` is a *valid corner-free interval* in the sense of the paper: it contains no natural
number, hence no value of the sup norm on `ℤ^d`.  Every interior point `r₀` of such an interval is
a corner-free scale, so `hasDerivAt_powerLaw_of_corner_free` applies.  This is the interval form of
the generalisation, matching the phrase "arbitrary valid corner-free power-law scale interval". -/
theorem hasDerivAt_powerLaw_of_corner_free_interval {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {u v r₀ : ℝ} (hu : 0 < u)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (hr₀ : r₀ ∈ Ioo u v) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r₀) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ r₀ then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β)))
      r₀ := by
  refine hasDerivAt_powerLaw_of_corner_free hd hα hβ p hp (lt_trans hu hr₀.1) ?_
  intro z hz
  exact corner_free_of_forall_nat_notMem (d := d) hI z (hz ▸ hr₀)


open Classical in
/-- **The value-level uncapped derivative on an arbitrary valid corner-free interval (cap route).**

`hasDerivAt_uncappedMoment_powerLaw_of_flux` leaves three flux inputs open.  All three are proved
here: monotonicity in the cap and the cap limit at the root are
`hflux_mono_powerLaw_zero_toNat` and `hflux_lim_powerLaw_zero_toNat`, and continuity of the whole
flux series is `continuousOn_flux_powerLaw_of_restoration_general_of_nat`.  The result is the
paper's value-level derivative `ψ'(r₀) = ∑_e c_{r₀}(e) PI_e(r₀)` at every interior point of a valid
corner-free interval. Strict subcriticality and the dimensional and geometric inputs remain
explicit; no additional analytic hypothesis is needed. -/
theorem hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {u v r₀ : ℝ} (hu : 0 < u) (huv : u < v)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (hr₀ : r₀ ∈ Ioo u v) :
    HasDerivAt (fun r => (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal)
      (∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r₀ then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r₀ ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r₀ e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β))) r₀ := by
  have hcont : ContinuousOn (fun r : ℝ => ∑' e : Sym2 (Fin d → ℤ),
      (radialKernel (normSeminorm ℝ (Fin d → ℝ)) (fun s => if s < r then 1 else 0) e : ℝ) *
      ((β : ℝ) * (((d : ℝ) + α) * r ^ (-((d : ℝ) + α) - 1)) *
        Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ))) *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) (Ioo u v) := by
    refine (continuousOn_flux_powerLaw_of_restoration_general_of_nat hd hα hβ p hp hu huv
      hI).congr (fun r _ => ?_)
    refine tsum_congr fun e => ?_
    simp only [one_mul, neg_mul, neg_neg]
  exact hasDerivAt_uncappedMoment_powerLaw_of_flux (R := v) hd hα hβ p (0 : Fin d → ℤ)
    hu huv le_rfl hI hr₀
    (PercLib.Analysis.CapFlux.hflux_mono_powerLaw_zero_toNat hd hα hβ hp hu huv hI)
    (PercLib.Analysis.CapFlux.hflux_lim_powerLaw_zero_toNat hd hα hβ hp hu huv hI) hcont

/-- For a finite `p`-th root moment, the ordinary integral of its real value is the `toReal` of
its extended integral. This identifies the carriers used by the binomial and cap-flux derivative
interfaces without converting a possibly infinite moment to a real number. -/
theorem integral_toReal_encard_pow_eq {d : ℕ} (o : Fin d → ℤ) (p : ℕ) {α r : ℝ} {β : ℝ≥0}
    (hfin : (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
      ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β))) ≠ ⊤) :
    ∫ ω, (((cluster ω o).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) =
      (∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal :=
  integral_toReal ((measurable_encard_cluster_toENNReal o).pow_const p).aemeasurable
    (ae_lt_top ((measurable_encard_cluster_toENNReal o).pow_const p) hfin)

open Classical in
/-- On a valid corner-free interval, the binomial pivotal form and the unrestricted pair-series
form of the derivative are equal. Both theorems differentiate the same finite-moment function:
the ordinary integral and `lintegral`-`toReal` expressions agree locally, so uniqueness of the
derivative identifies their values. -/
theorem binomial_eq_flux_powerLaw_of_corner_free_interval {d : ℕ} (hd : 1 ≤ d)
    {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) < globalCriticalIntensity
      (radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α))))
    (p : ℕ) (hp : 1 ≤ p) {u v r₀ : ℝ} (hu : 0 < u) (huv : u < v)
    (hI : ∀ k : ℕ, (k : ℝ) ∉ Ioo u v) (hr₀ : r₀ ∈ Ioo u v) :
    (β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
        (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r₀) *
      ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
        ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
          (∑' y : Fin d → ℤ,
            (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ r₀ then (1 : ℝ)
              else 0) *
            (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
            (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
          ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r₀) β)) =
      ∑' e : Sym2 (Fin d → ℤ),
        (radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (fun s => if s < r₀ then 1 else 0) e : ℝ) *
        ((β : ℝ) * (((d : ℝ) + α) * r₀ ^ (-((d : ℝ) + α) - 1)) *
          Real.exp (-(β : ℝ) * (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
            (powerLawProfile 1 ((d : ℝ) + α)) r₀ e : ℝ))) *
        ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r₀) β)) := by
  obtain ⟨M, hM, hroot⟩ := exists_uniform_root_succ_moment_bound_of_lt_globalCritical
    (d := d) hd hα (β := β) hβ
    (0 : Fin d → ℤ) p (u := u) (v := v) (R := v) hu (lt_trans hu huv)
  have hfin : ∀ r ∈ Ioo u v,
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) ≠ ⊤ := by
    intro r hr
    refine ne_top_of_le_ne_top hM ?_
    exact le_trans (rootMoment_le_of_le _ (0 : Fin d → ℤ) (Nat.le_succ p))
      (hroot r (Or.inl hr))
  have heq : (fun r : ℝ => (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))).toReal)
      =ᶠ[𝓝 r₀] (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β))) := by
    filter_upwards [Ioo_mem_nhds hr₀.1 hr₀.2] with r hr
    exact (integral_toReal_encard_pow_eq (0 : Fin d → ℤ) p (hfin r hr)).symm
  refine ((hasDerivAt_powerLaw_of_corner_free_interval (d := d) hd hα hβ p hp
    (u := u) (v := v) (r₀ := r₀) hu hI hr₀).congr_of_eventuallyEq heq).unique
    (hasDerivAt_uncappedMoment_powerLaw_of_corner_free_interval (d := d) hd hα hβ p hp
      (u := u) (v := v) (r₀ := r₀) hu huv hI hr₀)

end PercLib.Models.LongRange
