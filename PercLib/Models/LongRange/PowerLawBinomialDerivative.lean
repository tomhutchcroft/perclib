/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New derived proof-only results; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.1 and the conditional cut-off derivative interface in `TruncatedMoments`.
-/
module

public import PercLib.Models.LongRange.CutoffPowerLawAnalytic
public import PercLib.Models.LongRange.HighTemperatureDerivative
public import PercLib.Models.LongRange.PowerLawPivotalContinuity
public import PercLib.Models.LongRange.TruncatedMoments

/-!
# The power-law cut-off derivative at `r₀ = 3/2`

At the sup-norm power-law profile and on the corner-free nearest-neighbour window
`(5/4, 8/5)`, the recovered binomial derivative retains its uniform root-moment and local small-tail
premises. At high temperature the root-moment premise is discharged by a proved bound, leaving the
small-tail premise explicit. A zero-intensity witness confirms non-vacuity, but supplies no estimate
at positive intensity and no proof of Lemma I.4.1 or sharpness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration
open PercLib.Analysis
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-- **The power-law cut-off binomial derivative at `r₀ = 3/2` (root moment and small tail
visible).** For `α > 0`, any `β ≥ 0`, `p ≥ 1` and the sup-norm power law, the `p`-th
cut-off moment at radius `r` is differentiable at `r = 3/2` with the recovered binomial
derivative, provided (1) a uniform finite `(p+1)`-st root moment bound `M` holds through
`(5/4, 8/5)` and the outer scale `8/5`, and (2) the local small-tail estimate at that same
window. Weighted absolute summability of the pivotal flux is *not* assumed: it is derived
from the root moment bound. -/
theorem hasDerivAt_powerLaw_three_halves_of_root_moment_of_small_tail {d : ℕ}
    {α : ℝ} (hα : 0 < α) (β : ℝ≥0) (p : ℕ) (hp : 1 ≤ p) (M : ℝ≥0∞)
    (hM : M ≠ ⊤)
    (hroot : ∀ r ∈ (Ioo (5 / 4 : ℝ) (8 / 5) ∪ {(8 / 5 : ℝ)} : Set ℝ),
      (∫⁻ ω, ((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ (p + 1)
        ∂law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)) ≤ M)
    (htail : ∀ r₀ ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ ε > 0, ∃ U ∈ 𝓝 r₀,
      ∃ F : Finset (Sym2 (Fin d → ℤ)), ∀ r ∈ U ∩ Ioo (5 / 4 : ℝ) (8 / 5),
        ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
          ‖((radialKernel (normSeminorm ℝ (Fin d → ℝ))
                (fun s => if s < r then 1 else 0) e.1 : ℝ) *
              ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
                  (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
                Real.exp (-(β : ℝ) *
                  (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                    (powerLawProfile 1 ((d : ℝ) + α)) r e.1 : ℝ)))) *
            ∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
              ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖ ≤ ε) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) (3 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (3 / 2)) β)))
      (3 / 2) := by
  let K : ℝ → ℝ := powerLawProfile 1 ((d : ℝ) + α)
  let K' : ℝ → ℝ := fun t => (1 : ℝ) * (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))
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
  have hKa : AntitoneOn K (Ioi 0) :=
    antitoneOn_powerLawProfile_add (c := 1) (α := α) zero_le_one (by positivity)
  have hK' : ∀ t, 0 < t → HasDerivAt K (K' t) t :=
    fun t ht => hasDerivAt_powerLawProfile_add 1 α ht
  have hK'c : ContinuousOn K' (Ioi 0) := continuousOn_powerLawProfile_deriv_add 1 α
  have hcorner : ∀ z : Fin d → ℤ,
      normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ z) ∉ Ioo (5 / 4 : ℝ) (8 / 5) := by
    apply corner_free_of_forall_nat_notMem (d := d)
    intro m hm
    have h1 : (1 : ℝ) < (m : ℝ) := by linarith [hm.1]
    have h2 : (m : ℝ) < 2 := by linarith [hm.2]
    have h1' : 1 < m := by exact_mod_cast h1
    have h2' : m < 2 := by exact_mod_cast h2
    omega
  have habs : ∀ r ∈ Ioo (5 / 4 : ℝ) (8 / 5), Summable fun e => ‖cw r e *
      ∫ ω, (((cluster (insert e ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
        ((cluster (ω \ {e}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ)) K r) β))‖ :=
    summable_norm_cutoff_flux_of_root_succ_moment
      (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := K) (K' := K') β p hp M hM cw hcw
      hcorner (fun r hr => hroot r (Or.inl hr))
  exact hasDerivAt_integral_cutoff_pow_binomial_of_root_succ_moment_of_local_tail
    (N := ModelNorm.ofNorm (Fin d → ℝ)) (K := K) (K' := K') (R := 8 / 5) (u := 5 / 4)
    (v := 8 / 5) (r₀ := 3 / 2) hKa hK' hK'c β p hp M hM cw hcw
    (by norm_num) (by norm_num) (by norm_num) le_rfl hcorner hroot habs htail

/-- **The power-law cut-off binomial derivative at `r₀ = 3/2` (small tail the only input).**
At `β M < 1` with `M = ∑'_z ‖z‖ ^ (-(d + α))`, the uniform root `(p+1)`-st moment bound of
`hasDerivAt_powerLaw_three_halves_of_root_moment_of_small_tail` is furnished by production
`exists_powerLaw_root_succ_moment_bound` at this window, so the local small-tail estimate at
`(5/4, 8/5)` is the only input that is not proved here. Nothing about the small-tail
estimate itself is claimed. -/
theorem hasDerivAt_powerLaw_three_halves_of_small_tail {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal (∑' z : Fin d → ℤ,
      (‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) : ℝ≥0∞) < 1)
    (p : ℕ) (hp : 1 ≤ p)
    (htail : ∀ r₀ ∈ Ioo (5 / 4 : ℝ) (8 / 5), ∀ ε > 0, ∃ U ∈ 𝓝 r₀,
      ∃ F : Finset (Sym2 (Fin d → ℤ)), ∀ r ∈ U ∩ Ioo (5 / 4 : ℝ) (8 / 5),
        ∑' e : ↥(F : Set (Sym2 (Fin d → ℤ)))ᶜ,
          ‖((radialKernel (normSeminorm ℝ (Fin d → ℝ))
                (fun s => if s < r then 1 else 0) e.1 : ℝ) *
              ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
                  (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
                Real.exp (-(β : ℝ) *
                  (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                    (powerLawProfile 1 ((d : ℝ) + α)) r e.1 : ℝ)))) *
            ∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
              ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
              ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                (powerLawProfile 1 ((d : ℝ) + α)) r) β))‖ ≤ ε) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) β)))
      ((β : ℝ) * -((fun t : ℝ => (1 : ℝ) *
          (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) (3 / 2)) *
        ∑ ℓ ∈ Finset.range p, (p.choose ℓ : ℝ) *
          ∫ ω, (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞).toReal) ^ (ℓ + 1) *
            (∑' y : Fin d → ℤ,
              (if normSeminorm ℝ (Fin d → ℝ) (Int.cast ∘ y) ≤ (3 / 2 : ℝ) then (1 : ℝ)
                else 0) *
              (conn (0 : Fin d → ℤ) y)ᶜ.indicator (fun _ => (1 : ℝ)) ω *
              (((cluster ω y).encard : ℝ≥0∞).toReal) ^ (p - ℓ))
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) (3 / 2)) β)))
      (3 / 2) := by
  obtain ⟨M, hM, hroot⟩ := exists_powerLaw_root_succ_moment_bound (d := d) hd hα (β := β) hβ
    0 p (u := 5 / 4) (v := 8 / 5) (R := 8 / 5) (by norm_num) (by norm_num)
  exact hasDerivAt_powerLaw_three_halves_of_root_moment_of_small_tail hα β p hp M hM
    hroot htail

/-- **Non-vacuity of the pinned hypothesis package: `β = 0`.** At zero intensity the
weighted pivotal flux vanishes identically (the scalar rate is `0`), so the local small-tail
estimate holds with `F = ∅`. Together with `0 * M < 1` this makes
`hasDerivAt_powerLaw_three_halves_of_small_tail` applicable without any remaining input, and
its derivative constant `0` is exactly the value recorded here. This checks that the
small-tail hypothesis is satisfiable, not that it holds at positive `β`. -/
theorem hasDerivAt_powerLaw_three_halves_beta_zero {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) (p : ℕ) (hp : 1 ≤ p) :
    HasDerivAt (fun r : ℝ => ∫ ω,
        (((cluster ω (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
        ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
          (powerLawProfile 1 ((d : ℝ) + α)) r) (0 : ℝ≥0)))) 0 (3 / 2) := by
  have h := hasDerivAt_powerLaw_three_halves_of_small_tail (d := d) hd hα (β := 0)
    (by simp) p hp ?_
  · simpa using h
  · intro r₀ _ ε hε
    refine ⟨univ, Filter.univ_mem, ∅, fun r _ => ?_⟩
    have hzero : ∀ e : ↥((∅ : Finset (Sym2 (Fin d → ℤ))) : Set (Sym2 (Fin d → ℤ)))ᶜ,
        ‖((radialKernel (normSeminorm ℝ (Fin d → ℝ))
              (fun s => if s < r then 1 else 0) e.1 : ℝ) *
            (((0 : ℝ≥0) : ℝ) * -((fun t : ℝ => (1 : ℝ) *
                (-((d : ℝ) + α) * t ^ (-((d : ℝ) + α) - 1))) r) *
              Real.exp (-(((0 : ℝ≥0) : ℝ)) *
                (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
                  (powerLawProfile 1 ((d : ℝ) + α)) r e.1 : ℝ)))) *
          ∫ ω, (((cluster (insert e.1 ω) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p -
            ((cluster (ω \ {e.1}) (0 : Fin d → ℤ)).encard : ℝ≥0∞) ^ p).toReal
            ∂(law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
              (powerLawProfile 1 ((d : ℝ) + α)) r) (0 : ℝ≥0)))‖ = 0 := by
      intro e
      simp
    rw [tsum_congr hzero, tsum_zero]
    exact hε.le

end PercLib.Models.LongRange
