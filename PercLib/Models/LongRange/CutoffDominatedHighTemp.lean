/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file `PercLib/CriticalLRP/CutoffDominated.lean`
(the pointwise domination of Definition I.1.5 and its consequences), source revision
`58b6fe64fc3994d6bf3f9c2b6f673e99d093f44f`
(work/yujinhkim-critical-lrp-orchestration), supplied under its Apache-2.0 header; upstream
`yujinhkim/Critical-Long-range-percolation` at
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf` (not independently verified), licence Apache-2.0 as
declared in that file's header and `third_party/critical-lrp/NOTICE.md`. The mathematical
reference is T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 and p. 7.

Every statement below is at the *same* parameter `β`, for every scale `r > 0`, and no reduced
parameter `β (1 - K r / K 1)` appears: on the canonical bond interface the cut-off kernel of
Definition I.1.5 is already dominated by the uncut kernel at the same intensity
(`PercLib.Models.LongRange.cutoffKernel_le_radialKernel`, landed in
`PercLib/Models/LongRange/Defs.lean`), and both kernels vanish on loops by construction, so the
source's rescaling is not needed. The source needed `r ≥ 1`, a positive profile at `1`, and the
finiteness of the uncut first moment at the reduced parameter as a premise; the first-moment
premise is discharged here in the explicit high-temperature region `β M < 1`, and the bound is
uniform in the scale `r`. Only the first moment is claimed: no higher cluster moment and no
monotonicity in the scale is stated here.

This is a proof-only module: it introduces no definition, no alternative configuration model
and no new axiom.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Models.LongRange.CutoffPowerLaw
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail

/-!
# The cut-off kernel of Definition I.1.5 at high temperature

The cut-off kernel `J_r` of Definition I.1.5 is pointwise below the uncut kernel `J` at the same
parameter, so its off-diagonal rows are dominated by those of `J`. For the power-law profile
`K = powerLawProfile 1 (d + α)` on `ℤ^d` with the sup norm and `α > 0`, the uncut rows are
bounded by the total mass `M = ∑_z ‖z‖^{-d-α}`, hence so are the cut-off rows, for every scale
`r > 0`. The high-temperature results of `PercLib.Percolation.Bond.Intensity` then give the
first moment and the absence of an infinite cluster for the *cut-off* law in the explicit region
`β M < 1`, with a bound that does not depend on `r`.

## Main results

At the same parameter `β` and every scale `r > 0`, for a profile nonnegative on `(0, ∞)`:

* `cutoffProfile_le_self`: `K_r (s) ≤ K s` at `s > 0`;
* `rowSum_cutoffKernel_le`: off-diagonal row sums of `J_r` are at most those of `J`;
* `law_cutoffKernel_le_radialKernel`: `P_{β,r} ⪯ P_β` on every measurable increasing event;
* `tau_cutoffKernel_le_radialKernel`, `chi_cutoffKernel_le_radialKernel`,
  `law_cluster_infinite_cutoffKernel_le_radialKernel`: the pointwise comparisons of `τ`, `χ` and
  of the infinite-cluster event.

With a row bound `M` of the uncut kernel and `β M < 1`, at every scale `r > 0` and every root:

* `chi_cutoffKernel_le_inv_one_sub`: `χ(P_{β,r}) ≤ (1 - β M)⁻¹`;
* `chi_cutoffKernel_lt_top`: `χ(P_{β,r}) < ⊤`;
* `law_exists_infinite_cutoffKernel_eq_zero`: almost surely no infinite cluster.

For the power law `K = powerLawProfile 1 (d + α)`, `α > 0`, with `M = ∑_z ‖z‖^{-d-α}`:

* `rowSum_cutoffKernel_powerLaw_le`: the power-law cut-off rows are at most `M`;
* `chi_cutoffKernel_powerLaw_le_inv_one_sub`,
  `forall_chi_cutoffKernel_powerLaw_le_inv_one_sub`, `chi_cutoffKernel_powerLaw_lt_top`,
  `chi_cutoffKernel_powerLaw_ne_top`: `χ ≤ (1 - β M)⁻¹ < ∞` at every root and every scale,
  uniformly in the scale;
* `law_exists_infinite_cutoffKernel_powerLaw_eq_zero` and
  `law_cluster_infinite_cutoffKernel_powerLaw_eq_zero`: almost surely no infinite cluster;
* `inv_le_rootCriticalIntensity_cutoffKernel_powerLaw`,
  `inv_le_globalCriticalIntensity_cutoffKernel_powerLaw`: the critical intensities of the
  cut-off kernel are at least `M⁻¹`, uniformly in the scale;
* `exists_beta_interval_cutoffKernel_powerLaw_chi_lt_top`: a positive interval on which the
  cut-off first moment is finite at every scale and root.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.LongRange

open PercLib.Analysis

variable {d : ℕ} {N : ModelNorm (Fin d → ℝ)} {K : ℝ → ℝ} {r : ℝ}

/-! ## Row sums of the cut-off kernel -/

/-- **The cut-off profile of Definition I.1.5 is at most the profile itself, at `s > 0`**, for a
profile nonnegative on `(0, ∞)` and a scale `r > 0`: inside the cut-off
`K s - K r ≤ K s`, outside it `0 ≤ K s`. This is the pointwise scalar comparison
`cutoffProfile_dominated` of the source's `KernelGeometry.lean` without the rescaling factor
`(1 - K r / K 1)`, i.e. at the same intensity; it is the profile-level form of
`cutoffKernel_le_radialKernel`. (Not to be confused with `cutoffProfile_of_le`, which unfolds
the `if`.) -/
theorem cutoffProfile_le_self (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    cutoffProfile K r s ≤ K s := by
  by_cases h : s ≤ r
  · rw [cutoffProfile_of_le h]
    linarith [hK r hr]
  · rw [cutoffProfile_of_lt (not_le.1 h)]
    exact hK s hs

/-- **The off-diagonal rows of the cut-off kernel are dominated by those of the uncut kernel**,
at every scale `r > 0` and every vertex `v`. The kernel comparison is
`cutoffKernel_le_radialKernel` (`PercLib/Models/LongRange/Defs.lean`), which uses the
`if x = y then 0` convention on both sides, so no condition on the diagonal of `K` and no
condition on `K 0` enters; the profile only has to be nonnegative on `(0, ∞)`. -/
theorem rowSum_cutoffKernel_le (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r) (v : Fin d → ℤ) :
    rowSum (fun e => (cutoffKernel N K r e : ℝ≥0∞)) v ≤
      rowSum (fun e => (radialKernel N K e : ℝ≥0∞)) v :=
  rowSum_le_rowSum fun w _ =>
    ENNReal.coe_le_coe.2 (cutoffKernel_le_radialKernel hK hr s(v, w))

/-- **The power-law cut-off rows are bounded by the total mass** `M = ∑_z ‖z‖^{-d-α}`, at every
scale `r > 0` and every vertex `v`. The uncut row bound is `power_rowSum_le`
(`PercLib/Percolation/Bond/Exploration/BFS/IntensityMoments.lean`) with the identification
`radialKernel_powerLaw_mk`; the cut-off row is compared with it by
`rowSum_cutoffKernel_le`. -/
theorem rowSum_cutoffKernel_powerLaw_le (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {r : ℝ}
    (hr : 0 < r) (v : Fin d → ℤ) :
    rowSum (fun e => (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r e : ℝ≥0∞)) v ≤
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) := by
  classical
  refine (rowSum_cutoffKernel_le (N := ModelNorm.ofNorm (Fin d → ℝ)) ?_ hr v).trans ?_
  · intro t ht
    exact (powerLawProfile_pos (c := 1) one_pos ht).le
  · rw [rowSum_def]
    exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
      (PercLib.Percolation.Bond.Exploration.BFS.power_rowSum_le hd (by linarith)
        (PercLib.Percolation.Bond.Exploration.BFS.radialKernel_powerLaw_mk hα) v)

/-! ## Comparison of the cut-off law with the uncut law at the same parameter -/

/-- **Stochastic domination of the cut-off law by the uncut law at the same parameter.**
Every measurable increasing event is at least as likely under the uncut profile at `β` as under
the cut-off profile at `β`, for every scale `r > 0`. This is the same-`β` form of the source's
`longRangeMeasure_cutoff_dominated`, whose dominating law sits at the reduced parameter
`β (1 - K r / K 1)`; the coupling used is
`PercLib.Probability.prodBernoulli_mono_event`. -/
theorem law_cutoffKernel_le_radialKernel {A : Set (Config (Fin d → ℤ))} (hA : MeasurableSet A)
    (hup : IsUpperSet A) (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r) (β : ℝ≥0) :
    law (intensityProfile (cutoffKernel N.toSeminorm K r) β) A ≤
      law (intensityProfile (radialKernel N.toSeminorm K) β) A :=
  PercLib.Probability.prodBernoulli_mono_event _ _
    (intensityProfile_le_of_le (fun e => cutoffKernel_le_radialKernel hK hr e) β) hA hup

/-- **The cut-off law's connection probabilities are at most the uncut ones**, at the same
parameter `β` and every scale `r > 0`. -/
theorem tau_cutoffKernel_le_radialKernel (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r)
    (β : ℝ≥0) (x y : Fin d → ℤ) :
    tau (intensityProfile (cutoffKernel N K r) β) x y ≤
      tau (intensityProfile (radialKernel N K) β) x y :=
  tau_le_of_le (fun e => cutoffKernel_le_radialKernel hK hr e) β x y

/-- **The cut-off susceptibility is at most the uncut one**, at the same parameter `β` and every
scale `r > 0`. This is the `same β` form of the source's `lintegral_clusterVol_cutoff_le`, whose
dominating law sits at the reduced parameter `β (1 - K r / K 1)`. -/
theorem chi_cutoffKernel_le_radialKernel (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r)
    (β : ℝ≥0) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel N K r) β) x ≤
      chi (intensityProfile (radialKernel N K) β) x :=
  chi_le_of_le (fun e => cutoffKernel_le_radialKernel hK hr e) β x

/-- **The cut-off law has at most the uncut probability of an infinite cluster**, at the same
parameter `β` and every scale `r > 0` (the same-`β` form of the source's
`infiniteClusterProb_cutoff_le`). -/
theorem law_cluster_infinite_cutoffKernel_le_radialKernel (hK : ∀ t, 0 < t → 0 ≤ K t)
    (hr : 0 < r) (β : ℝ≥0) (x : Fin d → ℤ) :
    law (intensityProfile (cutoffKernel N K r) β) {ω | (cluster ω x).Infinite} ≤
      law (intensityProfile (radialKernel N K) β) {ω | (cluster ω x).Infinite} :=
  law_cluster_infinite_le_of_le (fun e => cutoffKernel_le_radialKernel hK hr e) β x

/-! ## The explicit first moment of a cut-off kernel

A row bound `M` for the uncut kernel is a row bound for every cut-off kernel, so the
high-temperature bound of `PercLib.Percolation.Bond.Intensity` applies to the cut-off law at
every scale, with the same constant. -/

/-- **The high-temperature susceptibility of a cut-off kernel is at most `(1 - β M)⁻¹`**, at
every scale `r > 0`, whenever the *uncut* kernel has off-diagonal rows at most `M` and
`β M < 1`. -/
theorem chi_cutoffKernel_le_inv_one_sub (hK : ∀ t, 0 < t → 0 ≤ K t) {M : ℝ≥0}
    (hM : ∀ v, rowSum (fun e => (radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel N.toSeminorm K r) β) x ≤ (1 - (β : ℝ≥0∞) * M)⁻¹ :=
  chi_intensity_le _ M (fun v => (rowSum_cutoffKernel_le hK hr v).trans (hM v)) β hβ x

/-- **A cut-off kernel has finite first moment at every scale** in the high-temperature region of
the uncut kernel. -/
theorem chi_cutoffKernel_lt_top (hK : ∀ t, 0 < t → 0 ≤ K t) {M : ℝ≥0}
    (hM : ∀ v, rowSum (fun e => (radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel N.toSeminorm K r) β) x < ⊤ :=
  chi_intensity_lt_top _ M (fun v => (rowSum_cutoffKernel_le hK hr v).trans (hM v)) β hβ x

/-- **A cut-off kernel has almost surely no infinite cluster at every scale** in the
high-temperature region of the uncut kernel. -/
theorem law_exists_infinite_cutoffKernel_eq_zero (hK : ∀ t, 0 < t → 0 ≤ K t) {M : ℝ≥0}
    (hM : ∀ v, rowSum (fun e => (radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * M < 1) {r : ℝ} (hr : 0 < r) :
    law (intensityProfile (cutoffKernel N.toSeminorm K r) β)
      {ω | ∃ x, (cluster ω x).Infinite} = 0 :=
  law_exists_infinite_intensity_eq_zero _ M
    (fun v => (rowSum_cutoffKernel_le hK hr v).trans (hM v)) β hβ

/-! ## The explicit first moment of the power-law cut-off law

The mass `M = ∑_z ‖z‖^{-d-α}` is that of `PercLib/Percolation/Bond/PowerLawHighTemp/Tail.lean`.
The only new input is `rowSum_cutoffKernel_powerLaw_le`; the rest is
`PercLib.Percolation.Bond.Intensity`. -/

/-- **The high-temperature susceptibility of the cut-off power law is at most
`(1 - β M)⁻¹`**, at every root and every scale `r > 0`, with `M = ∑_z ‖z‖^{-d-α}` and
`β M < 1`. No reduced parameter and no condition `r ≥ 1` appears, and the bound is uniform in
the scale. -/
theorem chi_cutoffKernel_powerLaw_le_inv_one_sub (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) x ≤
      (1 - (β : ℝ≥0∞) * ((Real.toNNReal
        (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  chi_intensity_le _ _ (rowSum_cutoffKernel_powerLaw_le hd hα hr) β hβ x

/-- **Simultaneous form: the bound holds at every scale and every root at once**, still in the
explicit region `β M < 1`. -/
theorem forall_chi_cutoffKernel_powerLaw_le_inv_one_sub (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) :
    ∀ (r : ℝ), 0 < r → ∀ x : Fin d → ℤ,
      chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) x ≤
        (1 - (β : ℝ≥0∞) * ((Real.toNNReal
          (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  fun r hr x => chi_cutoffKernel_powerLaw_le_inv_one_sub hd hα hβ (r := r) hr x

/-- **The first cluster moment of the cut-off power law is finite** — the susceptibility form. -/
theorem chi_cutoffKernel_powerLaw_lt_top (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) x < ⊤ :=
  chi_intensity_lt_top _ _ (rowSum_cutoffKernel_powerLaw_le hd hα hr) β hβ x

/-- **The first cluster moment of the cut-off power law is finite** — the expected cluster volume
`∫⁻ |K_x| d P_{β,r}`, which is `chi` by definition, is not `⊤`. This is the exact form of the
hypothesis `hχ` that `PercLib/Models/LongRange/InfiniteVolumeRusso.lean` takes as an input for
the cut-off family, discharged at the power law's high-temperature intensities. -/
theorem chi_cutoffKernel_powerLaw_ne_top (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) x ≠ ⊤ :=
  (chi_cutoffKernel_powerLaw_lt_top hd hα hβ hr x).ne

/-! ## No infinite cluster for the cut-off power law in the high-temperature region -/

/-- **Almost surely no cluster is infinite** under the cut-off power law, at every scale
`r > 0`, when `β M < 1`. This is the same-`β`, every-`r` form of the source's
`infiniteClusterProb_cutoff_le` followed by `infiniteClusterProb_cutoff_eq_zero`: the premise
"the uncut law has no infinite cluster" is discharged here by the explicit high-temperature
bound rather than assumed. -/
theorem law_exists_infinite_cutoffKernel_powerLaw_eq_zero (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {r : ℝ} (hr : 0 < r) :
    law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β)
        {ω | ∃ x, (cluster ω x).Infinite} = 0 :=
  law_exists_infinite_intensity_eq_zero _ _
    (rowSum_cutoffKernel_powerLaw_le hd hα hr) β hβ

/-- **The cluster at a fixed root is almost surely finite** under the cut-off power law at every
scale `r > 0`, when `β M < 1`. -/
theorem law_cluster_infinite_cutoffKernel_powerLaw_eq_zero (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    law (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) {ω | (cluster ω x).Infinite} = 0 :=
  law_cluster_infinite_intensity_eq_zero _ _
    (rowSum_cutoffKernel_powerLaw_le hd hα hr) β hβ x

/-! ## The critical intensities of the cut-off power law -/

/-- **The root critical intensity of the cut-off power law is at least `M⁻¹`**, at every root and
every scale `r > 0`. -/
theorem inv_le_rootCriticalIntensity_cutoffKernel_powerLaw (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) (x : Fin d → ℤ) :
    (((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞))⁻¹ ≤
      rootCriticalIntensity (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) x :=
  inv_le_rootCriticalIntensity _ _ (rowSum_cutoffKernel_powerLaw_le hd hα hr) x

/-- **The global critical intensity of the cut-off power law is at least `M⁻¹`**, at every scale
`r > 0`. -/
theorem inv_le_globalCriticalIntensity_cutoffKernel_powerLaw (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {r : ℝ} (hr : 0 < r) :
    (((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞))⁻¹ ≤
      globalCriticalIntensity (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) :=
  inv_le_globalCriticalIntensity _ _ (rowSum_cutoffKernel_powerLaw_le hd hα hr)

/-! ## Non-vacuity

The high-temperature hypothesis `β M < 1` holds at a positive parameter
(`exists_beta_positive_powerLaw`), so the statements above are not vacuous. -/

/-- **A positive parameter interval on which the cut-off first moment is finite at every scale.**
This is the cut-off counterpart of `exists_beta_interval_powerLaw_encard_cluster_pow_ne_top`,
with the *first* moment only. -/
theorem exists_beta_interval_cutoffKernel_powerLaw_chi_lt_top (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ (r : ℝ), 0 < r → ∀ x : Fin d → ℤ,
      chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) x < ⊤ := by
  refine ⟨((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) + 1)⁻¹,
    inv_pos.mpr (by positivity), fun β hβ r hr x => ?_⟩
  exact chi_cutoffKernel_powerLaw_lt_top hd hα
    (PercLib.Percolation.Bond.Exploration.BFS.mul_coe_lt_one_of_lt_inv_add_one hβ) hr x

/-- **Non-vacuity at a positive parameter, every scale.** -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (r : ℝ) (hr : 0 < r)
    (x : Fin d → ℤ) :
    ∃ β : ℝ≥0, 0 < β ∧
      chi (intensityProfile (cutoffKernel (normSeminorm ℝ (Fin d → ℝ))
        (powerLawProfile 1 ((d : ℝ) + α)) r) β) x < ⊤ := by
  obtain ⟨β₀, hβ₀, h⟩ := exists_beta_interval_cutoffKernel_powerLaw_chi_lt_top hd hα
  exact ⟨β₀ / 2, half_pos hβ₀, h (β₀ / 2) (half_lt_self hβ₀) r hr x⟩

end PercLib.Models.LongRange
