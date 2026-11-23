/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Definitions used here are those of `PercLib/Models/LongRange/Defs.lean` in this worktree
(production base `2471b808cd0f1b79dc8a1ba514d43e63b9b9595c`): the radial kernel, the cut-off
profile `J_r(s) = 1{s ≤ r} (K s - K r)` and the cut-off kernel of Definition I.1.5 of
T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, adapted as recorded in
that file's header from `yujinhkim/lrp`, `PercLib/CriticalLRP/KernelGeometry.lean`, revision
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc` (Apache-2.0). The law and susceptibility are those
of `PercLib/Percolation/Bond/Basic.lean` (`law`, `chi`), and the profile comparison machinery is
that of `PercLib/Percolation/Bond/IntensityScaling.lean` (`intensityProfile_le_of_le`,
`chi_le_of_le`) and `PercLib/Percolation/Bond/Intensity.lean` (`chi_intensity_le`).

Every declaration below is new. Nothing is copied from the source repository: the two geometric
monotonicity lemmas already landed in `Models/LongRange/Defs.lean` (`monotone_cutoffProfile`,
`monotone_cutoffKernel`) are *used*, not reproved, and the comparison theorems of
`Bond/IntensityScaling.lean` are applied rather than repeated. This is a proof-only module.
-/
module

public import PercLib.Models.LongRange.Defs
public import PercLib.Percolation.Bond.IntensityScaling
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Models.LongRange.CutoffDominatedHighTemp

/-!
# The cut-off family is monotone in the cut-off scale

For a profile `K` decreasing on `(0, ∞)`, the cut-off family `r ↦ J_r` of Definition I.1.5 is
nondecreasing at every pair, so every monotone functional of the open configuration — the edge
intensity, the two-point function, the susceptibility, the probability of an infinite cluster and
the critical intensities — is monotone in `r` as well. This file records the resulting
`r`-monotonicity for the current definitions, together with the exact side conditions:

* the hypothesis is `AntitoneOn K (Ioi 0)` only: no nonnegativity, no continuity, no
  differentiability and no value on the diagonal is used;
* the diagonal is `0` at every scale, so it never decides the comparison;
* `r ≤ 0` is admissible; the `if s ≤ r` branch of `cutoffProfile` and the truncation
  `Real.toNNReal` are handled by the existing profile lemma;
* no high-temperature hypothesis is needed for the comparison itself. The parameter enters only
  through the explicit bound and the almost-sure finiteness, which are stated here for a general
  row bound `M` so that a concrete kernel supplies its own mass.

The hypothesis cannot be dropped: `not_monotone_cutoffProfile_abs` and
`not_monotone_cutoffKernel_abs` show that a nonnegative profile that is not decreasing on
`(0, ∞)` violates the comparison, so the statements below are not vacuous consequences of
nonnegativity. `cutoffProfile_lt_cutoffProfile` records that they are also strict where `K` is.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.Models.LongRange

/-- **The cut-off profile respects the decreasing-profile convention.** If `K` is decreasing on
`(0, ∞)`, then so is `s ↦ J_r(s) = 1{s ≤ r} (K s - K r)` on `(0, ∞)`: it is `K s - K r` up to
`r`, and `0` beyond. Only monotonicity of `K` is used, and no value of `K` at `0`. -/
theorem antitoneOn_cutoffProfile {K : ℝ → ℝ} (hK : AntitoneOn K (Ioi 0)) (r : ℝ) :
    AntitoneOn (cutoffProfile K r) (Ioi 0) := by
  intro s hs t ht hst
  by_cases hsr : s ≤ r
  · rw [cutoffProfile_of_le hsr]
    by_cases htr : t ≤ r
    · rw [cutoffProfile_of_le htr]
      linarith [hK hs ht hst]
    · rw [cutoffProfile_of_lt (not_le.1 htr)]
      have hr : r ∈ Ioi (0 : ℝ) := mem_Ioi.2 (lt_of_lt_of_le hs hsr)
      linarith [hK hs hr hsr]
  · rw [cutoffProfile_of_lt (not_le.1 hsr)]
    rw [cutoffProfile_of_lt (not_le.1 fun h => hsr (hst.trans h))]

/-- **The comparison is strict where the profile is.** If `K` drops between `r` and `ρ`, then the
cut-off profile at `s ≤ r` is strictly smaller at the larger scale. No monotonicity of `K` is
needed, only the order of the two values. -/
theorem cutoffProfile_lt_cutoffProfile {K : ℝ → ℝ} {r ρ s : ℝ} (hsr : s ≤ r) (hrρ : r ≤ ρ)
    (h : K ρ < K r) : cutoffProfile K r s < cutoffProfile K ρ s := by
  rw [cutoffProfile_of_le hsr, cutoffProfile_of_le (hsr.trans hrρ)]
  linarith

/-- The power law drops strictly between two positive scales. -/
theorem powerLawProfile_lt {c a r ρ : ℝ} (hc : 0 < c) (ha : 0 < a) (hr : 0 < r) (hrρ : r < ρ) :
    powerLawProfile c a ρ < powerLawProfile c a r := by
  have hlt : ρ ^ (-a) < r ^ (-a) :=
    Real.strictAntiOn_rpow_Ioi_of_exponent_neg (by linarith : -a < 0)
      (mem_Ioi.2 hr) (mem_Ioi.2 (hr.trans hrρ)) hrρ
  simp only [powerLawProfile]
  exact mul_lt_mul_of_pos_left hlt hc

/-- **Strictness for the power law.** Between two positive scales the cut-off power-law profile is
strictly larger at the larger scale, at every displacement up to the smaller scale. -/
theorem cutoffProfile_powerLaw_lt {c a r ρ s : ℝ} (hc : 0 < c) (ha : 0 < a) (hs : 0 < s)
    (hsr : s ≤ r) (hrρ : r < ρ) :
    cutoffProfile (powerLawProfile c a) r s < cutoffProfile (powerLawProfile c a) ρ s :=
  cutoffProfile_lt_cutoffProfile hsr hrρ.le
    (powerLawProfile_lt hc ha (lt_of_lt_of_le hs hsr) hrρ)

/-- **The direction cannot be reversed.** For the power law the cut-off family is not decreasing
in the scale: at displacement `1` and scales `2 < 3` the profile is strictly larger at the larger
scale, so no inequality with the two sides exchanged can hold. -/
theorem not_forall_cutoffProfile_le_of_le {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ¬ ∀ r ρ : ℝ, r ≤ ρ → ∀ s : ℝ, 0 < s →
      cutoffProfile (powerLawProfile c a) ρ s ≤ cutoffProfile (powerLawProfile c a) r s := by
  intro h
  have h1 := h 2 3 (by norm_num) 1 (by norm_num)
  have h2 := cutoffProfile_powerLaw_lt (c := c) (a := a) hc ha (show (0 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) < 3 by norm_num)
  linarith

/-- **The diagonal is zero at every scale**, so no value of the profile at `0` and no
diagonal case of the comparison is ever used. -/
@[simp] theorem cutoffKernel_diag {d : ℕ} (N : Seminorm ℝ (Fin d → ℝ)) (K : ℝ → ℝ) (r : ℝ)
    (x : Fin d → ℤ) : cutoffKernel N K r s(x, x) = 0 := by
  rw [cutoffKernel_def, radialKernel_diag]

/-- **The decreasing hypothesis is necessary at the profile level.** The nonnegative profile
`s ↦ |s - 2|` is not decreasing on `(0, ∞)`, and the resulting cut-off profile is *not* monotone
in the scale: it is `1` at scale `2` and `0` at scale `3`, at displacement `1`. -/
theorem not_monotone_cutoffProfile_abs :
    ¬ Monotone fun r => cutoffProfile (fun s : ℝ => |s - 2|) r 1 := by
  intro h
  have h23 := h (show (2 : ℝ) ≤ 3 by norm_num)
  change cutoffProfile (fun s : ℝ => |s - 2|) 2 1 ≤ cutoffProfile (fun s : ℝ => |s - 2|) 3 1
    at h23
  rw [cutoffProfile_of_le (K := fun s : ℝ => |s - 2|) (r := 2) (s := 1) (by norm_num),
    cutoffProfile_of_le (K := fun s : ℝ => |s - 2|) (r := 3) (s := 1) (by norm_num)] at h23
  norm_num at h23

/-- **The decreasing hypothesis is necessary at the kernel level.** The nonnegative, continuous
profile `s ↦ |s - 2|` is not decreasing on `(0, ∞)`, and the cut-off kernel of the sup-norm model
on `ℤ` is *not* monotone in the scale: at the pair `{0, 1}` it is `1` at scale `2` and `0` at
scale `3`. Nonnegativity of the profile therefore does not suffice. -/
theorem not_monotone_cutoffKernel_abs :
    ¬ Monotone fun r => cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s : ℝ => |s - 2|) r
        s((0 : Fin 1 → ℤ), fun _ => 1) := by
  intro h
  have h23 := h (show (2 : ℝ) ≤ 3 by norm_num)
  change cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s : ℝ => |s - 2|) 2
      s((0 : Fin 1 → ℤ), fun _ => 1) ≤
    cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ)) (fun s : ℝ => |s - 2|) 3
      s((0 : Fin 1 → ℤ), fun _ => 1) at h23
  have hne : (0 : Fin 1 → ℤ) ≠ (fun _ => 1) := by
    intro hc
    have h0 : (0 : Fin 1 → ℤ) ⟨0, Nat.lt_succ_self 0⟩ = 0 := rfl
    rw [hc] at h0
    norm_num at h0
  rw [cutoffKernel_def, cutoffKernel_def,
    radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ)) hne,
    radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ)) hne] at h23
  simp only [normSeminorm_intCast] at h23
  have h2 : ‖(0 : Fin 1 → ℤ) - (fun _ => 1)‖ ≤ 2 := by norm_num
  have h3 : ‖(0 : Fin 1 → ℤ) - (fun _ => 1)‖ ≤ 3 := by norm_num
  rw [cutoffProfile_of_le (K := fun s : ℝ => |s - 2|) (r := 2)
      (s := ‖(0 : Fin 1 → ℤ) - (fun _ => 1)‖) h2,
    cutoffProfile_of_le (K := fun s : ℝ => |s - 2|) (r := 3)
      (s := ‖(0 : Fin 1 → ℤ) - (fun _ => 1)‖) h3] at h23
  norm_num at h23

/-- **Characterisation: the cut-off family is monotone in the scale exactly when the profile is
decreasing.** For a fixed displacement `s` (the relevant case is `s > 0`), monotonicity of
`r ↦ J_r(s)` over the scales `r ≥ s` is
*equivalent* to `K` being antitone on `[s, ∞)`. Hence the hypothesis of `monotone_cutoffKernel`
cannot be weakened: it is not merely sufficient, but the exact condition for monotonicity in the
scale at each fixed displacement. -/
theorem antitoneOn_iff_monotone_cutoffProfile {K : ℝ → ℝ} (s : ℝ) :
    AntitoneOn K (Ici s) ↔
      ∀ r ∈ Ici s, ∀ ρ ∈ Ici s, r ≤ ρ → cutoffProfile K r s ≤ cutoffProfile K ρ s := by
  constructor
  · intro hK r hr ρ hρ hrρ
    have h : s ≤ r := mem_Ici.1 hr
    rw [cutoffProfile_of_le h, cutoffProfile_of_le (h.trans hrρ)]
    linarith [hK hr hρ hrρ]
  · intro hm a ha b hb hab
    have h1 := hm a ha b hb hab
    rw [cutoffProfile_of_le (mem_Ici.1 ha), cutoffProfile_of_le (mem_Ici.1 hb)] at h1
    linarith

end PercLib.Models.LongRange

namespace PercLib.Percolation.Bond

variable {d : ℕ} {K : ℝ → ℝ} {N : Analysis.ModelNorm (Fin d → ℝ)}

/-- **Every increasing measurable functional of the configuration increases with the scale.**
This is the form in which the radius comparison passes to any cluster functional, not only the
susceptibility. -/
theorem lintegral_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) {r ρ : ℝ} (hrρ : r ≤ ρ)
    {β : ℝ≥0} {φ : Config (Fin d → ℤ) → ℝ≥0∞} (hφ : Measurable φ) (hmono : Monotone φ) :
    (∫⁻ ω, φ ω ∂law (intensityProfile (PercLib.Models.LongRange.cutoffKernel
        N.toSeminorm K r) β)) ≤
      ∫⁻ ω, φ ω ∂law (intensityProfile (PercLib.Models.LongRange.cutoffKernel
        N.toSeminorm K ρ) β) :=
  PercLib.Probability.lintegral_prodBernoulli_mono _ _
    (intensityProfile_le_of_le
      (fun e => PercLib.Models.LongRange.monotone_cutoffKernel hK e hrρ) β) hφ hmono

/-- **Edge intensities of the cut-off family increase with the scale.** -/
theorem intensityProfile_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) {r ρ : ℝ} (hrρ : r ≤ ρ)
    (β : ℝ≥0) :
    intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β ≤
      intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K ρ) β :=
  intensityProfile_le_of_le (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ) β

/-- **The two-point function increases with the scale.** -/
theorem tau_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) (β : ℝ≥0) {r ρ : ℝ} (hrρ : r ≤ ρ)
    (x y : Fin d → ℤ) :
    tau (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β) x y ≤
      tau (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K ρ) β) x y :=
  tau_le_of_le (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ) β x y

/-- **The susceptibility increases with the scale**, at every finite bond parameter and every
vertex. -/
theorem chi_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) (β : ℝ≥0) (x : Fin d → ℤ) :
    Monotone fun r =>
      chi (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β) x :=
  fun _ _ hrρ => chi_le_of_le (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ)
    β x

/-- **The probability that the cluster of a vertex is infinite increases with the scale.** -/
theorem law_cluster_infinite_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) (β : ℝ≥0)
    (x : Fin d → ℤ) :
    Monotone fun r =>
      law (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β)
        {ω | (cluster ω x).Infinite} :=
  fun _ _ hrρ => law_cluster_infinite_le_of_le
    (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ) β x

/-- **The probability that some cluster is infinite increases with the scale.** -/
theorem law_exists_cluster_infinite_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) (β : ℝ≥0) :
    Monotone fun r =>
      law (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β)
        {ω | ∃ x, (cluster ω x).Infinite} :=
  fun _ _ hrρ => law_exists_cluster_infinite_le_of_le
    (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ) β

/-- **Tail probabilities increase with the scale**: for every `n`, the probability that the
cluster of `x` has at least `n` vertices is monotone in the cut-off scale. -/
theorem law_encard_cluster_ge_cutoffKernel_mono (hK : AntitoneOn K (Ioi 0)) (β : ℝ≥0)
    (x : Fin d → ℤ) (n : ℕ∞) :
    Monotone fun r =>
      law (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β)
        {ω | n ≤ (cluster ω x).encard} := by
  intro r ρ hrρ
  refine PercLib.Probability.prodBernoulli_mono_event _ _
    (intensityProfile_le_of_le
      (fun e => PercLib.Models.LongRange.monotone_cutoffKernel hK e hrρ) β) ?_ ?_
  · exact (measurable_encard_cluster x) MeasurableSet.of_discrete
  · exact fun _ _ hωω' hω => le_trans hω (encard_le_encard (cluster_mono hωω' x))

/-- **Root critical intensities do not increase with the scale.** -/
theorem rootCriticalIntensity_cutoffKernel_anti (hK : AntitoneOn K (Ioi 0)) (x : Fin d → ℤ) :
    Antitone fun r =>
      rootCriticalIntensity (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) x :=
  fun _ _ hrρ => rootCriticalIntensity_anti
    (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ) x

/-- **Global critical intensities do not increase with the scale.** -/
theorem globalCriticalIntensity_cutoffKernel_anti (hK : AntitoneOn K (Ioi 0)) :
    Antitone fun r =>
      globalCriticalIntensity (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) :=
  fun _ _ hrρ => globalCriticalIntensity_anti
    (fun _ => PercLib.Models.LongRange.monotone_cutoffKernel hK _ hrρ)

/-! ## Consequences at a fixed high-temperature parameter

The comparisons above hold at every parameter. With a row bound for the *uncut* kernel, every
member of the family is subcritical at the same parameter `β` with `β M < 1`, with the explicit
susceptibility bound `(1 - β M)⁻¹`; a concrete kernel supplies `M` through its own row-sum
estimate. -/

/-- **Almost surely no infinite cluster at every scale**, under the same row bound and
`β M < 1`. -/
theorem law_cluster_infinite_cutoffKernel_eq_zero {M : ℝ≥0} {r : ℝ} {β : ℝ≥0}
    (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r)
    (hJ : ∀ v : Fin d → ℤ,
      rowSum (fun e => (PercLib.Models.LongRange.radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M)
    (hβ : (β : ℝ≥0∞) * M < 1) (x : Fin d → ℤ) :
    law (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β)
      {ω | (cluster ω x).Infinite} = 0 :=
  law_cluster_infinite_intensity_eq_zero _ M
    (fun v => (PercLib.Models.LongRange.rowSum_cutoffKernel_le
    hK hr v).trans (hJ v)) β hβ x

/-- **Almost surely no infinite cluster anywhere at every scale.** -/
theorem law_exists_cluster_infinite_cutoffKernel_eq_zero {M : ℝ≥0} {r : ℝ} {β : ℝ≥0}
    (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r)
    (hJ : ∀ v : Fin d → ℤ,
      rowSum (fun e => (PercLib.Models.LongRange.radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M)
    (hβ : (β : ℝ≥0∞) * M < 1) :
    law (intensityProfile (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) β)
      {ω | ∃ x, (cluster ω x).Infinite} = 0 :=
  law_exists_infinite_intensity_eq_zero _ M
    (fun v => (PercLib.Models.LongRange.rowSum_cutoffKernel_le
    hK hr v).trans (hJ v)) β hβ

/-- **The cut-off threshold is at least `M⁻¹` at every scale**: cutting off cannot lower the
critical intensity below the reciprocal of the row bound. -/
theorem inv_le_rootCriticalIntensity_cutoffKernel {M : ℝ≥0} {r : ℝ}
    (hK : ∀ t, 0 < t → 0 ≤ K t) (hr : 0 < r)
    (hJ : ∀ v : Fin d → ℤ,
      rowSum (fun e => (PercLib.Models.LongRange.radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M)
    (x : Fin d → ℤ) :
    (M : ℝ≥0∞)⁻¹ ≤
      rootCriticalIntensity (PercLib.Models.LongRange.cutoffKernel N.toSeminorm K r) x :=
  inv_le_rootCriticalIntensity _ M
    (fun v => (PercLib.Models.LongRange.rowSum_cutoffKernel_le
    hK hr v).trans (hJ v)) x

/-! ## The concrete power law

The radius comparisons instantiate at the power-law profile of Definition I.1.3, which is
decreasing on `(0, ∞)` for a nonnegative exponent. -/

/-- **The cut-off power-law family is monotone in the scale at every bond parameter.** -/
theorem chi_powerLaw_cutoffKernel_mono {d : ℕ} {c a : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (β : ℝ≥0)
    (x : Fin d → ℤ) :
    Monotone fun r =>
      chi (intensityProfile (PercLib.Models.LongRange.cutoffKernel
        (Analysis.ModelNorm.ofNorm (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile c a) r) β) x :=
  chi_cutoffKernel_mono (PercLib.Models.LongRange.antitoneOn_powerLawProfile hc ha) β x

/-- **The cut-off power-law family percolates with increasing probability in the scale.** -/
theorem law_cluster_infinite_powerLaw_cutoffKernel_mono {d : ℕ} {c a : ℝ} (hc : 0 ≤ c)
    (ha : 0 ≤ a) (β : ℝ≥0) (x : Fin d → ℤ) :
    Monotone fun r =>
      law (intensityProfile (PercLib.Models.LongRange.cutoffKernel
        (Analysis.ModelNorm.ofNorm (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile c a) r) β)
        {ω | (cluster ω x).Infinite} :=
  law_cluster_infinite_cutoffKernel_mono
    (PercLib.Models.LongRange.antitoneOn_powerLawProfile hc ha) β x

/-- **Power-law root critical intensities do not increase with the scale.** -/
theorem rootCriticalIntensity_powerLaw_cutoffKernel_anti {d : ℕ} {c a : ℝ} (hc : 0 ≤ c)
    (ha : 0 ≤ a) (x : Fin d → ℤ) :
    Antitone fun r =>
      rootCriticalIntensity (PercLib.Models.LongRange.cutoffKernel
        (Analysis.ModelNorm.ofNorm (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile c a) r) x :=
  rootCriticalIntensity_cutoffKernel_anti
    (PercLib.Models.LongRange.antitoneOn_powerLawProfile hc ha) x

/-! ## Non-degeneracy of the family

At a scale below the lattice spacing the sup-norm cut-off kernel vanishes, and the
susceptibility is exactly one: the family is not constant on a neighbourhood of scale zero once
an off-diagonal distance is allowed. -/

/-- **Below the lattice spacing the sup-norm cut-off is empty**: every cluster is a single
vertex, so the susceptibility is exactly one, at every parameter and every profile. -/
theorem chi_cutoffKernel_eq_one_of_lt_one {d : ℕ} {K : ℝ → ℝ} {β : ℝ≥0} {r : ℝ} (hr : r < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile (PercLib.Models.LongRange.cutoffKernel
      (normSeminorm ℝ (Fin d → ℝ)) K r) β) x = 1 := by
  refine chi_intensity_eq_one_of_rowSum_zero _ (fun v => ?_) β x
  simp only [rowSum_def, PercLib.Models.LongRange.cutoffKernel_eq_zero_of_lt_one hr,
    ENNReal.coe_zero]
  simp

/-- **A strict radius comparison of the power-law kernel**: with the sup norm on `ℤ`, the cut-off
power-law kernel `s ↦ s⁻²` is strictly smaller at scale `2` than at scale `3` at the pair
`{0, 1}`. So the monotonicity above is not an equality of laws. -/
theorem cutoffKernel_powerLaw_strict :
    PercLib.Models.LongRange.cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 2) 2 s((0 : Fin 1 → ℤ), fun _ => 1) <
      PercLib.Models.LongRange.cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 2) 3 s((0 : Fin 1 → ℤ), fun _ => 1) := by
  have hne : (0 : Fin 1 → ℤ) ≠ (fun _ => 1) := by
    intro hc
    have h0 : (0 : Fin 1 → ℤ) ⟨0, Nat.lt_succ_self 0⟩ = 0 := rfl
    rw [hc] at h0
    norm_num at h0
  have hnorm : ‖(0 : Fin 1 → ℤ) - (fun _ => 1)‖ = 1 := by norm_num
  rw [PercLib.Models.LongRange.cutoffKernel_def, PercLib.Models.LongRange.cutoffKernel_def,
    PercLib.Models.LongRange.radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ)) hne,
    PercLib.Models.LongRange.radialKernel_of_ne (N := normSeminorm ℝ (Fin 1 → ℝ)) hne]
  simp only [PercLib.Models.LongRange.normSeminorm_intCast, hnorm,
    PercLib.Models.LongRange.cutoffProfile_of_le (K := PercLib.Models.LongRange.powerLawProfile 1 2)
      (r := 2) (s := 1) (by norm_num),
    PercLib.Models.LongRange.cutoffProfile_of_le (K := PercLib.Models.LongRange.powerLawProfile 1 2)
      (r := 3) (s := 1) (by norm_num)]
  norm_num [PercLib.Models.LongRange.powerLawProfile]

/-! ## Non-vacuity witnesses -/

open PercLib.Models.LongRange in
/-- At bond parameter zero the high-temperature hypothesis `β M < 1` holds for every row bound,
and the explicit susceptibility bound is the value one that the empty graph gives. -/
example {d : ℕ} {K : ℝ → ℝ} {N : Analysis.ModelNorm (Fin d → ℝ)} {M : ℝ≥0}
    (hK : ∀ t, 0 < t → 0 ≤ K t) {r : ℝ} (hr : 0 < r)
    (hJ : ∀ v : Fin d → ℤ,
      rowSum (fun e => (radialKernel N.toSeminorm K e : ℝ≥0∞)) v ≤ M) (x : Fin d → ℤ) :
    chi (intensityProfile (cutoffKernel N.toSeminorm K r) 0) x ≤
      (1 - ((0 : ℝ≥0) : ℝ≥0∞) * M)⁻¹ :=
  PercLib.Models.LongRange.chi_cutoffKernel_le_inv_one_sub hK hJ (β := 0) (by simp) hr x

/-- The small-scale endpoint for the power law at `d = 1`, `α = 1`, `β = 0`: the cut-off at
scale `0` has susceptibility exactly one, while at scale `2` the comparison of the family applies
to it. -/
example (x : Fin 1 → ℤ) :
    chi (intensityProfile (PercLib.Models.LongRange.cutoffKernel (normSeminorm ℝ (Fin 1 → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 2) 0) 0) x = 1 :=
  chi_cutoffKernel_eq_one_of_lt_one (by norm_num) x

end PercLib.Percolation.Bond
