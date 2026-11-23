/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file `PercLib/CriticalLRP/PowerLawHighTemp.lean`,
source revision `6953cfc748205d5589dd0ed17f79afff0d44b2d7`, supplied under its Apache-2.0 header
(the sections "The row-sum bound and finite susceptibility" and "The critical intensity is
strictly positive" of that file). Canonical namespace prefix:
`PercLib.Percolation.Bond.Exploration.BFS`.

Presentation changes forced by the canonical interface, none of them a weakening:

* the source's law `longRangeMeasure (kernelJ K hK) hK β` is the canonical `law (intensityProfile J
  β)` at a pair intensity `J` with the same displacement profile;
* the source's `linfNorm` is the sup norm `‖·‖` on `Fin d → ℤ`;
* the source's `kernelJ`-presentation corollaries are not migrated (`kernelJ` is not part of the
  canonical bond interface); the power-law corollaries are stated instead for the production
  kernel `Models.LongRange.radialKernel … (powerLawProfile 1 (d + α))`, whose value is the
  source's `lrKernel d α`;
* the source's conditional `criticalBetaSet`/`criticalBeta` wrappers are not migrated: the
  canonical library has no such definition and the source's own statement requires an unproved
  nonemptiness input. The threshold results below are unconditional because the canonical
  `globalCriticalIntensity`/`rootCriticalIntensity` are `ℝ≥0∞`-valued infima (empty infimum
  `⊤`), unlike the source's `ℝ≥0`-valued convention.

No definition, no `Input`, no alternative configuration model, no cutoff law: this is a
proof-only module for the uncut power law in the explicit region `β M < 1`.
-/
module

public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail
public import PercLib.Models.TranslationInvariant

/-!
# High-temperature susceptibility and positive critical intensities for the power law

For the power-law pair intensity `J(x,y) = ‖y - x‖_∞^{-s}` on `ℤ^d` with `s > d`, let
`M = ∑'_z ‖z‖_∞^{-s}` be the mass of the profile. Then `β M < 1` gives

* `power_chi_intensity_le`: `χ(x) ≤ (1 - β M)⁻¹` at every vertex, the explicit row-sum bound;
* `power_chi_intensity_lt_top`: finite expected cluster volume at every vertex;
* `power_law_exists_infinite_eq_zero`: almost surely no cluster is infinite;
* `power_inv_powerMass_le_globalCriticalIntensity`,
  `power_inv_powerMass_le_rootCriticalIntensity`: both thresholds are at least `M⁻¹`, hence
  `power_globalCriticalIntensity_pos`, `power_rootCriticalIntensity_pos`: strictly positive.

The last four are the content of the source's "the critical intensity is strictly positive"; they
are unconditional here, since the canonical thresholds are `ℝ≥0∞`-valued infima.

The concrete production kernel `radialKernel (normSeminorm ℝ (Fin d → ℝ))
(powerLawProfile 1 (d + α))` (the source's `lrKernel d α`) has the same statements below the
`powerLaw_` prefix, together with the positive-parameter intervals
`exists_beta_interval_powerLaw_chi_lt_top` and `exists_beta_interval_powerLaw_noPercolation`.

Nothing here is a statement at `β M ≥ 1`, at `β_c`, or about sharpness; the natural-moment and
exponential-tail results at the same parameters are already landed in
`PercLib.Percolation.Bond.PowerLawHighTemp.Tail` and are not repeated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond.Exploration.BFS

/-! ## The row-sum bound and the explicit susceptibility bound -/

/-- **The explicit high-temperature susceptibility bound.** For the power-law profile on `ℤ^d`
with `s > d` and any pair intensity with that displacement profile, `χ(x) ≤ (1 - β M)⁻¹`
whenever `β M < 1`, where `M` is the total profile mass. Source:
`PowerLawHighTemp.power_chi_intensity_le`, with the source's `chi (intensityProfile J β)` and the
sup norm `‖·‖`. -/
theorem power_chi_intensity_le {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile J β) x ≤
      (1 - (β : ℝ≥0∞) *
        ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞))⁻¹ := by
  classical
  refine chi_intensity_le J (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)))
    (fun v => ?_) β hβ x
  rw [rowSum_def]
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-- **Finite susceptibility of the power-law intensity in the high-temperature regime.** At
`β M < 1` the expected cluster volume at every vertex is finite. Source:
`PowerLawHighTemp.power_chi_intensity_lt_top`. -/
theorem power_chi_intensity_lt_top {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile J β) x < ⊤ := by
  classical
  refine chi_intensity_lt_top J (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)))
    (fun v => ?_) β hβ x
  rw [rowSum_def]
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-- **No percolation at small `β`.** For the power-law profile with `s > d` and `β M < 1`, almost
surely no cluster is infinite. Source: `PowerLawHighTemp.power_kernelJ_infiniteClusterProb_eq_zero`,
with `infiniteClusterProb … β` written as the canonical `law (intensityProfile J β)` on the set
`{ω | ∃ x, (cluster ω x).Infinite}`. -/
theorem power_law_exists_infinite_eq_zero {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1) :
    law (intensityProfile J β) {ω | ∃ x : Fin d → ℤ, (cluster ω x).Infinite} = 0 := by
  classical
  refine law_exists_infinite_intensity_eq_zero J
    (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s))) (fun v => ?_) β hβ
  rw [rowSum_def]
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-! ## Positivity of the critical intensities -/

/-- **The global threshold of the power-law model is at least `M⁻¹`.** Source:
`PowerLawHighTemp.inv_le_globalCriticalIntensity` instantiated at the power-law mass; the source
states it inline inside `power_globalCriticalIntensity_pos`. -/
theorem power_inv_powerMass_le_globalCriticalIntensity {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hs : (d : ℝ) < s) {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s))) :
    ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      globalCriticalIntensity J := by
  classical
  refine inv_le_globalCriticalIntensity J
    (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s))) (fun v => ?_)
  rw [rowSum_def]
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-- **The root threshold of the power-law model is at least `M⁻¹`.** Source:
`PowerLawHighTemp.inv_le_rootCriticalIntensity` instantiated at the power-law mass. -/
theorem power_inv_powerMass_le_rootCriticalIntensity {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hs : (d : ℝ) < s) {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    (x : Fin d → ℤ) :
    ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      rootCriticalIntensity J x := by
  classical
  refine inv_le_rootCriticalIntensity J
    (Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s))) (fun v => ?_) x
  rw [rowSum_def]
  exact (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp).trans
    (power_rowSum_le hd hs hJ v)

/-- **The critical intensity of the power-law model is strictly positive.** Source:
`PowerLawHighTemp.power_globalCriticalIntensity_pos`. Unconditional: the canonical threshold is an
`ℝ≥0∞`-valued infimum, so no nonemptiness hypothesis is needed. -/
theorem power_globalCriticalIntensity_pos {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s))) :
    0 < globalCriticalIntensity J := by
  classical
  refine lt_of_lt_of_le ?_ (power_inv_powerMass_le_globalCriticalIntensity hd hs hJ)
  rw [ENNReal.inv_pos]
  exact ENNReal.coe_ne_top

/-- **The root threshold of the power-law model is strictly positive.** Source:
`PowerLawHighTemp.power_rootCriticalIntensity_pos`, at every root. -/
theorem power_rootCriticalIntensity_pos {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    (x : Fin d → ℤ) :
    0 < rootCriticalIntensity J x := by
  classical
  refine lt_of_lt_of_le ?_ (power_inv_powerMass_le_rootCriticalIntensity hd hs hJ x)
  rw [ENNReal.inv_pos]
  exact ENNReal.coe_ne_top

/-! ## The concrete power-law kernel on `ℤ^d`

The production presentation of the source's `lrKernel d α` is
`radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 (d + α))`; its value on a pair is
`Real.toNNReal (‖y - x‖^{-d-α})` (`radialKernel_powerLaw_mk`, landed in
`PercLib.Percolation.Bond.PowerLawHighTemp.Tail`). The statements below are the source's
`lrKernel`-presentation corollaries, with the source's `longRangeMeasure` written as the canonical
`law (intensityProfile _ β)`.
-/

/-- **Explicit high-temperature susceptibility bound for the paper's kernel**
`J(x,y) = ‖x - y‖_∞^{-d-α}`: `χ(x) ≤ (1 - β M)⁻¹` for `β M < 1`, with
`M = ∑'_z ‖z‖_∞^{-d-α}`. Source: `PowerLawHighTemp.lrKernel` corollaries of
`power_chi_intensity_le`. -/
theorem powerLaw_chi_le {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile
      (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β) x ≤
      (1 - (β : ℝ≥0∞) * ((Real.toNNReal
        (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  power_chi_intensity_le hd (by linarith) (radialKernel_powerLaw_mk hα) hβ x

/-- **Finite expected cluster volume for the paper's kernel** at `β M < 1`, every vertex. Source:
`PowerLawHighTemp.lrKernel_lintegral_clusterVol_ne_top`, in the `chi`-form of the canonical
interface. -/
theorem powerLaw_chi_lt_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile
      (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β) x < ⊤ :=
  power_chi_intensity_lt_top hd (by linarith) (radialKernel_powerLaw_mk hα) hβ x

/-- **No percolation for the paper's kernel** at `β M < 1`: almost surely no cluster is infinite.
Source: `PowerLawHighTemp.lrKernel_infiniteClusterProb_eq_zero`, with
`infiniteClusterProb (lrKernel d α) (lrKernel_nonneg d α) β = 0` written as the canonical law on
`{ω | ∃ x, (cluster ω x).Infinite}`. -/
theorem powerLaw_law_exists_infinite_eq_zero {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) * ((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < 1) :
    law (intensityProfile
      (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)
      {ω | ∃ x : Fin d → ℤ, (cluster ω x).Infinite} = 0 :=
  power_law_exists_infinite_eq_zero hd (by linarith) (radialKernel_powerLaw_mk hα) hβ

/-- **The global threshold of the paper's kernel is at least `M⁻¹`.** -/
theorem powerLaw_inv_powerMass_le_globalCriticalIntensity {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) :
    ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      globalCriticalIntensity
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) :=
  power_inv_powerMass_le_globalCriticalIntensity hd (by linarith) (radialKernel_powerLaw_mk hα)

/-- **The root threshold of the paper's kernel is at least `M⁻¹`**, at every root. -/
theorem powerLaw_inv_powerMass_le_rootCriticalIntensity {d : ℕ} (hd : 1 ≤ d) {α : ℝ}
    (hα : 0 < α) (x : Fin d → ℤ) :
    ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞)⁻¹ ≤
      rootCriticalIntensity
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) x :=
  power_inv_powerMass_le_rootCriticalIntensity hd (by linarith) (radialKernel_powerLaw_mk hα) x

/-- **The critical intensity of the paper's kernel is strictly positive.** -/
theorem powerLaw_globalCriticalIntensity_pos {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    0 < globalCriticalIntensity
      (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) :=
  power_globalCriticalIntensity_pos hd (by linarith) (radialKernel_powerLaw_mk hα)

/-- **The root threshold of the paper's kernel is strictly positive**, at every root. -/
theorem powerLaw_rootCriticalIntensity_pos {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (x : Fin d → ℤ) :
    0 < rootCriticalIntensity
      (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
        (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) x :=
  power_rootCriticalIntensity_pos hd (by linarith) (radialKernel_powerLaw_mk hα) x

/-! ## A positive interval of parameters

The endpoint is `β₀ = (M + 1)⁻¹` with `M` the profile mass, exactly as in the source's
`exists_beta_interval_power_kernelJ_chi_lt_top`; `mul_coe_lt_one_of_lt_inv_add_one` (landed in
`PercLib.Percolation.Bond.PowerLawHighTemp.Tail`) does the scalar comparison.
-/

/-- **A positive interval of parameters with finite susceptibility** for the paper's kernel.
Source: `PowerLawHighTemp.exists_beta_interval_power_kernelJ_chi_lt_top`. -/
theorem exists_beta_interval_powerLaw_chi_lt_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ → ∀ x : Fin d → ℤ,
      chi (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β) x < ⊤ := by
  refine ⟨((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) + 1)⁻¹,
    inv_pos.mpr (by positivity), fun β hβ x => ?_⟩
  exact powerLaw_chi_lt_top hd hα (mul_coe_lt_one_of_lt_inv_add_one hβ) x

/-- **A positive interval of parameters with no percolation** for the paper's kernel: on the same
interval the infinite-cluster event is null. The source states the susceptibility interval only;
this is the companion statement for the absence of an infinite cluster. -/
theorem exists_beta_interval_powerLaw_noPercolation {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β₀ : ℝ≥0, 0 < β₀ ∧ ∀ β : ℝ≥0, β < β₀ →
      law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)
        {ω | ∃ x : Fin d → ℤ, (cluster ω x).Infinite} = 0 := by
  refine ⟨((Real.toNNReal
      (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) + 1)⁻¹,
    inv_pos.mpr (by positivity), fun β hβ => ?_⟩
  exact powerLaw_law_exists_infinite_eq_zero hd hα (mul_coe_lt_one_of_lt_inv_add_one hβ)

/-! ## Non-vacuity

`exists_beta_positive_powerLaw` (landed in `PercLib.Percolation.Bond.PowerLawHighTemp.Tail`)
supplies a strictly positive parameter with `β M < 1`, so the statements above hold on a genuinely
positive parameter, not only at `β = 0`.
-/

/-- The high-temperature region of `powerLaw_chi_lt_top` contains a positive parameter. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β : ℝ≥0, 0 < β ∧ ∀ x : Fin d → ℤ,
      chi (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β) x < ⊤ := by
  obtain ⟨β, hβpos, hβM, -⟩ := exists_beta_positive_powerLaw hd hα
  exact ⟨β, hβpos, fun x => powerLaw_chi_lt_top hd hα hβM x⟩

/-- The high-temperature region of `powerLaw_law_exists_infinite_eq_zero` contains a positive
parameter. -/
example (d : ℕ) (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∃ β : ℝ≥0, 0 < β ∧
      law (intensityProfile
        (PercLib.Models.LongRange.radialKernel (normSeminorm ℝ (Fin d → ℝ))
          (PercLib.Models.LongRange.powerLawProfile 1 ((d : ℝ) + α))) β)
        {ω | ∃ x : Fin d → ℤ, (cluster ω x).Infinite} = 0 := by
  obtain ⟨β, hβpos, hβM, -⟩ := exists_beta_positive_powerLaw hd hα
  exact ⟨β, hβpos, powerLaw_law_exists_infinite_eq_zero hd hα hβM⟩

/-- At `β = 0` the abstract-`J` susceptibility bound is available for every power-law intensity
`J`, so the `hβ` hypothesis of the abstract statements is satisfiable at a parameter with no
extra structure on `J`. -/
example (d : ℕ) (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    (x : Fin d → ℤ) :
    chi (intensityProfile J 0) x ≤
      (1 - ((0 : ℝ≥0) : ℝ≥0∞) *
        ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  power_chi_intensity_le hd hs hJ (by rw [ENNReal.coe_zero, zero_mul]; exact zero_lt_one) x

/-- Agreement with the landed natural-moment API: the `chi`-form of the first moment is the
already landed `k = 1` case of `power_lintegral_encard_cluster_pow_ne_top`
(`PercLib/Percolation/Bond/Exploration/BFS/IntensityMoments.lean`). This is recorded so that the
duplication is visible, not claimed as new. -/
example {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s)
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hJ : ∀ x y : Fin d → ℤ, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-s)))
    {β : ℝ≥0}
    (hβ : (β : ℝ≥0∞) *
      ((Real.toNNReal (∑' z : Fin d → ℤ, (‖z‖ : ℝ) ^ (-s)) : ℝ≥0) : ℝ≥0∞) < 1)
    (x : Fin d → ℤ) :
    chi (intensityProfile J β) x < ⊤ :=
  lt_top_iff_ne_top.mpr (by
    simpa [chi, pow_one] using power_lintegral_clusterVol_pow_ne_top hd hs hJ hβ x 1)

end PercLib.Percolation.Bond.Exploration.BFS
