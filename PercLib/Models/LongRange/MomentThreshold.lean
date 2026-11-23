/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Adapted from the uncommitted, project-generated candidate `MomentThreshold.lean`, under the same
Apache 2.0 licence. Its digest is retained in the integration verification record and commit
message. This is a proof-only migration.
Mathematical reference: the sharpness and endpoint inputs of T. Hutchcroft, *Critical long-range
percolation I*, arXiv:2508.18807v1. This module proves divergence, not finiteness at criticality.

Strict-subcritical thresholds for cluster moments: the divergence half.

For a transitive summable pair intensity and every `k ≥ 1`, the `k`-th moment of the cluster
volume `|K_o|` is infinite at and above the susceptibility threshold `β_c`, and tends to `⊤`
as `β ↑ β_c`.  Equivalently, a finite `k`-th moment forces `β < β_c`.  No finiteness
statement below `β_c` is claimed here; that is the other half of the threshold.
-/
module

public import PercLib.Percolation.Bond.SusceptibilityEndpoint
public import PercLib.Percolation.Bond.MomentTransport
public import PercLib.Percolation.Bond.Sharpness
public import PercLib.Models.LongRange.FiniteSusceptibility
public import PercLib.Percolation.Bond.PowerLawHighTemp.Tail
public import PercLib.Percolation.Bond.Exploration.BFS.IntensityMoments
public import PercLib.Models.LongRange.PowerLaw

/-!
# The moment threshold of the full-lattice power-law bond model

For a transitive summable pair intensity, every positive order of cluster moment is infinite at
and above the susceptibility threshold and diverges on approach from below. For the raw power-law
model this identifies the threshold with `globalCriticalIntensity`, with no finiteness assertion at
criticality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

omit [Countable V] in
/-- For `k ≥ 1` the `k`-th power of the cluster volume dominates the cluster volume. -/
theorem encard_cluster_le_pow (ω : Config V) (o : V) {k : ℕ} (hk : 1 ≤ k) :
    ((cluster ω o).encard : ℝ≥0∞) ≤ ((cluster ω o).encard : ℝ≥0∞) ^ k := by
  set x : ℝ≥0∞ := ((cluster ω o).encard : ℝ≥0∞) with hx
  have h1 : 1 ≤ x := by
    rw [hx]
    simpa using ENat.toENNReal_le.2 (one_le_encard_cluster ω o)
  calc x = x * 1 := (mul_one x).symm
    _ ≤ x * x ^ (k - 1) := by
        gcongr
        exact one_le_pow₀ h1
    _ = x ^ k := by
        rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk).symm]
        exact (pow_succ' x (k - 1)).symm

omit [Countable V] in
/-- Every positive-order cluster moment dominates the susceptibility. -/
theorem chi_le_lintegral_encard_cluster_pow (q : Sym2 V → unitInterval) (o : V) {k : ℕ}
    (hk : 1 ≤ k) :
    chi q o ≤ ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law q) :=
  lintegral_mono fun ω => encard_cluster_le_pow ω o hk

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- **The `k`-th cluster moment is infinite at and above the susceptibility threshold.** -/
theorem lintegral_encard_cluster_pow_eq_top_of_sSup_le {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    (hb : sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤)
    {β : ℝ≥0}
    (hβ : sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) ≤
      (β : ℝ≥0∞))
    {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) = ⊤ := by
  set b := sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤})
    with hbdef
  have htop : chi (intensityProfile J b.toNNReal) o = ⊤ := chi_intensity_sSup_eq_top hJ hL hb
  have hle : b.toNNReal ≤ β := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hb.ne]
    exact hβ
  have hmono : chi (intensityProfile J b.toNNReal) o ≤ chi (intensityProfile J β) o :=
    chi_mono (fun e => intensityProfile_mono J hle e) o
  rw [htop] at hmono
  have htopβ : chi (intensityProfile J β) o = ⊤ := top_unique hmono
  have h := chi_le_lintegral_encard_cluster_pow (intensityProfile J β) o hk
  rw [htopβ] at h
  exact top_unique h

/-- **A finite `k`-th cluster moment forces the parameter below the threshold.** -/
theorem lt_sSup_of_lintegral_encard_cluster_pow_ne_top {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    (hb : sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤)
    {β : ℝ≥0} {k : ℕ} (hk : 1 ≤ k)
    (h : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) ≠ ⊤) :
    (β : ℝ≥0∞) <
      sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) := by
  by_contra hcon
  push Not at hcon
  exact h (lintegral_encard_cluster_pow_eq_top_of_sSup_le hJ hL hb hcon hk)

end PercLib.Percolation.Bond

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- **Divergence of every positive-order cluster moment at the threshold.** -/
theorem tendsto_lintegral_encard_cluster_pow_nhdsLT_sSup {J : Sym2 V → ℝ≥0} {o : V}
    (hJ : ∀ x, ∃ φ : V ≃ V, φ o = x ∧ ∀ e, J (Sym2.map φ e) = J e)
    (hR0 : 0 < rowSum (fun e => (J e : ℝ≥0∞)) o)
    (hL : rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤)
    (hb : sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) < ⊤)
    {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun β : ℝ≥0 => ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)))
      (𝓝[<] (sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) ''
        {β | chi (intensityProfile J β) o < ⊤})).toNNReal) (𝓝 ⊤) := by
  have hchi := tendsto_chi_intensity_nhdsLT_sSup hJ hR0 hL hb
  rw [ENNReal.tendsto_nhds_top_iff_nnreal] at hchi ⊢
  intro M
  filter_upwards [hchi M] with β hβ
  exact lt_of_lt_of_le hβ (chi_le_lintegral_encard_cluster_pow (intensityProfile J β) o hk)

end PercLib.Percolation.Bond

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-- For the raw power-law pair intensity `J s(x,y) = ‖y - x‖^(-(d+α))` on `ℤ^d` (`d ≥ 1`,
`α > 0`) the row sum at every root is finite and positive. -/
theorem powerLaw_rowSum_pos_and_lt_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (_hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) :
    rowSum (fun e => (J e : ℝ≥0∞)) o < ⊤ ∧ 0 < rowSum (fun e => (J e : ℝ≥0∞)) o := by
  classical
  constructor
  · have hrow := PercLib.Percolation.Bond.Exploration.BFS.power_rowSum_le
      (s := (d : ℝ) + α) hd (by linarith) hJ o
    refine lt_of_le_of_lt (le_trans ?_ hrow) ENNReal.coe_lt_top
    rw [rowSum_def]
    refine ENNReal.tsum_le_tsum fun w => ?_
    by_cases h : w = o
    · simp [h]
    · simp [h]
  · set e0 : Fin d → ℤ := Pi.single ⟨0, hd⟩ 1 with he0def
    have he0 : e0 ≠ 0 := by
      intro h
      have := congrFun h ⟨0, hd⟩
      simp [e0] at this
    have hsub : o + e0 ≠ o := by
      intro h
      exact he0 (add_left_cancel (by simpa using h : o + e0 = o + 0))
    rw [rowSum_def]
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum
      (f := fun w => if w = o then 0 else (J s(o, w) : ℝ≥0∞)) (o + e0))
    simp only [hsub, ite_false]
    rw [hJ, add_sub_cancel_left]
    exact ENNReal.coe_pos.2 (Real.toNNReal_pos.2 (Real.rpow_pos_of_pos (norm_pos_iff.2 he0) _))

/-- The power-law kernel has finite total mass. -/
theorem powerLaw_tsum_toNNReal_lt_top {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) :
    ∑' z : Fin d → ℤ, ((Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞) < ⊤ := by
  have hcoe : ∀ x : ℝ, 0 ≤ x → ((Real.toNNReal x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal x := by
    intro x hx
    rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal x hx]
  have h := (PercLib.Models.LongRange.tsum_ofReal_powerLaw_lt_top_iff hd α).2 hα
  have hcongr : (fun z : Fin d → ℤ =>
        ((Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α))) : ℝ≥0) : ℝ≥0∞))
      = fun z : Fin d → ℤ => ENNReal.ofReal (if z = 0 then 0 else ‖z‖ ^ (-((d : ℝ) + α))) := by
    funext z
    rw [hcoe _ (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hz : z = 0
    · subst hz
      have hz0 : (0 : ℝ) ^ (-α + -(d : ℝ)) = 0 := Real.zero_rpow (by linarith)
      simp [hz0]
    · simp [hz]
  rwa [hcongr]

end PercLib.Models.LongRange

namespace PercLib.Models.LongRange

open PercLib.Percolation.Bond

/-- **Every positive-order cluster moment is infinite at and above the critical intensity**,
for the raw full-lattice power-law law `J s(x,y) = ‖y - x‖^(-(d+α))`, in the presence of a finite
threshold `β_c < ⊤`. -/
theorem powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le_of_lt_top
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) {β : ℝ≥0}
    (hb : globalCriticalIntensity J < ⊤)
    (hβ : globalCriticalIntensity J ≤ (β : ℝ≥0∞)) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) = ⊤ := by
  obtain ⟨hrowlt, -⟩ := powerLaw_rowSum_pos_and_lt_top hd hα J hJ o
  have hksum := powerLaw_tsum_toNNReal_lt_top hd hα
  have hT := PercLib.Models.transitive_of_translationInvariant J
    (fun z : Fin d → ℤ => Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ
  have hrow := PercLib.Models.summable_rows_of_translationInvariant J
    (fun z : Fin d → ℤ => Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ hksum
  have heq : globalCriticalIntensity J =
      sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) :=
    globalCriticalIntensity_eq_sSup_chi_lt_top J hT hrow o
  rw [heq] at hb hβ
  exact PercLib.Percolation.Bond.lintegral_encard_cluster_pow_eq_top_of_sSup_le
    (fun x => hT o x) hrowlt hb hβ hk

/-- **Every positive-order cluster moment is infinite at and above the critical intensity**,
for the raw full-lattice power-law law `J s(x,y) = ‖y - x‖^(-(d+α))`.  No finiteness hypothesis on
`β_c` is needed: if `β_c = ⊤` the hypothesis `β_c ≤ β` is unsatisfiable. -/
theorem powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) {β : ℝ≥0}
    (hβ : globalCriticalIntensity J ≤ (β : ℝ≥0∞)) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) = ⊤ := by
  rcases eq_or_ne (globalCriticalIntensity J) ⊤ with htop | hfin
  · rw [htop] at hβ
    exact absurd hβ (by simp)
  · exact powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le_of_lt_top
      hd hα J hJ o (lt_top_iff_ne_top.2 hfin) hβ hk

/-- **A finite positive-order cluster moment forces `β < β_c`**, for the raw full-lattice
power-law law.  No finiteness hypothesis on `β_c` is needed. -/
theorem powerLaw_lt_globalCriticalIntensity_of_lintegral_encard_cluster_pow_ne_top
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) {β : ℝ≥0} {k : ℕ} (hk : 1 ≤ k)
    (h : ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) ≠ ⊤) :
    (β : ℝ≥0∞) < globalCriticalIntensity J := by
  rcases eq_or_ne (globalCriticalIntensity J) ⊤ with htop | hfin
  · rw [htop]
    exact ENNReal.coe_lt_top
  · obtain ⟨hrowlt, -⟩ := powerLaw_rowSum_pos_and_lt_top hd hα J hJ o
    have hksum := powerLaw_tsum_toNNReal_lt_top hd hα
    have hT := PercLib.Models.transitive_of_translationInvariant J
      (fun z : Fin d → ℤ => Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ
    have hrow := PercLib.Models.summable_rows_of_translationInvariant J
      (fun z : Fin d → ℤ => Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ hksum
    have heq : globalCriticalIntensity J =
        sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) :=
      globalCriticalIntensity_eq_sSup_chi_lt_top J hT hrow o
    rw [heq] at hfin ⊢
    exact PercLib.Percolation.Bond.lt_sSup_of_lintegral_encard_cluster_pow_ne_top
      (fun x => hT o x) hrowlt (lt_top_iff_ne_top.2 hfin) hk h

/-- **Divergence at the critical intensity** of every positive-order cluster moment, for the raw
full-lattice power-law law (here a finite threshold is required for the statement to be meaningful).
-/
theorem powerLaw_tendsto_lintegral_encard_cluster_pow_nhdsLT_globalCriticalIntensity
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) (hb : globalCriticalIntensity J < ⊤) {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun β : ℝ≥0 =>
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)))
      (𝓝[<] (globalCriticalIntensity J).toNNReal) (𝓝 ⊤) := by
  obtain ⟨hrowlt, hrowpos⟩ := powerLaw_rowSum_pos_and_lt_top hd hα J hJ o
  have hksum := powerLaw_tsum_toNNReal_lt_top hd hα
  have hT := PercLib.Models.transitive_of_translationInvariant J
    (fun z : Fin d → ℤ => Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ
  have hrow := PercLib.Models.summable_rows_of_translationInvariant J
    (fun z : Fin d → ℤ => Real.toNNReal ((‖z‖ : ℝ) ^ (-((d : ℝ) + α)))) hJ hksum
  have heq : globalCriticalIntensity J =
      sSup ((fun β : ℝ≥0 => (β : ℝ≥0∞)) '' {β | chi (intensityProfile J β) o < ⊤}) :=
    globalCriticalIntensity_eq_sSup_chi_lt_top J hT hrow o
  rw [heq] at hb ⊢
  exact PercLib.Percolation.Bond.tendsto_lintegral_encard_cluster_pow_nhdsLT_sSup
    (fun x => hT o x) hrowpos hrowlt hb hk

/-- At and above the critical intensity the susceptibility itself is infinite, for the raw
full-lattice power-law law (the `k = 1` case of the moment theorem). -/
theorem powerLaw_chi_eq_top_of_globalCriticalIntensity_le
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) {β : ℝ≥0}
    (hβ : globalCriticalIntensity J ≤ (β : ℝ≥0∞)) :
    chi (intensityProfile J β) o = ⊤ := by
  simpa [chi, pow_one] using
    powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le
      hd hα J hJ o hβ (k := 1) le_rfl

/-- Explicit radial-kernel form of the moment theorem for the raw full-lattice power-law law. -/
theorem radialKernel_powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α) (o : Fin d → ℤ) {β : ℝ≥0}
    {J : Sym2 (Fin d → ℤ) → ℝ≥0}
    (hβ : globalCriticalIntensity J ≤ (β : ℝ≥0∞)) {k : ℕ} (hk : 1 ≤ k)
    (hJ : J = radialKernel (normSeminorm ℝ (Fin d → ℝ)) (powerLawProfile 1 ((d : ℝ) + α))) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) = ⊤ :=
  powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le hd hα J
    (fun x y => by
      rw [hJ]
      exact PercLib.Percolation.Bond.Exploration.BFS.radialKernel_powerLaw_mk hα x y)
    o hβ hk

/-- **At the critical intensity itself every positive-order moment is infinite.**  This is the
`β = β_c` case (valid whenever `β_c < ⊤`, i.e. `β_c ≠ ⊤`), the point the strict-subcritical
statements must not silently cross. -/
theorem powerLaw_lintegral_encard_cluster_pow_eq_top_at_globalCriticalIntensity
    {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) (hb : globalCriticalIntensity J ≠ ⊤) {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂
        (law (intensityProfile J (globalCriticalIntensity J).toNNReal)) = ⊤ := by
  refine powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le
    hd hα J hJ o ?_ hk
  rw [ENNReal.coe_toNNReal hb]

/-- **Moment threshold summary for the raw full-lattice power-law law.**  For every `k ≥ 1`:
the `k`-th cluster moment is infinite at every `β ≥ β_c`, and the parameters with finite moment form
a downward closed set (hence are contained in `[0, β_c)`). -/
theorem powerLaw_moment_threshold {d : ℕ} (hd : 1 ≤ d) {α : ℝ} (hα : 0 < α)
    (J : Sym2 (Fin d → ℤ) → ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = Real.toNNReal ((‖y - x‖ : ℝ) ^ (-((d : ℝ) + α))))
    (o : Fin d → ℤ) {k : ℕ} (hk : 1 ≤ k) :
    (∀ β : ℝ≥0, globalCriticalIntensity J ≤ (β : ℝ≥0∞) →
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) = ⊤) ∧
      (∀ β β' : ℝ≥0, β' ≤ β →
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β)) ≠ ⊤ →
        ∫⁻ ω, ((cluster ω o).encard : ℝ≥0∞) ^ k ∂(law (intensityProfile J β')) ≠ ⊤) :=
  ⟨fun _ hβ => powerLaw_lintegral_encard_cluster_pow_eq_top_of_globalCriticalIntensity_le
      hd hα J hJ o hβ hk,
    fun _ _ hβ hfin => lintegral_encard_cluster_pow_ne_top_of_le
      (fun e => intensityProfile_mono J hβ e) o k hfin⟩

end PercLib.Models.LongRange
