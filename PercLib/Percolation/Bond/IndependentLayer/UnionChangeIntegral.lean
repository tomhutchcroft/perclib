/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof-only results, derived here; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5. These are integral identities for the change event; they assert no continuity or
probability estimate.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.UnionChange
public import PercLib.Percolation.Bond.Susceptibility

/-!
# Integrals over the union-change event

`UnionChange.lean` proves that the event `unionChange o = {z | cluster (z.1 ∪ z.2) o ≠
cluster z.1 o}` is measurable.  This file records what that buys at the level of `lintegral`s.

* `measurable_union_config`: the union of the two coordinates is a measurable function
  `Config V × Config V → Config V` (the σ-algebra on `Set` is the coordinate one).
* `measurable_encard_cluster_union_toENNReal`: consequently the volume of the *union* cluster of
  `o` is a measurable function of the configuration pair.
* `lintegral_indicator_unionChange`: the integral of the indicator of the change event is the
  measure of the event, `γ (unionChange o)`.
* `lintegral_union_change`: for a monotone cluster functional `Φ`, the increment of `Φ` under
  `ω ↦ ω ∪ D` is exactly the integral of the pointwise increment, taken over the change event.
  This is the representation that a capped moment estimate uses to isolate the change
  probability.
* `setLIntegral_compl_unionChange`: restricted to the complement of the change event, the union
  cluster and the old cluster give the same integral; this is the "off the rare event the
  functional does not move" step, in integral form.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### The union of the two coordinates is measurable -/

/-- The union of the two coordinates is a measurable function into the configuration space. -/
theorem measurable_union_config :
    Measurable fun z : Config V × Config V => z.1 ∪ z.2 :=
  measurable_fst.union measurable_snd

/-! ### The change event -/

/-- Off the change event the two clusters are literally equal. -/
theorem cluster_eq_of_notMem_unionChange {o : V} {z : Config V × Config V}
    (hz : z ∉ unionChange o) : cluster (z.1 ∪ z.2) o = cluster z.1 o :=
  not_not.1 hz

/-- The pointwise increment vanishes off the change event. -/
theorem tsub_eq_zero_of_notMem_unionChange {o : V} {Φ : Set V → ℝ≥0∞}
    {z : Config V × Config V} (hz : z ∉ unionChange o) :
    Φ (cluster (z.1 ∪ z.2) o) - Φ (cluster z.1 o) = 0 := by
  rw [cluster_eq_of_notMem_unionChange hz, tsub_self]

/-- The indicator of the change event, with the pointwise increment as value, is the pointwise
increment itself: the increment is supported on the change event. -/
theorem indicator_unionChange_tsub {o : V} {Φ : Set V → ℝ≥0∞} {z : Config V × Config V} :
    (unionChange o).indicator
        (fun z => Φ (cluster (z.1 ∪ z.2) o) - Φ (cluster z.1 o)) z
      = Φ (cluster (z.1 ∪ z.2) o) - Φ (cluster z.1 o) := by
  by_cases hz : z ∈ unionChange o
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz, tsub_eq_zero_of_notMem_unionChange hz]

/-- **The change-event representation.**  For a monotone cluster functional `Φ` whose value on the
cluster of `o` is measurable, the increment of `Φ` under `ω ↦ ω ∪ D` is the integral over the
change event of the pointwise increment:

`∫⁻ z, Φ (cluster (ω ∪ D) o) = ∫⁻ z, Φ (cluster ω o) + ∫⁻ z, 1_{change} (Φ (cluster (ω ∪ D) o) -
Φ (cluster ω o))`.

Nothing is divided, capped or estimated here; the identity is exact in `ℝ≥0∞`. -/
theorem lintegral_union_change (o : V) (γ : Measure (Config V × Config V))
    {Φ : Set V → ℝ≥0∞} (hΦ : Monotone Φ)
    (hmeas : Measurable fun ω : Config V => Φ (cluster ω o)) :
    ∫⁻ z, Φ (cluster (z.1 ∪ z.2) o) ∂γ
      = ∫⁻ z, Φ (cluster z.1 o) ∂γ
        + ∫⁻ z, (unionChange o).indicator
            (fun z => Φ (cluster (z.1 ∪ z.2) o) - Φ (cluster z.1 o)) z ∂γ := by
  have hle : ∀ z : Config V × Config V,
      Φ (cluster z.1 o) ≤ Φ (cluster (z.1 ∪ z.2) o) := fun z =>
    hΦ (cluster_mono subset_union_left o)
  have hpt : ∀ z : Config V × Config V, Φ (cluster (z.1 ∪ z.2) o) =
      Φ (cluster z.1 o) +
        (unionChange o).indicator
          (fun z => Φ (cluster (z.1 ∪ z.2) o) - Φ (cluster z.1 o)) z := by
    intro z
    rw [indicator_unionChange_tsub]
    exact (add_tsub_cancel_of_le (hle z)).symm
  refine (lintegral_congr hpt).trans ?_
  exact lintegral_add_left (hmeas.comp measurable_fst) _

variable [Countable V]

/-- **The union cluster is a measurable set-valued function of the configuration pair.**  Any
measurable functional of the union cluster of `o` is therefore measurable; this is the general form
of the measurability obligation in a cluster-moment estimate. -/
theorem measurable_cluster_union (o : V) :
    Measurable fun z : Config V × Config V => cluster (z.1 ∪ z.2) o :=
  (measurable_cluster o).comp measurable_union_config

/-- The change-event identity for a functional that is measurable on the space of subsets (rather
than assumed measurable after composition with the cluster). -/
theorem lintegral_union_change' (o : V) (γ : Measure (Config V × Config V))
    {Φ : Set V → ℝ≥0∞} (hΦ : Monotone Φ) (hΦm : Measurable Φ) :
    ∫⁻ z, Φ (cluster (z.1 ∪ z.2) o) ∂γ
      = ∫⁻ z, Φ (cluster z.1 o) ∂γ
        + ∫⁻ z, (unionChange o).indicator
            (fun z => Φ (cluster (z.1 ∪ z.2) o) - Φ (cluster z.1 o)) z ∂γ :=
  lintegral_union_change o γ hΦ (hΦm.comp (measurable_cluster o))

/-- The integral of the indicator of the change event is the measure of the change event. -/
theorem lintegral_indicator_unionChange (o : V) (γ : Measure (Config V × Config V)) :
    ∫⁻ z, (unionChange o).indicator (fun _ => (1 : ℝ≥0∞)) z ∂γ = γ (unionChange o) := by
  rw [lintegral_indicator_const (measurableSet_unionChange o) 1, one_mul]

/-- Restricted to the complement of the change event, the two clusters give the same integral.
This is the "off the rare event nothing moves" statement in the form used when the increment term
is integrated over the change event only. -/
theorem setLIntegral_compl_unionChange (o : V) (γ : Measure (Config V × Config V))
    (Φ : Set V → ℝ≥0∞) :
    ∫⁻ z in (unionChange o)ᶜ, Φ (cluster (z.1 ∪ z.2) o) ∂γ
      = ∫⁻ z in (unionChange o)ᶜ, Φ (cluster z.1 o) ∂γ :=
  setLIntegral_congr_fun (measurableSet_unionChange o).compl fun _ hz =>
    congrArg Φ (cluster_eq_of_notMem_unionChange hz)

variable {α : Type*} [MeasurableSpace α]

/-! ### Integrating a pointwise capped bound

The generic integration step used by capped moment estimates: a pointwise bound whose correction
term is supported on a measurable rare event, integrated in `ℝ≥0∞`.
-/

/-- **Integration of a capped pointwise bound.**  If `f ≤ g + C · 1_s + D · h` pointwise, `s` is
measurable and `g`, `h` are measurable, then

`∫⁻ f ≤ ∫⁻ g + C * μ s + D * ∫⁻ h`.

The measurability of `s` is what makes the middle term `C * μ s` rather than an outer measure. -/
theorem lintegral_le_of_pointwise_capped {μ : Measure α} {f g h : α → ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) (hg : Measurable g) (hh : Measurable h)
    (C D : ℝ≥0∞)
    (hpt : ∀ z, f z ≤ g z + C * s.indicator (fun _ => (1 : ℝ≥0∞)) z + D * h z) :
    ∫⁻ z, f z ∂μ ≤ ∫⁻ z, g z ∂μ + C * μ s + D * ∫⁻ z, h z ∂μ := by
  have hind : Measurable fun z => s.indicator (fun _ => (1 : ℝ≥0∞)) z :=
    measurable_const.indicator hs
  have hstep : ∫⁻ z, g z + C * s.indicator (fun _ => (1 : ℝ≥0∞)) z + D * h z ∂μ
      = ∫⁻ z, g z ∂μ + C * μ s + D * ∫⁻ z, h z ∂μ := by
    rw [lintegral_add_left (f := fun z => g z + C * s.indicator (fun _ => (1 : ℝ≥0∞)) z)
      (hg.add (hind.const_mul C))]
    rw [lintegral_add_left (f := g) hg]
    rw [lintegral_const_mul C hind, lintegral_const_mul D hh]
    rw [lintegral_indicator_const hs (1 : ℝ≥0∞), one_mul]
  calc ∫⁻ z, f z ∂μ
      ≤ ∫⁻ z, g z + C * s.indicator (fun _ => (1 : ℝ≥0∞)) z + D * h z ∂μ :=
        lintegral_mono hpt
    _ = ∫⁻ z, g z ∂μ + C * μ s + D * ∫⁻ z, h z ∂μ := hstep


end PercLib.Percolation.Bond
