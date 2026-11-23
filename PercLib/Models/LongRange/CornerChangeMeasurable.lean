/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof-only results, derived here; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5. The results below are measurability and integration statements for the
softened-edge coupling on `Fin d → ℤ`; they assert no continuity or derivative claim.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.UnionChangeIntegral
public import PercLib.Models.LongRange.CornerCoupling
public import PercLib.Models.LongRange.TruncatedMoments

/-!
# The change event of the softened-edge coupling on `Fin d → ℤ`

This file specialises the generic measurability certificate of `UnionChange.lean` and
`UnionChangeIntegral.lean` to the lattice `Fin d → ℤ` and to the scale-`n` support
`PercLib.Models.LongRange.scaleSupport n` of the reopening profile.

* `measurableSet_unionChange_lattice`: the change event
  `{z | cluster z.1 o ≠ cluster (z.1 ∪ z.2) o}` is measurable — the exact event whose indicator
  `PercLib.Models.LongRange.measure_change_le` bounds in probability.
* `measurable_encard_cluster_union_toENNReal`, `..._pow_toENNReal`: the (power of the) volume of
  the union cluster of `o` is a measurable function of the pair of configurations.  This is the
  measurability obligation of the `lintegral_const_mul` step in the capped moment estimate.
* `lintegral_union_change_pow_encard`: the exact identity expressing a change of the `p`-th
  cluster moment under `ω ↦ ω ∪ D` as an integral over the change event.
* `exists_crossingPair_bounded_of_mem_unionChange`: on the support `z.2 ⊆ scaleSupport n`, every
  change is witnessed by an ordered pair `(u, v)` with `u` in the old cluster, `v` outside it,
  `s(u, v) ∈ z.2` and the *length bound* `0 < ‖v - u‖ ≤ n`.  The positivity and the bound come
  from the support of the reopening profile, not from any further hypothesis.
* `ae_unionChange_iff_bounded_crossing`: the same as an almost-everywhere equivalence between the
  change event and the bounded crossing event.
* `lintegral_capped_change_bound`: the capped integration step for the `p`-th moment of the union
  cluster, with every measurability obligation discharged and with the pointwise cap
  `encard_pow_le_cap` used only through the measurable change event.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {d : ℕ}

/-! ### Measurability on the lattice -/

/-- The change event in the spelling used by the softened-edge coupling: the cluster of `o`
differs between `ω` and `ω ∪ D`. -/
theorem measurableSet_unionChange_lattice (o : Fin d → ℤ) :
    MeasurableSet {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
      cluster z.1 o ≠ cluster (z.1 ∪ z.2) o} :=
  measurableSet_unionChange' o

/-- The volume of the union cluster of `o` is measurable in the configuration pair. -/
theorem measurable_encard_cluster_union_toENNReal (o : Fin d → ℤ) :
    Measurable fun z : Config (Fin d → ℤ) × Config (Fin d → ℤ) =>
      ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) :=
  (measurable_encard_cluster_toENNReal (V := Fin d → ℤ) o).comp measurable_union_config

/-- The `p`-th power of the volume of the union cluster of `o` is measurable. -/
theorem measurable_encard_cluster_union_pow_toENNReal (o : Fin d → ℤ) (p : ℕ) :
    Measurable fun z : Config (Fin d → ℤ) × Config (Fin d → ℤ) =>
      ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p :=
  (measurable_encard_cluster_union_toENNReal o).pow_const p

/-- The `p`-th power of the volume of the old cluster of `o` is measurable. -/
theorem measurable_encard_cluster_fst_pow_toENNReal (o : Fin d → ℤ) (p : ℕ) :
    Measurable fun z : Config (Fin d → ℤ) × Config (Fin d → ℤ) =>
      ((cluster z.1 o).encard : ℝ≥0∞) ^ p :=
  ((measurable_encard_cluster_toENNReal (V := Fin d → ℤ) o).pow_const p).comp measurable_fst

/-! ### The exact moment increment identity -/

/-- The `p`-th moment of the volume of the union cluster of `o` equals the `p`-th moment of the
old cluster plus the integral over the change event of the pointwise increment. -/
theorem lintegral_union_change_pow_encard (o : Fin d → ℤ)
    (γ : Measure (Config (Fin d → ℤ) × Config (Fin d → ℤ))) (p : ℕ) :
    ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p ∂γ
      = ∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ
        + ∫⁻ z, (unionChange o).indicator
            (fun z => ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p -
              ((cluster z.1 o).encard : ℝ≥0∞) ^ p) z ∂γ := by
  refine lintegral_union_change o γ (Φ := fun S : Set (Fin d → ℤ) => ((S.encard : ℝ≥0∞) ^ p))
    ?_ ((measurable_encard_cluster_toENNReal (V := Fin d → ℤ) o).pow_const p)
  intro S T hST
  have h : ((S.encard : ℝ≥0∞)) ≤ ((T.encard : ℝ≥0∞)) := by
    exact_mod_cast Set.encard_le_encard hST
  simpa using pow_le_pow_left' h p

/-! ### The support of the reopening profile gives the length bound -/

/-- On the scale-`n` support, a change of the cluster of `o` is witnessed by an ordered pair
`(u, v)` with `u` in the old cluster, `v` outside it, the pair `s(u, v)` opened by `D`, and
`0 < ‖v - u‖ ≤ n`. -/
theorem exists_crossingPair_bounded_of_mem_unionChange {n : ℕ} {o : Fin d → ℤ}
    {z : Config (Fin d → ℤ) × Config (Fin d → ℤ)}
    (hz : z.2 ⊆ PercLib.Models.LongRange.scaleSupport n) (hchg : z ∈ unionChange o) :
    ∃ p : (Fin d → ℤ) × (Fin d → ℤ), p.1 ∈ cluster z.1 o ∧ p.2 ∉ cluster z.1 o ∧
      0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2 := by
  obtain ⟨p, hp⟩ := mem_iUnion.1 (unionChange_eq_iUnion_crossingPair o ▸ hchg)
  obtain ⟨hu, hv, hD⟩ := mem_crossingPair.1 hp
  have hne : p.1 ≠ p.2 := fun h => hv (h ▸ hu)
  have hS : s(p.1, p.2) ∈ PercLib.Models.LongRange.scaleSupport n := hz hD
  have hb : ‖p.1 - p.2‖ ≤ (n : ℝ) := (PercLib.Models.LongRange.mem_scaleSupport_mk hne).1 hS
  exact ⟨p, hu, hv, by rw [norm_sub_rev]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hne),
    by rwa [norm_sub_rev], hD⟩

/-- **Almost-everywhere representation of the change event.**  If the second marginal of `γ` is
supported on the scale-`n` edge set, then almost every point of the change event is a *bounded*
crossing: an ordered pair `(u, v)` with `u` in the old cluster of `o`, `v` outside it, the pair
opened by `D`, and length at most `n` (and positive).  The reverse implication needs no support
hypothesis, so this is an equivalence almost everywhere. -/
theorem ae_unionChange_iff_bounded_crossing {n : ℕ} {o : Fin d → ℤ}
    (γ : Measure (Config (Fin d → ℤ) × Config (Fin d → ℤ)))
    (hae : ∀ᵐ z ∂γ, z.2 ⊆ PercLib.Models.LongRange.scaleSupport n) :
    ∀ᵐ z ∂γ, (z ∈ unionChange o ↔ ∃ p : (Fin d → ℤ) × (Fin d → ℤ),
      p.1 ∈ cluster z.1 o ∧ p.2 ∉ cluster z.1 o ∧ 0 < ‖p.2 - p.1‖ ∧
        ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2) := by
  filter_upwards [hae] with z hz
  constructor
  · exact exists_crossingPair_bounded_of_mem_unionChange hz
  · rintro ⟨p, hu, hv, -, -, hD⟩
    exact unionChange_eq_iUnion_crossingPair o ▸
      mem_iUnion.2 ⟨p, mem_crossingPair.2 ⟨hu, hv, hD⟩⟩

/-- The covering event used by `PercLib.Models.LongRange.measure_change_le`: on the scale-`n`
support, the change event is contained in the event that some pair of length at most `n` from the
old cluster is opened by `D` (the condition that the far endpoint lies outside the old cluster is
dropped). -/
theorem unionChange_subset_badPair_event {n : ℕ} {o : Fin d → ℤ} :
    unionChange o ∩ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
        z.2 ⊆ PercLib.Models.LongRange.scaleSupport n}
      ⊆ {z : Config (Fin d → ℤ) × Config (Fin d → ℤ) |
          ∃ p : (Fin d → ℤ) × (Fin d → ℤ), p.1 ∈ cluster z.1 o ∧
            0 < ‖p.2 - p.1‖ ∧ ‖p.2 - p.1‖ ≤ (n : ℝ) ∧ s(p.1, p.2) ∈ z.2} := by
  rintro z ⟨hchg, hz⟩
  obtain ⟨p, hu, -, hpos, hlen, hD⟩ := exists_crossingPair_bounded_of_mem_unionChange hz hchg
  exact ⟨p, hu, hpos, hlen, hD⟩

/-! ### The capped integration step -/

/-- **The capped change bound for the `p`-th moment of the union cluster.**  Pointwise, the `p`-th
power of the volume of the union cluster is at most the `p`-th power of the old volume plus `B ^ p`
on the change event plus `B⁻¹` times the `(p + 1)`-st power of the union volume
(`encard_pow_le_cap`).  Integrating that inequality uses the measurability of the change event and
of both cluster volumes, and yields the bound below.  This is the integration step of the
softened-edge estimate `moment_le_soften`, with no measurability obligation left open. -/
theorem lintegral_capped_change_bound (o : Fin d → ℤ)
    (γ : Measure (Config (Fin d → ℤ) × Config (Fin d → ℤ))) (p : ℕ) {B : ℕ} (hB : 1 ≤ B) :
    ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p ∂γ
      ≤ ∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ
        + (B : ℝ≥0∞) ^ p * γ (unionChange o)
        + (B : ℝ≥0∞)⁻¹ *
          ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ := by
  refine lintegral_le_of_pointwise_capped
    (s := unionChange o) (measurableSet_unionChange o)
    (measurable_encard_cluster_fst_pow_toENNReal o p)
    (measurable_encard_cluster_union_pow_toENNReal o (p + 1)) ((B : ℝ≥0∞) ^ p) ((B : ℝ≥0∞)⁻¹) ?_
  intro z
  have hcap := PercLib.Models.LongRange.encard_pow_le_cap p B hB (cluster (z.1 ∪ z.2) o).encard
  by_cases hz : z ∈ unionChange o
  · rw [indicator_of_mem hz, mul_one]
    calc ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p
        ≤ (B : ℝ≥0∞) ^ p + (B : ℝ≥0∞)⁻¹ *
            ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) := hcap
      _ ≤ ((cluster z.1 o).encard : ℝ≥0∞) ^ p + (B : ℝ≥0∞) ^ p +
            (B : ℝ≥0∞)⁻¹ * ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) :=
          add_le_add_left
            (le_add_self (a := (B : ℝ≥0∞) ^ p)
              (b := ((cluster z.1 o).encard : ℝ≥0∞) ^ p)) _
  · rw [indicator_of_notMem hz, mul_zero, add_zero]
    rw [cluster_eq_of_notMem_unionChange hz]
    exact le_self_add

/-- **The real-valued form of the capped change bound.**  This is the shape a right-continuity
argument consumes: with `A` the old `p`-th moment, `γ` the joint law and `B ≥ 1` a cap, the new
`p`-th moment is at most `A` plus `B ^ p` times the probability of the measurable change event plus
`B⁻¹` times the `(p + 1)`-st moment of the new cluster.  The hypothesis that the two `ℝ≥0∞`
integrals and the measure of the change event are finite is exactly what is needed to pass
`toReal` through the additions and products. -/
theorem toReal_lintegral_capped_change_bound (o : Fin d → ℤ)
    (γ : Measure (Config (Fin d → ℤ) × Config (Fin d → ℤ))) (p : ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hγ : γ (unionChange o) ≠ ⊤)
    (hold : (∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ) ≠ ⊤)
    (hnew : (∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ) ≠ ⊤) :
    (∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p ∂γ).toReal
      ≤ (∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ).toReal
        + (B : ℝ) ^ p * (γ (unionChange o)).toReal
        + (B : ℝ)⁻¹ *
          (∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ).toReal := by
  have hcap := lintegral_capped_change_bound o γ p hB
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hC1 : (B : ℝ≥0∞) ^ p * γ (unionChange o) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top B)) hγ
  have hC2 : (B : ℝ≥0∞)⁻¹ *
      ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hB0) hnew
  have hRHS : (∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ) +
      (B : ℝ≥0∞) ^ p * γ (unionChange o) +
      (B : ℝ≥0∞)⁻¹ * ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hold, hC1⟩, hC2⟩
  calc (∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ p ∂γ).toReal
      ≤ ((∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ) +
          (B : ℝ≥0∞) ^ p * γ (unionChange o) +
          (B : ℝ≥0∞)⁻¹ *
            ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ).toReal :=
        ENNReal.toReal_mono hRHS hcap
    _ = (∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ).toReal
          + ((B : ℝ≥0∞) ^ p * γ (unionChange o)).toReal
          + ((B : ℝ≥0∞)⁻¹ *
              ∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ).toReal := by
        rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hold, hC1⟩) hC2,
          ENNReal.toReal_add hold hC1]
    _ = (∫⁻ z, ((cluster z.1 o).encard : ℝ≥0∞) ^ p ∂γ).toReal
          + (B : ℝ) ^ p * (γ (unionChange o)).toReal
          + (B : ℝ)⁻¹ *
              (∫⁻ z, ((cluster (z.1 ∪ z.2) o).encard : ℝ≥0∞) ^ (p + 1) ∂γ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
          ENNReal.toReal_inv, ENNReal.toReal_natCast]


end PercLib.Percolation.Bond
