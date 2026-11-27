/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Probability.Exploration.PriorityTailComparison

/-!
# Infinite-cluster bounds from finite-susceptibility comparison

## Main results

The finite-volume tail comparison bounds the actual probability of an infinite
root cluster at a larger intensity by the quadratic intensity error times the
susceptibility at a smaller intensity. Finiteness is required only at the source
intensity, where it justifies sending the tail threshold to infinity. A reciprocal
susceptibility bound along a sequence approaching the endpoint then forces its
infinite-cluster probability to vanish.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*} [Countable V]

/-- The actual infinite-cluster probability at the target intensity is bounded
by the quadratic comparison error. Only the source susceptibility must be finite. -/
theorem law_infinite_cluster_intensity_le_quadratic
    (o : V) (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0)
    (h₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (M : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M)
    (hchi : chi (intensityProfile J β₁) o ≠ ⊤) :
    law (intensityProfile J β₂) {ω : Config V | (cluster ω o).Infinite} ≤
      ENNReal.ofReal ((M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁) *
        chi (intensityProfile J β₁) o := by
  have htail (n : ℕ) (hn : 1 ≤ n) :
      law (intensityProfile J β₂) {ω : Config V | (cluster ω o).Infinite} ≤
        (2 / (n : ℝ≥0∞) + ENNReal.ofReal
          ((M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁)) * chi (intensityProfile J β₁) o := by
    refine (measure_mono ?_).trans
      (law_le_encard_cluster_intensity_le_chi_quadratic o n hn J β₁ β₂ h₁ hβ M hrow)
    intro ω hω
    change (n : ℕ∞) ≤ (cluster ω o).encard
    rw [hω.encard_eq]
    exact le_top
  have hzero : Tendsto (fun n : ℕ => (2 : ℝ≥0∞) / n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
        (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hlim : Tendsto (fun n : ℕ =>
      (2 / (n : ℝ≥0∞) + ENNReal.ofReal
        ((M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁)) * chi (intensityProfile J β₁) o)
      atTop (𝓝 (ENNReal.ofReal ((M : ℝ) * ((β₂ : ℝ) - β₁) ^ 2 / β₁) *
        chi (intensityProfile J β₁) o)) := by
    simpa only [zero_add] using ENNReal.Tendsto.mul_const
      (hzero.add tendsto_const_nhds) (Or.inr hchi)
  exact ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun n hn => htail n hn)

/-- A reciprocal susceptibility bound along intensities approaching an endpoint
forces the actual infinite-cluster probability at that endpoint to vanish.
The susceptibility bound is required only along the strictly smaller intensities. -/
theorem law_infinite_cluster_intensity_eq_zero_of_reciprocal_chi_bound
    (o : V) (J : Sym2 V → ℝ≥0) (b : ℝ≥0) (β : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < β n) (hlt : ∀ n, β n < b)
    (hlim : Tendsto (fun n => (β n : ℝ)) atTop (𝓝 (b : ℝ)))
    (M C : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M)
    (hchi : ∀ n, chi (intensityProfile J (β n)) o ≤
      ENNReal.ofReal ((C : ℝ) / ((b : ℝ) - β n))) :
    law (intensityProfile J b) {ω : Config V | (cluster ω o).Infinite} = 0 := by
  have hb : 0 < (b : ℝ) := NNReal.coe_pos.mpr ((hpos 0).trans (hlt 0))
  have hbound (n : ℕ) :
      law (intensityProfile J b) {ω : Config V | (cluster ω o).Infinite} ≤
        ENNReal.ofReal ((M : ℝ) * C * ((b : ℝ) - β n) / β n) := by
    have hβ : 0 < (β n : ℝ) := NNReal.coe_pos.mpr (hpos n)
    have hgap : 0 < (b : ℝ) - β n := sub_pos.mpr (NNReal.coe_lt_coe.mpr (hlt n))
    refine (law_infinite_cluster_intensity_le_quadratic o J (β n) b
      (hpos n) (hlt n).le M hrow
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hchi n))).trans ?_
    calc
      _ ≤ ENNReal.ofReal ((M : ℝ) * ((b : ℝ) - β n) ^ 2 / β n) *
          ENNReal.ofReal ((C : ℝ) / ((b : ℝ) - β n)) :=
        mul_le_mul' le_rfl (hchi n)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [hβ.ne', hgap.ne']
  have hgaplim : Tendsto (fun n => (b : ℝ) - β n) atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (b : ℝ)) atTop (𝓝 (b : ℝ))).sub hlim
  have hnum : Tendsto (fun n => (M : ℝ) * C * ((b : ℝ) - β n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hgaplim.const_mul ((M : ℝ) * C)
  have hreal : Tendsto (fun n => (M : ℝ) * C * ((b : ℝ) - β n) / β n)
      atTop (𝓝 0) := by
    convert hnum.div hlim hb.ne' using 1
    simp only [zero_div]
  have herr : Tendsto (fun n => ENNReal.ofReal
      ((M : ℝ) * C * ((b : ℝ) - β n) / β n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact le_antisymm (ge_of_tendsto herr (Eventually.of_forall hbound)) bot_le

/-- A reciprocal susceptibility bound throughout a nonempty left neighborhood
of an endpoint implies nonpercolation at the endpoint itself. -/
theorem law_infinite_cluster_intensity_eq_zero_of_chi_le_on_Ioo
    (o : V) (J : Sym2 V → ℝ≥0) {a b : ℝ≥0} (hab : a < b)
    (M C : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M)
    (hchi : ∀ β ∈ Ioo a b, chi (intensityProfile J β) o ≤
      ENNReal.ofReal ((C : ℝ) / ((b : ℝ) - β))) :
    law (intensityProfile J b) {ω : Config V | (cluster ω o).Infinite} = 0 := by
  have hb : b ∈ closure (Ioo a b) := by
    rw [closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  obtain ⟨β, hβ, hlim⟩ := mem_closure_iff_seq_limit.mp hb
  exact law_infinite_cluster_intensity_eq_zero_of_reciprocal_chi_bound o J b β
    (fun n => (show (0 : ℝ≥0) ≤ a from bot_le).trans_lt (hβ n).1) (fun n => (hβ n).2)
    (NNReal.continuous_coe.continuousAt.tendsto.comp hlim) M C hrow
    (fun n => hchi (β n) (hβ n))

/-- The same actual endpoint bound gives almost surely finite root clusters,
which can be used in the critical lace-expansion event identities. -/
theorem ae_finite_cluster_intensity_of_chi_le_on_Ioo
    (o : V) (J : Sym2 V → ℝ≥0) {a b : ℝ≥0} (hab : a < b)
    (M C : ℝ≥0) (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ M)
    (hchi : ∀ β ∈ Ioo a b, chi (intensityProfile J β) o ≤
      ENNReal.ofReal ((C : ℝ) / ((b : ℝ) - β))) :
    ∀ᵐ ω ∂law (intensityProfile J b), (cluster ω o).Finite := by
  rw [ae_iff]
  exact law_infinite_cluster_intensity_eq_zero_of_chi_le_on_Ioo o J hab M C hrow hchi

end PercLib.Percolation.Bond
