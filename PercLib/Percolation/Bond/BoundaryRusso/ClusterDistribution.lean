/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Original proofs using the canonical finite-cluster law, finite-volume approximation,
and finite-volume boundary Russo identity. No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.BoundaryRusso
public import PercLib.Percolation.Bond.BoundarySusceptibility
public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.IndependentLayer
public import PercLib.Percolation.Bond.ProfileRegularity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Boundary expectations and finite-volume exhaustion

## Main results

Finite root clusters eventually stabilize along any increasing vertex exhaustion.
Finite-cluster functionals have an exact countable distribution formula, with value zero
on infinite clusters. The boundary susceptibility is bounded by the cluster cardinality
times the intensity row cap and the uniform susceptibility.

All finiteness used here is derived from susceptibility bounds where these are assumed;
there is no premise that every configuration, or any critical cluster, is finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- A finite root cluster eventually equals its restriction to an increasing exhaustion.
The restricted clusters themselves are increasing; no assertion about boundary functionals
being monotone is needed. -/
theorem eventually_localCluster_eq_cluster_of_finite
    {S : ℕ → Set V} (hS : Monotone S) (hcover : ∀ v, ∃ n, v ∈ S n)
    (ω : Config V) (o : V) (hfin : (cluster ω o).Finite) :
    ∀ᶠ n in atTop, localCluster ω (S n) o = cluster ω o := by
  have hsub : (hfin.toFinset : Set V) ⊆ ⋃ n, localCluster ω (S n) o := by
    rw [hfin.coe_toFinset, iUnion_induce_cluster hS hcover]
  have hmono := monotone_induce_cluster hS ω o
  obtain ⟨N, hN⟩ := hmono.directed_le.exists_mem_subset_of_finset_subset_biUnion hsub
  filter_upwards [eventually_ge_atTop N] with n hn
  refine le_antisymm ((localCluster_subset ω (S n) o).trans inter_subset_left) ?_
  rw [← hfin.coe_toFinset]
  exact hN.trans (monotone_induce_cluster hS ω o hn)

open Classical in
/-- A finite-cluster functional is the sum of its values on the disjoint cluster events;
an infinite cluster contributes zero. This is a deterministic identity. -/
theorem finite_cluster_functional_eq_tsum (ω : Config V) (o : V)
    (F : Finset V → ℝ≥0∞) :
    (if h : (cluster ω o).Finite then F h.toFinset else 0) =
      ∑' C : Finset V, {ω : Config V | cluster ω o = (C : Set V)}.indicator
        (fun _ => F C) ω := by
  by_cases hfin : (cluster ω o).Finite
  · rw [dite_eq_left hfin, tsum_eq_single hfin.toFinset]
    · simp [hfin.coe_toFinset]
    · intro C hC
      have hne : cluster ω o ≠ (C : Set V) := by
        intro h
        apply hC
        apply Finset.coe_injective
        rw [hfin.coe_toFinset]
        exact h.symm
      simp [Set.indicator, hne]
  · rw [dite_eq_right hfin]
    have hz (C : Finset V) : {ω : Config V | cluster ω o = (C : Set V)}.indicator
        (fun _ => F C) ω = 0 := by
      have hne : cluster ω o ≠ (C : Set V) := fun h =>
        hfin (h.symm ▸ C.finite_toSet)
      simp [Set.indicator, hne]
    simp only [hz, tsum_zero]

open Classical in
/-- Finite-cluster functionals are measurable, with zero assigned on infinite clusters. -/
theorem measurable_finite_cluster_functional [Countable V] (o : V)
    (F : Finset V → ℝ≥0∞) :
    Measurable (fun ω : Config V =>
      if h : (cluster ω o).Finite then F h.toFinset else 0) := by
  simp_rw [finite_cluster_functional_eq_tsum]
  exact Measurable.tsum fun C => measurable_const.indicator
    (measurableSet_setOf_cluster_eq o (C : Set V))

open Classical in
/-- Exact countable finite-cluster distribution formula, without a finite-cluster or
finite-moment assumption. Both sides may be infinite. -/
theorem lintegral_finite_cluster_functional_eq_tsum [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (F : Finset V → ℝ≥0∞) :
    (∫⁻ ω, (if h : (cluster ω o).Finite then F h.toFinset else 0) ∂law q) =
      ∑' C : Finset V, law q {ω : Config V | cluster ω o = (C : Set V)} * F C := by
  simp_rw [finite_cluster_functional_eq_tsum]
  rw [lintegral_tsum (fun C : Finset V => (measurable_const.indicator
    (measurableSet_setOf_cluster_eq o (C : Set V))).aemeasurable)]
  refine tsum_congr fun C => ?_
  rw [lintegral_indicator_const (measurableSet_setOf_cluster_eq o (C : Set V)), mul_comm]

open Classical in
/-- The real expectation form of the finite-cluster distribution formula. Nonnegative
functionals are allowed even before proving their integrability; both real expressions use
the usual zero convention when the nonnegative expectation is infinite. -/
theorem integral_finite_cluster_functional_eq_tsum [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (F : Finset V → ℝ) (hF : ∀ C, 0 ≤ F C) :
    (∫ ω, (if h : (cluster ω o).Finite then F h.toFinset else 0) ∂law q) =
      ∑' C : Finset V, (law q).real {ω : Config V | cluster ω o = (C : Set V)} * F C := by
  let G : Config V → ℝ≥0∞ := fun ω =>
    if h : (cluster ω o).Finite then ENNReal.ofReal (F h.toFinset) else 0
  have hG : Measurable G := measurable_finite_cluster_functional o (fun C => .ofReal (F C))
  have hGr : ∀ ω, (G ω).toReal =
      (if h : (cluster ω o).Finite then F h.toFinset else 0) := by
    intro ω
    dsimp [G]
    split_ifs <;> simp [ENNReal.toReal_ofReal, hF]
  have hGt : ∀ ω, G ω < ⊤ := by
    intro ω
    dsimp [G]
    split_ifs <;> simp
  simp_rw [← hGr]
  rw [integral_toReal hG.aemeasurable (Eventually.of_forall hGt)]
  change (∫⁻ ω, (if h : (cluster ω o).Finite then
    ENNReal.ofReal (F h.toFinset) else 0) ∂law q).toReal = _
  rw [lintegral_finite_cluster_functional_eq_tsum q o (fun C => ENNReal.ofReal (F C)),
    ENNReal.tsum_toReal_eq fun C => ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top]
  refine tsum_congr fun C => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hF C)]
  rfl

/-- Finite susceptibility is the first moment of the actual finite-cluster distribution.
Almost sure finiteness is a consequence, not a separate hypothesis. -/
theorem tsum_law_cluster_eq_mul_card_eq_chi [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (hχ : chi q o ≠ ⊤) :
    (∑' C : Finset V, law q {ω : Config V | cluster ω o = (C : Set V)} * C.card) =
      chi q o := by
  classical
  rw [← lintegral_finite_cluster_functional_eq_tsum, chi]
  apply lintegral_congr_ae
  filter_upwards [ae_cluster_finite_of_chi_lt_top hχ.lt_top] with ω hω
  rw [dite_eq_left hω, hω.encard_eq_coe_toFinset_card]
  simp

open Classical in
/-- A finite set has boundary susceptibility at most its cardinality times the row cap
and the uniform susceptibility. Diagonal intensities do not enter the estimate. -/
theorem boundarySusceptibility_le_card_mul_row_cap [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤) (C : Finset V) :
    boundarySusceptibility J β C ≤
      (C.card : ℝ) * (R : ℝ) * (⨆ v, chi (intensityProfile J β) v).toReal := by
  let M := ⨆ v, chi (intensityProfile J β) v
  have hbound (u : V) (hu : u ∈ C) :
      (∑' v, (if v ∈ C then 0 else (J s(u, v) : ℝ≥0∞)) *
        ∑' w, law (intensityProfile J β) (localConn (C : Set V)ᶜ v w)) ≤ R * M := by
    calc
      _ ≤ ∑' v, (if v = u then 0 else (J s(u, v) : ℝ≥0∞)) * M := by
        refine ENNReal.tsum_le_tsum fun v => ?_
        by_cases hv : v ∈ C
        · simp [hv]
        · have hvu : v ≠ u := fun h => hv (h ▸ hu)
          rw [ite_eq_right hv, ite_eq_right hvu]
          exact mul_le_mul_right
            ((tsum_law_deleted_le_chi _ _ v).trans (le_iSup _ v)) _
      _ = rowSum (fun e => (J e : ℝ≥0∞)) u * M := by
        rw [rowSum_def, ENNReal.tsum_mul_right]
      _ ≤ R * M := mul_le_mul_left (hrow u) _
  rw [boundarySusceptibility_eq]
  calc
    _ ≤ ∑ _u ∈ C, (R : ℝ) * M.toReal := by
      refine Finset.sum_le_sum fun u hu => ?_
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hχ) (hbound u hu)
      rwa [toReal_boundaryRow J β C hχ u, ENNReal.toReal_mul, ENNReal.coe_toReal] at h
    _ = _ := by simp [nsmul_eq_mul, mul_assoc, M]

/-- The actual expected boundary susceptibility has a finite quantitative envelope:
row cap times uniform susceptibility times susceptibility at the root. -/
theorem tsum_law_cluster_eq_mul_ofReal_boundarySusceptibility_le [Countable V]
    (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (o : V) (R : ℝ≥0)
    (hrow : ∀ v, rowSum (fun e => (J e : ℝ≥0∞)) v ≤ R)
    (hχ : (⨆ v, chi (intensityProfile J β) v) ≠ ⊤) :
    (∑' C : Finset V, law (intensityProfile J β)
        {ω : Config V | cluster ω o = (C : Set V)} *
        ENNReal.ofReal (boundarySusceptibility J β C)) ≤
      (R : ℝ≥0∞) * (⨆ v, chi (intensityProfile J β) v) *
        chi (intensityProfile J β) o := by
  let q := intensityProfile J β
  let M := ⨆ v, chi q v
  have hPhi (C : Finset V) : ENNReal.ofReal (boundarySusceptibility J β C) ≤
      (C.card : ℝ≥0∞) * R * M := by
    calc
      _ ≤ ENNReal.ofReal ((C.card : ℝ) * (R : ℝ) * M.toReal) :=
        ENNReal.ofReal_le_ofReal (boundarySusceptibility_le_card_mul_row_cap J β R hrow hχ C)
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) R.coe_nonneg),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hχ]
  calc
    _ ≤ ∑' C : Finset V, law q {ω : Config V | cluster ω o = (C : Set V)} *
        ((C.card : ℝ≥0∞) * R * M) := ENNReal.tsum_le_tsum fun C => mul_le_mul_right (hPhi C) _
    _ = (R : ℝ≥0∞) * M *
        ∑' C : Finset V, law q {ω : Config V | cluster ω o = (C : Set V)} * C.card := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun _ => by ring
    _ = _ := by
      rw [tsum_law_cluster_eq_mul_card_eq_chi q o
        (ne_top_of_le_ne_top hχ (le_iSup _ o))]

open Classical in
/-- Finiteness of the weighted finite-cluster distribution gives actual integrability
of the corresponding nonnegative cluster functional. -/
theorem integrable_finite_cluster_functional_of_tsum_ne_top [Countable V]
    (q : Sym2 V → unitInterval) (o : V) (F : Finset V → ℝ) (hF : ∀ C, 0 ≤ F C)
    (hfin : (∑' C : Finset V, law q {ω : Config V | cluster ω o = (C : Set V)} *
      ENNReal.ofReal (F C)) ≠ ⊤) :
    Integrable (fun ω : Config V =>
      if h : (cluster ω o).Finite then F h.toFinset else 0) (law q) := by
  have h := integrable_toReal_of_lintegral_ne_top (μ := law q)
    (measurable_finite_cluster_functional o (fun C => ENNReal.ofReal (F C))).aemeasurable
    (by rwa [lintegral_finite_cluster_functional_eq_tsum q o (fun C => ENNReal.ofReal (F C))])
  convert h using 1
  funext ω
  split_ifs <;> simp [ENNReal.toReal_ofReal, hF]

end PercLib.Percolation.Bond
