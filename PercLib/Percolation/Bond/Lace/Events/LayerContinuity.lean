/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original proofs for the canonical lace events; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Events.Continuity
public import PercLib.Percolation.Bond.Lace.Events.LayerLocalization
public import PercLib.Probability.FiniteLayerContinuity

/-!
# One-sided continuity for a fixed ordered coefficient tuple

## Main results

The probability of the canonical finite-layer coefficient event is continuous
from below an upper profile at which the incoming root clusters are almost
surely finite. The random deleted-cluster sets in its `E'` events are included
in this assertion.

Each layer is restricted to its own finite vertex set. The probability error
is bounded by the sum of the upper-profile escape probabilities, with
coefficient one on each term. Only a fixed ordered bond tuple is considered;
no exchange of a limit with a sum over tuples is asserted.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology PercLib.Probability
open scoped ENNReal symmDiff

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

open scoped Classical in
/-- The uniform approximation error for a fixed ordered bond tuple is at most
the sum of the incoming-root escape probabilities at the upper profile. -/
theorem abs_pi_law_coefficientEvent_sub_restrict_le [Countable V]
    (q q₀ : Sym2 V → unitInterval) (hqq₀ : q ≤ q₀) {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V) (S : Fin (n + 2) → Finset V) :
    let F : Fin (n + 2) → Finset (Sym2 V) :=
      fun i => (S i ×ˢ S i).image fun z => s(z.1, z.2)
    |(Measure.pi (fun _ : Fin (n + 2) => law q)).real (coefficientEvent x y b) -
        (Measure.pi (fun _ : Fin (n + 2) => law q)).real
          {ω | (fun i => ω i ∩ (F i : Set (Sym2 V))) ∈ coefficientEvent x y b}| ≤
      ∑ i : Fin (n + 2), (law q₀).real
        (⋃ z ∈ (S i : Set V)ᶜ, conn (Fin.cases x (fun j => (b j).2) i) z) := by
  classical
  intro F
  let r : Fin (n + 2) → V := Fin.cases x (fun j => (b j).2)
  let μ := Measure.pi (fun _ : Fin (n + 2) => law q)
  let B : Set (Fin (n + 2) → Config V) :=
    {ω | (fun i => ω i ∩ (F i : Set (Sym2 V))) ∈ coefficientEvent x y b}
  let escape (i : Fin (n + 2)) : Set (Config V) :=
    ⋃ z ∈ (S i : Set V)ᶜ, conn (r i) z
  have hB : MeasurableSet B :=
    (measurableSet_coefficientEvent x y b).preimage (Measurable.of_eval
      (fun i => (measurable_pi_apply i).inter measurable_const))
  have hdiff : coefficientEvent x y b ∆ B ⊆
      ⋃ i, {ω : Fin (n + 2) → Config V | ω i ∈ escape i} := by
    intro ω hω
    by_contra hescape
    have hcluster (i : Fin (n + 2)) : cluster (ω i) (r i) ⊆ (S i : Set V) := by
      intro z hz
      by_contra hzS
      exact hescape (mem_iUnion.mpr ⟨i,
        mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hzS, hz⟩⟩⟩)
    have hrestrict (i : Fin (n + 2)) :
        cluster (ω i ∩ (F i : Set (Sym2 V))) (r i) ⊆ (S i : Set V) :=
      (cluster_mono inter_subset_left _).trans (hcluster i)
    have hagree : ∀ i, ∀ u ∈ (S i : Set V), ∀ v ∈ (S i : Set V),
        (s(u, v) ∈ ω i ↔ s(u, v) ∈ ω i ∩ (F i : Set (Sym2 V))) := by
      intro i u hu v hv
      have huv : s(u, v) ∈ (F i : Set (Sym2 V)) :=
        Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
      simp only [mem_inter_iff, huv, and_true]
    have heq := mem_coefficientEvent_iff_of_cluster_subset_of_agree x y b
      hcluster hrestrict hagree
    rcases hω with hω | hω
    · exact hω.2 (heq.mp hω.1)
    · exact hω.2 (heq.mpr hω.1)
  calc
    |μ.real (coefficientEvent x y b) - μ.real B| ≤
        μ.real (coefficientEvent x y b ∆ B) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_coefficientEvent x y b).nullMeasurableSet hB.nullMeasurableSet
    _ ≤ μ.real (⋃ i, {ω : Fin (n + 2) → Config V | ω i ∈ escape i}) :=
      measureReal_mono hdiff (measure_ne_top _ _)
    _ ≤ ∑ i, μ.real {ω : Fin (n + 2) → Config V | ω i ∈ escape i} :=
      measureReal_iUnion_fintype_le _
    _ = ∑ i, (law q).real (escape i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg ENNReal.toReal
        ((measurePreserving_eval (fun _ : Fin (n + 2) => law q) i).measure_preimage
          (measurableSet_escape (r i) (S i : Set V)).nullMeasurableSet)
    _ ≤ ∑ i, (law q₀).real (escape i) := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (prodBernoulli_mono_event q q₀ hqq₀
          (measurableSet_escape (r i) (S i : Set V))
          (isUpperSet_escape (r i) (S i : Set V)))

/-- For a fixed ordered bond tuple, the canonical independent-layer event has
continuous probability from profiles below an upper profile with almost surely
finite incoming root clusters. No summation over bond tuples is involved. -/
theorem continuousWithinAt_pi_law_coefficientEvent_Iic [Countable V]
    (q₀ : Sym2 V → unitInterval) {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V)
    (hfin : ∀ i : Fin (n + 2), ∀ᵐ ω ∂law q₀,
      (cluster ω (Fin.cases x (fun j => (b j).2) i)).Finite) :
    ContinuousWithinAt
      (fun q : Sym2 V → unitInterval =>
        (Measure.pi (fun _ : Fin (n + 2) => law q)) (coefficientEvent x y b))
      (Iic q₀) q₀ := by
  classical
  let μ (q : Sym2 V → unitInterval) := Measure.pi (fun _ : Fin (n + 2) => law q)
  have hreal : ContinuousWithinAt
      (fun q : Sym2 V → unitInterval => (μ q).real (coefficientEvent x y b))
      (Iic q₀) q₀ := by
    rw [Metric.continuousWithinAt_iff']
    intro ε hε
    have hδ : 0 < ε / (3 * (n + 2 : ℕ)) := by positivity
    choose S hS using fun i : Fin (n + 2) =>
      exists_finset_law_escape_lt_of_ae_cluster_finite q₀
        (Fin.cases x (fun j => (b j).2) i) (hfin i) hδ
    have hsum : (∑ i : Fin (n + 2), (law q₀).real
        (⋃ z ∈ (S i : Set V)ᶜ, conn (Fin.cases x (fun j => (b j).2) i) z)) < ε / 3 := by
      calc
        _ < ∑ _ : Fin (n + 2), ε / (3 * (n + 2 : ℕ)) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hS i)
        _ = ε / 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hn]
    let F : Fin (n + 2) → Finset (Sym2 V) :=
      fun i => (S i ×ˢ S i).image fun z => s(z.1, z.2)
    let B : Set (Fin (n + 2) → Config V) :=
      {ω | (fun i => ω i ∩ (F i : Set (Sym2 V))) ∈ coefficientEvent x y b}
    have hBc : Continuous fun q : Sym2 V → unitInterval => μ q B := by
      have h := continuous_pi_prodBernoulli_of_determined F (A := B) (by
        intro ω η heq
        change ((fun i => ω i ∩ (F i : Set (Sym2 V))) ∈ coefficientEvent x y b) ↔
          ((fun i => η i ∩ (F i : Set (Sym2 V))) ∈ coefficientEvent x y b)
        rw [funext heq])
      exact h.comp (show Continuous
        (fun q : Sym2 V → unitInterval => fun _ : Fin (n + 2) => q) by fun_prop)
    have hBr : ContinuousAt (fun q : Sym2 V → unitInterval => (μ q).real B) q₀ :=
      (ENNReal.continuousAt_toReal (measure_ne_top (μ q₀) B)).comp
        (f := fun q : Sym2 V → unitInterval => μ q B) hBc.continuousAt
    have hevent : ∀ᶠ q in 𝓝[Iic q₀] q₀,
        |(μ q).real B - (μ q₀).real B| < ε / 3 := by
      have h := (Metric.continuousAt_iff'.mp hBr (ε / 3) (by positivity)).filter_mono
        (nhdsWithin_le_nhds (s := Iic q₀))
      simpa only [Real.dist_eq] using h
    filter_upwards [hevent, self_mem_nhdsWithin] with q hdiff hqq₀
    have ha := abs_pi_law_coefficientEvent_sub_restrict_le q q₀ hqq₀ x y b S
    have hb := abs_pi_law_coefficientEvent_sub_restrict_le q₀ q₀ le_rfl x y b S
    change |(μ q).real (coefficientEvent x y b) - (μ q).real B| ≤ _ at ha
    change |(μ q₀).real (coefficientEvent x y b) - (μ q₀).real B| ≤ _ at hb
    have hab := abs_sub_le ((μ q).real (coefficientEvent x y b))
      ((μ q).real B) ((μ q₀).real (coefficientEvent x y b))
    have hbc := abs_sub_le ((μ q).real B) ((μ q₀).real B)
      ((μ q₀).real (coefficientEvent x y b))
    rw [abs_sub_comm ((μ q₀).real B)] at hbc
    rw [Real.dist_eq]
    linarith
  have h := ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt hreal
  simpa only [Function.comp_def, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

end PercLib.Percolation.Bond.Lace
