/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original proofs for the canonical lace events; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Events.Localization
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Percolation.Bond.FiniteVolume
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# One-sided continuity of the lace event

## Main results

The probability of the actual event `E'` for a fixed vertex set is continuous
from profiles below an upper profile whose root cluster is almost surely finite.
No finite susceptibility or local finiteness assumption is needed.

Restriction to the internal pairs of a finite vertex set gives a cylinder
approximation. Its probability error is at most the upper-profile probability
that the root cluster escapes this set. Only the escape event is compared by
monotonicity; the lace event itself need not be increasing.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology PercLib.Probability
open scoped ENNReal symmDiff

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Almost sure finiteness of a root cluster makes its escape probability from
a sufficiently large finite vertex set arbitrarily small. -/
theorem exists_finset_law_escape_lt_of_ae_cluster_finite [Countable V]
    (q : Sym2 V → unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂law q, (cluster ω x).Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset V, (law q).real (⋃ z ∈ (S : Set V)ᶜ, conn x z) < ε := by
  classical
  obtain ⟨S, hS, hcover⟩ := exists_finset_exhaustion (V := V)
  have hS' : Monotone fun n => (S n : Set V) :=
    fun m n hmn => Finset.coe_subset.2 (hS hmn)
  have hz : law q {ω | (cluster ω x).Infinite} = 0 := by
    exact ae_iff.mp hfin
  have hzero : (⨅ n, law q (⋃ z ∈ (S n : Set V)ᶜ, conn x z)) = 0 := by
    rw [← law_cluster_infinite_eq_iInf_escape q hS'
      (fun n => (S n).finite_toSet) hcover x]
    exact hz
  have hlt : (⨅ n, law q (⋃ z ∈ (S n : Set V)ᶜ, conn x z)) <
      ENNReal.ofReal ε := by
    rw [hzero]
    exact ENNReal.ofReal_pos.mpr hε
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hlt
  refine ⟨S n, ?_⟩
  have hr := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hn
  simpa only [Measure.real, ENNReal.toReal_ofReal hε.le] using hr

open scoped Classical in
/-- Restricting the configuration to pairs internal to a finite vertex set changes
the probability of `E'` by at most the upper-profile root escape probability. -/
theorem abs_law_laceEPrime_sub_restrict_le [Countable V]
    (q q₀ : Sym2 V → unitInterval) (hqq₀ : q ≤ q₀)
    (A : Set V) (x y : V) (S : Finset V) :
    let F : Finset (Sym2 V) := (S ×ˢ S).image fun z => s(z.1, z.2)
    |(law q).real (laceEPrime A x y) -
        (law q).real {ω | ω ∩ (F : Set (Sym2 V)) ∈ laceEPrime A x y}| ≤
      (law q₀).real (⋃ z ∈ (S : Set V)ᶜ, conn x z) := by
  classical
  intro F
  let E : Set (Config V) := {ω | ω ∩ (F : Set (Sym2 V)) ∈ laceEPrime A x y}
  have hE : MeasurableSet E :=
    (measurableSet_laceEPrime A x y).preimage (measurable_id.inter measurable_const)
  have hdiff : laceEPrime A x y ∆ E ⊆ ⋃ z ∈ (S : Set V)ᶜ, conn x z := by
    intro ω hω
    by_contra hescape
    have hcluster : cluster ω x ⊆ (S : Set V) := by
      intro z hz
      by_contra hzS
      exact hescape (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hzS, hz⟩⟩)
    have hrestrict : cluster (ω ∩ (F : Set (Sym2 V))) x ⊆ (S : Set V) :=
      (cluster_mono inter_subset_left x).trans hcluster
    have hagree : ∀ u ∈ (S : Set V), ∀ v ∈ (S : Set V),
        (s(u, v) ∈ ω ↔ s(u, v) ∈ ω ∩ (F : Set (Sym2 V))) := by
      intro u hu v hv
      have huv : s(u, v) ∈ (F : Set (Sym2 V)) :=
        Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
      simp only [mem_inter_iff, huv, and_true]
    have heq := mem_laceEPrime_iff_of_cluster_subset_of_agree
      (A := A) (B := A) (y := y) hcluster hrestrict hagree (fun _ _ => Iff.rfl)
    rcases hω with hω | hω
    · exact hω.2 (heq.mp hω.1)
    · exact hω.2 (heq.mpr hω.1)
  calc
    |(law q).real (laceEPrime A x y) - (law q).real E| ≤
        (law q).real (laceEPrime A x y ∆ E) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        (measurableSet_laceEPrime A x y).nullMeasurableSet hE.nullMeasurableSet
    _ ≤ (law q).real (⋃ z ∈ (S : Set V)ᶜ, conn x z) :=
      measureReal_mono hdiff (measure_ne_top _ _)
    _ ≤ (law q₀).real (⋃ z ∈ (S : Set V)ᶜ, conn x z) :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (prodBernoulli_mono_event q q₀ hqq₀ (measurableSet_escape x (S : Set V))
          (isUpperSet_escape x (S : Set V)))

/-- For any fixed prescribed set, the actual lace event `E'` is continuous from
profiles below a profile whose root cluster is almost surely finite. -/
theorem continuousWithinAt_law_laceEPrime_Iic [Countable V]
    (q₀ : Sym2 V → unitInterval) (A : Set V) (x y : V)
    (hfin : ∀ᵐ ω ∂law q₀, (cluster ω x).Finite) :
    ContinuousWithinAt
      (fun q : Sym2 V → unitInterval => law q (laceEPrime A x y))
      (Iic q₀) q₀ := by
  classical
  have hreal : ContinuousWithinAt
      (fun q : Sym2 V → unitInterval => (law q).real (laceEPrime A x y))
      (Iic q₀) q₀ := by
    rw [Metric.continuousWithinAt_iff']
    intro ε hε
    have hε₃ : 0 < ε / 3 := by positivity
    obtain ⟨S, hS⟩ := exists_finset_law_escape_lt_of_ae_cluster_finite q₀ x hfin hε₃
    let F : Finset (Sym2 V) := (S ×ˢ S).image fun z => s(z.1, z.2)
    let E : Set (Config V) := {ω | ω ∩ (F : Set (Sym2 V)) ∈ laceEPrime A x y}
    have hEc : Continuous fun q : Sym2 V → unitInterval => law q E := by
      apply continuous_prodBernoulli_of_determined F
      intro ω ω' heq
      change (ω ∩ (F : Set (Sym2 V)) ∈ laceEPrime A x y) ↔
        (ω' ∩ (F : Set (Sym2 V)) ∈ laceEPrime A x y)
      rw [heq]
    have hEr : ContinuousAt (fun q : Sym2 V → unitInterval => (law q).real E) q₀ :=
      (ENNReal.continuousAt_toReal (measure_ne_top (law q₀) E)).comp
        (f := fun q : Sym2 V → unitInterval => law q E) hEc.continuousAt
    have hevent : ∀ᶠ q in 𝓝[Iic q₀] q₀,
        |(law q).real E - (law q₀).real E| < ε / 3 := by
      have h := (Metric.continuousAt_iff'.mp hEr (ε / 3) hε₃).filter_mono
        (nhdsWithin_le_nhds (s := Iic q₀))
      simpa only [Real.dist_eq] using h
    filter_upwards [hevent, self_mem_nhdsWithin] with q hdiff hqq₀
    have ha := abs_law_laceEPrime_sub_restrict_le q q₀ hqq₀ A x y S
    have hb := abs_law_laceEPrime_sub_restrict_le q₀ q₀ le_rfl A x y S
    change |(law q).real (laceEPrime A x y) - (law q).real E| ≤ _ at ha
    change |(law q₀).real (laceEPrime A x y) - (law q₀).real E| ≤ _ at hb
    have hab := abs_sub_le ((law q).real (laceEPrime A x y))
      ((law q).real E) ((law q₀).real (laceEPrime A x y))
    have hbc := abs_sub_le ((law q).real E) ((law q₀).real E)
      ((law q₀).real (laceEPrime A x y))
    rw [abs_sub_comm ((law q₀).real E)] at hbc
    rw [Real.dist_eq]
    linarith
  have h := ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt hreal
  simpa only [Function.comp_def, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

end PercLib.Percolation.Bond.Lace
