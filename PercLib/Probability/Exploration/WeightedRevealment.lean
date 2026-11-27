/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original weighted revealment bounds for the existing stopped priority
exploration; no upstream proof is copied.
-/
module

public import PercLib.Probability.Exploration.PriorityStopped
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Weighted cost of the stopped priority exploration

## Main results

Every queried edge has a discovered endpoint and is queried at most once.
Charging it to one such endpoint bounds the total query weight by the sum
of the actual row weights over all discovered vertices. A uniform row cap
therefore costs exactly that cap times the truncated cluster volume.

The canonical-law corollaries retain the expected truncated volume and then
bound it by the smaller of susceptibility and the stopping threshold. No
local finiteness or finite susceptibility is assumed. The several parameters
specify the graph, priority order, root, threshold, profile, weights and row
cap; the mathematical assumptions are only a positive threshold and the row
bound. These are exploration-cost bounds, not an entropy comparison theorem.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The weighted incidence sum at one vertex is bounded by the canonical
off-diagonal row sum, without a local-finiteness assumption on the graph. -/
theorem tsum_incidenceSet_weight_le_rowSum (G : SimpleGraph V)
    (w : Sym2 V → ℝ≥0∞) (v : V) :
    (∑' e : G.incidenceSet v, w (e : Sym2 V)) ≤ rowSum w v := by
  classical
  rw [← (G.incidenceSetEquivNeighborSet v).symm.tsum_eq]
  change (∑' u : G.neighborSet v, w s(v, (u : V))) ≤ rowSum w v
  rw [rowSum_eq_tsum_ne]
  let f : G.neighborSet v → {u : V // u ≠ v} := fun u => ⟨u.1, u.2.ne.symm⟩
  have hf : Function.Injective f := by
    intro u u' h
    exact Subtype.ext (congrArg (fun a : {u : V // u ≠ v} => a.val) h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hf (fun u => w s(v, (u : V)))

/-- The total cost of the actual queries is at most the sum of row weights
at discovered vertices. Each query is charged only once. -/
theorem tsum_priorityQuery_weight_le_tsum_discovered_rowSum
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ)
    (ω : Config V) (w : Sym2 V → ℝ≥0∞) :
    (∑' t : ℕ, (priorityQuery G ι o n ω t).elim 0 (fun e => w (e : Sym2 V))) ≤
      ∑' v : (⋃ t, (priorityExploration G ι o n ω t).discovered), rowSum w (v : V) := by
  classical
  let D : Set V := ⋃ t, (priorityExploration G ι o n ω t).discovered
  let Q : Set ℕ := {t | ∃ e, priorityQuery G ι o n ω t = some e}
  let C (t : ℕ) : ℝ≥0∞ := (priorityQuery G ι o n ω t).elim 0 (fun e => w (e : Sym2 V))
  let e (t : Q) : G.edgeSet := Classical.choose t.property
  have he (t : Q) : priorityQuery G ι o n ω t = some (e t) :=
    Classical.choose_spec t.property
  have hsupport : Function.support C ⊆ Q := by
    intro t ht
    cases hq : priorityQuery G ι o n ω t with
    | none => exact (ht (by simp [C, hq])).elim
    | some f => exact ⟨f, hq⟩
  have hsum : (∑' t : ℕ, C t) = ∑' t : Q, w (e t : Sym2 V) := by
    rw [← tsum_subtype_eq_of_support_subset hsupport]
    apply tsum_congr
    intro t
    simp [C, he t]
  have hvertex (t : Q) : ∃ v ∈ (e t : Sym2 V), v ∈ D := by
    obtain ⟨v, hv, hD⟩ := (priorityQuery_mem_eligible (he t)).2
    exact ⟨v, hv, mem_iUnion.mpr ⟨t.1, hD⟩⟩
  choose v hv hD using hvertex
  let f : Q → Σ v : D, G.incidenceSet (v : V) := fun t =>
    ⟨⟨v t, hD t⟩, ⟨(e t : Sym2 V), (e t).property, hv t⟩⟩
  have hf : Function.Injective f := by
    intro t t' h
    have heq : e t = e t' := Subtype.ext
      (congrArg (fun p : Σ v : D, G.incidenceSet (v : V) => (p.2 : Sym2 V)) h)
    apply Subtype.ext
    exact priorityQuery_injective ((he t).trans (congrArg some heq)) (he t')
  calc
    (∑' t : ℕ, C t) = ∑' t : Q, w (e t : Sym2 V) := hsum
    _ ≤ ∑' p : Σ v : D, G.incidenceSet (v : V), w (p.2 : Sym2 V) :=
      ENNReal.tsum_comp_le_tsum_of_injective hf (fun p => w (p.2 : Sym2 V))
    _ = ∑' v : D, ∑' e : G.incidenceSet (v : V), w (e : Sym2 V) := ENNReal.tsum_sigma' _
    _ ≤ ∑' v : D, rowSum w (v : V) :=
      ENNReal.tsum_le_tsum fun v => tsum_incidenceSet_weight_le_rowSum G w v

/-- A row cap bounds the actual total query cost by exactly that cap times
the discovered truncated cluster volume. -/
theorem tsum_priorityQuery_weight_le
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ) (hn : 1 ≤ n)
    (ω : Config V) (w : Sym2 V → ℝ≥0∞) (M : ℝ≥0∞)
    (hrow : ∀ v, rowSum w v ≤ M) :
    (∑' t : ℕ, (priorityQuery G ι o n ω t).elim 0 (fun e => w (e : Sym2 V))) ≤
      M * ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞) := by
  classical
  let D : Set V := ⋃ t, (priorityExploration G ι o n ω t).discovered
  calc
    _ ≤ ∑' v : D, rowSum w (v : V) :=
      tsum_priorityQuery_weight_le_tsum_discovered_rowSum G ι o n ω w
    _ ≤ ∑' _v : D, M := ENNReal.tsum_le_tsum fun v => hrow v
    _ = (D.encard : ℝ≥0∞) * M := ENNReal.tsum_set_const D M
    _ = _ := by
      have hcard : D.encard = min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞) :=
        encard_iUnion_priorityExploration_discovered (G := G) (ι := ι) (o := o)
          (ω := ω) hn
      simp only [hcard, mul_comm, ENat.toENNReal_min]

/-- The canonical-law expected query cost is bounded by the actual expected
truncated cluster volume. No independence of the queried set is assumed. -/
theorem lintegral_tsum_priorityQuery_weight_le [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ) (hn : 1 ≤ n)
    (q : Sym2 V → unitInterval) (w : Sym2 V → ℝ≥0∞) (M : ℝ≥0∞)
    (hrow : ∀ v, rowSum w v ≤ M) :
    (∫⁻ ω, ∑' t : ℕ, (priorityQuery G ι o n ω t).elim 0
      (fun e => w (e : Sym2 V)) ∂law q) ≤
      M * ∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞) ∂law q := by
  have hK : Measurable (fun ω : Config V => (cluster (ω ∩ G.edgeSet) o).encard) :=
    (measurable_encard_cluster o).comp (measurable_id.inter measurable_const)
  have hm : Measurable (fun ω : Config V =>
      ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞)) :=
    (Measurable.of_discrete (f := fun k : ℕ∞ => ((min k (n : ℕ∞)) : ℝ≥0∞))).comp hK
  calc
    _ ≤ ∫⁻ ω, M * ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞) ∂law q :=
      lintegral_mono fun ω => tsum_priorityQuery_weight_le G ι o n hn ω w M hrow
    _ = _ := lintegral_const_mul M hm

/-- The expected truncated cluster volume is bounded by both the full
susceptibility and the stopping threshold. -/
theorem lintegral_truncated_restricted_cluster_le_min_chi
    (G : SimpleGraph V) (q : Sym2 V → unitInterval) (o : V) (n : ℕ) :
    (∫⁻ ω, ((min (cluster (ω ∩ G.edgeSet) o).encard (n : ℕ∞)) : ℝ≥0∞) ∂law q) ≤
      min (chi q o) (n : ℝ≥0∞) := by
  apply le_min
  · apply lintegral_mono
    intro ω
    exact (min_le_left _ _).trans
      (ENat.toENNReal_le.mpr (encard_le_encard (cluster_mono inter_subset_left o)))
  · calc
      _ ≤ ∫⁻ _ω : Config V, (n : ℝ≥0∞) ∂law q := lintegral_mono fun ω => by
        simpa only [ENat.toENNReal_coe] using
          (min_le_right ((cluster (ω ∩ G.edgeSet) o).encard : ℝ≥0∞)
            ((n : ℕ∞) : ℝ≥0∞))
      _ = _ := by simp

/-- The expected weighted query cost is at most the row cap times the
smaller of susceptibility and the stopping threshold. -/
theorem lintegral_tsum_priorityQuery_weight_le_min_chi [Countable V]
    (G : SimpleGraph V) (ι : G.edgeSet ↪ ℕ) (o : V) (n : ℕ) (hn : 1 ≤ n)
    (q : Sym2 V → unitInterval) (w : Sym2 V → ℝ≥0∞) (M : ℝ≥0∞)
    (hrow : ∀ v, rowSum w v ≤ M) :
    (∫⁻ ω, ∑' t : ℕ, (priorityQuery G ι o n ω t).elim 0
      (fun e => w (e : Sym2 V)) ∂law q) ≤ M * min (chi q o) (n : ℝ≥0∞) :=
  (lintegral_tsum_priorityQuery_weight_le G ι o n hn q w M hrow).trans
    (mul_le_mul_right (lintegral_truncated_restricted_cluster_le_min_chi G q o n) M)

end PercLib.Percolation.Bond
