/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.ThroughSet
public import PercLib.Percolation.Bond.Susceptibility

/-!
# Through-set and cutting events with a measurable random vertex set

## Main results

An avoiding connection is a countable union of events witnessed in fixed finite
vertex domains. This gives measurability when both the configuration and the
vertex set vary, including the deleted clusters supplied by earlier independent
layers in the lace expansion.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- An avoiding path lies in some finite domain disjoint from the vertex set. -/
theorem conn_avoiding_iff_exists_finset (A : Set V) (ω : Config V) (x y : V) :
    (∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
      ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩) ↔
      ∃ F : Finset V, (F : Set V) ⊆ Aᶜ ∧ ∃ hx : x ∈ F, ∃ hy : y ∈ F,
        ((openGraph ω).induce (F : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  constructor
  · rintro ⟨hx, hy, ⟨p⟩⟩
    let w := p.map (SimpleGraph.Embedding.induce Aᶜ).toHom
    have hw : ∀ z ∈ w.support, z ∈ Aᶜ := by
      intro z hz
      simp only [w, SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨a, _, rfl⟩ := hz
      exact a.property
    have hF : ∀ z ∈ w.support, z ∈ (w.support.toFinset : Set V) := by simp
    exact ⟨w.support.toFinset, fun z hz => hw z (List.mem_toFinset.mp hz),
      hF x w.start_mem_support, hF y w.end_mem_support, ⟨w.induce _ hF⟩⟩
  · rintro ⟨F, hF, hx, hy, hp⟩
    exact ⟨hF hx, hF hy, localConn_mono_domain ω hF ⟨x, hx⟩ ⟨y, hy⟩ hp⟩

variable {Ω : Type*} [MeasurableSpace Ω] [Countable V]

/-- Joint measurability of connections avoiding a measurable random vertex set. -/
theorem measurableSet_conn_avoiding_of_measurable
    {A : Ω → Set V} {ω : Ω → Config V} (hA : Measurable A) (hω : Measurable ω)
    (x y : V) :
    MeasurableSet {s : Ω | ∃ hx : x ∈ (A s)ᶜ, ∃ hy : y ∈ (A s)ᶜ,
      ((openGraph (ω s)).induce (A s)ᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
  classical
  simp only [conn_avoiding_iff_exists_finset, ofPred_exists]
  refine MeasurableSet.iUnion fun F => ?_
  have hF : MeasurableSet {s : Ω | (F : Set V) ⊆ (A s)ᶜ} := by
    change MeasurableSet {s : Ω | ∀ z, z ∈ (F : Set V) → z ∉ A s}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun z => MeasurableSet.iInter fun _ =>
      ((measurable_set_mem z).comp hA).setOf.compl
  refine hF.inter ?_
  exact (Measurable.exists fun hx : x ∈ F => Measurable.exists fun hy : y ∈ F =>
    ((measurableSet_setOf_reachable_induce (F : Set V) ⟨x, hx⟩ ⟨y, hy⟩).preimage hω).mem).setOf

/-- The through-set event is measurable in both inputs. -/
theorem measurableSet_throughSet_of_measurable
    {A : Ω → Set V} {ω : Ω → Config V} (hA : Measurable A) (hω : Measurable ω)
    (x y : V) : MeasurableSet {s : Ω | ω s ∈ throughSet (A s) x y} :=
  ((measurableSet_conn x y).preimage hω).diff
    (measurableSet_conn_avoiding_of_measurable hA hω x y)

/-- `E'` remains measurable when its vertex set comes from an earlier layer. -/
theorem measurableSet_laceEPrime_of_measurable
    {A : Ω → Set V} {ω : Ω → Config V} (hA : Measurable A) (hω : Measurable ω)
    (x y : V) : MeasurableSet {s : Ω | ω s ∈ laceEPrime (A s) x y} := by
  classical
  have heq : {s : Ω | ω s ∈ laceEPrime (A s) x y} =
      {s | ω s ∈ throughSet (A s) x y} \
        ⋃ u, ⋃ v, {s | ω s ∈ orientedPivotal x y u v} ∩
          {s | ω s ∈ throughSet (A s) x u} := by
    ext s
    simp [laceEPrime]
  rw [heq]
  exact (measurableSet_throughSet_of_measurable hA hω x y).diff
    (MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun v =>
      ((measurableSet_orientedPivotal x y u v).preimage hω).inter
        (measurableSet_throughSet_of_measurable hA hω x u))

/-- Measurability of the set-valued cluster after one pair is declared closed. -/
theorem measurable_deleted_cluster (e : Sym2 V) (x : V) :
    Measurable (fun ω : Config V => cluster (ω \ {e}) x) :=
  (measurable_cluster x).comp (by fun_prop)

/-- The paired independent-layer form used by positive lace coefficients. -/
theorem measurableSet_laceEPrime_deleted_cluster (e : Sym2 V) (a x y : V) :
    MeasurableSet {p : Config V × Config V |
      p.2 ∈ laceEPrime (cluster (p.1 \ {e}) a) x y} :=
  measurableSet_laceEPrime_of_measurable ((measurable_deleted_cluster e a).comp measurable_fst)
    measurable_snd x y

end PercLib.Percolation.Bond.Lace
