/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.TwoPaths
public import PercLib.Percolation.Bond.Lace.PivotalPartition

/-!
# The canonical first-pivotal partition

## Main results

When the through-set is the whole vertex space, the no-earlier-cutting event
is exactly double connection. This identifies the initial term of the lace
expansion without assuming an edge-Menger theorem or an expansion identity.
-/

@[expose] public section
noncomputable section

open Set

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- With the full vertex set, the no-earlier-cutting event is double connection. -/
@[simp] theorem laceEPrime_univ (x y : V) :
    laceEPrime univ x y = doubleConn x y := by
  classical
  ext ω
  constructor
  · intro h
    apply mem_doubleConn_iff_conn_and_no_pivotal.mpr
    refine ⟨by simpa using h.1, ?_⟩
    intro e hp
    induction e using Sym2.ind with
    | _ u v =>
      rcases reachable_sdiff_or_of_reachable_insert hp.1 with hn | hu | hv
      · exact hp.2 hn
      · apply h.2
        exact mem_iUnion.mpr ⟨u, mem_iUnion.mpr ⟨v,
          ⟨hp.1, hp.2, hu.1, hu.2⟩,
          by simpa using conn_mono sdiff_subset hu.1⟩⟩
      · apply h.2
        refine mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨u, ?_, ?_⟩⟩
        · change insert s(v, u) ω ∈ conn x y ∧ _
          have heq : s(v, u) = s(u, v) := Sym2.eq_swap
          simpa only [heq, conn, mem_ofPred_eq] using And.intro hp.1 (And.intro hp.2 hv)
        · simpa using conn_mono sdiff_subset hv.1
  · intro h
    refine ⟨by simpa using doubleConn_subset_conn x y h, ?_⟩
    intro hu
    obtain ⟨u, v, hp, _⟩ := by simpa only [mem_iUnion, mem_inter_iff] using hu
    exact not_pivotal_of_mem_doubleConn h s(u, v) ⟨hp.1, hp.2.1⟩

/-- A connected configuration is double or has its unique first pivotal pair. -/
theorem conn_eq_doubleConn_union_firstPivotal (x y : V) :
    conn x y = doubleConn x y ∪ ⋃ u, ⋃ v, cuttingEvent univ x y u v := by
  classical
  simpa using throughSet_eq_laceEPrime_union_cuttingEvent (univ : Set V) x y

theorem disjoint_doubleConn_firstPivotal (x y u v : V) :
    Disjoint (doubleConn x y) (cuttingEvent univ x y u v) := by
  classical
  simpa using disjoint_laceEPrime_cuttingEvent (univ : Set V) x y u v

open scoped Classical in
/-- The exact initial lace decomposition, with no loss or double counting. -/
@[tag "CM8M"]
theorem tau_eq_indicator_add_piZero_add_firstPivotal [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    tau q x y = (if x = y then 1 else 0) + piZero q x y +
      ∑' u, ∑' v, law q (cuttingEvent univ x y u v) := by
  classical
  simpa only [tau, throughSet_univ, laceEPrime_univ,
    law_doubleConn_eq_indicator_add_piZero] using
    law_throughSet_eq_add_tsum_cuttingEvent q univ x y

end PercLib.Percolation.Bond.Lace
