/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Original proofs for the canonical lace events; no upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.Events.Localization
public import PercLib.Percolation.Bond.Lace.FirstPivotal
public import PercLib.Percolation.Bond.Lace.Coefficients.Coefficients

/-!
# Localization of the finite-layer coefficient event

## Main results

For a fixed ordered bond tuple, the actual coefficient event is preserved by
internal agreement on a set containing the incoming root cluster of each layer.
The containing sets may differ between layers. The corresponding outgoing
deleted clusters agree globally, so the random prescribed sets in the next
layer's `E'` event are preserved exactly.

The initial double connection retains its certain diagonal. The statement is
deterministic, with no countability or finiteness assumption.
-/

@[expose] public section
noncomputable section

open Set

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Internal agreement on sets containing each incoming root cluster preserves
the canonical finite-layer event, including its random deleted-cluster sets. -/
theorem mem_coefficientEvent_iff_of_cluster_subset_of_agree {n : ℕ}
    (x y : V) (b : Fin (n + 1) → V × V)
    {ω η : Fin (n + 2) → Config V} {S : Fin (n + 2) → Set V}
    (hω : ∀ i, cluster (ω i) (Fin.cases x (fun j => (b j).2) i) ⊆ S i)
    (hη : ∀ i, cluster (η i) (Fin.cases x (fun j => (b j).2) i) ⊆ S i)
    (hconfig : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i,
      (s(u, v) ∈ ω i ↔ s(u, v) ∈ η i)) :
    (ω ∈ coefficientEvent x y b ↔ η ∈ coefficientEvent x y b) := by
  have hfirst : ω 0 ∈ doubleConn x (b 0).1 ↔ η 0 ∈ doubleConn x (b 0).1 := by
    rw [← laceEPrime_univ]
    apply mem_laceEPrime_iff_of_cluster_subset_of_agree
      (S := S 0) (hconfig := hconfig 0)
    · simpa only [Fin.cases_zero] using hω 0
    · simpa only [Fin.cases_zero] using hη 0
    · exact fun _ _ => Iff.rfl
  have hdeleted (i : Fin (n + 1)) :
      cluster (ω i.castSucc \ {s((b i).1, (b i).2)})
          (Fin.cases x (fun j => (b j).2) i.castSucc) =
        cluster (η i.castSucc \ {s((b i).1, (b i).2)})
          (Fin.cases x (fun j => (b j).2) i.castSucc) := by
    apply cluster_eq_of_cluster_subset_of_agree (S := S i.castSucc)
    · exact (cluster_mono sdiff_subset _).trans (hω i.castSucc)
    · exact (cluster_mono sdiff_subset _).trans (hη i.castSucc)
    · intro u hu v hv
      simp only [mem_sdiff, mem_singleton_iff, hconfig i.castSucc u hu v hv]
  have hnext (i : Fin (n + 1)) :
      ω i.succ ∈ laceEPrime
          (cluster (ω i.castSucc \ {s((b i).1, (b i).2)})
            (Fin.cases x (fun j => (b j).2) i.castSucc))
          (b i).2 (Fin.lastCases y (fun j => (b j).1) i.succ) ↔
        η i.succ ∈ laceEPrime
          (cluster (η i.castSucc \ {s((b i).1, (b i).2)})
            (Fin.cases x (fun j => (b j).2) i.castSucc))
          (b i).2 (Fin.lastCases y (fun j => (b j).1) i.succ) := by
    rw [hdeleted i]
    apply mem_laceEPrime_iff_of_cluster_subset_of_agree
      (S := S i.succ) (hconfig := hconfig i.succ)
    · simpa only [Fin.cases_succ] using hω i.succ
    · simpa only [Fin.cases_succ] using hη i.succ
    · exact fun _ _ => Iff.rfl
  exact and_congr hfirst (forall_congr' hnext)

end PercLib.Percolation.Bond.Lace
