/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.ThroughSet
public import PercLib.Percolation.Bond.ClusterCorrelation.Restoration

/-!
# Localization of lace events to the explored cluster

## Main results

The slice consisting of `E'(x,y;A)` and a specified root cluster `C` is
determined by the pairs touching `C`. The domain `C` need not be finite.
The proof transports deleted-edge and restricted-domain connections using
the existing cluster-agreement theorem.
-/

@[expose] public section
noncomputable section

open Set

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- The cluster after deleting any fixed set of pairs is still determined by
pairs touching a set containing the original root cluster. -/
theorem cluster_sdiff_eq_of_eqOn_touch {ω η : Config V} {C : Set V} {x : V}
    (hC : cluster ω x ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) (F : Set (Sym2 V)) :
    cluster (η \ F) x = cluster (ω \ F) x := by
  classical
  apply cluster_eq_of_eqOn_touch
  intro e he
  obtain ⟨z, hze, hz⟩ := he
  have hzC : z ∈ C := hC (conn_mono sdiff_subset hz)
  exact and_congr (hag e ⟨z, hze, hzC⟩).symm Iff.rfl

theorem conn_sdiff_iff_of_eqOn_touch {ω η : Config V} {C : Set V} {x : V}
    (hC : cluster ω x ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η))
    (F : Set (Sym2 V)) (y : V) : ω \ F ∈ conn x y ↔ η \ F ∈ conn x y := by
  classical
  change y ∈ cluster (ω \ F) x ↔ y ∈ cluster (η \ F) x
  rw [cluster_sdiff_eq_of_eqOn_touch hC hag]

theorem conn_iff_of_eqOn_touch {ω η : Config V} {C : Set V} {x : V}
    (hC : cluster ω x ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) (y : V) :
    ω ∈ conn x y ↔ η ∈ conn x y := by
  classical
  simpa using conn_sdiff_iff_of_eqOn_touch hC hag ∅ y

/-- Restricted connections from the root use only pairs touching its original cluster. -/
theorem localConn_iff_of_eqOn_touch {ω η : Config V} {C D : Set V} (x y : D)
    (hC : cluster ω (x : V) ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) :
    ((openGraph ω).induce D).Reachable x y ↔ ((openGraph η).induce D).Reachable x y := by
  classical
  have hcl : cluster (Sym2.map (Subtype.val : D → V) ⁻¹' η) x =
      cluster (Sym2.map (Subtype.val : D → V) ⁻¹' ω) x := by
    apply cluster_eq_of_eqOn_touch
    intro e he
    obtain ⟨z, hze, hz⟩ := he
    have hlocal : ((openGraph ω).induce D).Reachable x z := by
      rw [openGraph_induce]
      exact hz
    have hzC : (z : V) ∈ C := hC (conn_of_localConn ω D x z hlocal)
    exact (hag (Sym2.map Subtype.val e)
      ⟨z, Sym2.mem_map.mpr ⟨z, hze, rfl⟩, hzC⟩).symm
  rw [openGraph_induce, openGraph_induce]
  change y ∈ cluster (Sym2.map (Subtype.val : D → V) ⁻¹' ω) x ↔
    y ∈ cluster (Sym2.map (Subtype.val : D → V) ⁻¹' η) x
  rw [hcl]

theorem throughSet_iff_of_eqOn_touch {ω η : Config V} {A C : Set V} {x y : V}
    (hC : cluster ω x ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) :
    ω ∈ throughSet A x y ↔ η ∈ throughSet A x y := by
  classical
  rw [mem_throughSet_iff, mem_throughSet_iff]
  refine and_congr (conn_iff_of_eqOn_touch hC hag y) (not_congr ?_)
  constructor <;> rintro ⟨hx, hy, hp⟩
  · exact ⟨hx, hy, (localConn_iff_of_eqOn_touch ⟨x, hx⟩ ⟨y, hy⟩ hC hag).mp hp⟩
  · exact ⟨hx, hy, (localConn_iff_of_eqOn_touch ⟨x, hx⟩ ⟨y, hy⟩ hC hag).mpr hp⟩

/-- For an existing connection, both sides of a directed pivotal pair are
inside the root cluster, even when tested with the pair deleted. -/
theorem orientedPivotal_iff_of_eqOn_touch {ω η : Config V} {C : Set V} {x y u v : V}
    (hxy : ω ∈ conn x y) (hC : cluster ω x ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) :
    ω ∈ orientedPivotal x y u v ↔ η ∈ orientedPivotal x y u v := by
  classical
  have hyC : cluster ω y ⊆ C := fun z hz => hC (conn_trans hxy hz)
  have hη : η ∈ conn x y := (conn_iff_of_eqOn_touch hC hag y).mp hxy
  have hp : insert s(u, v) ω ∈ conn x y := conn_mono (subset_insert _ _) hxy
  have hpη : insert s(u, v) η ∈ conn x y := conn_mono (subset_insert _ _) hη
  have hd := conn_sdiff_iff_of_eqOn_touch hC hag {s(u, v)} y
  have hpre := conn_sdiff_iff_of_eqOn_touch hC hag {s(u, v)} u
  have hsuf : ω \ {s(u, v)} ∈ conn v y ↔ η \ {s(u, v)} ∈ conn v y := by
    rw [conn_symm v y]
    exact conn_sdiff_iff_of_eqOn_touch hyC hag {s(u, v)} v
  change (insert s(u, v) ω ∈ conn x y ∧ ω \ {s(u, v)} ∉ conn x y ∧
    ω \ {s(u, v)} ∈ conn x u ∧ ω \ {s(u, v)} ∈ conn v y) ↔
    (insert s(u, v) η ∈ conn x y ∧ η \ {s(u, v)} ∉ conn x y ∧
      η \ {s(u, v)} ∈ conn x u ∧ η \ {s(u, v)} ∈ conn v y)
  exact and_congr (iff_of_true hp hpη) (and_congr (not_congr hd) (and_congr hpre hsuf))

/-- `E'` is unchanged when only pairs outside a set containing the root cluster change. -/
theorem laceEPrime_iff_of_eqOn_touch {ω η : Config V} {A C : Set V} {x y : V}
    (hC : cluster ω x ⊆ C)
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) :
    ω ∈ laceEPrime A x y ↔ η ∈ laceEPrime A x y := by
  classical
  by_cases hxy : ω ∈ conn x y
  · have hex : (∃ u v, ω ∈ orientedPivotal x y u v ∧ ω ∈ throughSet A x u) ↔
        ∃ u v, η ∈ orientedPivotal x y u v ∧ η ∈ throughSet A x u := by
      constructor <;> rintro ⟨u, v, hp, ht⟩
      · exact ⟨u, v, (orientedPivotal_iff_of_eqOn_touch hxy hC hag).mp hp,
          (throughSet_iff_of_eqOn_touch hC hag).mp ht⟩
      · exact ⟨u, v, (orientedPivotal_iff_of_eqOn_touch hxy hC hag).mpr hp,
          (throughSet_iff_of_eqOn_touch hC hag).mpr ht⟩
    simpa only [laceEPrime, mem_sdiff, mem_iUnion, mem_inter_iff] using
      and_congr (throughSet_iff_of_eqOn_touch (A := A) hC hag) (not_congr hex)
  · have hη : η ∉ conn x y := fun h => hxy ((conn_iff_of_eqOn_touch hC hag y).mpr h)
    exact iff_of_false (fun h => hxy h.1.1) (fun h => hη h.1.1)

/-- A specified root-cluster slice of `E'` is determined by pairs touching
that cluster. This is the localization needed for cutting-bond factorization. -/
theorem laceEPrime_cluster_iff_of_eqOn_touch {ω η : Config V} {A C : Set V} {x y : V}
    (hag : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ ω ↔ e ∈ η)) :
    (ω ∈ laceEPrime A x y ∧ cluster ω x = C) ↔
      (η ∈ laceEPrime A x y ∧ cluster η x = C) := by
  classical
  constructor
  · rintro ⟨hE, hC⟩
    have hsub : cluster ω x ⊆ C := hC.subset
    refine ⟨(laceEPrime_iff_of_eqOn_touch hsub hag).mp hE, ?_⟩
    have hcl := cluster_sdiff_eq_of_eqOn_touch hsub hag ∅
    simpa [hC] using hcl
  · rintro ⟨hE, hC⟩
    have hsub : cluster η x ⊆ C := hC.subset
    have hrev : ∀ e, (∃ z ∈ e, z ∈ C) → (e ∈ η ↔ e ∈ ω) :=
      fun e he => (hag e he).symm
    refine ⟨(laceEPrime_iff_of_eqOn_touch hsub hrev).mp hE, ?_⟩
    have hcl := cluster_sdiff_eq_of_eqOn_touch hsub hrev ∅
    simpa [hC] using hcl

end PercLib.Percolation.Bond.Lace
