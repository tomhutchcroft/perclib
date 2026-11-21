/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
The zero-order decomposition is the general-profile form of Heydenreich and
van der Hofstad (2017), Section 6.2, equations (6.2.7)--(6.2.8).
-/
module

public import PercLib.Percolation.Bond.Lace.Basic
public import PercLib.Probability.CountableBK
public import PercLib.Probability.OpenEventHarris
public import PercLib.Probability.Coupling.Monotone
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity

/-!
# Double connections: certificates, deletion, and the zeroth coefficient

Double connection survives the deletion of any single pair and hence has no
pivotal pair. BK bounds its probability by the square of the two-point function.
All probability statements allow inhomogeneous profiles and endpoint values
zero and one. Countability is required only for measurability and probability
bounds that use BK or monotone coupling.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Double connection has two finite disjoint open subconfigurations, each
connecting the endpoints. -/
theorem mem_doubleConn_iff (ω : Config V) (x y : V) :
    ω ∈ doubleConn x y ↔
      ∃ F H : Config V, F.Finite ∧ H.Finite ∧ Disjoint F H ∧
        F ⊆ ω ∧ H ⊆ ω ∧ F ∈ conn x y ∧ H ∈ conn x y :=
  mem_disjointOccurrence_iff_open (isUpperSet_conn x y) (isUpperSet_conn x y) ω

theorem doubleConn_subset_conn (x y : V) : doubleConn x y ⊆ conn x y :=
  fun _ h => (disjointOccurrence_subset_inter _ _ h).1

@[simp] theorem doubleConn_self (x : V) : doubleConn x x = univ := by
  simp only [doubleConn, conn_self, disjointOccurrence_univ]

theorem doubleConn_comm (x y : V) : doubleConn x y = doubleConn y x := by
  simp only [doubleConn, conn_symm x y]

theorem isUpperSet_doubleConn (x y : V) : IsUpperSet (doubleConn x y) :=
  isUpperSet_disjointOccurrence (isUpperSet_conn x y) (isUpperSet_conn x y)

theorem doubleConn_mono {ω η : Config V} (h : ω ⊆ η) {x y : V}
    (hω : ω ∈ doubleConn x y) : η ∈ doubleConn x y :=
  isUpperSet_doubleConn x y h hω

theorem measurableSet_doubleConn [Countable V] (x y : V) :
    MeasurableSet (doubleConn x y) :=
  measurableSet_disjointOccurrence (isUpperSet_conn x y) (isUpperSet_conn x y)

/-- At least one of the two disjoint certificates avoids any specified pair. -/
theorem conn_sdiff_singleton_of_mem_doubleConn {ω : Config V} {x y : V}
    (h : ω ∈ doubleConn x y) (e : Sym2 V) : ω \ {e} ∈ conn x y := by
  obtain ⟨F, H, _, _, hd, hFω, hHω, hF, hH⟩ := (mem_doubleConn_iff ω x y).mp h
  by_cases he : e ∈ F
  · apply conn_mono (ω := H) _ hH
    intro f hf
    refine ⟨hHω hf, ?_⟩
    rintro rfl
    exact Set.disjoint_left.mp hd he hf
  · apply conn_mono (ω := F) _ hF
    intro f hf
    refine ⟨hFω hf, ?_⟩
    rintro rfl
    exact he hf

/-- One of the disjoint certificates avoids a specified pair. Retaining the
other certificate gives a disjoint occurrence with the deleted-pair connection. -/
theorem doubleConn_subset_disjointOccurrence_deleted (x y : V) (e : Sym2 V) :
    doubleConn x y ⊆ disjointOccurrence (conn x y)
      {ω : Config V | ω \ {e} ∈ conn x y} := by
  have hup : IsUpperSet {ω : Config V | ω \ {e} ∈ conn x y} :=
    fun _ _ h hω => conn_mono (sdiff_subset_sdiff_left h) hω
  intro ω h
  obtain ⟨F, H, hFfin, hHfin, hd, hFω, hHω, hF, hH⟩ := (mem_doubleConn_iff ω x y).mp h
  rw [mem_disjointOccurrence_iff_open (isUpperSet_conn x y) hup]
  by_cases he : e ∈ F
  · have heH : e ∉ H := fun heH => Set.disjoint_left.mp hd he heH
    refine ⟨F, H, hFfin, hHfin, hd, hFω, hHω, hF, ?_⟩
    change H \ {e} ∈ conn x y
    simpa only [sdiff_singleton_eq_self heH] using hH
  · refine ⟨H, F, hHfin, hFfin, hd.symm, hHω, hFω, hH, ?_⟩
    change F \ {e} ∈ conn x y
    simpa only [sdiff_singleton_eq_self he] using hF

/-- An open direct edge and an alternative connection give double connection. -/
theorem mem_doubleConn_of_direct_of_deleted {ω : Config V} {x y : V}
    (hxy : x ≠ y) (he : s(x, y) ∈ ω) (h : ω \ {s(x, y)} ∈ conn x y) :
    ω ∈ doubleConn x y := by
  obtain ⟨F, hFsub, hF⟩ := exists_finset_of_mem_conn h
  rw [mem_doubleConn_iff]
  refine ⟨{s(x, y)}, F, finite_singleton _, F.finite_toSet, ?_,
    singleton_subset_iff.mpr he, fun _ hf => (hFsub hf).1,
    mem_conn_of_mem hxy (mem_singleton _), hF⟩
  exact Set.disjoint_singleton_left.mpr fun hf => (hFsub hf).2 (mem_singleton _)

/-- Once the direct edge is inserted, double connection is exactly connection
after deleting that edge. -/
theorem insert_mem_doubleConn_iff {ω : Config V} {x y : V} (hxy : x ≠ y) :
    insert s(x, y) ω ∈ doubleConn x y ↔ ω \ {s(x, y)} ∈ conn x y := by
  constructor
  · intro h
    simpa only [insert_sdiff_of_mem, mem_singleton] using
      conn_sdiff_singleton_of_mem_doubleConn h s(x, y)
  · intro h
    apply mem_doubleConn_of_direct_of_deleted hxy (mem_insert _ _)
    simpa only [insert_sdiff_of_mem, mem_singleton] using h

/-- Double connection implies the existing graph-theoretic two-edge
reachability notion; no new graph connectivity notion is introduced. -/
theorem isEdgeReachable_two_of_mem_doubleConn {ω : Config V} {x y : V}
    (h : ω ∈ doubleConn x y) : (openGraph ω).IsEdgeReachable 2 x y := by
  rw [SimpleGraph.isEdgeReachable_two]
  intro e
  change ((SimpleGraph.fromEdgeSet ω).deleteEdges {e}).Reachable x y
  rw [SimpleGraph.deleteEdges_fromEdgeSet]
  exact conn_sdiff_singleton_of_mem_doubleConn h e

/-- A double connection has no pivotal pair, in the canonical insertion/deletion
form of pivotality. -/
theorem not_pivotal_of_mem_doubleConn {ω : Config V} {x y : V}
    (h : ω ∈ doubleConn x y) (e : Sym2 V) :
    ¬ (insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y) :=
  fun hp => hp.2 (conn_sdiff_singleton_of_mem_doubleConn h e)

@[simp] theorem empty_mem_doubleConn_iff (x y : V) :
    (∅ : Config V) ∈ doubleConn x y ↔ x = y := by
  constructor
  · intro h
    exact (empty_mem_conn_iff x y).mp (doubleConn_subset_conn x y h)
  · rintro rfl
    simp

/-- A single open pair cannot give a double connection between distinct vertices. -/
@[simp] theorem singleton_mem_doubleConn_iff (e : Sym2 V) (x y : V) :
    ({e} : Config V) ∈ doubleConn x y ↔ x = y := by
  constructor
  · intro h
    have hc := conn_sdiff_singleton_of_mem_doubleConn h e
    simpa only [sdiff_self, empty_mem_conn_iff] using hc
  · rintro rfl
    simp

/-- The direct edge and a two-edge detour are disjoint connection witnesses. -/
theorem mem_doubleConn_of_triangle {ω : Config V} {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyω : s(x, y) ∈ ω) (hxzω : s(x, z) ∈ ω) (hzyω : s(z, y) ∈ ω) :
    ω ∈ doubleConn x y := by
  rw [mem_doubleConn_iff]
  refine ⟨{s(x, y)}, {s(x, z), s(z, y)}, finite_singleton _,
    (finite_singleton _).insert _, ?_, singleton_subset_iff.mpr hxyω,
    insert_subset_iff.mpr ⟨hxzω, singleton_subset_iff.mpr hzyω⟩,
    mem_conn_of_mem hxy (mem_singleton _), ?_⟩
  · simp [Set.disjoint_singleton_left, hxy, hxz, hyz, Ne.symm hxy]
  · exact conn_trans (mem_conn_of_mem hxz (mem_insert _ _))
      (mem_conn_of_mem (Ne.symm hyz) (mem_insert_of_mem _ (mem_singleton _)))

@[simp] theorem law_doubleConn_self (q : Sym2 V → unitInterval) (x : V) :
    law q (doubleConn x x) = 1 := by
  rw [doubleConn_self, measure_univ]

theorem law_doubleConn_le_tau (q : Sym2 V → unitInterval) (x y : V) :
    law q (doubleConn x y) ≤ tau q x y :=
  measure_mono (doubleConn_subset_conn x y)

/-- A sharper BK bound retains the probability of connecting after any specified
pair is deleted. Its constant is one, and it improves the square bound. -/
@[tag "S9QJ"]
theorem law_doubleConn_le_tau_mul_deleted [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (e : Sym2 V) :
    law q (doubleConn x y) ≤ tau q x y * law q {ω : Config V | ω \ {e} ∈ conn x y} := by
  refine (measure_mono (doubleConn_subset_disjointOccurrence_deleted x y e)).trans ?_
  exact countable_profile_bk q (isUpperSet_conn x y)
    (fun _ _ h hω => conn_mono (sdiff_subset_sdiff_left h) hω)

/-- BK square bound for double connections, including the diagonal. -/
theorem law_doubleConn_le_tau_sq [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    law q (doubleConn x y) ≤ tau q x y ^ 2 := by
  simpa only [law, doubleConn, tau, pow_two] using
    countable_profile_bk q (isUpperSet_conn x y) (isUpperSet_conn x y)

@[simp] theorem piZero_self (q : Sym2 V → unitInterval) (x : V) : piZero q x x = 0 := by
  simp [piZero]

theorem piZero_of_ne (q : Sym2 V → unitInterval) {x y : V} (hxy : x ≠ y) :
    piZero q x y = law q (doubleConn x y) := by
  simp [piZero, hxy]

theorem piZero_comm (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y = piZero q y x := by
  simp only [piZero, eq_comm, doubleConn_comm x y]

theorem piZero_le_law_doubleConn (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y ≤ law q (doubleConn x y) := by
  unfold piZero
  split_ifs <;> simp

theorem piZero_le_tau (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y ≤ tau q x y :=
  (piZero_le_law_doubleConn q x y).trans (law_doubleConn_le_tau q x y)

theorem piZero_le_tau_sq [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y ≤ tau q x y ^ 2 :=
  (piZero_le_law_doubleConn q x y).trans (law_doubleConn_le_tau_sq q x y)

/-- The zeroth lace coefficient is bounded by the squared two-point function,
with its diagonal removed exactly. -/
@[tag "X30S"]
theorem piZero_le_offDiagonal_tau_sq [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y ≤ if x = y then 0 else tau q x y ^ 2 := by
  by_cases h : x = y
  · subst y
    simp
  · simpa [h] using piZero_le_tau_sq q x y

theorem piZero_le_tau_mul_deleted [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) (e : Sym2 V) :
    piZero q x y ≤ tau q x y * law q {ω : Config V | ω \ {e} ∈ conn x y} :=
  (piZero_le_law_doubleConn q x y).trans (law_doubleConn_le_tau_mul_deleted q x y e)

theorem piZero_le_one (q : Sym2 V → unitInterval) (x y : V) : piZero q x y ≤ 1 :=
  (piZero_le_tau q x y).trans (tau_le_one q x y)

theorem piZero_ne_top (q : Sym2 V → unitInterval) (x y : V) : piZero q x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (piZero_le_one q x y)

/-- Restoring the diagonal recovers the double-connection probability. -/
theorem law_doubleConn_eq_indicator_add_piZero (q : Sym2 V → unitInterval) (x y : V) :
    law q (doubleConn x y) = (if x = y then 1 else 0) + piZero q x y := by
  by_cases h : x = y
  · subst y
    simp
  · simp [piZero, h]

/-- The diagonal subtraction convention in the usual definition of `Π⁽⁰⁾`. -/
theorem piZero_eq_sub (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y = law q (doubleConn x y) - (if x = y then 1 else 0) := by
  by_cases h : x = y
  · subst y
    simp
  · simp [piZero, h]

/-- The exact zero-order decomposition, before selecting the first pivotal pair.
The residual event is connected without being doubly connected. -/
theorem tau_eq_indicator_add_piZero_add [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    tau q x y = (if x = y then 1 else 0) + piZero q x y +
      law q (conn x y \ doubleConn x y) := by
  rw [← law_doubleConn_eq_indicator_add_piZero]
  have h := measure_sdiff_add_inter (μ := law q) (conn x y) (measurableSet_doubleConn x y)
  rw [inter_eq_right.mpr (doubleConn_subset_conn x y)] at h
  simpa only [add_comm, tau] using h.symm

theorem piZero_mono [Countable V] {q q' : Sym2 V → unitInterval} (h : q ≤ q') (x y : V) :
    piZero q x y ≤ piZero q' x y := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [piZero_of_ne q hxy, piZero_of_ne q' hxy]
    exact prodBernoulli_mono_event q q' h (measurableSet_doubleConn x y)
      (isUpperSet_doubleConn x y)

/-- The zero profile has no off-diagonal lace contribution. -/
@[simp] theorem piZero_zero [Countable V] (x y : V) :
    piZero (fun _ : Sym2 V => 0) x y = 0 := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [piZero_of_ne _ hxy, law]
    have hμ : prodBernoulli (fun _ : Sym2 V => (0 : unitInterval)) =
        Measure.dirac (∅ : Config V) := by
      simpa using prodBernoulli_deterministic (∅ : Config V)
    rw [hμ, Measure.dirac_apply' _ (measurableSet_doubleConn x y)]
    simp [hxy]

/-! ### Non-vacuity at the smallest sizes and endpoint parameters -/

example : (∅ : Config Bool) ∉ doubleConn false true := by simp

example : ({s(false, true)} : Config Bool) ∉ doubleConn false true := by simp

example : (univ : Config (Fin 3)) ∈ doubleConn 0 1 :=
  mem_doubleConn_of_triangle (z := 2) (by decide) (by decide) (by decide)
    (mem_univ _) (mem_univ _) (mem_univ _)

example : piZero (fun _ : Sym2 (Fin 3) => 1) 0 1 = 1 := by
  rw [piZero_of_ne _ (by decide), law]
  have hμ : prodBernoulli (fun _ : Sym2 (Fin 3) => (1 : unitInterval)) =
      Measure.dirac (univ : Config (Fin 3)) := by
    simpa using prodBernoulli_deterministic (univ : Config (Fin 3))
  rw [hμ, Measure.dirac_apply' _ (measurableSet_doubleConn 0 1)]
  have h : (univ : Config (Fin 3)) ∈ doubleConn 0 1 :=
    mem_doubleConn_of_triangle (z := 2) (by decide) (by decide) (by decide)
      (mem_univ _) (mem_univ _) (mem_univ _)
  simp [h]

example : piZero (fun _ : Sym2 Bool => 0) false true = 0 := piZero_zero false true

end PercLib.Percolation.Bond.Lace
