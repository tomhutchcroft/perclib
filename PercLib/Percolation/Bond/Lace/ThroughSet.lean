/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
The through-set convention is that of Heydenreich and van der Hofstad,
Progress in High-Dimensional Percolation and Random Graphs (2017), Section 6.2,
Definition 6.2. Restricted connections reuse the canonical induced open graph.
-/
module

public import PercLib.Percolation.Bond.Lace.Basic
public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.BoundarySusceptibility

/-!
# Connections through a vertex set

A connection is through `A` if every open connecting path meets `A`. Existence
of the connection is part of the event. In particular, the empty path gives the
diagonal convention `x ↔ᴬ x` exactly when `x ∈ A`.

The event increases with the vertex set `A`. It is not in general increasing
in the open configuration: an added path may avoid `A`. The probability
decomposition below therefore uses measurable disjoint sets, not positive
association or BK applied directly to the through-set event.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal Classical

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

theorem mem_throughSet_iff (A : Set V) (x y : V) (ω : Config V) :
    ω ∈ throughSet A x y ↔ ω ∈ conn x y ∧
      ¬ ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
        ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := Iff.rfl

theorem throughSet_subset_conn (A : Set V) (x y : V) : throughSet A x y ⊆ conn x y :=
  sdiff_subset

theorem throughSet_comm (A : Set V) (x y : V) : throughSet A x y = throughSet A y x := by
  ext ω
  simp only [mem_throughSet_iff, conn_symm x y]
  constructor <;> rintro ⟨h, hn⟩
  · exact ⟨h, fun ⟨hy, hx, hxy⟩ => hn ⟨hx, hy, hxy.symm⟩⟩
  · exact ⟨h, fun ⟨hx, hy, hxy⟩ => hn ⟨hy, hx, hxy.symm⟩⟩

/-- A connection whose first endpoint lies in `A` necessarily goes through `A`. -/
theorem throughSet_eq_conn_of_left_mem {A : Set V} {x : V} (hx : x ∈ A) (y : V) :
    throughSet A x y = conn x y := by
  ext ω
  simp [mem_throughSet_iff, hx]

theorem throughSet_eq_conn_of_right_mem {A : Set V} {y : V} (hy : y ∈ A) (x : V) :
    throughSet A x y = conn x y := by
  rw [throughSet_comm, throughSet_eq_conn_of_left_mem hy, conn_symm]

@[simp] theorem throughSet_univ (x y : V) : throughSet univ x y = conn x y :=
  throughSet_eq_conn_of_left_mem (mem_univ x) y

@[simp] theorem throughSet_empty (x y : V) : throughSet ∅ x y = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro ω h
  obtain ⟨p⟩ := h.1
  exact h.2 ⟨by simp, by simp, ⟨p.induce (∅ : Set V)ᶜ (by simp)⟩⟩

/-- The diagonal contains the zero-edge path, so it records vertex membership. -/
theorem throughSet_self (A : Set V) (x : V) :
    throughSet A x x = if x ∈ A then univ else ∅ := by
  by_cases hx : x ∈ A
  · simp [hx, throughSet_eq_conn_of_left_mem hx, conn_self]
  · apply Set.ext
    intro ω
    simp only [ite_eq_right_iff.mpr (fun h => (hx h).elim), mem_empty_iff_false,
      iff_false]
    exact fun h => h.2 ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

@[simp] theorem mem_throughSet_self_iff (A : Set V) (x : V) (ω : Config V) :
    ω ∈ throughSet A x x ↔ x ∈ A := by
  rw [throughSet_self]
  by_cases hx : x ∈ A <;> simp [hx]

/-- Enlarging the required vertex set preserves through-set connections. -/
theorem throughSet_mono_set {A B : Set V} (hAB : A ⊆ B) (x y : V) :
    throughSet A x y ⊆ throughSet B x y := by
  rintro ω ⟨hc, hn⟩
  refine ⟨hc, ?_⟩
  rintro ⟨hx, hy, hp⟩
  have hBA : Bᶜ ⊆ Aᶜ := compl_subset_compl.mpr hAB
  exact hn ⟨hBA hx, hBA hy, localConn_mono_domain ω hBA ⟨x, hx⟩ ⟨y, hy⟩ hp⟩

/-- A through-set connection has a finite open witness, despite not being an
increasing event in the configuration. Any avoiding path in the witness would
also be an avoiding path in the original configuration. -/
theorem exists_finset_of_mem_throughSet {A : Set V} {x y : V} {ω : Config V}
    (h : ω ∈ throughSet A x y) :
    ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧ (F : Config V) ∈ throughSet A x y := by
  obtain ⟨F, hFω, hF⟩ := exists_finset_of_mem_conn h.1
  refine ⟨F, hFω, hF, ?_⟩
  rintro ⟨hx, hy, havoid⟩
  exact h.2 ⟨hx, hy, localConn_mono_config Aᶜ ⟨x, hx⟩ ⟨y, hy⟩ hFω havoid⟩

/-- Measurability of the existing induced-graph event, with endpoints allowed
outside the domain. Only the domain itself needs to be countable. -/
theorem measurableSet_conn_avoiding (A : Set V) [Countable ↥(Aᶜ : Set V)] (x y : V) :
    MeasurableSet {ω : Config V | ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
      ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion fun hx => MeasurableSet.iUnion fun hy =>
    measurableSet_localConn Aᶜ ⟨x, hx⟩ ⟨y, hy⟩

theorem measurableSet_throughSet [Countable V] (A : Set V) (x y : V) :
    MeasurableSet (throughSet A x y) :=
  (measurableSet_conn x y).diff (measurableSet_conn_avoiding A x y)

/-- Exactly the connections lost on deleting `A` form the through-set event. -/
theorem conn_eq_avoiding_union_throughSet (A : Set V) (x y : V) :
    conn x y = {ω : Config V | ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
        ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩} ∪ throughSet A x y := by
  ext ω
  constructor
  · intro h
    by_cases ha : ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
        ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩
    · exact Or.inl ha
    · exact Or.inr ⟨h, ha⟩
  · rintro (⟨hx, hy, h⟩ | h)
    · exact conn_of_localConn ω Aᶜ ⟨x, hx⟩ ⟨y, hy⟩ h
    · exact h.1

theorem disjoint_avoiding_throughSet (A : Set V) (x y : V) :
    Disjoint {ω : Config V | ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
        ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩} (throughSet A x y) :=
  Set.disjoint_left.mpr fun _ havo hthrough => hthrough.2 havo

/-- Exact two-point decomposition into connections avoiding and going through `A`. -/
@[tag "ZTE7"]
theorem tau_eq_avoiding_add_throughSet [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y : V) :
    tau q x y = law q {ω : Config V | ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
        ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩} +
      law q (throughSet A x y) := by
  rw [tau, conn_eq_avoiding_union_throughSet A x y,
    measure_union (disjoint_avoiding_throughSet A x y) (measurableSet_throughSet A x y)]

/-- The correction is a difference of finite two-point probabilities. -/
theorem law_throughSet_eq_sub [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y : V) :
    law q (throughSet A x y) = tau q x y -
      law q {ω : Config V | ∃ hx : x ∈ Aᶜ, ∃ hy : y ∈ Aᶜ,
        ((openGraph ω).induce Aᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩} := by
  rw [tau_eq_avoiding_add_throughSet q A x y,
    ENNReal.add_sub_cancel_left (measure_ne_top _ _)]

theorem law_throughSet_mono_set (q : Sym2 V → unitInterval) {A B : Set V}
    (hAB : A ⊆ B) (x y : V) : law q (throughSet A x y) ≤ law q (throughSet B x y) :=
  measure_mono (throughSet_mono_set hAB x y)

theorem law_throughSet_le_tau (q : Sym2 V → unitInterval) (A : Set V) (x y : V) :
    law q (throughSet A x y) ≤ tau q x y :=
  measure_mono (throughSet_subset_conn A x y)

/-- A path through `A` can be cut at a vertex of `A` into disjoint connections. -/
theorem throughSet_subset_iUnion_disjointOccurrence (A : Set V) (x y : V) :
    throughSet A x y ⊆ ⋃ a : A, disjointOccurrence (conn x (a : V)) (conn (a : V) y) := by
  intro ω h
  exact (conn_subset_deleted_union A x y h.1).resolve_left h.2

/-- A bound with constant one, obtained by splitting an open path at `A` and
applying BK to the two connection events. -/
@[tag "84FZ"]
theorem law_throughSet_le_tsum_tau_mul [Countable V]
    (q : Sym2 V → unitInterval) (A : Set V) (x y : V) :
    law q (throughSet A x y) ≤ ∑' a : A, tau q x a * tau q a y := by
  refine (measure_mono (throughSet_subset_iUnion_disjointOccurrence A x y)).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun a => ?_))
  exact countable_profile_bk q (isUpperSet_conn x (a : V)) (isUpperSet_conn (a : V) y)

/-- The singleton at the first endpoint gives equality in the through-set bound. -/
theorem law_throughSet_singleton_left (q : Sym2 V → unitInterval) (x y : V) :
    law q (throughSet {x} x y) = tau q x y := by
  rw [throughSet_eq_conn_of_left_mem (mem_singleton x)]
  rfl

/-- The right side of the through-set bound also equals `τ(x,y)` for `A = {x}`.
Thus the coefficient one in that bound is attained. -/
theorem tsum_tau_mul_singleton_left (q : Sym2 V → unitInterval) (x y : V) :
    (∑' a : ({x} : Set V), tau q x a * tau q a y) = tau q x y := by
  simp [tsum_fintype, tau_self]

/-! ### Directed pivotal and cutting events -/

theorem orientedPivotal_ne {ω : Config V} {x y u v : V}
    (h : ω ∈ orientedPivotal x y u v) : u ≠ v := by
  intro huv
  subst v
  exact h.2.1 (conn_trans h.2.2.1 h.2.2.2)

@[simp] theorem orientedPivotal_diag (x y u : V) : orientedPivotal x y u u = ∅ := by
  exact eq_empty_iff_forall_notMem.mpr fun _ h => orientedPivotal_ne h rfl

@[simp] theorem orientedPivotal_self (x u v : V) : orientedPivotal x x u v = ∅ := by
  exact eq_empty_iff_forall_notMem.mpr fun _ h => h.2.1 (SimpleGraph.Reachable.refl x)

/-- A pivotal pair has at most one direction from the first endpoint to the second. -/
theorem not_reverse_orientedPivotal {ω : Config V} {x y u v : V}
    (h : ω ∈ orientedPivotal x y u v) : ω ∉ orientedPivotal x y v u := by
  intro hrev
  rw [orientedPivotal, Sym2.eq_swap] at hrev
  exact h.2.1 (conn_trans h.2.2.1 hrev.2.2.2)

theorem measurableSet_orientedPivotal [Countable V] (x y u v : V) :
    MeasurableSet (orientedPivotal x y u v) := by
  have hi : Measurable (fun ω : Config V => insert s(u, v) ω) := by
    apply Measurable.of_mem
    intro e
    change Measurable (fun ω : Config V => e = s(u, v) ∨ e ∈ ω)
    fun_prop
  have hd : Measurable (fun ω : Config V => ω \ {s(u, v)}) := by fun_prop
  exact ((measurableSet_conn x y).preimage hi).inter
    (((measurableSet_conn x y).preimage hd).compl.inter
      (((measurableSet_conn x u).preimage hd).inter ((measurableSet_conn v y).preimage hd)))

theorem laceEPrime_subset_throughSet (A : Set V) (x y : V) :
    laceEPrime A x y ⊆ throughSet A x y := sdiff_subset

@[simp] theorem laceEPrime_empty (x y : V) : laceEPrime ∅ x y = ∅ := by
  simp [laceEPrime]

/-- No pair can be pivotal for a reflexive connection. -/
@[simp] theorem laceEPrime_self (A : Set V) (x : V) :
    laceEPrime A x x = throughSet A x x := by
  simp [laceEPrime]

theorem measurableSet_laceEPrime [Countable V] (A : Set V) (x y : V) :
    MeasurableSet (laceEPrime A x y) :=
  (measurableSet_throughSet A x y).diff (MeasurableSet.iUnion fun u =>
    MeasurableSet.iUnion fun v =>
      (measurableSet_orientedPivotal x y u v).inter (measurableSet_throughSet A x u))

theorem measurableSet_cuttingEvent [Countable V] (A : Set V) (x y u v : V) :
    MeasurableSet (cuttingEvent A x y u v) :=
  ((measurableSet_laceEPrime A x u).inter (measurableSet_orientedPivotal x y u v)).inter
    (measurableSet_mem s(u, v))

theorem cuttingEvent_subset_conn (A : Set V) (x y u v : V) :
    cuttingEvent A x y u v ⊆ conn x y := by
  intro ω h
  have he : s(u, v) ∈ ω := h.2
  have hp : insert s(u, v) ω ∈ conn x y := h.1.2.1
  rw [Set.insert_eq_of_mem he] at hp
  exact hp

@[simp] theorem cuttingEvent_empty (x y u v : V) : cuttingEvent ∅ x y u v = ∅ := by
  simp [cuttingEvent]

@[simp] theorem cuttingEvent_diag (A : Set V) (x y u : V) :
    cuttingEvent A x y u u = ∅ := by
  simp [cuttingEvent]

/-! ### Endpoint conventions and non-vacuity -/

@[simp] theorem empty_mem_throughSet_iff (A : Set V) (x y : V) :
    (∅ : Config V) ∈ throughSet A x y ↔ x = y ∧ x ∈ A := by
  constructor
  · intro h
    have hxy := (empty_mem_conn_iff x y).mp h.1
    subst y
    exact ⟨rfl, (mem_throughSet_self_iff A x ∅).mp h⟩
  · rintro ⟨rfl, hx⟩
    exact (mem_throughSet_self_iff A x ∅).mpr hx

example : (∅ : Config Bool) ∈ throughSet {false} false false := by simp

example : (∅ : Config Bool) ∉ throughSet {false} true true := by simp

example : ({s(false, true)} : Config Bool) ∈ throughSet {false} false true := by
  rw [throughSet_eq_conn_of_left_mem (mem_singleton false)]
  exact mem_conn_of_mem Bool.false_ne_true (mem_singleton _)

/-- The only edge of a two-vertex graph is a directed pivotal when occupied. -/
theorem singleton_mem_orientedPivotal_bool :
    ({s(false, true)} : Config Bool) ∈ orientedPivotal false true false true := by
  refine ⟨mem_conn_of_mem Bool.false_ne_true (mem_insert _ _), ?_,
    SimpleGraph.Reachable.refl _, SimpleGraph.Reachable.refl _⟩
  simp [empty_mem_conn_iff]

example : (∅ : Config Bool) ∈ laceEPrime {false} false false := by simp

example : (∅ : Config Bool) ∉ laceEPrime {false} true true := by simp

/-- The first direct edge is a genuine cutting pair, so the cutting event is nonempty. -/
example : ({s(false, true)} : Config Bool) ∈ cuttingEvent {false} false true false true := by
  refine ⟨⟨?_, singleton_mem_orientedPivotal_bool⟩, mem_singleton _⟩
  simp

end PercLib.Percolation.Bond.Lace
