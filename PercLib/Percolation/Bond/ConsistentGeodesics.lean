/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Consistent choice of geodesics. New for this project; no upstream proof is copied. The
construction is the standard one: among shortest paths take the one whose list of successive
displacements is least for a fixed well-order, compared first by length and then
lexicographically (mathlib's `List.Shortlex`).
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.List.Shortlex
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Consistent geodesics

A path in a graph on an additive group `V` from `u` is recorded by the list `ds` of its
successive displacements; its vertex list is `ds.scanl (· + ·) u`. Choosing the
`List.Shortlex`-least displacement list for a well-order of `V` selects a shortest path which
is unchanged by left translation and by passing to a subgraph that contains it.

## Main results

* `exists_scanl_eq_support_of_walk`, `exists_walk_of_isChain_scanl`: walks correspond to
  displacement lists along which consecutive partial sums are adjacent.
* `scanl_add_left`: partial sums from a translated start are the translated partial sums.
* `exists_consistent_geodesics`: on a countable additive group there is a choice
  `γ H u v` of a shortest path for all graphs `H` and vertices `u, v` which is
  translation-equivariant, consistent under restriction to subgraphs containing the chosen
  path, and measurable as a function of the open graph of a bond configuration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PercLib.Percolation.Bond

variable {V : Type*} [AddGroup V]

/-- Partial sums from a left-translated start are the left translates of the partial sums. -/
theorem scanl_add_left (a u : V) (ds : List V) :
    ds.scanl (· + ·) (a + u) = (ds.scanl (· + ·) u).map (a + ·) := by
  induction ds generalizing u with
  | nil => simp
  | cons d ds ih => simp only [List.scanl_cons, List.map_cons, add_assoc, ih]

/-- Every walk from `u` is the list of partial sums of its successive displacements. -/
theorem exists_scanl_eq_support_of_walk {H : SimpleGraph V} {u v : V} (p : H.Walk u v) :
    ∃ ds : List V, ds.scanl (· + ·) u = p.support ∧ ds.length = p.length ∧
      u + ds.sum = v := by
  induction p with
  | nil => exact ⟨[], by simp⟩
  | @cons u w v h q ih =>
    obtain ⟨ds, h1, h2, h3⟩ := ih
    refine ⟨(-u + w) :: ds, ?_, ?_, ?_⟩
    · simp [List.scanl_cons, h1]
    · simp [h2]
    · rw [List.sum_cons, ← add_assoc, add_neg_cancel_left, h3]

/-- A displacement list along which consecutive partial sums are adjacent is a walk. -/
theorem exists_walk_of_isChain_scanl {H : SimpleGraph V} {u v : V} {ds : List V}
    (hc : (ds.scanl (· + ·) u).IsChain H.Adj) (hv : u + ds.sum = v) :
    ∃ p : H.Walk u v, p.support = ds.scanl (· + ·) u ∧ p.length = ds.length := by
  induction ds generalizing u with
  | nil =>
    simp only [List.sum_nil, add_zero] at hv
    subst hv
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | cons d ds ih =>
    rw [List.scanl_cons, List.isChain_cons] at hc
    have hadj : H.Adj u (u + d) := hc.1 (u + d) (by simp [List.head?_scanl])
    obtain ⟨q, hq1, hq2⟩ := ih hc.2 (by rw [← hv, List.sum_cons, add_assoc])
    exact ⟨SimpleGraph.Walk.cons hadj q, by simp [hq1, List.scanl_cons], by simp [hq2]⟩

/-- On a countable additive group, shortest paths `γ H u v` (as vertex lists) can be chosen
for all graphs `H` so that the choice is translation-equivariant, unchanged when `H` is
replaced by a subgraph containing the chosen path, and measurable in the open graph of a bond
configuration. The value for unconnected vertices is `[]`. -/
theorem exists_consistent_geodesics [Countable V] :
    ∃ γ : SimpleGraph V → V → V → List V,
      (∀ (H : SimpleGraph V) (u v : V), H.Reachable u v →
        ∃ p : H.Walk u v, p.IsPath ∧ p.length = H.dist u v ∧ p.support = γ H u v) ∧
      (∀ (H : SimpleGraph V) (a u v : V),
        γ (H.map (Equiv.addLeft a).toEmbedding) (a + u) (a + v) = (γ H u v).map (a + ·)) ∧
      (∀ (H H' : SimpleGraph V) (u v : V), H' ≤ H → (γ H u v).IsChain H'.Adj →
        γ H' u v = γ H u v) ∧
      (∀ (u v : V) (l : List V),
        MeasurableSet {ω : Config V | γ (openGraph ω) u v = l}) := by
  classical
  let r : List V → List V → Prop := List.Shortlex WellOrderingRel
  have hwf : WellFounded r := List.Shortlex.wf WellOrderingRel.isWellOrder.wf
  let D : SimpleGraph V → V → V → Set (List V) := fun H u v =>
    {ds | (ds.scanl (· + ·) u).IsChain H.Adj ∧ u + ds.sum = v}
  let γ : SimpleGraph V → V → V → List V := fun H u v =>
    if h : (D H u v).Nonempty then (hwf.min _ h).scanl (· + ·) u else []
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · -- the chosen path is a shortest path
    intro H u v huv
    obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
    obtain ⟨ds, h1, h2, h3⟩ := exists_scanl_eq_support_of_walk p
    have hds : ds ∈ D H u v := ⟨by rw [h1]; exact p.isChain_adj_support, h3⟩
    have hD : (D H u v).Nonempty := ⟨ds, hds⟩
    have hmD : hwf.min _ hD ∈ D H u v := hwf.min_mem _ hD
    obtain ⟨q, hq1, hq2⟩ := exists_walk_of_isChain_scanl hmD.1 hmD.2
    have hlen : q.length = H.dist u v := by
      refine le_antisymm ?_ (SimpleGraph.dist_le q)
      rw [hq2, ← hp, ← h2]
      by_contra hlt
      exact hwf.not_lt_min _ hds (List.Shortlex.of_length_lt (not_le.mp hlt))
    refine ⟨q, q.isPath_of_length_eq_dist hlen, hlen, ?_⟩
    simp only [γ, dite_eq_left hD]
    exact hq1
  · -- translation equivariance
    intro H a u v
    have hadj : (fun x y : V => (H.map (Equiv.addLeft a).toEmbedding).Adj (a + x) (a + y)) =
        H.Adj := by
      funext x y
      exact propext (SimpleGraph.map_adj_apply (f := (Equiv.addLeft a).toEmbedding))
    have hD : D (H.map (Equiv.addLeft a).toEmbedding) (a + u) (a + v) = D H u v := by
      ext ds
      simp only [D, Set.mem_ofPred_eq, scanl_add_left, List.isChain_map, hadj, add_assoc,
        add_right_inj]
    simp only [γ, hD]
    split_ifs <;> simp [scanl_add_left]
  · -- consistency under restriction
    intro H H' u v hle hc
    have hsub : D H' u v ⊆ D H u v := fun ds h => ⟨h.1.imp (fun _ _ h => hle h), h.2⟩
    by_cases hD : (D H u v).Nonempty
    · have hmD : hwf.min _ hD ∈ D H u v := hwf.min_mem _ hD
      have hγ : γ H u v = (hwf.min _ hD).scanl (· + ·) u := dite_eq_left hD
      rw [hγ] at hc ⊢
      have hm' : hwf.min _ hD ∈ D H' u v := ⟨hc, hmD.2⟩
      have hD' : (D H' u v).Nonempty := ⟨_, hm'⟩
      have hmin : hwf.min _ hD' = hwf.min _ hD :=
        hwf.min_eq_of_forall_not_lt hm' (fun x hx => hwf.not_lt_min _ (hsub hx))
      simp only [γ, dite_eq_left hD', hmin]
    · have hD' : ¬ (D H' u v).Nonempty := fun h => hD (h.mono hsub)
      simp only [γ, dite_eq_right hD, dite_eq_right hD']
  · -- measurability
    intro u v l
    have hmem : ∀ ds : List V, MeasurableSet {ω : Config V | ds ∈ D (openGraph ω) u v} := by
      intro ds
      have hset : {ω : Config V | ds ∈ D (openGraph ω) u v} =
          {ω | (ds.scanl (· + ·) u).IsChain (openGraph ω).Adj} ∩ {_ω | u + ds.sum = v} := rfl
      rw [hset]
      refine MeasurableSet.inter ?_ (MeasurableSet.const _)
      cases ds with
      | nil => rw [List.scanl_nil]; exact measurableSet_isChain_openGraph u []
      | cons d ds =>
        rw [List.scanl_cons]
        exact measurableSet_isChain_openGraph u _
    have hmin : ∀ ds : List V, MeasurableSet
        {ω : Config V | ∃ h : (D (openGraph ω) u v).Nonempty, hwf.min _ h = ds} := by
      intro ds
      have hset : {ω : Config V | ∃ h : (D (openGraph ω) u v).Nonempty, hwf.min _ h = ds} =
          {ω | ds ∈ D (openGraph ω) u v} ∩
            ⋂ ds' : List V, {ω | r ds' ds → ds' ∉ D (openGraph ω) u v} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
        constructor
        · rintro ⟨h, rfl⟩
          exact ⟨hwf.min_mem _ h, fun ds' hr hds' => hwf.not_lt_min _ hds' hr⟩
        · rintro ⟨hds, hlt⟩
          exact ⟨⟨ds, hds⟩, hwf.min_eq_of_forall_not_lt hds (fun x hx hr => hlt x hr hx)⟩
      rw [hset]
      refine (hmem ds).inter (MeasurableSet.iInter fun ds' => ?_)
      by_cases hr : r ds' ds
      · have : {ω : Config V | r ds' ds → ds' ∉ D (openGraph ω) u v} =
            {ω | ds' ∈ D (openGraph ω) u v}ᶜ := by
          ext ω; simp [hr]
        rw [this]
        exact (hmem ds').compl
      · have : {ω : Config V | r ds' ds → ds' ∉ D (openGraph ω) u v} = univ := by
          ext ω; simp [hr]
        rw [this]
        exact MeasurableSet.univ
    have hempty : MeasurableSet {ω : Config V | ¬ (D (openGraph ω) u v).Nonempty} := by
      have : {ω : Config V | ¬ (D (openGraph ω) u v).Nonempty} =
          (⋃ ds : List V, {ω | ds ∈ D (openGraph ω) u v})ᶜ := by
        ext ω; simp [Set.Nonempty]
      rw [this]
      exact (MeasurableSet.iUnion hmem).compl
    have hset : {ω : Config V | γ (openGraph ω) u v = l} =
        (⋃ ds : List V, {_ω : Config V | ds.scanl (· + ·) u = l} ∩
          {ω | ∃ h : (D (openGraph ω) u v).Nonempty, hwf.min _ h = ds}) ∪
        ({ω | ¬ (D (openGraph ω) u v).Nonempty} ∩ {_ω | l = []}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
      by_cases hD : (D (openGraph ω) u v).Nonempty
      · simp only [γ, dite_eq_left hD]
        constructor
        · intro h
          exact Or.inl ⟨_, h, hD, rfl⟩
        · rintro (⟨ds, hl, h, rfl⟩ | ⟨hno, -⟩)
          · exact hl
          · exact absurd hD hno
      · simp only [γ, dite_eq_right hD]
        constructor
        · intro h
          exact Or.inr ⟨hD, h.symm⟩
        · rintro (⟨ds, -, h, -⟩ | ⟨-, h⟩)
          · exact absurd h hD
          · exact h.symm
    rw [hset]
    refine MeasurableSet.union (MeasurableSet.iUnion fun ds => ?_) (hempty.inter
      (MeasurableSet.const _))
    exact (MeasurableSet.const _).inter (hmin ds)

end PercLib.Percolation.Bond
