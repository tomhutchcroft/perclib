/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Proofs adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Generation/RowCharge.lean`; added at source revision
`81ff4de74a4eae0fd87ce59ebb2b09933fd9da95`, supplied under its Apache-2.0 header.
Definitions have moved to separately reviewed `Defs` modules. This is a proof-only module with
canonical prefix `PercLib.Percolation.Bond.Exploration.BFS`; explicit countability scoping keeps
the source premises while removing
forbidden section-option commands. Mathematical reference: the exploration outline, §4–§5.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.Generation.History.Defs

/-!
# Average intensity per discovered vertex

The row-sum bound is charged once per frontier vertex, avoiding any extra factor of the
frontier size. The statement concerns a finite queried block and does not require finite degree
outside it or a finite configuration graph.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration.BFS
open scoped ENNReal BigOperators Topology

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- **Row-sum charging.**  For a finite frontier `T`, an undiscovered set `U` disjoint from
it, and a finite set `S` of edges of `E(T,U)`, the intensities of `S` sum to at most
`m * #T`.  Each edge is charged to its unique endpoint in `T`, and the row of that endpoint
bounds the charged sum by `m`. -/
theorem sum_le_rowSum [Countable V] {p : Sym2 V → unitInterval} {m : ℝ} (hrow : RowSum p m)
    {T : Finset V} {U : Set V} (hTU : Disjoint (T : Set V) U) (S : Finset (Sym2 V))
    (hS : (S : Set (Sym2 V)) ⊆ edgeSet (T : Set V) U) :
    ∑ e ∈ S, ((p e : ℝ)) ≤ m * (T.card : ℝ) := by
  classical
  have hex : ∀ e ∈ S, ∃ x ∈ (T : Set V), ∃ y ∈ U, e = s(x, y) := fun e he => hS he
  -- each edge of `S` has exactly one endpoint in `T`
  have hone : ∀ e ∈ S, ∑ x ∈ T, (if x ∈ e then ((p e : ℝ)) else 0) = ((p e : ℝ)) := by
    intro e he
    obtain ⟨x0, hx0T, y0, hy0U, rfl⟩ := hex e he
    have hy0T : y0 ∉ (T : Set V) := fun h => (Set.disjoint_left.mp hTU h) hy0U
    have hzero : ∀ x ∈ T, x ≠ x0 →
        (if x ∈ s(x0, y0) then ((p s(x0, y0)) : ℝ) else 0) = 0 := by
      intro x hxT hne
      have hxe : ¬ (x ∈ s(x0, y0)) := by
        rw [Sym2.mem_iff]
        rintro (h | h)
        · exact hne h
        · exact hy0T (h ▸ hxT)
      simp [hxe]
    calc ∑ x ∈ T, (if x ∈ s(x0, y0) then ((p s(x0, y0)) : ℝ) else 0)
        = (if x0 ∈ s(x0, y0) then ((p s(x0, y0)) : ℝ) else 0) :=
          Finset.sum_eq_single x0 hzero (fun hx0 => absurd hx0T hx0)
      _ = ((p s(x0, y0)) : ℝ) := by simp
  -- the per-vertex charge
  have perVertex : ∀ x ∈ T, ∑ e ∈ S.filter (fun e => x ∈ e), ((p e : ℝ)) ≤ m := by
    intro x hxT
    set g : Sym2 V → V := fun e => if h : x ∈ e then Sym2.Mem.other h else x with hg
    have hge : ∀ e ∈ S.filter (fun e => x ∈ e), e = s(x, g e) := by
      intro e he
      have hx : x ∈ e := (Finset.mem_filter.mp he).2
      have h1 : g e = Sym2.Mem.other hx := by
        rw [hg]
        exact dite_eq_left hx
      rw [h1]
      exact (Sym2.other_spec hx).symm
    calc ∑ e ∈ S.filter (fun e => x ∈ e), ((p e : ℝ))
        = ∑ e ∈ S.filter (fun e => x ∈ e), ((p (s(x, g e))) : ℝ) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          exact congrArg (fun z : Sym2 V => ((p z : ℝ))) (hge e he)
      _ = ∑ y ∈ (S.filter (fun e => x ∈ e)).image g, ((p (s(x, y))) : ℝ) := by
          rw [Finset.sum_image]
          intro e he e' he' hgg
          rw [hge e he, hge e' he', hgg]
      _ ≤ m := hrow x _
  calc ∑ e ∈ S, ((p e : ℝ))
      = ∑ e ∈ S, ∑ x ∈ T, (if x ∈ e then ((p e : ℝ)) else 0) := by
        refine Finset.sum_congr rfl (fun e he => ?_)
        exact (hone e he).symm
    _ = ∑ x ∈ T, ∑ e ∈ S, (if x ∈ e then ((p e : ℝ)) else 0) := Finset.sum_comm
    _ = ∑ x ∈ T, ∑ e ∈ S.filter (fun e => x ∈ e), ((p e : ℝ)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_filter]
    _ ≤ ∑ _x ∈ T, m := Finset.sum_le_sum perVertex
    _ = m * (T.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

end PercLib.Percolation.Bond.Exploration.BFS
