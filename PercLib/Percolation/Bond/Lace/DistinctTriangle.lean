/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.DoubleConnection
public import PercLib.Percolation.Bond.BoundarySusceptibility

/-!
# Bounding the zeroth lace coefficient by distinct-vertex triangles

## Main results

Two edge-disjoint connections include one path avoiding the direct endpoint pair.
Splitting that path at its first interior vertex supplies three disjoint connection
certificates. BK therefore bounds the zeroth lace coefficient by the part of the
triangle diagram whose three vertices are distinct.

Together with the square bound and the exact diagonal decomposition of the closed
triangle, this gives the optimal coefficient four in the mass bound.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

private theorem exists_split_of_avoids_direct {F : Config V} {x y : V}
    (hxy : x ≠ y) (hF : F ∈ conn x y) (he : s(x, y) ∉ F) :
    ∃ u, u ≠ x ∧ u ≠ y ∧
      F ∈ disjointOccurrence (conn x u) (conn u y) := by
  classical
  obtain ⟨p, hp⟩ := (show (openGraph F).Reachable x y from hF).exists_isPath
  have hn : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hxy
  have ha : (openGraph F).Adj x p.snd := p.adj_snd hn
  have huy : p.snd ≠ y := by
    intro h
    apply he
    simpa only [h] using ((openGraph_adj_iff F x p.snd).mp ha).1
  refine ⟨p.snd, ha.ne.symm, huy, ?_⟩
  exact mem_disjointOccurrence_of_path p hp
    (p.snd_mem_support_of_mem_edges (SimpleGraph.Walk.mk_start_snd_mem_edges hn))

/-- A double connection between distinct endpoints contains three disjoint
connections around a triangle with three distinct vertices. -/
theorem exists_distinct_triangle_of_mem_doubleConn {ω : Config V} {x y : V}
    (hxy : x ≠ y) (hω : ω ∈ doubleConn x y) :
    ∃ u, u ≠ x ∧ u ≠ y ∧
      ω ∈ disjointOccurrence (disjointOccurrence (conn x u) (conn u y)) (conn x y) := by
  classical
  obtain ⟨F, H, hFf, hHf, hd, hFω, hHω, hF, hH⟩ :=
    (mem_doubleConn_iff ω x y).mp hω
  have use_witness (F H : Config V) (hFf : F.Finite) (hHf : H.Finite)
      (hd : Disjoint F H) (hFω : F ⊆ ω) (hHω : H ⊆ ω)
      (hF : F ∈ conn x y) (hH : H ∈ conn x y) (he : s(x, y) ∉ F) :
      ∃ u, u ≠ x ∧ u ≠ y ∧
        ω ∈ disjointOccurrence (disjointOccurrence (conn x u) (conn u y)) (conn x y) := by
    obtain ⟨u, hux, huy, hsplit⟩ := exists_split_of_avoids_direct hxy hF he
    refine ⟨u, hux, huy, ?_⟩
    exact (mem_disjointOccurrence_iff_open
      (isUpperSet_disjointOccurrence (isUpperSet_conn x u) (isUpperSet_conn u y))
      (isUpperSet_conn x y) ω).mpr ⟨F, H, hFf, hHf, hd, hFω, hHω, hsplit, hH⟩
  by_cases he : s(x, y) ∈ F
  · exact use_witness H F hHf hFf hd.symm hHω hFω hH hF
      (fun h => Set.disjoint_left.mp hd he h)
  · exact use_witness F H hFf hHf hd hFω hHω hF hH he

open scoped Classical in
/-- The zeroth lace coefficient is bounded by the triangle diagram with the
intermediate vertex and both endpoints all distinct. -/
theorem piZero_le_distinct_triangle [Countable V]
    (q : Sym2 V → unitInterval) (x y : V) :
    piZero q x y ≤ ∑' u,
      if u = x ∨ y = x ∨ u = y then 0 else
        tau q x u * tau q u y * tau q y x := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  rw [piZero_of_ne q hxy]
  have hsub : doubleConn x y ⊆ ⋃ u : V,
      if u = x ∨ y = x ∨ u = y then ∅ else
        disjointOccurrence (disjointOccurrence (conn x u) (conn u y)) (conn x y) := by
    intro ω hω
    obtain ⟨u, hux, huy, hu⟩ := exists_distinct_triangle_of_mem_doubleConn hxy hω
    refine mem_iUnion.mpr ⟨u, ?_⟩
    simpa only [hux, Ne.symm hxy, huy, or_self, ite_false] using hu
  refine (measure_mono hsub).trans
    ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun u => ?_))
  by_cases hu : u = x ∨ y = x ∨ u = y
  · simp [hu]
  simp only [hu, ite_false]
  have h := (countable_profile_bk q
    (isUpperSet_disjointOccurrence (isUpperSet_conn x u) (isUpperSet_conn u y))
    (isUpperSet_conn x y)).trans
      (mul_le_mul' (countable_profile_bk q (isUpperSet_conn x u) (isUpperSet_conn u y))
        le_rfl)
  simpa only [law, tau, conn_symm x y] using h

open scoped Classical in
/-- Summing the pointwise three-connection bound gives exactly the part of the
closed triangle having three distinct vertices. -/
theorem tsum_piZero_le_distinct_triangle [Countable V]
    (q : Sym2 V → unitInterval) (x : V) :
    ∑' y, piZero q x y ≤ ∑' u, ∑' v,
      if u = x ∨ v = x ∨ u = v then 0 else
        tau q x u * tau q u v * tau q v x := by
  classical
  calc
    ∑' y, piZero q x y ≤ ∑' y, ∑' u,
        if u = x ∨ y = x ∨ u = y then 0 else
          tau q x u * tau q u y * tau q y x :=
      ENNReal.tsum_le_tsum (piZero_le_distinct_triangle q x)
    _ = ∑' u, ∑' y,
        if u = x ∨ y = x ∨ u = y then 0 else
          tau q x u * tau q u y * tau q y x := ENNReal.tsum_comm

end PercLib.Percolation.Bond.Lace
