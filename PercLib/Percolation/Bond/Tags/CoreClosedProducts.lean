/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project, written on 2026-11-21. A restatement of library lemmas; no upstream
code is copied.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Percolation.Bond.ClusterLaw
public import PercLib.Percolation.Bond.DegreeGenerating

/-! # Correspondence wrappers: isolation and finite-cluster products

## Main results

* `law_degree_eq_zero_eq_tprod_and_pos_iff`: on a countable vertex set, the probability that
  `v` has open degree zero is `∏'_{w ≠ v} (1 - q(s(v,w)))`, and it is positive if and only if
  the off-diagonal row sum at `v` is finite and `q(s(v,w)) < 1` for every `w ≠ v`.
* `cluster_eq_finset_eq_inter_and_law_eq_tprod`: for a finite set `C ∋ x`,
  `{K(x) = C} = I_C ∩ D_C` on any vertex set; on a countable vertex set the three events are
  measurable and `P(K(x) = C) = P(I_C) P(D_C) = P(I_C) ∏'_{u ∈ C, v ∉ C} (1 - q(s(u,v)))`.

All mathematical inputs are proved in `PercLib.Percolation.Bond.DegreeGenerating` and
`PercLib.Percolation.Bond.ClusterLaw`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- On a countable vertex set, the probability that `v` has open degree zero is the product of
the closed probabilities of the pairs at `v`; it is positive if and only if the off-diagonal row
sum at `v` is finite and no pair at `v` is certain. -/
@[tag "UNJ6"]
theorem law_degree_eq_zero_eq_tprod_and_pos_iff [Countable V] (q : Sym2 V → unitInterval)
    (v : V) :
    law q {ω : Config V | {w | (openGraph ω).Adj v w}.encard = 0} =
      ∏' w : {w // w ≠ v}, (1 - (unitInterval.toNNReal (q s(v, w.1)) : ℝ≥0∞)) ∧
    (0 < law q {ω : Config V | {w | (openGraph ω).Adj v w}.encard = 0} ↔
      rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞ ∧ ∀ w, w ≠ v → q s(v, w) < 1) :=
  ⟨law_degree_eq_zero_eq_tprod q v, law_degree_eq_zero_pos_iff q v⟩

/-- For a finite set `C ∋ x`, on any vertex set, the cluster of `x` is `C` exactly when every
vertex of `C` is connected to `x` inside `C` and every pair from `C` to its complement is
closed. On a countable vertex set these three events are measurable, and
`P(K(x) = C) = P(I_C) P(D_C)` with `P(D_C)` the product of the closed probabilities of the
boundary pairs, each indexed once with its endpoint in `C` first. -/
@[tag "R3I9"]
theorem cluster_eq_finset_eq_inter_and_law_eq_tprod (x : V) (C : Finset V) (hx : x ∈ C) :
    {ω : Config V | cluster ω x = C} =
      {ω : Config V | ∀ y ∈ C, ω ∈ localConn (C : Set V) x y} ∩
        {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} ∧
    ∀ [Countable V] (q : Sym2 V → unitInterval),
      MeasurableSet {ω : Config V | cluster ω x = C} ∧
      MeasurableSet {ω : Config V | ∀ y ∈ C, ω ∈ localConn (C : Set V) x y} ∧
      MeasurableSet {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} ∧
      law q {ω : Config V | cluster ω x = C} =
        law q {ω : Config V | ∀ y ∈ C, ω ∈ localConn (C : Set V) x y} *
          law q {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} ∧
      law q {ω : Config V | ∀ u ∈ C, ∀ v ∉ C, s(u, v) ∉ ω} =
        ∏' z : {z : V × V // z.1 ∈ C ∧ z.2 ∉ C},
          (1 - (unitInterval.toNNReal (q s(z.1.1, z.1.2)) : ℝ≥0∞)) :=
  ⟨setOf_cluster_eq_eq_inter (C := (C : Set V)) hx, fun q =>
    ⟨measurableSet_setOf_cluster_eq x (C : Set V),
      measurableSet_setOf_forall_localConn x C.countable_toSet,
      measurableSet_setOf_boundary_closed (C : Set V),
      law_cluster_eq_eq_mul q (C := (C : Set V)) hx,
      law_boundary_closed_eq_tprod q (C : Set V)⟩⟩

end PercLib.Percolation.Bond
