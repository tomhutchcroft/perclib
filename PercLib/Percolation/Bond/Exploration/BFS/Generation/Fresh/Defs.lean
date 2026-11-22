/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Generation/Fresh.lean`; added at source revision
`81ff4de74a4eae0fd87ce59ebb2b09933fd9da95`,
supplied under its Apache-2.0 header. This is a reviewed definitions/constructor interface on the
canonical bond configuration. No alternative configuration model is introduced.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.BFSProduct.Defs

/-!
# An over-approximating set of queryable edges

`freshEdges` uses `univ` at `none`, a conservative over-approximation used for finite-subset
exhaustion, not a finite fresh coordinate set. The permitted fresh set `freshEdgeSet`, whose
fallback is empty because it must be disjoint from revelation, is defined separately.
-/

@[expose] public section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Percolation.Bond.Exploration.BFS
open scoped ENNReal BigOperators Topology

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- The queried edge set `E(A,U)` at a compressed state: for `some (Q,T)` it is
`E(T, (Q ∪ T)ᶜ)`, and for the trivial state the whole space (a superset, which is all the
one-step estimate uses). -/
def freshEdges (σ : FinState V) : Set (Sym2 V) :=
  match σ with
  | some (Q, T) => edgeSet (T : Set V) (((Q : Set V) ∪ (T : Set V))ᶜ)
  | none => univ

end PercLib.Percolation.Bond.Exploration.BFS
