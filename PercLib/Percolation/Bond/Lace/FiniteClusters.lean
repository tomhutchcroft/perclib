/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for this project; no upstream Lean code is copied.
-/
module

public import PercLib.Percolation.Bond.Lace.CuttingFactorization

@[expose] public section
noncomputable section

open MeasureTheory Set

namespace PercLib.Percolation.Bond.Lace

variable {V : Type*}

/-- Vanishing percolation probability at a vertex implies finiteness of every
deleted-bond cluster at that vertex, almost surely. No susceptibility bound is
needed for the cluster-factorization hypothesis. -/
theorem ae_deleted_cluster_finite_of_no_infinite_cluster
    (q : Sym2 V → unitInterval) (a : V)
    (hzero : law q {ω : Config V | (cluster ω a).Infinite} = 0) (u v : V) :
    ∀ᵐ ω ∂law q, (cluster (ω \ {s(u, v)}) a).Finite := by
  have hf : ∀ᵐ ω ∂law q, (cluster ω a).Finite := by
    rw [ae_iff]
    exact hzero
  filter_upwards [hf] with ω hω
  exact hω.subset (cluster_mono sdiff_subset a)

end PercLib.Percolation.Bond.Lace
