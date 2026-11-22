/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Adapted from repository `yujinhkim/lrp`, file
`PercLib/CriticalLRP/Exploration/BFS/Generation/Step.lean`; added at source revision
`81ff4de74a4eae0fd87ce59ebb2b09933fd9da95`,
supplied under its Apache-2.0 header. This is a reviewed definitions/constructor interface on the
canonical bond configuration. No alternative configuration model is introduced.
-/
module

public import PercLib.Percolation.Bond.Exploration.BFS.BFSProduct.Defs

/-!
# The statewise exponential frontier bound

At a finite compressed state, `stateBound` is the power of the scalar one-generation Poisson
bound. At `none`, where a finite frontier is not known, the bound is `⊤`, deliberately supplying
no fictitious finiteness promise. This interface does not prove a cluster moment bound.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PercLib.Percolation.Bond.Exploration.BFS

variable {V : Type*}

/-- The one-step bound attached to a compressed state: at `some (Q,T)` it is
`e^{(λ-1) m #T}`, and at the trivial state `none` it is `⊤` (no information, which is all
that a state without finite processed set and frontier can give). -/
def stateBound (τ m : ℝ) (σ : FinState V) : ℝ≥0∞ :=
  match σ with
  | some (_, T) => ENNReal.ofReal (Real.exp ((τ - 1) * (m * (T.card : ℝ))))
  | none => ⊤

end PercLib.Percolation.Bond.Exploration.BFS
