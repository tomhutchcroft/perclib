/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New proof-only results, derived here; no old-source code is copied.
Mathematical reference: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 (the change event used in the softened-edge coupling). The results below are
measurability statements only; they assert no continuity or probability estimate.
-/
module

public import PercLib.Percolation.Bond.IndependentLayer.Exploration

/-!
# Definitions for component-change crossing events

The boundary event joins a vertex in the old cluster to a vertex outside it, along an edge from
the second configuration. The change event compares the root cluster after adding that second
configuration. They concern arbitrary bond configurations and are exact, not finite-graph
substitutes or approximate events.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The boundary event of the ordered pair `p = (u, v)`: in the configuration pair `z = (ω, D)`,
the vertex `p.1` lies in the `ω`-cluster of `o`, the vertex `p.2` does not, and the pair
`s(p.1, p.2)` is open in `D`.

Such a pair is precisely an added pair that joins the old cluster of `o` to its complement. -/
def crossingPair (o : V) (p : V × V) : Set (Config V × Config V) :=
  {z | p.1 ∈ cluster z.1 o} ∩ {z | p.2 ∉ cluster z.1 o} ∩ {z | s(p.1, p.2) ∈ z.2}

/-- The union-change event at the root `o`: the cluster of `o` differs between `ω` and `ω ∪ D`.

Only one inclusion can fail, because the cluster is monotone in the configuration, so this is the
same as asking that some vertex newly enters the cluster. -/
def unionChange (o : V) : Set (Config V × Config V) :=
  {z | cluster (z.1 ∪ z.2) o ≠ cluster z.1 o}

end PercLib.Percolation.Bond
