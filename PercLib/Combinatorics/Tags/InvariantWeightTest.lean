/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
Correspondence wrapper for the invariant-weight optimization assertion G3HT, proved from
`InvariantWeightTest.lean`. No new definitions.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Combinatorics.InvariantWeightTest

/-!
# Invariant weighted tests for the root-edge square sum

Restates `SimpleGraph.tsum_incidenceSet_sq_le_sq_iff_forall_invariant_weight` under the
hypotheses of the assertion.

## Main results

* `SimpleGraph.tsum_incidenceSet_sq_le_sq_iff_forall_invariant_weight_of_isPretransitive`: for
  a group acting transitively by automorphisms on a countable simple graph with an edge, the
  root-edge square sum of an invariant `a` is at most `B ^ 2` iff every normalized invariant test
  weight supported on finitely many edge orbits gives `∑_{e ∋ o} √(w e) a e ≤ B`.
-/

@[expose] public section
noncomputable section

open scoped ENNReal NNReal

namespace SimpleGraph

/-- **G3HT.** Let a group `Γ` act transitively by automorphisms on a countable simple graph `G`
with at least one edge, and fix a root `o`. Suppose each edge orbit has finite intersection with
the set `E_o` of edges at `o`. Let `a : Sym2 V → [0, ∞]` be `Γ`-invariant on edges and let
`0 ≤ B < ∞`. Then `∑_{e ∈ E_o} a e ^ 2 ≤ B ^ 2` if and only if, for every nonnegative
`Γ`-invariant weight `w` supported on finitely many edge orbits with `∑_{e ∈ E_o} w e = 1`,
`∑_{e ∈ E_o, w e > 0} √(w e) a e ≤ B`. Zero-weight terms are omitted automatically, since
`0 * ⊤ = 0` in `ℝ≥0∞`. -/
@[tag "G3HT"]
theorem tsum_incidenceSet_sq_le_sq_iff_forall_invariant_weight_of_isPretransitive
    {V Γ : Type*} [Countable V] [Group Γ] [MulAction Γ V] [MulAction.IsPretransitive Γ V]
    (G : SimpleGraph V) (hG : ∀ (g : Γ) (x y : V), G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (_hne : G.edgeSet.Nonempty) (o : V)
    (hfin : ∀ e ∈ G.edgeSet,
      {f ∈ G.incidenceSet o | ∃ g : Γ, Sym2.map (g • ·) e = f}.Finite)
    {a : Sym2 V → ℝ≥0∞} (ha : ∀ g : Γ, ∀ e ∈ G.edgeSet, a (Sym2.map (g • ·) e) = a e)
    (B : ℝ≥0) :
    ∑' e : G.incidenceSet o, a e ^ 2 ≤ (B : ℝ≥0∞) ^ 2 ↔
      ∀ w : Sym2 V → ℝ≥0, (∀ g : Γ, ∀ e ∈ G.edgeSet, w (Sym2.map (g • ·) e) = w e) →
        (∃ F : Finset (Sym2 V), ↑F ⊆ G.edgeSet ∧
          ∀ e ∈ G.edgeSet, w e ≠ 0 → ∃ f ∈ F, ∃ g : Γ, Sym2.map (g • ·) f = e) →
        ∑' e : G.incidenceSet o, (w e : ℝ≥0∞) = 1 →
        ∑' e : G.incidenceSet o, (NNReal.sqrt (w e) : ℝ≥0∞) * a e ≤ B :=
  tsum_incidenceSet_sq_le_sq_iff_forall_invariant_weight G hG o hfin ha B

end SimpleGraph
