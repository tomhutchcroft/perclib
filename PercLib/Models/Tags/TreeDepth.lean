/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors
-/
/-
New for this project, written on 2026-11-21. A restatement of library lemmas; no upstream
code is copied. Mathematical reference: G. Grimmett, *Percolation* (2nd ed., 1999), the rooted
tree example.
-/
module

public import PercLib.Meta.Tag
public import PercLib.Models.TreeRecursion

/-! # Correspondence wrapper: depth events on the rooted `k`-ary tree

The vertices are the words `List (Fin k)`, the root is `[]`, the children of `u` are the words
`b :: u`, and the profile gives open probability `p` to tree edges, `0` to the other
non-diagonal pairs and any value to diagonal pairs. Write `r n` for the probability that the
root is joined to some word of length `n`.

## Main results

* `kTree_depth_events_union_bound_and_limit`: when the open graph lies in the tree, a word is
  joined to the root exactly when its edges to the root are open, and the root cluster is
  infinite exactly when it reaches every depth; the depth events are measurable; `r 0 = 1`,
  `r n ≤ (k p)ⁿ`, `r n → P(|K(o)| = ∞)`, and `k p < 1` gives an almost surely finite root cluster.
* `kTree_depth_recursion_and_percolation_criterion`: `r (n + 1) = 1 - (1 - p r n)^k` for every
  `k`; for `k ≥ 1`, `P(|K(o)| = ∞) > 0` iff `k p > 1` or `p = 1`; for `k ≥ 2` and `k p = 1` the
  root cluster is almost surely finite; at `p = 1` every tree edge is almost surely open; for
  `k = 0` the root cluster is `{[]}`.

All mathematical inputs are proved in `PercLib.Models.Tree` and `PercLib.Models.TreeRecursion`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

/-- On the rooted `k`-ary tree: for a configuration whose open graph lies in the tree, a word
is joined to the root iff all its edges to the root are open, and the root cluster is infinite
iff it reaches every depth; the depth events are measurable; and with open probability `p` on
tree edges, `0` on other pairs and any diagonal, `r 0 = 1`, `r n ≤ (k p)ⁿ`,
`r n → P(|K(o)| = ∞)`, and `k p < 1` implies `P(|K(o)| = ∞) = 0`. -/
@[tag "GGH2"]
theorem kTree_depth_events_union_bound_and_limit (k : ℕ) :
    (∀ ω : Config (List (Fin k)),
      openGraph ω ≤ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u) →
      ∀ w : List (Fin k),
        (openGraph ω).Reachable [] w ↔ ∀ m < w.length, s(w.drop (m + 1), w.drop m) ∈ ω) ∧
    (∀ ω : Config (List (Fin k)),
      openGraph ω ≤ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u) →
      ((cluster ω []).Infinite ↔
        ∀ n, ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w)) ∧
    (∀ n : ℕ, MeasurableSet {ω : Config (List (Fin k)) |
      ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w}) ∧
    ∀ (p : unitInterval) (q : Sym2 (List (Fin k)) → unitInterval),
      (∀ e, ¬ e.IsDiag → q e =
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
          else 0) →
      law q {ω | ∃ w : List (Fin k), w.length = 0 ∧ (openGraph ω).Reachable [] w} = 1 ∧
      (∀ n : ℕ,
        law q {ω | ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w} ≤
          ((k : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)) ^ n) ∧
      Tendsto
        (fun n => law q {ω | ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w})
        atTop (𝓝 (law q {ω | (cluster ω []).Infinite})) ∧
      ((k : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞) < 1 →
        law q {ω | (cluster ω []).Infinite} = 0) :=
  ⟨fun _ hω => reachable_nil_iff_of_openGraph_le hω,
    fun _ hω => cluster_nil_infinite_iff_forall_reach_depth_of_openGraph_le hω,
    measurableSet_reach_depth,
    fun p q hq => ⟨law_reach_depth_zero q, law_reach_depth_le p q hq,
      tendsto_law_reach_depth p q hq, law_cluster_nil_infinite_eq_zero p q hq⟩⟩

/-- On the rooted `k`-ary tree with open probability `p` on tree edges, `0` on other pairs and
any diagonal: `r (n + 1) = 1 - (1 - p r n)^k` for every `k ≥ 0`; for `k ≥ 1` the root cluster
is infinite with positive probability iff `k p > 1` or `p = 1`; for `k ≥ 2` it is almost surely
finite at `k p = 1`; at `p = 1` every tree edge is almost surely open; and for `k = 0` the root
cluster is `{[]}`. -/
@[tag "UHVH"]
theorem kTree_depth_recursion_and_percolation_criterion (k : ℕ) (p : unitInterval)
    (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    (∀ n : ℕ,
      law q {ω | ∃ w : List (Fin k), w.length = n + 1 ∧ (openGraph ω).Reachable [] w} =
        1 - (1 - (unitInterval.toNNReal p : ℝ≥0∞) *
          law q {ω | ∃ w : List (Fin k), w.length = n ∧ (openGraph ω).Reachable [] w}) ^ k) ∧
    (1 ≤ k →
      (0 < law q {ω | (cluster ω []).Infinite} ↔ 1 < (k : ℝ) * (p : ℝ) ∨ p = 1)) ∧
    (2 ≤ k → (k : ℝ) * (p : ℝ) = 1 → law q {ω | (cluster ω []).Infinite} = 0) ∧
    (p = 1 → ∀ᵐ ω ∂law q,
      (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet ⊆ ω) ∧
    (k = 0 → ∀ ω : Config (List (Fin k)), cluster ω [] = {[]}) :=
  ⟨law_reach_depth_succ p q hq,
    fun hk => law_cluster_nil_infinite_pos_iff hk p q hq,
    fun hk hkp => law_cluster_nil_infinite_eq_zero_of_mul_eq_one hk p q hq hkp,
    ae_kTree_edgeSet_subset_of_eq_one p q hq,
    fun hk => cluster_nil_eq_singleton_of_eq_zero hk⟩

end PercLib.Models
