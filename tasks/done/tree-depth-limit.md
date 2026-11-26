---
id: tree-depth-limit
title: Infinite root cluster on a rooted tree as the limit of depth probabilities
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Infinite root cluster on a rooted tree as the limit of depth probabilities

Being done by the project's own agents (finished, under review); do not start it.

## Goal
Prove wiki assertion **GGH2** (article `binary-tree-percolation`) in full and tag it. All parts
are in `PercLib/Models/Tree.lean` except the public statement that the probability of an
infinite root cluster is the limit of the depth probabilities, which appears only inside a proof
in `PercLib/Models/TreeRecursion.lean`.

## Target
The `k`-ary rooted tree has vertices `List (Fin k)` (root `[]`), with an edge from `u` to `b :: u`.
Let `q` be a profile equal to `p` on tree edges and `0` on other non-diagonal pairs (diagonal
arbitrary), and `r_n = P_q(the root is connected to some word of length n)`.
1. (deterministic) If the open graph lies in the tree, a word is connected to the root exactly
   when every edge of its ancestral chain is open (`reachable_nil_iff_of_subset`), and the root
   cluster is infinite exactly when it reaches every depth (`cluster_nil_infinite_iff`).
2. `r_0 = 1`, `r_n ≤ (kp)^n` (`law_reach_depth_le`), and
   `P_q(|K(o)| = ∞) = lim_{n→∞} r_n`.
3. In particular `kp < 1` implies `P_q(|K(o)| = ∞) = 0` (`law_cluster_nil_infinite_eq_zero`).

Note that the library's deterministic lemmas assume the configuration is contained in the
tree's edge set (no loops), while the article assumes the open graph (loops erased) lies in the
tree: either prove the loop-erased form or show the two agree, and say which in the pull
request. New area lemma for 2 (sketch):
```lean
theorem tendsto_law_reach_depth (p : unitInterval) (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e = if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) =>
      ∃ b, w = b :: u).edgeSet then p else 0) :
    Tendsto (fun n => law q {ω | ∃ w : List (Fin k), w.length = n ∧
        (openGraph ω).Reachable [] w}) atTop (𝓝 (law q {ω | (cluster ω []).Infinite}))
```
Extract it from the proof in `TreeRecursion.lean` (around `law_cluster_nil_infinite_pos_iff`)
and, if convenient, re-prove that theorem using it without changing its statement. Tagged
statement: the conjunction of 1-3.

## Owned files
- `PercLib/Models/Tree.lean` (append only), and `PercLib/Models/TreeRecursion.lean` only to reuse
  the new lemma inside existing proofs.
- New `PercLib/Models/Tags/TreeDepth.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Models/{Tree,TreeRecursion}.lean`, `PercLib/Percolation/Bond/*`, mathlib; wiki assertions
GGH2, XHFN.

## Stop condition
GGH2 tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
