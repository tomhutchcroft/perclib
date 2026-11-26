---
id: finite-graph-susceptibility-levels
title: On a finite connected graph every susceptibility level has a unique parameter
difficulty: hard
kind: interface
labels: []
---

# On a finite connected graph every susceptibility level has a unique parameter

## Goal
Prove wiki assertion **6JZB** (article `finite-graph-criticality`) and tag it. On a finite
connected graph, the susceptibility `p ↦ χ_v(p) = E_p|K_v|` of homogeneous bond percolation is a
polynomial that increases strictly from `1` to `N`, so each level in `[1, N]` is attained at
exactly one parameter. This is how finite-graph "critical" parameters such as `p_λ` (level
`λ N^{1/3}`) are defined.

## Target
Let `G` be a connected simple graph on a finite type `V` with `N = |V| ≥ 2`, and let
`q_p(e) = p` for `e ∈ G.edgeSet` and `0` otherwise (`p ∈ [0,1]`). For each vertex `v`:
1. there is a real polynomial `P` with `χ_v(p) = P(p)` for all `p ∈ [0,1]`;
2. `p ↦ χ_v(p)` is continuous and strictly increasing on `[0,1]`, with `χ_v(0) = 1` and
   `χ_v(1) = N`;
3. each `c ∈ [1, N]` has exactly one `p ∈ [0,1]` with `χ_v(p) = c`, and no `c` outside `[1, N]`
   is attained;
4. in particular the solution at `c = λ N^{1/3}` (`λ > 0`) lies in `(0,1)` iff
   `1 < λ N^{1/3} < N`, and for fixed `λ > 0` this holds for all large `N`. (The article says
   "on a transitive graph" here only so that the solution does not depend on `v`; state 4 for
   every `v`, or for transitive `G`, whichever is faithful and free.)

Sketch of the profile and one area lemma:
```lean
-- inline profile: fun e => if e ∈ G.edgeSet then p else 0
theorem strictMono_chi_of_connected [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (hN : 2 ≤ Fintype.card V) (v : V) :
    StrictMono fun p : unitInterval =>
      (chi (fun e => if e ∈ G.edgeSet then p else 0) v).toReal
```
Intended proof (article): expand over the finitely many configurations for 1; monotone coupling
for monotonicity (`chi_mono`, `PercLib/Percolation/Bond/ProfileRegularity.lean`); for strictness,
an edge `e` at `v` has positive probability of being open at `q` but closed at `p` while all other
edges are closed at `q`, raising `|K_v|` from 1 to 2; 3 follows by the intermediate value theorem.
Search the library for an existing finite-expansion formula of `law q` on finitely many
coordinates (`PercLib/Probability/FiniteExpectation.lean`, `ProductExpectation.lean`).

Tagged statement: the conjunction of 1–4.

## Owned files
- New `PercLib/Models/FiniteGraphSusceptibility.lean` (area lemmas).
- New `PercLib/Models/Tags/FiniteGraphSusceptibility.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Models/FiniteGraph.lean`, `PercLib/Percolation/Bond/ProfileRegularity.lean`,
`PercLib/Percolation/Bond/ClusterCount.lean`, `PercLib/Probability/FiniteExpectation.lean`,
`PercLib/Probability/ProductExpectation.lean`, `PercLib/Probability/Coupling/`, mathlib; wiki
assertion 6JZB (its proof uses no other assertion).

## Stop condition
6JZB tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement in full, the area lemmas, what was searched,
build result.
