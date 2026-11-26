---
id: intrinsic-balls-one-arm
title: Intrinsic balls, spheres and one-arm probabilities (definition tag)
difficulty: medium
kind: interface
labels: []
---

# Intrinsic balls, spheres and one-arm probabilities (definition tag)

## Goal
Tag the definition assertion **8W1Q** (article `intrinsic-geometry`): intrinsic balls and
spheres of a configuration, the intrinsic one-arm probability `Q_r`, and its supremum `Q_r^*`
over deterministic subgraphs. Several ready assertions of the article (`R5XZ`, `KEO7`, …) are
stated with these objects. The library already uses the intrinsic distance
`SimpleGraph.edist (openGraph ω)` inline (`PercLib/Percolation/Bond/BallExploration.lean`); this
task gives the ball, sphere and arm probabilities names and API.

## Target
For `ω : Config V`, `x : V`, `r : ℕ`, with `d_ω = (openGraph ω).edist`:
1. `B_ω(x,r) = {y | d_ω(x,y) ≤ r}` and `S_ω(x,r) = {y | d_ω(x,y) = r}`;
2. for a measure `μ` on configurations and a root `o`, `Q_r = μ {ω | S_ω(o,r).Nonempty}`;
3. for a profile `q`, `Q_r^* = ⨆ H : SimpleGraph V, law q {ω | S_{ω ∩ H.edgeSet}(o,r).Nonempty}`
   (the bond law on `H` keeps the edge probabilities of `q` on `H`; restricting the configuration
   to `H.edgeSet` under `law q` gives exactly that law, and a spanning subgraph always contains
   `o`).

Sketch (spelling free):
```lean
def intrinsicBall (ω : Config V) (x : V) (r : ℕ) : Set V := {y | (openGraph ω).edist x y ≤ r}
def intrinsicSphere (ω : Config V) (x : V) (r : ℕ) : Set V := {y | (openGraph ω).edist x y = r}
@[tag "8W1Q"]
def oneArmProb (μ : Measure (Config V)) (o : V) (r : ℕ) : ℝ≥0∞ :=
  μ {ω | (intrinsicSphere ω o r).Nonempty}
def subgraphOneArmProb (q : Sym2 V → unitInterval) (o : V) (r : ℕ) : ℝ≥0∞ :=
  ⨆ H : SimpleGraph V, oneArmProb (law q) o r  -- with ω replaced by ω ∩ H.edgeSet
```
(Write the last one so that the configuration is intersected with `H.edgeSet`, e.g. via
`(law q).map (· ∩ H.edgeSet)`, and prove the unfolding lemma.) The tag may sit on one of the
definitions with the others referenced from its docstring, or on a small `Tags/` statement
collecting their unfolding lemmas; say which in the pull request.

Basic API (D-35): membership lemmas (`mem_intrinsicBall`, `mem_intrinsicSphere`, `@[simp]`);
`intrinsicSphere_subset_intrinsicBall`; `intrinsicBall_mono` in `r`; monotonicity of
`intrinsicBall` in `ω` (open edges only shorten distances: `ω ⊆ ω'` gives
`B_ω(x,r) ⊆ B_ω'(x,r)`); `x ∈ intrinsicBall ω x 0`; `oneArmProb_le_subgraphOneArmProb`
(take `H = ⊤`) when `μ = law q`; and the article's warning that spheres are not monotone:
on the path `o - u - v` the sphere of radius two contains `v`, and adding the edge `o - v`
empties it (an explicit `Fin 3` example).

## Owned files
- New `PercLib/Percolation/Bond/IntrinsicGeometry/Defs.lean` (definitions and API).
- New `PercLib/Percolation/Bond/Tags/IntrinsicBalls.lean`, only if the tag goes on a statement.
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/Basic.lean`, `PercLib/Percolation/Bond/BallExploration.lean`
(reuse its spelling of the ball), mathlib (`SimpleGraph.edist`); wiki assertion 8W1Q.

## Stop condition
8W1Q tagged, the API above proved, built with `--wfail`.

## Hand-off
Pull request description: the definitions in full, where the tag sits, the API lemmas, build
result.
