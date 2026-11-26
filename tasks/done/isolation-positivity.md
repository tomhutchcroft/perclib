---
id: isolation-positivity
title: When a vertex is isolated with positive probability
difficulty: medium
kind: interface
labels: []
---

# When a vertex is isolated with positive probability

## Goal
Prove wiki assertion **UNJ6** (article `open-degree-laws`) in full and tag it. The library
expresses the isolation probability as a decreasing limit of finite products
(`law_isolated_eq_iInf`, `PercLib/Percolation/Bond/DegreeGenerating.lean`); the positivity
criterion is missing.

## Target
On a countable vertex set, with `D_v` the open degree of `v` and `R_v = Σ_{w ≠ v} q_{vw}` the
off-diagonal row sum (`rowSum`, `PercLib/Percolation/Bond/Basic.lean`):
1. `P_q(D_v = 0) = ∏_{w ≠ v} (1 − q_{vw})`, the product being the decreasing limit over any finite
   exhaustion of the other vertices (exists as `law_isolated_eq_iInf`);
2. `P_q(D_v = 0) > 0` if and only if `R_v < ∞` and `q_{vw} < 1` for every `w ≠ v`.

Sketch of the new area lemma:
```lean
theorem law_isolated_pos_iff [Countable V] (q : Sym2 V → unitInterval) (v : V) :
    0 < law q {ω : Config V | ∀ w, ¬ (openGraph ω).Adj v w} ↔
      rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞ ∧ ∀ w, w ≠ v → q s(v, w) < 1
```
Proof idea (article): a factor `1` kills the product; otherwise use `−log(1−t) ≥ t` for the
forward direction and `−log(1−t) ≤ 2t` on `[0, 1/2]` for the converse, after removing the
finitely many terms above `1/2`. Search mathlib for infinite products of `1 − a_i`
(`ENNReal.tprod`, `Real.tendsto_prod_one_sub`, `Multipliable`, products in `NNReal`) first.
Tagged statement: the conjunction of 1 and 2. Diagonal values of `q` must play no role.

## Owned files
- `PercLib/Percolation/Bond/DegreeGenerating.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/IsolationPositivity.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/DegreeGenerating.lean`, `Basic.lean`, `InfiniteDegree.lean`, mathlib;
wiki assertion UNJ6.

## Stop condition
UNJ6 tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
