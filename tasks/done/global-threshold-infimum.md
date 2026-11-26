---
id: global-threshold-infimum
title: The global critical intensity is the infimum of the rooted ones
difficulty: easy
kind: interface
labels: [good-first-task]
---

# The global critical intensity is the infimum of the rooted ones

## Goal
Prove wiki assertion **JZN0** (article `criticality`) and tag it. The library has only the
inequality `globalCriticalIntensity J ≤ rootCriticalIntensity J x`
(`globalCriticalIntensity_le_rootCriticalIntensity`,
`PercLib/Percolation/Bond/RootIndependence.lean`).

## Target
On a countable vertex set, for every kernel `J`,
`β_c^{global} = inf_{v ∈ V} β_c(v)`. Sketch:
```lean
theorem globalCriticalIntensity_eq_iInf_rootCriticalIntensity [Countable V]
    (J : Sym2 V → ℝ≥0) :
    globalCriticalIntensity J = ⨅ v, rootCriticalIntensity J v
```
Proof: the event that some cluster is infinite is the countable union over roots of the rooted
events, so it has positive probability iff some rooted event does (`measure_iUnion_null_iff`);
hence the parameter set defining `globalCriticalIntensity` is the union over `v` of those
defining `rootCriticalIntensity J v` (`PercLib/Percolation/Bond/Intensity/Defs.lean`), and
`sInf` of a union is the infimum of the `sInf`s (`sInf_iUnion`). The empty vertex type is
covered (both sides are `⊤`). Tagged statement: the equality.

## Owned files
- `PercLib/Percolation/Bond/RootIndependence.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/GlobalThreshold.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/{RootIndependence,Basic}.lean`, `Intensity/Defs.lean`, mathlib; wiki
assertion JZN0.

## Stop condition
JZN0 tagged and proved, modules built with `--wfail`.

## Hand-off
Pull request description: the tagged statement, the area lemma, searches, build result.
