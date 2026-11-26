---
id: kernel-comparison-off-diagonal
title: Kernel comparison with domination only off the diagonal
difficulty: medium
kind: interface
labels: []
---

# Kernel comparison with domination only off the diagonal

Being done by the project's own agents; do not start it.

## Goal
Prove wiki assertion **CKJQ** (article `intensity-comparison`) in full and tag it. The library
compares two kernels `J ≤ J'` only when the inequality holds on **every** pair, diagonal
included; the assertion assumes it only on non-diagonal pairs, which is enough because loops
never affect graph observables.

## Target
Let `V` be countable and `J, J' : Sym2 V → ℝ≥0` with `J e ≤ J' e` for every non-diagonal `e`.
For every finite `β ≥ 0` and all `x, y`, writing `q = intensityProfile J β`,
`q' = intensityProfile J' β`:
- `τ_q(x,y) ≤ τ_{q'}(x,y)`;
- `P_q(|K(x)| = ∞) ≤ P_{q'}(|K(x)| = ∞)`;
- `P_q(some cluster is infinite) ≤ P_{q'}(some cluster is infinite)`;
- `χ_q(x) ≤ χ_{q'}(x)`;
and consequently `rootCriticalIntensity J' x ≤ rootCriticalIntensity J x` and
`globalCriticalIntensity J' ≤ globalCriticalIntensity J`. Susceptibilities and thresholds may
be infinite; no summability is assumed.

Area lemmas: one `…_of_le_offDiagonal` version of each of `tau_le_of_le`,
`law_cluster_infinite_le_of_le`, `law_exists_cluster_infinite_le_of_le`, `chi_le_of_le`,
`rootCriticalIntensity_anti`, `globalCriticalIntensity_anti`
(`PercLib/Percolation/Bond/IntensityScaling.lean`), with hypothesis
`(h : ∀ e, ¬ e.IsDiag → J e ≤ J' e)`. Proof idea: erase the diagonal of both kernels (the
kernel `fun e => if e.IsDiag then 0 else J e` is pointwise below `J'`'s erased kernel), apply the
existing all-pairs lemmas, and transfer back with `law_event_eq_of_offDiagonal`
(`PercLib/Percolation/Bond/Diagonal/Probability.lean`) or the EYCQ cluster-law statement
(`diagonal_insensitive_cluster_laws`, `PercLib/Probability/Tags/Symmetries.lean`); the
thresholds follow because they are defined from these probabilities. Check the article for
the exact list of conclusions grouped under CKJQ before writing the tagged conjunction.

Tagged statement: the conjunction of all six conclusions under the off-diagonal hypothesis.

## Owned files
- `PercLib/Percolation/Bond/IntensityScaling.lean` (append only).
- New `PercLib/Percolation/Bond/Tags/KernelComparison.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/IntensityScaling.lean`, `Diagonal/Probability.lean`,
`PercLib/Probability/Tags/Symmetries.lean` (use the area lemmas behind EYCQ, not the tagged
statement), `Intensity/Defs.lean`; wiki assertions CKJQ, EYCQ.

## Stop condition
CKJQ tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
