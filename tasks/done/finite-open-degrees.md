---
id: finite-open-degrees
title: Summable incident probabilities give finite open degrees everywhere
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Summable incident probabilities give finite open degrees everywhere

## Goal
Tag wiki assertion **I24D** (article `product-model`). On a host that need not be locally finite
(long-range models), a summable row of edge probabilities at `v` makes the open degree at `v`
finite almost surely, and countability upgrades this to a single almost-sure event on which
every open degree is finite. Every ingredient is proved; the task is to state the assertion
faithfully and assemble it.

## Target
For a countable vertex type `V` and a profile `q`:
1. the expected open degree at `v` equals the off-diagonal row sum `Σ_{w ≠ v} q(v,w)`
   (`lintegral_degree`, `PercLib/Percolation/Bond/Degree.lean`);
2. if that row sum is finite, the open degree at `v` is finite almost surely
   (`ae_finite_neighbors_of_rowSum_lt_top`, `PercLib/Percolation/Bond/LocalFiniteness.lean`);
3. if every row sum is finite, then almost surely every vertex has finite open degree
   (`ae_all_finite_neighbors_of_rowSum_lt_top`, same file).

Sketch of the tagged statement:
```lean
theorem finite_open_degrees_of_rowSum [Countable V] (q : Sym2 V → unitInterval) :
    (∀ v, ∫⁻ ω, ({w | (openGraph ω).Adj v w}.encard : ℝ≥0∞) ∂law q =
        rowSum (fun e => unitInterval.toENNReal (q e)) v) ∧
    (∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞ →
        ∀ᵐ ω ∂law q, ((openGraph ω).neighborSet v).Finite) ∧
    ((∀ v, rowSum (fun e => unitInterval.toENNReal (q e)) v < ∞) →
        ∀ᵐ ω ∂law q, ∀ v, ((openGraph ω).neighborSet v).Finite)
```
Use one spelling of "the open degree is finite" throughout (the neighbour set, or its `encard`
being `< ⊤`); if the two spellings are needed, add the bridging lemma in the area file. The
assertion's remarks about site percolation and dependent models are context, not part of the
statement.

## Owned files
- New `PercLib/Percolation/Bond/Tags/FiniteOpenDegrees.lean` (the tagged statement only).
- New `PercLib/Percolation/Bond/DegreeFiniteness.lean`, only if a bridging lemma is needed.
- Their import lines in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/Degree.lean`, `PercLib/Percolation/Bond/LocalFiniteness.lean`,
`PercLib/Percolation/Bond/Basic.lean`, mathlib; wiki assertions I24D and 5PAT (cylinder
probabilities, tagged in `PercLib/Probability/Tags/ProductModel.lean`). Compare with the tagged
`open_degree_law` (`SZLN`, `PercLib/Percolation/Bond/Tags/CoreOpenDegree.lean`) and reuse its
area lemmas.

## Stop condition
I24D tagged, built with `--wfail`; or the statement is found false as written (report it).

## Hand-off
Pull request description: the tagged statement in full, the lemmas it restates, build result.
