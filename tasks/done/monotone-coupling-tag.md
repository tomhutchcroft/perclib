---
id: monotone-coupling-tag
title: Monotone product coupling (2ML7)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Monotone product coupling

Being done by the project's own agents; do not start it.

## Goal
Tag wiki assertion **2ML7** (article `product-model`). The mathematics is essentially
`PercLib/Probability/Coupling/Monotone.lean`; it is a shared prerequisite of the lace-expansion
area (see `tasks/areas/lace-expansion.md`).

## Target
State 2ML7 exactly as the wiki block `tag-2ML7` and the article's front-matter `context` say:
independent uniforms `U_e` give `ω_q(e) = 1{U_e ≤ q(e)}` with law the product measure of `q`,
and `q ≤ q'` edgewise gives `ω_q ≤ ω_{q'}` simultaneously (with any further clause of the block,
for example the comparison of cutoff scales). Existing lemmas:
`exists_bond_monotone_coupling`, `exists_prodBernoulli_monotone_coupling`,
`prodBernoulli_mono_event`, `lintegral_prodBernoulli_mono`. If a clause has no lemma, prove it in
the area file.

## Owned files
- `PercLib/Probability/Coupling/Monotone.lean` (append only, only if a clause is missing).
- New `PercLib/Probability/Tags/MonotoneCoupling.lean` (the tagged restatement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`main`, mathlib, the article `wiki/articles/product-model.md`.

## Stop condition
2ML7 stated faithfully and proved, modules built with `lake build --wfail`; or the statement is
false or under-hypothesised as written (open a "Mathematical gap" issue).

## Hand-off
Pull request description: the tagged statement, the area lemmas used, build result. A
maintainer reviews the statement against the wiki.
