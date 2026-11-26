---
id: correlation-length-condition
title: Correlation lengths of a profile family and the condition (CL) (definition tag)
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Correlation lengths of a profile family and the condition (CL) (definition tag)

## Goal
Tag the definition assertion **J7SM** (article `cutoff-localization`): the mass-weighted
correlation length `ξ_p(r)` of a family of bond profiles and the correlation-length condition
(CL). The same bound `E Σ_{x ∈ K_o} d(o,x)^p ≤ (C_p r)^p χ` is already spelled out as a
hypothesis in `PercLib/Percolation/Bond/SpatialMoments/Localization.lean`; a definition lets later
statements of the article use it by name.

## Target
Let `V` be an additive group, `N : V → ℝ≥0∞` a weight with `d(o,x) = N(x - o)` (for instance a
norm on `ℤ^d`), `o : V` the root and `q : ℝ → Sym2 V → unitInterval` a family of profiles indexed
by the cutoff `r`. With `χ_r = chi (q r) o` and the spatial moment
`spatialMoment (q r) o (fun x => N x ^ p) = E Σ_{x ∈ K_r} d(o,x)^p`
(`PercLib/Percolation/Bond/SpatialMoments/Defs.lean`):
1. `ξ_p(r) = (spatialMoment (q r) o (N ^ p) / χ_r) ^ (1/p)` for finite real `p > 0`;
2. (CL) holds if for every finite `p > 0` there is a finite `C_p` with `ξ_p(r) ≤ C_p r` for every
   `r ≥ 1`; `C_p` may depend on `p`, not on `r`.

Sketch (spelling free):
```lean
/-- The mass-weighted correlation length `ξ_p(r)`. -/
def corrLength (N : V → ℝ≥0∞) (q : ℝ → Sym2 V → unitInterval) (o : V) (p r : ℝ) : ℝ≥0∞ :=
  (spatialMoment (q r) o (fun x => N x ^ p) / chi (q r) o) ^ (1 / p)

/-- The correlation-length condition (CL). -/
@[tag "J7SM"]
def CorrLengthCondition (N : V → ℝ≥0∞) (q : ℝ → Sym2 V → unitInterval) (o : V) : Prop :=
  ∀ p : ℝ, 0 < p → ∃ C : ℝ≥0, ∀ r : ℝ, 1 ≤ r → corrLength N q o p r ≤ C * ENNReal.ofReal r
```
Basic API: unfolding lemmas, and the multiplied form
`corrLength N q o p r ≤ C * ofReal r ↔ spatialMoment (q r) o (N ^ p) ≤ (C * ofReal r) ^ p * chi (q r) o`
for `p > 0` and `0 < χ_r < ∞`, which is the hypothesis shape used in `Localization.lean`.
Do not change `Localization.lean`. If the article's cutoff families are indexed by a different
type, use that type and say so; the order of quantifiers (`C` after `p`, before `r`) is fixed.

## Owned files
- New `PercLib/Percolation/Bond/CutoffLocalization/Defs.lean`.
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Percolation/Bond/SpatialMoments/Defs.lean`, `PercLib/Percolation/Bond/Basic.lean`
(`chi`, `cluster`), mathlib; wiki assertion J7SM.

## Stop condition
J7SM tagged, the multiplied-form lemma proved, module built with `--wfail`.

## Hand-off
Pull request description: both definitions in full, the API lemmas, build result.
