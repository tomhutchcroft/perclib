---
id: profile-perturbation-bound
title: Total-variation and observable bounds for summable profile perturbations
difficulty: easy
kind: interface
labels: [good-first-task]
---

# Total-variation and observable bounds for summable profile perturbations

Being done by the project's own agents; do not start it.

## Goal
Prove wiki assertion **W90W** (article `profile-continuity`) in full and tag it. The library
bounds `|P_q(A) − P_r(A)|` by `Σ_i |q_i − r_i|`; the assertion adds the cap by one and the
bound for bounded observables.

## Target
Let `I` be countable, `q, r : I → [0,1]`, `d₁(q,r) = Σ_i |q_i − r_i| ∈ [0, ∞]`.
1. For every measurable event `A`, `|P_q(A) − P_r(A)| ≤ min{1, d₁(q,r)}`.
2. For every bounded measurable `f : Set I → ℝ`,
   `|E_q f − E_r f| ≤ osc(f) · min{1, d₁(q,r)}`, where `osc(f) = sup f − inf f`.

Here `P_q = prodBernoulli q`. Since `d₁` may be infinite, state the real bounds with
`(min 1 d₁).toReal` (or in `ℝ≥0∞`), for example:
```lean
theorem abs_integral_prodBernoulli_sub_le [Countable ι] (q r : ι → unitInterval)
    {f : Set ι → ℝ} (hf : Measurable f) {m M : ℝ} (hfm : ∀ ω, m ≤ f ω) (hfM : ∀ ω, f ω ≤ M) :
    |∫ ω, f ω ∂prodBernoulli q - ∫ ω, f ω ∂prodBernoulli r| ≤
      (M - m) * (min 1 (∑' i, ENNReal.ofReal |(q i : ℝ) - r i|)).toReal
```
(any bounds `m ≤ f ≤ M` give `osc(f) ≤ M − m`, which is the useful form; if you state `osc`
literally, use `⨆`/`⨅` with `BddAbove`/`BddBelow`). Tagged statement: the conjunction of 1
and 2, for the literal supremum over measurable events if you choose that formulation.

Proof idea: the uniform coupling `X_i = 1{U_i ≤ q_i}`, `Y_i = 1{U_i ≤ r_i}` gives
`P(X ≠ Y) ≤ min{1, d₁}` and `|f(X) − f(Y)| ≤ osc(f) 1{X ≠ Y}`. The library has a monotone
coupling (`exists_prodBernoulli_monotone_coupling`, `PercLib/Probability/Coupling/Monotone.lean`)
and the event bounds `prodBernoulli_le_add_tsum_dist`, `abs_prodBernoulli_real_sub_le`
(`PercLib/Probability/TotalVariation.lean`); reuse them rather than building a new coupling.

## Owned files
- `PercLib/Probability/TotalVariation.lean` (append only).
- New `PercLib/Probability/Tags/ProfilePerturbation.lean` (the tagged statement only).
- Its import line in `PercLib.lean`.

## Allowed inputs
`PercLib/Probability/TotalVariation.lean`, `ProdBernoulli.lean`, `Coupling/*`, mathlib; wiki
assertion W90W.

## Stop condition
W90W tagged and proved, modules built with `--wfail`; or the statement is found false as written
(report it).

## Hand-off
Pull request description: the tagged statement, the area lemmas, searches, build result.
