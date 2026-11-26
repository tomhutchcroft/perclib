---
id: lrp-I526
title: Lemma I.5.26, signed driven ODE with two vanishing errors (port)
difficulty: medium
kind: proof-only
labels: []
---

# Lemma I.5.26, signed driven ODE with two vanishing errors (port)

## Goal
Port Lemma I.5.26 of arXiv:2508.18807v1: the asymptotic ratio for a signed solution of a
driven linear ODE whose forcing is regularly varying of larger index. Follow "Rules for port
tasks" in `tasks/README.md`.

## Target
Source file (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`):
`PercLib/CriticalLRP/Analysis/Lemma_I_5_26.lean`.

Main statement (source `lemma_I_5_26`): let `h` be measurable, regularly varying of index
`b > 0` and eventually positive; let `0 < a < b`, `A, C ∈ ℝ`; let `f` be differentiable on
`(0, ∞)` with `|f| ≤ C h` eventually and, eventually,
`f'(x) = ((a + ε₁(x)) f(x) + (A + ε₂(x)) h(x)) / x` with `ε₁, ε₂ → 0`. Then
`f(r)/h(r) → A/(b − a)`, equivalently `f − (A/(b−a)) h = o(h)`. Sketch:
```lean
theorem tendsto_div_of_signed_driven_ode {h f f' ε₁ ε₂ : ℝ → ℝ} {a b A C : ℝ}
    (hb : 0 < b) (hh : RegularlyVarying b h) (hhm : Measurable h)
    (ha : 0 < a) (hab : a < b) (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hO : ∀ᶠ r in atTop, |f r| ≤ C * h r)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hode : ∀ᶠ x in atTop, f' x = ((a + ε₁ x) * f x + (A + ε₂ x) * h x) / x) :
    Tendsto (fun r => f r / h r) atTop (𝓝 (A / (b - a)))
```
Port also the little-o form (`lemma_I_5_26_isLittleO'`), the one-error and signed forms
(`lemma_I_5_26_signed_ode`, `tendsto_div_of_signed_weighted_ode`), `increment_integrating_factor`
unless `PercLib/Analysis/DrivenODE.lean` has it, and the source's example
`lemma_I_5_26_example` as a non-vacuity `example`.

Wiki tag 2KB9 is a stronger statement (it does not assume `|f| = O(h)`): do not tag. If you can
prove the statement without `hO`, do so in a separate theorem and say so.

## Owned files
- New `PercLib/Analysis/SignedDrivenODE.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Analysis/DrivenODE.lean`, `PercLib/Analysis/MomentHierarchy.lean`,
  `PercLib/Analysis/RegularVariation/*`.
- The source file above (read as text); arXiv:2508.18807v1, §I.5.

## Stop condition
The listed statements are ported and the module builds with `--wfail`; or a statement is false
or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: public theorems with signatures and source names; statement changes;
searches; build result.
