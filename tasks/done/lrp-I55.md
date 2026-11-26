---
id: lrp-I55
title: Lemma I.5.5, driven ODE with equal exponents and logarithmic corrections (port)
difficulty: medium
kind: proof-only
labels: []
---

# Lemma I.5.5, driven ODE with equal exponents and logarithmic corrections (port)

## Goal
Port Lemma I.5.5 of arXiv:2508.18807v1 in full (the strict case `b < a` is already in
`PercLib/Analysis/DrivenODE.lean`), together with the critical logarithmic estimates used for
the equal-exponent case. Follow "Rules for port tasks" in `tasks/README.md`.

## Target
Source files (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`, under
`PercLib/CriticalLRP/Analysis/`): `Lemma_I_5_5.lean`, `CriticalLog.lean`,
`AENormalizedIncrement.lean`.

Main statement (source `lemma_I_5_5`): let `a, b > 0`, `h` measurable, regularly varying of
index `b` and positive on `(0, ∞)`, `f` positive and differentiable on `(0, ∞)` with
`f'(r) / ((a f(r) + h(r)) / r) → 1` as `r → ∞`. Then `f` is regularly varying of index
`max a b`, and if `b ≤ a` also `h/f → 0` and `f'(r) / (a f(r)/r) → 1`.
In PercLib's notation (sketch):
```lean
theorem regularlyVarying_max_of_tendsto_deriv_ratio {f f' h : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hh : RegularlyVarying b h) (hhm : Measurable h)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hderiv : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hasym : Tendsto (fun r => f' r / ((a * f r + h r) / r)) atTop (𝓝 1)) :
    RegularlyVarying (max a b) f ∧ (b ≤ a →
      Tendsto (fun r => h r / f r) atTop (𝓝 0) ∧
      Tendsto (fun r => f' r / (a * f r / r)) atTop (𝓝 1))
```
(the name is a suggestion; a hypothesis already implied by `RegularlyVarying` may be dropped,
and the pull request says so). Also port `lemma_I_5_5_of_eq` (the equal-index case), the
critical-window lemmas of `Lemma_I_5_5.lean`, the logarithmic-integrability lemmas of
`CriticalLog.lean` (`not_logarithmicallyIntegrable_of_tendsto_pos`,
`tendsto_intervalIntegral_div_mul_log`, …; the source's `LogarithmicallyIntegrable` is written
out inline) and `normalized_increment_of_driving_ode_ac`.

**Overlap.** `PercLib/Analysis/DrivenODE.lean` already has the strict case
(`regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt`) and a normalized-increment
identity (`normalized_increment_of_driving_ode`); `PercLib/Analysis/LinearODEAsymptotics.lean`
has three-regime linear ODE asymptotics. Reuse them; port only what is missing. Candidate wiki
tag GAF9 (partial): do not tag.

## Owned files
- New `PercLib/Analysis/CriticalDrivenODE.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Analysis/DrivenODE.lean`, `LinearODEAsymptotics.lean`, `LogExponent.lean`,
  `PercLib/Analysis/RegularVariation/*`.
- The three source files above (read as text); arXiv:2508.18807v1, §I.5.

## Stop condition
Lemma I.5.5 (all cases) and the listed supporting lemmas are ported and the module builds with
`--wfail`; or a statement is false or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: public theorems with signatures and source names; statement changes;
which source lemmas were replaced by existing PercLib lemmas; searches; build result.
