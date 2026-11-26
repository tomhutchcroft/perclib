---
id: lattice-power-box-mass
title: A pointwise lattice power law gives the box-mass power law
difficulty: hard
kind: interface
labels: []
---

# A pointwise lattice power law gives the box-mass power law

## Goal
Prove and tag wiki assertion **J9YA** (article `two-point-averages`): summing a pointwise power
law `a(x) ≈ |x|^{-d+α}` over the box `‖x‖_∞ ≤ R` gives the box mass `A(R) ≈ R^α`, in three
strengths (two-sided bounds, logarithmic asymptotics, exact asymptotics with the explicit
constant). The statement is pure analysis on `ℤ^d`; it is the summation step behind the
averaged two-point exponents.

## Target
Let `d ≥ 1`, `0 < α < d`, `a : (Fin d → ℤ) → ℝ` with `a ≥ 0`, and
`A(R) = Σ_{‖x‖_∞ ≤ R} a(x)` for real `R ≥ 1`. Write `|x|` for the Euclidean norm of `x` cast to
`EuclideanSpace ℝ (Fin d)`; limits in `x` are along `Filter.cofinite` on `ℤ^d` (all lattice points
tending to infinity, not one ray); limits in `R` are along `atTop`.
1. If `a(x) ≍ |x|^{-d+α}` (`Asymptotics.IsTheta` along `cofinite`), then `A(R) ≍ R^α`.
2. If `log a(x) / log |x| → -d+α` along `cofinite` (with `a(x) > 0` eventually), then
   `log A(R) / log R → α`.
3. If `a(x) ~ c |x|^{-d+α}` with `c > 0` (`Asymptotics.IsEquivalent`), then
   `A(R) ~ c R^α ∫_{[-1,1]^d} |u|^{-d+α} du`, the integral being finite since `α > 0`.

Sketch of the third part (spelling free):
```lean
theorem isEquivalent_boxSum_of_isEquivalent {d : ℕ} (hd : 1 ≤ d) {α c : ℝ} (hα : 0 < α)
    (hαd : α < d) (hc : 0 < c) (a : (Fin d → ℤ) → ℝ) (ha : 0 ≤ a)
    (h : (fun x => a x) ~[Filter.cofinite]
      fun x => c * ‖(WithLp.equiv 2 _).symm (fun i => (x i : ℝ))‖ ^ (-(d : ℝ) + α)) :
    (fun R : ℝ => ∑ x ∈ Finset.Icc (-(⌊R⌋ : ℤ) • 1) ((⌊R⌋ : ℤ) • 1), a x) ~[Filter.atTop]
      fun R => c * R ^ α *
        ∫ u in Set.Icc (-1 : Fin d → ℝ) 1, ‖(WithLp.equiv 2 _).symm u‖ ^ (-(d : ℝ) + α)
```
(any spelling of the box `{x | ‖x‖_∞ ≤ R}` as a `Finset` is fine, e.g. `Finset.Icc` in the
product order with `⌊R⌋`; state a bridging lemma if you use another). The tagged statement is
the conjunction of the three implications; each is a named lemma in the area file. Route for 3:
a Riemann-sum comparison on the shell `ε R ≤ ‖x‖_∞ ≤ R`, plus the bound of 1 for the inner ball
`‖x‖_∞ ≤ ε R` (which contributes `O((εR)^α)`). Search mathlib and `PercLib/Analysis/` for
lattice-point / Riemann-sum counting lemmas before writing one.

## Owned files
- New `PercLib/Analysis/LatticePowerSums.lean` (area lemmas).
- New `PercLib/Analysis/Tags/LatticePowerSums.lean` (the tagged statement only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
Mathlib (`Asymptotics`, `MeasureTheory.integral`, `Finset.Icc` on `Fin d → ℤ`), `PercLib/Analysis/`;
wiki assertion J9YA. Parts 1 and 2 may be submitted as a first pull request with part 3 left
open, if the tag is added only once all three are proved.

## Stop condition
J9YA tagged, built with `--wfail`; or one of the implications is found false as written
(report the counterexample).

## Hand-off
Pull request description: the tagged statement in full, the lemmas it restates, what was
searched, build result.
