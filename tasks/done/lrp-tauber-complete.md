---
id: lrp-tauber-complete
title: Theorem I.2.11, the Laplace-tail Tauberian equivalence (port, completion)
difficulty: hard
kind: proof-only
labels: []
---

# Theorem I.2.11, the Laplace-tail Tauberian equivalence (port, completion)

## Goal
Complete the formalisation of Theorem I.2.11 of arXiv:2508.18807v1 (Feller XIII.5.2): for a
probability measure on `[0, ∞)`, a regularly varying Laplace defect is equivalent to a
regularly varying tail. The Abelian direction, the endpoint bridges and the first half of the
converse are already in `PercLib/Analysis/Tauberian/{Laplace,Endpoints,Converse}.lean`; this
task proves the converse and assembles the equivalence. Follow "Rules for port tasks" in
`tasks/README.md`.

## Target
Source files (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`, under
`PercLib/CriticalLRP/Analysis/`): `TauberianConverseComplete.lean`, `TauberianPointwise.lean`.

Main statement: let `μ` be a probability measure on `ℝ` with `μ(−∞, 0) = 0`, `0 ≤ α < 1`, and
`f` measurable and regularly varying of index `−α`. Then, as `h ↓ 0` and `x → ∞`,
`E_μ[1 − e^{−hX}] / f(1/h) → 1`  if and only if  `μ([x, ∞)) / (f(x)/Γ(1−α)) → 1`.
Sketch:
```lean
theorem tendsto_laplace_div_iff_tendsto_tail_div (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) {f : ℝ → ℝ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hf : RegularlyVarying (-α) f) (hfm : Measurable f) :
    Tendsto (fun h => (∫ s, (1 - Real.exp (-(h * s))) ∂μ) / f (1 / h)) (𝓝[>] 0) (𝓝 1) ↔
      Tendsto (fun x => (μ (Set.Ici x)).toReal / (f x / Real.Gamma (1 - α))) atTop (𝓝 1)
```
plus the exact power-law corollary (`f x = x^{-α}`), the converse in kernel form
(source `tendsto_tail_of_laplace`, `tendsto_Phi_one`), the identification of the limit profile
with `u ↦ u^{-α}` (source `limitProfile_eq_rpow_ae`, `exists_limitProfile_eq_rpow_and_tendsto_one`
and the pointwise versions of `TauberianPointwise.lean`), and the non-vacuity examples.
Discharge the converse hypothesis of
`laplace_asymptotic_iff_tail_ge_of_strict_converse` (`Tauberian/Endpoints.lean`) rather than
re-proving the forward direction. The limit profile and profile bound are written out as in
`Tauberian/Converse.lean` (no new `def`).

**Overlap.** `PercLib/Probability/GhostTransform.lean` (`tail_asymp_iff_ghost_asymp`) proves the
integer-valued case up to constants; do not duplicate it, and say in the pull request how the
two relate. Candidate wiki tag SLGY (Karamata's Laplace-tail equivalence): do not tag; say
whether the statement matches.

## Owned files
- New `PercLib/Analysis/Tauberian/Complete.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Analysis/Tauberian/{Laplace,Endpoints,Converse}.lean`,
  `PercLib/Analysis/LaplaceUniqueness.lean`, `PercLib/Analysis/RegularVariation/*`,
  `PercLib/Probability/GhostTransform.lean`.
- The two source files above (read as text); arXiv:2508.18807v1, Theorem I.2.11; W. Feller,
  *An Introduction to Probability Theory and Its Applications*, Vol. II, XIII.5.

## Stop condition
The equivalence and the listed supporting statements compile with `--wfail`; or a statement is
false or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: public theorems with signatures and source names; statement changes;
the relation to `GhostTransform`; candidate-tag comparison; searches; build result.
