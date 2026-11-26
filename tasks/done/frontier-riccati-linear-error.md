---
id: frontier-riccati-linear-error
title: A linear error preserves subthreshold Riccati propagation (19IN)
difficulty: medium
kind: interface
labels: []
---

# A linear error preserves subthreshold Riccati propagation

Being done by the project's own agents; do not start it.

## Goal
Prove and tag wiki assertion **19IN** (article `mesoscopic-tail-transfer`, anchor
`tag-19IN`). It is on the frontier: no recorded prerequisites.

## Target
Statement sketch (namespace `PercLib.Analysis`; fixes the mathematics, not the spelling):
- binders: `α A e r₀ : ℝ`, `0 < α`, `0 < A`, `0 ≤ e`, `e < α`, `0 < r₀`; `f : ℝ → ℝ` with
  `∀ t, r₀ ≤ t → 0 < f t`, `∀ p q, r₀ ≤ p → p ≤ q → AbsolutelyContinuousOnInterval f p q`, and
  `∀ᵐ t, r₀ ≤ t → deriv f t ≤ A * t ^ (-α - 1) * f t ^ 2 + e * t⁻¹ * f t`;
- for `r ≥ r₀` with `f r ≤ (α - e) * r ^ α / A` and every `R ≥ r`, writing
  `B R = 1 / f r - A / ((α - e) * r ^ α) + A / ((α - e) * r ^ α) * (r / R) ^ (α - e)`:
  `0 < B R ∧ f R ≤ (R / r) ^ e * (B R)⁻¹`;
- for `0 < θ < 1` with `f r ≤ (1 - θ) * (α - e) * r ^ α / A`:
  `∀ R ≥ r, f R ≤ θ⁻¹ * (R / r) ^ e * f r`.

`0 < r₀` is a typing hypothesis: the article's `t⁻¹` and `t^{-α-1}` presuppose `t > 0`.
Area lemmas: the integrated inequality
`R^e / f R ≥ r^e / f r - A/(α - e) (r^{e-α} - R^{e-α})`, the positivity of `B`, the bound and
the `θ` corollary; the tagged statement `@[tag "19IN"]` is their conjunction.

Template: `le_of_deriv_le_mul_sq` in `PercLib/Analysis/ReciprocalODE.lean` does the same
integration for `(1/T)' ≥ -a`; here the function is `t ↦ t^e / f t`. Reuse its absolute
continuity steps; if a helper there is private, prove a general public lemma in your file.

## Owned files
- New `PercLib/Analysis/RiccatiLinearError.lean` (theorems only).
- New `PercLib/Analysis/Tags/RiccatiLinearError.lean` (the tagged statement only; skeleton
  as in `PercLib/Analysis/Tags/MesoscopicTailTransfer.lean`).
- Their import lines in `PercLib.lean`.

## Allowed inputs
`main`, mathlib (`AbsolutelyContinuousOnInterval` API, `integral_rpow`), the article
`wiki/articles/mesoscopic-tail-transfer.md`.

## Stop condition
Area lemmas and the tagged statement compile with `lake build --wfail`; or the statement is
false or needs a hypothesis the article does not state (stop, open a "Mathematical gap"
issue with the counterexample).

## Hand-off
Pull request description: the tagged statement, each binder with the reason it is there,
searches made, build result. A maintainer reviews the statement against the wiki.
