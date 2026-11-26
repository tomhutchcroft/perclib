---
id: hier-pointwise-ingredients
title: Pointwise sibling and outer-shell bounds for non-radial hierarchical kernels
difficulty: hard
kind: proof-only
labels: []
---

# Pointwise sibling and outer-shell bounds for non-radial hierarchical kernels

Being done by the project's own agents; do not start it.

## Goal
Prove the two pointwise ingredients of two-sided pointwise bounds on the critical two-point
function of long-range percolation on the hierarchical lattice for a translation-invariant
kernel that need not be radial (wiki assertion 7YNX; arXiv:2103.17013v1 proves pointwise
bounds only for radial kernels, by shell averaging). The library has the summed (shell)
versions; this task proves the versions for a single target point.

## Target
Setting and notation as in `PercLib/Models/HierarchicalSibling.lean` and
`PercLib/Models/HierarchicalTranslation.lean`: `V = ℕ →₀ (Fin d → ZMod L)`, `h`, `Λ_m`; `J`
translation invariant; `q_m(β)` = `intensityProfile J β` restricted to pairs inside `Λ_m`;
`a_m(β) = E_{q_m}|K_0 ∩ Λ_m|`; `τ_m(0,x)` the connection probability under `q_m`.

1. **Outer-shell upper bound.** If `J(u,v) ≤ K(h(v−u))` for `u ≠ v` with `K` antitone, then for
   every `x` with `h x = m+1`,
   `τ_{m+1}(0, x) ≤ β K(m+1) a_m(β) a_{m+1}(β)`.
   (First exit from the child block of `0` and BK, as in
   `law_localConn_ball_succ_le_of_translationInvariant`, but with the target in the outer
   shell.) State the precise form the proof gives, including any harmless additive term, and
   prove it.
2. **Pointwise sibling lower bound.** Under the hypotheses of `sum_shell_tau_ge`
   (`c L^{−(d+α)h} ≤ J`, translation invariance, `β > 0`, `M_n(β)² ≤ (A/β) L^{(d+α)n}`), for
   every `x` with `h x = n+1`,
   `k' β L^{−(d+α)(n+1)} a_n(β)² ≤ τ_{n+1}(0, x)`
   with an explicit `k' = k'(d, L, α, c, A) > 0`. The proof of `sum_shell_tau_ge` already
   handles one sibling pair of blocks; extract that step as a lemma (the cross-edge estimate of
   `PercLib/Percolation/Bond/CrossEdge.lean` applied to the clusters of `0` and `x` in their
   own level-`n` blocks) and make `sum_shell_tau_ge`'s structure visible in your proof. Do not
   change `sum_shell_tau_ge` itself.

Both are proof-only lemmas; do **not** tag 7YNX (its two-sided conclusion also needs the
critical bounds of Theorem 1.1, which are not yet proved).

## Owned files
- New `PercLib/Models/HierarchicalPointwise.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Models/HierarchicalSibling.lean`, `HierarchicalTranslation.lean`,
  `HierarchicalTwoPointUpper.lean`, `HierarchicalSymmetry.lean`, `HierarchicalGeometry.lean`,
  `PercLib/Percolation/Bond/CrossEdge.lean`, `PercLib/Probability/ProdBernoulliIndependence.lean`,
  `PercLib/Probability/CountableBK.lean`.
- arXiv:2103.17013v1, Lemma 2.8 and Proposition 2.10; wiki assertion 7YNX (article
  `hierarchical-runaway`).

## Stop condition
Both bounds proved and the module builds with `--wfail`; or one of them is false as stated
(report the counterexample and the corrected form).

## Hand-off
Pull request description: both theorems with full signatures and constants; any statement
adjustment with reasons; searches; build result.
