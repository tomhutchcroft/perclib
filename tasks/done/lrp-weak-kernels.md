---
id: lrp-weak-kernels
title: Weak convergence of size-biased laws and Laplace-kernel limits (port)
difficulty: medium
kind: proof-only
labels: []
---

# Weak convergence of size-biased laws and Laplace-kernel limits (port)

## Goal
Port the lemmas that turn weak convergence of size-biased laws into convergence of the Laplace
and exponential kernel integrals used in the volume-tail argument of arXiv:2508.18807v1
(§I.3), deriving two hypotheses that `PercLib/Analysis/VolumeTail/SizeBiasMGF.lean` currently
takes. Follow "Rules for port tasks" in `tasks/README.md`.

## Target
Source file (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`):
`PercLib/CriticalLRP/Analysis/WeakKernels.lean`.

Port its theorems with the source's own size-biased law replaced by PercLib's
`withDensity` form (`PercLib/Probability/SizeBias.lean`), in particular:
- for probability measures `Q_r ⇒ Q_∞` on `ℝ` carried by `[0, ∞)` with `Q_∞{0} = 0`, the
  convergence of `∫ k_λ dQ_r` to `∫ k_λ dQ_∞` for the Laplace kernel at every fixed rate
  `λ > 0` and along converging rates (source `tendsto_integral_kern`,
  `tendsto_integral_kern_of_tendsto_rate`, `tendsto_integral_kern_comp`,
  `tendsto_integral_kern_sizeBiasedLaw(_of_tendsto_rate)`);
- for every `c > 0`, the convergence of `∫ e^{−c|y|} dQ_r` (no support or atom hypothesis),
  and its moving-rate form (source `tendsto_integral_exp_abs(_atTop)`,
  `tendsto_integral_exp_abs_sizeBiasedLaw(_of_tendsto_rate)`);
- the Laplace transform bounds and continuity (`abs_laplace_le_one`, `continuousOn_laplace`,
  `abs_layerCake_sub_le`), and the counterexamples showing the atom hypothesis is needed
  (`integral_kern_dirac_zero_ne_layerCake`, `kern_not_continuousAt_zero`), as `example`s or
  theorems;
- the chi-square instances (`chiSquare_constant_sequence_moving_rate(_exp)`,
  `chiSquare_exp_abs_atTop`), stated with the chi-square law already in
  `PercLib/Probability/ChiSquare*.lean`.

The source's `laplace`, `clipExp`, `layerCake`, `kern` are written out or replaced by
`laplaceKernel` of `PercLib/Probability/SizeBiasLimits.lean`; check mathlib for a Laplace
transform first. If one is genuinely needed as a definition, stop and propose it in an issue.

**Overlap.** `PercLib/Probability/SizeBiasLimits.lean` already proves weak-convergence results
for the Laplace kernel (wiki tag 7W00) and bounded-continuous sandwiches; reuse them. Candidate
wiki tags 0N85, 7W00: do not tag.

## Owned files
- New `PercLib/Probability/WeakKernels.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Probability/{SizeBias,SizeBiasLimits,ChiSquareMoments,ChiSquareLimit,ChiSquareDeterminacy}.lean`,
  `PercLib/Analysis/VolumeTail/*`.
- The source file above (read as text); arXiv:2508.18807v1, §I.3.

## Stop condition
The listed statements are ported and the module builds with `--wfail`; or a statement is false
or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: public theorems with signatures and source names; how each source
definition was replaced; which hypotheses of `VolumeTail/SizeBiasMGF.lean` are now derivable;
searches; build result.
