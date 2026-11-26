---
id: lrp-levy-measures
title: Lévy measures of the cut-off stable law and quadratic ball integrals (port)
difficulty: medium
kind: proof-only
labels: []
---

# Lévy measures of the cut-off stable law and quadratic ball integrals (port)

Being done by the project's own agents; do not start it.

## Goal
Port the measure-theoretic lemmas about the stable and cut-off Lévy measures of (I.5.16) in
arXiv:2508.18807v1 §I.5.2, and the quadratic integrals over balls, onto PercLib's existing Lévy
definitions. Follow "Rules for port tasks" in `tasks/README.md`.

## Target
Source files (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`, under
`PercLib/CriticalLRP/`): `LevyAnalysis/Measures.lean`, `LevyAnalysis/LevyGap.lean`,
`LevyAnalysis/LevyMass.lean`, `LevyAnalysis/LevyLocalL1.lean`, `LevyAnalysis/LevyScaling.lean`,
`Analysis/QuadraticBall.lean`.

Port the lemmas of these files (the definitions are already in
`PercLib/Probability/Dispersion/Defs.lean`: `cutoffLevyDensity`, `stableLevyDensity`,
`cutoffLevyMeasure`, `stableLevyMeasure`, `levyExponent`). In particular: measurability and
symmetry of the densities, the moment integrals, the gap between the stable and cut-off
densities and its uniform convergence (`levyDens_gap_tendsto_uniform`), the derivative in the
cut-off (`hasDerivAt_levyRealLam_of_lt/gt`, `lintegral_levyDens_deriv`), the gap masses
(`lintegral_levyDens_gap(_one)`), the local `L¹` estimate
(`lintegral_gap_ball_le`, `tendsto_toReal_lintegral_gap_ball`), the scaling relations
(`map_const_smul_PiInf`, `PiLam_eq_smul_map_PiOne`, …), and the quadratic ball integrals
(`integral_ball_quadratic_hom`, `ballInnerMoment_pos`, `integral_ball_innerMoment_scaling`, …).

**Re-parametrisation.** The source uses the ambient norm `‖x‖` and a Haar-measure parameter;
PercLib's Lévy definitions use a seminorm `N : Seminorm ℝ E` and `volume`. Re-state every lemma
in PercLib's parametrisation. The source's `levyRealInf`, `levyRealLam`, `rieszKernel`,
`ballQuadraticIntegral` are written out inline; if one genuinely cannot be, stop and explain in
the pull request.

**Erratum.** `LevyScaling.lean` records that the factor `λ^{d−α}` printed in the scaling of
(I.5.16) is inconsistent. Keep the corrected statement and report the discrepancy in a
"Mathematical gap" issue, citing the paper's equation.

Candidate wiki tag 42PB (partial): do not tag.

## Owned files
- New `PercLib/Probability/Dispersion/LevyMeasures.lean` and `PercLib/Analysis/QuadraticBall.lean`
  (theorems only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
- `PercLib/Probability/Dispersion/Defs.lean`, `PercLib/Analysis/HomogeneousBallIntegrals.lean`,
  mathlib's Haar measure and `Seminorm` API.
- The six source files above (read as text); arXiv:2508.18807v1, §I.5.2.

## Stop condition
All lemmas ported in PercLib's parametrisation and both modules build with `--wfail`; or a
statement is false or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: public theorems with signatures and source names; how each statement
was re-parametrised; the erratum issue link; searches; build result.
