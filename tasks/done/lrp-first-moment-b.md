---
id: lrp-first-moment-b
title: First-moment asymptotic at criticality (port, second half)
difficulty: hard
kind: proof-only
labels: []
---

# First-moment asymptotic at criticality (port, second half)

## Goal
Port the second half of the first-moment bootstrap of arXiv:2508.18807v1, §I.4: the
asymptotic of the first moment of the cluster volume at criticality and the bound for all
`β`, on top of the first half already in the library (`PercLib/Analysis/FirstMomentBootstrap.lean`,
`PercLib/Analysis/HardyMajorant.lean`). Follow "Rules for port tasks" in `tasks/README.md`.

## Target
Source files (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`, under
`PercLib/CriticalLRP/`):
`VolumeMoments/FirstMoment/Asymptotic.lean`, `VolumeMoments/FirstMoment/Bootstrap.lean`,
`VolumeMoments/FirstMoment/Main.lean`.

Port every public theorem of these files, faithfully modulo the notion changes of the port
rules, in particular:
- `Asymptotic.lean`: `first_moment_lower_bound`, `first_moment_asymptotic`,
  `first_moment_error_logIntegrable`, `tendsto_rpow_mul_integral_Ioi`;
- `Bootstrap.lean`: `bootstrap_perturbed`, `first_moment_bound_all_beta`, and the helper
  inequalities they need (`tree_graph_error_bound`, `error_of_E0_E1`, the threshold lemmas)
  unless the library already has them;
- `Main.lean`: `error_decomp` and `first_moment_asymptotic_at_critical`. The latter is not the
  model statement of the paper: give it a name that says what it proves.

Constants of the source (`oneSubE0`, `cE1`, …) are written out; no new `def`.

**Premises.** The source's bootstrap takes a sharpness input, an a-priori bound and a
left-limit (regularity) input that the paper does not state. Keep each as an explicit
hypothesis and list them in the pull request. Proposition I.4.2 and Lemma I.4.8 of the paper
are therefore **not** proved by this task, and the pull request must not describe them as
proved.

## Owned files
- New `PercLib/Analysis/FirstMomentAsymptotic.lean` (theorems only).
- Its import line in `PercLib.lean`.

## Allowed inputs
- `PercLib/Analysis/FirstMomentBootstrap.lean`, `HardyMajorant.lean`, `RiccatiBootstrap.lean`,
  `RiccatiComparison.lean`, `QuadraticRecursion.lean`, `ReciprocalODE.lean`,
  `PercLib/Analysis/RegularVariation/*`. Check each source helper against these before porting
  it: several are already present under other names.
- The three source files above (read as text).
- arXiv:2508.18807v1, §I.4.

## Stop condition
All public theorems of the three files are ported and `lake build --wfail
PercLib.Analysis.FirstMomentAsymptotic` succeeds; or a source statement is false or vacuous
after translation (report it, port the rest).

## Hand-off
Pull request description: every public theorem with its Lean signature and the source theorem
it ports; every statement change (before/after); the explicit premises the paper does not
state; what was searched in mathlib and PercLib; build result.
