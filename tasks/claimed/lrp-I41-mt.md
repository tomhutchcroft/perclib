---
id: lrp-I41-mt
title: Mass-transport identity of Lemma I.4.1 and the cut-off corner (port)
difficulty: hard
kind: proof-only
labels: []
---

# Mass-transport identity of Lemma I.4.1 and the cut-off corner (port)

Being done by the project's own agents; do not start it.

## Goal
Port the mass-transport identity behind Lemma I.4.1 of arXiv:2508.18807v1 (the Russo-type
derivative of cluster-volume moments for long-range percolation with a cut-off kernel) and the
non-differentiability of the cut-off profile at its corner, rewritten onto PercLib's bond
model. Follow "Rules for port tasks" in `tasks/README.md`.

## Target
Source files (`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c`, under
`PercLib/CriticalLRP/`): `MassTransportI41.lean`, `CountableProduct/MassTransport.lean`,
`Tightness/LemmaI26Cutoff.lean`, `CutoffCorner.lean`, `CutoffRusso.lean`.

1. The mass-transport form of the Russo identity: the source's `massTransport_russo`,
   `i41_massTransport`, `i41_binomial`, `i41_cutoff_massTransport`, `i41_cutoff_binomial`,
   `lintegral_cluster_massTransport`, `lintegral_cluster_ball_massTransport`,
   `lemma_I_2_6_cutoff(_real_integral)`.
2. The corner of the cut-off profile: `hasDerivWithinAt_cutoffProfile_Iic/Ioi`,
   `not_hasDerivAt_cutoffProfile` and the same three for the edge probability
   (`…_cutoffEdgeProbability…`), stated for PercLib's `cutoffProfile`
   (`PercLib/Models/LongRange/Defs.lean`).
3. `CutoffRusso.lean`'s `hasDerivAt_cutoffEdgeProbability_if` and
   `hasDerivAt_expectation_cutoff`, rewritten onto PercLib's Russo formula.

**No second model.** The source's `clusterVolR`, `shiftConfig`, `cutoffSymKernel`
(= PercLib's `cutoffKernel`), `russoLHS`/`russoRHS` and its finite-configuration model are not
ported. Rewrite every statement onto the bond law `law (intensityProfile J β)`, transport by
`Sym2.map`, cluster volume `(cluster ω x).encard`, and `PercLib/Probability/Russo*.lean`. No new
`def`.

Lemma I.4.1 for unbounded observables `|K|^p` is **not** in scope (the library's
`InfiniteVolumeRusso` covers bounded, eventually constant observables): state in the pull
request what is proved and what remains.

Candidate wiki tags 4OFD, GG8B, 09EI: do not tag; say which statement matches which.

## Owned files
- New `PercLib/Models/LongRange/MassTransportI41.lean` and
  `PercLib/Models/LongRange/CutoffCorner.lean` (theorems only).
- Their import lines in `PercLib.lean`.

## Allowed inputs
- `PercLib/Models/LongRange/{Defs,QuantileMoments,InfiniteVolumeRusso}.lean`,
  `PercLib/Probability/MassTransport.lean`, `PercLib/Probability/MassTransportTuple.lean`,
  `PercLib/Probability/Transport/*`, `PercLib/Probability/Russo*.lean`.
- The five source files above (read as text); arXiv:2508.18807v1, §I.2 and §I.4.

## Stop condition
Items 1-3 are ported on the bond model and both modules build with `--wfail`; or a statement
is false or vacuous after translation (report it, port the rest).

## Hand-off
Pull request description: every public theorem with signature and the source theorem it
ports; statement changes; how each second-model notion was replaced; what of Lemma I.4.1
remains; candidate tag matches; searches; build result.
