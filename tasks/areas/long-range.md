# Area map: long-range percolation (Part I)

This page maps the formalisation of T. Hutchcroft, *Critical long-range percolation I: High
effective dimension* (arXiv:2508.18807v1, "Part I" below), and of what it uses from Parts II
and III (arXiv:2508.18808v1, arXiv:2508.18809v1), onto the Lean library. It is written from
public material only: the Lean library in [`PercLib/`](../../PercLib/), the wiki in
[`wiki/`](../../wiki/), the decisions in [`docs/DECISIONS.md`](../../docs/DECISIONS.md), the
published papers, and the public repository `yujinhkim/lrp` (branch `critical-lrp-1`, commit
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`, licence Apache-2.0), whose directory
`PercLib/CriticalLRP/` is an outside formalisation of Part I. Statuses are as of 21 November
2026 (integration branch at `2023c28`; formal statuses from the library manifest built at
`f7bb516`, which has the same tagged statements). The companion document
[`docs/reports/long-range-concordance.md`](../../docs/reports/long-range-concordance.md)
compares the definitions of the two formalisations.

## 1. Scope

The area is the formalisation of Part I, together with the results of Parts II and III that
Part I uses. An outside formalisation of Part I exists, and the library has been porting from
it file by file under decision D-33 (the outside code is read as a source; each ported file
credits it in its header, decision D-6). An arrangement with its author for merging the two
efforts is being agreed. **Until it is settled, the project queues no new ports from the
outside formalisation** and makes no interface change to the definitions listed in section 3.
To ask about the area, or to propose a definition or a change, open an issue with the
repository's "proposal for a definition", "mathematical gap" or "question" template, or say so
in the description of the pull request that needs it.

## 2. Files of the outside formalisation

Every Lean file of `PercLib/CriticalLRP/` (and the root aggregator `PercLib/CriticalLRP.lean`)
at commit `d382e4c`, with its status in this library:

- **ported**: the content is in the perclib file(s) named, whose header credits the source
  file. The commit is the merge on the integration branch that added the perclib file;
  `00c7fb2` is the public snapshot that starts this repository's history (the port predates
  it). Ports adapt rather than copy: the library's notions replace the source's (see the
  concordance), unused hypotheses are dropped, source definitions are usually written out,
  and declarations are renamed. Source lemmas that duplicate mathlib or the library are not
  carried over.
- **partly ported**: what is in and what is not.
- **in flight**: a port in progress. There is none at present.
- **not ported (held)**: a port package was written and is paused until the arrangement is
  settled. **Not ported (not yet packaged)**: no package exists.
- **excluded** under D-33: the file is an aggregator; or it is built on a second model of
  configurations (the source's `BondGraph`, finite `Finset` configurations, its own rooted tree
  type) or on its own definitions over the configuration type, and the library already has its
  own development of the same content on the bond interface; or it belongs to the Lemma I.5.8
  finite-box material or the Lemma I.5.9 weighted tree bound, which need a fresh development
  on the bond interface; or it is a hypothesis package shown inconsistent (the `I58Cross`
  transport package); or it is superseded by a stronger perclib lemma.

"Lines" are the source file's lines.

### Counts

| Directory | Files | ported | partly ported | in flight | not ported (held) | not ported (not yet packaged) | excluded |
|---|---:|---:|---:|---:|---:|---:|---:|
| `PercLib/CriticalLRP.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| top level | 26 | 3 | 1 | 0 | 3 | 0 | 19 |
| `Analysis/` | 57 | 45 | 3 | 0 | 7 | 1 | 1 |
| `BK/` | 23 | 1 | 4 | 0 | 0 | 0 | 18 |
| `Correlation/` | 12 | 5 | 1 | 0 | 0 | 3 | 3 |
| `CountableProduct/` | 32 | 2 | 3 | 0 | 1 | 2 | 24 |
| `LevyAnalysis/` | 15 | 3 | 2 | 0 | 4 | 6 | 0 |
| `MomentProblem/` | 5 | 5 | 0 | 0 | 0 | 0 | 0 |
| `RussoInf/` | 12 | 5 | 0 | 0 | 1 | 1 | 5 |
| `Tightness/` | 37 | 6 | 1 | 0 | 1 | 0 | 29 |
| `TreeExpansion/` | 23 | 0 | 0 | 0 | 0 | 0 | 23 |
| `TreeGraph/` | 6 | 0 | 0 | 0 | 0 | 0 | 6 |
| `VolumeMoments/` | 25 | 9 | 1 | 0 | 0 | 0 | 15 |
| **all** | **274** | **84** | **16** | **0** | **17** | **13** | **144** |

### The root aggregator

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `CriticalLRP.lean` | 45 | excluded | — | aggregator (imports only) |

### `PercLib/CriticalLRP/` (top level)

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Analysis.lean` | 76 | excluded | — | aggregator (imports only) |
| `BK.lean` | 36 | excluded | — | aggregator (imports only) |
| `CountableProduct.lean` | 45 | excluded | — | aggregator (imports only) |
| `CutoffCorner.lean` | 161 | not ported (held) | — | non-differentiability of the cut-off edge probability at the corner `r = N(x − y)` |
| `CutoffRusso.lean` | 127 | not ported (held) | — | finite model; small rewrite onto perclib's Russo formula |
| `CylinderRusso.lean` | 182 | excluded | — | superseded by `Probability/RussoCylinder.lean` |
| `FiniteBernoulli.lean` | 159 | excluded | — | second model (`Configuration E := Finset E`); superseded by `Probability/ProdBernoulli.lean`, `FiniteExpectation.lean` |
| `FiniteGraphCluster.lean` | 272 | excluded | — | second model (finite graph given by endpoint maps); superseded by `Models/FiniteGraph.lean` |
| `FiniteVolume.lean` | 28 | excluded | — | aggregator (imports only) |
| `KernelGeometry.lean` | 312 | partly ported | `Models/LongRange/Defs.lean` (00c7fb2) | in: `cutoffProfile`, the radial and cut-off kernels and the model profile (as `powerLawProfile`) are in `Models/LongRange/Defs.lean`; not: the kernel comparison and summability lemmas (`cutoffKernel_le_radialKernel` and the domination and summability statements): held |
| `LatticeGeometry.lean` | 443 | excluded | — | superseded by `Models/LongRange/PowerLaw.lean` (sup norm, ball counts) |
| `LemmaI41.lean` | 153 | excluded | — | second model (finite `Finset` configurations); superseded by `Probability/Russo.lean`, `CovarianceRusso.lean`, `Percolation/Bond/FiniteVolumeRusso.lean`, `MomentDerivatives.lean`, `IntensityMonotone.lean` |
| `LevyAnalysis.lean` | 35 | excluded | — | aggregator (imports only) |
| `MassTransportI41.lean` | 679 | not ported (held) | — | own `clusterVolR`, `shiftConfig`, `cutoffSymKernel`; to be rewritten onto the bond interface |
| `MomentConvergence.lean` | 842 | ported | `Probability/MomentConvergence.lean` (0542fe8) |  |
| `MomentDeterminacy.lean` | 23 | excluded | — | aggregator (imports only) |
| `MomentExpansion.lean` | 78 | ported | `Probability/MassTransportTuple.lean` (00c7fb2) |  |
| `MonotoneLaw.lean` | 211 | excluded | — | second model (finite `Finset` configurations); superseded by `Probability/Russo.lean`, `CovarianceRusso.lean`, `Percolation/Bond/FiniteVolumeRusso.lean`, `MomentDerivatives.lean`, `IntensityMonotone.lean` |
| `ODE.lean` | 426 | ported | `Analysis/RiccatiComparison.lean` (00c7fb2) |  |
| `RussoFinite.lean` | 280 | excluded | — | second model (finite `Finset` configurations); superseded by `Probability/Russo.lean`, `CovarianceRusso.lean`, `Percolation/Bond/FiniteVolumeRusso.lean`, `MomentDerivatives.lean`, `IntensityMonotone.lean` |
| `RussoInf.lean` | 27 | excluded | — | aggregator (imports only) |
| `RussoSecondOrder.lean` | 513 | excluded | — | second model (finite `Finset` configurations); superseded by `Probability/Russo.lean`, `CovarianceRusso.lean`, `Percolation/Bond/FiniteVolumeRusso.lean`, `MomentDerivatives.lean`, `IntensityMonotone.lean` |
| `Tightness.lean` | 40 | excluded | — | aggregator (imports only) |
| `TreeExpansion.lean` | 31 | excluded | — | aggregator (imports only) |
| `TreeGraph.lean` | 26 | excluded | — | aggregator (imports only) |
| `VolumeMoments.lean` | 42 | excluded | — | aggregator (imports only) |

### `PercLib/CriticalLRP/Analysis/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `A3Limit.lean` | 629 | ported | `Analysis/VolumeTail/A3Limit.lean` (af7698a) |  |
| `AENormalizedIncrement.lean` | 115 | ported | `Analysis/CriticalDrivenODE.lean` (c1f840a) |  |
| `ChiSquareA3.lean` | 604 | ported | `Analysis/VolumeTail/ChiSquareConstants.lean` (326123b) |  |
| `CriticalLog.lean` | 570 | ported | `Analysis/CriticalDrivenODE.lean` (c1f840a) |  |
| `GeneralInverse.lean` | 826 | ported | `Analysis/RegularVariation/Defs.lean` (00c7fb2), `Analysis/RegularVariation/GeneralInverse.lean` (ac699cd) |  |
| `GyrationODE.lean` | 282 | ported | `Analysis/GyrationODE.lean` (00c7fb2) |  |
| `GyrationReduction.lean` | 408 | ported | `Analysis/GyrationReduction.lean` (14f4e8c) |  |
| `I32Endpoint.lean` | 250 | ported | `Analysis/VolumeTail/Endpoint.lean` (af7698a) |  |
| `Karamata.lean` | 330 | ported | `Analysis/RegularVariation/Karamata.lean` (00c7fb2) |  |
| `KaramataDivergence.lean` | 67 | ported | `Analysis/RegularVariation/KaramataPrimitive.lean` (ce9131c) |  |
| `KaramataMain.lean` | 234 | ported | `Analysis/RegularVariation/Karamata.lean` (00c7fb2) |  |
| `KaramataPrimitive.lean` | 559 | ported | `Analysis/RegularVariation/KaramataPrimitive.lean` (ce9131c) |  |
| `KaramataTail.lean` | 238 | ported | `Analysis/RegularVariation/GeneralInverse.lean` (ac699cd) |  |
| `LaplaceUnique.lean` | 471 | ported | `Analysis/LaplaceUniqueness.lean` (84b680e), `Analysis/Tauberian/Endpoints.lean` (40549b0) |  |
| `LatticeBallAsymptotic.lean` | 109 | partly ported | `Models/LongRange/QuantileMoments.lean` (00c7fb2) | in: sup-norm ball counts in `QuantileMoments.lean`; not: the unit-ball-volume asymptotics (part of Lemma I.4.6): not yet packaged |
| `Lemma_I_4_13.lean` | 850 | ported | `Analysis/RegularVariation/LogErrorTransforms.lean` (2916289) |  |
| `Lemma_I_4_21.lean` | 622 | ported | `Analysis/DrivenODE.lean` (7316ae9) |  |
| `Lemma_I_4_22.lean` | 416 | ported | `Analysis/DrivenODE.lean` (7316ae9) |  |
| `Lemma_I_4_23.lean` | 202 | ported | `Combinatorics/DoubleFactorialConvolution.lean` (00c7fb2) |  |
| `Lemma_I_5_26.lean` | 605 | ported | `Analysis/SignedDrivenODE.lean` (c1c4083) |  |
| `Lemma_I_5_5.lean` | 536 | ported | `Analysis/CriticalDrivenODE.lean` (c1f840a) |  |
| `Lemma_I_5_5_lt.lean` | 256 | ported | `Analysis/DrivenODE.lean` (7316ae9) |  |
| `Lemma_I_5_6.lean` | 575 | ported | `Analysis/CriticalLogODE.lean` (14f4e8c) |  |
| `LogPrimitive.lean` | 112 | excluded | — | superseded: `tendsto_karamataPrimitive_tail` (`RegularVariation/KaramataPrimitive.lean`) is stronger |
| `LogScaling.lean` | 263 | ported | `Analysis/RegularVariation/LogScaling.lean` (00c7fb2) |  |
| `MGFAssembly.lean` | 532 | ported | `Analysis/VolumeTail/MGFAssembly.lean` (af7698a) |  |
| `MassTransport.lean` | 88 | ported | `Probability/MassTransportTuple.lean` (00c7fb2) |  |
| `MonotoneRV.lean` | 96 | ported | `Analysis/RegularVariation/Algebra.lean` (00c7fb2) |  |
| `ODE_I_4_5_three.lean` | 222 | ported | `Analysis/RiccatiComparison.lean` (00c7fb2) | same content as `ODE.lean`, which the perclib header cites |
| `PercolationI32.lean` | 235 | not ported (not yet packaged) | — | premises `hD`, `hG` (discharged in perclib) |
| `PotterBounded.lean` | 114 | ported | `Analysis/RegularVariation/UniformConvergence.lean` (00c7fb2) |  |
| `PotterODE.lean` | 493 | ported | `Analysis/RegularVariation/PotterODE.lean` (00c7fb2) |  |
| `PropositionI32.lean` | 97 | not ported (held) | — |  |
| `QuadraticBall.lean` | 175 | not ported (held) | — |  |
| `RVAlgebra.lean` | 182 | ported | `Analysis/RegularVariation/Algebra.lean` (00c7fb2) |  |
| `RVInverseMonotone.lean` | 791 | ported | `Analysis/RegularVariation/LevelInverse.lean` (76e42ab) |  |
| `RVInversePotter.lean` | 245 | ported | `Analysis/RegularVariation/LevelInverse.lean` (76e42ab) |  |
| `RegularVariation.lean` | 474 | ported | `Analysis/RegularVariation/Defs.lean` (00c7fb2), `Analysis/RegularVariation/LogODE.lean` (00c7fb2) |  |
| `SizeBiasedMGF.lean` | 366 | ported | `Analysis/VolumeTail/SizeBiasMGF.lean` (326123b) |  |
| `TauberianConverse.lean` | 677 | ported | `Analysis/Tauberian/Converse.lean` (f230564) |  |
| `TauberianConverseComplete.lean` | 1,096 | ported | `Analysis/Tauberian/Complete.lean` (caa28bc) |  |
| `TauberianEndpoints.lean` | 691 | ported | `Analysis/Tauberian/Endpoints.lean` (40549b0) |  |
| `TauberianLaplace.lean` | 1,222 | ported | `Analysis/Tauberian/Laplace.lean` (53f666a) |  |
| `TauberianPointwise.lean` | 332 | ported | `Analysis/Tauberian/Complete.lean` (caa28bc) |  |
| `UniformConvergence.lean` | 1,040 | ported | `Analysis/RegularVariation/UniformConvergence.lean` (00c7fb2) |  |
| `VolumeLaw.lean` | 178 | not ported (held) | — | uses the source's own ghost and law definitions; to be rewritten onto the bond law |
| `VolumeTail.lean` | 102 | ported | `Analysis/VolumeTail/Normalizer.lean` (af7698a) |  |
| `VolumeTailAllN.lean` | 226 | partly ported | `Models/LongRange/OmittedLayer.lean` (00c7fb2), `Models/LongRange/RootIndependence.lean` (00c7fb2) | in: the premises `hD`, `hG` written out and discharged (`OmittedLayer.lean`, `RootIndependence.lean`); not: the all-`n` form of Proposition I.3.1: not yet packaged |
| `VolumeTailLatticePositivity.lean` | 108 | not ported (held) | — | discharges the premise `hTailPos` for the source's lattice kernel; to be re-proved for `cutoffKernel` |
| `VolumeTailLower.lean` | 191 | ported | `Analysis/VolumeTail/UpToConstants.lean` (326123b) |  |
| `VolumeTailModel.lean` | 143 | not ported (held) | — |  |
| `VolumeTailPercolation.lean` | 77 | not ported (held) | — |  |
| `VolumeTailPositivity.lean` | 248 | not ported (held) | — |  |
| `VolumeTailUpToConstants.lean` | 150 | ported | `Analysis/VolumeTail/UpToConstants.lean` (326123b) |  |
| `VolumeTailUpper.lean` | 485 | partly ported | `Models/LongRange/OmittedLayer.lean` (00c7fb2), `Models/LongRange/RootIndependence.lean` (00c7fb2) | in: the premises `hD`, `hG` written out and discharged (`OmittedLayer.lean`, `RootIndependence.lean`); not: the upper volume-tail theorems (Proposition I.3.1): not yet packaged |
| `WeakBoundedKernels.lean` | 1,054 | ported | `Probability/WeakKernels.lean` (62be6c2) |  |
| `WeakKernels.lean` | 1,013 | ported | `Probability/WeakKernels.lean` (62be6c2) |  |

### `PercLib/CriticalLRP/BK/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Association.lean` | 351 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `BKApprox.lean` | 294 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `BKGeneral.lean` | 1,499 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `Basic.lean` | 572 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `BoolMeasure.lean` | 791 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `BorelReduction.lean` | 159 | partly ported | `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (00c7fb2) | in: statements, in `ClusterCorrelation/Inequalities.lean`; not: the proofs on the source's `BondGraph` model (replaced by new proofs on the bond interface) |
| `Bridge.lean` | 224 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `CanonicalBridge.lean` | 323 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `CanonicalCardinal.lean` | 65 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `ClusterCardinal.lean` | 172 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `Edges.lean` | 621 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `Finite.lean` | 146 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `FunctionalENNReal.lean` | 230 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `FunctionalFromBelow.lean` | 319 | partly ported | `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (00c7fb2) | in: statements, in `ClusterCorrelation/Inequalities.lean`; not: the proofs on the source's `BondGraph` model (replaced) |
| `FunctionalIndicator.lean` | 155 | partly ported | `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (00c7fb2) | in: statements, in `ClusterCorrelation/Inequalities.lean`; not: the proofs on the source's `BondGraph` model (replaced) |
| `FunctionalInterface.lean` | 86 | partly ported | `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (00c7fb2) | in: statements, in `ClusterCorrelation/Inequalities.lean`; not: the proofs on the source's `BondGraph` model (replaced) |
| `Graph.lean` | 413 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `GraphConsequences.lean` | 322 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `InternalWitness.lean` | 268 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `LayerCake.lean` | 282 | ported | `Probability/LayerCakeProduct.lean` (00c7fb2) |  |
| `Lift.lean` | 223 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `TruncatedCard.lean` | 239 | excluded | — | second model (the source's `BondGraph` and `edgeLaw`); superseded by `Probability/CountableBK.lean`, `ProfileBK.lean`, `FKG.lean`, `Harris.lean` and `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (Lemma I.2.1 without `p < 1`) |
| `TwoCopy.lean` | 178 | excluded | — | superseded by `Probability/DeterministicModification.lean` and `ClusterCorrelation/Restoration.lean` |

### `PercLib/CriticalLRP/Correlation/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `CovarianceGapGeneral.lean` | 89 | ported | `Percolation/Bond/ClusterCorrelation/CovarianceGap.lean` (e12b2f6) |  |
| `HgapClusterWeights.lean` | 237 | ported | `Percolation/Bond/ClusterCorrelation/CovarianceGap.lean` (e12b2f6) |  |
| `HgapDisjointConnections.lean` | 246 | ported | `Percolation/Bond/ClusterCorrelation/CovarianceGap.lean` (e12b2f6) |  |
| `Hrest.lean` | 695 | partly ported | `Percolation/Bond/ClusterCorrelation/Defs.lean` (00c7fb2), `Percolation/Bond/ClusterCorrelation/Inequalities.lean` (00c7fb2) | in: statements, in `ClusterCorrelation/Defs.lean` and `Inequalities.lean`; not: the `BondGraph` proofs (Lemma I.2.1 is proved differently) |
| `HvolPermutation.lean` | 248 | excluded | — | superseded by `Models/LongRange/RootIndependence.lean` (`lintegral_encard_cluster_eq_of_translationInvariant`, `…_of_transitive`) |
| `HvolRootIndependence.lean` | 639 | excluded | — | superseded by `Models/LongRange/RootIndependence.lean` (`lintegral_encard_cluster_eq_of_translationInvariant`, `…_of_transitive`) |
| `HvolWeightNotInvariant.lean` | 84 | not ported (not yet packaged) | — | witness: the weight q_u is not translation invariant |
| `PrintedEventFails.lean` | 106 | not ported (not yet packaged) | — | erratum witness: printed proof of Lemma I.4.12 |
| `SelfRestoration.lean` | 246 | not ported (not yet packaged) | — | erratum witness: printed proof of Lemma I.4.12 |
| `SquareWitness.lean` | 103 | ported | `Percolation/Bond/ClusterCorrelation/CovarianceGap.lean` (e12b2f6) |  |
| `TreeGraphCanonical.lean` | 311 | excluded | — | superseded by `ClusterCorrelation/TwoClusterGap.lean` with `treeGraphInequality` |
| `TwoClusterGap.lean` | 417 | ported | `Percolation/Bond/ClusterCorrelation/Defs.lean` (00c7fb2), `Percolation/Bond/ClusterCorrelation/Restoration.lean` (00c7fb2), `Percolation/Bond/ClusterCorrelation/TwoClusterGap.lean` (00c7fb2) |  |

### `PercLib/CriticalLRP/CountableProduct/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Base.lean` | 544 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `ClusterFKG.lean` | 106 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `ClusterFinset.lean` | 186 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `ClusterInfinite.lean` | 119 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `ClusterLevelSets.lean` | 142 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `ClusterWindow.lean` | 201 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `Compatibility.lean` | 135 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `Critical.lean` | 201 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `EdgeTouch.lean` | 134 | ported | `Percolation/Bond/ClusterCorrelation/Restoration.lean` (00c7fb2) |  |
| `FKGProduct.lean` | 1,226 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `GhostCoupling.lean` | 705 | partly ported | `Models/LongRange/OmittedLayer.lean` (00c7fb2) | in: the premise `hD` (`shiftProb`) written out and discharged in `OmittedLayer.lean`; not: the source's ghost coupling itself: superseded by perclib's independent-layer ghost comparison |
| `GhostCutoffCounterexample.lean` | 415 | not ported (not yet packaged) | — | erratum witness: cut-off form of (I.3.5) |
| `GhostExitDecomposition.lean` | 177 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `GhostField.lean` | 436 | partly ported | `Models/LongRange/RootIndependence.lean` (00c7fb2) | in: the premise `hG` (`ghostHits`) written out and discharged in `RootIndependence.lean`; not: the source's ghost field: superseded by perclib's independent-layer ghost comparison |
| `GhostIndependence.lean` | 224 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `GhostMixedBlock.lean` | 530 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `GhostRestoration.lean` | 452 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `GhostShapeSum.lean` | 140 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `LRPTailBounds.lean` | 220 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `LRPTailBridge.lean` | 71 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `LRPTailLevelSets.lean` | 163 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `LastExit.lean` | 141 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `Lattice.lean` | 301 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `Main.lean` | 26 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `Marks.lean` | 303 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `MassTransport.lean` | 165 | not ported (held) | — | own `shiftConfig`/`clusterVol`; to be rewritten onto perclib's transport |
| `RandomRestoration.lean` | 516 | ported | `Percolation/Bond/ClusterCorrelation/Restoration.lean` (00c7fb2) |  |
| `RestorationCompl.lean` | 768 | partly ported | `Percolation/Bond/ClusterCorrelation/Restoration.lean` (00c7fb2) | in: law preservation of the restoration map, re-proved in `ClusterCorrelation/Restoration.lean`; not: the printed complementary map and its counterexample `threeConfig` (erratum witness for the printed proof of Lemma I.4.12): not yet packaged; the perclib header does not cite this file |
| `RestorationDegree.lean` | 371 | not ported (not yet packaged) | — | erratum witness: cut-off/degree form of (I.3.5) |
| `RestorationLaw.lean` | 176 | excluded | — | own ghost model over the configuration type; superseded by `Percolation/Bond/IndependentLayer/{Ghost,Exploration,Conditional,AddedVolume}.lean` |
| `TwoPoint.lean` | 102 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |
| `ZeroOne.lean` | 304 | excluded | — | own definitions over the configuration type (`edgeMeasure`, `clusterVol`, `longRangeMeasure` via uniform marks, `criticalBeta`, `lrKernel`, `shiftConfig`); superseded by the bond interface (`Percolation/Bond/Basic.lean`) and `ZeroOne`, `Ergodic`, `Transport`, `ClusterTails`, `ClusterCorrelation/`, `Probability/Coupling/Monotone.lean`, `Probability/Harris.lean` |

### `PercLib/CriticalLRP/LevyAnalysis/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Dispersion.lean` | 903 | partly ported | `Probability/Dispersion/Defs.lean` (00c7fb2) | in: the Lévy exponent (as `levyExponent`) and the predicate `IsExpTimeStoppedLaw` in `Probability/Dispersion/Defs.lean`; not: existence (`exists_nuDisp`, `exists_laplaceMixture`), the convolution powers and the characteristic-function API: not yet packaged |
| `DispersionGaussian.lean` | 63 | not ported (not yet packaged) | — |  |
| `DispersionMGF.lean` | 1,064 | not ported (not yet packaged) | — |  |
| `GaussianCharFun.lean` | 195 | not ported (not yet packaged) | — |  |
| `GaussianMGF.lean` | 249 | not ported (not yet packaged) | — |  |
| `Homogeneous.lean` | 242 | ported | `Analysis/HomogeneousBallIntegrals.lean` (00c7fb2) |  |
| `LevyCosh.lean` | 324 | not ported (not yet packaged) | — |  |
| `LevyGap.lean` | 275 | not ported (held) | — |  |
| `LevyLocalL1.lean` | 76 | not ported (held) | — |  |
| `LevyMass.lean` | 273 | not ported (held) | — |  |
| `LevyOddPart.lean` | 952 | not ported (not yet packaged) | — |  |
| `LevyScaling.lean` | 237 | not ported (held) | — | records the printed λ^(d−α) factor in (I.5.16) scaling as inconsistent |
| `Measures.lean` | 420 | partly ported | `Probability/Dispersion/Defs.lean` (00c7fb2) | in: the Lévy densities and measures (as `stableLevyMeasure`, `cutoffLevyMeasure`, for a model norm) in `Probability/Dispersion/Defs.lean`; not: the lemmas: held |
| `Radial.lean` | 106 | ported | `Analysis/HomogeneousBallIntegrals.lean` (00c7fb2) |  |
| `Rpow.lean` | 95 | ported | `Analysis/HomogeneousBallIntegrals.lean` (00c7fb2) |  |

### `PercLib/CriticalLRP/MomentProblem/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `ChiSquare.lean` | 322 | ported | `Probability/ChiSquareDeterminacy.lean` (84b680e) |  |
| `ChiSquareTail.lean` | 942 | ported | `Probability/ChiSquareLimit.lean` (d2820a7), `Probability/ChiSquareMoments.lean` (d2820a7) |  |
| `MGF.lean` | 63 | ported | `Probability/MomentDeterminacy.lean` (00c7fb2) |  |
| `Moments.lean` | 467 | ported | `Probability/MomentDeterminacy.lean` (00c7fb2) |  |
| `SizeBiasing.lean` | 143 | ported | `Probability/ChiSquareMoments.lean` (d2820a7) |  |

### `PercLib/CriticalLRP/RussoInf/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Capstone.lean` | 108 | ported | `Models/LongRange/InfiniteVolumeRusso.lean` (00c7fb2) |  |
| `CutoffFlux.lean` | 127 | ported | `Models/LongRange/InfiniteVolumeRusso.lean` (00c7fb2) |  |
| `Degree.lean` | 201 | excluded | — | subsumed by the rewrite in `Models/LongRange/InfiniteVolumeRusso.lean` |
| `DominatedFlux.lean` | 180 | ported | `Analysis/DominatedDerivative.lean` (00c7fb2), `Models/LongRange/InfiniteVolumeRusso.lean` (00c7fb2) |  |
| `Exchange.lean` | 1,099 | ported | `Models/LongRange/InfiniteVolumeRusso.lean` (00c7fb2) |  |
| `FluxBase.lean` | 331 | excluded | — | subsumed by the rewrite in `Models/LongRange/InfiniteVolumeRusso.lean` |
| `FluxMain.lean` | 183 | ported | `Models/LongRange/InfiniteVolumeRusso.lean` (00c7fb2) |  |
| `Geometry.lean` | 143 | excluded | — | subsumed by the rewrite in `Models/LongRange/InfiniteVolumeRusso.lean` |
| `RussoDominated.lean` | 451 | excluded | — | alternative dominator and sharpness-input forms; `Models/LongRange/InfiniteVolumeRusso.lean` proves the cut-off case outright |
| `Sharpness.lean` | 175 | excluded | — | alternative dominator and sharpness-input forms; `Models/LongRange/InfiniteVolumeRusso.lean` proves the cut-off case outright |
| `SpatialDominated.lean` | 944 | not ported (not yet packaged) | — | dominator and sharpness inputs in place of `hunif` |
| `SpatialExchange.lean` | 708 | not ported (held) | — | the forms without the premise `hunif` only |

### `PercLib/CriticalLRP/Tightness/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `BFSParent.lean` | 282 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Canonical.lean` | 203 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `CanonicalPower.lean` | 263 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `ClusterWitness.lean` | 270 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `DiscreteLayerCake.lean` | 249 | ported | `Probability/DiscreteLayerCake.lean` (00c7fb2) |  |
| `DisplaysToTightness.lean` | 563 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `EndpointCounterexample.lean` | 223 | excluded | — | counterexample at the `k = 0` endpoint of the per-scale tightness theorem (arXiv:2008.11197); the perclib statement starts at one iteration |
| `EndpointDomain.lean` | 224 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Exhaustion/Basic.lean` | 79 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Exhaustion/Locality.lean` | 137 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Exhaustion/Passage.lean` | 206 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Exhaustion/Restrict.lean` | 277 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Exhaustion/Window.lean` | 155 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Infinite/BFS.lean` | 266 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Infinite/Canonical.lean` | 165 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Infinite/Pointed.lean` | 411 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Infinite/Power.lean` | 174 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Infinite/RealPower.lean` | 336 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Infinite/Truncated.lean` | 467 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `LemmaI26Averaging.lean` | 817 | ported | `Models/LongRange/QuantileMoments.lean` (00c7fb2) |  |
| `LemmaI26Cutoff.lean` | 89 | not ported (held) | — |  |
| `LongRangePower.lean` | 84 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `MaxCluster.lean` | 140 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `MaxClusterPower.lean` | 221 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `MomentRatio.lean` | 322 | ported | `Percolation/Bond/Tightness/MomentRatio.lean` (00c7fb2) |  |
| `MomentRatioAux.lean` | 138 | ported | `Probability/TailSums.lean` (00c7fb2) |  |
| `PointedPower.lean` | 252 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `RealExponent.lean` | 434 | partly ported | `Percolation/Bond/Tightness/MomentRatio.lean` (00c7fb2) | in: the real-exponent form of Corollary I.2.5 in `Tightness/MomentRatio.lean`; not: window monotonicity and existence of the median scale (replaced by perclib's tightness scale) |
| `RealMomentRatio.lean` | 511 | ported | `Probability/MomentRatioFromTail.lean` (00c7fb2) |  |
| `RealPieces.lean` | 762 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `RealPower.lean` | 286 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `RootSpine.lean` | 460 | excluded | — | superseded by `Combinatorics/TreeSplitting.lean` |
| `TailEstimates.lean` | 172 | ported | `Probability/TailSums.lean` (00c7fb2) |  |
| `TreePieces.lean` | 811 | excluded | — | superseded by `Combinatorics/TreeSplitting.lean` |
| `TreePiecesBridge.lean` | 64 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `TreePiecesExamples.lean` | 138 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |
| `Universal.lean` | 148 | excluded | — | second model (`BondGraph`, finite `edgeLaw`); superseded by `universalTightness` (`Percolation/Bond/Tightness/BKStep.lean`) on the bond interface |

### `PercLib/CriticalLRP/TreeExpansion/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Basic.lean` | 209 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `BranchSplit.lean` | 317 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `Consistency.lean` | 71 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `Count.lean` | 315 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `FiniteWeightedTreeSum.lean` | 205 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported; its `WeightedTreeSum` interface is vacuous for p > 0 |
| `Forest.lean` | 459 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `Insert.lean` | 331 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `LabelledWeights.lean` | 197 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `MarkedLeaf.lean` | 897 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported |
| `Moment.lean` | 102 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `MomentAssembly.lean` | 187 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `Moments.lean` | 247 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `Orbit.lean` | 166 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `PathWeightedTreeSum.lean` | 354 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported |
| `SourceFaithfulConsumer.lean` | 717 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported |
| `SpatialTreeGraph.lean` | 749 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported |
| `ThreePointBridge.lean` | 175 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `TreeGraphInequality.lean` | 317 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `TreeSumRecursion.lean` | 294 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `TreeSumRecursionFull.lean` | 768 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `Weight.lean` | 160 | excluded | — | second model (finite configurations and the source's own rooted tree type `RTree`); the ordinary moment bound is `lintegral_encard_pow_le` (`Percolation/Bond/TreeGraph/Moments.lean`) |
| `WeightSharpness.lean` | 428 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported |
| `WeightedTreeSumTwo.lean` | 245 | excluded | — | Lemma I.5.9 weighted tree bound: finite abelian group, finite configuration model and own tree type; to be rewritten on the bond interface and perclib's `TreeShape`, not ported; its `WeightedTreeSum` interface is vacuous for p > 0 |

### `PercLib/CriticalLRP/TreeGraph/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `ClusterMoments.lean` | 145 | excluded | — | second model (finite `Finset`-edge model, `BKIncreasing` premise); superseded by `Percolation/Bond/TreeGraph/BranchPoint.lean` (three-point tree-graph inequality) and `TreeGraph/Moments.lean` |
| `Connectivity.lean` | 312 | excluded | — | second model (finite `Finset`-edge model, `BKIncreasing` premise); superseded by `Percolation/Bond/TreeGraph/BranchPoint.lean` (three-point tree-graph inequality) and `TreeGraph/Moments.lean` |
| `Extended.lean` | 132 | excluded | — | second model (finite `Finset`-edge model, `BKIncreasing` premise); superseded by `Percolation/Bond/TreeGraph/BranchPoint.lean` (three-point tree-graph inequality) and `TreeGraph/Moments.lean` |
| `Monotone.lean` | 197 | excluded | — | second model (finite `Finset`-edge model, `BKIncreasing` premise); superseded by `Percolation/Bond/TreeGraph/BranchPoint.lean` (three-point tree-graph inequality) and `TreeGraph/Moments.lean` |
| `Spatial.lean` | 214 | excluded | — | second model (finite `Finset`-edge model, `BKIncreasing` premise); superseded by `Percolation/Bond/TreeGraph/BranchPoint.lean` (three-point tree-graph inequality) and `TreeGraph/Moments.lean` |
| `ThreePoint.lean` | 291 | excluded | — | second model (finite `Finset`-edge model, `BKIncreasing` premise); superseded by `Percolation/Bond/TreeGraph/BranchPoint.lean` (three-point tree-graph inequality) and `TreeGraph/Moments.lean` |

### `PercLib/CriticalLRP/VolumeMoments/`

| Source file | Lines | Status | perclib file (merge commit) | Notes |
|---|---:|---|---|---|
| `Bootstrap.lean` | 485 | ported | `Analysis/RiccatiBootstrap.lean` (84b680e) |  |
| `ClusterAlgebra.lean` | 201 | excluded | — | abstract cluster structure; superseded by the binomial identities of `Probability/MassTransportTuple.lean` |
| `Convolution.lean` | 269 | excluded | — | superseded by `Analysis/MomentHierarchy.lean` and `Combinatorics/DoubleFactorialConvolution.lean` |
| `DFactorial.lean` | 77 | ported | `Combinatorics/DoubleFactorialConvolution.lean` (00c7fb2) |  |
| `ErrorTerms.lean` | 138 | ported | `Analysis/FirstMomentBootstrap.lean` (59abb1f) |  |
| `FiniteCutoffModel.lean` | 764 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `FirstMoment/Asymptotic.lean` | 372 | ported | `Analysis/FirstMomentAsymptotic.lean` (1146988) |  |
| `FirstMoment/Bootstrap.lean` | 472 | ported | `Analysis/FirstMomentAsymptotic.lean` (1146988) |  |
| `FirstMoment/LogIntegrability.lean` | 384 | ported | `Analysis/HardyMajorant.lean` (59abb1f) |  |
| `FirstMoment/Main.lean` | 140 | ported | `Analysis/FirstMomentAsymptotic.lean` (1146988) |  |
| `I58Collapse.lean` | 474 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `I58Cross.lean` | 1,122 | excluded | — | transport hypothesis package for Lemma I.5.8, jointly unsatisfiable (shown in `I58Nonvacuity.lean`); D-33 excludes inconsistent hypothesis sets |
| `I58Model.lean` | 92 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `I58Nonvacuity.lean` | 619 | excluded | — | the source's proof that the `I58Cross` package is inconsistent; recorded, not ported |
| `I58Reflect.lean` | 387 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `I58ReflectLaw.lean` | 101 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `I58ReflectWitness.lean` | 207 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `I58Remainder.lean` | 867 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `I58Separation.lean` | 666 | excluded | — | Lemma I.5.8 finite-box material: abstract finite weighted model or finite box model (a second model); the paper's remainder estimates enter as named hypotheses |
| `MomentODE.lean` | 214 | excluded | — | superseded by `Analysis/MomentHierarchy.lean` and `Combinatorics/DoubleFactorialConvolution.lean` |
| `ODELowerComparison.lean` | 123 | ported | `Analysis/RiccatiComparison.lean` (00c7fb2) | same statement as in `ODE.lean`, which the perclib header cites |
| `ODENocont.lean` | 145 | ported | `Analysis/RiccatiComparison.lean` (00c7fb2) | same statement as in `ODE.lean`, which the perclib header cites |
| `QuadraticMerge.lean` | 742 | excluded | — | second model (finite `Finset` configurations); superseded by `Percolation/Bond/SpatialMoments/Derivative.lean` |
| `SpatialMoments.lean` | 101 | partly ported | `Percolation/Bond/SpatialMoments/Defs.lean` (00c7fb2) | in: the notion (perclib's `spatialMoment`, infinite volume, on the bond interface); not: the finite-model derivative (superseded by `SpatialMoments/Derivative.lean`) |
| `SpatialPivot.lean` | 568 | excluded | — | second model (finite `Finset` configurations); superseded by `Percolation/Bond/SpatialMoments/Derivative.lean` |

## 3. The perclib interface the area sits on

**These definitions are frozen pending the joint review.** Until the review with the author of
the outside formalisation, the project makes no interface change to
`PercLib/Models/LongRange/**/Defs.lean`, `PercLib/Analysis/ModelNorm/` or
`PercLib/Probability/Dispersion/Defs.lean` beyond what is already merged; merged changes are
announced in [`docs/INTERFACE_CHANGES.md`](../../docs/INTERFACE_CHANGES.md) (the latest is
the `ModelNorm` structure and the measure-general `connProb`).

**Bond interface** ([`PercLib/Percolation/Bond/Basic.lean`](../../PercLib/Percolation/Bond/Basic.lean),
namespace `PercLib.Percolation.Bond`). One model of configurations for the whole library
(decision D-2):

- `Config V := Set (Sym2 V)`: the set of open unordered pairs of a type `V` of vertices (the
  complete graph on `V`; loops are discarded by `openGraph`);
- `law q := prodBernoulli q` for a profile `q : Sym2 V → unitInterval`
  ([`Probability/ProdBernoulli.lean`](../../PercLib/Probability/ProdBernoulli.lean));
- `openGraph ω`, `conn x y : Set (Config V)`, `cluster ω x : Set V`; cluster volumes are written
  `(cluster ω x).encard` (no separate definition);
- `tau q x y := law q (conn x y)`, `chi q x := ∫⁻ ω, (cluster ω x).encard ∂law q`;
- `connProb μ x y := μ (conn x y)`: the **measure-general connection kernel**, for any measure
  `μ` on configurations, with `connProb_law : connProb (law q) = tau q`. Results that do not use
  independence are stated for `μ`;
- `rowSum a v := ∑' w, if w = v then 0 else a s(v, w)` for an edge weight
  `a : Sym2 V → ℝ≥0∞` (diagonal excluded; for a profile use `unitInterval.toENNReal ∘ q`);
- `IsCut ω k` for a preordered `V`: no open pair joins `a ≤ k` to `b > k`;
- also `localConn`, `localCluster`, `boundaryFlux`.

**Intensities** ([`Percolation/Bond/Intensity/Defs.lean`](../../PercLib/Percolation/Bond/Intensity/Defs.lean)):
`intensityProfile J β e = 1 - exp(-β J e)` for a kernel `J : Sym2 V → ℝ≥0` and `β : ℝ≥0`, so the
long-range law at intensity `β` is `law (intensityProfile J β)`; `rootCriticalIntensity J x` and
`globalCriticalIntensity J`, both in `ℝ≥0∞`.

**Norms** ([`Analysis/ModelNorm/Defs.lean`](../../PercLib/Analysis/ModelNorm/Defs.lean),
namespace `PercLib.Analysis`): `ModelNorm E`, a `Seminorm ℝ E` that vanishes only at `0`, with
`ModelNorm.ofNorm F` (the norm of a normed space), `ModelNorm.comp`, comparison with the ambient
norm in finite dimension (`exists_le_mul_norm`, `exists_pos_mul_norm_le`), and the type synonym
`WithModelNorm N` carrying the normed-space structure of `N` (`toCLE`).

**Kernels and profiles** ([`Models/LongRange/Defs.lean`](../../PercLib/Models/LongRange/Defs.lean),
[`Models/LongRange/CutoffPowerLaw.lean`](../../PercLib/Models/LongRange/CutoffPowerLaw.lean),
namespace `PercLib.Models.LongRange`):

- `radialKernel N K : Sym2 (Fin d → ℤ) → ℝ≥0`, `J(x, y) = K(N(x - y))` (truncated at `0`) for
  `x ≠ y` and `0` on the diagonal, for a seminorm `N` on `ℝ^d` evaluated at integer points
  (Definition I.1.3); lemmas take `N : ModelNorm (Fin d → ℝ)`;
- `cutoffProfile K r s = if s ≤ r then K s - K r else 0` and `cutoffKernel N K r := radialKernel N
  (cutoffProfile K r)` (Definition I.1.5);
- `powerLawProfile c a s = c * s ^ (-a)` (the wiki uses `c = 1/a`, `a = d + α`);
- the tagged power-law statements `CutoffPowerLawFormula` (PVA8), `CutoffPowerLawMonotone`
  (MQNP), `CutoffPowerLawDeficit` (LF50), `CutoffPowerLawDerivative` (6YYS), proved in
  `CutoffPowerLaw.lean` with the general-profile lemmas `tendsto_cutoffKernel`,
  `hasDerivAt_cutoffKernel`, `hasDerivAt_intensityProfile_of_hasDerivAt`.

Model results built on these (proofs, no new definitions): `PowerLaw.lean` (sup norm and ball
counts), `SoftCutoff.lean`, `OmittedLayer.lean` (the omitted layer `J - J_r`, row bounds),
`RootIndependence.lean`, `InfiniteVolumeRusso.lean` (Russo formula along the cut-off family),
`QuantileMoments.lean` (Lemma I.2.6), `FiniteSusceptibility.lean`, `Convolution.lean`,
`FourierSymbol.lean`, `CutPoints.lean`, `OneDimensional.lean`.

**Lévy and dispersion** ([`Probability/Dispersion/Defs.lean`](../../PercLib/Probability/Dispersion/Defs.lean)):
`stableLevyDensity N α`, `cutoffLevyDensity N α l`, `stableLevyMeasure N α`,
`cutoffLevyMeasure N α l` (Lebesgue measure with density, for a seminorm `N` on an inner product
space; (I.5.16)), `levyExponent L u` (lower integral of `1 - cos ⟪x, u⟫`), and the predicate
`IsExpTimeStoppedLaw ψ ν` (a probability measure with characteristic function `(1 + ψ)⁻¹`;
Definition I.5.16).

**Analysis notions** ([`Analysis/RegularVariation/Defs.lean`](../../PercLib/Analysis/RegularVariation/Defs.lean)):
`RegularlyVarying ρ f` and `SlowlyVarying L` (measurable on a tail, eventually positive, ratio
limit), `LogarithmicallyIntegrable`, `IsLogErrorFunction`, and the generalized inverse
`genInv f x₀ y`.

**Other notions the area uses**: `spatialMoment q o w` ([`Percolation/Bond/SpatialMoments/Defs.lean`](../../PercLib/Percolation/Bond/SpatialMoments/Defs.lean));
the tree-shape type `TreeShape k` ([`Percolation/Bond/Multipoint/Defs.lean`](../../PercLib/Percolation/Bond/Multipoint/Defs.lean));
size-biased laws are written with mathlib's `Measure.withDensity`
([`Probability/SizeBias.lean`](../../PercLib/Probability/SizeBias.lean)), without a definition.

## 4. Tagged assertions of the Part I articles

The wiki articles that record Part I as a source (in `wiki/records/<article>.json`) or cite it in
their text, with every assertion's formal status from the manifest: **proved**, **proved
modulo** (a proof that takes a cited `…Input`, listed in
[`docs/CITED_INPUTS.md`](../../docs/CITED_INPUTS.md)), **statement only**, or **unformalised**.
The library has no `…Input` structure at present, so no assertion is proved modulo; conditional
results take ordinary hypotheses and are not counted as proofs of the paper's statements.
"(erratum)" marks an assertion named in a provisional erratum record. The "Part I locator" is
taken from the assertion's text or from the wiki's reading map
[`wiki/sources/long-range-I-2508.18807v1.md`](../../wiki/sources/long-range-I-2508.18807v1.md);
"—" means none is recorded (the assertion may still belong to Part I or come from elsewhere).
Assertions of other articles that the outside formalisation also touches (Lemma I.2.1 in
`harris-inequality` and `countable-reimer`, the tree-graph bound in `tree-graph`, the kernels in
`displacement-kernels`) are not listed.

Several Part I results are formalised without a tagged restatement: Lemma I.4.21
(`regularlyVarying_of_tendsto_deriv_ratio`, `tendsto_div_of_tendsto_deriv_ratio`) and Lemma
I.5.5 (`regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio`) have been checked against the
paper as proved as stated, but no `Tags/` statement carries them yet, so the manifest lists the
corresponding wiki assertion (B5SL for I.4.21) as unformalised. See the concordance, section 2.

#### [cutoff-families](../../wiki/articles/cutoff-families.md)

5 assertions: 4 proved, 1 unformalised. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `PVA8` | definition | Integrated cutoff kernel | proved | Definition I.1.5 |
| `MQNP` | proposition | Monotonicity and limit of the cutoff family | proved | Definition I.1.5 |
| `LF50` | proposition | Difference between integrated and hard cutoff kernels | proved | Definition I.1.5 |
| `6YYS` | proposition | Derivatives of the cutoff kernel and edge probability | proved | Definition I.1.5 |
| `4OFD` | proposition | Finite-edge Russo derivative along the cutoff family | unformalised | Definition I.1.5 (Russo along the cut-off family) |

#### [cutoff-scaling](../../wiki/articles/cutoff-scaling.md)

6 assertions: 6 unformalised. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `QT3F` | theorem | Uniform power-law cutoff bounds determine moment scales | unformalised | — |
| `ADN0` | corollary | Volume scaling identities under cutoff and matching hypotheses | unformalised | — |
| `CAV9` | theorem | Radial two-point cutoff bounds determine susceptibility scaling | unformalised | — |
| `T5JS` | proposition | An integrable cutoff hierarchy transfers moment bounds to the full law | unformalised | — |
| `IK5Y` | proposition | Finite dominating cluster moments imply continuity in the bond parameter | unformalised | — |
| `XANO` | theorem | Critical tails and uniform moment bounds determine the subcritical volume scale | unformalised | — |

#### [regular-variation](../../wiki/articles/regular-variation.md)

4 assertions: 1 proved, 3 unformalised. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `3491` | definition | Slow and regular variation at infinity | proved (erratum) | §I.2.2 (definition) |
| `LTJ1` | proposition | Tail integral for one minus the Laplace transform | unformalised | — |
| `SLGY` | theorem | Karamata's Tauberian theorem for regularly varying tails | unformalised | Theorem I.2.11 |
| `PVM9` | corollary | Exact critical total-progeny tail constant | unformalised | — |

#### [marginal-ode](../../wiki/articles/marginal-ode.md)

11 assertions: 5 proved, 6 unformalised. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `2KB9` | theorem | Regularly varying forcing determines a signed linear asymptotic | unformalised (erratum) | Lemma I.5.26 |
| `B5SL` | theorem | An asymptotic linear equation with dominant regularly varying driving term | unformalised | Lemma I.4.21 |
| `09N5` | theorem | Marginal ODE asymptotic with integrable multiplicative error | unformalised | — |
| `OP8F` | theorem | A marginal deficit gap determines the logarithmic second moment | proved | — |
| `QKHV` | corollary | Power-log cutoff scales give the normalized full volume tail | unformalised (erratum) | Remark I.1.16 (erratum record) |
| `5O1G` | theorem | Double-factorial moment asymptotics from a closed power-law hierarchy | proved | — |
| `OBTO` | theorem | A slowly varying second-moment factor propagates through the hierarchy | proved | — |
| `SR9U` | proposition | Exact unperturbed marginal ODE solution | unformalised | — |
| `63GS` | proposition | A nonintegrable error produces a second logarithmic factor | unformalised | — |
| `DUWG` | proposition | Riccati comparisons without a continuous derivative | proved | — |
| `K58A` | proposition | Exact tail remainder for a perturbed Riccati equation | proved | — |

#### [size-biased-laws](../../wiki/articles/size-biased-laws.md)

29 assertions: 6 proved, 23 unformalised. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `6L9Z` | definition | Size-biased probability law | unformalised | — |
| `0OEW` | theorem | Near-critical finite-progeny size bias converges to a squared normal | unformalised | — |
| `KOY8` | corollary | Near-critical finite-progeny tail and ghost limits at a fixed cutoff scale | unformalised | — |
| `0N85` | theorem | Squared-normal size-biased limit from cutoff moment asymptotics | unformalised | — |
| `7W00` | proposition | Tail and ghost-transform limits under convergent size-biased laws | proved | — |
| `FJWB` | proposition | Ghost comparison from an omitted-edge row bound | proved | — |
| `BEJT` | proposition | Ghost comparison for two independent bond layers | proved | — |
| `C4E9` | proposition | The added layer of a soft power-law cutoff has a small probability row | proved | — |
| `9PSJ` | theorem | Full tail asymptotics from a multiplicative cutoff comparison | unformalised | — |
| `26NT` | theorem | Cutoff moments give the full critical volume-tail equivalent under explicit endpoint assumptions | unformalised | — |
| `SBWK` | theorem | Distant survival size-biases a fixed critical generation | unformalised | — |
| `XCA8` | proposition | Consistency of the size-biased tree restrictions | unformalised | — |
| `RMFH` | theorem | Spine construction of the critical size-biased tree | unformalised | — |
| `SYJ4` | proposition | Total-variation approximation by the spine law below a distant survival horizon | unformalised | — |
| `JNOW` | proposition | Generation and ball means under critical tree size bias | unformalised | — |
| `4AVL` | proposition | Exact future-generation mass conditioned on critical survival | unformalised | — |
| `OBSY` | theorem | Critical population limits under comparable and distant survival conditioning | unformalised | — |
| `XA7C` | proposition | Rescaled cluster measures under volume size bias | unformalised | — |
| `WGQ7` | proposition | Fixed total mass does not prevent spatial escape | proved | — |
| `Y3SX` | theorem | Polynomial tree-moment asymptotics determine the size-biased random-measure limit | unformalised | — |
| `45EB` | proposition | Chi-square mass mixing turns reduced-tree lengths into independent exponentials | unformalised | Corollary I.5.22; Theorem I.5.24; Theorem I.5.24 and Remark I.5.23 |
| `AYPN` | proposition | Ghost bound for the mass gained from an independent layer | proved | (I.5.49)–(I.5.50) |
| `L9YJ` | theorem | A regularly varying volume tail makes omitted cluster mass negligible | unformalised (erratum) | (I.5.49)–(I.5.50) |
| `BB3O` | theorem | Transfer from cutoff laws to a measure finite away from zero mass | unformalised (erratum) | Lemma I.5.33; Proof of Theorems I.1.9 and I.1.17 |
| `DX2Y` | proposition | Undoing volume bias gives the fixed-ratio cutoff measures and their diagrams | unformalised | Lemma I.5.36 |
| `W9BP` | theorem | Local mixed moments and spatial tightness determine the canonical weighted limit | unformalised | Lemma I.5.37 and proof of Lemma I.5.33 |
| `E22E` | theorem | Compactness and escape for conditioned or volume-biased cluster laws | unformalised | — |
| `FM8D` | theorem | Kesten's two planar conditioning limits define the same IIC law | unformalised | — |
| `Q7E9` | theorem | Two-point bounds give a common IIC limit for distant sets and supercritical conditioning | unformalised | — |

#### [spatial-cutoff-moments](../../wiki/articles/spatial-cutoff-moments.md)

28 assertions: 4 proved, 24 unformalised. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `0CUF` | proposition | Strict domination and finite spatial moments for a soft power-law cutoff | unformalised | — |
| `7F5O` | theorem | Quantitative cutoff susceptibility from subcritical finiteness and endpoint divergence | unformalised | — |
| `K3DB` | theorem | All cutoff volume-moment asymptotics under the susceptibility endpoint assumptions | unformalised | — |
| `57RX` | theorem | Projected second-moment derivative for increasing intensity families | unformalised | — |
| `5OBO` | theorem | Cluster-volume moments with a projected spatial weight | unformalised | — |
| `6DOC` | theorem | Spatial derivative error bounded by four-point collisions | unformalised | — |
| `GAF9` | theorem | Three spatial-moment regimes for a linear equation with integrable coefficient error | proved | — |
| `Z11O` | corollary | Spatial second-moment asymptotics from a quantitative cutoff susceptibility equivalent | unformalised | — |
| `MWZ7` | proposition | The bounded-jump displacement resolvent has exponential moments and a density | unformalised (erratum) | (I.5.16); (I.5.16)–(I.5.20), Definition I.5.16; Definition I.5.16 |
| `GFEM` | proposition | Normalized tree integrals are joint moments of independent edge displacements | unformalised | — |
| `57FJ` | proposition | Spatial normalization changes the regular-variation indices | proved (erratum) | §I.5.4, opening normalization |
| `5VYE` | proposition | A Green-kernel tree bound gives factorial compact-test moments | unformalised | (I.1.11); (I.1.11), Lemma I.5.34; Lemma I.5.34 |
| `42PB` | proposition | Rescaled cutoff resolvents converge to the full Green kernel and its tree diagrams | unformalised | Lemma I.5.35; Lemmas I.5.35–I.5.36 |
| `ALO4` | proposition | Cutoff second moments and negligible added mass prevent spatial escape | unformalised | Lemma I.5.32 |
| `VMEJ` | proposition | Volume bias bounds absolute mixed spatial moments by one-point moments | proved | Lemma I.5.27; Proposition I.5.14 and Lemma I.5.27 |
| `1K61` | theorem | Exact mixed-moment derivative keeps the two clusters distinct | unformalised (erratum) | (I.5.35); Lemma I.5.28 |
| `IX97` | theorem | A resolvent identity determines the split recurrence for tree moments | unformalised (erratum) | Proposition I.5.30; Theorem I.5.21 |
| `GY8M` | theorem | A factorized spatial-moment equation has the binary-tree asymptotics | unformalised (erratum) | Lemma I.5.29; Theorem I.5.21 |
| `QLN7` | proposition | A weighted tree bound controls the single-point derivative error at every even degree | unformalised | — |
| `LDR1` | theorem | All cutoff displacement moments converge to the normalized resolvent moments | unformalised | Proposition I.5.14 and Lemma I.5.27 |
| `2VIE` | theorem | Mixed spatial derivatives factorize when the collision scale is negligible | unformalised | Lemma I.5.29 |
| `HBLN` | theorem | The normalized high-dimensional cutoff model has the spatial tree-moment limit | unformalised | Theorem I.5.21 |
| `MWLQ` | proposition | Homogeneous integration over an arbitrary norm ball | proved | — |
| `WKJR` | proposition | BK and symmetry give the even spatial-moment upper hierarchy | unformalised | — |
| `YU52` | theorem | Sharp cutoff susceptibility bounds all spatial moments when alpha is below two | unformalised | — |
| `AR3F` | proposition | A volume-moment input and spatial moments retain the vertex factor | unformalised | Proposition I.4.20 |
| `YHNS` | theorem | The critical mixed spatial derivative has a collision error of relative order V squared | unformalised | Lemma I.5.29 |
| `AL0I` | theorem | Critical cutoff clusters have the general-norm spatial tree-moment limit | unformalised | Corollary I.5.22; Theorem I.5.21 |

#### [universal-tightness](../../wiki/articles/universal-tightness.md)

6 assertions: 6 proved. All are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `GJIW` | definition | Maximum cluster intersection and its quantile scale | proved | — |
| `AU8B` | proposition | Deterministic bounds on the maximum and quantile | proved | — |
| `4724` | theorem | Universal upper and lower tails at the quantile scale | proved | Lemma I.2.3 (from arXiv:2008.11197) |
| `21D4` | theorem | Rooted upper-tail refinement | proved | — |
| `2FN1` | corollary | Uniform moment bound at the quantile scale | proved | Corollary I.2.5 (from arXiv:2008.11197) |
| `AWWZ` | corollary | Expected maximum comparable to the quantile scale | proved | — |

#### [cutoff-hydrodynamics](../../wiki/articles/cutoff-hydrodynamics.md)

53 assertions: 4 proved, 49 unformalised. Most come from Parts II and III; only the 3 tied to a Part I locator are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `121D` | theorem | Ordinary hydrodynamics makes the second-moment error vanish | unformalised | Proposition I.4.15 |
| `RM79` | theorem | The upper hierarchy propagates the critical second-moment scale | unformalised | (I.4.19) |
| `326J` | theorem | Ordinary hydrodynamics gives every critical volume-moment equivalent | unformalised | Proposition I.4.20 |

#### [multipoint-trees](../../wiki/articles/multipoint-trees.md)

45 assertions: 5 proved, 1 statement only, 39 unformalised. Most come from Parts II and III; only the 1 tied to a Part I locator are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `65MV` | theorem | Independent internal stars retain second moments in the tree-graph bound | unformalised | Lemma I.4.16 |

#### [intrinsic-geometry](../../wiki/articles/intrinsic-geometry.md)

30 assertions: 2 proved, 28 unformalised. Most come from Parts II and III; only the 1 tied to a Part I locator are listed.

| Tag | Kind | Title | Formal status | Part I locator |
|---|---|---|---|---|
| `R6CI` | corollary | The source interception error is negligible above and at the upper critical dimension | unformalised | Lemma I.5.27; Proposition I.4.20 |

## Branches taken by Yujin Kim (ruling 24; fork `yujinhkim/perclib`)

His branches are the claims in this area: do not start the same work. Tip and status as last seen by the coordinator.

| Branch | Tip | Status |
|---|---|---|
| `lrp-I41-mt-updated` | `e6cf6fe` | merged into `claude/zen-lovelace-rvlcw2` (via the branch below), 22 Nov 2026; pull request #9 |
| `work/yujin-cutoff-moment-prereqs` | `39f24c2` | merged into `claude/zen-lovelace-rvlcw2` at `4ca13cb` (proof-only, gate passed), 22 Nov 2026; pull request #10 |
