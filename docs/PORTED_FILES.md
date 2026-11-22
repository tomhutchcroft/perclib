# Files adapted from outside work

This file lists every Lean file under `PercLib/` that is adapted from outside work: code,
definitions, statements or a proof argument taken from another formalisation. For each file
it records the source repository, the source path(s), the source revision and the licence
as the file header states them. Decision D-6 (`docs/DECISIONS.md`) requires each such file
to credit its source in its own header. The last column says whether the header credit is
**complete** (repository, path, revision and licence all stated), **partial** (with what is
missing) or **absent**. A file that only cites outside work and copies nothing from it is
listed separately at the end. The headers themselves are the authoritative credit; this
list is an index of them.

Checked against the integration branch on 21 November 2026. Every file under `PercLib/`
was checked: the leading comment blocks of all 372 files, a search for the source
repositories and revisions anywhere in the files, and the first commit of each file.
Updated the same day: the seven partial headers were completed (now marked "complete,
fixed 21 November 2026") and `third_party/critical-lrp/` was added.

## Summary

| Source | Files | Complete | Partial | Absent |
|---|---:|---:|---:|---:|
| `github.com/yujinhkim/lrp` (long-range formalisation) | 62 | 62 | 0 | 0 |
| `github.com/tomhutchcroft/near-critical-diffusivity` | 14 | 14 | 0 | 0 |
| `github.com/anthropics/formal-math` (`percolation/`, PercolationContinuity) | 3 | 3 | 0 | 0 |
| `github.com/nitromannitol/percolation-after-anthropic` | 2 | 2 | 0 | 0 |
| **Total** | **81** | **81** | **0** | **0** |

## 1. `github.com/yujinhkim/lrp` (the formalisation of *Critical long-range percolation I*)

Contributor: yujinhkim. Branch `critical-lrp-1`, revision
`d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`. Licence: Apache-2.0, as declared in the source
file headers and in the source repository's `third_party/critical-lrp/NOTICE.md`. perclib
redistributes the licence text and that notice (passages not about the adapted Lean sources
omitted) in `third_party/critical-lrp/` (`LICENSE`, `NOTICE.md`, `README.md`, and
`OPENAI_MATH_LICENSE.txt`, which the notice names), so the headers' pointer to
`third_party/critical-lrp/NOTICE.md` also resolves in perclib. The headers
also name the upstream origin `github.com/yujinhkim/Critical-Long-range-percolation` at
revision `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Every header in this section gives that
branch, revision, licence and upstream origin; source paths below are relative to
`PercLib/CriticalLRP/` in the source repository.

What was taken: **code**, code adapted (statements and proofs, modified as the header
records); **defs**, definitions adapted, the rest new; **stmts**, statements taken, proofs
new; **arg**, the argument or premise read from the source and written out on the bond
interface, no code copied.

| perclib file | Source path(s) | Taken | Header credit |
|---|---|---|---|
| `Analysis/CriticalDrivenODE.lean` | `Analysis/Lemma_I_5_5.lean`, `Analysis/CriticalLog.lean`, `Analysis/AENormalizedIncrement.lean` | code | complete |
| `Analysis/CriticalLogODE.lean` | `Analysis/Lemma_I_5_6.lean` (the header also names `Analysis/LogPrimitive.lean`, not ported) | code | complete |
| `Analysis/DominatedDerivative.lean` | `RussoInf/DominatedFlux.lean` | code | complete |
| `Analysis/DrivenODE.lean` | `Analysis/Lemma_I_4_21.lean`, `Analysis/Lemma_I_4_22.lean`, `Analysis/Lemma_I_5_5_lt.lean` | code | complete |
| `Analysis/FirstMomentAsymptotic.lean` | `VolumeMoments/FirstMoment/Asymptotic.lean`, `VolumeMoments/FirstMoment/Bootstrap.lean`, `VolumeMoments/FirstMoment/Main.lean` | code | complete |
| `Analysis/FirstMomentBootstrap.lean` | `VolumeMoments/ErrorTerms.lean` | code | complete |
| `Analysis/GyrationODE.lean` | `Analysis/GyrationODE.lean` | code | complete |
| `Analysis/GyrationReduction.lean` | `Analysis/GyrationReduction.lean` | code | complete |
| `Analysis/HardyMajorant.lean` | `VolumeMoments/FirstMoment/LogIntegrability.lean` | code | complete |
| `Analysis/HomogeneousBallIntegrals.lean` | `LevyAnalysis/Radial.lean`, `LevyAnalysis/Rpow.lean`, `LevyAnalysis/Homogeneous.lean` | code | complete |
| `Analysis/LaplaceUniqueness.lean` | `Analysis/LaplaceUnique.lean` | code | complete |
| `Analysis/RegularVariation/Algebra.lean` | `Analysis/RVAlgebra.lean`, `Analysis/MonotoneRV.lean` | code | complete |
| `Analysis/RegularVariation/Defs.lean` | `Analysis/RegularVariation.lean`, `Analysis/GeneralInverse.lean` (definitions `LogarithmicallyIntegrable`, `IsLogErrorFunction`, `genInv`) | defs | complete, fixed 21 November 2026 (branch, revision, source paths and upstream origin added to the header; previously only in the section comment) |
| `Analysis/RegularVariation/GeneralInverse.lean` | `Analysis/GeneralInverse.lean`, `Analysis/KaramataTail.lean` | code | complete |
| `Analysis/RegularVariation/Karamata.lean` | `Analysis/Karamata.lean`, `Analysis/KaramataMain.lean` | code | complete |
| `Analysis/RegularVariation/KaramataPrimitive.lean` | `Analysis/KaramataPrimitive.lean`, `Analysis/KaramataDivergence.lean` | code | complete |
| `Analysis/RegularVariation/LevelInverse.lean` | `Analysis/RVInverseMonotone.lean`, `Analysis/RVInversePotter.lean` | code | complete |
| `Analysis/RegularVariation/LogErrorTransforms.lean` | `Analysis/Lemma_I_4_13.lean` | code | complete |
| `Analysis/RegularVariation/LogODE.lean` | `Analysis/RegularVariation.lean` | code | complete |
| `Analysis/RegularVariation/LogScaling.lean` | `Analysis/LogScaling.lean` | code | complete |
| `Analysis/RegularVariation/PotterODE.lean` | `Analysis/PotterODE.lean` | code | complete |
| `Analysis/RegularVariation/UniformConvergence.lean` | `Analysis/UniformConvergence.lean`, `Analysis/PotterBounded.lean` | code | complete, fixed 21 November 2026 (the header now credits the "Part 2" statements of `Analysis/UniformConvergence.lean` and `Analysis/PotterBounded.lean`) |
| `Analysis/RiccatiBootstrap.lean` | `VolumeMoments/Bootstrap.lean` | code | complete |
| `Analysis/RiccatiComparison.lean` | `ODE.lean` | code | complete |
| `Analysis/SignedDrivenODE.lean` | `Analysis/Lemma_I_5_26.lean` | code | complete |
| `Analysis/Tauberian/Complete.lean` | `Analysis/TauberianConverseComplete.lean`, `Analysis/TauberianPointwise.lean` | code | complete |
| `Analysis/Tauberian/Converse.lean` | `Analysis/TauberianConverse.lean` | code | complete |
| `Analysis/Tauberian/Endpoints.lean` | `Analysis/TauberianEndpoints.lean`, `Analysis/LaplaceUnique.lean` | code | complete |
| `Analysis/Tauberian/Laplace.lean` | `Analysis/TauberianLaplace.lean` | code | complete |
| `Analysis/VolumeTail/A3Limit.lean` | `Analysis/A3Limit.lean` | code | complete |
| `Analysis/VolumeTail/ChiSquareConstants.lean` | `Analysis/ChiSquareA3.lean` | code | complete |
| `Analysis/VolumeTail/Endpoint.lean` | `Analysis/I32Endpoint.lean` | code | complete |
| `Analysis/VolumeTail/MGFAssembly.lean` | `Analysis/MGFAssembly.lean` | code | complete |
| `Analysis/VolumeTail/Normalizer.lean` | `Analysis/VolumeTail.lean` | code | complete |
| `Analysis/VolumeTail/SizeBiasMGF.lean` | `Analysis/SizeBiasedMGF.lean` | code | complete |
| `Analysis/VolumeTail/UpToConstants.lean` | `Analysis/VolumeTailUpToConstants.lean`, `Analysis/VolumeTailLower.lean` | code | complete |
| `Combinatorics/DoubleFactorialConvolution.lean` | `Analysis/Lemma_I_4_23.lean`, `VolumeMoments/DFactorial.lean` | code | complete |
| `Models/LongRange/Defs.lean` | `KernelGeometry.lean` | defs | complete |
| `Models/LongRange/InfiniteVolumeRusso.lean` | `RussoInf/DominatedFlux.lean`, `RussoInf/Exchange.lean`, `RussoInf/FluxMain.lean`, `RussoInf/CutoffFlux.lean`, `RussoInf/Capstone.lean` | arg | complete |
| `Models/LongRange/OmittedLayer.lean` | `Analysis/VolumeTailAllN.lean`, `Analysis/VolumeTailUpper.lean`, `CountableProduct/GhostCoupling.lean` | arg | complete |
| `Models/LongRange/QuantileMoments.lean` | `Tightness/LemmaI26Averaging.lean`, `Analysis/LatticeBallAsymptotic.lean` | code | complete |
| `Models/LongRange/RootIndependence.lean` | `Analysis/VolumeTailAllN.lean`, `Analysis/VolumeTailUpper.lean`, `CountableProduct/GhostField.lean` | arg | complete |
| `Percolation/Bond/ClusterCorrelation/CovarianceGap.lean` | `Correlation/HgapDisjointConnections.lean`, `Correlation/CovarianceGapGeneral.lean`, `Correlation/HgapClusterWeights.lean`, `Correlation/SquareWitness.lean` | code | complete |
| `Percolation/Bond/ClusterCorrelation/Defs.lean` | `Correlation/TwoClusterGap.lean`, `Correlation/Hrest.lean` | defs | complete |
| `Percolation/Bond/ClusterCorrelation/Inequalities.lean` | `BK/FunctionalIndicator.lean`, `BK/FunctionalFromBelow.lean`, `BK/FunctionalInterface.lean`, `BK/BorelReduction.lean`, `Correlation/Hrest.lean` | stmts | complete |
| `Percolation/Bond/ClusterCorrelation/Restoration.lean` | `CountableProduct/RandomRestoration.lean`, `CountableProduct/EdgeTouch.lean`, `Correlation/TwoClusterGap.lean` | stmts | complete |
| `Percolation/Bond/ClusterCorrelation/TwoClusterGap.lean` | `Correlation/TwoClusterGap.lean` | arg | complete |
| `Percolation/Bond/SpatialMoments/Defs.lean` | `VolumeMoments/SpatialMoments.lean` (the notion `spatialMoment`) | arg | complete |
| `Percolation/Bond/Tightness/MomentRatio.lean` | `Tightness/MomentRatio.lean`, `Tightness/RealExponent.lean` | code | complete |
| `Probability/ChiSquareDeterminacy.lean` | `MomentProblem/ChiSquare.lean` | code | complete |
| `Probability/ChiSquareLimit.lean` | `MomentProblem/ChiSquareTail.lean` | code | complete |
| `Probability/ChiSquareMoments.lean` | `MomentProblem/SizeBiasing.lean`, `MomentProblem/ChiSquareTail.lean` | code | complete |
| `Probability/DiscreteLayerCake.lean` | `Tightness/DiscreteLayerCake.lean` | code | complete |
| `Probability/Dispersion/Defs.lean` | `LevyAnalysis/Measures.lean`, `LevyAnalysis/Dispersion.lean` | defs | complete |
| `Probability/LayerCakeProduct.lean` | `BK/LayerCake.lean` | code | complete |
| `Probability/MassTransportTuple.lean` | `Analysis/MassTransport.lean`, `MomentExpansion.lean` | code | complete |
| `Probability/MomentConvergence.lean` | `MomentConvergence.lean` | code | complete |
| `Probability/MomentDeterminacy.lean` | `MomentProblem/MGF.lean`, `MomentProblem/Moments.lean` | code | complete |
| `Probability/MomentRatioFromTail.lean` | `Tightness/RealMomentRatio.lean` | code | complete |
| `Probability/TailSums.lean` | `Tightness/MomentRatioAux.lean`, `Tightness/TailEstimates.lean` | code | complete |
| `Probability/WeakKernels.lean` | `Analysis/WeakKernels.lean`, `Analysis/WeakBoundedKernels.lean` | code | complete |

All perclib paths in this section are relative to `PercLib/`.

### Bounded high-temperature migration supplement — 22 November 2026

These two files come from the later local source branch
`work/yujinhkim-critical-lrp-orchestration`. Their headers give the complete revision and
Apache-2.0 credit. This supplement records the new tail/intensity landing; it does not re-audit
or renumber the 21 November tables above.

| perclib file | Source path (repository root) | Source revision | Taken | Header credit |
|---|---|---|---|---|
| `Percolation/Bond/HighTemperatureTail.lean` | `PercLib/CriticalLRP/HighTemperatureTail.lean` | `7802b33d22f7516ab155005e8526d0b4264ad855` | code | complete |
| `Percolation/Bond/Exploration/BFS/IntensityMoments.lean` | `PercLib/CriticalLRP/IntensityMoments.lean` | `95248147f2fcfeb9c2666c706089d86ee17887a6` | code | complete |

## 2. `github.com/tomhutchcroft/near-critical-diffusivity`

Revision `c820fea91a7482c1755de0ec94ecb9f59ccfcacc`. Reused with Tom Hutchcroft's
permission (`docs/DECISIONS.md`, D-6 and R-3). The native `NearCritical/` files carry no
licence header, and no upstream licence is asserted for them. The source's
`Percolation/Literature/` tree holds code vendored from the `percolation/` project of
`anthropics/formal-math` (Apache-2.0; licence and notices in `third_party/percolation/`); the
four headers that adapt files from that tree say so. The licence column records what the
header says. Source paths are relative to the root of that repository.

| perclib file | Source path(s) | Taken | Licence as stated | Header credit |
|---|---|---|---|---|
| `Probability/BKEndpoints.lean` | `NearCritical/BKEndpoints.lean` | code | no licence header; permission | complete |
| `Probability/BKLowDensity.lean` | `NearCritical/BK.lean` | code | no licence header; permission | complete |
| `Probability/CountableBK.lean` | `NearCritical/CountableBK.lean`, `NearCritical/ProfileCountableBKStrict.lean`, `NearCritical/CylinderBK.lean` | stmts (Lean text new) | no upstream licence asserted; permission | complete |
| `Probability/CylinderDisjointOccurrence.lean` | `NearCritical/CylinderDisjointOccurrence.lean` | code | no licence header; permission | complete |
| `Probability/DisjointOccurrence.lean` | `NearCritical/DisjointOccurrence.lean`, `NearCritical/BK.lean` (certificate part) | code | no per-file licence header; permission | complete |
| `Probability/FiniteExpectation.lean` | `NearCritical/FiniteExpectation.lean` | code | no licence header; permission | complete |
| `Probability/ProductExpectation.lean` | `NearCritical/ProductExpectation.lean` | code | no licence header; permission | complete |
| `Probability/ProfileBK.lean` | `NearCritical/ProfileBKStrict.lean`, `NearCritical/BKAllParameters.lean` | stmts (Lean text new) | no upstream licence asserted; permission | complete |
| `Probability/Russo.lean` | `NearCritical/Russo.lean` | code | no repository-wide licence; permission | complete |
| `Probability/ProdBernoulliIndependence.lean` | `Percolation/Literature/BernoulliPercolation.lean` | code (generalised) | vendored formal-math tree (Apache-2.0, `third_party/percolation/`) for any vendored part; permission | complete, fixed 21 November 2026 |
| `Probability/FiniteEnergy/Insertion.lean` | `Percolation/Literature/FiniteEnergy.lean` | arg | vendored formal-math tree (Apache-2.0, `third_party/percolation/`) for any vendored part; permission | complete, fixed 21 November 2026 |
| `Percolation/Bond/LocalConnectivity.lean` | `Percolation/Literature/SharpnessDCTProofs.lean` | code (generalised) | vendored formal-math tree (Apache-2.0, `third_party/percolation/`) for any vendored part; permission | complete, fixed 21 November 2026 |
| `Probability/Transport/Reindexing.lean` | `Percolation/Literature/BondPercolationSymmetry.lean` | code (generalised) | vendored formal-math tree (Apache-2.0, `third_party/percolation/`) for any vendored part; permission | complete, fixed 21 November 2026 |
| `Probability/Pivotal/Algebra.lean` | `NearCritical/Russo.lean` (the force/flip/difference method) | arg | no licence header; permission | complete, fixed 21 November 2026 |

## 3. `github.com/anthropics/formal-math`, project `percolation/` (PercolationContinuity)

Copyright 2026 Anthropic, PBC. Revision `795efb86f191735c5481675763537cfb4ff37e55`. Licence:
Apache License 2.0; the licence text and the retained notices are in
`third_party/percolation/LICENSE` and `third_party/percolation/NOTICE`. Source paths are
relative to `percolation/` in that repository.

| perclib file | Source path(s) | Taken | Header credit |
|---|---|---|---|
| `Probability/ProdBernoulli.lean` | `Percolation/Literature/LatticeModels/ProdBernoulli.lean`, `Percolation/Literature/LatticeModels/ProdBernoulliProofs.lean` | code | complete |
| `Probability/Harris.lean` | `Percolation/Literature/HarrisInequality.lean` | code | complete |
| `Probability/Cylinder.lean` | `Percolation/Literature/LatticeModels/ProdBernoulliIndependence.lean` | code | complete |

## 4. `github.com/nitromannitol/percolation-after-anthropic`

Prompted by Ahmed Bou-Rabee. Revision `a5cc72bd7627f313abbb00bcb47616678abbeb35`. Licence:
Apache License 2.0; full attribution in `third_party/percolation/NOTICE`, licence text in
`third_party/percolation/LICENSE`.

| perclib file | Source path(s) | Taken | Header credit |
|---|---|---|---|
| `Models/Site/Basic.lean` | `Hypergraph/SiteStatements.lean`, `PercolationAudit/SiteCriticality/SolutionBasic.lean` | code | complete (the header also records that the `Site`/`zdGraph` vocabulary originates in PercolationContinuity at `795efb86…`, without a path) |
| `Percolation/Bond/Basic.lean` | `Hypergraph/SiteStatements.lean` (lines 308–374 at that revision; five measurability proofs, through `Models/Site/Basic.lean`) | code | complete |

## Files that cite outside work but adapt none of it

These headers name a source only to say that the file is new work built on an adapted
perclib file, or that the source was not used. They need no D-6 credit of their own.

| perclib file | What the header says |
|---|---|
| `Probability/FiniteContinuity.lean` | New consequences of `Probability/ProductExpectation.lean`; copies no upstream proof |
| `Probability/RussoCylinder.lean` | New transport of `Probability/Russo.lean`; no upstream proof copied |
| `Probability/RussoIntegral.lean` | New consequences of `Probability/Russo.lean` |
| `Probability/OpenEventHarris.lean` | Covers the role of three near-critical-diffusivity declarations; the source was not consulted and nothing was copied |
