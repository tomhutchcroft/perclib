# Long-range percolation: concordance of two formalisations

This document sets the core definitions of the outside formalisation of T. Hutchcroft,
*Critical long-range percolation I* (arXiv:2508.18807v1, "Part I"; repository
`yujinhkim/lrp`, branch `critical-lrp-1`, commit `d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc`,
directory `PercLib/CriticalLRP/`, licence Apache-2.0) beside their counterparts in this library.
It is a basis for a joint review of the interface, not a verdict: where the two differ, it
records what each does and what porting a statement from one to the other involves. It also
collects what formalisation in both projects has found about the papers. The file-by-file
status of the outside formalisation, and the library's interface for the area, are in
[`tasks/areas/long-range.md`](../../tasks/areas/long-range.md).

Written from public material only, on 21 November 2026 (integration branch at `2023c28`).
Source paths below are relative to the outside repository's `PercLib/CriticalLRP/`; perclib
paths are relative to this repository's `PercLib/`. The outside code was read as text; nothing
of it was built or run for this document.

**Background.** Both projects state percolation on the same kind of object: the outside
formalisation was started on an early version of this library and reuses its configuration
type and law through abbreviations (`CountableProduct/Base.lean`: `abbrev Config V :=
PercLib.Percolation.Bond.Config V`, `abbrev edgeMeasure π := PercLib.Percolation.Bond.law π`).
The differences are therefore mostly in what is built on top: the kernel and its norm, the
regular-variation notions, how much is bundled into definitions and structures, and a few
auxiliary models used for finite-volume arguments. This library ports under decision D-33 of
[`docs/DECISIONS.md`](../DECISIONS.md): where it already has a notion it uses its own, it
does not add aliases, a second model of configurations is rewritten rather than bridged,
definitions are stated as generally as the paper states them, and a premise the source needed
but the paper does not state stays an explicit hypothesis (the paper's theorem then stays an
unproved target).

## 1. Core definitions

| Notion | Outside formalisation (name, file) | perclib (name, file) | Differences | What a port changes |
|---|---|---|---|---|
| Configurations | `Config V` (`CountableProduct/Base.lean`), an abbreviation of the library's `Config` at the commit it started from, where it was `Sym2 V → Prop` (`config_eq_pi`) | `Config V := Set (Sym2 V)` (`Percolation/Bond/Basic.lean`) | Same object; the library has since changed the carrier from predicates to sets (definitionally equal). | `ω e` becomes `e ∈ ω`; proofs that unfold the predicate form are adjusted. |
| Auxiliary configuration models | `BondGraph V E := E → Sym2 V` with configurations `Set E` and `edgeLaw` (`BK/Graph.lean`); `Configuration E := Finset E` with `configurationLaw`, `expectation`, `probability` (`FiniteBernoulli.lean`); finite graphs given by endpoint maps `s t : E → V` (`FiniteGraphCluster.lean`, `VolumeMoments/SpatialMoments.lean`) | none: finite-volume arguments use `prodBernoulli` on a finite index type (`Probability/ProdBernoulli.lean`, `FiniteExpectation.lean`) and windows of the one bond model | The outside formalisation proves BK, Russo, tree-graph and finite-volume moment results in these models; the library proves the same results on the bond interface (`Probability/CountableBK.lean`, `ProfileBK.lean`, `Russo.lean`, `Percolation/Bond/FiniteVolumeRusso.lean`, `TreeGraph/`, `Tightness/BKStep.lean`). | Under D-33 a result stated in a second model is rewritten onto the bond interface, not bridged; most such files are marked excluded (superseded) in the area map. |
| Law | `edgeMeasure π` (abbreviation of the library's `law π`); `bernoulliEdgeProb J hJ β e = 1 − exp(−β J e)` and `longRangeMeasure J hJ β := edgeMeasure (bernoulliEdgeProb J hJ β)` for `J : Sym2 V → ℝ`, `hJ : ∀ e, 0 ≤ J e` (`CountableProduct/Marks.lean`); a uniform-marks construction `markMeasure`, `atParameter` | `law q := prodBernoulli q` for `q : Sym2 V → unitInterval`; `intensityProfile J β e = 1 − exp(−β J e)` for `J : Sym2 V → ℝ≥0` (`Percolation/Bond/Intensity/Defs.lean`); the long-range law is `law (intensityProfile J β)`; monotone coupling in `Probability/Coupling/Monotone.lean` | Kernel nonnegativity is a separate proof `hJ` in the source and is carried by the type `ℝ≥0` in perclib. The source names the long-range law; perclib composes `law` and `intensityProfile`. Statements that do not use independence are stated in perclib for any measure `μ` on configurations (`connProb μ`). | `longRangeMeasure J hJ β` becomes `law (intensityProfile J' β)` with `J' e = (J e).toNNReal` (equal to `J` under `hJ`); the marks coupling is replaced by perclib's monotone coupling. |
| Connection and clusters | `Connects`, `cluster` (abbreviations onto the library), `PathConnects`, `clusterVol ω v : ℝ≥0∞ := (cluster ω v).encard`, `InInfiniteCluster ω v := clusterVol ω v = ⊤`, `percolationProb`, `infiniteClusterProb` (`CountableProduct/Base.lean`, `Marks.lean`) | `conn x y : Set (Config V)`, `cluster ω x`, `tau q x y`, `connProb μ x y`, `chi q x` (`Percolation/Bond/Basic.lean`); the volume is written `(cluster ω x).encard` and an infinite cluster `(cluster ω x).Infinite` | The source names the volume and the infinite-cluster event; perclib writes them out. | Unfold `clusterVol` to `((cluster ω v).encard : ℝ≥0∞)`, `InInfiniteCluster` to `(cluster ω v).Infinite`. |
| Critical point | `criticalBeta J hJ := sInf {β : ℝ≥0 | infiniteClusterProb J hJ β = 1}` (`CountableProduct/Critical.lean`) | `globalCriticalIntensity J := sInf {β | 0 < P_β(∃ x, K_x infinite)}` and `rootCriticalIntensity J x := sInf {β | 0 < P_β(K_x infinite)}`, both in `ℝ≥0∞` (`Percolation/Bond/Intensity/Defs.lean`); `rootCriticalIntensity_eq_globalCriticalIntensity_of_translationInvariant` (`Models/LongRange/FiniteSusceptibility.lean`) | Event: almost-sure existence (source) against positive probability (perclib); these agree by the zero-one law. Type and empty set: in `ℝ≥0` the infimum of the empty set is `0`, so `criticalBeta = 0` when no intensity percolates; in `ℝ≥0∞` it is `⊤`. | A statement at or below `β_c` names which notion it uses; with perclib's notion, the value `⊤` (no percolation at any finite intensity, e.g. in one dimension with summable crossing intensity) is a case to treat. |
| Kernel | `radialKernel K ρ x y := if x = y then 0 else K (ρ x y)` and `cutoffKernel K ρ r x y := if x = y then 0 else cutoffProfile K r (ρ x y)` for any type `V` with a function `ρ : V → V → ℝ`, real-valued, two-argument (`KernelGeometry.lean`); `lrKernel d α : Sym2 (Fin d → ℤ) → ℝ`, `‖x − y‖^(−(d+α))` with the sup norm of `ℤ^d` (`CountableProduct/Critical.lean`); `cutoffSymKernel` (in `MassTransportI41.lean`) | `radialKernel N K : Sym2 (Fin d → ℤ) → ℝ≥0`, `K(N(x − y))` truncated at `0` for `x ≠ y`, `0` on the diagonal, for `N : Seminorm ℝ (Fin d → ℝ)` evaluated at integer points; `cutoffKernel N K r := radialKernel N (cutoffProfile K r)` (`Models/LongRange/Defs.lean`); lemmas take `N : ModelNorm (Fin d → ℝ)` | Vertex set: any `V` with a distance function (source) against `ℤ^d` with a norm of `ℝ^d` (perclib, per the D-33 amendment: the paper's norm is a norm on `ℝ^d`). Values: `ℝ` against `ℝ≥0` (as `intensityProfile` requires). Arguments: ordered pair against `Sym2`. The source's lattice kernel fixes the sup norm and constant `1`. | `radialKernel K ρ` becomes `radialKernel N K` with `ρ x y = N (Int.cast ∘ (x − y))`; values agree when `K ≥ 0`; `lrKernel d α = radialKernel (ModelNorm.ofNorm _) (powerLawProfile 1 (d + α))` on `Fin d → ℝ` with its sup norm. Results for a general `V` and `ρ` (none needed so far) would need a separate general statement. |
| Profiles | `modelProfile d α s := s^(−d−α)`; `cutoffProfile K r s := if s ≤ r then K s − K r else 0` (`KernelGeometry.lean`) | `powerLawProfile c a s := c * s^(−a)`; `cutoffProfile` identical (`Models/LongRange/Defs.lean`) | perclib carries a normalising constant `c` (the wiki articles use `c = 1/a`, so that the cut-off profile is `∫_s^r t^(−a−1) dt`). | `modelProfile d α = powerLawProfile 1 (d + α)`. |
| Norms | the ambient norm `‖·‖` of a finite-dimensional real normed (inner product) space `E` and a Haar measure parameter `μ` in `LevyAnalysis/`; an arbitrary `ρ` in `KernelGeometry.lean`; the sup norm (`linfNorm`, `latticeDist`, `box`) in `LatticeGeometry.lean` | `ModelNorm E`, a structure extending `Seminorm ℝ E` with definiteness, with `ofNorm`, `comp`, and the type synonym `WithModelNorm N` that carries the normed-space structure of `N` (`Analysis/ModelNorm/Defs.lean`); sup-norm ball counts in `Models/LongRange/PowerLaw.lean` | The source varies the norm by changing the space's norm instance; perclib passes the norm as a parameter, so one inner product (for Fourier pairings) and one Lebesgue measure coexist with any model norm. | Each statement over `‖·‖` is re-parametrised by `N`; `WithModelNorm N` gives access to mathlib's normed-space lemmas for `N` where a proof needs them. |
| Lévy measures and dispersion | `levyDensInf α`, `levyDensLam α lam`, `levyDensOne α`, `PiInf α μ`, `PiLam α lam μ`, `PiOne α μ` (`LevyAnalysis/Measures.lean`); `levyPsi` (Bochner) and `levyExp` (lower integral), `addConv`, `convPow`, `expGeom`, `truncSet`; existence `exists_nuDisp` (a symmetric probability measure with characteristic function `(1 + ψ)⁻¹`) (`LevyAnalysis/Dispersion.lean`); `rieszKernel` | `stableLevyDensity N α`, `cutoffLevyDensity N α l`, `stableLevyMeasure N α`, `cutoffLevyMeasure N α l` (Lebesgue measure with density), `levyExponent L u` (lower integral), predicate `IsExpTimeStoppedLaw ψ ν` (probability measure with characteristic function `(1 + ψ)⁻¹`) (`Probability/Dispersion/Defs.lean`) | Norm `‖·‖` against seminorm parameter `N`; Haar parameter `μ` against `volume`; the source's existence statement also gives symmetry, which perclib's predicate does not include; perclib has no convolution-power definitions (mathlib has `Measure.mconv`/`conv`). | Replace `‖x‖` by `N x` and `μ` by `volume`; `levyExp` is `levyExponent`; `levyPsi` is its real form under integrability; convolution powers via mathlib, or a proposed definition. |
| Cluster volume law and moments | `volumeLaw π o := (edgeMeasure π).map (fun ω => (clusterVol ω o).toReal)` (`Analysis/VolumeLaw.lean`); `spatialMoment s t q o ω := ∑_{x ∈ K_o} q x` and `volWeightedSpatialMoment` in the finite endpoint-map model (`VolumeMoments/SpatialMoments.lean`); `ghostProb`, `ghostLaw`, `ghostMass`, `ghostHits`, `weightedGhostMass` (`CountableProduct/GhostField.lean`) | no volume-law definition (written out where used); `spatialMoment q o w := E_q[∑_{x ∈ K_o} w(x − o)]` in `ℝ≥0∞` on an additive group, infinite volume (`Percolation/Bond/SpatialMoments/Defs.lean`); the ghost field is expressed through identities such as `lintegral_cluster_one_sub_exp_eq_prod` (`Percolation/Bond/IndependentLayer/Ghost.lean`) and `Probability/GhostTransform.lean` | The source names the observables; perclib defines the spatial moment as an expectation and writes the others out. The source's spatial moment is a random variable in a finite model, perclib's an expectation in infinite volume. | Write `volumeLaw` out (or agree a definition); rewrite finite-model spatial observables as expectations over `law q`; replace `ghostHits` by the integral `∫⁻ (1 − e^{−h|K_o|}) d(law q)`. |
| Size-biased laws | `sizeBias μ := μ.withDensity (fun x => ENNReal.ofReal x)` on `ℝ`, unnormalised (`MomentProblem/SizeBiasing.lean`); `sizeBiasedLaw`, `sizeBiasedBaseLaw`, `mean`, `secMoment`, `sbMean` (`Analysis/SizeBiasedMGF.lean`) | no definition: `P.withDensity (fun ω => X ω / ∫ X dP)` written out (`Probability/SizeBias.lean`, `SizeBiasLimits.lean`, `ChiSquareMoments.lean`) | Named, unnormalised (source) against written out, normalised (perclib). | Express each source quantity through `withDensity`; normalisation constants become explicit. |
| Regular variation | `RegularlyVaryingAtTop f a := (∀ᶠ x, f x ≠ 0) ∧ ∀ l > 0, f(l x)/f(x) → l^a`, `SlowlyVaryingAtTop` (`Analysis/RegularVariation.lean`) | `RegularlyVarying ρ f`, `SlowlyVarying L`: measurable on some tail `[a, ∞)`, eventually positive, `f(c x)/f(x) → c^ρ` (`Analysis/RegularVariation/Defs.lean`) | Argument order; eventual non-vanishing against eventual positivity; no measurability against tail measurability (the paper says regularly varying functions are taken measurable). | Swap arguments; add positivity and tail measurability where the source assumed only non-vanishing; drop separate positivity hypotheses that the perclib notion contains. |
| Logarithmic integrability | `LogarithmicallyIntegrable h := Measurable h ∧ ∃ r₀ > 0, ∫_{r₀}^∞ |h r|/r dr < ∞`, `IsLogErrorFunction` (`Analysis/RegularVariation.lean`) | same names, with measurability on a tail instead of global measurability (`Analysis/RegularVariation/Defs.lean`) | Global against tail measurability. | Proofs first pass to a globally measurable function equal to `h` on a tail (`exists_measurable_eqOn_Ici`). |
| Bundled regular-variation data | `structure RVPosData f ρ` (index `ρ > 0`, measurability, regular variation, a threshold `≥ 1` with positivity above it, a Potter exponent `ε ∈ (0, 1/2]`, `ε < ρ`, and Potter bounds above the threshold), with `RVPosData.of`, `RVPosData.genInv` (`Analysis/GeneralInverse.lean`) | unbundled: hypotheses `0 < ρ`, `Measurable f`, `RegularlyVarying ρ f`, and lemmas producing thresholds and Potter bounds (`RegularlyVarying.exists_threshold`, `RegularlyVarying.exists_potter_threshold`, `RegularlyVarying.uniform_ratio`, `Analysis/RegularVariation/GeneralInverse.lean`) | One structure argument against several hypotheses plus existence lemmas. | Each use of `D : RVPosData f ρ` becomes the three hypotheses, and fields are obtained from the existence lemmas inside proofs. |
| Generalized inverse | `levelSet f x0 y`, `genInv f x0 y := sInf (levelSet f x0 y)` (`Analysis/GeneralInverse.lean`); `levelInverse f X hcont htop y`, a level point chosen with `Classical.choose`, depending on continuity and divergence proofs (`Analysis/RVInverseMonotone.lean`) | `genInv f x₀ y := sInf {x | x₀ ≤ x ∧ y ≤ f x}` (level set inlined, `Analysis/RegularVariation/Defs.lean`); the source's `levelInverse` results are proved for `genInv` (`Analysis/RegularVariation/LevelInverse.lean`) | Two inverses (one choice-built and proof-dependent) against one. Junk value: `sInf ∅ = 0` in both. | `levelInverse` becomes `genInv`; statements that used `f (levelInverse … y) = y` use `genInv` with continuity. |
| Analytic auxiliaries | `errorTail`, `powerExpWeight` (`Analysis/Lemma_I_4_21.lean`); `potKer`, `logTransformFirst`, `logTransformSecond` (`Analysis/Lemma_I_4_13.lean`); `oddFact` (`MomentProblem/ChiSquare.lean`); Tauberian `Phi`, `profileBound`, `limitProfile`; kernels `kern`, `expK`, `kernBCF` (`Analysis/WeakKernels.lean`, `WeakBoundedKernels.lean`); `A3const`, `A4const`, `Qinf`, `normalizer`, `lapDefect` | written out inline in statements; `oddFact` is mathlib's `Nat.doubleFactorial` | Named helper definitions against inline expressions (the library adds a definition only with its basic API, in a `Defs.lean` file). | Inline the definition; where the same expression would recur a third time, propose a definition instead. |
| Mass transport | `shiftConfig`, `clusterVolR` (`MassTransportI41.lean`, `CountableProduct/MassTransport.lean`) | `Sym2.map` transport of configurations (`Percolation/Bond/Transport.lean`), `Probability/MassTransport.lean`, `Probability/MassTransportTuple.lean` | Own shift against the library's transport. | Rewrite with `Sym2.map` and the library's mass-transport lemmas. |
| Trees | rooted binary tree type `RTree` (`TreeExpansion/Basic.lean`) | `TreeShape k` (`Percolation/Bond/Multipoint/Defs.lean`) | Two tree types; D-33 keeps one. | Recursion on `RTree` is rewritten on `TreeShape`. |

**Notes.**

1. The outside formalisation and the library share the bond law, so statements about
   `edgeMeasure` port verbatim; the work concentrates on the kernel layer (vertex set, norm,
   value type), on the analysis notions (measurability and positivity in regular variation,
   bundling), and on naming policy (the library writes out most auxiliary definitions).
2. Hypotheses the source needed and the paper does not state are kept as explicit hypotheses
   in a port (D-33). Several have since been discharged in the library (section 2.3).
3. Ported declarations are renamed after their conclusions (mathlib style), with the source
   name recorded in the port's documentation; a few early ports keep paper-numbered names
   (for example `lemma_I_4_13_first`, `lemma_I_2_10`).

## 2. What formalisation found about the papers

### 2.1 Lemma I.4.13, second half: an implicit local-integrability assumption

Lemma I.4.13 says that for `a > 0` the transform `T h (r) = r^(−a) ∫_1^r s^(a−1) h(s) ds` of a
logarithmically integrable error function `h` (measurable, `∫^∞ |h(r)| dr/r < ∞`, `h(r) → 0`)
is again one. The integral is defined only if `s^(a−1) h(s)` is integrable on `(1, r]`, which
the hypotheses do not give. Take

  `h(s) = 1_{(1,2)}(s) · (s − 1)^(−1)`.

It is measurable, vanishes on `[2, ∞)`, and tends to `0`, so it is a logarithmically integrable
error function; but `s^(a−1) h(s)` is integrable on no `(1, r]` with `r > 1`, for any `a`. So
the lemma uses local integrability of `h` on `(1, ∞)` implicitly. Compiled in
[`Analysis/RegularVariation/LogErrorTransformsTail.lean`](../../PercLib/Analysis/RegularVariation/LogErrorTransformsTail.lean):

- `isLogErrorFunction_indicator_sub_inv`: `IsLogErrorFunction ((Ioo 1 2).indicator fun s => (s − 1)⁻¹)`;
- `not_integrableOn_rpow_mul_indicator_sub_inv (a) (hr : 1 < r)`:
  `¬ IntegrableOn (fun s => s^(a−1) * (Ioo 1 2).indicator (fun s => (s − 1)⁻¹) s) (Ioc 1 r)`;
- the form with the assumption made explicit, `IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc_one`
  (hypotheses `IsLogErrorFunction h`, `0 < a`, `∀ r, IntegrableOn h (Ioc 1 r)`).

The same file records that a premise-free Lean statement (`IsLogErrorFunction.rpow_neg_mul_setIntegral_Ioc`)
is provable only because a non-integrable function has integral `0` in Lean; it is not the
faithful form. The first half of the lemma and the second half with lower limit `r₀` are in
`Analysis/RegularVariation/LogErrorTransforms.lean` (`lemma_I_4_13_first`, `lemma_I_4_13_second`).

### 2.2 Lemmas I.4.21 and I.5.5 hold as stated

Both have been compared with the paper's statements binder by binder; every hypothesis of
the Lean statements is a hypothesis of the paper or comes from writing functions on `(0, ∞)` as
functions on `ℝ`, and none goes beyond the paper.

- **Lemma I.4.21** (`f′ ∼ r^(−1)(a f + h)` with `h` regularly varying of index `b > a`): the two
  conclusions are `tendsto_div_of_tendsto_deriv_ratio` and
  `regularlyVarying_of_tendsto_deriv_ratio` ([`Analysis/DrivenODE.lean`](../../PercLib/Analysis/DrivenODE.lean)).
  The outside formalisation proved it under an extra assumption `f > 0`, which the paper does
  not make; the perclib proof does not use it, and also asks positivity of `h` only eventually.
- **Lemma I.5.5** (`f′ ∼ (a f + h)/r` with `h` of general index `b`):
  `regularlyVarying_max_and_tendsto_of_tendsto_deriv_ratio`
  ([`Analysis/CriticalDrivenODE.lean`](../../PercLib/Analysis/CriticalDrivenODE.lean)), assembled from
  the cases `b < a` (`regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_lt`, `DrivenODE.lean`),
  `a = b` (`regularlyVarying_and_tendsto_of_tendsto_deriv_ratio_of_eq`, which needs only eventual
  positivity of `f` and no positivity of `h`) and `a < b` (Lemma I.4.21). The global positivity
  of `f` and `h` in the full statement is the paper's own hypothesis.

Neither has a tagged (`Tags/`) restatement yet.

### 2.3 Premises of the outside formalisation discharged in perclib

D-33 lists premises that the outside formalisation needed and the paper does not state. Their
status in this library:

| Premise (source) | Where the source assumes it | perclib | Declaration |
|---|---|---|---|
| `hunif`: locally uniform convergence of the windowed cluster functionals | `RussoInf/Exchange.lean`, `FluxMain.lean`, `Capstone.lean` (infinite-volume Russo formula, Lemma I.4.1) | discharged: the Russo formula along the cut-off family is proved from a dominator, with no uniformity premise | `integral_sub_eq_integral_flux`, `integral_sub_eq_integral_flux_cutoff`, `hasDerivAt_integral_cutoff` ([`Models/LongRange/InfiniteVolumeRusso.lean`](../../PercLib/Models/LongRange/InfiniteVolumeRusso.lean)) |
| `hD`: omitted-edge row bound, in the `shiftProb` form | `Analysis/VolumeTailUpper.lean`, `VolumeTailAllN.lean`, `PercolationI32.lean`, `CountableProduct/GhostCoupling.lean` (Propositions I.3.1, I.3.2) | discharged for the power-law cut-off family, for any norm comparable with the sup norm (every norm on `ℝ^d` is) | `tsum_shiftProb_le`, with `tsum_omittedKernel_le`, `tsum_omittedLayer_le` ([`Models/LongRange/OmittedLayer.lean`](../../PercLib/Models/LongRange/OmittedLayer.lean)) |
| `hG`: the ghost-hit probability of a vertex is at most that of the root | same files, `CountableProduct/GhostField.lean` | discharged, with equality, for the radial and cut-off kernels at every norm, profile, scale and intensity | `ghost_hits_le_root_radialKernel`, `ghost_hits_le_root_cutoffKernel` ([`Models/LongRange/RootIndependence.lean`](../../PercLib/Models/LongRange/RootIndependence.lean)) |
| `f > 0` in Lemma I.4.21 | `Analysis/Lemma_I_4_21.lean` | not needed | `regularlyVarying_of_tendsto_deriv_ratio`, `tendsto_div_of_tendsto_deriv_ratio` (`Analysis/DrivenODE.lean`) |
| global `Measurable h` in the second half of Lemma I.4.13 | `Analysis/Lemma_I_4_13.lean` | replaced by tail measurability (with `b ≤ r₀`) | `isLogErrorFunction_rpow_neg_mul_setIntegral_Ioc_of_measurable_Ici` (`Analysis/RegularVariation/LogErrorTransformsTail.lean`) |
| `Measurable δ₂` in Lemma I.5.6 (two-error form) | `Analysis/Lemma_I_5_6.lean` | removed (a measurable forcing term is built from the equation); the hypothesis `δ₂ → 0` is kept | `exists_tendsto_of_critical_two_error_ode`, `tendsto_div_mul_rpow_mul_log_of_critical_two_error_ode` ([`Analysis/CriticalLogODE.lean`](../../PercLib/Analysis/CriticalLogODE.lean)) |

Still open in this library: `hTailPos` (positivity of the volume tail at every `n`, Proposition
I.3.1), which the outside formalisation discharges for its lattice kernel in
`Analysis/VolumeTailLatticePositivity.lean` and which would have to be re-proved for
`cutoffKernel`; `δ₂ → 0` in Lemma I.5.6; the sharpness, a-priori and regularity hypotheses of the
first-moment bootstrap (Proposition I.4.2, Corollary I.4.8; `Analysis/FirstMomentAsymptotic.lean`,
`Analysis/RiccatiBootstrap.lean`), kept explicit; and the hypothesis package
`FullLawGhostRatio` of the analytic half of Propositions I.3.1/I.3.2, whose perclib form
(`Analysis/VolumeTail/`) keeps the comparison as explicit hypotheses. While such a hypothesis
remains, the corresponding statement of the paper is not counted as proved.

### 2.4 Findings recorded in the outside formalisation

The outside formalisation records further points about the printed text in its own files. They
are listed here for the review as the source states them; the library has not checked them
independently unless noted.

- Proposition I.5.2, case `α > 2`: the printed form of `ξ₂²(r)` is inconsistent with
  `ξ₂(r) ∼ √A r^(α/2)` in the same proposition (`Analysis/GyrationReduction.lean`).
- (I.5.16) scaling: the printed factor `λ^(d−α)` is inconsistent with the displayed densities;
  `λ^(−d−α)` is consistent (`LevyAnalysis/LevyScaling.lean`).
- Lemma I.4.12: two steps of the printed proof fail, with explicit configurations
  (`Correlation/PrintedEventFails.lean`, `Correlation/SelfRestoration.lean`,
  `CountableProduct/RestorationCompl.lean`). The statement of Lemma I.4.12 is proved in this
  library for every profile (`Percolation/Bond/ClusterCorrelation/TwoClusterGap.lean`).
- (I.3.5): the cut-off form does not follow from a degree-tail cost
  (`CountableProduct/GhostCutoffCounterexample.lean`, `RestorationDegree.lean`).
- The `k = 0` endpoint of the per-scale universal tightness theorem of arXiv:2008.11197 fails
  (`Tightness/EndpointCounterexample.lean`); the library's statement starts at one iteration.
- The outside formalisation's own hypothesis package for the Lemma I.5.8 transport step
  (`VolumeMoments/I58Cross.lean`) is jointly unsatisfiable for any non-trivial weight
  (`VolumeMoments/I58Nonvacuity.lean`); this is about the package, not the paper.

### 2.5 Provisional errata on Parts I–III in the public wiki

The wiki keeps erratum records in [`wiki/errata/`](../../wiki/errata/). Every record below is
**provisional**: the diagnosis comes from reading the arXiv v1 HTML and PDF renditions, and no
author confirmation or later edition is assumed. Each line gives the key, the locator in the
paper, the wiki assertions that carry the correction, and the record's title. The records
themselves give the claim, the problem, the correction and its consequences for a formal
statement.

**Part I (arXiv:2508.18807v1)**, [`wiki/errata/hutchcroft-lrp-1.json`](../../wiki/errata/hutchcroft-lrp-1.json), 7 records:

- `levy-first-moment-weight` (proof of Lemma I.5.17, (I.5.16); `MWZ7`): First-moment weighting in the displacement-density proof. Status: provisional.
- `spatial-normalization-indices` (§I.5.4, (I.1.14); `57FJ`, `L9YJ`, `BB3O`): Regular-variation indices after changing to spatial radius. Status: provisional.
- `mixed-moment-cluster-index` (Lemma I.5.28, (I.5.35); `1K61`, `GY8M`): The moved marked vertices belong to the second cluster. Status: provisional.
- `mixed-moment-radius-factor` (Lemma I.5.29, (I.5.44); `1K61`, `IX97`, `GY8M`): Missing radius power in the factorized mixed-moment formula. Status: provisional.
- `signed-ode-shift-derivative` (proof of Lemma I.5.26; `2KB9`): Derivative of the integral shift in the signed ODE proof. Status: provisional.
- `karamata-tail-constant` (Lemma I.2.10; `3491`): Karamata integral tail constant for index below minus one. Status: provisional.
- `critical-inverse-log-sign` (Remark I.1.16, Theorem I.1.15; `QKHV`): Sign of the inverse normalization at the critical dimension. Status: provisional.

**Part II (arXiv:2508.18808v1)**, [`wiki/errata/hutchcroft-lrp-2.json`](../../wiki/errata/hutchcroft-lrp-2.json), 15 records:

- `multiscale-tower-indices` (§II.5.3, proof of Proposition II.5.9; `L5IG`, `2BBE`): Intersection ranges in the multiscale tower identity. Status: provisional.
- `cutoff-derivative-endpoint-integral` (proof of Proposition II.2.5, (II.2.5); `AUAE`): The alpha=d endpoint of the cutoff derivative integral. Status: provisional.
- `spread-insertion-self-distance` ((II.3.8), proof of Lemma II.3.7; `0VKF`, `WDGK`): The insertion product must exclude the point being inserted. Status: provisional.
- `geometric-gladkov-product-exponent` (proof of Corollary II.3.8; `C4A5`, `WDGK`): Square-root exponent in the geometric multipoint induction. Status: provisional.
- `inversion-sign-and-complex-form` (proof of Proposition II.3.9; `9YE6`, `N76U`): Inversion conventions in the covariance proof. Status: provisional.
- `multigraph-summation-order` (§II.4.1, proof of Lemma II.4.6; `1EWL`, `SOHR`): Positive elimination exponents in the multigraph moment sum. Status: provisional.
- `exact-cutoff-derivative-coefficient` (§II.4.3, (II.4.27); `GG8B`, `A3G0`): The exact second-moment equation retains the kernel derivative. Status: provisional.
- `truncation-back-propagation-normalization` (Lemma II.5.5; `OP4X`, `KKGL`): Normalization and radius scope in truncated back-propagation. Status: provisional.
- `negligibility-truncation-comparison` (proof of Proposition II.5.3; `KKGL`, `OP4X`): Truncation direction at the end of the negligibility proof. Status: provisional.
- `small-window-moment-exponents` (proof of Theorem II.5.2(1); `SOG8`, `AS7A`): Moment and tail exponents in the small-window proof. Status: provisional.
- `annular-small-volume-and-ghost-scope` (Theorem II.5.2(2), (II.5.9); `L6K3`, `AYPN`, `79SD`): Small-volume and endpoint scope of the annular argument. Status: provisional.
- `subcritical-radius-variables` (§II.6.1, Lemma II.6.1; `04ZI`, `KA3B`): Radius variables in the subcritical derivative displays. Status: provisional.
- `two-point-upper-integration` (§II.6.1, proof of Lemma II.6.3; `TFKR`, `KA3B`): Factor indices and integration range in the two-point upper bound. Status: provisional.
- `two-point-joining-windows` (§II.6.1, Lemma II.6.5; `9ZEL`, `NI07`): Window centers and small chosen radii in the joining argument. Status: provisional.
- `subcritical-capped-expectation` (§II.6.2, proof of Theorem II.1.15; `XANO`, `IK5Y`, `T5JS`): Capping, rather than truncating, in the subcritical second-moment lower bound. Status: provisional.

**Part III (arXiv:2508.18809v1)**, [`wiki/errata/hutchcroft-lrp-3.json`](../../wiki/errata/hutchcroft-lrp-3.json), 26 records:

- `critical-inverse-log-signs` (§III.1.3, (III.1.18); `QKHV`): Logarithm signs in the introductory inverse-scale calculation. Status: provisional.
- `modified-intensity-chain-factor` (§III.3.1, proof of Lemma III.3.4; `1BO9`): Missing alpha in the modified-intensity chain rule. Status: provisional.
- `modified-reciprocal-integral` (§III.3.1, proof of Corollary III.3.12; `AGX4`): Squared denominator and intensity variable in the reciprocal comparison. Status: provisional.
- `last-large-quantile-scale` (proof of Lemma III.3.14; `0HMO`, `CXTO`): The last large-quantile scale needs its own normalized threshold. Status: provisional.
- `added-layer-endpoints` (Lemma III.3.15, (III.3.15); `5FCO`, `1AQ4`): Continuation probabilities and row sums must use the exit endpoints. Status: provisional.
- `fictitious-lambda-power` (Lemma III.3.16, (III.3.16); `SQGG`): The initial derivative lower bound has a positive twelfth power of lambda. Status: provisional.
- `cap-radius-power` (proof of Proposition III.3.13; `0NU2`, `BTM3`): The cap estimate supplies the first power of the radius exponent. Status: provisional.
- `biased-tail-conversion` (proof of Lemma III.3.21; `2Z34`): The unbiasing event and its square-root scale must agree. Status: provisional.
- `mesoscopic-selected-radius` (Lemma III.3.22, (III.3.23); `2HXZ`, `Q7O9`): The selected scale must also index the percolation law. Status: provisional.
- `riccati-linear-rearrangement` (Lemma III.3.23; `19IN`, `Q7O9`): Extra radius factor in the rearranged Riccati estimate. Status: provisional.
- `restricted-cluster-heredity` (Lemma III.4.2, (III.4.3); `BN7Z`, `XFCJ`, `OTH1`, `X86B`): The restricted-cluster comparison needs a hereditary class and consistent paths. Status: provisional.
- `gluing-window-radius` (Lemma III.4.4, Lemma III.4.1; `20LA`, `9CER`): The local surplus is at radius 2r, while the next subtraction uses radius r. Status: provisional.
- `gluing-normalized-errors` ((III.4.8), (III.4.9); `JY26`, `9CER`, `F42K`): The gluing proof needs normalized truncation errors and consistent band scales. Status: provisional.
- `gluing-modified-growth` (proof of Lemma III.4.1, (III.4.10); `F42K`, `JY26`, `XHJ4`, `AGX4`, `VW2E`): The modified-law case adds an unsupported cap and loses the derivative-gain scale. Status: provisional.
- `many-scales-recursion` (proof of Lemma III.4.5, (III.4.11); `NE2Q`, `WKM2`, `2YIE`): The scale recursion needs a weighted tail budget and parameter-dependent separation. Status: provisional.
- `many-scales-conditioning` (proof of Lemma III.4.5, (III.4.12); `WKM2`, `2YIE`, `QXP9`): The second-cluster filtration reveals future scales and its recurrence loses the radius normalization. Status: provisional.
- `recentering-partition` (Lemma III.4.6, (III.4.14); `43QA`, `LHT3`): The recentering calculation changes window radii and reverses the Markov factor. Status: provisional.
- `recentering-scale-count` (proof of Lemma III.4.6, Lemma III.4.5; `QXP9`, `43QA`, `LHT3`): The recentering union bound uses the wrong bad-scale threshold. Status: provisional.
- `joining-cutoff-window` (proof of Proposition III.3.1, (III.4.18); `7IVI`, `LHT3`, `L3TC`): The joining interval ends at the largest permitted cross distance. Status: provisional.
- `local-moment-translation` (proof of Lemma III.4.7; `9JTA`, `BCKB`): The mixed local-moment term loses the transformed window centres. Status: provisional.
- `weighted-tail-product-index` ((III.5.2); `AR3F`, `3M2Y`): The weighted tail display includes an unbound first factor. Status: provisional.
- `first-deficit-susceptibility-power` (Theorem III.6.6, (III.6.13); `5J3U`, `OP8F`): The first deficit moment normalization loses a susceptibility factor. Status: provisional.
- `weighted-geodesic-unbound-target` (Lemma III.6.18; `V7V5`): The weighted geodesic estimate uses an unbound target. Status: provisional.
- `interception-diagram-missing-link` (proof of Lemma III.6.17; `ZGVN`, `IEOH`, `LK8Z`, `O10I`, `R6CI`): The printed interception diagram loses the link to the root cluster. Status: provisional.
- `deficit-ode-merger-forcing` (Lemma III.6.13, Lemma III.6.12; `ENWJ`, `J2QW`, `RDLW`): The deficit ODE forcing terms disagree with the merger formulas. Status: provisional.
- `joint-cut-repeated-path-condition` (proof of Lemma III.6.16; `RIH3`, `1P14`, `DR5Q`): The joint-cut proof repeats one path-avoidance condition. Status: provisional.


## 3. Open interface questions for the joint review

Each question lists the options seen so far. Where the library has made a choice, it is
noted; that is a description of the current state, not a recommendation.

1. **Bundled or unbundled regular-variation data.** (a) A structure like `RVPosData` bundling
   index, measurability, regular variation, threshold and Potter bounds; (b) explicit
   hypotheses with existence lemmas for thresholds and Potter bounds; (c) a smaller structure
   for the groups of hypotheses that recur (a threshold group, a vanishing-error group), placed
   in a `Defs.lean` with its API. The library currently uses (b).
2. **Generalized inverse.** (a) `genInv` (infimum of a level set above a threshold); (b) a
   choice-built level selection such as `levelInverse`, which depends on continuity and
   divergence proofs; (c) both, with a bridge lemma. The library currently uses (a) only.
3. **Which notion of regular variation.** (a) eventual non-vanishing, no measurability
   (`RegularlyVaryingAtTop f a`); (b) eventual positivity and measurability on a tail
   (`RegularlyVarying ρ f`); and the argument order. The library currently uses (b), with the
   index first.
4. **Norm of the long-range kernel.** (a) the ambient norm of a normed space, varying the
   instance (with a type synonym per norm); (b) a norm passed as a parameter (`ModelNorm`, or a
   `Seminorm` plus definiteness), with `WithModelNorm N` to reach mathlib's normed-space API;
   (c) an arbitrary distance function `ρ : V → V → ℝ`. The library currently uses (b); the
   D-33 amendment fixed the norm to be a norm on `ℝ^d` restricted to `ℤ^d`.
5. **Vertex set and value type of the kernel.** (a) any type with a distance, real-valued,
   two arguments; (b) `ℤ^d`, `ℝ≥0`-valued on `Sym2`, as `intensityProfile` requires. The library
   currently uses (b), with general-profile lemmas on `ℤ^d`.
6. **Normalisation of the power law.** (a) `s^(−d−α)` with constant `1`; (b) `c s^(−a)` with a
   constant parameter (the wiki uses `c = 1/(d + α)`). The library currently uses (b).
7. **Measure in the Lévy definitions.** (a) a Haar measure parameter; (b) Lebesgue measure
   (`volume`). The library currently uses (b). Related: whether the exponential-time law should
   be a predicate (`IsExpTimeStoppedLaw`) or a constructed measure, and whether symmetry is part
   of it.
8. **Critical point.** (a) `inf{β : an infinite cluster exists almost surely}` in `ℝ≥0`; (b)
   `inf{β : positive probability of an infinite cluster}`, global or at a root, in `ℝ≥0∞`. The
   library currently uses (b); the two differ at the empty set (`0` against `⊤`).
9. **Named or written-out auxiliary quantities** (volume law, size-biased laws, error tails and
   weights, Tauberian profiles, constants of the volume-tail argument). (a) named definitions;
   (b) written out, with a definition proposed once an expression recurs a third time; the
   library's rule is that a definition lands in a `Defs.lean` with its basic API. The library
   currently uses (b); a shared definition of the normalised size-biased law has been suggested
   but not adopted.
10. **Auxiliary finite models.** Whether finite-volume arguments may use a separate finite
    configuration type (`Finset` configurations, `BondGraph`) or must use the one bond model on
    a finite index type. D-33 currently rules out second models.
11. **Tree type.** `RTree` or `TreeShape`; D-33 keeps one tree type, currently `TreeShape`.
12. **Names.** Paper-numbered names (`lemma_I_5_5`) or names describing the conclusion, with
    the paper number in the docstring. The library's rule is the latter; a few early ports keep
    paper-numbered names.
13. **Hypotheses beyond the paper.** How to record a port whose proof needs a premise the paper
    does not state: (a) an explicit hypothesis, the paper's statement staying an unproved target
    (the library's current practice, D-33); (b) a cited-input structure (reserved in the library
    for results of the literature the paper cites, D-4).
