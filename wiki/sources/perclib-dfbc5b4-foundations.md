# Train 10: sharpness, ghost comparison and moment tools

This inventory is pinned to private lrp merged main dfbc5b4f4e964374431189c682520bff85e008e6. It records **34 explicit public theorem starts in four complete files / 1,001 lines**, together with six shared contracts and the complete diffs of 23 previously read files against [Train 9](sources/perclib-f51f639.md). Private proofs and anonymous witnesses were read but are excluded from the declaration census. Source inspection does not supply a compiled tag association or an independent correspondence review.

## Percolation/Bond/Sharpness

| Source line | Contract | Exposition |
|---|---|---|
| [L54](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | Escape from a set is the union of root connections to vertices outside it, on any vertex type. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L61](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | Summable real intensity rows give finite extended off-diagonal rows. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L70](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | For summable rows and a finite set, the extended boundary functional is the nonnegative-real embedding of its real-valued form. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L105](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | On countable vertices with summable rows, boundary flux at least one for every finite root set above t>=0 gives the finite-domain escape derivative and f prime >= (1-f)/beta. No transitivity is assumed in this implication. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L142](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | For a transitive summable intensity kernel on countable vertices, the supremum of parameters admitting a strict finite-set contraction is at most the root percolation threshold. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L158](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | For a summable intensity kernel on countable vertices, the root threshold is at most that contraction supremum. This direction needs no transitivity and includes an infinite supremum. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L188](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | Under transitivity and summable rows, the root threshold equals the contraction supremum, in the extended nonnegative reals. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L202](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | Susceptibility at the root is finite at every finite parameter strictly below its threshold, under the same countable transitive summable hypotheses. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L215](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | That strict subcritical finiteness holds at every vertex. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L224](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | On countable vertices, finite root susceptibility at beta implies beta is at most the root threshold. This implication does not assume transitivity or summable intensity rows. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L239](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | Under transitivity and summable rows, the root threshold is the supremum of finite-susceptibility parameters. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L250](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | The global threshold is the same contraction supremum. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L263](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | The global threshold is the same finite-susceptibility supremum. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L272](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | At or above the root threshold, every finite set containing the root has boundary functional at least one, under transitivity and summability. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |
| [L288](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Sharpness.lean) | For every finite beta above the threshold, the infinite-cluster probability is at least 1-beta_c/beta. The strict inequality forces a finite threshold. | [Argument](../articles/finite-size-sharpness.md#section-complete-sharpness-source) |

## Percolation/Bond/IndependentLayer/Conditional

| Source line | Contract | Exposition |
|---|---|---|
| [L44](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IndependentLayer/Conditional.lean) | Keeping a deterministic set of bonds and independently sampling its complement recombines to the original profile. | [Argument](../articles/size-biased-laws.md#section-hard-cutoff-source) |
| [L52](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IndependentLayer/Conditional.lean) | The omitted off-diagonal row bound is exactly the row bound required by independent-layer comparison. | [Argument](../articles/size-biased-laws.md#section-hard-cutoff-source) |
| [L67](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IndependentLayer/Conditional.lean) | On countable vertices, at positive field, an almost surely finite cutoff root cluster and omitted rows bounded by an extended delta give both monotonicity of the ghost transform and the upper comparison with the supremum of full-model transforms over roots. | [Argument](../articles/size-biased-laws.md#section-hard-cutoff-source) |
| [L99](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IndependentLayer/Conditional.lean) | An invariant transitive profile gives equal ghost-transform expressions at every root; the formal equality is stated for any real field and any vertex type. | [Argument](../articles/size-biased-laws.md#section-hard-cutoff-source) |
| [L115](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IndependentLayer/Conditional.lean) | If the full profile is transitive, the supremum in the positive-field comparison can be replaced by its value at the chosen root. The cutoff itself need not be transitive, but its root cluster must still be almost surely finite. | [Argument](../articles/size-biased-laws.md#section-hard-cutoff-source) |

## Probability/LayerCake

| Source line | Contract | Exposition |
|---|---|---|
| [L43](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | A measurable extended-natural variable has measurable integer upper-tail events. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |
| [L50](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | For any measure, its extended first moment is the sum of the probabilities or measures of tails at thresholds n+1, n>=0. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |
| [L67](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | Truncation at the natural N gives the finite tail sum through threshold N, including N=0. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |
| [L95](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | Natural-number powers are monotone for every nonnegative real exponent. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |
| [L101](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | For a strictly positive real exponent p, an extended-natural value to the power p is the tail-indicator series weighted by (n+1)^p-n^p, including the infinite value. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |
| [L142](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | For any measure and measurable extended-natural variable, integration gives the same weighted series for every real moment p>0, allowing infinite integrals. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |
| [L169](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/LayerCake.lean) | For a measurable nonnegative real X and t>=0, the integral of X on X>t is t times the measure of X>t plus the integral, over s>t, of the measure of X>s. No finiteness of the measure or moments is assumed. | [Argument](../articles/integrated-lower-tails.md#section-real-layer-source) |

## Probability/PaleyZygmund

| Source line | Contract | Exposition |
|---|---|---|
| [L43](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | The square of the product of two extended nonnegative square roots equals the product, with the extended zero-times-infinity convention. | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |
| [L51](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | For any measure and measurable X>=0 and event A, the squared integral of X over A is at most the integral of X squared times the measure of A; infinite values are allowed. | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |
| [L73](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | For a probability measure, measurable extended nonnegative X with finite mean and 0<=theta<1, (1-theta)^2 (E X)^2 <= P(X>theta E X) E X^2. The second moment may be infinite. | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |
| [L104](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | Taking theta=0 gives the second-moment bound with the strict event X>0, still assuming a finite mean. | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |
| [L112](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | For measurable nonnegative real X in L2 with positive second moment, division gives the usual real probability lower bound; theta lies in [0,1). | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |
| [L150](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | The extended Paley–Zygmund inequality applies to a root-cluster volume on countable vertices with finite root susceptibility. | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |
| [L160](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/PaleyZygmund.lean) | If all vertex susceptibilities are at most a finite M, then (1-theta)^2 chi(o) <= P(volume>theta chi(o)) M^2. Transitivity is not required. | [Argument](../articles/integrated-lower-tails.md#section-second-moment-source) |

## Percolation/Bond/ConnectionKernel

| Source line | Contract | Exposition |
|---|---|---|
| [L194](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ConnectionKernel.lean) | The two-point probability is finite, since it is at most one; this formerly private fact is now public. | [Argument](../articles/connection-kernels.md) |

## Percolation/Bond/Tightness/FiniteQuantile

| Source line | Contract | Exposition |
|---|---|---|
| [L99](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tightness/FiniteQuantile.lean) | The largest cluster intersection with a finite window is monotone in the bond configuration; this formerly private fact is now public. | [Argument](../articles/window-tightness-interfaces.md) |

## Probability/DeterminedIndependence

| Source line | Contract | Exposition |
|---|---|---|
| [L81](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | Measurable events unchanged by restriction to disjoint coordinate sets are independent under the product law. The coordinate sets need not be finite. | [Argument](../articles/product-model.md) |

## Probability/Russo

| Source line | Contract | Exposition |
|---|---|---|
| [L444](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Russo.lean) | The finite cube weights sum to one for every real profile; positivity is not needed for this algebraic identity. | [Argument](../articles/russo-formula.md) |
| [L450](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Russo.lean) | For a profile in the unit interval, the cube expectation of an event indicator equals its probability. | [Argument](../articles/russo-formula.md) |
| [L457](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Russo.lean) | For a unit-interval profile, the expectation of the increasing-event pivotal indicator equals the probability of the corresponding insert/delete event. | [Argument](../articles/russo-formula.md) |

## Reconciliation of earlier modules

These are complete delta readings against the earlier pinned inventories, not fresh complete-file inventories. Old source links remain at their original revisions.

| Module | Change |
|---|---|
| [Models/TreeRecursion](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TreeRecursion.lean) | Imports the shared restriction-independence result and removes its private duplicate; the recursion contracts are unchanged. |
| [Models/UnattainedThreshold](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/UnattainedThreshold.lean) | Uses the canonical zero-intensity identity; its public statements are unchanged. |
| [Percolation/Bond/ClosedCertificates](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClosedCertificates.lean) | Removes a duplicate lower-set lemma for nonconnection; its remaining statements are unchanged. |
| [Percolation/Bond/ClusterLaw](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterLaw.lean) | Removes private image and block-independence duplicates; the finite-cluster and domain-Markov statements are unchanged. |
| [Percolation/Bond/ConnectionKernel](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ConnectionKernel.lean) | Makes the finite two-point probability helper public; the kernel estimates retain their statements. |
| [Percolation/Bond/DisjointUnion](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DisjointUnion.lean) | Uses the canonical disjoint-coordinate independence result in place of a private proof. |
| [Percolation/Bond/IndependentLayer/Ghost](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IndependentLayer/Ghost.lean) | Uses canonical finite-cylinder and complement helpers; the ghost-comparison statements are unchanged. |
| [Percolation/Bond/IntensityMonotone](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IntensityMonotone.lean) | Imports the canonical measurability of infinite-cluster existence and removes its duplicate. |
| [Percolation/Bond/RootIndependence](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/RootIndependence.lean) | Imports the canonical zero-profile identity and removes its private duplicate. |
| [Percolation/Bond/Tightness/BKStep](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tightness/BKStep.lean) | Uses the shared monotonicity of the maximum intersection in place of its duplicate. |
| [Percolation/Bond/Tightness/FiniteQuantile](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tightness/FiniteQuantile.lean) | Makes maximum-intersection monotonicity public and updates the call in quantile monotonicity. |
| [Percolation/Bond/Tightness/Moments](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tightness/Moments.lean) | Imports the canonical positive-quantile and measurability tools and removes duplicate helpers and a duplicate singleton witness. The three public moment contracts retain their scope. |
| [Percolation/Bond/TriangleDecay](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TriangleDecay.lean) | Uses the shared finite two-point probability helper. |
| [Probability/Coordinate](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Coordinate.lean) | Uses canonical finite all-open cylinder measurability. |
| [Probability/CovarianceRusso](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/CovarianceRusso.lean) | Removes its private cube-weight normalization proof and uses the shared result. |
| [Probability/DeterminedIndependence](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | Adds the restriction-form independence result, derived from the existing determined-event theorem. |
| [Probability/FiniteEnergy/Insertion](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteEnergy/Insertion.lean) | Uses the canonical measurable subtype-image helper. |
| [Probability/OpenEventHarris](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/OpenEventHarris.lean) | Uses canonical finite-cylinder measurability. |
| [Probability/Russo](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Russo.lean) | Collects three shared finite-cube identities without changing the existing Russo conclusions. |
| [Probability/RussoIntegral](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/RussoIntegral.lean) | Removes private event and pivotal expectation identities in favor of the shared versions. |
| [Probability/Superposition](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Imports the canonical complement law and removes its duplicate. |
| [Probability/Tags/Russo](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Russo.lean) | Removes private expectation-identity duplicates; the five tagged assertion statements are unchanged. |
| [Probability/VarianceTensorization](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/VarianceTensorization.lean) | Removes its duplicate public cube-weight normalization theorem and uses the shared one. |

## Scope and provenance

The sharpness header attributes new proofs to PROVER-G, assembling existing finite-size, wired-derivative and integration results. The witnesses include a zero kernel on the integers, a finite two-vertex model with infinite critical intensity, and a free-group tree where the density conclusion is nonvacuous. The source mentions L0TE and T-5 in comments but contains no tag attribute for those declarations. Its countable transitive summable model permits zero kernels and disconnected support. Critical infinite-cluster absence and spatial exponential decay are not conclusions of this file.

Its FJWB comparison is for a deterministic set of retained bonds and an independent complementary profile; the singleton zero-profile witness covers zero omitted rows. The full model, rather than the cutoff, supplies transitivity. Almost-sure cutoff finiteness is assumed, not inferred from a finite range or a row bound. The formal row parameter may be infinite, although a useful quantitative comparison requires it finite. This comparison includes the factor expressing absence of a mark in the old cluster. It is distinct from the fresh-mark added-volume estimate AYPN.

Finite constant and infinite constant variables test the extended-value endpoints. The real-exponent identities require p>0; the separate monotonicity lemma permits p=0. The real truncated identity uses strict tails and includes the boundary term t times the tail measure. The ghost-series formula is delegated to its own transform module.

Its probability form requires a finite first moment; its event Cauchy–Schwarz inequality does not. The real quotient form also requires a positive finite second moment. A Bernoulli variable witnesses equality in the second-moment bound, and the zero intensity on the naturals witnesses the cluster estimate. No transitivity is needed when susceptibilities are uniformly bounded.
