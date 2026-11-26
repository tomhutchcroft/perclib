# Cutoff, correlation, spatial-moment and multipoint interfaces

This inventory records **39 explicit named public theorems in four complete files / 847 lines**, together with **21 definitions and structures**, at private lrp merged main f51f639c15d742034cc6e2058008c79f48392873. Each file has been read in full. A definition whose value is a proposition specifies a target: it does not prove that proposition. Inline theorem attributes are included in the census; private helpers and anonymous witnesses are not.

## Models/LongRange/Defs

| Source line | Kind | Definition or target |
|---|---|---|
| [L56](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Object | Radial pair intensity from a group norm and the nonnegative part of a real profile. |
| [L62](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Object | Cutoff profile: K(s)-K(r) for s<=r, zero otherwise. |
| [L67](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Object | The corresponding cutoff pair intensity. |
| [L74](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Object | Power-law profile c s^(-a). |
| [L82](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Target proposition PVA8 | Integral and positive-part formulas for the normalized power-law cutoff, alpha>0 and r>0. |
| [L93](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Target proposition MQNP | Monotonicity, convergence to the full kernel and monotonicity of the opening probabilities. |
| [L105](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Target proposition LF50 | Exact intensity deficit for a non-diagonal pair inside the cutoff. |
| [L116](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Target proposition 6YYS | Intensity and opening-probability derivatives away from the cutoff corner. |

| Source line | Proved contract | Exposition |
|---|---|---|
| [L132](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | The radial pair kernel is zero on the diagonal and the nonnegative part of the real radial profile off it. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L135](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Every diagonal radial intensity is zero. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L139](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | The off-diagonal kernel is the nonnegative part of the profile at the displacement norm. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L143](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | If that profile value is nonnegative, coercing the off-diagonal intensity to the reals recovers it exactly. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L148](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Distinct lattice vertices have strictly positive displacement under an additive group norm. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L151](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | The cutoff kernel is the radial kernel of the truncated difference profile. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L154](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | At distance s<=r, the cutoff profile equals K(s)-K(r). | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L156](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | At distance s>r, the cutoff profile is zero. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L160](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | If K is decreasing on positive distances, then for fixed s>0 its cutoff profile is increasing in the real cutoff radius. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L174](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Under the same hypothesis, each cutoff pair intensity is increasing in its radius. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L185](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | For nonnegative K on positive distances and r>0, the cutoff kernel is at most the full kernel; monotonicity of K is not required for this bound. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L197](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | A positive power-law coefficient gives a positive profile at positive distances, for any real exponent. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L200](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Nonnegative coefficient and exponent make the power-law profile decreasing on positive distances. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L207](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | The canonical additive group norm equals the usual lattice supremum norm. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L210](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | A nonzero integer lattice vector has supremum norm at least one. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L216](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | The one-dimensional inverse-square example is positive off the diagonal. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L222](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | Its radial intensity row is summable. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L238](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | The radius-one inverse-square cutoff vanishes beyond one and is positive at distances strictly between zero and one. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |
| [L248](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/Defs.lean) | For the lattice supremum norm, every cutoff kernel at radius less than one vanishes, with no assumption on K. | [Argument](../articles/displacement-kernels.md#section-cutoff-interface) |

## Percolation/Bond/ClusterCorrelation/Defs

| Source line | Kind | Definition or target |
|---|---|---|
| [L46](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | Object | Restore a configuration using the first copy on pairs touching its root cluster and the second on all other pairs. |
| [L52](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | Target proposition | BK for increasing measurable cluster functionals restricted to distinct clusters. |
| [L61](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | Target proposition | Harris lower product bound for increasing measurable cluster functionals. |
| [L71](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | Target proposition | Upper product bound with the contribution from the event that the roots are connected. |
| [L82](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | Target proposition | Two-cluster gap bound with the five-factor diagram, for every bond profile. |

| Source line | Proved contract | Exposition |
|---|---|---|
| [L89](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | An edge in the restored configuration comes from the first copy if it touches its root cluster, and from the second copy otherwise. | [Argument](../articles/harris-inequality.md#section-cluster-interface) |
| [L94](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | On countable vertices, restoration is a measurable map of the two configurations. | [Argument](../articles/harris-inequality.md#section-cluster-interface) |
| [L111](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | On a pair touching the first root cluster, restoration agrees with the first configuration. | [Argument](../articles/harris-inequality.md#section-cluster-interface) |
| [L116](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | On a pair not touching that cluster, restoration agrees with the second configuration. | [Argument](../articles/harris-inequality.md#section-cluster-interface) |
| [L121](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | Restoring a configuration from two identical copies returns the same configuration. | [Argument](../articles/harris-inequality.md#section-cluster-interface) |
| [L148](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/ClusterCorrelation/Defs.lean) | The two-cluster gap inequality holds in the special case where the third marked vertex equals the first root; this is not its general proof. | [Argument](../articles/harris-inequality.md#section-cluster-interface) |

## Percolation/Bond/SpatialMoments/Defs

| Source line | Kind | Definition or target |
|---|---|---|
| [L44](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SpatialMoments/Defs.lean) | Object | Extended nonnegative weighted spatial moment on an additive group. |

| Source line | Proved contract | Exposition |
|---|---|---|
| [L47](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SpatialMoments/Defs.lean) | The weighted spatial moment is the nonnegative integral of the sum of weights over the root cluster. | [Argument](../articles/spatial-cutoff-moments.md#section-weighted-interface) |
| [L52](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SpatialMoments/Defs.lean) | Increasing the nonnegative weight increases the moment, without a countability premise. | [Argument](../articles/spatial-cutoff-moments.md#section-weighted-interface) |
| [L58](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SpatialMoments/Defs.lean) | On a countable additive group, the moment equals the sum over vertices of the two-point function times the displacement weight. | [Argument](../articles/spatial-cutoff-moments.md#section-weighted-interface) |
| [L76](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SpatialMoments/Defs.lean) | For the all-closed profile, the spatial moment equals the weight at zero; infinite weights are allowed. | [Argument](../articles/spatial-cutoff-moments.md#section-weighted-interface) |

## Percolation/Bond/Multipoint/Defs

| Source line | Kind | Definition or target |
|---|---|---|
| [L46](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Structure | Trivalent tree with k labelled leaves and k-2 internal vertices. |
| [L53](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Object | Equivalence by graph isomorphisms fixing all leaf labels. |
| [L61](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Object | Quotient of represented trees by that equivalence. |
| [L69](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Object | Nonnegative tree weight summed over internal positions, using a chosen quotient representative. |
| [L78](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Target proposition AFH6 | The countable multipoint tree-graph inequality for k>=2, allowing repeated marked positions. |
| [L220](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Object Y4H4 | Recursive three-part distance on a finite metric space, with diameter squared as the base case. |
| [L257](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Object CS13 | Minimum rooted-tree sweep product over parent maps whose iterates reach the root. |

| Source line | Proved contract | Exposition |
|---|---|---|
| [L84](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | Two represented tree shapes agree exactly when there is a graph isomorphism fixing the labelled leaves. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L91](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | If every two represented graphs are equal, the tree-shape quotient is a subsingleton. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L116](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | The single-edge graph supplies the trivalent shape with two labelled leaves. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L126](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | The three-leaf star supplies the trivalent shape with three labelled leaves. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L154](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | The set of two-leaf shapes is nonempty. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L157](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | The set of three-leaf shapes is nonempty. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L161](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | There is exactly one two-leaf shape. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L188](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | There is exactly one three-leaf shape. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L267](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | The recursive three-part distance of a pair is its squared distance, also when the two points coincide. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |
| [L279](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Multipoint/Defs.lean) | The sweep product of two distinct points is their squared distance. | [Argument](../articles/multipoint-trees.md#section-shape-interface) |

## Boundaries of the interface results

The four tagged cutoff propositions are targets, despite their tag annotations. The API proves elementary monotonicity and comparison facts, and an inverse-square summability witness in dimension one. It does not prove all four targets, nor general row summability for every additive group norm. The derivative target excludes the corner radius but does not require a positive radius: below the positive displacement distance the cutoff is locally constant zero. The deficit target's inside-cutoff premise already forces positive radius. The twelve frozen articles, including cutoff-families, are unchanged.

Restoration measurability does not prove preservation of the bond law or independence after an adaptive exposure. The four correlation propositions allow profiles taking the values zero and one and nonnegative extended-valued functionals, provided the cluster compositions are measurable and the functionals increasing. The upper covariance comparison is written additively, avoiding subtraction of infinite quantities. Constant-functional witnesses and the coincident-root gap witness do not establish the general propositions.

The spatial-moment identity is Tonelli for countably many vertices and arbitrary nonnegative weights. It needs no finite moment, transitivity or finite susceptibility. It supplies no spatial derivative identity or ratio normalization.

The multipoint module constructs tree shapes and proves the two- and three-leaf counts. It does not prove the general double-factorial enumeration, representative-independence of the weight, or the multipoint inequality. The geometric definitions take minima over finite candidate families, with a zero fallback when the family is empty; the three-part recursion has a checked decreasing-cardinality argument. In the sweep definition the parent-iterate witness allows iteration zero, so the set used at a non-root vertex includes that vertex as well as its descendants and parent. This agrees with the intended diameter factor. Only the displayed pair evaluations are proved here, not a general comparison between the two geometric quantities.

## Provenance

The long-range file records partial adaptation of KernelGeometry.lean, and the correlation file adaptation of TwoClusterGap.lean and Hrest.lean, from yujinhkim/lrp at d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc. Their headers record Apache-2.0 attribution and an earlier origin not independently verified here. The correlation targets now use arbitrary probability profiles, including endpoint values. The spatial-moment file identifies its mathematical antecedent but supplies a new countable extended-value interface in place of the earlier finite real-valued one. The multipoint file records new interface work. No new paper erratum is inferred from these declarations, and no compiled association or independent correspondence certification is claimed.
