# Core definitions, model bounds and cluster-volume counting at 22d8485

This inventory covers the remaining **thirteen complete modules**, totalling **1,741 lines**, at private lrp merged source 22d8485da86b12aa41d1985b07939d2e6e612e26. Ten files have **77 named public theorems**; three contain definitions, a standard-Borel instance or tag infrastructure without named theorem declarations. Those three are classified separately below and contribute no theorem rows. The new volume-tail assertion is TEYS; most other results already have full exposition, retained here without duplication.

## Basic

| Source line | Contract | Exposition |
|---|---|---|
| [L11](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Basic.lean) | For real a and b, twice their product is at most the sum of their squares; expand the nonnegative square of a minus b. | Nonnegativity of the square of a minus b. |

## Models/FiniteGraph

| Source line | Contract | Exposition |
|---|---|---|
| [L40](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FiniteGraph.lean) | On a finite simple host with degrees at most Delta, edge probabilities at most p and zero off-host probabilities give the susceptibility bound with row Delta p below one; diagonals are unrestricted. | [Argument](../articles/walk-kernels.md#section-bonds) |
| [L69](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FiniteGraph.lean) | For n vertices with constant off-diagonal probability p, the row is exactly (n minus 1) p, giving the corresponding susceptibility bound at each root. | [Argument](../articles/walk-kernels.md#section-bonds) |
| [L83](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FiniteGraph.lean) | On one vertex susceptibility equals one for every diagonal probability. | [Argument](../articles/walk-kernels.md#section-bonds) |

## Models/TranslationInvariant

| Source line | Contract | Exposition |
|---|---|---|
| [L40](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | An even finite nonnegative displacement kernel descends to unordered pairs on an arbitrary additive group; commutativity is not assumed. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L49](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | Every off-diagonal intensity row equals the displacement-kernel sum away from zero, as an extended nonnegative sum. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L59](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | That off-diagonal row is bounded by the total kernel mass, which also includes zero. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L67](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | On a countable additive group, an off-diagonal probability-row bound m below one gives susceptibility at most the inverse of one minus m. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L77](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | A finite bound M on total intensity-kernel mass gives the small-intensity susceptibility bound when beta M is below one. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L85](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | The same total-mass hypothesis bounds the global critical intensity below by the extended inverse of M. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L93](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | The same bound holds for every rooted critical intensity. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L104](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | A unit point mass has extended sum one on any type with decidable equality; no group assumption is retained. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L111](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | The sum of unit masses at a and minus a has total mass two, even if the two points coincide. | [Argument](../articles/displacement-kernels.md#section-probability) |
| [L118](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/TranslationInvariant.lean) | The two-point intensity kernel is even, including elements of order two and zero. | [Argument](../articles/displacement-kernels.md#section-probability) |

## Percolation/Bond/Basic

| Source line | Contract | Exposition |
|---|---|---|
| [L91](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Open-graph adjacency is membership of the unordered pair together with distinct endpoints. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L96](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Configuration inclusion implies inclusion of the simple open graphs. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L100](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | The empty configuration has no open graph edge. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L103](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Membership of the connection event is graph reachability. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L106](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Cluster membership is membership of the corresponding connection event. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L111](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Self-connection is the whole configuration space, including its length-zero witness. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L115](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Connection is symmetric. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L120](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Connection is transitive by concatenation. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L125](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Connection is increasing in the configuration. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L131](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | An open non-diagonal pair connects its endpoints. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L137](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | In the empty configuration two vertices connect exactly when they are equal. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L142](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Every root belongs to its own cluster. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L146](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Cluster membership is symmetric in the root and tested vertex. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L150](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Each cluster in the empty configuration is the root singleton. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L155](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | The extended cluster cardinality is at least one. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L159](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | The diagonal two-point value is one for every profile. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L163](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | The two-point function is symmetric. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L167](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Every two-point value is at most one. | [Argument](../articles/cluster-partitions.md#section-open-pairs) |
| [L174](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | A fixed finite vertex-list walk event is measurable without ambient countability. | [Argument](../articles/cluster-partitions.md#section-random-set) |
| [L190](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Connection is the union of finite-list walk witnesses with the required final vertex, as a deterministic identity. | [Argument](../articles/cluster-partitions.md#section-random-set) |
| [L203](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | Connection events are measurable on a countable vertex type. | [Argument](../articles/cluster-partitions.md#section-random-set) |
| [L217](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | An infinite root cluster is equivalent to escape from every finite vertex set, without a countability hypothesis on this set identity. | [Argument](../articles/cluster-partitions.md#section-random-set) |
| [L233](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Basic.lean) | The infinite-root-cluster event is measurable on a countable vertex type. | [Argument](../articles/cluster-partitions.md#section-random-set) |

## Percolation/Bond/Intensity

| Source line | Contract | Exposition |
|---|---|---|
| [L44](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | At zero finite intensity the entire profile is zero, including diagonal coordinates. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L51](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | The intensity profile is coordinatewise nondecreasing in its finite nonnegative parameter. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L61](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Each opening probability is at most beta times its finite nonnegative intensity. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L70](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | A uniform off-diagonal intensity-row bound M gives a probability-row bound beta M, without vertex countability. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L90](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | On countable vertices, beta M below one gives the susceptibility upper bound at every root. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L97](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Under the same strict row condition susceptibility is finite. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L104](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Under the same condition the probability that any infinite cluster exists is zero. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L115](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | In particular the infinite-cluster probability at a specified root is zero. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L125](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Any finite parameter with positive global infinite-cluster probability is at least the extended inverse of M. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L135](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | The global threshold is at least the extended inverse of M, including an empty percolation-parameter set. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L144](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Every rooted threshold has the same lower bound. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L154](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Zero off-diagonal intensity rows give infinite global threshold. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L163](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | Zero off-diagonal intensity rows give infinite threshold at every root. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L173](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | With zero off-diagonal rows susceptibility is one at every finite parameter and root. | [Argument](../articles/walk-kernels.md#section-intensity) |
| [L183](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity.lean) | At parameter zero susceptibility is one without any row bound. | [Argument](../articles/walk-kernels.md#section-intensity) |

## Percolation/Bond/Tags/SubcriticalBound

| Source line | Contract | Exposition |
|---|---|---|
| [L20](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | 53Z9 bundles the susceptibility bound at every root and simultaneous almost-sure finiteness, under a uniform off-diagonal probability-row bound below one. | [Argument](../articles/subcritical-bound.md#section-statement) |
| [L28](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | YFF7 bundles existence of a finite simple-path certificate and its exact distinct-coordinate product probability; no ambient countability is assumed. | [Argument](../articles/subcritical-bound.md#section-proof-paths) |
| [L40](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | UMQY bundles the walk-weight recurrence and bound by m to the path length for an arbitrary extended kernel, including infinite m. | [Argument](../articles/subcritical-bound.md#section-proof-recurrence) |
| [L48](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | F12C bundles the full chain from susceptibility through walk weights to the geometric series, retaining countability and the strict row bound. | [Argument](../articles/subcritical-bound.md#section-proof-sum) |
| [L64](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | 012G bundles zero infinite-cluster probability at every root and simultaneous finiteness, assuming finite susceptibility at every root. | [Argument](../articles/subcritical-bound.md#section-proof-finiteness) |
| [L80](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | E771 gives the row bound at every finite nonnegative parameter and the susceptibility conclusion when beta M is below one. | [Argument](../articles/subcritical-bound.md#section-intensity) |
| [L91](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tags/SubcriticalBound.lean) | JZ47 bundles both threshold bounds and the zero-M conclusion, including vanishing of every off-diagonal intensity. | [Argument](../articles/subcritical-bound.md#section-intensity) |

## Percolation/Bond/Tightness/Defs

| Source line | Contract | Exposition |
|---|---|---|
| [L102](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tightness/Defs.lean) | For a singleton observation window the maximum full-cluster intersection is always one, on any vertex type. | [Argument](../articles/window-tightness-interfaces.md#section-observables) |
| [L111](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Tightness/Defs.lean) | For that singleton the integer tightness quantile is exactly two, for every profile and without ambient countability. | [Argument](../articles/window-tightness-interfaces.md#section-observables) |

## Percolation/Bond/TreeCounting

| Source line | Contract | Exposition |
|---|---|---|
| [L46](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | The number of distinct vertices visited by a walk is at most one more than its number of distinct unordered edges. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L62](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | A finite walk from inside a set to outside it crosses an edge from the set to its complement. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L72](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | A two-step detour through an adjacent vertex can be inserted at a visited vertex, retaining all previous visited vertices. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L98](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | A root cluster with at least n plus one vertices supplies, for each k at most n, a closed open walk of length 2k visiting at least k plus one vertices. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L147](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | On a locally finite host with degrees bounded by Delta, at most Delta to the power m walks of length m join two fixed vertices. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L172](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | On countable vertices, off-diagonal support of the profile on the host implies simultaneous almost-sure containment of all open non-diagonal edges. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L192](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | With host degree bounded by Delta and host probabilities at most p, the probability of root cluster volume at least n plus one is at most (Delta squared times p) to the power n, for every natural n. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |
| [L265](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeCounting.lean) | Summing those tails gives the extended susceptibility bound with denominator one minus Delta squared times p; without the strict inequality the extended right side can be infinite. | [Argument](../articles/bounded-degree-paths.md#section-volume-tail) |

## Percolation/Bond/TreeGraph/Defs

| Source line | Contract | Exposition |
|---|---|---|
| [L30](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeGraph/Defs.lean) | When the middle vertex is the root, the root term of the three-point diagram alone bounds the joint connection probability; no countability is required. | [Argument](../articles/tree-graph.md#section-endpoints) |
| [L49](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/TreeGraph/Defs.lean) | On two vertices with bond probability t, repeated-target joint connection has probability t and its diagram equals t squared plus t, with arbitrary diagonal probabilities. | [Argument](../articles/tree-graph.md#section-endpoints) |

## Percolation/Bond/Wiring/BoundaryLaw

| Source line | Contract | Exposition |
|---|---|---|
| [L23](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Wiring/BoundaryLaw.lean) | Reading an injective family of pair coordinates has the product of the selected Bernoulli marginals, without countability. | [Argument](../articles/boundary-laws.md#section-boundary) |
| [L31](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Wiring/BoundaryLaw.lean) | Fixing one endpoint makes unordered-pair indexing by the other endpoint injective; the fixed endpoint need not lie in the domain. | [Argument](../articles/boundary-laws.md#section-boundary) |
| [L41](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Wiring/BoundaryLaw.lean) | An injectively indexed family of disjoint coordinate blocks is mutually independent as full predicate tuples, with no countability hypothesis. | [Argument](../articles/boundary-laws.md#section-boundary) |
| [L65](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Wiring/BoundaryLaw.lean) | On countable vertices, the boundary indicators at internal vertices and all internal pair coordinates are mutually independent; the domain may be infinite. | [Argument](../articles/boundary-laws.md#section-boundary) |
| [L129](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Wiring/BoundaryLaw.lean) | For any root, the event that all coordinates from it to the exterior are closed has probability equal to the product of their closed probabilities. | [Argument](../articles/boundary-laws.md#section-boundary) |
| [L150](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Wiring/BoundaryLaw.lean) | Under explicit finite nonnegative real intensities, a nonnegative real parameter, exterior summability and agreement of exterior probabilities, the closed-boundary probability is the exponential of minus the total exterior intensity times the parameter. | [Argument](../articles/boundary-laws.md#section-intensity) |

## Files without named theorem declarations

These three files have been read in full. Their absence from the theorem-row total is intentional.

| Module | Source | Role and exposition |
|---|---|---|
| Meta/Tag | [L20](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Meta/Tag.lean) | The tag parser requires a four-character string using digits or uppercase letters. Its comment assigns cross-module uniqueness checking to the compiled manifest; the parser itself checks the string syntax, not mathematical correspondence. |
| Probability/Defs | [L26](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Defs.lean) | The named standard-Borel instance transports a Polish realization of countable predicate tuples to the existing measurable configuration space. The [metric proof](../articles/finite-transcripts.md#section-standard-borel) gives the same mathematical property; the empty index type and conditioning on one bond are included in source examples. |
| Percolation/Bond/Intensity/Defs | [L31](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Intensity/Defs.lean) | The finite nonnegative intensity profile and the rooted/global thresholds are defined at lines 31, 41 and 47. Thresholds are extended-valued infima of finite percolating parameters, with empty infimum infinity; [the intensity account](../articles/walk-kernels.md#section-intensity) keeps them distinct from susceptibility thresholds. |

## Definitions within the theorem-bearing files

Bond/Basic uses the existing product measure on sets of unordered pairs. Its Config abbreviation at line 60, law at 64 and probability-measure instance at 66 are distinct from its graph at 71, connection event at 74, cluster at 78, two-point function at 81 and extended susceptibility at 84. Graph loops are discarded; their coordinates remain in the product law. The [cluster-convention account](../articles/cluster-partitions.md#section-open-pairs) and [measurability proof](../articles/cluster-partitions.md#section-random-set) distinguish arbitrary-set deterministic identities from countability-dependent probabilistic claims. The source retains its attribution for the adapted measurability arguments.

Tightness/Defs defines the maximum and rooted intersections at lines 56 and 60, the integer quantile at 64, and two proposition-valued targets at 70 and 89. These target definitions do not prove themselves. The [interface article](../articles/window-tightness-interfaces.md#section-properties) preserves the constants, strict and non-strict tails, all ambient roots and the corrected k at least one range; its appended account follows the later implementation. TreeGraph/Defs similarly defines the L82Q proposition at line 25 and proves only the two elementary witnesses listed above. Its general proof belongs to the later [branch-point implementation](../articles/tree-graph.md#section-source-branch). Definitions, named instances, syntax extensions, private lemmas and anonymous examples are excluded from the 77 public theorem rows.

## Scope retained in the model applications

The finite-graph model uses exactly n minus one possible neighbours on a complete graph. Its susceptibility criterion is not a characterization of cluster finiteness: every cluster on a finite vertex type is finite at every parameter. The empty vertex type has no root, while a single vertex has susceptibility one regardless of its loop coordinate.

The translation module assumes an additive group, not necessarily an Abelian group. The article's multiplicative convention makes the corresponding right-translation action explicit. The source intensity bounds use total kernel mass, including the identity; the article's off-diagonal version is sharper when the identity mass is positive. The point-mass and two-point identities keep coincident support points: if a equals minus a, the contributions add to two rather than collapse to one. The source's lattice witness uses one coordinate axis, not all nearest-neighbour directions.

The subcritical wrappers preserve the full bundles under 53Z9, YFF7, UMQY, F12C, 012G, E771 and JZ47. The original frozen article is unchanged. In particular, the all-roots almost-sure conclusion uses countability; the deterministic walk recurrence allows infinite weights; the intensity row bound has no small-parameter premise until susceptibility is deduced; and zero off-diagonal intensity rows give infinite thresholds even with nonzero diagonal intensities. No conclusion at the threshold is inferred.

For the boundary-law module, sampling injective coordinates and independence of whole disjoint blocks do not require countability. Measurability of the exterior existence indicators does. The joint boundary/internal independence theorem indexes boundary roots inside the domain. The separate closed-coordinate product theorem allows a root outside the domain too, in which case it is a statement about the indicated coordinate family and may include a diagonal coordinate; it is not then the internal-root ghost construction. Its exponential formula retains exterior summability and nonnegative finite parameters, avoiding an undefined zero-times-infinity expression. Empty exterior, zero intensity and a probability-one boundary edge are explicit witnesses.

The closed-walk volume proof records distinct edges separately from repeated traversals. Its susceptibility estimate is an extended nonnegative inequality at all parameters, becoming informative when Delta squared times p is below one. The article proves the associated exponential-moment bound as an additional deduction, rather than claiming that it is exported by this module.

## Coverage census and limits

Ten of these thirteen files are byte-identical to the earlier 3c0755b source pin: Basic, Meta/Tag, the two model files, Bond/Basic, both intensity files, Tightness/Defs, BoundaryLaw and Probability/Defs. Their older source records and locators remain unchanged. The subcritical association, TreeCounting and TreeGraph/Defs files were absent at that older pin and have separate source records here.

Cumulative detailed coverage is **1,475 declaration-start locators in 147 theorem-bearing modules across 51 inventories**. The three non-theorem modules classified above complete the source inventory of all **150 tracked PercLib modules** at 22d8485; the separate root import file is not a library module in this census. Coverage is by pinned source contract, not by independent mathematical result: wrappers and later revisions may record related claims. This closes the module-inventory queue, not the paper-reading, proof-quality or fingerprint-bound correspondence-review obligations. No formal status is authored or upgraded, and the provisional errata are unchanged.
