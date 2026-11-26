# Integer-line and zero-one examples at caed44f

This inventory records **18 explicit named public theorems in two modules** at private lrp merged source caed44fe69ae18235ca1b7adc3b8a072bf05b7ea. Both complete source files were read. Private helpers and anonymous examples are excluded; neither module adds a definition or an Input.

The exposition preserves JK7V, ZH13, 1J3B and the frozen finite-host statement KB1L. It adds the source's decreasing-event recurrence proof and explains the line-plus-root realization, including its endpoints and unconstrained line chords. These are source-inspected occurrences with pending correspondence, not compiled tag associations.

## Models/LongRange/OneDimensional

| Source line | Contract | Exposition |
|---|---|---|
| [L34](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | Membership of a pair in a translated configuration is equivalent to membership of its translated-back pair. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L48](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | A cut at k after translation by g is a cut at k−g before translation. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L60](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | Cuts unbounded to the right form a measurable event on integer configurations. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L72](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | Cuts unbounded to the left form a measurable event on integer configurations. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L86](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | A fully translation-invariant profile whose cut probabilities have one strictly positive lower bound has cuts arbitrarily far to the right with probability one. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L126](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | Under the same profile and uniform positive cut bound, cuts occur arbitrarily far to the left with probability one. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L166](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | For any configuration, cuts at l < x <= r confine the cluster of x to the finite integer interval (l,r]. | [Argument](../articles/displacement-kernels.md#section-line-cuts) |
| [L178](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | For finite nonnegative radial intensities with summable r J(r), at each finite beta >= 0, almost surely every cluster is finite simultaneously. The radial identity includes diagonal pairs. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L228](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | Under the same radial and weighted-summability hypotheses, every rooted critical intensity is infinite. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |
| [L245](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/LongRange/OneDimensional.lean) | Under the same radial and weighted-summability hypotheses, the global critical intensity is infinite. | [Argument](../articles/displacement-kernels.md#section-cut-recurrence) |

## Models/ZeroOneExamples

| Source line | Contract | Exposition |
|---|---|---|
| [L35](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | If all nearest-neighbour line bonds are open, every line vertex is reachable from line zero, regardless of other open pairs. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L49](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | Under that deterministic line-opening hypothesis, the cluster of line zero is infinite. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L57](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | On the integer line plus an extra root, unit line-bond probabilities, root-to-zero probability p, and zero probabilities on other root-line pairs give global percolation probability one and root percolation probability p. Extra line bonds and diagonals are unrestricted. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L107](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | Every p in [0,1] is realized as a root infinite-cluster probability in a countable independent-bond model with global infinite-cluster probability one. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L129](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | On any finite vertex type, every cluster is finite in every configuration. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L133](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | On any finite vertex type, including the empty type, the global infinite-cluster event is empty. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L139](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | Every finite nonnegative intensity kernel on a finite vertex type has infinite global critical intensity. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |
| [L149](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/ZeroOneExamples.lean) | Every such finite-vertex kernel has infinite rooted critical intensity at every chosen root. | [Argument](../articles/infinite-cluster-zero-one.md#section-line-root-model) |

## Scope and correspondence

The one-dimensional module assumes full profile translation invariance for cut recurrence, and a radial kernel identity on every pair for its intensity application. The graph statements allow arbitrary diagonal values after erasure, but this is an additional argument rather than the literal exported hypothesis. The weighted first moment is a real summability condition; its zero term vanishes regardless of the finite value of J(0). Each finite beta has one full-measure event on which all roots have finite clusters. This does not specify one event shared across all beta under a coupling.

The cut proof uses continuity from above followed by the translation zero-one law, not independence of cuts or a claim of positive spatial density. Its anonymous witnesses are the r^{-3} kernel (with totalized inverse at zero) and the nearest-neighbour kernel. It does not settle the marginal r^{-2} percolation regime. The earlier [cut-product inventory](sources/perclib-5d6efa8-line-cuts.md) remains separate.

The prescribed-root source uses a doubly infinite line whereas the earlier wiki proof uses a ray. Both realize the same interior-p assertion. The concrete source additionally allows p = 0 and p = 1 and arbitrary probabilities on non-nearest-neighbour line pairs and loops. The almost-sure argument uses a countable intersection for the probability-one line bonds and simultaneous exclusion of probability-zero root bonds. Its witness chooses p = 1/2.

Finite-host statements require only a finite vertex type, not a finite-degree infinite host. The global result includes the empty type; the rooted result has an explicit root. Both thresholds are infima of empty sets of finite intensities, hence infinity. The source's finite witness uses three vertices and a unit kernel. No large-component scaling claim follows.

No new published-paper error is identified. Existing errata remain unchanged. The [Train 5 map](sources/perclib-caed44f.md) records the remaining modules; source inspection does not itself update formal status.
