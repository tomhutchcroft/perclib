# Binary-tree laws and the critical arm at caed44f

This inventory records **20 explicit named public theorems** in three modules at private lrp merged source caed44fe69ae18235ca1b7adc3b8a072bf05b7ea: nine exact connection/susceptibility/survival results, seven geometry and critical-arm results, and four finite-shape/Catalan results. Private lemmas, imports and anonymous examples are excluded. No new definitions are introduced in these modules.

The [binary-tree article](../articles/binary-tree-percolation.md) preserves its earlier statements CQYY, 9K6O and NDIC. New sections give the direct word-sum, fixed-point, reciprocal-increment and shape-bijection arguments. These source occurrences remain pending; a source comment referring to a wiki tag is not a compiled association or a fingerprint-bound correspondence approval. The [earlier 23-row inventory](sources/perclib-5d6efa8-trees.md) concerns the separate geometry and depth-recursion modules and remains valid.

The common probability model has vertices that are finite words, probability p on tree edges and zero on every other non-diagonal pair. Diagonal parameters are arbitrary except for the critical-arm exports that explicitly use the canonical profile. The root is the empty word, not a vertex of degree three in an unrooted regular tree.

## BinaryTree

| Source line | Contract | Exposition |
|---|---|---|
| [L51](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | For any finite branching number k, the root-to-word connection probability is p to the word length; all p in [0,1] and arbitrary diagonal marginals. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L114](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | The extended sum of r to the word length over words on k letters equals the geometric series with ratio kr, for every nonnegative extended r and every k >= 0. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L132](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | The root susceptibility on the k-ary tree is the extended inverse of 1−kp, with truncated subtraction; it is infinite when kp >= 1. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L142](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | On the binary tree, for p < 1/2 the root susceptibility is the real reciprocal (1−2p)^{-1}, embedded in the nonnegative extended reals. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L155](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | At and above p = 1/2, binary root susceptibility is infinite. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L170](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | At and below p = 1/2, the binary root cluster is finite almost surely. | [Argument](../articles/binary-tree-percolation.md#section-branching) |
| [L187](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | For 1/2 < p <= 1, the binary root survival probability is 1−((1−p)/p)^2; the positive fixed point is selected by the depth-sequence lower bound. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L299](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | Binary root survival is positive exactly when p > 1/2. | [Argument](../articles/binary-tree-percolation.md#section-branching) |
| [L317](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTree.lean) | Binary root susceptibility is finite exactly when p < 1/2. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |

## BinaryTreeArm

| Source line | Contract | Exposition |
|---|---|---|
| [L45](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | The k-ary word graph is acyclic for every natural k; descendant sets show every edge is a bridge. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L78](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | Every word is connected to the empty word, including the singleton graph for k = 0. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L90](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | For every finite k and p in [0,1], all-pairs connection probability is p to the host graph distance; non-tree non-diagonal pairs have probability zero and diagonals are arbitrary. | [Argument](../articles/binary-tree-percolation.md#section-tree-sums) |
| [L129](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | Any real sequence starting at one and satisfying x_(n+1) = x_n−x_n^2/4 has n x_n tending to four. Positivity and bounds are proved, not assumed. | [Argument](../articles/binary-tree-percolation.md#section-arm-reciprocals) |
| [L203](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | The ancestral-path event at depth zero has probability one under the canonical critical binary profile. | [Argument](../articles/binary-tree-percolation.md#section-arm-reciprocals) |
| [L215](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | For that profile, the real-valued depth probabilities satisfy r_(n+1) = r_n−r_n^2/4. | [Argument](../articles/binary-tree-percolation.md#section-arm-reciprocals) |
| [L249](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeArm.lean) | For that profile and the ancestral-path depth event, n r_n tends to four. | [Argument](../articles/binary-tree-percolation.md#section-arm-reciprocals) |

## BinaryTreeCatalan

| Source line | Contract | Exposition |
|---|---|---|
| [L237](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeCatalan.lean) | For a configuration contained in the raw tree edge set and a finite root-containing set closed under taking parents, equality with the root cluster is equivalent to open internal edges and closed child-boundary edges. | [Argument](../articles/binary-tree-percolation.md#section-word-shapes) |
| [L278](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeCatalan.lean) | Every such shape C has probability p^{card(C)−1}(1−p)^{card(C)+1} under the supported homogeneous tree profile, allowing arbitrary diagonal marginals. | [Argument](../articles/binary-tree-percolation.md#section-word-shapes) |
| [L435](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeCatalan.lean) | For n >= 1, the probability of a finite root cluster of cardinality n is Cat(n)p^{n−1}(1−p)^{n+1}. | [Argument](../articles/binary-tree-percolation.md#section-word-shapes) |
| [L566](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/BinaryTreeCatalan.lean) | The same finite-size probability is [binom(2n,n)/(n+1)]p^{n−1}(1−p)^{n+1}, with p in [0,1] and 0^0 = 1. | [Argument](../articles/binary-tree-percolation.md#section-catalan) |

## Scope and proof correspondence

The root connection and geometric-sum results allow k = 0 and k = 1. At k = 0 there is only the root, whose contribution is one even when p = 0. The scalar sum also allows r = infinity; the source uses the nonnegative extended conventions 0 times infinity = 0 and r^0 = 1. A finite real weight suffices for the probability application. The extended susceptibility inverse has truncated subtraction, so it is infinite for kp >= 1, not a negative reciprocal. The all-pairs connection identity uses host distance; only the root susceptibility is evaluated by counting k^n words at depth n.

The deterministic shape lemma assumes the entire raw configuration lies in the tree edge set, so it is loop-free. The probability proof first erases the diagonals without changing the cluster event and then uses almost-sure tree support. Its finite internal and boundary coordinate sets are disjoint and have n−1 and n+1 elements. The final size event explicitly conjoins finiteness with the natural cardinality condition. The displayed masses are unconditioned; above criticality their sum is less than one, and at p = 1 every finite-size mass vanishes.

The shape count uses mathlib's finite set of ordered binary trees with n nodes and its Catalan cardinality theorem, followed by the central-binomial identity for the explicit formula. The new source proves a size-preserving bijection with finite parent-closed word sets. This inventory records how those imported results enter the argument, not a new independent audit of the mathlib Catalan development. The article's earlier generating-function derivation gives the mathematical count separately. The module header cites Grimmett's second edition as model provenance without a precise locator; this batch does not claim a fresh edition-specific reading of that book.

The critical-arm exports use the canonical half-open tree profile and the finite ancestral-witness event. The earlier tree support argument identifies this event almost surely with reaching the specified depth. The scalar recursion theorem proves positivity and convergence internally; no general Galton–Watson survival asymptotic is imported. The article's two-sided finite-n bounds follow from the same reciprocal sum and are explanatory consequences, not extra exported theorem rows.

The exact-law source includes endpoint witnesses at p = 0, 1/2 and 1. The arm source checks r_1 = 3/4, r_2 = 39/64 and the adjacent-vertex two-point formula. The Catalan source checks cluster sizes one and two. These anonymous examples are not included in the count of 20. None of the three modules exports the critical volume Stirling equivalents, the joint near-critical cutoff approximation or the finite-cluster moment asymptotics. Those remain additional wiki deductions with separate correspondence requirements.

This inspection identifies no new published-paper error and changes no provisional erratum. The remaining Train 5 modules are listed in the [additions map](sources/perclib-caed44f.md); neither this inventory nor the cumulative count certifies complete source coverage.
