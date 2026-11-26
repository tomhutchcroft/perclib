# Bond association and grouped toolkit statements at 22d8485

This inventory records **23 named public theorems in five complete files**, totalling 641 lines, at private lrp merged source 22d8485da86b12aa41d1985b07939d2e6e612e26. Two files specialize Harris to graph events. Three contain grouped associations for existing wiki tags. The article proofs and all previous tagged statements are retained; the new escape-transfer corollary is EWMP.

## Percolation/Bond/HarrisDecreasing

| Source line | Contract | Exposition |
|---|---|---|
| [L33](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisDecreasing.lean) | Non-connection events are decreasing on arbitrary vertex types. | [Argument](../articles/harris-inequality.md#section-bond-correlation) |
| [L37](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisDecreasing.lean) | On countable vertices two non-connection events are positively correlated. | [Argument](../articles/harris-inequality.md#section-bond-correlation) |
| [L43](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisDecreasing.lean) | A connection and a non-connection event are negatively correlated, with complementary probability one minus the two-point function. | [Argument](../articles/harris-inequality.md#section-bond-correlation) |
| [L51](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisDecreasing.lean) | The extended cluster volume is increasing in the configuration, without countability. | [Argument](../articles/harris-inequality.md#section-bond-correlation) |
| [L57](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisDecreasing.lean) | On countable vertices susceptibility times a connection probability is at most the cluster-volume integral over that connection event, with infinite values allowed. | [Argument](../articles/harris-inequality.md#section-bond-correlation) |

## Percolation/Bond/HarrisLocal

| Source line | Contract | Exposition |
|---|---|---|
| [L32](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisLocal.lean) | Two internal connections in one countable induced domain are positively correlated; the source also assumes the ambient vertex type countable. | [Argument](../articles/harris-inequality.md#section-local-escape) |
| [L43](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisLocal.lean) | Internal two-point probabilities are supermultiplicative through an intermediate vertex in the same domain. | [Argument](../articles/harris-inequality.md#section-local-escape) |
| [L51](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisLocal.lean) | A full connection probability times the escape probability at its second endpoint is bounded by the escape probability at its first endpoint, for any deterministic set. | [Argument](../articles/harris-inequality.md#section-local-escape) |
| [L60](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisLocal.lean) | Escape inside a countable induced domain to a vertex of that domain outside a prescribed set is measurable. | [Argument](../articles/harris-inequality.md#section-local-escape) |
| [L72](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisLocal.lean) | The same escape-transfer inequality holds with both connections restricted to the same induced domain. | [Argument](../articles/harris-inequality.md#section-local-escape) |
| [L87](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/HarrisLocal.lean) | The product of finitely many internal connection probabilities is at most their joint probability, including the empty family. | [Argument](../articles/harris-inequality.md#section-local-escape) |

## Probability/Tags/Harris

| Source line | Contract | Exposition |
|---|---|---|
| [L23](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Harris.lean) | UPFU bundles the three-point lower bound, increasingness and measurability of escape events, and the finite-set escape characterization and regularity of the rooted infinite-cluster event on countable vertices. | [Argument](../articles/harris-inequality.md#section-connections) |

## Probability/Tags/ProductModel

| Source line | Contract | Exposition |
|---|---|---|
| [L19](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/ProductModel.lean) | 6RZ8 bundles measurable inverse coordinate relabellings, their inverse identities, the transported product law and its measurable-event formula, on arbitrary coordinate types. | [Argument](../articles/product-symmetries.md#section-transport) |
| [L33](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/ProductModel.lean) | VEUZ gives law and measurable-event invariance when a coordinate bijection preserves the profile. | [Argument](../articles/product-symmetries.md#section-invariance) |
| [L44](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/ProductModel.lean) | Restriction to any deterministic coordinate subset has its restricted product law, without finiteness or countability. | [Argument](../articles/product-symmetries.md#section-pullback) |
| [L62](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/ProductModel.lean) | EE11 gives the finite injective transcript weight and factorization with a measurable complement event under its restricted law. | [Argument](../articles/finite-transcripts.md#section-fixed) |
| [L79](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/ProductModel.lean) | 56TE gives the conditional quotient for an actual deterministic adaptive transcript, assuming distinct queries along that answer string and strictly positive transcript probability. | [Argument](../articles/finite-transcripts.md#section-conditioning) |
| [L97](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/ProductModel.lean) | 5PAT gives disjoint finite open/closed cylinder products on arbitrary coordinate types, including deterministic probabilities. | [Argument](../articles/product-model.md#section-law) |

## Probability/Tags/Russo

| Source line | Contract | Exposition |
|---|---|---|
| [L24](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Russo.lean) | 71GK bundles forcing, state-independent signed differences, increasing-event pivotality and the closed-pivotal identity; this deterministic wrapper omits coordinate finiteness. | [Argument](../articles/russo-formula.md#section-pivotality) |
| [L44](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Russo.lean) | 7WIO bundles the real-profile polynomial derivative and its integral identification and within-domain probability derivative on a finite coordinate type. | [Argument](../articles/russo-formula.md#section-profile) |
| [L81](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Russo.lean) | WU9R gives both the polynomial and within-domain increasing-event derivatives, with arbitrary signed coordinate velocities. | [Argument](../articles/russo-formula.md#section-events) |
| [L102](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Russo.lean) | 4IHK gives the homogeneous polynomial derivative and within-domain probability derivative, including the probability endpoints. | [Argument](../articles/russo-formula.md#section-events) |
| [L170](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Tags/Russo.lean) | IENL bundles intensity Russo, the closed-pivotal sum, its individual exponential factor and the insertion-increment derivative for arbitrary real observables. | [Argument](../articles/russo-formula.md#section-intensity) |

## Graph-event scope

Non-connection is decreasing, while cluster volume is increasing, without any countability hypothesis. The probabilistic corollaries assume countable vertices for measurability. The volume inequality is in extended nonnegative arithmetic and allows infinite expectation; it is not a signed covariance identity in that case. The two-vertex half-probability examples test the mixed event and volume bounds.

Internal connections use one induced domain. The local module explicitly assumes both ambient and domain countability; this inventory does not silently remove either source hypothesis. Escape is a countable union of internal connections, and concatenation supplies the deterministic inclusion after Harris. The transfer does not require F finite, a root in F, separate domains, disjoint paths or positive probabilities. The empty finite family gives both sides one. The source witnesses include the full domain on natural vertices and escape from the empty set.

## Product associations

Relabelling uses an actual coordinate bijection, with inverse maps and the transported profile composed with that inverse. Invariance requires profile preservation. Restriction to an arbitrary deterministic coordinate subset is a separate law statement, and factorization uses its restricted law for the complement of the transcript range. The conditional transcript wrapper assumes the answer recursion, agreement of the fixed queries with that answer string, injectivity along it and positive transcript mass. It divides only by that positive finite mass. Neither random queried-set independence nor an infinite adaptive transcript is asserted. The mixed zero-one and empty-cylinder witnesses remain included.

## Russo coefficients and domains

The 71GK wrapper explicitly drops finite-coordinate dependence for its deterministic forcing identities. The derivative wrappers require a finite coordinate type. Their polynomial identities do not require the real profile to lie in the probability cube, and coordinate velocities can have either sign. The probability statements instead require agreement with an actual unit-interval profile at the base point and throughout the chosen parameter set. A within-domain derivative predicate can hold at an isolated point without defining a unique derivative; the article retains an accumulation-point assumption for its ordinary derivative interpretation.

IENL includes the state-independent pivotal coefficient, the closed-pivotal coefficient, their coordinatewise relation with exp(-beta J), and the insertion-increment formula for arbitrary real observables. Its private pairing lemmas prove the closed-coordinate factor without division. The original Russo module's source record correctly describes that conversion as an expository deduction from that older module; this wrapper now exports the complete grouped statement. Zero intensity, the homogeneous endpoints and a polynomial evaluated outside the probability cube are witnessed separately. No infinite pivotal-sum formula is inferred.

Cumulative detailed coverage is 1,398 declaration-start locators in 137 modules across 50 inventories. Thirteen older modules remain outside the detailed theorem inventories, including definitions and infrastructure. Imports, private pairing lemmas and anonymous witnesses are excluded from the public row count. None of these source attributes, or this inventory, substitutes for exact compiled evidence and fingerprint-bound correspondence review. No formal status is authored or upgraded.
