# Product laws, blocks and transcript contracts at 5d6efa8

This inventory covers all **32 named public theorems across six modules**: four product-law construction results, three finite-cylinder results, seven block-independence results, five determined-event results, six transcript results and seven relabelling results. Private `lrp` revision 5d6efa862d99e11fb1f01619be7700b85c1c8f7b, inspected 16 November 2026. Imported declarations and anonymous witnesses are excluded. Named theorems with attributes on the same line are included. These are source inventories, not compiled tag associations or independent correspondence verdicts.

## The configuration law

| Source line | Contract | Exposition |
| --- | --- | --- |
| [ProdBernoulli.lean L49](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulli.lean) | The arbitrary-profile configuration law agrees with the weighted Dirac-product construction. | [Argument](../articles/profile-continuity.md#section-product-law) |
| [ProdBernoulli.lean L61](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulli.lean) | The law is equivalently the pushforward of the predicate-valued product under the measurable identification with open sets. | [Argument](../articles/profile-continuity.md#section-product-law) |
| [ProdBernoulli.lean L68](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulli.lean) | The profile equal to p on a fixed subset and zero elsewhere agrees with the homogeneous set-Bernoulli construction on that subset. | [Argument](../articles/profile-continuity.md#section-product-law) |
| [ProdBernoulli.lean L77](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulli.lean) | A constant profile is the homogeneous construction on the whole coordinate set. | [Argument](../articles/profile-continuity.md#section-product-law) |

## Finite cylinders

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Cylinder.lean L38](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Cylinder.lean) | The all-open event of a finite coordinate set has probability the product of its individual probabilities, on arbitrary ambient sets. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [Cylinder.lean L56](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Cylinder.lean) | The packaged finite-cylinder target holds for every index type. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [Cylinder.lean L60](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Cylinder.lean) | The one-coordinate marginal is its assigned opening probability. | [Argument](../articles/profile-continuity.md#section-restriction) |

## Independent restrictions

| Source line | Contract | Exposition |
| --- | --- | --- |
| [ProdBernoulliIndependence.lean L29](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | Coordinate membership variables are mutually independent. | [Argument](../articles/finite-transcripts.md#section-blocks) |
| [ProdBernoulliIndependence.lean L44](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | The open-coordinate events are mutually independent, including zero/one profiles. | [Argument](../articles/finite-transcripts.md#section-blocks) |
| [ProdBernoulliIndependence.lean L50](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | Restrictions to two disjoint sets, as predicate-valued tuples, are independent. | [Argument](../articles/finite-transcripts.md#section-blocks) |
| [ProdBernoulliIndependence.lean L57](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | The same restrictions, as open subsets of the two blocks, are independent. | [Argument](../articles/finite-transcripts.md#section-blocks) |
| [ProdBernoulliIndependence.lean L65](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | Measurable observables of two disjoint block restrictions are independent. | [Argument](../articles/finite-transcripts.md#section-blocks) |
| [ProdBernoulliIndependence.lean L74](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | Measurable events on two disjoint blocks have a factored joint probability. | [Argument](../articles/finite-transcripts.md#section-blocks) |
| [ProdBernoulliIndependence.lean L83](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProdBernoulliIndependence.lean) | Finite disjoint blocks are a specialization without any restriction on the ambient index set. | [Argument](../articles/finite-transcripts.md#section-blocks) |

## Determined events

| Source line | Contract | Exposition |
| --- | --- | --- |
| [DeterminedIndependence.lean L31](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | Extending an open set on a block by closed coordinates outside it is measurable. | [Argument](../articles/finite-transcripts.md#section-determined-events) |
| [DeterminedIndependence.lean L51](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | A determined ambient set is the restriction preimage of its closed-extension preimage; this set identity requires no measurability. | [Argument](../articles/finite-transcripts.md#section-determined-events) |
| [DeterminedIndependence.lean L67](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | Measurable ambient events determined by two disjoint blocks have a factored joint probability. | [Argument](../articles/finite-transcripts.md#section-determined-events) |
| [DeterminedIndependence.lean L80](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | A finite intersection of events determined by subsets of a common block is determined by that block. | [Argument](../articles/finite-transcripts.md#section-determined-events) |
| [DeterminedIndependence.lean L92](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterminedIndependence.lean) | A finite family of measurable events determined by pairwise disjoint blocks has joint probability the product of its probabilities. | [Argument](../articles/finite-transcripts.md#section-determined-events) |

## Finite adaptive transcripts

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Transcript.lean L26](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Exploration/Transcript.lean) | Sampling an arbitrary injective coordinate family gives the product law on the sampled index type. | [Argument](../articles/finite-transcripts.md#section-block-families) |
| [Transcript.lean L34](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Exploration/Transcript.lean) | A finite transcript at distinct coordinates has the product of the bit probabilities. | [Argument](../articles/finite-transcripts.md#section-fixed) |
| [Transcript.lean L52](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Exploration/Transcript.lean) | A finite transcript factors from every measurable event on its unqueried complement, without a positivity assumption. | [Argument](../articles/finite-transcripts.md#section-fixed) |
| [Transcript.lean L81](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Exploration/Transcript.lean) | A deterministic adaptive answer string is exactly its fixed-string transcript cylinder; repeated queries are permitted in this identity. | [Argument](../articles/finite-transcripts.md#section-adaptive) |
| [Transcript.lean L112](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Exploration/Transcript.lean) | If the coordinates along the fixed answer string are distinct, its adaptive probability has the product formula. | [Argument](../articles/finite-transcripts.md#section-adaptive) |
| [Transcript.lean L129](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Exploration/Transcript.lean) | The actual adaptive answer event factors from every measurable event on the complement of that string’s distinct query coordinates. | [Argument](../articles/finite-transcripts.md#section-conditioning) |

## Relabelling

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Reindexing.lean L22](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | Relabelling configurations by a coordinate bijection is measurable. | [Argument](../articles/product-symmetries.md#section-transport) |
| [Reindexing.lean L28](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | Relabelling pushes the product law to the inverse-transported profile. | [Argument](../articles/product-symmetries.md#section-transport) |
| [Reindexing.lean L50](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | The measurable-event preimage probability equals its transported-profile probability. | [Argument](../articles/product-symmetries.md#section-transport) |
| [Reindexing.lean L56](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | The same measurable-event identity holds for real-valued probabilities, including endpoint profiles. | [Argument](../articles/product-symmetries.md#section-transport) |
| [Reindexing.lean L63](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | A profile-preserving coordinate permutation leaves the entire product law invariant. | [Argument](../articles/product-symmetries.md#section-invariance) |
| [Reindexing.lean L73](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | A vertex bijection transports the profile on unordered pairs, including diagonal coordinates. | [Argument](../articles/product-symmetries.md#section-bonds) |
| [Reindexing.lean L86](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Reindexing.lean) | A vertex permutation preserving the entire pair profile preserves the configuration law, including its diagonals. | [Argument](../articles/product-symmetries.md#section-bonds) |

## Definitions and scope

The canonical tagged product-law definition at ProdBernoulli line 44 and its probability-measure instance are outside the theorem count. The Cylinder target definition at line 32 merely packages the finite all-open identity; its realization is counted at line 56. No second configuration law is introduced. The weighted representation, predicate/open-set identification and subset-supported homogeneous specialization are explained in the existing canonical-law section. For uncountable ambient coordinates, the subset-supported construction is a measurable pushforward, not an unproved assertion that an uncountable intersection of coordinate constraints is measurable.

All six modules allow arbitrary ambient coordinate sets. Blocks and the injectively sampled index family may be infinite or uncountable; their observables and events must have the stated measurability. The finite transcript itself has finitely many coordinates, and its product formula requires distinctness. The adaptive cylinder identity permits repeats, whereas the adaptive probability product and its factorization require distinct queries along the fixed string. Conditional division by a positive transcript probability is an expository consequence; the source factorization also applies to null transcripts. No independence between the random queried set and its answers is asserted.

FH29 factors a determined measurable ambient event through a fixed restriction using measurable closed extension. Its underlying set identity holds even for a nonmeasurable ambient set, but the probability statement does not drop measurability. The finite intersection helper establishes determination by the union block used in the induction. Empty blocks, empty transcripts and endpoint probabilities are permitted. These fixed blocks are distinct from witnesses chosen after observing a configuration.

Coordinate relabelling transports the profile by the inverse bijection. A genuine symmetry requires preservation of that profile. Vertex relabelling acts on every unordered-pair coordinate, including loops; the pair-law invariance theorem assumes invariance of diagonal probabilities too. Erasing loops in graph observables is a separate argument, already recorded in LNKT. Source examples include mixed zero/one profiles, empty coordinate sets, infinite disjoint integer blocks, a loop/non-loop transcript, coordinate swaps and nonzero constant pair profiles.

The earlier source records remain pinned to their own revisions. This inventory links the current common source pin, including same-line tagged declarations at Transcript line 81 and Reindexing line 73; it does not silently replace older locators. No prior article statement, source record, permanent tag or erratum is changed, and no new independent correspondence verdict is claimed.
