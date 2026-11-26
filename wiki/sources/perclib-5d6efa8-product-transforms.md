# Product-transformation contracts at 5d6efa8

This inventory covers all **23 named public theorems** in four modules at private `lrp` revision 5d6efa862d99e11fb1f01619be7700b85c1c8f7b, inspected 16 November 2026. Imported declarations and anonymous witnesses are excluded. The [extended product-symmetries article](../articles/product-symmetries.md#section-characterization) preserves its earlier relabelling, loop-erasure and host-support exposition. Complementation reuses the existing [Harris complement assertion](../articles/harris-inequality.md#section-complement), rather than allocating a duplicate identity.

## Product-law characterization by all-open events

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Characterization.lean L33](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Characterization.lean) | A probability measure with the finite all-open probabilities of a profile is that product law. | [Argument](../articles/product-symmetries.md#section-characterization) |
| [Characterization.lean L40](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Characterization.lean) | Every finite all-open event is measurable. | [Argument](../articles/product-symmetries.md#section-characterization) |
| [Characterization.lean L46](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Characterization.lean) | A measurable pushforward is a specified product law exactly when all finite all-open probabilities match. | [Argument](../articles/product-symmetries.md#section-characterization) |

## Restriction, thinning and superposition

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Superposition.lean L43](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Restriction to an arbitrary coordinate subset has the restricted product law on that subset. | [Argument](../articles/product-symmetries.md#section-pullback) |
| [Superposition.lean L61](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Negating a Bernoulli truth value complements its parameter. | [Argument](../articles/harris-inequality.md#section-complement) |
| [Superposition.lean L73](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Complementing the configuration complements the product profile. | [Argument](../articles/harris-inequality.md#section-complement) |
| [Superposition.lean L89](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Finite all-open events generate the product sigma-algebra. | [Argument](../articles/product-symmetries.md#section-characterization) |
| [Superposition.lean L108](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Finite all-open events form a pi-system. | [Argument](../articles/product-symmetries.md#section-characterization) |
| [Superposition.lean L118](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Two probability laws agreeing on all finite all-open events are equal. | [Argument](../articles/product-symmetries.md#section-characterization) |
| [Superposition.lean L125](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Intersecting independent product configurations multiplies their profiles. | [Argument](../articles/product-symmetries.md#section-superposition) |
| [Superposition.lean L152](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Superposition.lean) | Uniting independent product configurations multiplies closed probabilities. | [Argument](../articles/product-symmetries.md#section-superposition) |

## Deterministic opening, closing and host masking

| Source line | Contract | Exposition |
| --- | --- | --- |
| [DeterministicModification.lean L21](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | Intersection with a fixed set retains its marginals and fixes all other coordinates closed. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L42](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | Union with a fixed set fixes its coordinates open and retains the remaining marginals. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L62](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | Deleting a fixed set fixes its marginals closed and retains the others. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L70](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | For any increasing set, restriction lowers its inverse-image outer measure, without a measurability assumption. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L76](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | For any increasing set, deterministic opening raises its inverse-image outer measure, without a measurability assumption. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L82](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | For measurable increasing events, the masked product profile gives the lower probability comparison. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L90](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | For measurable increasing events, the forced-open product profile gives the upper probability comparison. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L127](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | Masking a bond configuration by a simple host edge set gives the masked product profile. | [Argument](../articles/product-symmetries.md#section-modification) |
| [DeterministicModification.lean L133](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/DeterministicModification.lean) | On countable vertices, masking by a host cannot increase the two-point probability. | [Argument](../articles/product-symmetries.md#section-modification) |

## Injective coordinate pullback

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Transport/Pullback.lean L31](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Pullback.lean) | Sampling independent variables along an injective index map gives the composed product law on any common measurable state space. | [Argument](../articles/product-symmetries.md#section-pullback) |
| [Transport/Pullback.lean L69](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Pullback.lean) | The inverse image of a Bernoulli configuration along an injective coordinate map has the composed profile. | [Argument](../articles/product-symmetries.md#section-pullback) |
| [Transport/Pullback.lean L85](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Transport/Pullback.lean) | The measurable-event pullback formula for that injective sampling law. | [Argument](../articles/product-symmetries.md#section-pullback) |

## Hypotheses and distinctions

All four modules allow arbitrary coordinate types. The probability-measure hypotheses in the uniqueness statements, measurability of the map in the pushforward characterization, injectivity of the sampling map and independence of the two layers are retained. No strict interior condition on a Bernoulli parameter is needed. Empty coordinate sets, empty/full deterministic sets and zero/one profiles are covered. The general pullback theorem has a common measurable state space and probability measures on its input coordinates; the Bernoulli case is its specialization.

Restriction to a subset changes the coordinate type. Deterministic masking instead retains the original coordinate type and fixes discarded marginals at zero. A simple host mask also closes diagonal coordinates; earlier loop-erasure results explain why this part does not affect graph observables. The source two-point comparison assumes countable vertices to ensure connection measurability. Its two purely set-inclusion comparison lemmas do not require measurable events; the article states them with outer measure and separately uses measurability for profile-law event formulas.

The source writes membership decidability for the deterministic profile formulas. This is the choice of cases in the displayed piecewise probabilities, with classical membership available for an arbitrary fixed set; it is not a finiteness restriction or a probabilistic hypothesis. A modifying set selected from the configuration is not covered by those deterministic formulas. Independent random thinning is covered by a different theorem whose joint input law is explicitly a product.

The configuration-complement theorem is already CW1V. The earlier relabelling assertions 6RZ8, VEUZ and 6VY0 remain unchanged, as do their historical source records; the injective theorem does not require surjectivity. Finite families of independent layers follow by induction from the two-layer laws and are marked as exposition rather than extra source exports.

The four new tags NGWR, YMHY, 6J1Y and KDNA are prose identities, not compiled associations. These source-contract matches await independent correspondence review. No published-source error was identified; existing errata remain unchanged.
