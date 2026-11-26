# Finite expectation, coupling and profile contracts at 5d6efa8

This inventory covers all **30 named public theorems across five modules** at private `lrp` revision 5d6efa862d99e11fb1f01619be7700b85c1c8f7b, inspected 16 November 2026: five explicit expectation results, four homogeneous polynomial results, nine finite-continuity results, five ordered-coupling results and seven total-variation results. Imported declarations, definitions and anonymous witnesses are excluded from this count. Source inspection is not independent correspondence review or compiled association.

## Finite weighted expectations

| Source line | Contract | Exposition |
| --- | --- | --- |
| [ProductExpectation.lean L37](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProductExpectation.lean) | Finite configurations have the product of their open and closed coordinate weights as extended probability mass. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [ProductExpectation.lean L59](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProductExpectation.lean) | The same finite configuration mass is given as a real product. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [ProductExpectation.lean L68](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProductExpectation.lean) | Every real observable on a finite configuration space has the explicit weighted-sum integral. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [ProductExpectation.lean L78](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProductExpectation.lean) | Restriction to a finite coordinate block pushes any ambient product law to that block’s product law. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [ProductExpectation.lean L96](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/ProductExpectation.lean) | An arbitrary real observable of a finite block has the explicit finite weighted expectation, with arbitrary ambient indices. | [Argument](../articles/profile-continuity.md#section-restriction) |

## Homogeneous expectation polynomials

| Source line | Contract | Exposition |
| --- | --- | --- |
| [FiniteExpectation.lean L45](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteExpectation.lean) | The homogeneous averaging polynomial evaluates to the explicit finite expectation at every real parameter. | [Argument](../articles/russo-formula.md#section-profile) |
| [FiniteExpectation.lean L52](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteExpectation.lean) | The finite expectation is differentiable on the entire real line, with derivative the polynomial derivative. | [Argument](../articles/russo-formula.md#section-profile) |
| [FiniteExpectation.lean L58](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteExpectation.lean) | At a unit-interval parameter the algebraic expectation equals the canonical product-law integral. | [Argument](../articles/russo-formula.md#section-profile) |
| [FiniteExpectation.lean L64](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteExpectation.lean) | The averaging polynomial evaluated at a probability parameter equals that integral. | [Argument](../articles/russo-formula.md#section-profile) |

## Finite observations and product topology

| Source line | Contract | Exposition |
| --- | --- | --- |
| [FiniteContinuity.lean L23](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | A finite-coordinate event probability is the sum of its multiaffine configuration weights. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [FiniteContinuity.lean L31](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | Any finite-coordinate event probability is continuous in the full profile, including endpoint coordinates. | [Argument](../articles/profile-continuity.md#section-finite) |
| [FiniteContinuity.lean L48](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | A cylinder probability equals its finite-block probability. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [FiniteContinuity.lean L60](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | A finite cylinder has the explicit sum of its configuration weights in any ambient index type. | [Argument](../articles/profile-continuity.md#section-restriction) |
| [FiniteContinuity.lean L69](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | A fixed finite-cylinder probability is continuous in the ambient product topology, without countability. | [Argument](../articles/profile-continuity.md#section-finite) |
| [FiniteContinuity.lean L76](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | Coordinatewise convergence along any filter implies convergence of every fixed finite-cylinder probability. | [Argument](../articles/profile-continuity.md#section-finite) |
| [FiniteContinuity.lean L91](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | On finite vertex sets, the two-point function is continuous in the whole pair profile. | [Argument](../articles/profile-continuity.md#section-finite) |
| [FiniteContinuity.lean L96](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | Connection inside a fixed finite vertex domain is continuous in the ambient pair profile. | [Argument](../articles/profile-continuity.md#section-finite) |
| [FiniteContinuity.lean L102](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/FiniteContinuity.lean) | Coordinatewise profile convergence along any filter preserves fixed finite-domain connection probabilities. | [Argument](../articles/profile-continuity.md#section-finite) |

## Ordered coupling

| Source line | Contract | Exposition |
| --- | --- | --- |
| [Monotone.lean L22](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Coupling/Monotone.lean) | Two ordered Bernoulli parameters admit a three-state coupling with masses p, q-p and 1-q. | [Argument](../articles/profile-continuity.md#section-order) |
| [Monotone.lean L62](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Coupling/Monotone.lean) | Ordered profiles on countable coordinates admit a coupling with the first open set contained in the second almost surely. | [Argument](../articles/profile-continuity.md#section-order) |
| [Monotone.lean L104](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Coupling/Monotone.lean) | Every measurable increasing event is more likely under the larger countable profile. | [Argument](../articles/profile-continuity.md#section-order) |
| [Monotone.lean L115](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Coupling/Monotone.lean) | Every measurable increasing extended-nonnegative observable has larger lower integral under the larger countable profile, even for infinite expectations. | [Argument](../articles/profile-continuity.md#section-order) |
| [Monotone.lean L124](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/Coupling/Monotone.lean) | The ordered coupling specializes to countable bond vertices with every unordered-pair coordinate retained. | [Argument](../articles/profile-continuity.md#section-order) |

## Summable profile changes

| Source line | Contract | Exposition |
| --- | --- | --- |
| [TotalVariation.lean L40](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | A unit-interval probability has the same extended nonnegative value whether coerced through nonnegative reals or embedded from the real value. | [Argument](../articles/profile-continuity.md#section-total-variation) |
| [TotalVariation.lean L47](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | For ordered profiles on countable coordinates, each event probability is at most the other plus the extended sum of parameter increases. | [Argument](../articles/profile-continuity.md#section-total-variation) |
| [TotalVariation.lean L115](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | The two nonnegative differences through the minimum of two probabilities sum to their absolute difference. | [Argument](../articles/profile-continuity.md#section-total-variation) |
| [TotalVariation.lean L128](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | Any measurable event probability under q is at most that under r plus the extended sum of absolute coordinate differences, on countable indices. | [Argument](../articles/profile-continuity.md#section-total-variation) |
| [TotalVariation.lean L146](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | When the discrepancy sum is finite, the real absolute difference of measurable-event probabilities is at most that sum. | [Argument](../articles/profile-continuity.md#section-total-variation) |
| [TotalVariation.lean L180](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | The countable bond two-point function satisfies the same one-sided extended discrepancy inequality. | [Argument](../articles/profile-continuity.md#section-total-variation) |
| [TotalVariation.lean L185](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Probability/TotalVariation.lean) | The rooted infinite-cluster probability on countable bond vertices satisfies the same extended discrepancy inequality. | [Argument](../articles/profile-continuity.md#section-total-variation) |

## Scope and additional deductions

The two named definitions in FiniteExpectation, at lines 36 and 41, define the averaging polynomial and its finite weighted-sum evaluation. The polynomial identities and derivative are algebra on every real parameter; the probability-law interpretation requires the unit interval. The existing 7WIO explains this distinction. Empty blocks, zero observables, the one-coordinate observable and mixed deterministic coordinate probabilities are included in the source witnesses and existing prose.

Finite block restriction and continuity allow arbitrary ambient coordinate sets. Every observable on the finite configuration space is bounded and integrable. The source convergence statements allow arbitrary filters, not only sequences; RA0Z's continuity in the product topology gives these statements directly. The finite-domain bond event uses paths inside that domain, rather than full-space paths that may leave it. There is no conclusion about continuity of an arbitrary infinite-volume event in the product topology.

The three-state coordinate coupling needs no ambient countability. The exported whole-profile coupling does assume countability, as do its event and extended-nonnegative-integral comparisons. This ensures that the target event of coordinatewise containment is measurable. The pointwise three-state construction is stronger than merely showing each coordinate is ordered almost surely, and the article explains that distinction. Bond specialization retains diagonal coordinates and requires profile order there too.

W90W states total variation with the supremum-over-events normalization, whose maximum value is one. The source exports the underlying one-sided extended inequalities and, when the discrepancy sum is finite, their real absolute-difference form. Its proof compares both profiles with their coordinatewise minimum; the article also gives the common-uniform coupling directly. The cap by one, bounded-observable consequence, uniform convergence under vanishing l1 discrepancy and diagonal-erased bond sum are deductions. The source's sum includes all unordered pairs.

Countability is retained in the total-variation statement. No profile ordering or increasingness of the event is assumed. Infinite discrepancy is allowed in the extended inequality but cannot be converted to a useful finite real bound. A nonzero homogeneous change on infinitely many coordinates has infinite discrepancy, so this theorem supplies no critical-parameter continuity. The single-coordinate equality and zero discrepancy for identical profiles cover nontrivial and endpoint witnesses.

Existing source pins and occurrence records, mathematical article bodies, tags and all errata remain unchanged. The new total-variation correspondence awaits independent review and compiled association.
