# Open-degree source contracts at 5d6efa8

This source inspection covers all **15 named public theorems** in the degree and degree-generating modules at private `lrp` revision 5d6efa862d99e11fb1f01619be7700b85c1c8f7b. Imported declarations and anonymous witnesses are excluded. Neither file adds definitions or tagged assertions. The [article](../articles/open-degree-laws.md) groups the contracts into their mathematical arguments; these rows do not assign a formal status or establish an independent correspondence review.

## Degree

| Source line | Contract | Exposition |
|---|---|---|
| [L37](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | An adjacency event is empty on the diagonal and a single-coordinate open event otherwise. | [Argument](../articles/open-degree-laws.md#section-counts) |
| [L45](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | Each adjacency event is measurable on any vertex type. | [Argument](../articles/open-degree-laws.md#section-counts) |
| [L53](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | Its probability is zero on the diagonal and the pair marginal otherwise. | [Argument](../articles/open-degree-laws.md#section-counts) |
| [L63](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | Full degree is a measurable extended integer on countable vertices. | [Argument](../articles/open-degree-laws.md#section-first-moments) |
| [L68](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | The degree is a nonnegative sum of adjacency indicators; this deterministic identity needs no countability. | [Argument](../articles/open-degree-laws.md#section-first-moments) |
| [L75](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | On countable vertices the expected degree is the off-diagonal row sum, allowing infinity. | [Argument](../articles/open-degree-laws.md#section-first-moments) |
| [L84](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | For every natural threshold k, k times the probability of degree at least k is at most that row sum. At k = 0 the claim is tautological. | [Argument](../articles/open-degree-laws.md#section-first-moments) |
| [L97](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | The expected count in a finite set of pair coordinates is the sum of their marginals; diagonal coordinates count if included. No ambient countability is needed. | [Argument](../articles/open-degree-laws.md#section-first-moments) |
| [L102](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/Degree.lean) | For a finite vertex set inside countable vertices, the expected number of open pairs oriented outwards is the sum of the outgoing marginals. | [Argument](../articles/open-degree-laws.md#section-first-moments) |

## DegreeGenerating

| Source line | Contract | Exposition |
|---|---|---|
| [L42](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DegreeGenerating.lean) | The one-coordinate factor has expectation s q + 1 − q for every extended nonnegative s. | [Argument](../articles/open-degree-laws.md#section-generating) |
| [L59](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DegreeGenerating.lean) | Factors of distinct pair coordinates incident to one fixed vertex are mutually independent. A diagonal coordinate is still a distinct raw coordinate. | [Argument](../articles/open-degree-laws.md#section-generating) |
| [L68](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DegreeGenerating.lean) | For a finite set of vertices, the generating function of the incident-coordinate count is the product of one-coordinate factors, with no ambient countability assumption. | [Argument](../articles/open-degree-laws.md#section-generating) |
| [L84](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DegreeGenerating.lean) | At generating parameter zero, the finite no-open-pair probability is the product of complementary marginals. | [Argument](../articles/open-degree-laws.md#section-generating) |
| [L113](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DegreeGenerating.lean) | For an increasing sequence of finite sets and 0 ≤ s ≤ 1, integration commutes with the decreasing infimum of count powers. | [Argument](../articles/open-degree-laws.md#section-isolation) |
| [L139](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/DegreeGenerating.lean) | On countable vertices, the isolation probability is the decreasing product along a finite exhaustion after erasing the root. | [Argument](../articles/open-degree-laws.md#section-isolation) |

## Conventions and additional deductions

Raw pair coordinates include a possible diagonal coordinate. Finite pair-count expectations and generating functions count it when the chosen set includes it; graph degree and isolation never count it. The article explicitly erases the root when passing from incident-coordinate formulas to degree formulas. A finite outgoing boundary counts each crossing unordered bond once through its orientation out of the set.

The finite generating-function identity includes the extended parameter infinity, using zero times infinity equal to zero. The decreasing limit is restricted to parameters in [0,1]; at parameter one it is one even for an infinite count, while at zero the zeroth power is one. Ambient countability is unnecessary for a sequence of finite-coordinate counts, since their union is countable. It is imposed for the full-degree and all-vertex assertions.

The source's first-moment bound is valid with infinite expectation but cannot alone show almost-sure infinite degree. XJ74 supplies that conclusion using independence and the generating product. UNJ6 likewise adds the logarithmic criterion for a strictly positive isolation product. These are informal deductions beyond the two modules, not newly exported or reviewed Lean correspondences.

The anonymous source witnesses cover a two-vertex finite mean, infinite mean for constant positive marginals on the natural numbers, a two-vertex generating function and a natural-number exhaustion. They do not increase the fifteen-theorem count. No new published-source erratum is asserted by this inspection.
