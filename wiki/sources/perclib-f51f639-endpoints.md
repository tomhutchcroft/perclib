# Derivative limits, intrinsic growth and susceptibility endpoints

This inventory records **22 explicit named public theorems in four complete files / 861 lines** at private lrp merged main f51f639c15d742034cc6e2058008c79f48392873. All four files have been read in full. Anonymous witnesses and private proof steps are excluded from the declaration count. The endpoint exports complete the previously missing clauses of 5LNL and MXGM at source level; compiled association and independent prose correspondence remain separate.

## Analysis/DominatedDerivative

| Source line | Contract | Exposition |
|---|---|---|
| [L56](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Analysis/DominatedDerivative.lean) | On an interval contained in I, pointwise convergence of differentiable functions and their derivatives, with measurable derivatives bounded by one integrable function, gives the exact integrated identity for the limits. Both orientations of the interval are allowed. | [Argument](../articles/spatial-cutoff-moments.md#section-dominated-source) |
| [L108](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Analysis/DominatedDerivative.lean) | On an open set I, the same assumptions on compact subintervals give the derivative of the limit at each point where the limiting derivative is continuous and locally strongly measurable. | [Argument](../articles/spatial-cutoff-moments.md#section-dominated-source) |

## Percolation/Bond/IntrinsicGrowth

| Source line | Contract | Exposition |
|---|---|---|
| [L41](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IntrinsicGrowth.lean) | An intrinsic-ball connection is witnessed by a simple open path of length at most the radius, on arbitrary vertices. | [Argument](../articles/intrinsic-geometry.md#section-growth-source) |
| [L62](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IntrinsicGrowth.lean) | On countable vertices, the ball connection probability is at most the sum of the simple-path product weights. | [Argument](../articles/intrinsic-geometry.md#section-growth-source) |
| [L80](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IntrinsicGrowth.lean) | A uniform extended off-diagonal probability-row bound D gives expected intrinsic ball volume at most the sum of D^j from j=0 to the natural radius. | [Argument](../articles/intrinsic-geometry.md#section-growth-source) |
| [L134](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IntrinsicGrowth.lean) | Transitivity of a probability profile makes its off-diagonal row sums equal, including infinite values. | [Argument](../articles/intrinsic-geometry.md#section-growth-source) |
| [L147](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/IntrinsicGrowth.lean) | The intrinsic-ball upper bound specializes to a transitive profile with D equal to its root probability-row sum; neither finite D nor infinite susceptibility is assumed. | [Argument](../articles/intrinsic-geometry.md#section-growth-source) |

## Percolation/Bond/SusceptibilityEndpoint

| Source line | Contract | Exposition |
|---|---|---|
| [L42](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SusceptibilityEndpoint.lean) | For a transitive intensity kernel with finite off-diagonal row sum, a finite supremum of finite-susceptibility parameters has infinite susceptibility at that endpoint. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L69](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SusceptibilityEndpoint.lean) | If susceptibility is finite on (a,b), a>=0, and infinite at b, then it is arbitrarily large below b after every fixed s in (a,b). This lemma needs neither transitivity nor a row-sum assumption. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L107](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Percolation/Bond/SusceptibilityEndpoint.lean) | For a transitive kernel with positive finite off-diagonal intensity row R, finite susceptibility on (a,b), a>=0, and infinite susceptibility at b, the real susceptibility at beta in (a,b) is at least 1/(R(b-beta)). | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |

## Models/FreeGroupTree

| Source line | Contract | Exposition |
|---|---|---|
| [L53](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Left multiplication preserves the right Cayley edges of the rank-two free group. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L68](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | The unit-weight Cayley intensity has an invariant automorphism carrying the identity to any vertex. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L83](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Equivalently, an invariant automorphism carries any specified vertex to any other. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L99](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Its off-diagonal intensity row sum is finite. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L123](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | That row sum is strictly positive. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L136](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Adjoining a positive letter appends the corresponding generator on the right of the represented group element. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L143](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Distinct positive words represent distinct group elements. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L164](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Every positive word is reached along a Cayley walk of its own length. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L188](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | For beta>=1, every Cayley edge has opening probability at least one half. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L219](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | Susceptibility is infinite for every beta>=1, by summing over positive words. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L252](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | The model has a susceptibility threshold b with 0<b<=1, finite susceptibility at every beta<b, and infinite susceptibility at b. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |
| [L307](https://github.com/tomhutchcroft/perclib/blob/a920a1ec32e38ee69a36bc4d4b81ef6a1ec1de7d/PercLib/Models/FreeGroupTree.lean) | The same endpoint witness is expressed with real parameters and the nonnegative-part convention. | [Argument](../articles/integrated-susceptibility.md#section-endpoint-source) |

## Scope of the implications

The derivative-limit theorem is analytic. The source assumes pointwise convergence at every point of I, globally almost-everywhere strongly measurable approximating derivatives, a common bound on I, and interval integrability of that bound. Its pointwise derivative conclusion additionally assumes continuity and local strong measurability of the limiting flux. It does not prove any percolation flux envelope, correlation identity, or interchange of an infinite edge sum with a derivative. The open set need not be connected; the differentiation argument uses a small interval inside it.

The intrinsic-growth file proves only the upper bound portion of R5XZ. Its bound holds at radius zero and with infinite row bound D, using extended nonnegative arithmetic. The lower sphere and ball estimates, the thinning comparison and the intrinsic-arm bootstrap remain separate. Transitivity is needed only to replace a uniform row bound by the row at one root.

The endpoint module distinguishes divergence at a finite susceptibility threshold from a quantitative blow-up bound near an endpoint already known to have infinite susceptibility. The latter requires positive finite R. The lemma producing arbitrarily large finite susceptibilities below the endpoint has no transitivity or row-sum premise; finite-domain continuity and the supremum representation suffice. These statements do not identify the susceptibility threshold with the percolation threshold.

The free-group source supplies a concrete invariant finite-row model satisfying the endpoint hypotheses. Its positive-word argument needs only a lower bound for each path probability, not independence between different root-connection events. It proves a finite positive threshold bounded above by one, not an exact critical value. The endpoint witness is independently obtained from right-openness and the supremum, so using it to instantiate the endpoint theorem is not circular.

## Provenance

DominatedDerivative is adapted from yujinhkim/lrp at d382e4c28d92dd4e698ebf4f2aaf0bc932ae73fc, file PercLib/CriticalLRP/RussoInf/DominatedFlux.lean, under the Apache-2.0 declaration recorded in its header. That header also names the earlier Critical-Long-range-percolation origin, which has not been independently verified here. The other files identify new project proofs or restoration of earlier private-library proofs. The endpoint proofs were previously held for a model witness; the restoration does not introduce a paper correction. Existing errata remain provisional.
