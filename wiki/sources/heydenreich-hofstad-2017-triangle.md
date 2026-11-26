# Heydenreich–van der Hofstad: the triangle condition

Read Chapter 4 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.41–47, PDF indices52–58. Extracted text was checked; visual-page and published-edition comparison remain pending.

| Locator | Reconciliation |
|---|---|
| 4.1.1; Theorem 4.1 | [67VP, 7UDJ and 2ZI0](articles/triangle-condition.md) state the diagram and the full mean-field theorem. The new arguments do not certify the entire theorem. |
| Discussion after Theorem 4.1 | [5W46](articles/triangle-susceptibility.md#section-critical) proves critical nonpercolation from the finite triangle, uniqueness and Harris. |
| Exercise 4.1 | [KCOF](articles/infrared-diagrams.md#section-walk-threshold) transfers the lazy-walk calculation to the ordinary nearest-neighbour walk and proves the dimension-six threshold. |
| 4.2.2–4.2.7; Lemmas 4.3–4.4; 4.2.8–4.2.17 | [8ZGG](articles/triangle-susceptibility.md#section-reciprocal) proves a globally Lipschitz reciprocal and the probability-parameter lower bound, including finite-volume approximation. |
| Exercise 4.2; 4.2.18 | [8ZGG](articles/triangle-susceptibility.md#section-reciprocal) gives both one-sided derivatives of a finite maximum and uses ordinary derivatives only almost everywhere. |
| 4.2.19–4.2.24 | [4800, 7902 and J1LW](articles/integrated-susceptibility.md) supply the two-cluster identity, deletion loss and tree-diagram estimate in the intensity parametrization. |
| Theorem 4.2; 4.2.25 | [0Y4K](articles/triangle-susceptibility.md#section-small-triangle) integrates the resulting inequality after changing to bond probability. A small neighbouring open triangle is an explicit hypothesis. |
| Paragraph following 4.2.25 | The regularization step from mere triangle finiteness is omitted by the manuscript and remains a separate coverage obligation. Large-distance open-triangle decay alone does not discharge it. |
| 4.2.26 | An indicated approximation motivating the lace expansion; it is not used as an identity. |
| 4.3.1; Corollary 4.5 | [5W46](articles/triangle-susceptibility.md#section-critical) proves the three one-sided exponent restrictions, each conditional on existence of that exponent. |

The susceptibility lower bound is unconditional. Its matching upper bound here uses the stronger small-triangle premise; the full mean-field theorem also needs the later density and field arguments. No new erratum or compiled association is inferred from the almost-everywhere wording in the finite-maximum argument.

## Quantified mean-field consequences

The [explicit-range section](articles/green-free-triangle.md#section-explicit-susceptibility) supplies a common range d>=10^11 for the susceptibility, critical field and tail, density, and moment-cutoff arguments. YT0O bounds the critical neighbouring triangle by 189/d. E5ZR verifies the positive field coefficient at least 2/11 by rational comparisons and an exponential-series bound, giving critical tail constants 1/360 and6 and density constants 1/3 and24 on the scale 2d(p-p_c). 9TAI gives the subcritical second-moment lower bound chi cubed/3, upper tail 8 n^(-1/2) exp[-n/(4 chi squared)], and lower tail 1/(139968 sqrt(n)) for n<=chi squared/6, for p_c/2<=p<p_c. The real-order moment regimes follow by the existing tail-sum argument. The exact comparison script is reproduced in the article.

This is a coarse independent quantification of the written proof chain, not a sharp numerical dimension claim from the source. It does not settle arbitrary finite-triangle regularization, limiting amplitudes or tail profiles. All previous statements, provisional errata and formal statuses are preserved.

## Finite triangles without a smallness assumption

The [finite-triangle endpoint theorem](articles/triangle-susceptibility.md#section-finite-triangle), ADWR, combines the proved corrected boundary inequality with reciprocal integration. For normalized transitive unimodular weights, a finite susceptibility threshold b and finite critical diagonal triangle D give 1/(b-beta)<=chi(beta)<=2 D squared+3 beta b D squared/(b-beta). The existing entropy and tail-field arguments then give the two-sided critical square-root tail and field law. [I23O](articles/triangle-susceptibility.md#section-finite-triangle-lattice) identifies the endpoint and adds the supercritical density lower bound for nearest-neighbour lattice percolation by sharpness.

The [moment and cutoff extension](articles/mean-field-cluster-moments.md#section-finite-triangle-cutoff), 7T8L, obtains a cubic second moment from the boundary derivative and exploration score. A size-biased band and continuity of the moment ratio give a lower tail up to alpha chi squared/2, and the critical/exponential upper bounds give the susceptibility-squared cutoff, all positive real moment orders and fixed-cutoff inverse-volume estimates. These are model-dependent constants, not the uniform high-dimensional constants of the earlier results. No small-neighbouring-triangle hypothesis is used.

These deductions complete the general finite-triangle implication previously left separate in this map. They use a different proof from classical endpoint separation: that surgery argument itself is still not supplied. They do not establish triangle finiteness in a new dimension, transfer site-percolation normalizations unchanged, identify a limiting amplitude or cutoff profile, or prove a singular free-energy asymptotic. The original source statements and all provisional errata remain unchanged; no compiled status is asserted.
