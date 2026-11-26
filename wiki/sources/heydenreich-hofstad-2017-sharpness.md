# Heydenreich–van der Hofstad: sharpness and magnetization

Read Chapter 3 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.27–37, PDF indices38–48. The record uses extracted text; published-edition correspondence and visual-page verification remain unchecked.

| Locator | Reconciliation |
|---|---|
| Theorems 3.1–3.2; 3.2.3–3.2.4 | [L0TE and RDF0](articles/finite-size-sharpness.md): threshold identification and finite susceptibility. [JQLC](articles/sharpness-bond-parameter.md#section-boundary) translates to the bond probability. |
| 3.2.5–3.2.9; Exercise 3.1 | [TVM9](articles/sharpness-bond-parameter.md#section-contraction): internal cluster support, independent blocks, recurrence and all-radius bound. |
| Explanation after 3.2.6 | [Coordinate-support repair](../errata/heydenreich-hofstad.json#internal-cluster-coordinate-support): the closed internal boundary is part of the event. |
| Sentence after 3.2.9 | [Rate correction](../errata/heydenreich-hofstad.json#all-radius-exponential-rate): the claimed rate fails in an explicit finite example; a smaller rate works at every radius. |
| Lemma 3.3; 3.2.10–3.2.21; Exercise 3.2 | [HATE](articles/finite-size-sharpness.md#section-pivotal) and [JQLC](articles/sharpness-bond-parameter.md#section-boundary): pivotal orientation, exact finite-product derivative and density integration. The [divided formula uses interior parameters](../errata/heydenreich-hofstad.json#probability-derivative-endpoints). |
| 3.2.22 | [Boundary multiplicity repair](../errata/heydenreich-hofstad.json#box-boundary-multiplicity); [JQLC](articles/sharpness-bond-parameter.md#section-boundary) proves divergence with the degree factor. |
| 3.4.1–3.4.3; Exercise 3.4 | [Positive-field range](articles/sharpness-bond-parameter.md#section-field-range), using [VF24, 8B62 and J2TE](articles/ghost-fields.md). The [finite-size series retains infinite-cluster mass](../errata/heydenreich-hofstad.json#magnetization-infinite-mass). |
| Exercise 3.3 | [3C2F](articles/ghost-fields.md#section-tails): two-sided power comparisons for reciprocal exponent strictly between zero and one. This is not a claimed exact Abelian constant or a proof of every interpretation of the source's asymptotic notation. |
| Proposition 3.6; 3.5.1–3.5.6; Exercise 3.5 | [ZDVK](articles/sharpness-bond-parameter.md#section-inverse): the scalar inequality gives both lower bounds, with the [inverse based at its actual lower endpoint](../errata/heydenreich-hofstad.json#magnetization-inverse-endpoint). |
| Theorem 3.4; 3.6.1–3.6.6 | [7HP2](articles/sharpness-bond-parameter.md#section-rectangle): an absolutely continuous rectangle argument; [G192](articles/sharpness-bond-parameter.md#section-differential-inequalities) supplies its percolation premises. |
| Lemma 3.5; 3.7.1–3.7.8 | [G192](articles/sharpness-bond-parameter.md#section-differential-inequalities): finite closed-pivotal identity, degree bound and positive-field limiting argument. [F7SW](articles/ghost-fields.md#section-intensity) gives a separate finite-increment regularity proof. |
| 3.7.9–3.7.21 | [G192](articles/sharpness-bond-parameter.md#section-differential-inequalities): the one-mark contribution, BK with mark coordinates, finite cut alternative and last pivotal bond. Torus approximation yields the second inequality almost everywhere and the combined scalar inequality at every fixed interior parameter. |
| Exercises 3.6–3.8 | The proposed half-space proof and finiteness of pivotal bonds for connection to infinity have been read, but are not supplied by the finite ghost argument. They remain to be reconciled separately. The density conclusion already has the complete finite-set proof above. |

Six additional provisional manuscript discrepancies have complete written fixes. Four require local proof or formula corrections; two change a displayed rate or endpoint domain while preserving the main theorem. All eleven entries for this manuscript remain provisional, with repair status separate from editorial confirmation. The finite-volume limit is justified using positive-field decay of the cluster-volume contribution; it does not assume infinite-volume Russo differentiability everywhere. Existing compiled associations are not extended by these new proofs.

## Remaining exercises and their hypotheses

| Locator | Added reconciliation |
|---|---|
| Exercise 3.3 | [FZQQ](articles/sharpness-exercises.md#section-tail-asymptotics) gives exact equivalents with the Gamma factor, the borderline logarithm, and the logarithmic-exponent rule. The source's different asymptotic conventions remain distinct; no new erratum is asserted. |
| Exercise 3.7, nearest-neighbour uniqueness input | [Y6SG](articles/sharpness-exercises.md#section-uniqueness) supplies the encounter-box forest construction and boundary count, rather than citing the full long-range uniqueness target. |
| Exercise 3.7, half-space implication | [5E0D](articles/sharpness-exercises.md#section-pivotals) proves finiteness of all rooted pivotal sets from positive half-space percolation. Half-space positivity itself remains a premise. |
| Exercises 3.6 and 3.8 | [9PPO](articles/sharpness-exercises.md#section-zero-field) proves the integrated density inequality and its consequence at every differentiability point, hence almost everywhere, by a zero-field limit. Differentiability at every supercritical parameter is not asserted. |

These additions supersede the earlier row leaving all three final exercises unreconciled. The full-text comparison with Chayes–Chayes, *The Mean Field Bound for the Order Parameter of Bernoulli Percolation*, IMA volume 8 (1987), pp.49–71, [DOI 10.1007/978-1-4613-8734-3_5](https://doi.org/10.1007/978-1-4613-8734-3_5), remains pending: the publisher landing page and references were checked, but the chapter is subscription content. The half-space proof here is supplied directly and is not attributed to an unread source. Existing errata, repair assessments and compiled associations are unchanged.
