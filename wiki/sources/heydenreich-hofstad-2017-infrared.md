# Heydenreich–van der Hofstad: infrared and walk diagrams

Read Chapter 5 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.49–57, PDF indices60–68. This record concerns extracted text from that dated manuscript; visual-page and published-edition correspondence remain unchecked.

| Locator | Reconciliation |
|---|---|
| Theorems 5.1 and5.4; 5.1.1; 5.2.2–5.2.3 | Infrared bounds are explicit premises in [ANZF](articles/infrared-diagrams.md#section-infrared). Their lace-expansion proofs in Chapters 6–8 remain to be reconciled. |
| Lemma 5.3; 5.1.2–5.1.4 | [70KD and F77A](articles/connection-kernels.md) prove cluster positivity and Fourier nonnegativity, with finite-susceptibility scope. |
| Corollary 5.2; 5.1.5–5.1.9; 5.1.17 | [ANZF](articles/infrared-diagrams.md#section-infrared) proves triangle finiteness conditional on the infrared estimate and passes to criticality in spatial sums. |
| 5.1.10–5.1.16; Exercise 5.1 | [RD3X](articles/infrared-diagrams.md#section-walk-moments) supplies uniform inverse moments by convexity, with elementary trigonometric bounds. It does not rely on the displayed Gaussian normalization. |
| 5.1.18–5.1.20 | [ANZF](articles/infrared-diagrams.md#section-infrared) gives the neighbouring-triangle bound and its smallness for sufficiently large dimension under a common amplitude bound. |
| Exercises 5.2 and5.5 | [ANZF](articles/infrared-diagrams.md#section-infrared) proves the open-polygon inequalities by Fourier positivity and their critical limits. |
| 5.2.1; 5.2.4; Exercise 5.3 | [ZRVJ](articles/infrared-diagrams.md#section-spreadout) distinguishes a holding walk from loopless percolation and proves nontriviality of the percolation threshold. |
| Section 5.3; 5.3.1–5.3.3 | An overview of expansion, coefficient bounds and bootstrap. These are separate remaining proof obligations, not consequences of the walk bounds alone. |
| Proposition 5.5; 5.4.1–5.4.5 | [RD3X](articles/infrared-diagrams.md#section-walk-moments) gives the dimension-uniform weighted bound and its damped form. The [spatial Fourier expression is a zero coefficient](../errata/heydenreich-hofstad.json#walk-integral-zero-coefficient). |
| Exercise 5.4; 5.4.6–5.4.8 | [A9W9](articles/infrared-diagrams.md#section-shifted) proves both shifted integrals with the same unshifted bound. |
| Proposition 5.6; 5.4.9–5.4.14; Exercise 5.6 | [ZRVJ](articles/infrared-diagrams.md#section-spreadout) proves the symbol gap, the small-frequency estimate and the weighted diagram bound. |
| Paragraph after Proposition 5.6 | The [baseline correction](../errata/heydenreich-hofstad.json#spreadout-triangle-baseline) distinguishes a small nontrivial diagram from the full triangle, which is one plus a term of order L to the minus d. |

Both newly recorded discrepancies have written fixes. The zero-coefficient correction is local; the baseline correction changes the claimed quantity tending to zero while preserving the intended high-dimensional perturbation argument. They remain provisional manuscript findings, without author confirmation, a checked published edition or a new compiled association. The mean-field exponents in Corollary 5.2 additionally invoke the full triangle theorem; the walk analysis does not prove that theorem by itself.

## Explicit sixth-norm certificates

[LKS9](articles/infrared-diagrams.md#section-sixth-certificates) replaces the unspecified sixth walk-integral constants by finite return counts and a proved tail bound. It also proves that both relevant integrals decrease with dimension. [NI0W](articles/infrared-diagrams.md#section-connector-certificate) gives exact rational certificates: for dimensions at least 40, 64 or 100, infrared amplitude and j_c bounded respectively by 21/20, 11/10 or 23/20 imply sixth-norm connector bounds below 407/500, 37/50 or 181/250. The full certificate is reproduced in the article and stored as a standard-library Python script. These bounds supply the smallness input to FWHO, conditional on its remaining critical hypotheses. They do not establish the required percolation infrared amplitudes at these dimensions or a numerical percolation threshold. No source erratum or formal-status promotion is asserted.


## Spatial logarithmic thresholds

[GZCA](articles/infrared-diagrams.md#section-spatial-log-diagrams) is an independent spatial extension of the diagram discussion. Two-sided power decay with a logarithmic factor gives matching dyadic-shell bounds for truncated bubbles and triangles, their exact integrability criteria, and tails in the finite cases. The triangle proof separately sums the shortest side, including coincident vertices, rather than assuming all sides are macroscopic.

[9ZD3](articles/infrared-diagrams.md#section-marginal-diagrams) specializes this calculation to Gaussian power decay in dimensions four and six. In six dimensions every fixed logarithmic power leaves the bubble finite, while the triangle requires a logarithmic power strictly below -1/3; equality gives a double logarithm. These are conditional implications, not a newly checked source statement, a determination of a model's logarithmic exponent, or a reverse-BK repair. No new source reading, source erratum, independent audit or Lean verification is claimed.


## The first directional walk correction

[C5GY](articles/infrared-diagrams.md#section-local-fourier-remainder) proves the localized Fourier decay estimate and the cutoff comparison used by [IY26](articles/infrared-diagrams.md#section-walk-green-correction). The latter gives the two-term nearest-neighbour Green expansion in every integer dimension at least three, with the explicit fourth-degree angular term and a remainder uniform over lattice directions. The heat-kernel calculation differentiates before integrating, so it also covers dimensions three and four without a divergent biharmonic-potential step.

These are independent extensions of the walk analysis, not a newly checked source occurrence or a correction of a published statement. The dimension-six formula concerns the ordinary walk; it does not supply a percolation two-point expansion. No new source reading, source erratum, independent audit or Lean verification is claimed.


## Killing and the marginal logarithm

[WXT8](articles/infrared-diagrams.md#section-killed-diagram-asymptotics) gives the power singularity below the walk-diagram dimension threshold and the exact logarithmic coefficient at the threshold, for symmetric finite-range laws generating the lattice. Subtracting the quadratic symbol gives a convergent finite-part formula and a quantified remainder. Holding changes both the coefficient and the finite part.

[KC8U](articles/infrared-diagrams.md#section-marginal-killing-coefficients) specializes to the four-dimensional bubble and six-dimensional triangle. An exact derivative identity then gives the six-dimensional bubble's approach to its finite critical value, including the term linear in the killing gap. These are independent extensions of the existing walk analysis, not additional statements read in the source. No new source reading, source erratum, percolation asymptotic, independent audit or Lean verification is claimed.


## Shifted diagrams at the marginal dimension

[7PM4](articles/infrared-diagrams.md#section-shifted-marginal-profile) gives the common profile of the shifted bubble in dimension four and the one-shift triangle in dimension six, including general covariance normalization. The convergence is uniform for bounded frequency divided by mass. [2RVB](articles/infrared-diagrams.md#section-critical-shifted-finite-part) proves the critical nonzero-frequency asymptotic separately and identifies its constant relative to the finite part from killing regularization.

These deductions extend the existing walk and shifted-integral discussion. They are not new statements read in the manuscript and do not assert convergence of an undamped spatial Fourier series. No new source reading, source erratum, percolation asymptotic, independent audit or Lean verification is claimed.
