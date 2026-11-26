# Heydenreich–van der Hofstad: correlation length and critical Fourier asymptotics

Sections 11.1–11.2 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.135–139 / PDF indices146–150, have been read in extracted text. Visual-page and published-edition checks remain unavailable. This map distinguishes consequences of the completed classical bootstrap from inputs that still require the cited primary papers.

| Locator | Reconciliation |
|---|---|
| Theorem 11.1, 11.1.1; Exercise 11.1 | [CM3M](articles/correlation-length-fourier.md#section-moment) proves the exact squared-length identity. [93RC](articles/correlation-length-fourier.md#section-nearcritical) proves the near-critical comparison in sufficiently large dimension, retaining its factor d. The [missing-square entry](errata/heydenreich-hofstad.json#second-moment-square) is a notation repair; the [scope entry](errata/heydenreich-hofstad.json#correlation-length-nearcritical-scope) restricts the parameter interval. The numerical d>=11 threshold remains attributed. |
| Theorem 11.1, 11.1.2 | The all-orders gap-exponent comparison is read but not proved by the second-moment argument. The primary Nguyen and Hara–Slade inputs remain to be read. |
| Theorem 11.2; 11.1.3–11.1.5 | [1BG0](articles/correlation-length-fourier.md#section-tilted) proves the conditional tilted identity and reciprocal normalization. The [mass entry](errata/heydenreich-hofstad.json#mass-susceptibility-reciprocal) remains a partial fix because the uniform tilted coefficient estimates and identification of the mass are not supplied. The primary Hara proof and its constants remain to be checked. |
| Open Problem 11.1 | The manuscript's supercritical question is read. Its current research status is not assessed. |
| Theorem 11.3; Exercise 11.2 | [ET10](articles/correlation-length-fourier.md#section-fourier) proves the critical Fourier equivalent and computes its amplitude using the absolute second moment. It proves the power remainder conditional on the higher absolute moment; that higher-moment input remains separate. |
| Theorem 11.4; 11.2.4–11.2.15 | The spatial-asymptotic strategy is read. Fourier asymptotics alone are not taken to imply the spatial theorem. The improving spatial bootstrap and the signed-kernel heat estimates remain unfinished. |
| Exercise 11.3 | [BT9V](articles/correlation-length-fourier.md#section-continuity) proves exponential moment control below criticality and continuity of the spatial weighted supremum. |
| Exercise 11.4 | The pointwise first-coefficient diagram estimate remains to be supplied. |
| Exercise 11.5 | [ZPZZ](articles/correlation-length-fourier.md#section-heat) justifies the heat-integral representation by absolute Fubini in d>2 under a quadratic Fourier lower bound; positivity of the spatial kernel is unnecessary. |
| Exercise 11.6 | The convolution remainder and its range of exponents remain to be checked; it is not used to infer spatial asymptotics here. |

Two new provisional entries have complete fixes (one notation repair and one statement-range qualification). The reciprocal-mass entry is explicitly partial: its algebra is repaired, but its analytic inputs remain unproved. No author confirmation or new compiled association is claimed. Section 11.3 has been read through the beginning of its intrinsic-arm induction; its full reconciliation is next.

## Convolution exercise completed

Exercise 11.6 is now reconciled with [Hara's primary convolution lemma](sources/hara-2008-convolution.md). [MZ23](articles/spatial-convolution-asymptotics.md#section-remainder) proves the corrected exponent/symmetry ranges, [UDUU](articles/spatial-convolution-asymptotics.md#section-obstructions) diagnoses the unrestricted version, and [I8BE](articles/spatial-convolution-asymptotics.md#section-transfer) verifies the range used in the spatial lace application. The Green-function and pointwise coefficient estimates remain separate inputs.

## First-coefficient spatial exercise completed

Exercise 11.4 is now proved in [4CGW and P8KQ](articles/spatial-lace-coefficient-bounds.md). Each of two routes contributes a long edge; the nine possible choices leave four summable diagrams in d>6. This gives squared spatial decay for the zeroth and first coefficients and moments below order d-4. It does not give a summable bound over coefficient order, and the spatial bootstrap premise remains explicit. No new erratum is needed for this exercise.

## Signed spatial Green input completed

The [signed-kernel Gaussian proof](articles/signed-kernel-gaussian-asymptotics.md) now supplies the analytic theorem used in (11.2.10)–(11.2.15), including its higher-moment remainder and the exact lace amplitude. It makes the coordinate symmetries explicit. The all-order spatial coefficient bound and improving bootstrap are still required; the two-coefficient exercise does not close that gap.

## The gap-exponent argument completed in the classical regime

The [Nguyen primary-source map](sources/nguyen-gap-1987.md) now closes the moment-gap deduction left open above. The [lattice proof](articles/mean-field-cluster-moments.md#section-lattice-gap) combines the already proved score inequality, small neighbouring triangle, moment continuity and tree-graph estimates. It yields every fixed higher moment and gap ratio in sufficiently large dimension, retaining q=2d. Further deductions give fractional moments, the half-order logarithm, a critical-window cutoff tail and the density of clusters above a fixed lower cutoff. The numerical d>=11 threshold, general finite-triangle regularization, tilted mass and spatial-bootstrap obligations remain distinct. No old statement or provisional erratum is changed.

## The true mass and endpoint divergence

The [Hara reading map](sources/hara-correlation-1990.md) and [tilted-susceptibility proof](articles/tilted-susceptibility.md) now discharge the mass-identification obligation listed above. A finite-box contraction proves joint openness of tilted summability; its axial boundary is the exponential decay rate and the tilted sum diverges there. The mass is continuous below criticality and tends to zero at criticality. The actual-mass lace identity remains conditional on endpoint exponential moments of the coefficient kernel. Quantitative tilted coefficient bounds are still needed for the full correlation-length theorem, so the existing reciprocal entry remains partial. No previously tagged statement is changed.

## The uniform tilted coefficient input completed

The [tilted Fourier bootstrap](articles/tilted-fourier-bootstrap.md) now closes the remaining qualitative coefficient step. All nonnegative orders have cosh-weighted mass of order inverse dimension and each weighted coordinate second moment of order inverse dimension squared, uniformly up to the smaller of the true mass and one. This proves the reciprocal mass comparison and the exponential correlation-length exponent in sufficiently large dimension, on an explicit near-critical interval. The [reciprocal entry](errata/heydenreich-hofstad.json#mass-susceptibility-reciprocal) now has a fix found in that regime. It stays provisional; no numerical d>=11 threshold or source constants are claimed. The all-order spatial bootstrap and the other separately queued obligations remain.

## Quantified mean-field consequences

The [explicit-range section](articles/green-free-triangle.md#section-explicit-susceptibility) supplies a common range d>=10^11 for the susceptibility, critical field and tail, density, and moment-cutoff arguments. YT0O bounds the critical neighbouring triangle by 189/d. E5ZR verifies the positive field coefficient at least 2/11 by rational comparisons and an exponential-series bound, giving critical tail constants 1/360 and6 and density constants 1/3 and24 on the scale 2d(p-p_c). 9TAI gives the subcritical second-moment lower bound chi cubed/3, upper tail 8 n^(-1/2) exp[-n/(4 chi squared)], and lower tail 1/(139968 sqrt(n)) for n<=chi squared/6, for p_c/2<=p<p_c. The real-order moment regimes follow by the existing tail-sum argument. The exact comparison script is reproduced in the article.

This is a coarse independent quantification of the written proof chain, not a sharp numerical dimension claim from the source. It does not settle arbitrary finite-triangle regularization, limiting amplitudes or tail profiles. All previous statements, provisional errata and formal statuses are preserved.

## Finite triangles without a smallness assumption

The [finite-triangle endpoint theorem](articles/triangle-susceptibility.md#section-finite-triangle), ADWR, combines the proved corrected boundary inequality with reciprocal integration. For normalized transitive unimodular weights, a finite susceptibility threshold b and finite critical diagonal triangle D give 1/(b-beta)<=chi(beta)<=2 D squared+3 beta b D squared/(b-beta). The existing entropy and tail-field arguments then give the two-sided critical square-root tail and field law. [I23O](articles/triangle-susceptibility.md#section-finite-triangle-lattice) identifies the endpoint and adds the supercritical density lower bound for nearest-neighbour lattice percolation by sharpness.

The [moment and cutoff extension](articles/mean-field-cluster-moments.md#section-finite-triangle-cutoff), 7T8L, obtains a cubic second moment from the boundary derivative and exploration score. A size-biased band and continuity of the moment ratio give a lower tail up to alpha chi squared/2, and the critical/exponential upper bounds give the susceptibility-squared cutoff, all positive real moment orders and fixed-cutoff inverse-volume estimates. These are model-dependent constants, not the uniform high-dimensional constants of the earlier results. No small-neighbouring-triangle hypothesis is used.

These deductions complete the general finite-triangle implication previously left separate in this map. They use a different proof from classical endpoint separation: that surgery argument itself is still not supplied. They do not establish triangle finiteness in a new dimension, transfer site-percolation normalizations unchanged, identify a limiting amplitude or cutoff profile, or prove a singular free-energy asymptotic. The original source statements and all provisional errata remain unchanged; no compiled status is asserted.
