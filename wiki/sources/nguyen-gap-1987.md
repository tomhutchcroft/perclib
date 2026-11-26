# Nguyen: gap exponents and the cluster-volume scale

[Nguyen, Journal of Statistical Physics 49 (1987), 235–243](https://doi.org/10.1007/BF01009960) was read through the publicly accessible [extracted article text](https://www.academia.edu/106958121/Gap_exponents_for_percolation_processes_with_triangle_condition). The publisher page confirms the bibliographic identity; its PDF is subscription content. OCR formulas were not visually checked. No suspected OCR defect is recorded as an erratum.

The source uses site clusters. Section 2, Theorem 3 / (4), printed pp.238–239, reduces the second-moment comparison to a susceptibility derivative. Section 3, Lemma 1 / (7)–(10), printed p.241, then gives the higher moment gaps. The Proposition / (5)–(6), pp.240–242, concerns a power of the moment-ratio cutoff. Its discussion does not prove that taking a limit in the cutoff exponent preserves uniform constants.

The [bond-model article](articles/mean-field-cluster-moments.md) supplies four written deductions from the wiki's existing results:

| Assertion | What is established here |
|---|---|
| [Moment comparison](articles/mean-field-cluster-moments.md#section-moment-comparison) | A size-biased band at scale chi squared gives real-order higher moments and their ratios. |
| [Lattice gap](articles/mean-field-cluster-moments.md#section-lattice-gap) | The exploration score and small neighbouring triangle give a cubic second moment at every subcritical parameter in the stated range. The degree factor is retained. |
| [Cutoff tails](articles/mean-field-cluster-moments.md#section-cutoff-tail) | Weighted exponential moments give the upper cutoff; an intermediate parameter gives the lower critical window. Tail summation includes the half-order logarithm and finite lower critical moments. |
| [Large-cluster density](articles/mean-field-cluster-moments.md#section-large-cluster-density) | A fixed sufficiently small multiple of chi squared has root probability of order inverse chi and inverse-volume density of order inverse chi cubed. The exact moment-ratio cutoff and singular free energy are not identified. |

[Durrett–Nguyen (1985)](https://sites.math.duke.edu/~rtd/reprints/paper28.pdf), Section 5, printed pp.265–266 / PDF indices12–13, was also read in extracted text. Its cluster/boundary Cauchy–Schwarz calculation motivates the second-moment reduction. Here UTUF/4GNM give a separately justified countable bond argument, including the integrated passage and almost-everywhere derivative. Moment continuity extends the resulting inequality to every parameter.

The conclusions apply in sufficiently large dimensions through the classical bootstrap. The numerical dimension threshold and the regularization needed for an arbitrary finite triangle remain separate obligations. No new Lean association, source correction or visual-PDF verification is claimed.

## Quantified mean-field consequences

The [explicit-range section](articles/green-free-triangle.md#section-explicit-susceptibility) supplies a common range d>=10^11 for the susceptibility, critical field and tail, density, and moment-cutoff arguments. YT0O bounds the critical neighbouring triangle by 189/d. E5ZR verifies the positive field coefficient at least 2/11 by rational comparisons and an exponential-series bound, giving critical tail constants 1/360 and6 and density constants 1/3 and24 on the scale 2d(p-p_c). 9TAI gives the subcritical second-moment lower bound chi cubed/3, upper tail 8 n^(-1/2) exp[-n/(4 chi squared)], and lower tail 1/(139968 sqrt(n)) for n<=chi squared/6, for p_c/2<=p<p_c. The real-order moment regimes follow by the existing tail-sum argument. The exact comparison script is reproduced in the article.

This is a coarse independent quantification of the written proof chain, not a sharp numerical dimension claim from the source. It does not settle arbitrary finite-triangle regularization, limiting amplitudes or tail profiles. All previous statements, provisional errata and formal statuses are preserved.

## Finite triangles without a smallness assumption

The [finite-triangle endpoint theorem](articles/triangle-susceptibility.md#section-finite-triangle), ADWR, combines the proved corrected boundary inequality with reciprocal integration. For normalized transitive unimodular weights, a finite susceptibility threshold b and finite critical diagonal triangle D give 1/(b-beta)<=chi(beta)<=2 D squared+3 beta b D squared/(b-beta). The existing entropy and tail-field arguments then give the two-sided critical square-root tail and field law. [I23O](articles/triangle-susceptibility.md#section-finite-triangle-lattice) identifies the endpoint and adds the supercritical density lower bound for nearest-neighbour lattice percolation by sharpness.

The [moment and cutoff extension](articles/mean-field-cluster-moments.md#section-finite-triangle-cutoff), 7T8L, obtains a cubic second moment from the boundary derivative and exploration score. A size-biased band and continuity of the moment ratio give a lower tail up to alpha chi squared/2, and the critical/exponential upper bounds give the susceptibility-squared cutoff, all positive real moment orders and fixed-cutoff inverse-volume estimates. These are model-dependent constants, not the uniform high-dimensional constants of the earlier results. No small-neighbouring-triangle hypothesis is used.

These deductions complete the general finite-triangle implication previously left separate in this map. They use a different proof from classical endpoint separation: that surgery argument itself is still not supplied. They do not establish triangle finiteness in a new dimension, transfer site-percolation normalizations unchanged, identify a limiting amplitude or cutoff profile, or prove a singular free-energy asymptotic. The original source statements and all provisional errata remain unchanged; no compiled status is asserted.
