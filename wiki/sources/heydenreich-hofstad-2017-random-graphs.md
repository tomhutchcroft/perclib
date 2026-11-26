# Heydenreich–van der Hofstad: critical random graphs

Section 13.1 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf) has been read in full in extracted text, printed pp.152–158 / PDF indices163–169. The chapter introduction on printed p.151 was also read. Published-edition and visual-page comparison remain unavailable.

| Locator | Wiki coverage |
|---|---|
| 13.1.15; Exercises 13.2–13.3 | [Exploration](articles/critical-random-graph-clusters.md#section-exploration) gives both comparisons, stopping the lower coupling when k vertices have been discovered. |
| 13.1.16–13.1.18; Exercise 13.4 | [Binomial progeny](articles/critical-random-graph-clusters.md#section-progeny) supplies uniform estimates from Dwass, Fourier inversion, Stirling bounds and the survival fixed point. |
| Proposition 13.3; Lemma 13.4; Exercise 13.5 | [Root tails and susceptibility](articles/critical-random-graph-clusters.md#section-tails) retain the size cutoff and distinguish the negative-window susceptibility upper bound. |
| Proposition 13.2 | Existing [25Z4](articles/cluster-partitions.md#section-cluster-covariance), applied to threshold indicators, supplies the variance estimate without a new assertion. |
| Theorem 13.1; Exercise 13.1 | [Largest component](articles/critical-random-graph-clusters.md#section-largest) proves both tails, including integer rounding and a threshold in n independent of A. |
| 13.1.1–13.1.4 | Sharp off-window asymptotics, duality and the joint critical scaling limit are context here, not consequences of this tightness proof. |

The new article proves the critical-size argument. Later torus comparisons and scaling limits remain separate work. No new source erratum, author confirmation or compiled association is asserted.

## Quotient comparison and high-dimensional tori

Section 13.2 has now been read in full in extracted text, printed pp.158–160 / PDF indices169–171.

| Locator | Wiki coverage |
|---|---|
| Proposition 13.7 | [Neighbour lifting](articles/quotient-cluster-bounds.md#section-lifting) proves stochastic domination by stopped finite exploration, for countable locally finite graphs. The orbit-map hypothesis is checked directly. |
| 13.2.4–13.2.5; upper part of Theorem 13.5 | [Critical torus bound](articles/quotient-cluster-bounds.md#section-torus) combines lattice critical tails with the lifting argument. Vertex counting retains an A to the power minus three-halves bound; integrating it also bounds largest-component moments below order three-halves. |
| Theorem 13.6 exponential upper tail | Existing rooted damping 12NL upgrades the power bound to the exponential upper bound in the torus article. It gives all positive largest-component moments; existing hyperscaling WRHL also gives the susceptibility upper bound. |
| Theorem 13.5 lower bound; Theorem 13.6 ordered components | Matching lower bounds and lower bounds for the other ordered components remain separate. |

No second cluster-covariance theorem is introduced. The general finite-volume upper-tail deduction also applies to dependent random graphs whenever its uniform root-tail hypothesis holds. The proof does not use a configuration projection that changes edge marginals.

## Susceptibility-defined finite critical points

Section 13.3 has now been read in full in extracted text, printed pp.161–168 / PDF indices172–179. The following rows separate proved deductions from the chapter's cited finite-triangle inputs.

| Locator | Wiki coverage |
|---|---|
| 13.3.1 | [Susceptibility level](articles/finite-graph-criticality.md#section-parameter): existence and uniqueness with the target level in its valid range. |
| 13.3.2–13.3.5 | [Constant mode](articles/finite-graph-criticality.md#section-triangle): exact complete-graph matrix formula and the necessary volume contribution. |
| Exercise 13.7; 13.3.13–13.3.18 | Existing [tree-graph moments](articles/multipoint-trees.md) and [weighted exponential series](articles/exponential-moments.md#section-series) are reused. |
| Lemma 13.10 | [Optimized tail](articles/finite-graph-criticality.md#section-optimized-tail): the admissible optimizer retains the square-root prefactor. |
| Theorem 13.8 upper bound; Exercise 13.8 | [Largest-component bounds](articles/finite-graph-criticality.md#section-largest): logarithmic subcritical threshold and the exponential critical-window bound, conditional on the stated susceptibility estimate. |
| Exercise 13.9 | [One-sided parameter comparison](articles/finite-graph-criticality.md#section-parameter-comparison) from quotient domination and the lattice susceptibility upper bound. |
| Exercise 13.6; lower parts of Theorems 13.8–13.9; 13.3.23 | The finite-triangle differential estimates and lower critical-window root tails still need their own proof or primary-source reconciliation. |
| Theorem 13.11; Open Problems 13.1–13.2 | Supercritical conclusions and alternative critical-point definitions remain separate. The manuscript's historical open-problem descriptions are not current-status certifications. |

Two displayed-formula issues have provisional fixes: the common branch vertex in the tree event and the admissible exponential-parameter interval. Both retain the intended final estimates. Visual comparison of these pages remains unavailable.

## Hypercube mixing and the short-loop criterion

Section 13.4 is now fully read in extracted text. The [version-specific map](sources/hypercube-mixing.md) links the scalar recurrence proof of hypercube mixing and an explicit finite-triangle criterion. Two local book repairs separate the parity mode and replace a false uniform asymptotic equality by the upper bound needed in the proof. The primary NBW source has a separate operator-norm workaround; the hypercube short-loop sum has a direct Fourier-moment proof, while the critical-location and giant-component arguments remain unfinished. Section 13.5 has only been started.

## Subsequent critical-parameter proof

The [critical-parameter article](articles/hypercube-critical-parameter.md) now proves the susceptibility-threshold upper bound through a corrected boundary-growth induction, and supplies the sharper short-loop estimate. It concludes the finite triangle bound uniformly up to that threshold. The earlier article and its tagged statements are preserved. See the [new reading map](sources/hypercube-critical-parameter.md) for source versions and the provisional repairs.

## Subsequent finite-window proofs

The [finite-triangle window article](articles/finite-triangle-window.md) supplies susceptibility control below the reference parameter, finite-field estimates, a lower root tail with its cutoff, and largest-component tightness throughout a bounded window. The [reading map](sources/finite-triangle-window.md) distinguishes reconstructed proofs from source inputs and records the provisional Exercise13.6 normalization correction. The susceptibility upper bound above the reference parameter remains separate.

## Positive-window susceptibility completed

The [marked-volume article](articles/finite-window-susceptibility.md) now proves the expectation bound left open above: chi(p) is at most C(lambda)[N^(1/3)+m^2(p−p_c)^2N] for p_c <= p <= 1/2. It gives two-sided susceptibility throughout a bounded window, largest-component moments through order two, and uniform integrability below order two. The [reading map](sources/finite-window-susceptibility.md) records Section 8 and Appendix A.3 of the original finite-graph preprint. Off-window giant-component lower bounds and ordered limits remain separate.

## Supercritical density and concentration

The [large-cluster article](articles/finite-supercritical-clusters.md) now proves the shared-boundary variance estimate, field-growth lower bound, supercritical density at the mesoscopic cutoff, and concentration with a relative largest-component upper bound. Its [reading map](sources/finite-supercritical-clusters.md) records the complete Section 9 and the necessary Section 5.2 and Section 6 arguments. A singleton-cutoff proof error is provisionally corrected with a local repair. A giant-component lower bound and geometric sprinkling remain separate.

## Sharper subcritical estimates

The [subcritical article](articles/finite-subcritical-clusters.md) now proves the integrated triangle estimate, a positive-denominator threshold bound, sharp susceptibility asymptotics and largest-component expectation and probability bounds below the window. Its [reading map](sources/finite-subcritical-clusters.md) distinguishes the corrected threshold formula from the source. The provisional statement correction has a complete fix; the component bounds retain a logarithmic gap.
