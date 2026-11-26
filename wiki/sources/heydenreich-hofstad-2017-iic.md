# Heydenreich–van der Hofstad: incipient infinite clusters

Chapter 12 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf) has been read in full in extracted text, printed pp.147–150 / PDF indices158–161. Its percolation construction is a sketch with cited analytic inputs; the reading does not turn that sketch into a complete existence or uniqueness proof. Published-edition and visual-page comparison remain unavailable.

| Locator | Reconciliation |
|---|---|
| Section 12.1; Theorem 12.1 | Existing [E22E](articles/size-biased-laws.md#section-local-cluster-limits) constructs subsequential cylinder limits for susceptibility bias, distant-point conditioning and arm conditioning, and proves that their root clusters are infinite. It does not identify the limits or prove full-sequence convergence. |
| Remarks after Theorem 12.1 | Countable finite-coordinate consistency gives the probability measure. Percolation one-endedness and shared pivotal structure are still separate inputs. No arm exponent is needed merely for subsequential cylinder compactness. |
| Theorem 12.2 upper bound; 12.2.5–12.2.9 | [N20X](articles/incipient-cluster-limits.md#section-biased-bound) proves the bubble bound through finite-box events. The [provisional noncylinder-limit entry](errata/heydenreich-hofstad.json#iic-noncylinder-limit) has a complete local repair to this proof; the displayed full-event equality is not used or established. |
| Exercise 12.1 | [G86R](articles/incipient-cluster-limits.md#section-point-bound) proves the same upper bound from distant-point conditioning. A split near the distant endpoint controls the convolution tail; pointwise convergence of the ratio alone is not substituted for dominated convergence. |
| Lemma 12.3; Exercise 12.2 | Existing [SBWK, XCA8, RMFH and SYJ4](articles/size-biased-laws.md#section-spine) provide survival conditioning, consistent size bias, the explicit spine and total-variation convergence. [JNOW](articles/size-biased-laws.md#section-mass) gives generation and ball means. These proofs are reused, not duplicated. |
| 12.2.16–12.2.18 | The marked-event lace equation gives the displayed susceptibility-biased limit if the event-dependent coefficients converge in l1 and the susceptibility diverges. Construction of those coefficients, a uniform summable bound and convergence are not proved by the algebraic cancellation in the sketch. |
| Remaining parts of Theorems 12.1 and 12.2 | The model-specific lace construction, identification of susceptibility bias, one-endedness and the lower two-point bound are not proved here. The later cited [Q7E9](articles/size-biased-laws.md#section-high-dimensional-iic) already gives a common distant-set and supercritical-conditioning limit under two-sided spatial bounds in d>6, without the book's stronger arm-exponent hypothesis. It is a cited input, not a new proof in this chapter map. |

One new diagnosis is provisional with a complete local proof repair. No author confirmation, independent mathematical audit or new compiled association is claimed.


## Intrinsic volume in the cylinder limits

The [short-path tree estimate](articles/incipient-cluster-limits.md#section-short-tree), 0HRJ, is an additional deduction from the existing multipoint BK proof. A breadth-first tree preserves the intrinsic-radius restrictions; one unrestricted leaf accounts for the cluster-volume bias. For k>=1 it gives E_Qp |B(r)|^k <= (2k-1)!! [E_p |B(r)|]^(2k).

[KIGU](articles/incipient-cluster-limits.md#section-intrinsic-limit-moments) passes these bounds to every susceptibility-biased cylinder limit. It also covers distant-point limits under the explicitly stated fixed-shift ratio limit for the critical two-point function. The intrinsic-ball observable is a bounded cylinder function on the nearest-neighbour lattice. In the distant-point diagram, every position other than the conditioned endpoint is restricted to a finite deterministic ball, which justifies the ratio passage without an infinite-sum domination claim.

[Z78U](articles/incipient-cluster-limits.md#section-intrinsic-volume-tail) combines finite-triangle susceptibility and thinning to give exponential upper tails on the radius-squared scale, and an almost-sure upper bound of order r squared log log r. This does not supply the matching quadratic lower volume, spectral dimension, one-endedness, full-sequence convergence or equality of constructions. No new erratum or compiled status is claimed; the earlier noncylinder-limit repair and its provisional status remain unchanged.


## Matching intrinsic lower volume and resistance

The lower-volume task left separate above is now supplied by [KGPE/RG3Z](articles/incipient-cluster-limits.md#section-boundary-density). A stopped intrinsic boundary controls residual cluster mass under susceptibility bias. The critical arm bound then gives a lower-volume probability of order epsilon on the radius-squared scale. With the existing upper tail this yields intrinsic volume exponent two almost surely. [3FTE/POD2](articles/incipient-cluster-limits.md#section-history-transfer) give the event comparison and linear resistance growth using uniform subgraph arms and disjoint cutsets. The [Kozma–Nachmias source map](sources/kozma-nachmias-2009-intrinsic-iic.md) distinguishes their original distant-point arguments from the separately proved susceptibility-biased extension. Random-walk consequences and identification of IIC constructions remain separate; no prior erratum or formal status is changed.
