# Heydenreich–van der Hofstad: branching random walk

Read §2.2 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.22–25, PDF indices33–36. The record uses extracted text; published-edition correspondence and visual-page verification remain unchecked.

| Locator | Reconciliation |
|---|---|
| Opening model discussion; 2.2.1 | [Model and occupation](articles/branching-random-walk.md#section-model); [exceptional root](articles/embedded-branching-trees.md#section-occupation). |
| 2.2.2–2.2.6; 2.2.18 | [8KZO](articles/embedded-branching-trees.md#section-occupation): displacement independence survives conditioning on extinction. |
| 2.2.7; 2.2.10 | [Generation-zero correction](../errata/heydenreich-hofstad.json#generation-zero-occupation), with homogeneous and regular-root conventions separated. |
| 2.2.8–2.2.9 | [94E7 and 02EB](articles/branching-random-walk.md): Green occupation identity and finite-range spatial equivalent. Critical finiteness requires dimension at least three. |
| 2.2.11–2.2.14 | [Abel limit and spectral density](articles/embedded-branching-trees.md#section-occupation), with the integrability condition explicit. |
| 2.2.15 | [MC4U](articles/embedded-branching-trees.md#section-radius) proves radius probability comparable to the inverse square. |
| 2.2.16 | [TX3U](articles/embedded-branching-trees.md#section-axis-length): exact coordinate decay rate by exponential tilting. |
| 2.2.17; 2.2.19 | [8KZO](articles/embedded-branching-trees.md#section-occupation): exact second-moment length and its near-critical amplitude. |
| Theorem 2.2, genealogical exponents | [Regular-tree laws](articles/regular-tree-percolation.md), including corrected conditioning and the root constants. |
| Theorem 2.2, spatial exponents | [Embedded-tree proofs](articles/embedded-branching-trees.md): both length exponents, the two-point exponent in dimension at least three, and the logarithmic radius exponent. |

The source omits the spatial-radius proof. MC4U supplies comparison bounds using a branching-map supersolution and a generation second moment; an exact radius asymptotic constant remains outside its claim. The root-count discrepancy has a written local repair and remains provisional. The model's occupation field is not a percolation two-point function. Chapter 3, published-edition comparison and new compiled associations remain separate work.


## Further spatial asymptotics

[S78W](articles/embedded-branching-trees.md#section-axis-prefactor) adds the exact transverse integral and the full axis prefactor to TX3U's exponential rate. [LEJR](articles/embedded-branching-trees.md#section-massive-crossover) gives a continuum profile with a uniform absolute error as the killing parameter approaches criticality. The relative estimate is restricted to bounded mass times distance; the fixed-subcritical lattice rate is different from the continuum mass.

These are deductions from the nearest-neighbour walk kernel and the existing localized Fourier estimate, not additional claims read in the manuscript. Both retain the exceptional-root occupation factor of 8KZO. No new source reading, source error, independent audit, percolation asymptotic or Lean verification is claimed.
