# Triangle paper: initial source check

Inspected [HTML](https://arxiv.org/html/2106.06400v3) and
[PDF text](https://arxiv.org/pdf/2106.06400v3), 15 November 2026.

| Locators | Wiki disposition |
| --- | --- |
| Lemma 2.1, printed pp. 11–12 | [Positive-part correction and counterexample](../articles/boundary-susceptibility.md) |
| Equations (2.4)–(2.5), printed p. 12 | [Squared-numerator consequence](../articles/boundary-susceptibility.md) |
| Proposition 1.8; Appendix A | [Mass-transport diagram bound](../articles/connection-kernels.md) |

Both renditions contain the boundary formula and Cauchy–Schwarz inputs discussed
in the linked article. The correction concerns the nontransitive lemma; the
stronger numerator also has a [small-intensity counterexample](../articles/boundary-susceptibility.md). The source diagnoses remain provisional pending author confirmation.

## Expanded reading map

The initial heading and three locators are retained. The following map adds 24 passage groups across Sections 1–4 and Appendix A of arXiv:2106.06400v3. The PDF is dated 28 July 2022; the later HTML conversion date is not a new paper edition. Numbered locators refer to this version, not an unchecked journal edition.

Article links preserve the historical critical-methods revision 18ab9d7cfea0056c5f234b744386bc7420fa6f86 inspected for this map. They identify existing exposition, alternative arguments and gaps; they are not reviewed source occurrences or evidence of Lean compilation. A passage count measures the reading inventory, not completed mathematics.

## Section 1: statements and dependencies

| Source locator | Existing exposition and remaining obligation |
| --- | --- |
| Theorem 1.1; Proposition 1.7 | [4KBG](../articles/boundary-susceptibility.md) proves the corrected squared-positive-part inequality almost everywhere. Its row bound, finite susceptibility and mass-transport assumptions are explicit. [MTYL and 1EWX](../articles/boundary-susceptibility.md) refute the stronger numerator. These are replacement targets, not exact source correspondences. |
| Corollary 1.2 | [6PGV](../articles/integrated-susceptibility.md) integrates the corrected inequality. Its prefactor has a factor two in the correction term and it needs no endpoint divergence. [TC6Q](../articles/integrated-susceptibility.md) retains its separate, stronger differential hypothesis; the two statements must not be conflated. |
| Theorem 1.3; Remarks 1.4–1.5 | [JL1S](../articles/stopped-exploration.md) supplies the tail comparison for positive intensities and positive integer thresholds. The truncated-cluster estimate stays available when susceptibility is infinite. The historical comparison of methods is not a further proved assertion. |
| Corollary 1.6 and its proof | [6PGV](../articles/integrated-susceptibility.md) and [QS3L](../articles/stopped-exploration.md) give a route from diagram control to logarithmic upper bounds. Matching lower bounds and optimal logarithmic exponents remain separate. The wiki does not turn the surrounding predictions into theorems. |
| Proposition 1.8 | [IZAO](../articles/connection-kernels.md) proves the diagram comparison under an explicit mass-transport property and finite susceptibility. Its current statement does not cover infinite susceptibility merely because the source locator does. |
| Section 1.4; Theorem 1.9 | The [hierarchical reading map](sources/hierarchical-2103.17013v1.md) tracks the critical two-point inputs. [MS6M](../articles/hierarchical-runaway.md) supplies a conditional diagram calculation. Neither pointer proves the off-critical correlation-length application inventoried below. |

## Section 2: the susceptibility argument

| Source locator | Existing exposition and remaining obligation |
| --- | --- |
| Equation (2.1) | [4800](../articles/integrated-susceptibility.md) supplies a two-cluster derivative identity on a countable group with its own integrability assumptions. [4KBG](../articles/boundary-susceptibility.md) uses an integrated Russo argument for the boundary functional. A lower Dini derivative and an almost-everywhere derivative are not interchangeable without that passage. |
| Lemma 2.1; equation (2.3) | [67GX](../articles/boundary-susceptibility.md) retains the positive part before squaring, the last-exit path outside the set and a finite uniform susceptibility bound. [JTBG](../articles/boundary-susceptibility.md) explains the nontransitive obstruction. The original three-entry check above is preserved. |
| Equations (2.4)–(2.7) | [Weighted cluster moments](../articles/boundary-susceptibility.md) and [4KBG](../articles/boundary-susceptibility.md) keep the susceptibility factors through the random-cluster Cauchy–Schwarz calculation. The three tree orientations supply the denominator estimate; they do not recover the stronger numerator. |
| Equations (2.8)–(2.10) | [CS16](../articles/connection-kernels.md) and [IZAO](../articles/connection-kernels.md) provide a matrix-and-trace route. The Fourier argument and its choice of dual group are not separately supplied by these articles. No Fourier source correspondence is inferred from the common conclusion. |

## Section 3: entropy and exploration

| Source locator | Existing exposition and remaining obligation |
| --- | --- |
| Theorem 3.1; Remark 3.2 | [D66F](../articles/entropy-comparison.md) uses one Borel output rule for the full transcript and assumes positive intensities and finite weighted cost. It covers infinite runs. Completion of a sigma-algebra separately under each law does not supply the required rule. |
| Equations (3.2)–(3.3); Lemma 3.3 | [Entropy chain rule](../articles/entropy-comparison.md), [58HC](../articles/entropy-comparison.md) and [KHB7](../articles/entropy-comparison.md) supply the event comparison and coordinate cost. The Bernoulli estimate uses a Poisson comparison; zero-weight coordinates have zero cost. General measure-space entropy theory is not claimed here. |
| Equations (3.5)–(3.7) | [CH4N](../articles/entropy-comparison.md) gives the finite-transcript identity with revealments under the first law. [D66F](../articles/entropy-comparison.md) passes to Borel events by finite-prefix approximation. This alternative proof avoids a separate theorem on infinite-transcript relative entropy. |
| Equations (3.8)–(3.9) | [28UY and PWBU](../articles/stopped-exploration.md) construct a fair countable exploration; [DCRV](../articles/stopped-exploration.md) bounds weighted cost; [JL1S](../articles/stopped-exploration.md) performs the probability comparison. Halting and Borel computation are kept distinct, including on graphs of infinite degree. |

## Section 4: the hierarchical application

| Source locator | Existing exposition and remaining obligation |
| --- | --- |
| Theorems 1.9 and 4.1 | The current articles do not give a complete proof of these applications. [QS3L](../articles/stopped-exploration.md) handles logarithmic susceptibility inputs; a general power-law input needs its own optimization. Critical two-point bounds alone are not an off-critical susceptibility theorem. |
| Equation (4.5) | The finite-volume application must use [the corrected quadratic inequality](../articles/boundary-susceptibility.md). The positive part can be compared with susceptibility only after a uniform separation from the triangle diagram has been established. This map does not silently import the stronger printed formula. |
| Lemma 4.2; equation (4.6) | [The finite-set criterion](../articles/integrated-susceptibility.md) and [FF30](../articles/hierarchical-runaway.md) provide related first-exit and boundary-flux inputs. The root-containing set, restricted connection law and intensity normalization must agree before reusing them in this application. |
| Equation (4.7); Lemma 4.3 | The scale defined by successive boundary thresholds and the off-critical block comparison still need dedicated exposition. [7YNX](../articles/hierarchical-runaway.md) concerns critical two-point bounds and does not fill this gap. |
| Proposition 4.4; Remarks 4.5–4.6 | The remaining application needs uniform finite-block diagram estimates, integration over the threshold interval, and conversion back to the chosen length scale. [MS6M](../articles/hierarchical-runaway.md) supplies a critical diagram input only. Improved multipoint estimates and optimal exponents remain separate tasks. |

## Appendix A: matrix and trace arguments

| Source locator | Existing exposition and remaining obligation |
| --- | --- |
| Lemma A.1; Remark A.2 | [70KD](../articles/connection-kernels.md) proves positive semidefiniteness from the cluster partition, without independence. A uniform strictly positive lower operator bound from singleton probabilities is not part of that assertion. |
| Lemma A.3 | [UZ7J](../articles/connection-kernels.md) and [C2YT](../articles/connection-kernels.md) give the cubic diagonal and first diagram comparisons. Their finite diagonal bounds and symmetry assumptions are explicit. The existing open-triangle decay proof is a separate result. |
| Proposition A.4; Theorems A.5–A.6; Lemmas A.7–A.8 | [CS16](../articles/connection-kernels.md) proves the finite comparison by an eigenvector expansion; [87W3](../articles/connection-kernels.md) passes its needed special case to the countable connection kernel by finite principal matrices. These do not reproduce the general Schur, Ando or block-matrix theorems. The order is positive semidefinite order, not entrywise order. |
| Lemma A.9; Proposition A.10; Lemma A.11 | [IZAO](../articles/connection-kernels.md) proves the signed trace identity after establishing absolute convergence. Its final quadratic form avoids the general square-root and positive-trace-product lemmas. Those general statements remain outside the supplied exposition. |
| Final proof of Proposition 1.8 | [IZAO](../articles/connection-kernels.md) completes the finite-susceptibility diagram comparison. A source claim at an endpoint with divergent susceptibility needs a separately justified limiting argument; a limit of the diagrams is not supplied merely by citing this tag. |

## Recorded source corrections and Lean obligations

The [source-correction concordance](sources/source-corrections-b20bbd7.md) preserves the existing provisional boundary-positive-part and triangle-numerator records. Their [current pinned source record](../errata/hutchcroft-triangle-2021.json) gives the affected tags and formal obligations. The corresponding [private errata page](../errata/hutchcroft-triangle-2021.json) may advance after this map's snapshot.

A Lean proof of the corrected inequality must retain its hypotheses and almost-everywhere qualification; it cannot certify the stronger printed numerator. The reciprocal integration and logarithmic transfer are separate obligations. No assertion tag, mathematical statement, source verdict or compiled association is added here. The general Appendix A results, the hierarchical off-critical application, the bibliography and journal-version reconciliation remain unfinished.


## Appendix A proof completion and current reconciliation

The historical map above is preserved. Its matrix gaps are now supplied by the following additions, checked against arXiv v3 HTML and PDF text. The functional calculus uses the bounded self-adjoint spectral theorem as an explicit standard input; no formal correspondence is inferred.

| Source locator | Current proof and scope |
| --- | --- |
| Lemma A.1; Remark A.2; operator-norm discussion | [R1HO](../articles/connection-kernels.md#section-singleton-lower) retains singleton cluster squares and gives the common bound exp(-beta L). [The row-and-column argument](../articles/connection-kernels.md#section-schur) proves boundedness separately. |
| Theorem A.5 | [TAB8](../articles/connection-kernels.md#section-schur) proves the general Schur theorem by finite Gram matrices and its operator norm bound by tensor compression. Finite restrictions characterize semidefiniteness; a uniform positive lower bound must use the same constant on every restriction. |
| Lemmas A.7–A.8 | [530W](../articles/connection-kernels.md#section-block-matrices) completes the square for bounded operators with an invertible lower block, and diagonalizes equal-diagonal blocks. Density justifies the possibly non-finitely-supported minimizing vector. |
| Theorem A.6; Proposition A.4 | [0FTH](../articles/connection-kernels.md#section-ando) treats commuting bounded semidefinite operators, including singular ones, through Gram block factorizations. No inverse is assumed. The general bounded-operator comparison extends the existing finite CS16. |
| Lemma A.9 | [Z4JP](../articles/connection-kernels.md#section-invariant-roots) uses unitary conjugation and uniqueness, retaining the square-root norm exponent one half. |
| Proposition A.10; Lemma A.11 | [AKHL and F77F](../articles/connection-kernels.md#section-faithful-trace) give closure, a faithful tracial state and nonnegative trace of a positive pair. The positive pair need not commute; absolute convergence precedes signed mass transport. |
| Proposition 1.8 at the critical endpoint | [QGQ1](../articles/connection-kernels.md#section-diagram-limits) expands the nonnegative diagrams before monotone convergence. Finite susceptibility holds at each approximating parameter, while the limiting susceptibility may be infinite. Finite-path coupling supplies the intensity-law endpoint, with the infinite-threshold convention made explicit. |

Three appended [provisional errata](../errata/hutchcroft-triangle-2021.json) distinguish the uniform-lower-bound wording, the semidefinite proof's use of inverses, and the square-root norm exponent. They repair intermediate steps without changing the Schur, Ando, invariant-root or diagram conclusions. Neither author confirmation nor a journal-version check is claimed.

The earlier Section 4 gap entries are also historical: [6F2J](../articles/hierarchical-runaway.md#section-boundary-scales), [OVWJ](../articles/hierarchical-runaway.md#section-off-critical) and [WPAD](../articles/hierarchical-runaway.md#section-off-critical-tails) already supply the boundary-scale, susceptibility, length, tail and density deductions under their stated endpoint two-point and flux inputs. The source-corrected square is used after separation from the triangle diagram. These conditional proofs do not discharge those endpoint inputs. The present change reconciles those existing proofs and does not create a competing application.

Remaining work includes the independent source/correspondence audit, the full journal-edition comparison, bibliography, the separate Fourier derivation and reconciliation of the hierarchical endpoint inputs. The matrix appendix's listed propositions now have prose proofs with their analytic inputs identified; this does not certify every source sentence or a Lean implementation.


## Fourier argument completed on both source groups

The [Fourier proof](../articles/connection-kernels.md#section-fourier-diagrams) (F77A) supplies equations (2.8)–(2.10) on the Euclidean lattice and the hierarchical direct sum. The duals are respectively the torus and the compact product of finite character groups. Finite character quadratic forms establish transform positivity without invoking an unproved identification of the dual; absolute summability justifies the Fourier expansions. Hölder and convolution Cauchy–Schwarz then give both diagram inequalities. The passage uses normalized Haar measure, and the existing hierarchical-dual erratum is retained without reclassification. Critical kernels with infinite row sum use QGQ1, not an asserted convergent Fourier series.

This closes the separate Fourier-exposition gap recorded immediately above. Independent correspondence, the full journal-edition and bibliography checks, and reconciliation of the hierarchical endpoint inputs remain.
