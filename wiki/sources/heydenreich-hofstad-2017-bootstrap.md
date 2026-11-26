# Heydenreich–van der Hofstad: the Fourier bootstrap

Read Sections 8.1–8.2 and the opening of Section 8.3 through part of Lemma 8.5 in the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf). The fully read section range is printed pp.89–96 / PDF indices100–107. This is extracted-text evidence; visual-page and published-edition checks remain unavailable. The full chapter has not been read or proved.

| Locator | Reconciliation |
|---|---|
| Lemma 8.1 | [NL05](articles/fourier-bootstrap.md#section-continuity) proves the continuous forbidden-region argument with the weak-to-strong implication explicit. |
| 8.1.4–8.1.10; Exercises 8.1–8.2 | Illustrative ODE bootstrap. The source example is read; the perturbed and delayed exercise formulations remain separate tasks. |
| 8.2.1–8.2.3; Exercise 8.3 | With lambda=1-1/chi, the zero-frequency walk transform is chi by direct substitution. [NL05](articles/fourier-bootstrap.md#section-continuity) supplies the surrounding regularity. |
| 8.2.4–8.2.8; 8.2.13–8.2.15; Exercise 8.4 | [NL05](articles/fourier-bootstrap.md#section-continuity) derives the discrete Fourier identity and proves finiteness and continuity of the supremum, including the k=0 convention. [8LOF](articles/fourier-bootstrap.md#section-moments) supplies the weighted continuity from subcritical susceptibility. |
| 8.2.9–8.2.10 | [TTS1](articles/fourier-bootstrap.md#section-walk) proves the comparison with factor 2/(1+lambda). No inference from a possibly missing factor in the extracted equality is used. |
| 8.2.11–8.2.18 | Motivation for frequency-diagram estimates. The claimed dimension-dependent smallness is not yet supplied by this map. |
| Lemma 8.2; 8.2.19–8.2.20; 8.2.22–8.2.30 | [84XD](articles/fourier-bootstrap.md#section-reciprocal) proves the reciprocal estimate with absolute values. The [provisional sign erratum](errata/heydenreich-hofstad.json#reciprocal-fourier-sign) records a finite-support counterexample to the unrestricted statement and a complete fix. |
| 8.2.21 | [TTS1](articles/fourier-bootstrap.md#section-walk) gives the unchanged positive random-walk specialization. |
| Proposition 8.3; Lemmas 8.4–8.5 and later sections | Reading has begun, but the frequency-diagram bounds and the quantitative bootstrap improvement remain unfinished. The previously supplied [AA7H](articles/lace-coefficient-diagrams.md#section-infrared-smallness) already gives a conditional weighted-triangle estimate; it is not an unconditional infrared theorem. |

The new erratum is a statement-scope repair with a complete written proof: reciprocal signs must be controlled, or the factors replaced by their absolute values. It does not alter the random-walk case and does not claim a changed percolation threshold or dimension. No author confirmation, published-edition verification or new compiled association is claimed.

## Completing the nearest-neighbour bootstrap

The full Chapter 8 has now been read in extracted text, printed pp.89–108 / PDF indices100–119. The following completes the previously unfinished quantitative bounds and critical passage. This does not claim visual-page or published-edition verification.

| Locator | Completed argument or remaining scope |
|---|---|
| Lemma 8.5 | [54IO](articles/bootstrap-diagram-bounds.md#section-triangles) gives the weighted triangle of order 1/d and the nontrivial full triangle bound. |
| Lemma 8.6 | [PEVH](articles/bootstrap-diagram-bounds.md#section-pair) proves both weighted-pair estimates; the unshifted estimate retains its extra 1/d. |
| Lemma 8.7; Exercise 8.5 | [L1Y7](articles/bootstrap-diagram-bounds.md#section-h) treats all three shifts by one Holder argument. The [connector-mass entry](errata/heydenreich-hofstad.json#h-diagram-prefactor) has a complete local normalization repair. |
| Proposition 8.3; Lemma 8.4 | [6G0E](articles/bootstrap-diagram-bounds.md#section-coefficients) sums the coefficient norms and frequency bounds. At order one it uses the refined (7.2.15), rather than the unrefined (7.2.14) cited at the end of the manuscript proof. |
| Lemma 8.9; Exercise 8.6 | [8LOF and NL05](articles/fourier-bootstrap.md#section-moments) already give weighted continuity and continuity of the third supremum, including frequencies approaching zero. |
| Lemma 8.11 | [W2WX](articles/completed-fourier-bootstrap.md#section-first) improves the edge mass and Fourier ratio and verifies positive effective reciprocals. The [local algebra entry](errata/heydenreich-hofstad.json#bootstrap-algebra-identities) records the sign correction. |
| Lemma 8.12 | [12ZK](articles/completed-fourier-bootstrap.md#section-second) supplies an exact quotient difference identity and a complete estimate with the required reciprocal signs established. The same local entry gives the corrected first-difference product formula. |
| Propositions 8.8 and8.10 | [MYG7](articles/completed-fourier-bootstrap.md#section-bootstrap) closes the pointwise improvement by continuity, with constants uniform in the subcritical parameter. |
| Corollary 8.13 | [F7N7](articles/completed-fourier-bootstrap.md#section-critical) passes the spatial diagrams and coefficient norms to criticality, then proves positivity and integrability of the critical Fourier density before Fourier inversion. |
| Exercises 8.1–8.2 | The illustrative ODE variants remain to be written; they are not prerequisites for the percolation proof above. |
| Exercise 8.7 | The next-order nearest-neighbour threshold asymptotic remains open in this map. The leading 2d p_c = 1+O(1/d) is supplied. |
| Exercise 8.8 | The spread-out bootstrap and its threshold normalization remain separate. The nearest-neighbour argument does not settle this exercise. |

Both new errata have fixes found and local significance: a connector prefactor and algebraic identities change, while the bounds and theorem hypotheses survive. The earlier reciprocal-sign repair is now checked in its effective-kernel application by W2WX and12ZK. All entries remain provisional; no author confirmation or new compiled association is asserted.

## A coarse explicit dimension bound

[NOTF and66SP](articles/bootstrap-diagram-bounds.md#section-explicit-diagrams) retain numerical constants in the existing diagram proof with weak bootstrap bound two. The finite certificate I_(40,6)<669/500 yields triangle, pair and H bounds; exact geometric sums give a full weighted coefficient budget of 50000000/d. [7GNW](articles/completed-fourier-bootstrap.md#section-explicit-dimension) then closes the bootstrap for every integer d>=10^11, with infrared amplitude at most 521/500 and 2d p_c at most 1001/1000. It supplies the critical normalization, absolute second moments, finite clusters, quadratic gap and sixth-norm smallness required by FWHO. Thus the Gaussian spatial expansion with remainder exponent 4/(d+2), the coefficient tail of exponent 2(d-2), and weighted critical continuity for s<d-4 hold in that explicit range. A complete standard-library rational certificate is reproduced with the proof.

This is an independent, deliberately coarse quantification of the written argument, not a numerical dimension claim attributed to the source. It does not settle the conditional hypotheses at dimensions 15, 40, 64 or100, or the dimension range near six. The earlier statements, provisional errata and formal statuses are unchanged.
