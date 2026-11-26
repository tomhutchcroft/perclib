# Heydenreich–van der Hofstad: green-free clusters and mean-field bounds

The full Chapter 9 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf) has been read in extracted text, printed pp.109–119 / PDF indices120–130. Visual-page and published-edition verification remain unavailable. The article supplies the bounded-ratio high-dimensional results, including the previously abbreviated green-free diagram estimates.

| Locator | Reconciliation |
|---|---|
| Exercise 9.1 | The ghost formula and coupling in [J2TE](articles/ghost-fields.md) and [G192](articles/sharpness-bond-parameter.md#section-differential-inequalities) give monotonicity in both parameters. Each finite-cluster summand is concave in the field, and infinite clusters contribute a constant. |
| Lemma 9.1; 9.1.2–9.1.6 | [OB0K](articles/green-free-triangle.md#section-differential) proves the differential inequality with the triangle-size condition explicit. The [scope entry](errata/heydenreich-hofstad.json#triangle-coefficient-scope) has a complete statement repair. |
| Exercise 9.2 | [C2V4](articles/green-free-triangle.md#section-amplitude) derives the coefficient limit 1/(2e) from the completed bootstrap. |
| Lemma 9.3 | C2V4 integrates the inequality from positive field, takes the zero-field limit, and supplies the uniform upper square-root bound with constant square root 12. |
| Theorem 9.2; 9.2.6–9.2.11 | [ZK0V](articles/green-free-triangle.md#section-tails) gives explicit two-sided tail constants and handles n=1. The [numerical constant entry](errata/heydenreich-hofstad.json#critical-tail-constant) is a local repair of the final substitution. |
| Theorem 9.4 | The sharp local cluster-size asymptotic is attributed to Hara–Slade and is not proved here. It requires the later superprocess analysis; bounded-ratio tail estimates do not imply it. |
| Exercise 9.3; 9.3.2–9.3.10 | [JR88](articles/green-free-triangle.md#section-extrapolation) performs the field reparametrization and integrates the inverse-level slope only on its valid domain. The almost-everywhere chain-rule issue is handled by a locally bi-Lipschitz change of coordinates and Fubini. |
| Theorem 9.5 | [74SS](articles/green-free-triangle.md#section-exponents) gives dimension-uniform density bounds on the scale 2d(p-p_c), clipped at one. The [dimension-scale entry](errata/heydenreich-hofstad.json#density-dimension-scale) explains why unscaled uniform constants cannot hold. |
| Open Problem 9.1 | The sharp density asymptotic is not resolved by the bounds above. Its current status outside the dated manuscript is not assessed. |
| Lemma 9.6; 9.4.1–9.4.10 | OB0K proves the last-pivotal cutting identity, including the conditional coordinate supports and finiteness before subtracting the signed loss. |
| 9.4.11–9.4.24 | OB0K derives the two-green-cluster lower bound and the single-bond loss. The positive-part convention controls multiplication of lower bounds. |
| Lemma 9.7 | [J3M4](articles/green-free-triangle.md#section-green-free) proves green-free BK by conditioning on the green-connected set. Infinite-volume passage uses bounded convergence of indicators. |
| 9.4.25–9.4.37 | OB0K bounds the signed deletion loss by a nonnegative green-free connection event before enlarging the other indicator. The four disjoint path witnesses are constructed by the first hit of two green arms. |

The three entries have fixes found: one local numerical repair and two statement-scope repairs. The high-dimensional mean-field conclusions are supplied with their corrected hypotheses and dimension normalization. All source diagnoses remain provisional, with no author confirmation or new compiled association. This is separate from the reverse-BK work assigned to FIXER.

## Finite cutting proof and author-version comparison

The [finite magnetization article](articles/finite-magnetization-deletion.md) gives the complete signed-deletion, two-cluster and last-pivotal argument. Its [reading map](sources/finite-magnetization-deletion.md) compares the early preprint with the September 2004 author revision, which already repairs the cubic coefficient and diagonal convention. A separate scope entry proves the positive-part replacement and gives an exact K4 counterexample to the unrestricted later polynomial. Existing small-triangle statements are unchanged.

## Quantified mean-field consequences

The [explicit-range section](articles/green-free-triangle.md#section-explicit-susceptibility) supplies a common range d>=10^11 for the susceptibility, critical field and tail, density, and moment-cutoff arguments. YT0O bounds the critical neighbouring triangle by 189/d. E5ZR verifies the positive field coefficient at least 2/11 by rational comparisons and an exponential-series bound, giving critical tail constants 1/360 and6 and density constants 1/3 and24 on the scale 2d(p-p_c). 9TAI gives the subcritical second-moment lower bound chi cubed/3, upper tail 8 n^(-1/2) exp[-n/(4 chi squared)], and lower tail 1/(139968 sqrt(n)) for n<=chi squared/6, for p_c/2<=p<p_c. The real-order moment regimes follow by the existing tail-sum argument. The exact comparison script is reproduced in the article.

This is a coarse independent quantification of the written proof chain, not a sharp numerical dimension claim from the source. It does not settle arbitrary finite-triangle regularization, limiting amplitudes or tail profiles. All previous statements, provisional errata and formal statuses are preserved.
