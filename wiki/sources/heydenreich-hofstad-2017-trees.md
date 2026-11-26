# Heydenreich–van der Hofstad: regular trees

Read §2.1 of the [17 March 2017 author manuscript](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf), printed pp.17–22, PDF indices28–33. The reconciliation uses extracted PDF text; no visual-page or published-edition verification is claimed.

| Locator | Reconciliation |
|---|---|
| Theorem 2.1; 2.1.1–2.1.7 | [0JTK](articles/regular-tree-percolation.md#section-duality): root degree and forward degree remain distinct. |
| Exercise 2.1; moment-gap discussion | [1KBO](articles/regular-tree-percolation.md#section-moments): both sides, all positive moment orders. |
| 2.1.8–2.1.18; Exercise 2.2 | [0JTK](articles/regular-tree-percolation.md#section-duality): fixed points, survival and amplitudes for degree at least three. The source treats the line separately. |
| 2.1.19–2.1.23 | [Correct conditional law](articles/regular-tree-percolation.md#section-duality); provisional [duality erratum](../errata/heydenreich-hofstad.json#extinction-conditioning). |
| 2.1.24; Exercise 2.3 | Existing [one-ancestor Dwass proof](articles/branching-processes.md#section-dwass) and the [forest queue](articles/regular-tree-percolation.md#section-forest-progeny). |
| Exercise 2.4; 2.1.26 | [UPOZ](articles/regular-tree-percolation.md#section-forest-progeny); provisional [target correction](../errata/heydenreich-hofstad.json#forest-hitting-target). |
| 2.1.27 | [LS6G](articles/regular-tree-percolation.md#section-size-law): forward formula and exact root law. |
| 2.1.28–2.1.29 | [1KBO](articles/regular-tree-percolation.md#section-moments); provisional [constant correction](../errata/heydenreich-hofstad.json#local-to-tail-constant). |
| 2.1.30–2.1.31; Exercise 2.5 | [X9U3](articles/regular-tree-percolation.md#section-survival); provisional [error-rate correction](../errata/heydenreich-hofstad.json#survival-error-rate). |
| Exercise 2.6 | [Bounded-degree path counting](articles/bounded-degree-paths.md): the sharper threshold bound does not require transitivity. |

The four reported discrepancies have written repairs. The first changes a conditional parameter and the resulting finite-cluster formulas; the next two correct a target and a constant; the last weakens the claimed error rate and supplies its missing term. The critical exponents remain unchanged. Confirmation and Lean correspondence are separate: no new compiled association is supplied.

Section 2.2 and later chapters remain to reconcile. This map does not identify a branching-walk occupation count with a percolation connection probability.
