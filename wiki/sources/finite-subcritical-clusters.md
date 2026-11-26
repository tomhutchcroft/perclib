# Finite graphs below the critical window

The [article](articles/finite-subcritical-clusters.md) retains the triangle error in the susceptibility integral and combines existing root-tail bounds to control the largest component below the window.

| Source and locator | Reading and coverage |
|---|---|
| [Borgs–Chayes–van der Hofstad–Slade–Spencer](https://arxiv.org/pdf/math/0401069), arXiv:math/0401069v1, Section 1.2 and Theorem 1.5, printed pp.4 and7 / PDF indices3 and6 | The standing susceptibility normalization and the precise strong-triangle hypotheses were checked. The sharp susceptibility asymptotic is proved with fixed constants and a uniform gap below a=1. |
| Same preprint, Section 4.1, (4.1)–(4.4), printed p.19 / PDF index18 | The integrated error is reconstructed from the existing five-factor differential bound. A positive denominator repairs the threshold upper bound throughout a<1. The weakened denominator in (1.30) needs an additional positivity hypothesis; an exact complete-graph example establishes the issue. |
| Same preprint, Section 4.2, (4.5)–(4.6), printed pp.19–20 / PDF indices18–19 | The expectation upper bound is proved by a real cutoff; the existing optimized tail supplies the probability bound. The new expectation proof also permits nonuniform independent bonds. |
| Same preprint, Section 7, component lower bound, and Section 1.4, (1.34)–(1.36), printed pp.30–31 and8 / PDF indices29–30 and7 | Existing root-tail and covariance proofs give explicit lower constants, including rounding and cutoffs below one. The resulting off-window bounds retain their logarithmic gap. |

The source reading is extracted preprint text; the visual PDF and journal version were not compared. The threshold entry is provisional, with a complete fix of statement-level significance. No existing assertion was edited, and no new Lean verification or independent audit is claimed. A matching logarithmic component lower bound requires more than the argument given here. Giant-component lower bounds and geometric sprinkling remain separate.


## Completing the complete-graph benchmark

The additional reading covers Section 2.1.2, Theorem 2.1(i) and the comparison following (2.15), printed pp.12–13 / PDF indices11–12, and Section 3.4.2, (3.10), printed p.16 / PDF index15, of the same preprint. [P1F1/XF00](articles/finite-subcritical-clusters.md#section-tree-component-counts) now give an exact tree-count and variance proof of the missing logarithmic lower bound for $G(N,(1-\varepsilon)/N)$. Summing over a size interval is essential, as is cancellation of the quadratic finite-population term. [X0R0](articles/finite-subcritical-clusters.md#section-er-logarithmic-law) proves the leading size $2\varepsilon^{-2}\log(N\varepsilon^3)$ for every fixed rank, in probability and mean absolute normalized error, when $\varepsilon\to0$ and $N\varepsilon^3\to\infty$. This is a written complete-graph argument; the general triangle-condition gap remains. The book theorem cited by the source was not independently read, and no new erratum or joint critical-window limit is claimed.


## Complete-graph extreme sizes

[EMO3/VGZ9/CJ8R](articles/finite-subcritical-clusters.md#section-bicyclic-bound) refine the preceding complete-graph benchmark by a self-contained counting argument. A cycle-rank-two subgraph bound and exact unicyclic enumeration exclude cyclic components at the extreme threshold. Ordered tree-component factorial moments give Poisson exceedances and the fixed-rank Gumbel order-statistic laws, with $I=-\varepsilon-\log(1-\varepsilon)$ retained in the normalization. These are written extensions of the article's exact enumeration, not claims that the cited Borgs–Chayes–van der Hofstad–Slade–Spencer passages state a second-order theorem. The general-host gap and joint critical-window law remain separate.

For a primary comparison of the leading law, Theorem 1.1 on printed p.133 / PDF index0 of [Nachmias–Peres, *Component sizes of the random graph outside the scaling window*](https://alea.impa.br/articles/v3/03-06.pdf), ALEA 3 (2007), 133–142, was read in extracted publisher PDF text. It states the fixed-rank leading subcritical size in the same regime; that theorem is not used as an input to the new fluctuation proof. No new erratum, independent mathematical audit or Lean verification is claimed.


## Centered moments below the window

[RN5K/XHEC/OL4S](articles/finite-subcritical-clusters.md#section-poisson-component-tail) supply the tail estimates needed for centered moment convergence and the fixed-rank expectation correction. The exploration uses at most $N-1$ fresh bonds per step, allowing domination by Poisson offspring with mean exactly $1-\varepsilon$. The resulting exponential rate remains $I=-\varepsilon-\log(1-\varepsilon)$, so no restriction such as $\varepsilon\log(N\varepsilon^3)\to0$ is added. Tree-count bands control the other tail uniformly, including the zero-padding endpoint. Every polynomial centered moment converges, as do exponential transforms for parameter of absolute value below one.

Additional primary reading: Section 3, Lemma 3.1, equation (3.1), and the upper-bound portion of the proof of Theorem 1.1, printed pp.136–137 / PDF indices3–4, of the [Nachmias–Peres article](https://alea.impa.br/articles/v3/03-06.pdf). Its binomial exploration and progeny estimates provide context for the exact-rate bound written here; its truncated rate is not used to infer centered moment convergence. The corrected expectation is $[B-(5/2)\log B+\gamma-H_{r-1}+o(1)]/I$ for every fixed rank, for both all components and tree components. This is a written extension of the complete-graph benchmark, not a new source erratum or a claimed Lean theorem.


## Joint interval counts and the ordered extreme vector

[7W39](articles/finite-subcritical-clusters.md#section-joint-er-extremes) extends the existing ordered-tree factorial moments to several disjoint size intervals. Independent marking and the zero-count alternating bounds identify the multivariate generating function. The cap is removed only after this calculation, and the earlier cyclic-component estimate transfers the law to all components. The resulting ordered vector is $(-\log E_1,-\log(E_1+E_2),\ldots)$ for independent mean-one exponentials. Every fixed number of the largest components are trees with probability tending to one.

The primary comparison remains [Nachmias–Peres, Theorem 1.1](https://alea.impa.br/articles/v3/03-06.pdf), printed p.133 / PDF index0, read in extracted publisher-PDF text. That is a leading probability theorem; the joint extreme law is derived here from the article's exact enumeration, not attributed to it. This does not supply a joint critical-window limit or a new erratum.
