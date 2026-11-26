# Susceptibility in the finite critical window

The [article](articles/finite-window-susceptibility.md) completes the positive-window expectation estimate and derives largest-component moments through order two.

| Source and locator | Reading and coverage |
|---|---|
| [Borgs–Chayes–van der Hofstad–Slade–Spencer](https://arxiv.org/pdf/math/0401069), arXiv:math/0401069v1, 8 January 2004; document dated 6 May 2003, Section 8, (8.1)–(8.23), printed pp.31–34 / PDF indices30–33 | Statements and proof were read in extracted text. The article gives the marked-volume moment comparison, transport, positive-window susceptibility bound and the bounded-window consequence, with its own explicit constants. |
| Same preprint, Appendix A.3, (A.49)–(A.58), printed pp.43–44 / PDF indices42–43 | The complete subsection was read. The article reconstructs the differential inequality using the change in the square of the total marked volume when an edge opens, then conditions on the unmarked endpoint cluster. The induced complement retains its product law, so this decoupling does not require a nonmonotone disjoint-occurrence theorem. |
| Existing finite-triangle-window and cluster-partitions articles | Their component-window and partition results yield moments of the largest component through order two. Uniform integrability is proved only below order two. |

This batch adds no erratum. The small-field choice is split from the regime handled by the deterministic bound chi <= N, so no marking parameter exceeds one. No change to a published statement is alleged. Off-window giant-component lower bounds, concentration, ordered-component limits, the remaining appendices, and the journal-version comparison remain separate. No new Lean proof or independent audit is claimed.

## Supercritical density and concentration

The [large-cluster article](articles/finite-supercritical-clusters.md) now proves the shared-boundary variance estimate, field-growth lower bound, supercritical density at the mesoscopic cutoff, and concentration with a relative largest-component upper bound. Its [reading map](sources/finite-supercritical-clusters.md) records the complete Section 9 and the necessary Section 5.2 and Section 6 arguments. A singleton-cutoff proof error is provisionally corrected with a local repair. A giant-component lower bound and geometric sprinkling remain separate.

## Sharper subcritical estimates

The [subcritical article](articles/finite-subcritical-clusters.md) now proves the integrated triangle estimate, a positive-denominator threshold bound, sharp susceptibility asymptotics and largest-component expectation and probability bounds below the window. Its [reading map](sources/finite-subcritical-clusters.md) distinguishes the corrected threshold formula from the source. The provisional statement correction has a complete fix; the component bounds retain a logarithmic gap.



## All squared-mass moments

YN7V extends the earlier second-moment consequences: a uniform susceptibility bound M <= K N^(1/3) gives every positive moment of the normalized total squared component mass. Its proof uses Y84V and the conditional independent law outside an exposed cluster, then groups powers by set partitions. The proof is supplied in the article; no independence of distinct cluster sizes or new source reading is claimed. The [critical-window article](articles/finite-triangle-window.md) applies it to complete-graph expectation limits.




## Growth of the total-mass moments

81TZ keeps the moment-order dependence in YN7V. A block recursion bounds the partition coefficient by a geometric multiple of (2m)!, giving an exponential moment for the square root of total squared component mass on the scale sqrt(max(NM,M^4)). This is a written deduction from the existing tree-graph and cluster-exposure arguments, not a newly read source assertion. No new source correction or formal correspondence is claimed.




## Multiplicative cluster functionals

1NYQ extends the existing distinct-cluster exposure argument to a nonnegative superadditive weight f. Conditional independence in the complement and monotonicity of the cluster sum give an exponential upper bound on the product of (1+f). For f(s)=exp(t(s/a)^2)-1, Cauchy–Schwarz relates the total-mass transform to a second squared-mass moment and a largest-component transform. This is a written deduction, with no new source passage, source correction or formal correspondence claimed.
