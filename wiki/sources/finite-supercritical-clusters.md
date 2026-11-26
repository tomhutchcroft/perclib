# Large-cluster volume above the finite critical window

The [article](articles/finite-supercritical-clusters.md) proves the shared-boundary variance bound, supercritical large-cluster density and concentration, and a relative upper bound for the largest component.

| Source and locator | Reading and coverage |
|---|---|
| [Borgs–Chayes–van der Hofstad–Slade–Spencer](https://arxiv.org/pdf/math/0401069), arXiv:math/0401069v1, 8 January 2004, document dated 6 May 2003, Section 5.2, Proposition 5.1(ii), Corollary 5.2(ii), (5.25)–(5.36), printed pp.23–25 / PDF indices22–24 | The rectangle integration and its finite critical-field application were read. The wiki supplies a complete proof with explicit field choices, constants and a positive reference level. |
| Same preprint, Section 6, proofs of Theorems 1.4(i) and 1.6(i), (6.14)–(6.19), printed p.29 / PDF index28 | Read and reconstructed. The density above the real cutoff epsilon^(-2)(epsilon N^(1/3))^alpha is proved to be of order epsilon for fixed 0<alpha<1 sufficiently far above the window. The root-tail-to-expectation bound is also proved. |
| Same preprint, complete Section 9, Lemma 9.1 and Theorem 1.6(ii), (9.1)–(9.13), printed pp.34–36 / PDF indices33–35 | Read in extracted text. The exact shared-boundary covariance is proved for arbitrary independent bond probabilities, followed by the homogeneous concentration argument and its exponent eta=(3−2alpha)/(15−6alpha). The relative upper bound uses the density lower bound proved in the same article. |
| Same preprint, proof of (9.8), singleton cutoff | A provisional local correction records that the truncated mean is the root-isolation probability, bounded by one. A direct scalar field bound supplies the repair. The theorem and its exponents are unchanged. |

The extracted (9.6) also contains an apparent negative exponent on the shared-boundary cardinality. The preceding exact identity and the reconstructed proof use the nonnegative cardinality. Without a visual or source-TeX comparison this remains a typography audit lead, not a second diagnosed erratum. PDF screenshot access was unavailable and direct download failed; the journal version has not been compared.

The concentration regime epsilon N^eta -> infinity is stronger than epsilon N^(1/3) -> infinity. These results concern the total volume in large clusters and an upper bound for the largest. They do not prove a matching giant-component lower bound or uniqueness; geometric sprinkling remains separate. No new Lean verification or independent audit is claimed.

## Finite cutting proof and author-version comparison

The [finite magnetization article](articles/finite-magnetization-deletion.md) gives the complete signed-deletion, two-cluster and last-pivotal argument. Its [reading map](sources/finite-magnetization-deletion.md) compares the early preprint with the September 2004 author revision, which already repairs the cubic coefficient and diagonal convention. A separate scope entry proves the positive-part replacement and gives an exact K4 counterexample to the unrestricted later polynomial. Existing small-triangle statements are unchanged.

## Sharp field growth and the 2017 appendix

The [sharp-field map](sources/sharp-supercritical-field.md) supplies the factor-one-half upper differential inequality from Section A.6 and a repaired leading lower-bound argument for Lemma A.6 in Section A.4. The new rectangle remains above the window and keeps both fields valid, but gives a logarithmic error. Three provisional entries separate that partial quantitative repair, the tail-ratio sign and a distinct-root-mark issue in the separate lower inequality. Earlier statements and source scopes are unchanged.

## Characteristic repair of the lower field bound

The [characteristic-field map](sources/characteristic-field-growth.md) supplies a new finite proof from the zero-field susceptibility. It removes the lower rectangle’s logarithmic loss and gives a polynomial lower-tail error; with the corrected upper route, the two-sided error has exponent min(alpha/2,1/3-alpha). The rectangle erratum is now fix found/substantial, still provisional. Earlier statements and their tags remain unchanged; the earlier descriptions of an unresolved polynomial lower error record the prior state.

## Quantitative tails and large-cluster mass

The [quantitative-tail map](sources/quantitative-supercritical-tails.md) records the retained upper-error balance, a logarithmic marking choice and a large-cluster variance application. The new upper-error entry is partial/statement/provisional; the completed lower characteristic repair remains found/substantial. A largest-component upper bound assumes epsilon^5 N tends to infinity and does not establish a giant-component lower bound. Earlier tagged results remain unchanged.


## The complete-graph giant and its complement

[AUTD/2KT9/U6EN](articles/finite-supercritical-clusters.md#section-er-exploration) now supply the barely supercritical complete-graph benchmark. A uniform martingale estimate gives the parabolic exploration profile, a long excursion gives one giant, and the graph left at its completion is subcritical. The proof then handles the conditioning caused by selecting the giant before applying the existing subcritical fixed-rank law. Consequently $L_1/(2\varepsilon N)\to1$ in probability and mean absolute error, while every fixed rank $r\ge2$ has size asymptotic to $2\varepsilon^{-2}\log(N\varepsilon^3)$ in probability. All other components have mean $o(\varepsilon N)$ on the giant scale; convergence of their logarithmically normalized means is not asserted.

Primary reading: [Nachmias–Peres, *Component sizes of the random graph outside the scaling window*](https://alea.impa.br/articles/v3/03-06.pdf), ALEA 3 (2007), Section 4, Lemmas 4.1–4.2 and the proof of Theorem 1.2, printed pp.138–141 / PDF indices5–8, in extracted publisher PDF text. The wiki gives its own quantitative exploration estimate and a separate expectation argument. This is a complete-graph extension of the finite-graph chapter; the earlier general-host giant and sprinkling questions remain separate. No new erratum, independent mathematical audit or Lean verification is claimed.


## Sprinkling on locally tree-like expanders

[9906/NVCH/YTZU](articles/finite-supercritical-clusters.md#section-expander-paths) give short edge-disjoint paths, uniform conditional coalescence of large clusters, and the giant vertex density for fixed-degree regular expanders converging locally to the regular tree. The last convergence is in probability and mean absolute error; the second-largest component is sublinear. All parameters are fixed before the graph-size limit.

Primary passages read in extracted author-PDF text:

| Source | Locator | Use |
|---|---|---|
| [Alon–Benjamini–Stacey, *Percolation on finite graphs and isoperimetric inequalities*](https://web.math.princeton.edu/~nalon/PDFS/abs8.pdf) | Section 3, Proposition 3.1 and proof, printed pp.13–14 / PDF indices12–13 | Edge expansion, the total edge budget and independent sprinkling connect large-cluster unions. The wiki separates this mechanism from the source's high-girth first round. |
| [Krivelevich–Lubetzky–Sudakov, *Asymptotics in percolation on high-girth expanders*](https://www.cs.tau.ac.il/~krivelev/expperc.pdf) | Theorem 1, printed p.2 / PDF index1; Section 2.1, Claim 2.3, Corollary 2.4 and proof of Proposition 2.2, printed pp.8–9 / PDF indices7–8 | Comparison for the sharp giant vertex density. The wiki's fixed-cutoff variance proof allows a vanishing fraction of non-tree neighbourhoods. The source's edge counts, degree laws, 2-core and exponential concentration are not reproduced. |

The source's descendant extinction probability $q$ and the article's branch-failure probability $u$ satisfy $q=u^{d-1}$ and $u=1-p+pq$. Its giant-density expression $1-q(1-p)-pq^2$ therefore equals $1-u^d$. This is a notation change, not a source correction. No new erratum or Lean correspondence is asserted. Earlier general-host and near-critical questions remain open in this map; the expander result addresses the explicitly stated fixed-parameter class.


## Exponential deviations and the giant's local profile

[YCHK/UPQ2/OH6B/VSGH](articles/finite-supercritical-clusters.md#section-expander-local-concentration) complete the fixed-parameter giant vertex/edge/degree conclusions for locally tree-like regular expanders. A bond-flip bound gives concentration of weighted cutoff mass. This yields exponential giant-size and uniqueness bounds and the empirical local law of tree percolation conditioned to survive. The degree law gives the edge and cycle-excess densities. The cubic excess expansion takes the graph-size limit before the parameter approaches criticality.

Additional reading: [Krivelevich–Lubetzky–Sudakov](https://www.cs.tau.ac.il/~krivelev/expperc.pdf), Theorem 1 (1.2), (1.4), printed p.2 / PDF index1; Theorem 2.1 (2.1), printed p.6 / PDF index5; Section 2.1 through the final degree deduction, printed pp.6–9 / PDF indices5–8, in extracted author-PDF text. The earlier description of edge/degree/exponential conclusions as unreproduced records the preceding state. The 2-core conclusions and near-critical uniformity remain separate.

The [new provisional erratum](errata/krivelevich-lubetzky-sudakov-expanders.json#edge-union-explanation) concerns only the prose explanation after (2.4): its displayed union needs at least one large endpoint cluster after deleting the edge. A two-edge open path distinguishes this from requiring both. The fix is found and its significance is notational; neither the displayed definition nor the final density changes. Visual PDF and publisher-version comparison were unavailable, and no author confirmation or Lean verification is claimed. The extracted direction arrow for descendant extinction as the parameter increases is a further typography-check lead, not a separate diagnosed erratum.


## The 2-core and the reserved-edge argument

[0ATK/S8OP/TGLZ/2K74](articles/finite-supercritical-clusters.md#section-expander-thick-sets) complete the fixed-parameter 2-core argument. A sparse independent colour reservation preserves expansion of macroscopic thick sets. Red-only sprinkling then puts the endpoints of most eligible blue edges in one red component, producing cycle witnesses. Independent blue sampling, conditioned only on the full uncoloured graph, gives the core edge lower bound. Local deletion-cluster tests supply the upper bound and degree profile, including negligible other cores and negligible bridges within the giant core. The earlier references to the 2-core as unfinished record the preceding state.

Primary reading: [Krivelevich–Lubetzky–Sudakov](https://www.cs.tau.ac.il/~krivelev/expperc.pdf), the full Section 2.2, (2.19)–(2.29), Proposition 2.5, Claims 2.8–2.9, Corollary 2.10, Remarks 2.11–2.12 and the degree deduction, printed pp.10–14 / PDF indices9–13, in extracted author-PDF text. The reconstruction uses its own conservative colour/counting constants and allows a vanishing fraction of exceptional local neighbourhoods.

The [red-parameter correction](errata/krivelevich-lubetzky-sudakov-expanders.json#red-first-round-parameter) is provisional, with a complete local proof repair. A red first-round edge is present with probability $(1-\vartheta)p_0$, so its branch extinction probability must replace the one at $p_0$ in the eligible-blue-edge lower expectation. Choose colour and first-round parameters for the target error, then the sprinkling tolerance and cutoff. The main fixed-parameter theorem survives; the uncorrected intermediate lower expectation is not retained. No publisher-version comparison, author confirmation or new Lean verification is claimed.


## Robustness, separators and linear cycles

[58KB/P3AV/PMXD/F067/8NPK](articles/finite-supercritical-clusters.md#section-expander-thinning-deletion) extend the fixed-parameter expander chapter to uniform vertex-deletion resilience. A deletion witness can depend on the observed configuration: after fixing it, independent thinning pays only for the incident edges. The exponential giant-size bound at a smaller parameter makes every small deletion leave almost all the giant connected. This excludes small balanced separators. A direct depth-first-search proof produces a path separator, and sprinkling between the outer thirds of a long first-round path gives a linear cycle. The connector-intersection lemma handles paths that revisit the original path, so internal disjointness is not assumed.

Primary reading: [Krivelevich–Lubetzky–Sudakov](https://www.cs.tau.ac.il/~krivelev/expperc.pdf), Section 4, Theorem 4.1 and its full proof, Corollary 4.2, Lemma 4.3 and the following cycle paragraph, printed pp.18–20 / PDF indices17–19, in extracted author-PDF text. The remaining complete-minor paragraph was read for scope; its external separator theorem and minor conclusion are not reproduced. The wiki supplies its own DFS proof and explicit uniform-deletion and connector statements, allowing a vanishing proportion of non-tree host neighbourhoods. No near-critical uniformity is inferred.

The [conditional-erasure entry](errata/krivelevich-lubetzky-sudakov-expanders.json#thinning-deletion-probability-direction) is provisional/fix found/notation. The probability of erasing at most $d|S|$ incident edges is at least the corresponding power, rather than at most as the source sentence says. Its next displayed comparison already uses the correct direction; the theorem and quantitative mechanism are unchanged. Visual PDF and publisher-version comparison were unavailable, and no author confirmation or Lean verification is claimed.


## The barely supercritical giant's Gaussian limit

[UEXT/WEV8/UKVG/MEUA](articles/finite-supercritical-clusters.md#section-er-early-start) complete the barely supercritical complete-graph fluctuation argument. The first components take a tight $\varepsilon^{-2}$ time and create a tight $\varepsilon^{-1}$ restart count. An exact weighted exploration representation, a conditional characteristic-function calculation and local control at the excursion endpoint give the Gaussian limit centered at the Poisson survival probability. A separate expansion identifies the $N\varepsilon^5$ transition for the leading-order center. No convergence of centered means or variances is asserted.

Primary reading: [Bollobás–Riordan, *Asymptotic normality of the size of the giant component via a random walk*](https://arxiv.org/pdf/1010.4595), arXiv:1010.4595, 11-page version, Theorem 1 and Corollary 2, Section 2, equations (3)–(21), Lemmas 3–8 and the concluding proof, printed pp.2–10 / PDF indices1–9, read in extracted PDF text. Journal metadata: Journal of Combinatorial Theory, Series B 102(1) (2012), 53–61, [doi:10.1016/j.jctb.2011.04.003](https://doi.org/10.1016/j.jctb.2011.04.003). The source covers bounded supercritical parameters more generally; this reconstruction proves the vanishing-epsilon case. It supplies direct dyadic early-start bounds and a characteristic-function proof in place of importing a martingale central limit theorem. The publisher version was not compared. No new erratum or compiled correspondence is claimed.


## From component probability laws to all leading-scale moments

[N9DF/PMEN/PW6A/DNIW](articles/finite-supercritical-clusters.md#section-er-exponential-increments) give a conditional binomial maximal estimate, a global cubic-exponential upper tail, an exponential bound for fixed relative giant-size errors, and convergence of every fixed positive component moment on its leading scale. For every fixed rank after the giant, the mean is asymptotic to $2\varepsilon^{-2}\log(N\varepsilon^3)$. The complement is conditioned on having no component above its stated cutoff; the proof bounds that conditioning denominator uniformly and separately controls the exceptional event. Earlier descriptions of the logarithmic means as unfinished record the preceding state.

Primary comparison: [Nachmias–Peres, *Component sizes of the random graph outside the scaling window*](https://alea.impa.br/articles/v3/03-06.pdf), ALEA 3 (2007), Theorem 1.2 and the full Section 4 proof, printed pp.133–134 and138–141 / PDF indices0–1 and5–8, read in extracted publisher-PDF text. The source asserts probability limits and explains the conditioned complement. The new exponential block bound and the moment upgrade are written deductions here, not attributed to that theorem. No new erratum or compiled correspondence is claimed. Centered giant moments and a centered law for the supercritical non-giant ranks remain separate.


## Joint Gaussian and extreme-component limits

[DD9N/OH30/K1HI/KU4Y](articles/finite-supercritical-clusters.md#section-er-dual-extreme-normalization) prove the centered non-giant count and rank laws jointly with the Gaussian giant. The exact dual identity reduces the exponential rate to $I=\varepsilon-\log(1+\varepsilon)$. The giant's size uncertainty changes the complementary normalization by $o(1)$ after choosing a slowly growing Gaussian-size interval. Conditional on the giant vertex set, the cutoff-conditioned complementary law then has the same uniform multivariate limit. This proves independence of the Gaussian variable from the whole fixed-rank extreme vector; the ordered extreme coordinates themselves share exponential partial sums. The leading quadratic rate has a deterministic shift $(2/3)\varepsilon\log(N\varepsilon^3)$.

Primary inputs already read in extracted text: [Bollobás–Riordan, arXiv:1010.4595v2](https://arxiv.org/abs/1010.4595v2), Theorem 1, Corollary 2 and Section 2, printed pp.2–10 / PDF indices1–9; and [Nachmias–Peres](https://alea.impa.br/articles/v3/03-06.pdf), Theorem 1.2 and the conditional-complement argument in Section 4, printed pp.133–134 and140–141 / PDF indices0–1 and7–8. The arXiv index identifies the 11-page version as v2, revised 16 April 2011. The source marginal theorems provide context; the multivariate enumeration, normalization stability and independence argument are supplied here. No centered-moment convergence, joint critical-window conclusion, new erratum or compiled correspondence is claimed.


## Centered moments and covariance of extreme ranks

[Y85E/LXGK/NVPH/M7A4](articles/finite-supercritical-clusters.md#section-er-early-exponential-tails) complete the centered polynomial-moment consequences of the preceding joint law. A weighted exponential martingale controls the number and duration of early components; a good-trajectory estimate then controls all moments at the giant's Gaussian scale. The exceptional event is handled using the global largest-component tail, rather than the number of vertices. For the smaller ranks, the exact complementary normalization is controlled over the whole relative-size event before conditioning and mixing.

The resulting expectation correction is $(\gamma-H_{r-2})/I$, and the covariance of ranks $r,s\ge2$, multiplied by $I^2$, tends to $\sum_{\ell=\max(r,s)-1}^{\infty}\ell^{-2}$. The Gaussian coordinate is independent of the entire extreme vector in the limiting mixed moments; the extreme coordinates themselves remain correlated.

The primary comparison remains [Bollobás–Riordan, arXiv:1010.4595v2](https://arxiv.org/abs/1010.4595v2), Theorem 1, Corollary 2 and Section 2, printed pp.2–10 / PDF indices1–9, and [Nachmias–Peres](https://alea.impa.br/articles/v3/03-06.pdf), Theorem 1.2 and Section 4's conditional-complement argument, printed pp.133–134 and140–141 / PDF indices0–1 and7–8, previously read in extracted PDF text. Their distributional statements and conditional-complement method are distinguished from the uniform-integrability and covariance arguments supplied here. This adds no source erratum, exponential-transform theorem, joint critical-window result or compiled correspondence.


## Hypercube sprinkling away from the narrow window

[YI8S/5IGY/12DQ/E6FX](articles/finite-supercritical-clusters.md#section-hypercube-short-paths) supply an explicit path packing, its finite conditional sprinkling bound, and the cube giant and susceptibility laws when $\log(1/\varepsilon)=o(m^{1/3})$. The proof uses the existing strong triangle and mean-square mass estimates, with a new coarse packing from coordinate concentration.

Comparison reading: [van der Hofstad–Nachmias](https://ems.press/content/serial-article-files/32188), Section 2.3 and Sections 7.1–7.2, printed pp.737–738,791–793,796 / PDF indices12–13,66–68,71, in extracted text. Their full near-window joining theorem remains separate; no new source error is asserted.


## Critical-window exploration

The [finite-triangle-window map](sources/finite-triangle-window.md) now records the separate critical-scale Brownian exploration and surplus-mark results. They use the same finite queue construction with a different normalization. Ranked critical component limits remain separate.


## Ranked critical law

The [critical-window map](sources/finite-triangle-window.md) now includes the ranked size and surplus theorem. This complements the outside-window laws; varying the window parameter as a process remains separate.



## Critical parameter coupling

The [critical-window map](sources/finite-triangle-window.md) now includes Z8T1, the joint ranked-size law at every finite list of window parameters. The square-summable coalescent construction and its jointly continuous kernels are proved there. This does not yet give path-space convergence or joint surplus evolution.



## Critical path law

The [critical-window map](sources/finite-triangle-window.md) now includes TIGK, the J1 limit of the ranked size process on bounded parameter intervals, and its parameter-integrated squared-mass consequence. The proof uses the exact clock change and explicit stopped-increment and compact-containment arguments. Joint surplus evolution and expectation limits remain separate.



## Critical-window moment upgrade

The [critical-window article](articles/finite-triangle-window.md) now gives polynomially bounded ranked-size and path-functional expectations, uniformly convergent susceptibility on compact parameter intervals, and all positive moments of the integrated squared mass. The required uniform integrability follows from the written susceptibility and distinct-cluster estimates. These are new deductions from existing material, with no new source erratum or surplus-process claim.



## Critical cycle increments

The [critical-window article](articles/finite-triangle-window.md) now proves the joint size-path and new-cycle point-process law, with all polynomial count moments. The total limiting cycle-birth intensity is half the squared l2 mass; the simple-graph rejection error is explicit. Its reading map records the limited comparison with Bhamidi–Budhiraja–Wang's transition rates and Poisson construction. Full ranked-surplus dynamics remain separate.




## Critical weighted marked states

The [critical-window article](articles/finite-triangle-window.md) now proves the fixed-parameter size-weighted marked limit and a uniform estimate for inherited initial surplus tails over bounded parameter intervals. Its RJJ9/1QUE/NH8N proofs use a subcritical cycle count, stopped exploration and a localized linear merger drift. The reading map records the comparison with the marked metric and inherited-surplus arguments of Bhamidi–Budhiraja–Wang. Full joint ranked marked-process convergence remains unfinished.




## Joint critical sizes and surpluses

The [critical-window article](articles/finite-triangle-window.md) now proves JSGY, the joint weighted marked law at finite parameter lists. It constructs the limiting transition law, tracks label ancestry and new Poisson marks, and compares the multigraph proposals with the simple graph at O(N^(-1/3)) error. Its reading map records the Section 4.2 comparison with Bhamidi–Budhiraja–Wang. Marked path convergence and a common-Brownian representation remain separate.
