# The finite triangle window

[The article](articles/finite-triangle-window.md) proves susceptibility bounds, finite-field estimates, root tails through the susceptibility scale, and largest-component tightness throughout a bounded degree-normalized window.

| Source and locator | Reading and coverage |
|---|---|
| [Borgs–Chayes–van der Hofstad–Slade–Spencer](https://arxiv.org/pdf/math/0401069), arXiv:math/0401069v1,8January2004; document dated6May2003, Section4.1,(4.1)–(4.2), printed p.19 / PDF index18 | The susceptibility differential bounds and integration were read. The wiki proves them by finite Russo and the existing five-factor deletion bound, averaging over roots to avoid a Cayley-graph restriction. |
| Same preprint, Section5.1,Proposition5.1,Lemma5.3,Proposition5.4 and Lemma5.5, printed pp.21–22 / PDF indices20–21 | Field statements and hypotheses were read. The wiki supplies a finite version of its existing cutting-bond argument, explicit smallness constants and a finite inverse-field extrapolation; the later source proofs and AppendixA.2 have not been fully audited. |
| Same preprint, Section6,Lemmas6.1–6.2 and proofs, printed pp.27–29 / PDF indices26–28; Section3.6, printed p.18 / PDF index17 | Root-tail conversion and the critical-window deductions were read. The wiki retains the finite-mean cutoff and proves the component bound using its existing cluster-covariance theorem. Its numerical constants are deliberately different from the source's. |
| [Heydenreich–van der Hofstad](https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf),17March2017,Section13.3,Exercise13.6,(13.3.11),printed p.163 / PDF index174 | Extracted text confirms that the exercise defines a relative displacement but uses the additive normalization in the formula. The four-cycle counterexample and corrected statement have written proofs. This entry is provisional, with a fix found and statement-level significance. |

The positive-window susceptibility upper bound, off-window giant-component results, ordered-component limits, full original-paper audit and published-version comparison remain separate. No new Lean verification, visual PDF comparison or independent review is claimed. The existing hypercube triangle theorem can supply the hypothesis for sufficiently small fixed lambda and large dimension; no new hypercube asymptotic is asserted here.

## Positive-window susceptibility completed

The [marked-volume article](articles/finite-window-susceptibility.md) now proves the expectation bound left open above: chi(p) is at most C(lambda)[N^(1/3)+m^2(p−p_c)^2N] for p_c <= p <= 1/2. It gives two-sided susceptibility throughout a bounded window, largest-component moments through order two, and uniform integrability below order two. The [reading map](sources/finite-window-susceptibility.md) records Section 8 and Appendix A.3 of the original finite-graph preprint. Off-window giant-component lower bounds and ordered limits remain separate.

## Supercritical density and concentration

The [large-cluster article](articles/finite-supercritical-clusters.md) now proves the shared-boundary variance estimate, field-growth lower bound, supercritical density at the mesoscopic cutoff, and concentration with a relative largest-component upper bound. Its [reading map](sources/finite-supercritical-clusters.md) records the complete Section 9 and the necessary Section 5.2 and Section 6 arguments. A singleton-cutoff proof error is provisionally corrected with a local repair. A giant-component lower bound and geometric sprinkling remain separate.

## Sharper subcritical estimates

The [subcritical article](articles/finite-subcritical-clusters.md) now proves the integrated triangle estimate, a positive-denominator threshold bound, sharp susceptibility asymptotics and largest-component expectation and probability bounds below the window. Its [reading map](sources/finite-subcritical-clusters.md) distinguishes the corrected threshold formula from the source. The provisional statement correction has a complete fix; the component bounds retain a logarithmic gap.

## Finite cutting proof and author-version comparison

The [finite magnetization article](articles/finite-magnetization-deletion.md) gives the complete signed-deletion, two-cluster and last-pivotal argument. Its [reading map](sources/finite-magnetization-deletion.md) compares the early preprint with the September 2004 author revision, which already repairs the cubic coefficient and diagonal convention. A separate scope entry proves the positive-part replacement and gives an exact K4 counterexample to the unrestricted later polynomial. Existing small-triangle statements are unchanged.


## Brownian exploration in the complete-graph window

[Aldous (1997)](https://doi.org/10.1214/aop/1024404421), Theorem 3 (printed p.816 / PDF index4), Sections 2.1–2.2 (pp.819–824 / indices7–12), was read in extracted text from the [43-page journal PDF](https://escholarship.org/content/qt5s77j58b/qt5s77j58b_noSplash_2827d3aa70ed7a526db5fb6e9bf213b0.pdf). R1RF/FOTE/CY46/GGL3 supply discrete-time proofs of the martingale, reflected-queue and surplus-mark limits. The opening of Section 2.3 was read to identify the separate excursion and late-component steps; its full proof and the multiplicative coalescent remain outside this addition. No new source erratum or formal correspondence is claimed.


## Ranked components and late exploration

The same Aldous journal PDF, Corollary 2 and Section 2.3 (printed pp.814,824–826 / PDF indices2,12–14), is now read through its complete proof. Lemma 25 (pp.843–844 / indices31–32) was also read for comparison. 2N9T/59NH/CH8I/M7BY prove regularity, record matching and the ranked size/surplus limit. The late squared-mass bound comes from the stopped unexplored graph. Parameter-process convergence and the nonuniform model remain separate; no erratum or new formal correspondence.



## Coalescent construction and parameter laws

Aldous Proposition 5 (printed p.818 / PDF index6), Section 4.2 (pp.836–843 / indices24–31) and Corollary 24 (p.843 / index31) were read in the searchable journal PDF. 3G0K/5HM7/7HLE/Z8T1 supply a square-summable construction, an attachment estimate, joint continuity and the finite-dimensional critical-parameter law. The new estimate explicitly counts each added vertex's own squared mass. The searchable text of Lemma 23 appears to omit this term; direct downloads and the publisher copy were inaccessible, and the screenshot connector returned no inspectable image. Verification against the printed formula remains pending; no source erratum is asserted on that basis. Path-space convergence, joint surplus evolution and a common-Brownian representation remain separate.



## Path-space upgrade

O3IS/R8LD/GRSC/TIGK extend the written coalescent argument to J1 path convergence. The stopped estimate follows from 3G0K; an increasing quadratic bound controls exit counts, and deterministic marginal tightness supplies compact containment. The result applies to finite initial-law approximations and then to the exact critical-window clock change. This is a written extension of the earlier Aldous comparison, not a claim that Corollary 24 itself states this path topology. Standard Skorokhod compactness and identification theorems are the topological inputs. Joint surplus evolution, a common-Brownian coupling and expectation limits remain separate. A renewed attempt to retrieve the author copy for the Lemma 23 printed-formula check returned 403; that source question is unchanged and no erratum is asserted.



## Critical moments and expectations

A40L chooses a small susceptibility reference level on the complete graph, verifies its triangle bound by R2Y7, and applies the already-proved finite-window transport estimate CAZQ. YN7V expands powers of total squared mass by distinct clusters and bounds them using the existing tree-graph moments. 1DEZ/KCRC then pass the ranked and path laws to polynomially bounded expectations, including uniform susceptibility convergence and every positive moment of the integrated squared mass. These are deductions from existing written arguments; no new paper passage was read and none of these added formulas is attributed to a newly checked source statement. Joint surplus evolution and common-Brownian representation remain separate. The printed-formula question about Aldous Lemma 23 is unchanged; no erratum is added.



## New cycle births in parameter time

[Bhamidi–Budhiraja–Wang, arXiv:1212.5493v1 (21 December 2012)](https://arxiv.org/pdf/1212.5493v1), Section 2.3.2, printed pp.7–8 / PDF indices6–7, was read for the marked state space and transition rates. The opening construction of Section 4, printed pp.11–12 / indices10–11, and Lemma 4.9 with its proof, printed pp.14–15 / indices13–14, were read for the Poisson multigraph and internal-surplus estimate. The full near-Feller and marked entrance-law proofs have not been audited.

6TZO/6248/M7RY give a loop-free finite-proposal construction, an O(N^(-1/3)) comparison with the simple graph, joint convergence of new cycle-closing edges and the critical size path, and mixed-Poisson moment formulas. Conditional independence is proved from the autonomous finite partition generator. These are written deductions using the earlier path and moment bounds, not a claim to have proved the source's full marked-state theorem. The initial marked-state tail and its propagation remain separate. No source correction is asserted.




## Weighted initial surplus and its propagation

[Bhamidi–Budhiraja–Wang, arXiv:1212.5493v1](https://arxiv.org/pdf/1212.5493v1), Section 2.3.2, (2.8), printed pp.7–8 / PDF indices6–7, was read for the size-weighted marked metric. Section 4.1, Proposition 4.5, Lemmas 4.6–4.7 and their proofs, printed pp.13–14 / indices12–13, was read for inherited surplus and finite-graph approximation. This is the 21 December 2012 preprint, not a comparison with the published version.

RJJ9 counts simple cycles and bounds their conditional attached mass to control the weighted surplus of a subcritical G(m,p). Applied at the stopped critical exploration, it bounds late weighted surplus by 1/[2(T−lambda)^2]. 1QUE combines this with the bounded-time mark limit and completion-time tightness, proving the fixed-parameter law in the weighted metric. NH8N uses the exact linear merger drift and stopping at bounded squared mass to propagate any selected initial marked tail, including the critical initial tail. These are written proofs. Full ranked marked-process convergence, allocation of new cycle marks, and its path topology remain separate; no source correction or compiled correspondence is asserted.




## Joint marked parameter laws

[Bhamidi–Budhiraja–Wang, arXiv:1212.5493v1](https://arxiv.org/pdf/1212.5493v1), Section 4.2: the statement of Lemma 4.12 and its introductory approximation discussion, printed p.16 / PDF index15, and its proof on pp.18–20 / indices17–19 were read in extracted text for comparison. This is not an audit of every auxiliary lemma in that section or a published-version comparison.

V90S proves continuity of the component masses, connections and ranks of finitely many positive-mass labels. KBJ8 constructs the countable marked coalescent and bounds births missed by finite restrictions through the stopped squared-mass difference. 4DZC combines these with NH8N to prove joint convergence at finite observation times under an explicit no-ties hypothesis. JSGY applies this to critical Erdős–Rényi, proves the marked entrance-law identity, and includes the loop/repeated-edge error and the finite tie-rule comparison. This supplies finite-dimensional marked-process convergence, not marked path-space convergence. All four are written proofs; no source correction or formal correspondence is asserted.




## Exponential observables and moment determinacy

NROY applies the explicit finite-graph bound 81TZ and A40L to critical size paths, extending expectation convergence to a stated class of exponentially growing observables. L1PJ combines the existing conditional-Poisson proposal law with a uniform square-root Poisson estimate; it proves joint square-root exponential-transform convergence for integrated squared mass and new cycle increments. NM14 then proves that their mixed moments determine their joint law on the nonnegative quadrant by independently signing the square roots. These are written deductions from existing results; no new passage was read, no correction to a source is asserted, and no exponential moment of the squared mass or cycle count without the square root is claimed.




## Full exponential transforms

7CDV combines the existing complete-graph cubic largest-component tail PMEN with the new cluster-product inequality 1NYQ and the m=2 bound in YN7V. It proves all positive exponential moments of critical squared mass and expectation convergence for exponentially growing size-path observables. ME2X transfers this to integrated squared mass and new cycle increments by the already-established conditional-Poisson proposal coupling, with the exact limiting mixed-Poisson transform. 0Y6N proves entire dependence on both complex transform parameters and locally uniform convergence of every derivative. These strengthen the preceding square-root results using the additional complete-graph tail input. No new external passage was read, source correction asserted or formal correspondence promoted. Full marked path convergence remains separate.




## Joint paths of mass and total weighted surplus

0DWE adds the birth contribution to the inherited-mark drift NH8N and proves a quantitative stopped-increment estimate for total size-weighted surplus. The complete product-space metric and the increasing control S+H permit the existing tightness criterion to apply to both coordinates with one time change. EURS combines this with JSGY and the finite-proposal comparison to prove the critical size/weighted-surplus path law and convergence in distribution of their time integrals. The candidate's stochastic continuity is checked by retaining finitely many old marks and new births and following their endpoint labels. These are written deductions from the existing arguments; no new paper passage or formal correspondence was checked. Full ranked marked-path convergence remains separate.

This batch also repairs a missing plus sign in the proof's explicit bound B_Lambda(q) in 7CDV: the cutoff term exp(q A_Lambda^2) and the tail integral must be added. At q=0 the sum is one, whereas the mistakenly juxtaposed product was zero. The tagged statement and all hypotheses and conclusions are unchanged. This is a transcription error in our exposition, not an erratum attributed to a published source.


## Expectations of the weighted surplus

U59P integrates the existing centered-binomial maximal bound N9DF, uses the exact conditional binomial mark law GGL3, and combines their polynomial exploration-time moments with the cubic largest-component tail. This bounds every fixed moment of the early weighted-surplus contribution even though its completion time is random. O4TX then combines that bound with RJJ9's vanishing late mean to prove uniform integrability of the full weighted surplus. It gives moving-parameter and uniform first-moment limits, the Brownian length-times-area formula, and expectation convergence for joint path observables growing linearly in weighted surplus. In particular the time-integrated weighted-surplus expectation left separate in EURS now converges. Higher weighted-surplus moments, full ranked marked-path convergence and a common-Brownian parameter representation remain separate. These are written deductions from existing arguments; no new paper passage, source correction or formal correspondence is claimed.


## Fractional moments and mixed path expectations

WPKA makes the cutoff dependence in U59P explicit and obtains a finite-N late bound from RJJ9 before choosing a cutoff that depends on the tail level. Balancing the two terms gives tail exponents 2r/(r+1), hence uniform integrability and moving-parameter/uniform limits for every surplus power below two. JTVN combines these powers with the all-positive squared-size exponential bound 7CDV by Hölder, passing mixed path expectations to the joint EURS limit without assuming independence. These are deductions from the existing written arguments; no new source passage or formal correspondence is claimed. The endpoint second moment, positive exponential moments of total weighted surplus, the full ranked marked-path topology and a common-Brownian parameter representation remain separate.


## All weighted-surplus moments through dyadic exploration

QKHG sharpens the queue estimate by using the current component's duration, bounded by the largest component, in the positive drift term. On a dyadic exploration interval, its random completion horizon has queue moments of order T^(r/2). Separately, the unexplored subcritical graph and YN7V give late squared-mass moments of order T^(-r). Conditional on the complete discovery transcript, the surplus is a weighted Bernoulli sum. Its partition expansion and Cauchy–Schwarz give Lr bounds of order T^(-1/2) for each block, summable over dyadic intervals. The two conditioning arguments are kept distinct. DK7F then passes every positive surplus moment, variance, covariance and exponentially size-weighted polynomial surplus observable to the joint limit. This closes the second-moment gap recorded in WPKA/JTVN without changing their statements. These are deductions from the existing written arguments; no new source passage, erratum or formal correspondence is claimed. Positive surplus exponential moments and the full ranked marked-path topology remain separate.


## The measure of surplus across component sizes

GZ95 maps a weighted marked state to the finite measure sum_i x_i y_i delta_(x_i). It proves continuity of this map and controls the bounded-Lipschitz change at each merger or birth by the increase of F(S+H), with F(r)=r+(2/3)r^(3/2). R8LD and the existing stopped estimates then give tightness in a complete product space. EAQD identifies the critical path limit using JSGY. The deterministic bound passes through the common Skorokhod time changes; the EURS projection has no fixed-time jumps, which makes finite-dimensional evaluation valid for the new coordinate. All-moment bounds give convergence of growing path expectations. At fixed limiting times the distinct masses recover individual marks, while equal masses are aggregated. This does not settle the full ranked marked-path topology. These are deductions from the existing arguments and standard weak-measure topology; no new source passage, erratum or formal correspondence is claimed.


## Weighted-surplus lower tails and Laplace transforms

7E7T uses the fixed-parameter Brownian marked representation of GGL3/1QUE. A Gaussian event of probability at least c exp(-18 L^3) keeps the reflected path above L^2 for an interval of length L. That excursion has length at least L and area at least L^3; its conditionally Poisson mark is at least half its mean with probability at least one half. This gives weighted surplus at least L^4/2, the lower tail c exp(-C x^(3/4)), moment growth at least q^(4/3), and divergence of exponential moments of powers above 3/4. Monotonicity and truncated expectations give uniform finite-N divergence. B7V7 combines this obstruction with DK7F to obtain convergence of the joint size/surplus Laplace transform and all mixed derivatives on compact subsets of the closed surplus half-plane. The surplus transform has all right derivatives at zero but a Taylor series of radius zero. No matching upper tail, claim at power 3/4, common-Brownian parameter coupling, new source passage, source error or formal correspondence is asserted. The Gaussian density, reflection principle and Poisson Chebyshev estimate are stated explicitly in the proof.


## Conditional surplus kernels and the variance decomposition

OPH4 couples each Bernoulli(p) candidate to a Poisson(p) variable with expected absolute error at most p^2. Size weighting sums the full-graph error to p times the conditional weighted-surplus mean. Its Poisson kernel is continuous in first Wasserstein distance at positive mass sequences, by finite-coordinate coupling and summable conditional-mean tails. OWBW augments the existing excursion matching with candidate-area Riemann sums. The identity between the expected conditional-mean rank tail and the expected marked rank tail, together with 1QUE/O4TX, supplies the full summable tail. This gives joint convergence of sizes, weighted marks, conditional means and conditional kernels. All-moment bounds give convergence of the two terms in total variance. Conditional on Brownian geometry the transform is entire, with cumulants given by length powers times excursion area; averaging over geometry can destroy every positive exponential moment. These are deductions from the existing exploration and marked-state results. No new source passage, published-source correction, common-parameter conditional-kernel process or formal correspondence is claimed.


## Surplus drift and differentiability of its mean

WVGG derives the simple-graph drift by counting closed edges between components and within a component. The internal count is (k^2-3k+2)/2 minus surplus. This retains both the factor 1/(1-p_N) and the correction -3 N^(-2/3) S_N/2+N^(-1)-N^(-4/3) H_N. Its expected uniform difference from the augmented-coalescent drift is O(N^(-2/3)) on bounded critical intervals. 83JM passes the compensated martingales through EAQD's size/measure path limit. The drift is continuous on the closed state subspace whose surplus measure is supported below the size norm; all-moment bounds justify passage of martingale identities and expectations. Absence of fixed-time jumps makes the mean drift continuous, yielding a strictly positive continuous derivative of expected weighted surplus. The moving-parameter marked-state limit gives uniform convergence of the finite derivatives on compact intervals. OWBW's conditional means give the Brownian-area version of that derivative. These are deductions from the existing results and finite jump-process calculus; no new source passage, published-source error or formal correspondence is claimed.


## Drift and martingale equations for the surplus profile

LX6L tests the size-weighted surplus measure with a locally Lipschitz function whose local supremum and Lipschitz bounds grow polynomially. Collecting the merger increments by the component carrying a mark produces a kernel determined by the size sequence and surplus measure; subtracting its diagonal removes self-mergers even at equal sizes. The squared-mass tail gives uniform convergence of that kernel, so the drift is continuous on the compatible state space. The finite simple-graph drift retains the exact internal missing-edge correction, with expected uniform error O(N^(-2/3)). E4JW passes the compensated profiles through EAQD and proves C1 convergence of their expectations on compact parameter intervals. Polynomial tests give the explicit size/surplus hierarchy, involving only size powers of order at least two. The hierarchy retains joint moments and is not closed in the means. These are deductions from existing results and the merger/birth calculation; no new source passage, published-source error or formal correspondence is claimed.


## Quadratic rates and realized quadratic variation

VM8H computes products of surplus-profile increments and the exact finite simple-graph quadratic-rate correction. For countable marked states it identifies the additional sum K=sum_i x_i y_i^2: weighted surplus H=sum_i x_i y_i alone does not bound the square of a merger increment. The total-surplus quadratic rate is finite exactly when K is finite for nonzero mass states. XT0C instead controls variation along actual critical paths. Each profile increment is bounded by a polynomial local constant times the increase of H. This variation bound passes through the common Skorokhod clock. Uniform convergence with bounded variation then controls the cumulative jump-product sums directly. All-moment bounds give convergence of mixed moments and allow the finite product-martingale identities to pass to the limit. The result identifies realized quadratic variation, not a density for its predictable compensator; the countable squared-mark tail estimate and covariance derivative limits remain open. These are deductions from existing results and jump-process calculus; no new source passage, published-source error or Lean correspondence is asserted.


## Future surplus moments and predictable covariations

4W2Z bounds D_I=sum_(i in I,j!=i) x_i x_j^3 y_i^2 by (1/h+S) times the conditional second moment of the selected old marks' weighted contribution h time units later. Direct connection probabilities are at least h x_i x_j/(1+h S), and expansion of the future square supplies the bound. Critical all-moment estimates then give finite K=sum x_i y_i^2 almost surely and all moments of the quadratic rates, without claiming moments of K itself. NH8N transports negligible initial mark tails; conditional Jensen converts their later moments into present quadratic-rate tail control. A separate finite marked head and small mass tail finish the truncation argument.

GJB6 uses those tails to pass quadratic rates and their integrals through the critical size/measure path limit. Positive distinct limiting masses recover finitely many marks at almost every time. The exact finite product-martingale identity identifies the predictable bracket; the product-mean identity gives C1 covariance convergence on compact parameter intervals. The finite-rate error is pointwise Lr uniformly in the parameter, not an expected supremum of instantaneous errors. This supplies the additional control left open in VM8H/XT0C while preserving their statements. These are deductions from existing graphical, moment and tail results; no new source passage, published-source error or Lean correspondence is asserted.


## Nonlinear observables of the surplus profile

BH5K extends the future-moment estimate to every power r>=1. A later inherited surplus rth moment bounds the present directed rate sum x_i*x_j^(r+1)*y_i^r. Transported initial mark tails, followed by a finite marked head and an l2 mass tail, give compact uniform Lq truncation of the full jump rth moment. No moments of the finite-head marked factor are needed.

KP1O uses these bounds for C1 functions of finitely many surplus profiles whose gradients grow polynomially. The mean-value formula separates first and higher jump moments, making the nonlinear generator and its rank tails integrable. The exact internal missing-edge count gives the finite correction and a pointwise Lq error of order N^(-2/3), uniform in the parameter. Positive distinct masses recover the finite marked heads through the size/measure path limit. Uniform integrability then passes compensators, martingale identities and expectation derivatives. Finite Taylor expansion gives a correlated polynomial hierarchy; bounded Fourier tests give the joint characteristic-function equation, uniformly on compact parameter/frequency sets. These are deductions from existing results, the mean-value formula and finite jump-process calculus. No new source passage, published-source error or Lean correspondence is asserted.


## Sharp squared-mass and weighted-surplus tails

X92C applies the finite merger generator to 1/S. Before a component reaches size sqrt(s)/2, starting from S>=s, its drift is at most -1/2. Stopping bounds the expected hitting time by 2/s. In the critical simple graph the clock factor only makes this drift more negative. Thus large present S forces a large component within 4/s parameter units with probability at least one half; the existing cubic largest-component tail gives exp(-c s^(3/2)), uniformly in the finite graphs and the limit.

J2VQ bounds the supremum of the fixed-parameter reflected Brownian queue by exp(-c h^(3/2)). The initial interval of length sqrt(h) uses reflection. Later unit intervals use grids of mesh n^(-2), the reversed-increment bound by Brownian motion with drift -n/4, and reflection inside each grid cell. The conditional weighted-surplus mean is at most queue supremum times squared mass; no independence is used. Conditional Poisson exponential Markov, with parameter x^(-1/4), then yields the matching exp(-c x^(3/4)) upper tail. Combined with 7E7T this gives sharp moment growth and a positive finite threshold for exponential moments of H^(3/4), without identifying the threshold or its boundary. Monotonicity transfers the conclusions to integrated surplus. The signed-square-root argument from NM14 gives joint moment determinacy. The surplus upper bound concerns the limiting law; no finite-N exponential-power uniformity is claimed. These are deductions from existing results, finite stopped-generator calculus, Brownian reflection and exponential martingales. No new source passage, published-source correction or Lean correspondence is asserted.


## Uniform finite queue and surplus tails

N81A pads the actual discovery trials at step i to N-i independent Bernoulli trials, so the full queue is bounded by one plus the reflection of a walk with independent Bin(N-i,p_N)-1 increments. Only this independent walk is reversed. Its deterministic mean is a concave quadratic. An initial interval of length sqrt(h) on the critical scale uses N9DF; late unit intervals use mesh c_N^2/n^2, a reversed exponential supermartingale at each left endpoint, and forward maximal bounds inside each cell. The restriction h<=c_N^2 comes from the actual deterministic queue bound, and ensures the linear term in Bernstein's estimate is strong enough. This gives the full uniform queue tail of power 3/2.

65IO conditions separately on the actual discovery transcript, leaving genuine surplus bits independent Bernoulli. The weighted conditional mean is at most Np_N times queue supremum times squared mass. X92C and the new queue estimate bound this product; conditional exponential Markov then gives the uniform finite surplus tail of power 3/4. Uniform integrability passes small endpoint-power exponential moments, and every fixed exponential moment below that power, through the moving-parameter limit. A terminal-time Holder bound upgrades the joint path expectation theorem to simultaneous fractional-exponential growth. No exact maximal parameter, boundary convergence, fractional-exponential parameter derivative, new source passage, source error or formal correspondence is asserted.


## Global exploration and weighted component shapes

The [global queue limit](../articles/finite-triangle-window.md#section-critical-global-queue-law) uses the late blocks of N81A at a fixed height, so that the queue vanishes uniformly after a large exploration time. It retains the Brownian geometry in the joint ranked-size, weighted-surplus and conditional-kernel law.

The [weighted shape theorem](../articles/finite-triangle-window.md#section-critical-excursion-shape-law) records whole component queue shapes with squared-size weights. Its exact finite identity distinguishes queue area from the conditional surplus mean by the root/processed-vertex correction. Moment and fractional-exponential conclusions follow from the established queue, size and surplus tails. This is a fixed-parameter exploration result, not a full marked-state process theorem across the critical window.


## Higher conditional distances and analytic transforms

[WYUD](../articles/finite-triangle-window.md#section-surplus-higher-wasserstein) uses the existing Bernoulli–Poisson coupling edge by edge. Every fixed discrepancy moment is O(p^2); a set-partition expansion controls the weighted sum. Uniform critical moments then give E W_q^q=O(N^(-1)) for all finite q>=1, and continuity upgrades the random conditional kernel topology. This is a finite Poisson approximation rate, not a rate to the Brownian limit.

[L3KC](../articles/finite-triangle-window.md#section-surplus-conditional-analytic-limit) treats the conditional transform as a random entire function. Local logarithms are used only on disks where each binomial factor stays near one. Their error is bounded by 2p a^2 exp(2aR)U; continuity of the weighted Poisson exponent and Cauchy's formula pass the transforms and derivatives. Stirling-number expansion gives exact conditional cumulants and the order-N^(-1) correction to the corresponding Poisson cumulants. No global finite-transform logarithm, averaged positive transform integrability, source correction or formal correspondence is asserted.
