---
{
  "id": "cutoff-localization",
  "title": "Localization of cutoff clusters",
  "subtitle": "Spatial mass and volume moments",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Correlation lengths control the mass outside a large ball. Localization of higher volume moments needs additional control of large clusters; a uniform moment-ratio bound supplies one sufficient condition.",
  "context": [
    "A countable metric vertex set with root $o$; $B_R=\\{x:d(o,x)\\leq R\\}$.",
    "For each real $r\\geq1$, $K_r$ is a random subset containing $o$, with measurable membership events and finite positive mean size.",
    "These are conditions on a family of laws. No coupling between different radii is assumed."
  ],
  "related": [
    "spatial-cutoff-moments",
    "cutoff-families",
    "cutoff-scaling",
    "multipoint-trees",
    "pointwise-long-range"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "hutchcroft-lrp-2",
    "hutchcroft-pointwise-2024"
  ],
  "aliases": [
    "CL",
    "wCL",
    "weak cutoff localization",
    "correlation-length condition",
    "radius of gyration"
  ],
  "prototypeUses": []
}
---

## Spatial localization {#section-spatial}

<p>Write $X_r=|K_r|$, $m_q(r)=\mathbb E X_r^q$, and $\chi_r=m_1(r)$. In a cutoff percolation model, $K_r$ is the root cluster under the cutoff law at the full model's critical parameter. Finite susceptibility of that cutoff law is a hypothesis here.</p>

<a id="tag-J7SM" data-assertion="definition" data-title="Correlation-length condition"></a>
<p>For each finite real $p&gt;0$, define</p>
<div class="math-display">$$\xi_p(r)^p=\frac{1}{\chi_r}\mathbb E\sum_{x\in K_r}d(o,x)^p.$$</div>
<p>The family satisfies the correlation-length condition (CL) if, for every finite $p&gt;0$, there is a finite constant $C_p$ such that $\xi_p(r)\leq C_p r$ for every $r\geq1$. The constant may depend on $p$ but not on $r$.</p>
<p>The normalization weights a cluster by its mass and then samples a vertex uniformly from it. It is not the law obtained by first sampling an unweighted cluster and then a uniform vertex. The quantified condition above concerns finite $p$.</p>

<a id="tag-32GP" data-assertion="proposition" data-title="A spatial moment localizes the first volume moment"></a>
<p>If $\xi_p(r)\leq C_p r$ for one fixed $p&gt;0$ and every $r\geq1$, then for every $C&gt;0$, writing $Z_{r,C}=|K_r\setminus B_{Cr}|$,</p>
<div class="math-display">$$\frac{\mathbb E Z_{r,C}}{\chi_r}\leq\left(\frac{C_p}{C}\right)^p.$$</div>
<p>Consequently, for each $\varepsilon&gt;0$ a single finite $C&gt;0$ gives $\chi_r\leq(1+\varepsilon)\mathbb E|K_r\cap B_{Cr}|$ for all $r\geq1$.</p>
<p><em>Proof.</em> Every vertex outside the ball contributes more than $(Cr)^p$ to the spatial sum. Take expectations and divide by $\chi_r(Cr)^p$. Since $X_r=|K_r\cap B_{Cr}|+Z_{r,C}$, it suffices to choose $C$ so that $(C_p/C)^p\leq\varepsilon/(1+\varepsilon)$.</p>
<p>This controls the expected mass lost outside the ball, rather than the probability that the entire cluster lies inside it. It also gives $\mathbb P(Z_{r,C}&gt;0)\leq\chi_r(C_p/C)^p$, but the latter bound need not be small uniformly when $\chi_r$ grows.</p>

## Localization of volume moments {#section-moments}

<a id="tag-AWWU" data-assertion="definition" data-title="Weak cutoff localization of four volume moments"></a>
<p>Suppose $m_q(r)&lt;\infty$ for $q=1,2,3,4$ and every $r\geq1$. The family satisfies weak cutoff localization (wCL) if for every $\varepsilon&gt;0$ there exists a finite $C&gt;0$ such that, simultaneously for $q=1,2,3,4$ and all $r\geq1$,</p>
<div class="math-display">$$m_q(r)\leq(1+\varepsilon)\mathbb E|K_r\cap B_{Cr}|^q.$$</div>
<p>The same ball radius factor must work for all four moments and all cutoff scales. The local count is the intersection of the full cutoff cluster with the ball, not the root cluster obtained by deleting paths that leave the ball.</p>

<a id="tag-39MV" data-assertion="theorem" data-title="Spatial localization and moment ratios imply weak cutoff localization"></a>
<p>Suppose the spatial bound $\xi_p(r)\leq C_p r$ holds for some fixed $p&gt;0$. Suppose also that the moments through order seven are finite and that, for each $q=2,3,4$, there is a finite constant $A_q$ such that</p>
<div class="math-display">$$\frac{m_{2q-1}(r)\chi_r}{m_q(r)^2}\leq A_q\qquad(r\geq1).$$</div>
<p>Then (wCL) holds. More precisely, with $A_1=1$ and $Y_{r,C}=|K_r\cap B_{Cr}|$,</p>
<div class="math-display">$$0\leq\frac{m_q(r)-\mathbb E Y_{r,C}^q}{m_q(r)}\leq q\sqrt{A_q}\left(\frac{C_p}{C}\right)^{p/2}\qquad(q=1,2,3,4).$$</div>
<p><em>Proof.</em> Fix $r,C$ and suppress their indices. Since $0\leq Y\leq X$, the factorization of $X^q-Y^q$ gives $X^q-Y^q\leq qX^{q-1}Z$, where $Z=X-Y$. Cauchy–Schwarz, applied to $X^{q-1}\sqrt Z$ and $\sqrt Z$, yields</p>
<div class="math-display">$$\mathbb E(X^{q-1}Z)\leq\bigl(\mathbb E[X^{2q-2}Z]\,\mathbb E Z\bigr)^{1/2}\leq\bigl(m_{2q-1}(r)\,\mathbb E Z\bigr)^{1/2}.$$</div>
<p>Use the spatial estimate for $\mathbb E Z$, then divide by $m_q(r)$. For $q=1$ the moment ratio equals one. Choose $C$ large enough that all four right-hand sides are at most $\varepsilon/(1+\varepsilon)$. Rearranging gives (wCL).</p>
<p>The uniform moment ratios are additional assumptions, not consequences of the definition of (CL). For example, the two-sided moment scales $m_s(r)\asymp z(r)^{s-a}$ for $s=1,\ldots,7$, with fixed $0&lt;a&lt;1$ and constants uniform in $r$, supply them: the powers in $m_{2q-1}\chi/m_q^2$ cancel. The <a href="/articles/cutoff-scaling/#section-volume">uniform volume-tail cutoff bounds</a> are one way to obtain those scales. Establishing such bounds for a particular model remains a separate problem.</p>

## From localized damping to full moment ratios {#section-damping}

<a id="tag-0WAE" data-assertion="proposition" data-title="Localized exponential damping controls the full moment ratios"></a>
<p>Let $0\leq Y_r\leq X_r$ and write $m_p(r)=\mathbb E X_r^p$. Suppose the first four moments are finite and positive. Let $Q(r)&gt;0$, and suppose constants $A,b,L&gt;0$, independent of $r$, satisfy</p>
<div class="math-display">$$\mathbb P(Y_r\geq tQ(r))\leq A e^{-bt}\mathbb P(Y_r\geq Q(r))\qquad(t\geq1),$$</div>
<div class="math-display">$$m_j(r)\leq L\mathbb E Y_r^j\qquad(j=2,3,4).$$</div>
<p>There is a finite constant $D$, depending only on $A,b,L$, for which</p>
<div class="math-display">$$m_2\leq DQm_1,\qquad m_3\leq DQ^2m_1,\qquad m_3\leq DQm_2,\qquad m_4\leq DQ^2m_2.$$</div>
<p><em>Proof.</em> The <a href="/tag/BZDZ/">rooted damping estimate</a> gives $\mathbb E Y_r^{p+q}\leq D_{p,q}Q(r)^q\mathbb E Y_r^p$. Apply it for $(p,q)=(1,1),(1,2),(2,1),(2,2)$, use localization at order $p+q$, and then $Y_r\leq X_r$. Take $D=L\max D_{p,q}$ over these four pairs.</p>
<p>For cutoff clusters, (wCL) with $\varepsilon=1$ supplies one fixed $C\geq1$ and $L=2$, with $Y_r=|K_r\cap B_{Cr}|$. If the rooted damping bound holds at the window quantile, take $Q(r)=M(r,Cr)$. Under an increasing coupling of the cutoff laws, $M(r,Cr)\leq M(Cr,Cr)$. Thus the estimates retain one fixed radius factor; no limit in $C$ is taken while $r$ varies.</p>
<p>This direction of implication is distinct from the earlier sufficient criterion for (wCL). Here localization and rooted damping are inputs, and the conclusion concerns moment ratios. It must not be used together with that criterion as a circular proof of localization.</p>

## Why the higher moments matter {#section-example}

<a id="tag-IBK7" data-assertion="proposition" data-title="Spatial localization alone need not localize the second volume moment"></a>
<p>There is a family of finite random subsets on a countable metric space satisfying (CL), with every volume moment finite at every radius, for which (wCL) fails already at $q=2$.</p>
<p>To construct it, let $N_n=\lceil e^{n^2}\rceil$ for integers $n\geq2$. Attach $N_n$ leaves to a root by edges of length $n^2$, for each $n$, and use the resulting tree metric on the root and leaves. At radius $r=n$, let $K_n$ consist of the root and all $N_n$ leaves in that group with probability $a_n=N_n^{-3/2}$, and otherwise just the root. At every other radius take the root alone. This defines random subsets, not an independent-bond model.</p>
<p>Every set in each law is finite. At an integer radius, $\chi_n=1+N_n^{-1/2}$ and</p>
<div class="math-display">$$\frac{\xi_p(n)^p}{n^p}=\frac{N_n^{-1/2}n^p}{1+N_n^{-1/2}}.$$</div>
<p>For every fixed $p&gt;0$ this is bounded in $n$, since exponential decay dominates $n^p$; at other radii it is zero. Thus (CL) holds for all finite $p$. But if $n&gt;C$, all the leaves used at radius $n$ lie outside $B_{Cn}$, so $|K_n\cap B_{Cn}|=1$, whereas</p>
<div class="math-display">$$m_2(n)=1+a_n\bigl((N_n+1)^2-1\bigr)=1+N_n^{1/2}+2N_n^{-1/2}\longrightarrow\infty.$$</div>
<p>No fixed $C$ can therefore give the $q=2$ comparison even with $\varepsilon=1$. Rare large sets have negligible expected spatial mass but dominate the second volume moment. Additional structure of a percolation model may rule this out; the definition of (CL) alone does not.</p>

## Source scope {#section-source}

<p>The definitions make finite moments and the range $r\geq1$ explicit so that the ratios and comparisons are meaningful. (wCL) is a separate input supplied by model-specific localization technology. The conditional argument above gives one sufficient moment-ratio criterion; it is not a proof of any model-specific localization claim. Neither a Sak upper bound nor a sharp crossover boundary is established here.</p>

## Quoted localization regimes {#section-quoted-regimes}

<p>Model-specific Euclidean two-point and localization results are not additional hypotheses of the conditional propositions above. In particular, the following distinctions must be kept.</p>

<ul><li>Averaged two-point bounds are distinct from pointwise estimates. Pointwise comparisons are available only where the required localization and regularity inputs are available, including the non-perturbative $\alpha&lt;1$ range and separately supplied perturbative regimes. An averaged estimate alone is not recorded here as a pointwise estimate.</li>
<li>The range $\alpha&lt;1$ is a sufficient localization range for the Euclidean power-law models treated in the literature, together with two-sided kernel regularity and a non-trivial critical point. The passage from (CL) to a pointwise upper bound also calls for regularity inputs; the definition of (CL), by itself, does not prove that bound for every kernel.</li>
<li>The following paragraph discusses the larger $\alpha&lt;2$ spatial range in the high- and critical-effective-dimensional models covered by the cutoff theory. That model qualification cannot be dropped or applied to every pair $(d,\alpha)$. The expected Sak crossover in low dimensions is presented separately as a prediction.</li>
<li>The matching pointwise lower bound is attributed to separate arguments. Failure of (CL) in some short-range regimes is also distinct from a theorem identifying the entire expected crossover boundary.</li></ul>

<p>These are scope distinctions, not a correspondence certificate for external references. Before assigning a permanent theorem tag to a model-specific localization result, the source theorem and revision must fix the dimension and parameter ranges, kernel regularity, critical-point assumptions, cutoff convention and uniformity of its constants. The conditional results in this article and the <a href="/articles/cutoff-hydrodynamics/">cutoff hydrodynamics article</a> therefore retain their stated inputs.</p>

<p>Candidate locators are now available in the <a href="https://arxiv.org/pdf/2508.18808v1">versioned PDF of Long-range II</a>: kernel assumptions on p. 3 and §II.1.1, (CL) in Definition II.1.3, and Theorems II.1.5 and II.1.7 on pp. 10–11. The kernel is radial and decreasing, with $|J'(r)|=C(1+\delta_r)r^{-d-\alpha-1}$, $\delta_r\to0$ and $\int_{r_0}^\infty|\delta_r|\,dr/r&lt;\infty$; footnote 3 relaxes the rate assumption for low-dimensional results. These locators narrow the correspondence work; they do not establish that every formulation above has identical hypotheses.</p>


## Spatial moments and pointwise decay {#section-pointwise}

<p>The passage from (CL) to a two-point bound uses more than the definition of a correlation length. The following formulation isolates the inputs from §II.2.1 of <a href="https://arxiv.org/pdf/2508.18808v1">Long-range II</a>. Use the supremum norm on $\mathbb Z^d$; changing a fixed norm only changes the constants.</p>

<a id="tag-AUAE" data-assertion="proposition" data-title="Correlation lengths and rapid cutoff decay under explicit derivative inputs"></a>
<p>Let $d\geq1$ and $0&lt;\alpha\leq d$. For $r\geq1$, let $\tau_r(x,y)$ be the two-point function of a translation-invariant percolation law, increasing to $\tau_\infty(x,y)$, and put $\chi_r=\sum_x\tau_r(0,x)&lt;\infty$. Suppose there are positive constants, independent of $r,R,x,y$, such that</p>
<div class="math-display">$$\chi_r\geq c r^\alpha,\qquad
\sum_{\|x\|_\infty\leq R}\tau_\infty(0,x)\leq A R^\alpha\quad(R\geq1),\qquad
\tau_1(x,y)\leq A_0e^{-c_0\|x-y\|_\infty}\quad(x\ne y).$$</div>
<p>Assume that $r\mapsto\tau_r(x,y)$ is locally absolutely continuous and, for some $D&gt;0$ and $L\geq1$, satisfies almost everywhere</p>
<div class="math-display">$$0\leq\partial_r\tau_r(x,y)\leq D r^{-d-\alpha-1}
\sum_{\|a-b\|_\infty\leq Lr}\tau_r(x,a)\tau_r(b,y).$$</div>
<p>If $\xi_p(r)\leq C_p r$ for one $p&gt;d-\alpha$, then, uniformly for $r\geq1$ and distinct $x,y$, writing $R=\|x-y\|_\infty$,</p>
<div class="math-display">$$\tau_r(x,y)\leq C R^{-d+\alpha}(1\vee R/r)^{-p+d-\alpha}.$$</div>
<p>Under the same standing inputs, (CL) is equivalent to the existence of a nonincreasing function $h:(0,\infty)\to(0,1]$, with $t^q h(t)\to0$ for every $q&gt;0$, such that</p>
<div class="math-display">$$\tau_r(x,y)\leq C R^{-d+\alpha}h(R/r).$$</div>
<p>Either condition implies $\tau_\infty(x,y)\leq C R^{-d+\alpha}$.</p>

<p><em>Proof.</em> The spatial moment bound gives $\sum_{\|z\|_\infty&gt;\lambda r}\tau_r(0,z)\leq C_p^p\lambda^{-p}\chi_r$. Choose one fixed $\lambda\geq1$ making the right-hand side at most $\chi_r/2$. Domination by $\tau_\infty$ in the remaining ball then gives $\chi_r\leq2A(\lambda r)^\alpha$. In particular, the derivative bound with its geometric restriction discarded is at most $C r^{-d+\alpha-1}$.</p>
<p>For $1\leq r\leq R/(4L)$, each contributing pair $a,b$ has $\|x-a\|_\infty&gt;R/4$ or $\|y-b\|_\infty&gt;R/4$. Applying the spatial tail bound to that factor and summing the other one yields</p>
<div class="math-display">$$\partial_r\tau_r(x,y)\leq C R^{-p}r^{p-d+\alpha-1}.$$</div>
<p>Since $p-d+\alpha&gt;0$, integration from $1$ to $r$ and the exponential bound at $r=1$ give $\tau_r(x,y)\leq C R^{-p}r^{p-d+\alpha}$. The exponentially small initial term is absorbed because $r\geq1$.</p>
<p>If $\alpha&lt;d$, integrate the unrestricted derivative bound from $R/(4L)$ upwards; its total integral is at most $C R^{-d+\alpha}$. If $\alpha=d$, use $\tau_r(x,y)\leq1$ instead. Thus the claimed bound also holds for $r\geq R/(4L)$, after adjusting its constant. The finitely many lattice displacements with $R&lt;4L$ are covered by the same adjustment. This treats the endpoint without integrating $r^{-1}$ to infinity.</p>
<p>When (CL) holds, choose $p&gt;d-\alpha+q$ for each desired power $q$. The preceding estimates have a common envelope: let</p>
<div class="math-display">$$F(t)=\sup\{R^{d-\alpha}\tau_r(x,y):r\geq1,\ x\ne y,\ R/r\geq t\},$$</div>
<p>with the empty supremum equal to zero. Then $F$ is nonincreasing, bounded by a finite $M&gt;0$, and decays faster than every power. The function $h(t)=(F(t)/M+e^{-t})/2$ is positive, at most one, and has the required decay; it bounds the two-point function with constant $2M$. Monotone convergence in $r$ gives the full-model bound.</p>
<p>Conversely, the lattice shell of radius $n$ has at most $C_d n^{d-1}$ vertices. For any $p&gt;0$, choose $q&gt;\alpha+p$ and use $h(t)\leq C_q(1\vee t)^{-q}$. Splitting the shell sum at $r$ gives</p>
<div class="math-display">$$\sum_x\|x\|_\infty^p\tau_r(0,x)
\leq C_p\sum_{n\geq1}n^{\alpha+p-1}h(n/r)
\leq C_p r^{\alpha+p}.$$</div>
<p>Divide by the assumed lower bound $\chi_r\geq c r^\alpha$ to obtain (CL). The root contributes zero to this spatial moment.</p>

## Random boxes and exponential cutoff decay {#section-random-boxes}

<p>In the range $\alpha&lt;1$, randomizing the box size produces a small exit sum at a scale comparable to the cutoff. A previously established pointwise bound supplies the last segment of the path. This is the input used in §II.2.2 of Long-range II; it must not be deduced from the localization conclusion one is trying to prove.</p>

<a id="tag-YUHF" data-assertion="proposition" data-title="Random-box exit bounds give exponential decay beyond the cutoff"></a>
<p>Let $d\geq1$ and $0&lt;\alpha&lt;1$. For each $r\geq1$, consider independent bond percolation on $\mathbb Z^d$ with symmetric translation-invariant opening probabilities $q_r(x,y)$. Suppose, uniformly in $r$ and distinct $x,y$,</p>
<div class="math-display">$$q_r(x,y)=0\quad\hbox{if }\|x-y\|_\infty&gt;Lr,\qquad
q_r(x,y)\leq A\|x-y\|_\infty^{-d-\alpha},\qquad
\tau_r(x,y)\leq B\|x-y\|_\infty^{-d+\alpha},$$</div>
<p>where $L\geq1$ and $A,B&lt;\infty$ do not depend on $r$. Then there are constants $C,c&gt;0$, independent of $r,x,y$, such that</p>
<div class="math-display">$$\tau_r(x,y)\leq C\|x-y\|_\infty^{-d+\alpha}
\exp\!\left(-c\frac{\|x-y\|_\infty}{r}\right).$$</div>
<p>Consequently $\chi_r&lt;\infty$ and $\sum_x\|x\|_\infty^p\tau_r(0,x)\leq C_p r^{\alpha+p}$ for every $p&gt;0$. If in addition $\chi_r\geq c_1r^\alpha$, then (CL) holds.</p>

<p><em>Proof.</em> Set $\Lambda_n=[-n,n]^d\cap\mathbb Z^d$ and define</p>
<div class="math-display">$$\Phi_r(n)=\sum_{a\in\Lambda_n,\ b\notin\Lambda_n}
\mathbb P_r(0\xleftrightarrow{\Lambda_n}a)q_r(a,b).$$</div>
<p>For $a\in\Lambda_n$, write $k=n-\|a\|_\infty$. An edge leaving the box has length at least $k+1$, so its total opening probability is at most $C(k+1)^{-\alpha}$ by shell summation. It is zero when $k\geq Lr$. Sum first over box sizes and then over their vertices. The pointwise bound, including the root separately, gives $\sum_{a\in\Lambda_N}\tau_r(0,a)\leq C N^\alpha$, and hence</p>
<div class="math-display">$$\frac1N\sum_{n=1}^N\Phi_r(n)
\leq\frac C N\sum_{a\in\Lambda_N}\tau_r(0,a)
\sum_{0\leq k\leq\lceil Lr\rceil}(k+1)^{-\alpha}
\leq C\left(\frac rN\right)^{1-\alpha}.$$</div>
<p>Choose a fixed, sufficiently large $D$ and take $N=\lceil Dr\rceil$. Some integer $s\leq N$ then has $\Phi_r(s)\leq1/2$. Put $R'=s+Lr\leq C r$.</p>
<p>Fix $z\ne0$, write $R=\|z\|_\infty$, and take $m=\lfloor R/(2R')\rfloor$. On a simple open path from $0$ to $z$, successively record the first edge leaving the box of radius $s$ about the endpoint of the preceding recorded edge. Each exit advances by at most $R'$ in supremum distance. The first $m$ exits therefore end at a vertex at distance at most $R/2$ from $0$, leaving a final connection of length at least $R/2$.</p>
<p>The internal path segments, the exit edges and the final connection have disjoint edge witnesses. Apply <a href="/tag/AUUG/">BK for finitely many events</a>, then sum over all exit endpoints. Each exit contributes at most $\Phi_r(s)\leq1/2$, while the final segment contributes at most $C R^{-d+\alpha}$. This also covers $m=0$ using the assumed pointwise bound. Thus</p>
<div class="math-display">$$\tau_r(0,z)\leq C R^{-d+\alpha}2^{-m}
\leq C'R^{-d+\alpha}e^{-cR/r}.$$</div>
<p>Shell summation proves the susceptibility and spatial moment bounds. Dividing the latter by $\chi_r\geq c_1r^\alpha$ proves the last assertion.</p>
<p>For the paper's soft cutoff, $q_r=1-e^{-\beta_cJ_r}\leq\beta_cJ_r\leq\beta_cJ$ and the cutoff support gives the required jump bound, with $L$ accounting for norm equivalence. The pointwise input is <a href="https://arxiv.org/html/2404.07276v1">Theorem 1.4 of the earlier two-point paper</a>, inspected as a cited theorem, not proved here. Its hypotheses include a symmetric summable translation-invariant kernel with two-sided power-law bounds and $\alpha&lt;1$. The cutoff susceptibility lower bound is the separate input (II.2.2). These inputs close the random-box argument; they do not supply higher volume-moment localization or determine the full crossover boundary.</p>


## Low-dimensional volume moments and localization {#section-low-dimensional-moments}

<a id="tag-SOHR" data-assertion="theorem" data-title="A second-moment barrier gives moment scaling and weak localization below the critical dimension"></a>
<p>Assume the translation-invariant laws and two-point and higher-point bounds of <a href="/tag/1EWL/">1EWL</a>, now with independent bonds and $d&lt;3\alpha$. Write $X=|K_0|$, $\chi_r=\mathbb E_rX$, $M_p(r)=\mathbb E_rX^p$, and $\theta=(d+\alpha)/2$. Suppose $M_2$ is locally absolutely continuous on $[1,\infty)$ and that finite sets $B_r\subset\mathbb Z^d$ and measurable coefficients $a(r)\geq0$ satisfy</p>
<div class="math-display">$$a(r)r^{d+\alpha+1}\longrightarrow a_0&lt;\infty,\qquad
a(r)|B_r|r^{\alpha+1}\longrightarrow b&gt;0,\qquad
\liminf_{r\to\infty}r^{-\alpha}\chi_r\geq\frac{\alpha}{b}.$$</div>
<p>Assume the following derivative identity holds almost everywhere:</p>
<div class="math-display">$$M_2'(r)=3a(r)\mathbb E_r\left[X^2\sum_{y\in B_r}\mathbf1_{\{y\notin K_0\}}|K_y|\right].$$</div>
<p>Then for every integer $p\geq1$ there are constants $0&lt;c_p\leq C_p&lt;\infty$ such that</p>
<div class="math-display">$$c_p r^{\alpha+(p-1)\theta}\leq M_p(r)\leq C_p r^{\alpha+(p-1)\theta}\qquad(r\geq1).$$</div>
<p>For every such $p$ and every $\varepsilon&gt;0$, some $L&lt;\infty$ satisfies</p>
<div class="math-display">$$M_p(r)\leq(1+\varepsilon)\mathbb E_r|K_0\cap\{x:\|x\|_\infty\leq Lr\}|^p\qquad(r\geq1).$$</div>
<p>Thus the first four moments satisfy weak cutoff localization with a common radius for each prescribed error.</p>

<p><em>Proof.</em> Put $\kappa=\alpha+\theta$. By 1EWL, all the moments used below are finite, $M_3\leq C r^\theta M_2$, and $\chi_r\leq C r^\alpha$. We prove a lower bound for $r^{-\kappa}M_2$ by showing that it cannot decrease while it is small.</p>
<p>Suppose $M_2(r)\leq\delta r^\kappa$, and truncate cluster size at $T=\sqrt\delta\,r^\theta$. Since $X-(X\wedge T)\leq X^2/T$, for any fixed small $\eta&gt;0$ and all sufficiently large $r$ we have</p>
<div class="math-display">$$\mathbb E_r(X\wedge T)\geq\chi_r-\frac{M_2(r)}T
\geq\left(\frac\alpha b-\eta-\sqrt\delta\right)r^\alpha.$$</div>
<p>Harris applied to $X^2$ and $|K_y|\wedge T$, followed by subtraction of the event $y\in K_0$, yields</p>
<div class="math-display">$$\mathbb E_r[X^2(|K_y|\wedge T)\mathbf1_{\{y\notin K_0\}}]
\geq M_2\mathbb E_r(X\wedge T)
-\mathbb E_r[X^2(X\wedge T)\mathbf1_{\{y\in K_0\}}].$$</div>
<p>Bounded approximations justify Harris for $X^2$. Summing over $B_r$ and using $|K_0\cap B_r|\leq X$ in the error term gives</p>
<div class="math-display">$$M_2'\geq3a(r)\bigl[|B_r|M_2\mathbb E_r(X\wedge T)-T M_3\bigr].$$</div>
<p>Consequently, whenever $M_2\leq\delta r^\kappa$ and $r$ is sufficiently large,</p>
<div class="math-display">$$\frac{rM_2'}{M_2}\geq
3\left[a(r)|B_r|r^{\alpha+1}\left(\frac\alpha b-\eta-\sqrt\delta\right)
-C\sqrt\delta\,a(r)r^{d+\alpha+1}\right].$$</div>
<p>As $\eta,\delta$ tend to zero the limiting right side tends to $3\alpha$, whereas $\kappa&lt;3\alpha$ because $d&lt;3\alpha$. Choose these constants and then $r_0$ so that the right side is at least $\kappa$. The locally absolutely continuous function $f=r^{-\kappa}M_2$ therefore has $f'\geq0$ almost everywhere on $\{r\geq r_0:f(r)\leq\delta\}$. Applying the chain rule to $(\delta-f)_+$ shows that this positive part is nonincreasing. Hence</p>
<div class="math-display">$$f(r)\geq\min\{f(r_0),\delta\}&gt;0\qquad(r\geq r_0).$$</div>
<p>On $1\leq r\leq r_0$, the inequality $X\geq1$ supplies a positive lower constant. The same observation extends the assumed eventual susceptibility lower bound to all $r\geq1$. For $p\geq2$, Jensen under the size-biased probability measure gives</p>
<div class="math-display">$$M_p\geq\frac{M_2^{p-1}}{\chi_r^{p-2}}\geq c_p r^{\alpha+(p-1)\theta}.$$</div>
<p>The upper bound was proved in 1EWL.</p>
<p>Finally let $Y=|K_0\cap\{\|x\|_\infty\leq Lr\}|$. Factoring $X^p-Y^p$ and using the spatial moment bound in 1EWL gives</p>
<div class="math-display">$$0\leq M_p-\mathbb E_rY^p
\leq p\mathbb E_r[X^{p-1}(X-Y)]
\leq\frac{pW_p(r)}{(Lr)^2}
\leq C_pL^{-2}r^{\alpha+(p-1)\theta}.$$</div>
<p>Divide by the lower bound for $M_p$ and choose $L$ so that the relative error is at most $\varepsilon/(1+\varepsilon)$. Taking the largest of the four radii proves the final assertion.</p>
<p>This is the argument of Part II, §II.4.1 with its model inputs separated. For the soft cutoff in that paper, $a(r)=\beta_c|J'(r)|$; the derivative identity uses Russo's formula and mass transport, and the sharp susceptibility lower coefficient comes from Part I. Those facts, their regularity hypotheses and the higher-order probability inequality must be supplied to obtain the full model theorem. No weak localization or seventh-moment ratio has been assumed in this proof.</p>


## Susceptibility from weak localization {#section-weak-first-moment}

<a id="tag-79SD" data-assertion="proposition" data-title="A divergent cutoff mean and weak first-moment localization determine susceptibility order and its dimension endpoint"></a>
<p>Let $K_r$ be the root cluster of a translation-invariant bond law on $\mathbb Z^d$, dominated by a full-law root cluster $K_\infty$. Write $B_R=\{x:\|x\|_\infty\leq R\}$ and $\chi_r=\mathbb E|K_r|$. Suppose $\chi_r$ is finite, positive and locally absolutely continuous for $r\geq r_0&gt;0$, tends to infinity, and satisfies</p>
<div class="math-display">$$0\leq\chi_r'\leq a(r)\chi_r^2\quad\text{a.e.},\qquad a(r)\sim b r^{-\alpha-1},\quad b,\alpha&gt;0.$$</div>
<p>Assume also, for fixed $C,L,A&lt;\infty$, with $C\geq1$ and $L,A&gt;0$,</p>
<div class="math-display">$$\chi_r\leq L\mathbb E|K_r\cap B_{Cr}|,\qquad
\mathbb E|K_\infty\cap B_R|\leq A R^\alpha$$</div>
<p>at all sufficiently large radii. Then</p>
<div class="math-display">$$\chi_r\asymp r^\alpha,\qquad
\liminf_{r\to\infty}r^{-\alpha}\chi_r\geq\frac\alpha b,\qquad \alpha\leq d.$$</div>
<p>If $\alpha=d$, the full-law root cluster is infinite with positive probability.</p>
<p><em>Proof.</em> Integrate the derivative of $1/\chi$ from $r$ to $R$. Since $\chi_R\to\infty$, letting $R\to\infty$ gives</p>
<div class="math-display">$$\frac1{\chi_r}\leq\int_r^\infty a(s)\,ds\sim\frac b\alpha r^{-\alpha}.$$</div>
<p>The upper bound follows directly from localization, domination and the averaged estimate: $\chi_r\leq LA(Cr)^\alpha$. Also $\chi_r\leq L|B_{Cr}|=O(r^d)$, so the lower bound rules out $\alpha&gt;d$.</p>
<p>If $\alpha=d$ and $K_\infty$ were finite almost surely, then $|K_\infty\cap B_R|/|B_R|\to0$ almost surely and is bounded by one. Dominated convergence would give $\mathbb E|K_\infty\cap B_R|=o(R^d)$, contradicting the localization bound and $\chi_r\succeq r^d$. This proves the endpoint assertion without assuming a continuous transition.</p>
<p>The averaged input concerns the full law, while the differential inequality concerns the cutoff law. In the setting of <a href="/tag/GG8B/">GG8B</a>, the latter follows from the distinct-cluster upper bound with $a(r)=c(r)|B_r|$. Divergence of the cutoff susceptibility is still a separate criticality input. This is the mechanism of Lemma II.4.9 and Corollary II.4.10; it does not presume a pointwise critical estimate.</p>


## The susceptibility scale below criticality {#section-subcritical-susceptibility}

<a id="tag-04ZI" data-assertion="proposition" data-title="A reciprocal cutoff bound gives the minimum of the cutoff and full susceptibilities"></a>
<p>Let $\alpha,A,C&gt;0$. For each parameter $\beta$, let $f_\beta:[1,\infty)\to(0,\infty)$ be nondecreasing and locally absolutely continuous, with limit $X_\beta\in(0,\infty]$. Suppose, uniformly in $\beta$,</p>
<div class="math-display">$$f_\beta(r)\leq C r^\alpha,\qquad
f_\beta'(r)\leq A r^{-\alpha-1}f_\beta(r)^2\quad\text{a.e.}$$</div>
<p>With $1/\infty=0$,</p>
<div class="math-display">$$\left(X_\beta^{-1}+\frac A\alpha r^{-\alpha}\right)^{-1}
\leq f_\beta(r)\leq\min\{Cr^\alpha,X_\beta\}.$$</div>
<p>Consequently $f_\beta(r)\asymp\min\{r^\alpha,X_\beta\}$ with constants depending only on $\alpha,A,C$.</p>
<p><em>Proof.</em> Apply <a href="/tag/OP4X/">the reciprocal inequality</a> between $r$ and $R$ and let $R\to\infty$. The integral is $\int_r^\infty A s^{-\alpha-1}ds=(A/\alpha)r^{-\alpha}$. Monotonicity gives the upper bound by $X_\beta$. Finally, if $m=\min(r^\alpha,X_\beta)$, then $X_\beta^{-1}+(A/\alpha)r^{-\alpha}\leq(1+A/\alpha)/m$. This also covers $X_\beta=\infty$.</p>
<p>For increasing cutoffs converging edgewise to the full model, the monotone coupling and finite witnesses give $\chi_{\beta,r}\uparrow\chi(\beta)$. Thus the proposition gives Lemma II.6.1 once its critical cutoff upper bound and uniform Russo inequality are supplied. It does not assume finite full susceptibility or identify which parameters have it.</p>

## Uniform spatial localization below criticality {#section-subcritical-spatial}

<a id="tag-KA3B" data-assertion="theorem" data-title="Critical cutoff spatial bounds extend uniformly to all smaller percolation parameters"></a>
<p>Fix a norm on $\mathbb R^d$, $b,\alpha&gt;0$ and $p\geq1$. On $\mathbb Z^d$ consider independent bonds with intensities $\beta J_r(y-x)$, where $0\leq\beta\leq b$ and $r\geq1$. Assume $J_r$ is symmetric and nonnegative, vanishes for $\|z\|&gt;r$, increases to a finite value $J_\infty(z)$ for every $z\ne0$, and is locally absolutely continuous in $r$, with</p>
<div class="math-display">$$\partial_rJ_r(z)=v(r)\mathbf1_{\{\|z\|\leq r\}}\quad(z\ne0)\quad\text{a.e.},\qquad
0\leq v(r)\leq A r^{-d-\alpha-1}.$$</div>
<p>Write $\chi_{\beta,r}=\mathbb E_{\beta,r}|K_0|$, $\chi(\beta)=\mathbb E_{\beta,\infty}|K_0|$, and $S_{p,\beta}(r)=\mathbb E_{\beta,r}\sum_{x\in K_0}\|x\|^p$. Suppose that at the upper parameter, for every $r\geq1$,</p>
<div class="math-display">$$\chi_{b,r}\leq C_0r^\alpha,\qquad S_{p,b}(r)\leq D_p r^{p+\alpha}.$$</div>
<p>Then there are constants $c,C,C_p&gt;0$, independent of $\beta$ and $r$, such that</p>
<div class="math-display">$$c\min\{r^\alpha,\chi(\beta)\}\leq\chi_{\beta,r}\leq C\min\{r^\alpha,\chi(\beta)\},\qquad
S_{p,\beta}(r)\leq C_p r^p\chi_{\beta,r}.$$</div>
<p>In particular, uniformly in $\beta$ and $r\geq1$,</p>
<div class="math-display">$$\mathbb E_{\beta,r}|K_0\setminus B_{Lr}|\leq C_pL^{-p}\chi_{\beta,r}\quad(L\geq1),\qquad
\mathbb E_{\beta,r}|K_0\cap B_r|\geq c' r^\alpha\quad(1\leq r\leq\chi(\beta)^{1/\alpha}),$$</div>
<p>where $B_R=\{x:\|x\|\leq R\}$ and the upper radius is infinite when $\chi(\beta)=\infty$.</p>
<p><em>Proof.</em> Domination by parameter $b$ makes the finite-cutoff susceptibility and the $p$th spatial sum finite. The exact first-moment derivative and the distinct-cluster upper bound give</p>
<div class="math-display">$$0\leq\chi_{\beta,r}'\leq\beta v(r)|B_r|\chi_{\beta,r}^2
\leq A_0r^{-\alpha-1}\chi_{\beta,r}^2.$$</div>
<p>The identities and local absolute continuity follow from <a href="/tag/GG8B/">GG8B</a>; on bounded radius intervals its derivative envelope has finite support. Since $|B_r|\leq C_d r^d$, the constant $A_0$ is uniform in $\beta\leq b$. Apply 04ZI to obtain the susceptibility comparison.</p>
<p>For the spatial sum, the same finite-volume differentiation gives</p>
<div class="math-display">$$S_{p,\beta}'(r)=\beta v(r)\sum_{x,y,z}
\mathbf1_{\{\|y-x\|\leq r\}}\|z\|^p
\mathbb P_{\beta,r}(0\leftrightarrow x,\ y\leftrightarrow z,\ 0\nleftrightarrow y).$$</div>
<p>The joining window is centered at $x$. The two connections on the right have disjoint witnesses. BK therefore bounds their probability by $\tau_{\beta,r}(0,x)\tau_{\beta,r}(y,z)$. The elementary inequality</p>
<div class="math-display">$$\|z\|^p\leq3^{p-1}\bigl(\|x\|^p+\|y-x\|^p+\|z-y\|^p\bigr)$$</div>
<p>then gives, after summing in $x$, $y-x$ and $z-y$,</p>
<div class="math-display">$$0\leq S_{p,\beta}'(r)
\leq A_p r^{-\alpha-1}\chi_{\beta,r}S_{p,\beta}(r)
+B_p r^{p-\alpha-1}\chi_{\beta,r}^2.$$</div>
<p>This also justifies the countable derivative formula. On a compact radius interval, use the finite-support rate envelope and the two-point functions at the upper endpoint and parameter $b$ in the BK bound. The displayed three-term estimate makes the resulting sum integrable. For each triple the finite-volume connection and distinctness probabilities converge, so dominated convergence applies to the derivative sums and their parameter integrals. Passing to the limit in the integrated finite identity proves local absolute continuity. This is the one-weight argument of <a href="/tag/1K61/">1K61</a>; only polynomial growth of the weight is needed here. There is no induction on $p$.</p>
<p>Fix $\beta$ and put $X=\chi(\beta)$. If $X=\infty$, critical domination and the susceptibility lower bound give the claimed result immediately. Suppose $X&lt;\infty$, and set $y(r)=r^{-p}S_{p,\beta}(r)$. Then</p>
<div class="math-display">$$y'(r)\leq\frac{A_p r^{-\alpha}\chi_{\beta,r}-p}{r}y(r)
+B_p r^{-\alpha-1}\chi_{\beta,r}^2.$$</div>
<p>Choose $\lambda\geq1$, independently of $\beta$, so that $A_p\lambda^{-\alpha}\leq p/2$, and put $R=\lambda X^{1/\alpha}\geq1$. For $r\geq R$ the coefficient of $y$ is nonpositive. Dropping that term and integrating gives</p>
<div class="math-display">$$y(r)\leq y(R)+\frac{B_p}{\alpha}R^{-\alpha}X^2
\leq\left(D_p\lambda^\alpha+\frac{B_p}{\alpha}\lambda^{-\alpha}\right)X.$$</div>
<p>Here critical domination bounds $y(R)$ by $D_pR^\alpha$. Also $\chi_{\beta,r}\geq cX$ for $r\geq R$. For $1\leq r\leq R$, the susceptibility comparison gives $\chi_{\beta,r}\geq c\lambda^{-\alpha}r^\alpha$, and critical domination again suffices. This proves the uniform spatial bound on both sides of the susceptibility scale.</p>
<p>The spatial tail estimate follows by dividing the weighted sum by $(Lr)^p$. Choose $L\geq1$ so that $C_pL^{-p}\leq1/2$. If $r\geq L$ and $r\leq X^{1/\alpha}$, apply this estimate at cutoff $s=r/L$ and use monotonicity in the cutoff:</p>
<div class="math-display">$$\mathbb E_{\beta,r}|K_0\cap B_r|
\geq\mathbb E_{\beta,s}|K_0\cap B_{Ls}|
\geq\tfrac12\chi_{\beta,s}\geq\tfrac c2(r/L)^\alpha.$$</div>
<p>For $1\leq r&lt;L$, the root itself gives the same conclusion after decreasing the constant. This proves the final assertion.</p>
<p>These are the susceptibility and localization mechanisms of Lemma II.6.1, Proposition II.6.2 and (II.6.1). The theorem needs the critical spatial upper bound at the chosen order $p$, not all lower orders. The normalization and finite-cutoff assumptions are explicit; no claim about sharpness, the location of the critical parameter or the matching full two-point function is inferred.</p>


## The two-point upper bound across the susceptibility scale {#section-two-point-upper}

<a id="tag-TFKR" data-assertion="proposition" data-title="Uniform spatial tails give the two-point crossover upper bound"></a>
<p>Let $d\geq1$, $0&lt;\alpha\leq d$ and $b&gt;0$. For $0\leq\beta\leq b$, suppose translation-invariant cutoff laws increase with radius $r\geq1$ to their full laws and are dominated by the laws at $b$. Write $\tau_{\beta,r}$ for their two-point functions, $\chi_{\beta,r}&lt;\infty$ for their susceptibilities, $X_\beta=\chi(\beta)\in[1,\infty]$ and $\xi_\beta=X_\beta^{1/\alpha}$. Suppose the critical cutoff estimate</p>
<div class="math-display">$$\tau_{b,r}(x,y)\leq C R^{-d+\alpha}h(R/r),\qquad R=\|x-y\|_\infty\geq1,$$</div>
<p>holds with the function $h$ of <a href="/tag/AUAE/">AUAE</a>. Suppose for some fixed real $p&gt;d+\alpha$, uniformly in $\beta,r$ and $L\geq1$,</p>
<div class="math-display">$$\sum_{\|z\|_\infty&gt;Lr}\tau_{\beta,r}(0,z)\leq C_pL^{-p}\chi_{\beta,r}.$$</div>
<p>Finally assume local absolute continuity in radius and the almost-everywhere bound</p>
<div class="math-display">$$0\leq\partial_r\tau_{\beta,r}(x,y)\leq A r^{-d-\alpha-1}
\sum_{\|a-b'\|_\infty\leq r}\tau_{\beta,r}(x,a)\tau_{\beta,r}(b',y).$$</div>
<p>Then a constant independent of $\beta,x,y$ gives</p>
<div class="math-display">$$\tau_{\beta,\infty}(x,y)\leq C'R^{-d+\alpha}(1\vee R/\xi_\beta)^{-2\alpha},$$</div>
<p>with $R/\infty=0$. The spatial-tail input follows from <a href="/tag/KA3B/">KA3B</a> at the chosen order; the derivative and critical cutoff inputs are stated separately.</p>
<p><em>Proof.</em> Monotone cutoff convergence gives $\tau_{\beta,\infty}(x,y)\leq CR^{-d+\alpha}$. This proves the assertion when $X_\beta=\infty$ or $R\leq8\xi_\beta$, after adjusting the constant. Assume $X_\beta&lt;\infty$ and $R&gt;8\xi_\beta$, and abbreviate $X=X_\beta$, $\xi=\xi_\beta$.</p>
<p>For $r\leq R/8$, a contributing pair satisfies $\|x-a\|_\infty&gt;R/4$ or $\|y-b'\|_\infty&gt;R/4$, by the triangle inequality along $x,a,b',y$. Apply the tail bound to the corresponding two-point factor and sum the other one. Since $\chi_{\beta,r}\leq X$,</p>
<div class="math-display">$$\partial_r\tau_{\beta,r}(x,y)\leq C X^2R^{-p}r^{p-d-\alpha-1}.$$</div>
<p>Integrating from $\xi\geq1$ to $R/8$ gives an upper bound $CX^2R^{-d-\alpha}$ because $p&gt;d+\alpha$. For $r\geq R/8$, discard the displacement constraint and integrate $Ar^{-d-\alpha-1}X^2$ to infinity. This gives the same bound. Both are upper estimates; the first integral need not be comparable from below to its upper-endpoint power when its endpoints approach one another.</p>
<p>The remaining initial value satisfies</p>
<div class="math-display">$$\tau_{\beta,\xi}(x,y)\leq CR^{-d+\alpha}h(R/\xi)
\leq C R^{-d+\alpha}(R/\xi)^{-2\alpha}=CX^2R^{-d-\alpha}.$$</div>
<p>Add these three bounds. The integration takes place only in the range $R&gt;8\xi$; the bounded-ratio case was already covered. This proves the crossover estimate, including the infinite-susceptibility convention. The <a href="/errata/hutchcroft-lrp-2/#two-point-upper-integration">provisional source entry</a> records the endpoint and factor-index repairs to Lemma II.6.3.</p>

## A joining edge gives the matching lower bound {#section-two-point-lower}

<a id="tag-NI07" data-assertion="theorem" data-title="Separated cutoff clusters give the two-point crossover lower bound"></a>
<p>Fix $d\geq1$, $0&lt;\alpha\leq d$ and $0&lt;\beta_0\leq b&lt;\infty$. Let $J(z)=J(-z)$ be finite and nonnegative off zero, with</p>
<div class="math-display">$$c_J\|z\|_\infty^{-d-\alpha}\leq J(z)\leq C_J\|z\|_\infty^{-d-\alpha}\quad(z\ne0),\qquad c_J&gt;0.$$</div>
<p>For each $r\geq1$, let the symmetric displacement kernel $J_r\leq J$ vanish outside $B_r$. Use independent bonds of intensity $\beta J_r$ for the cutoff and $\beta J$ for the full model. Put $\xi_\beta=\chi(\beta)^{1/\alpha}\in[1,\infty]$. Assume the following bounds with constants independent of $\beta\in[\beta_0,b]$ and $r$:</p>
<div class="math-display">$$\mathbb E_{\beta,r}|K_0\cap B_r|\geq c_1r^\alpha\quad(1\leq r\leq\xi_\beta),\qquad
\mathbb E_{b,r}|K_0\cap B_r|^2\leq C_2r^{(d+3\alpha)/2}.$$</div>
<p>Also assume the critical cutoff laws at $b$ satisfy the two-point and four-point hypotheses of <a href="/tag/9ZEL/">9ZEL</a>. Then, uniformly over distinct $x,y$ and $\beta\in[\beta_0,b]$,</p>
<div class="math-display">$$\tau_{\beta,\infty}(x,y)\geq cR^{-d+\alpha}(1\vee R/\xi_\beta)^{-2\alpha},\qquad R=\|x-y\|_\infty.$$</div>
<p><em>Proof.</em> Write $\omega$ as the union of an intensity-$\beta J_r$ configuration and an independent intensity-$\beta(J-J_r)$ configuration. Fix for now $1\leq r\leq\min(R/4,\xi_\beta)$, put $U=|K_x\cap B_r(x)|$, $V=|K_y\cap B_r(y)|$, and let $Z$ count added open pairs joining these two cutoff traces. Their lengths lie between $R/2$ and $3R/2$, hence exceed $r$. Their added opening probabilities are therefore their full opening probabilities, uniformly comparable to $R^{-d-\alpha}$.</p>
<p>Conditioning on the cutoff configuration and using Harris for $U,V$ gives</p>
<div class="math-display">$$\mathbb E Z\geq cR^{-d-\alpha}\mathbb E(UV)
\geq cR^{-d-\alpha}(\mathbb E_{\beta,r}|K_0\cap B_r|)^2
\geq c r^{2\alpha}R^{-d-\alpha}.$$</div>
<p>Let $A=\{x\leftrightarrow y\text{ in the cutoff}\}$. The variable $UV\mathbf1_A$ is increasing, so critical domination and 9ZEL give</p>
<div class="math-display">$$\mathbb E[Z\mathbf1_A]\leq CR^{-d-\alpha}\mathbb E(UV\mathbf1_A)
\leq C R^{-d-\alpha}r^{d+\alpha}R^{-d+\alpha}H(R/r).$$</div>
<p>Relative to $r^{2\alpha}R^{-d-\alpha}$, the last expression is at most $C(r/R)^{d-\alpha}H(R/r)$. Choose a fixed $\varepsilon\in(0,1/4]$ sufficiently small, and take $r=\varepsilon\min(R,\xi_\beta)$ whenever this is at least one. Since $\alpha\leq d$, the last ratio is uniformly small. For $Y=Z\mathbf1_{A^c}$ and $m_*=r^{2\alpha}R^{-d-\alpha}$, it follows that $\mathbb E Y\geq c m_*$.</p>
<p>On $A^c$ the two cutoff clusters are disjoint. Expanding their squared window masses and applying BK to the two rooted connection events yields</p>
<div class="math-display">$$\mathbb E(U^2V^2\mathbf1_{A^c})\leq
\mathbb E U^2\,\mathbb E V^2\leq C r^{d+3\alpha}.$$</div>
<p>Repeated vertices in either squared mass cause no difficulty: the associated root-to-itself path may be empty. Distinct joining pairs correspond to distinct unordered bonds because the windows are disjoint. Their added states are independent, even if they share an endpoint. Thus</p>
<div class="math-display">$$\mathbb E[Z(Z-1)\mathbf1_{A^c}]
\leq CR^{-2d-2\alpha}r^{d+3\alpha}
=C m_*(r/R)^{d+\alpha}\leq C m_*.$$</div>
<p>Consequently $\mathbb E Y^2\leq\mathbb E Y+C m_*\leq C'\mathbb E Y$. Cauchy–Schwarz now gives $\mathbb P(Y&gt;0)\geq(\mathbb E Y)^2/\mathbb E Y^2\geq c m_*$. One joining pair suffices to connect $x$ and $y$ in the full model, and the chosen radius makes $m_*$ a constant multiple of the claimed crossover expression.</p>
<p>It remains to cover $\varepsilon\min(R,\xi_\beta)&lt;1$. The direct bond has probability at least $cR^{-d-\alpha}$, uniformly in $\beta\geq\beta_0$, by the lower bound on $J$. The desired expression is $R^{-d-\alpha}\min(R,\xi_\beta)^{2\alpha}\leq\varepsilon^{-2\alpha}R^{-d-\alpha}$, so this direct-bond bound suffices. This includes small susceptibility scales even when $R$ is large.</p>
<p>The lower local mean is supplied by <a href="/tag/KA3B/">KA3B</a> under its assumptions. The window second-moment upper bound is the $p=2$ case of <a href="/tag/AS7A/">AS7A</a> under its full-law quantile inputs. Together with the four-point input and TFKR, these give a conditional route to the matching estimate in Theorem II.1.14; they do not identify the models satisfying every premise. The proof does not require a lower estimate on the cutoff two-point function. The <a href="/errata/hutchcroft-lrp-2/#two-point-joining-windows">source entry</a> distinguishes this direct use of 9ZEL from the stronger intermediate comparison printed after (II.6.3).</p>


## A proved pointwise upper input {#section-pointwise-input}

<p>The previously cited upper bound used in YUHF now has a <a href="/tag/TGF9/">written proof</a> for globally comparable power kernels with $0&lt;\alpha&lt;\min\{1,d\}$. The proof averages translated boxes and contracts the short-edge contribution across scales, using MRZO's spatial average but no localization assumption. By monotone domination it supplies the upper bound for each finite-range cutoff in YUHF. The separate susceptibility lower bound is still required to deduce (CL); this update does not assert a pointwise lower theorem or discharge every later moment/localization premise.</p>
