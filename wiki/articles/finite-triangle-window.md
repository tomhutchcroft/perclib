---
{
  "id": "finite-triangle-window",
  "title": "The finite triangle window",
  "subtitle": "Susceptibility, root tails and the largest component",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The finite triangle condition gives a square-root cluster tail up to the susceptibility scale. A variance bound and positive-field extrapolation then give the largest-component scale throughout a bounded critical window.",
  "context": [
    "Independent bond percolation on a finite connected simple vertex-transitive graph of degree $m$ and order $N$.",
    "The reference parameter is defined by $\\chi(p_c)=\\lambda N^{1/3}$; it is not an infinite-volume threshold.",
    "Window displacements are normalized as $m(p-p_c)$."
  ],
  "related": [
    "finite-graph-criticality",
    "green-free-triangle",
    "cluster-partitions",
    "hypercube-critical-parameter"
  ],
  "sourceIds": [
    "borgs-chayes-finite-window",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "finite triangle condition",
    "finite critical window",
    "lower cluster tail",
    "susceptibility normalization"
  ],
  "prototypeUses": []
}
---

## Susceptibility and the parameter scale {#section-susceptibility}

<p>Write $T_p(x,y)=\mathbb P_p(x\leftrightarrow y)$, $\chi(p)=\sum_yT_p(o,y)$ and $L_1=\max_x|C_x|$. Matrix powers below are sums over the finite vertex set. Fix $p_c\in(0,1)$, put $H=\chi(p_c)$, and suppose</p>
<div class="math-display">$$T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+a\qquad(x,y\in V).$$</div>
<p>The proofs retain the finite value $H$. In particular, the lower root tail stops at a constant times $H^2$.</p>

<a id="tag-F5Y5" data-assertion="theorem" data-title="Finite susceptibility bounds with the degree-normalized parameter"></a>
<p>If $a<1$, then for $0\le p\le p_c$, with $\varepsilon=m(p_c-p)$,</p>
<div class="math-display">$$\frac1{H^{-1}+\varepsilon}\le\chi(p)\le\frac1{H^{-1}+(1-a)\varepsilon}.$$</div>
<p>Consequently $1-H^{-1}\le mp_c\le(1-H^{-1})/(1-a)$. If instead $p=p_c(1-\delta)$, both occurrences of $\varepsilon$ must be replaced by $mp_c\delta$.</p>
<p><em>Proof.</em> Finite Russo and BK give $\chi'(p)\le m\chi(p)^2$. Indeed, if an oriented edge $(u,v)$ is pivotal for $o\leftrightarrow z$, its closed-edge configuration contains disjoint paths $o\leftrightarrow u$ and $v\leftrightarrow z$, neither using that edge. Their probability is at most $T_p(o,u)T_p(v,z)$ by BK; summing over $z$ and the oriented edges gives the bound.</p>
<p>For the other direction let $Q(x,z;y,w)=\mathbb P_p(x\leftrightarrow z,\ y\leftrightarrow w,\ x\not\leftrightarrow y)$. Average the exact closed-pivotal identity over the root:</p>
<div class="math-display">$$(1-p)\chi'(p)=\frac1N\sum_{(x,y):\,x\sim y}\sum_{z,w}Q(x,z;y,w).$$</div>
<p>Use the <a href="/tag/J1LW/">five-factor deletion bound</a>. The independent-product term sums to $m\chi^2$, while the error, after the two terminal sums, is</p>
<div class="math-display">$$\frac{\chi^2}{N}\sum_{(x,y):\,x\sim y}T_p^3(x,y)\le ma\chi^2.$$</div>
<p>Thus $\chi'\ge m(1-a)\chi^2/(1-p)\ge m(1-a)\chi^2$ on $[0,p_c]$. All sums are finite, and transitivity gives the common terminal row sum $\chi$; no group structure is needed. Integrating $m(1-a)\le-\partial_p(1/\chi)\le m$ from $p$ to $p_c$ proves the bounds. Taking $p=0$, where $\chi=1$, gives the estimate for $mp_c$.</p>

<a id="tag-QPI1" data-assertion="proposition" data-title="The relative displacement cannot replace the additive displacement in the finite susceptibility bound"></a>
<p>The susceptibility upper bound in Exercise 13.6 of the checked 2017 manuscript is false with its stated relative parameter. On the four-cycle $T_{4,1}$ take $p_c=1/100$ and $a=1/10$. Then</p>
<div class="math-display">$$H=1+2p_c+2p_c^2+2p_c^3-3p_c^4=\frac{102020197}{10^8},\qquad T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+\frac1{10},$$</div>
<p>but at $p=0$, hence relative displacement $\delta=1$,</p>
<div class="math-display">$$\chi(0)=1>\frac1{H^{-1}+9/10}.$$</div>
<p><em>Proof.</em> The two routes to an adjacent vertex have lengths one and three, and those to the opposite vertex both have length two. Inclusion–exclusion gives the displayed $H$. The row sum of $T^3$ is $H^3$, and its diagonal is at least one. Every entry of $T^3-I$ is therefore nonnegative and at most $H^3-1<1/10$. Finally $H<10$ implies $H^{-1}+9/10>1$. Choosing $\lambda=H/4^{1/3}$ makes this $p_c$ exactly the source's susceptibility-defined parameter.</p>
<p>The repair is to use $m(p_c-p)$, as in the original finite-graph paper, or to insert $mp_c$ beside the relative displacement. This is a <a href="/errata/heydenreich-hofstad/#finite-window-parameter-normalization">provisional statement-level correction</a>; the powers of the volume in the window are unchanged.</p>

## The field bounds at a finite reference level {#section-field}

<p>Give each vertex an independent green mark with probability $\gamma$, and let $M(p,\gamma)=\mathbb E_p[1-(1-\gamma)^{|C_o|}]$.</p>
<a id="tag-KQN9" data-assertion="theorem" data-title="Uniform finite-graph field bounds below a small-triangle reference parameter"></a>
<p>Suppose $a\le1/100$ and $H\ge100$. For all $0\le p\le p_c$ and $0\le\gamma\le1$,</p>
<div class="math-display">$$\frac13\min\{\sqrt\gamma,\gamma\chi(p)\}\le M(p,\gamma)\le\min\{\sqrt{48\gamma},\gamma\chi(p)\}.$$</div>
<p><em>Proof.</em> The finite-graph part of <a href="/tag/G192/">G192</a> uses only transitivity and the degree. It gives</p>
<div class="math-display">$$(1-p)M_p\le m(1-\gamma)MM_\gamma,\qquad M\le\gamma M_\gamma+M^2+pMM_p.$$</div>
<p>Here all derivatives are polynomial derivatives. The first formula conditions on the green-free root cluster; the second partitions a green connection according to whether there is one mark, two disjoint marked paths, or a last pivotal bond. Thus both formulas apply on the present graph, with $m$ in place of $2d$. The inverse-field calculation <a href="/tag/ZDVK/">ZDVK</a>, now based at $M(p,0)=0$ and $M_\gamma(p,0)=\chi(p)$, gives</p>
<div class="math-display">$$M\ge\frac{\sqrt{\chi^{-2}+4K\gamma}-\chi^{-1}}{2K},\qquad K=1+\frac{mp}{1-p}.$$</div>
<p>An edge has $p_c\le T_{p_c}(x,y)\le T_{p_c}^3(x,y)\le a$. The preceding susceptibility bound gives $99/100\le mp_c\le100/99$, so $K\le1+(100/99)^2<3$. Rationalizing the square root shows that the last display is at least $(\sqrt{1+4K}-1)/(2K)$ times $\min\{\sqrt\gamma,\gamma\chi\}$, and this coefficient is greater than $1/3$ for $K\le3$.</p>
<p>For the upper bound apply the cutting-bond proof of <a href="/tag/OB0K/">OB0K</a> at $p_c$. Its finite version is</p>
<div class="math-display">$$M\ge\kappa(1-\gamma)M^2M_\gamma,\quad
\kappa=mp_c\left[\binom m2p_c^2(1-p_c)^{m-2}\{(1-a)^2-a\}-p_c-a\right].$$</div>
<p>To check its scope, condition on the cluster beyond the last pivotal bond. Forcing two distinct root bonds gives a double-green probability at least $\binom m2p_c^2(1-p_c)^{m-2}M^2\{(1-a)^2-a\}$. Deleting the root costs at most $aM$ on each arm, and the intersection loss is at most $aM^2$ by the three-point tree bound. Closing the pivotal bond costs at most $p_cM^2$. The remaining cluster-deletion error is bounded exactly as in OB0K by $p_cM^2\chi_\gamma W$, where $\chi_\gamma=(1-\gamma)M_\gamma$ and</p>
<div class="math-display">$$W=\sum_{(u,v):\,u\sim v}\sum_w T_{p_c}(y,u)T_{p_c}(v,w)T_{p_c}(y,w)
=\frac1N\sum_{(u,v):\,u\sim v}T_{p_c}^3(u,v)\le ma.$$</div>
<p>The first sum is independent of $y$ by transitivity; averaging over $y$ gives the equality. This replaces the lattice convolution in the original proof. The green-free BK step and all cluster exposures are finite, so no limiting hypothesis is needed.</p>
<p>Write $r=mp_c$. Since $p_c\le1/100$ and $r\ge99/100$, we have $m\ge99$, $\binom m2p_c^2\ge12/25$, $(1-p_c)^{m-2}\ge\exp[-r/(1-p_c)]\ge1/4$, and $(1-a)^2-a\ge97/100$. These bounds give $\kappa\ge1/12$. Divide by $M>0$ and integrate from field zero:</p>
<div class="math-display">$$M(p_c,\gamma)^2\le24\log\frac1{1-\gamma}\le48\gamma\qquad(0\le\gamma\le1/2).$$</div>
<p>For larger fields use $M\le1$. Monotonicity in $p$ extends this bound below $p_c$. Finally $1-(1-\gamma)^n\le n\gamma$ gives $M\le\gamma\chi$, and continuity supplies every endpoint.</p>

## The lower root tail {#section-root-tail}

<a id="tag-1ZWD" data-assertion="theorem" data-title="A square-root root-cluster tail up to the finite susceptibility scale"></a>
<p>Under the same assumptions, for $0\le p\le p_c$ and every integer $k\ge1$,</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\le\frac{12}{\sqrt k}.$$</div>
<p>If also $k\le\chi(p)^2/40000$, then</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\ge\frac1{1000\sqrt k}.$$</div>
<p><em>Proof.</em> On $|C_o|\ge k$, the field $1/k$ marks the cluster with probability at least $1-e^{-1}$. The field upper bound therefore gives the first assertion. For the lower bound, split the defining expectation at $|C_o|<k$. For $0<\gamma\le\widetilde\gamma\le1$, the elementary inequalities $1-(1-\gamma)^n\le\gamma n$ and $\widetilde\gamma n\le e^{\widetilde\gamma n}[1-(1-\widetilde\gamma)^n]$ give</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\ge M(p,\gamma)-\frac\gamma{\widetilde\gamma}e^{\widetilde\gamma k}M(p,\widetilde\gamma).$$</div>
<p>Take $\widetilde\gamma=1/k$ and $\gamma=1/(40000k)$. The cutoff hypothesis ensures $\gamma\ge\chi^{-2}$, so the right side is at least</p>
<div class="math-display">$$\frac1{\sqrt k}\left(\frac1{600}-\frac{e\sqrt{48}}{40000}\right)\ge\frac1{1000\sqrt k}.$$</div>
<p>For the last inequality it suffices that $e\sqrt{48}<20$. This calculation is the finite-mean version of <a href="/tag/ZK0V/">ZK0V</a>; it does not extend the lower bound beyond the stated cutoff.</p>

## From root clusters to a large component {#section-component}

<a id="tag-EPK3" data-assertion="corollary" data-title="A second-moment lower bound for the largest component below the reference parameter"></a>
<p>If $p\le p_c$ and $1\le k\le\chi(p)^2/40000$ is an integer, then</p>
<div class="math-display">$$\mathbb P_p(L_1\ge k)\ge\frac1{1+10^6k\chi(p)/N}.$$</div>
<p><em>Proof.</em> Put $Z_k=\sum_x\mathbf1_{\{|C_x|\ge k\}}$. Its mean is at least $N/(1000\sqrt k)$. The cluster-covariance bound <a href="/tag/25Z4/">25Z4</a> gives $\operatorname{Var}Z_k\le N\chi(p)$. Cauchy–Schwarz applied to $Z_k\mathbf1_{\{Z_k>0\}}$ yields $\mathbb P(Z_k>0)\ge(\mathbb EZ_k)^2/\mathbb EZ_k^2$. Substitute the two estimates and use $\{Z_k>0\}=\{L_1\ge k\}$.</p>

## Passing above the reference parameter {#section-extrapolation}

<a id="tag-1T2M" data-assertion="theorem" data-title="Positive-field extrapolation gives an upper root tail above the finite reference parameter"></a>
<p>For $p_c\le p\le b\le1/2$ and every integer $k\ge1$,</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\le\frac{20}{\sqrt k}+192m(p-p_c).$$</div>
<p><em>Proof.</em> Set $F(p,h)=M(p,1-e^{-h})$ and $L=m/(1-b)$. The finite differential inequality above gives $F_p\le LFF_h$. For each fixed level $s\in(0,1)$, $F$ has a positive inverse $h=H_p(s)$: the graph is finite, $F(p,0)=0$, and $F_h>0$. Implicit differentiation gives $\partial_pH_p(s)\ge-Ls$. At $s=F(p,h)$ this implies $H_{p_c}(s)\le h+L(p-p_c)s$. The field upper bound at $p_c$ now yields</p>
<div class="math-display">$$s^2\le48[h+L(p-p_c)s],\qquad s\le\sqrt{48h}+48L(p-p_c).$$</div>
<p>For $k\ge2$ take $\gamma=1/k$, so $h=-\log(1-1/k)\le2/k$, and divide by $1-e^{-1}$. Since $(1-e^{-1})^{-1}<2$, $2\sqrt{96}<20$ and $L\le2m$, the stated constants follow. For $k=1$ the bound is immediate. Only the triangle condition at $p_c$ was used; no triangle estimate above it is assumed.</p>

## The component scale throughout a bounded window {#section-window}

<a id="tag-CBIL" data-assertion="theorem" data-title="Largest-component tightness in the degree-normalized finite triangle window"></a>
<p>Fix $\lambda>0$ and $\Lambda\ge0$. Suppose $H=\lambda N^{1/3}$, $a\le1/100$, $H\ge100$, and</p>
<div class="math-display">$$p_-=p_c-\frac{\Lambda}{mN^{1/3}}\ge0,\qquad p_+=p_c+\frac{\Lambda}{mN^{1/3}}\le\frac12.$$</div>
<p>There is a constant $C=C(\lambda,\Lambda)$ such that, for all $p\in[p_-,p_+]$ and all $A>0$,</p>
<div class="math-display">$$\mathbb P_p\!\left(A^{-1}N^{2/3}\le L_1\le AN^{2/3}\right)\ge1-\frac CA.$$</div>
<p>Also, writing $c=(\lambda^{-1}+\Lambda)^{-1}$, the following bounds hold, with integer $k$ in the second one:</p>
<div class="math-display">$$cN^{1/3}\le\chi(p)\le\lambda N^{1/3}\quad(p_-\le p\le p_c),\qquad
\mathbb P_p(|C_o|\ge k)\ge\frac1{1000\sqrt k}\quad\left(1\le k\le\frac{c^2N^{2/3}}{40000},\ p_-\le p\le p_+\right).$$</div>
<p><em>Proof.</em> The susceptibility bounds give $cN^{1/3}\le\chi(p_-)\le\lambda N^{1/3}$. The root lower bound at $p_-$ therefore has the asserted range; coupling extends it to the whole window.</p>
<p>For the lower component bound it again suffices to work at $p_-$. If $N^{2/3}/A\le1$, failure is impossible. Otherwise put $k=\lceil N^{2/3}/A\rceil\le2N^{2/3}/A$. For $A\ge80000/c^2$ this lies below $\chi(p_-)^2/40000$. Chebyshev and the same $Z_k$ as above give</p>
<div class="math-display">$$\mathbb P_{p_-}(L_1<k)\le\frac{\operatorname{Var}Z_k}{(\mathbb EZ_k)^2}\le\frac{10^6k\chi(p_-)}N\le\frac{2\cdot10^6\lambda}{A}.$$</div>
<p>For smaller $A$ enlarge the constant so that the claimed lower probability is nonpositive. This also handles every rounding case.</p>
<p>For the upper bound put $k=\lfloor AN^{2/3}\rfloor+1$. A component of size at least $k$ contributes at least $k$ to $Z_k$, hence</p>
<div class="math-display">$$\mathbb P_p(L_1>AN^{2/3})\le\frac Nk\mathbb P_p(|C_o|\ge k)\le\frac{20}{A^{3/2}}+\frac{192\Lambda}{A}.$$</div>
<p>Below $p_c$ use the root upper bound with constant 12, and above it use extrapolation. Combine the two failure bounds for $A\ge1$; for $A<1$ take $C\ge1$. For example $C=80000/c^2+2\cdot10^6\lambda+20+192\Lambda+1$ suffices.</p>
<p>The susceptibility upper bound stated here is only for $p\le p_c$. A matching susceptibility bound throughout the positive half of the window requires an additional argument; neither component tightness in probability nor the displayed root tail alone supplies its expectation. Off-window giant components, ordered-component limits and the joint scaling limit also remain separate.</p>

<p>The <a href="/tag/X0R0/">complete-graph logarithmic law</a> now complements the general below-window bounds: if $p=(1-\varepsilon)/N$, $\varepsilon\to0$ and $N\varepsilon^3\to\infty$, each fixed-rank component of $G(N,p)$ has size asymptotic to $2\varepsilon^{-2}\log(N\varepsilon^3)$ in probability and mean absolute normalized error. Exact tree-component enumeration supplies the lower bound; it does not close the logarithmic gap for other finite transitive hosts.</p>

<p>For the barely subcritical complete graph, the <a href="/tag/CJ8R/">fixed-rank fluctuation law</a> refines the logarithmic leading size. With $I=-\varepsilon-\log(1-\varepsilon)$ and $B=\log(NI^{3/2}/[(1-\varepsilon)\sqrt{2\pi}])$, the variable $IL_1-B+\tfrac52\log B$ converges to the standard Gumbel law. Exact tree counts give Poisson exceedances, and separate cycle estimates show that cyclic components do not affect this limit. This uses the complete graph and the full regime $\varepsilon\to0$, $N\varepsilon^3\to\infty$.</p>

<p>The complete-graph fluctuation law also has <a href="/tag/OL4S/">convergence of centered moments</a>. Exact-rate Poisson exploration bounds and a tree-count lower tail give, for each fixed rank $r$, $\mathbb EL_r=[B-\tfrac52\log B+\gamma-H_{r-1}+o(1)]/I$, with the same expansion for tree components. The error here is $o(I^{-1})$; the exact $I=-\varepsilon-\log(1-\varepsilon)$ is retained throughout the barely subcritical regime.</p>

<p>Above the complete-graph window, the <a href="/tag/2KT9/">exploration argument</a> proves a unique giant with $L_1\sim2\varepsilon N$ when $p=(1+\varepsilon)/N$, $\varepsilon\to0$ and $N\varepsilon^3\to\infty$. Every fixed rank after the giant has size asymptotic to $2\varepsilon^{-2}\log(N\varepsilon^3)$ in probability. The <a href="/tag/U6EN/">mean-size argument</a> also gives $\mathbb EL_1\sim2\varepsilon N$ and $\mathbb EL_2=o(\varepsilon N)$. The remaining graph is handled with its conditioning made explicit; these are complete-graph conclusions, not a general-host giant theorem.</p>

<p>For a different geometric regime, <a href="/tag/NVCH/">short-path sprinkling</a> turns large-cluster mass into a giant on bounded-degree expanders. The <a href="/tag/YTZU/">locally tree-like expander theorem</a> identifies its density with the regular-tree survival probability at every fixed parameter and makes the second-largest component sublinear. Its uniform expansion and local-limit hypotheses are separate from the finite-triangle assumptions above; it does not establish the near-critical hypercube or torus giant.</p>

<p>The expander comparison now also has <a href="/tag/UPQ2/">exponential fixed-parameter deviation bounds</a> and the <a href="/tag/VSGH/">giant's degree, edge and cycle-excess densities</a>. Its <a href="/tag/OH6B/">empirical local law</a> is percolation on the regular tree conditioned to survive. The cubic excess expansion concerns these fixed-parameter limiting densities, with the graph-size limit taken first.</p>

<p>For the fixed-parameter expander regime, the <a href="/tag/TGLZ/">2-core argument</a> reserves blue edges as cycle witnesses and sprinkles only red edges. It proves the giant core's edge density, a local two-sided approximation, and negligible total size of the other cores. The <a href="/tag/2K74/">core degree profile</a> gives its vertex density and quadratic near-threshold expansion, with the graph-size limit taken first.</p>


<p>For the fixed-parameter regular-expander class, the <a href="/tag/P3AV/">vertex-deletion argument</a> now shows that deleting a sufficiently small proportion of vertices leaves all but any prescribed small proportion of the giant in one component. It rules out small balanced separators. A depth-first-search separator and a separate short-connector argument give <a href="/tag/8NPK/">cycles of linear length in the giant and its 2-core</a>, with exponentially small failure probability. These results retain fixed supercritical $p$ and do not resolve near-critical geometric sprinkling.</p>


## Gaussian complete-graph fluctuations above the window {#section-er-giant-fluctuations}

<p>The <a href="/articles/finite-supercritical-clusters/#section-er-giant-clt">complete-graph fluctuation theorem</a> now gives $(L_1-N\rho)/\sqrt{2N/\varepsilon}\Rightarrow\mathcal N(0,1)$ for $G(N,(1+\varepsilon)/N)$ throughout $\varepsilon\to0$, $N\varepsilon^3\to\infty$, where $1-\rho=e^{-(1+\varepsilon)\rho}$. The proof keeps the exact exploration trajectory and controls both endpoints of the giant excursion. The <a href="/tag/MEUA/">centering corollary</a> explains why replacing $N\rho$ by $2\varepsilon N$ requires the additional condition $N\varepsilon^5\to0$ for a centered limit. These are complete-graph distributional results; general-host sprinkling, joint critical-window limits and convergence of the centered moments remain separate.</p>


## Complete-graph component moments above the window {#section-er-component-moments}

<p>The <a href="/tag/DNIW/">complete-graph moment theorem</a> strengthens the barely supercritical benchmark to every fixed positive moment: $L_1/(2\varepsilon N)\to1$ and $L_r/[2\varepsilon^{-2}\log(N\varepsilon^3)]\to1$ in $q$th mean for every fixed $q>0$ and $r\ge2$. A global cubic-exponential upper tail controls rare large components; an exponentially likely giant-size event and the exact conditional law of its complement control the remaining ranks. In particular their means have the sharp logarithmic leading constant. This does not give a centered Gaussian moment theorem or a general-host logarithmic lower bound.</p>


## Joint complete-graph fluctuations outside the window {#section-er-joint-fluctuations}

<p>The <a href="/tag/K1HI/">joint ordered-size theorem</a> now identifies the Gaussian giant and every fixed vector of smaller extreme components in the barely supercritical complete graph. The giant fluctuation is independent of the limiting extreme-size vector, whose coordinates are negative logarithms of successive exponential arrival times. The exact rate is $I=\varepsilon-\log(1+\varepsilon)$, and the <a href="/tag/KU4Y/">rate-bias corollary</a> records the shift caused by replacing it by $\varepsilon^2/2$. The <a href="/tag/7W39/">subcritical joint-count theorem</a> supplies the corresponding independent Poisson interval counts below the window. These are outside-window distributional results; centered supercritical moments and joint critical-window laws remain separate.</p>


## Centered moments outside the window {#section-er-centered-fluctuation-moments}

<p>For the barely supercritical complete graph, <a href="/tag/LXGK/">LXGK</a> gives all centered Gaussian moments of the giant, including $\operatorname{Var}(L_1)\sim2N/\varepsilon$. <a href="/tag/NVPH/">NVPH</a> passes the joint giant/extreme-size law to every continuous function of polynomial growth, with the exact rate $I=\varepsilon-\log(1+\varepsilon)$. It yields $\mathbb E L_r=[D+\gamma-H_{r-2}+o(1)]/I$ for each fixed $r\ge2$. The <a href="/tag/M7A4/">covariance formula</a> describes the correlated extreme ranks and their vanishing scaled covariance with the giant. These strengthen the preceding outside-window distributional results; they do not settle joint critical-window laws or analogous near-critical results on geometric hosts.</p>


## A martingale limit on a growing time mesh {#section-critical-martingale-limit}

<p>The remaining sections specialize to the complete graph. The window parameter below is measured from $1/N$, not from a susceptibility-defined reference point. We first give the probability argument needed to pass from its exploration walk to a continuous limit.</p>

<a id="tag-R1RF" data-assertion="proposition" data-title="Uniform fourth moments and averaged conditional variances give a Brownian limit for a martingale array"></a>
<p>Let $b_N\to\infty$, and let $\Delta_{N,i}$ be martingale differences for $1\le i\le\lceil Tb_N\rceil$, for each fixed $T>0$. Write $v_{N,i}=\mathbb E(\Delta_{N,i}^2\mid\mathcal F_{N,i-1})$. Suppose that, for each $T$, there is a deterministic $K_T<\infty$ such that</p>
<div class="math-display">$$\mathbb E(\Delta_{N,i}^4\mid\mathcal F_{N,i-1})\le K_T,\qquad
\frac1{b_N}\sum_{i\le\lceil Tb_N\rceil}\mathbb E|v_{N,i}-1|\longrightarrow0.$$</div>
<p>The polygonal interpolation of $b_N^{-1/2}\sum_{i\le k}\Delta_{N,i}$ at times $k/b_N$ converges in distribution in $C([0,T])$, with the uniform norm, to standard Brownian motion.</p>
<p><em>Proof.</em> For bounded deterministic $u_i$, conditional Taylor expansion gives</p>
<div class="math-display">$$\mathbb E(e^{iu_i\Delta_{N,i}/\sqrt{b_N}}\mid\mathcal F_{N,i-1})
=1-\frac{u_i^2v_{N,i}}{2b_N}+R_{N,i},\qquad
\mathbb E|R_{N,i}|\le Cb_N^{-3/2}.$$</div>
<p>Compare these factors successively with $e^{-u_i^2/(2b_N)}$, which are deterministic and have modulus at most one. Conditioning at each step and telescoping bounds the error in the characteristic function of the weighted sum by</p>
<div class="math-display">$$\frac C{b_N}\sum_{i\le\lceil Tb_N\rceil}\mathbb E|v_{N,i}-1|+Cb_N^{-1/2}+Cb_N^{-1}\longrightarrow0.$$</div>
<p>Take $u_i$ constant on each of finitely many disjoint time intervals. The deterministic product tends to the characteristic function of independent centered normal increments with variances equal to the interval lengths. The Cramér–Wold argument gives the finite-dimensional distributions at grid approximations to any prescribed times.</p>
<p>For tightness, a block sum $S_h$ of $h$ consecutive differences has $\mathbb E S_h^2\le Ch$. Expanding $(S_{h-1}+\Delta)^4$, conditioning, and using the uniform conditional second, third and fourth moment bounds gives</p>
<div class="math-display">$$\mathbb E S_h^4\le\mathbb E S_{h-1}^4+C(h-1)+C\sqrt{h-1}+C,$$</div>
<p>so $\mathbb E S_h^4\le Ch^2$ for $h\ge1$, uniformly over the starting index in the time horizon. The same estimate holds with deterministic coefficients of absolute value at most one. For the interpolated process $\widehat M_N$, it follows that</p>
<div class="math-display">$$\mathbb E|\widehat M_N(t)-\widehat M_N(s)|^4\le C_T|t-s|^2\qquad(0\le s,t\le T).$$</div>
<p>If $|t-s|\ge b_N^{-1}$, use the block estimate and the two fractional endpoint increments. If $|t-s|<b_N^{-1}$, at most two increments occur, each with interpolation coefficient at most $b_N|t-s|$; their fourth moment after normalization is at most $Cb_N^2|t-s|^4\le C|t-s|^2$. The Kolmogorov tightness criterion now gives tightness in $C([0,T])$. The endpoint interpolation errors vanish by the same moment bound. Every subsequential limit has the Brownian finite-dimensional distributions, proving the claim. $\square$</p>

## The exploration drift inside the critical window {#section-critical-exploration-drift}

<p>Let $\lambda_N\to\lambda\in\mathbb R$ and</p>
<div class="math-display">$$p_N=\frac{1+\lambda_NN^{-1/3}}N,\qquad b_N=N^{2/3},\qquad c_N=N^{1/3}.$$</div>
<p>For sufficiently large $N$, $p_N\in(0,1)$. Explore $G(N,p_N)$ in breadth-first order, choosing the least undiscovered vertex whenever the active queue is empty. At step $i$, reveal only edges from the processed vertex to still undiscovered vertices. Let $A_i$ be the active queue size after that step, $\eta_i$ the number newly discovered, $C_i$ the number of roots chosen, and</p>
<div class="math-display">$$Y_k=\sum_{i=1}^k(\eta_i-1),\qquad
M_k=\sum_{i=1}^k\Delta_i,\qquad
\Delta_i=\eta_i-\mathbb E(\eta_i\mid\mathcal F_{i-1}).$$</div>
<p>All four processes start at zero. The exploration identities used above the window hold for every $p$:</p>
<div class="math-display">$$\begin{aligned}
\eta_i\mid\mathcal F_{i-1}&\sim\operatorname{Bin}\bigl(N-i+1-A_{i-1}-\mathbf1_{\{A_{i-1}=0\}},p_N\bigr),\\
A_k&=Y_k+C_k,\qquad
C_k=1-\min_{0\le j<k}Y_j\quad(k\ge1),\\
Y_k&=M_k+\lambda_NN^{-1/3}k-\frac{p_N}2k(k-1)
-p_N\sum_{i=1}^kA_{i-1}-p_NC_k .
\end{aligned}$$</div>
<p>The binomial parameter subtracts a newly selected root before its incident edges are tested. A completed component is a strict descending record of $Y$; the walk drops by exactly one below the preceding record. These observations prove the first two lines directly, and summing the conditional means proves the last.</p>

<a id="tag-FOTE" data-assertion="proposition" data-title="Critical complete-graph exploration has a uniformly negligible drift error and asymptotically unit conditional variance"></a>
<p>Fix $T>0$, put $H_N=\lceil Tb_N\rceil$, and linearly interpolate $\widehat Y_N(k/b_N)=Y_k/c_N$ and $\widehat M_N(k/b_N)=M_k/c_N$. There is a constant $K_T$, depending also on a bound for $|\lambda_N|$, such that for all sufficiently large $N$,</p>
<div class="math-display">$$\mathbb E\max_{k\le H_N}A_k^2\le K_TN^{2/3},\qquad
\mathbb E\sup_{0\le t\le T}\left|\widehat Y_N(t)-\widehat M_N(t)-\lambda_Nt+\frac{t^2}2\right|^2
\le K_TN^{-2/3},$$</div>
<div class="math-display">$$\frac1{b_N}\sum_{i\le H_N}\mathbb E|v_i-1|\le K_TN^{-1/3},
\qquad v_i=\mathbb E(\Delta_i^2\mid\mathcal F_{i-1}).$$</div>
<p><em>Proof.</em> Each offspring mean is at most $Np_N\le2$ eventually. Thus $v_i\le2$, and Doob's inequality gives $\mathbb E W^2\le8H_N$ for $W=\max_{k\le H_N}|M_k|$. If a component starts just after time $s$, then until it ends,</p>
<div class="math-display">$$A_k=1+Y_k-Y_s\le1+(\lambda_N)_+N^{-1/3}H_N+2W.$$</div>
<p>The same upper bound holds when the queue is empty. Its squared expectation is $O_T(N^{2/3})$, which proves the first estimate and handles negative window parameters as well.</p>
<p>Subtract the desired drift from the exact identity at grid times. The difference in the quadratic terms is bounded, before division by $c_N$, by</p>
<div class="math-display">$$\frac{|p_N-N^{-1}|H_N^2}2+\frac{p_NH_N}2.$$</div>
<p>The remaining two errors are bounded by $p_NH_N\max_{k\le H_N}A_k$ and $p_NH_N$, since $C_k\le k$. Each has bounded second moment before division by $c_N$: here $|p_N-N^{-1}|=O(N^{-4/3})$ and $p_NH_N=O_T(N^{-1/3})$. Linear interpolation preserves the bound; interpolating the quadratic function adds at most $1/(8b_N^2)$. This proves the second estimate.</p>
<p>With $n_i=N-i+1-A_{i-1}-\mathbf1_{\{A_{i-1}=0\}}$, we have $v_i=n_ip_N(1-p_N)$. Consequently</p>
<div class="math-display">$$\mathbb E|v_i-1|
\le|\lambda_N|N^{-1/3}+2p_N+p_N(i+\mathbb EA_{i-1})
\le K_TN^{-1/3}.$$</div>
<p>Summing proves the last estimate. For use in R1RF, the fourth central moment of a binomial variable of mean $\mu\le2$ is at most $\mu+3\mu^2\le14$; hence the required conditional fourth moments are uniformly bounded. $\square$</p>

## Brownian exploration and reflection {#section-critical-brownian-queue}

<a id="tag-CY46" data-assertion="theorem" data-title="The critical complete-graph exploration, active queue and root count converge jointly to Brownian motion with parabolic drift and its reflection"></a>
<p>Under the preceding assumptions, let $B$ be standard Brownian motion and define</p>
<div class="math-display">$$W_\lambda(t)=B(t)+\lambda t-\frac{t^2}2,\qquad
J_\lambda(t)=-\min_{0\le s\le t}W_\lambda(s),\qquad
R_\lambda(t)=W_\lambda(t)+J_\lambda(t).$$</div>
<p>Interpolate $\widehat A_N(k/b_N)=A_k/c_N$ and $\widehat C_N(k/b_N)=C_k/c_N$ linearly as well. For every fixed $T>0$,</p>
<div class="math-display">$$\bigl(\widehat Y_N,\widehat A_N,\widehat C_N\bigr)
\ \xrightarrow{\ d\ }\ (W_\lambda,R_\lambda,J_\lambda)
\qquad\text{in }C([0,T])^3.$$</div>
<p><em>Proof.</em> FOTE verifies every hypothesis of R1RF with $b_N=N^{2/3}$. Thus $\widehat M_N$ converges to $B$, and the drift error in FOTE gives $\widehat Y_N\Rightarrow W_\lambda$. The running-minimum map is Lipschitz in the uniform norm, and the reflection map $f\mapsto f-\min_{s\le\cdot}f(s)$ is Lipschitz with constant two.</p>
<p>At each grid time, the record identity gives</p>
<div class="math-display">$$0\le C_k+\min_{0\le j\le k}Y_j\le1.$$</div>
<p>If step $k$ sets a new record, its downward jump is exactly one and the left side is zero; otherwise it is one, apart from time zero. The interpolated minimum differs from the running minimum of the interpolated walk by at most the largest oscillation on a single mesh interval. After scaling this tends to zero in probability, since $\widehat Y_N$ is tight with continuous limits. Therefore $\widehat C_N+\min_{s\le\cdot}\widehat Y_N(s)$ tends uniformly to zero in probability. Use $\widehat A_N=\widehat Y_N+\widehat C_N$ and continuity of both maps to obtain the joint limit. $\square$</p>
<p>In particular, the integrated queue converges jointly with the walk:</p>
<div class="math-display">$$\frac1N\sum_{i\le\lfloor tb_N\rfloor}A_{i-1}
\ \xrightarrow{\ d\ }\ \int_0^tR_\lambda(s)\,ds\qquad(0\le t\le T),$$</div>
<p>uniformly in $t$. This follows from Riemann sums, since $b_Nc_N=N$ and the scaled queue has a continuous limit.</p>

## Surplus edges as marks under the queue {#section-critical-surplus-marks}

<p>Keep the edges joining two already active vertices unexposed during the exploration. Just before processing vertex $i$ in breadth-first order, the number of other active vertices is</p>
<div class="math-display">$$a_i=(A_{i-1}-1)_+.$$</div>
<p>When the queue is empty a new root has no other active vertex, so this formula covers restarts. Let $\zeta_i$ count the open edges from the processed vertex to these $a_i$ vertices. Each such edge is counted once. Within a completed component their total is its surplus, namely its edge count minus its vertex count plus one.</p>

<a id="tag-GGL3" data-assertion="theorem" data-title="Critical complete-graph surplus marks converge jointly with exploration to a Poisson point measure with reflected-Brownian intensity"></a>
<p>For fixed $T>0$, put</p>
<div class="math-display">$$\Pi_N=\sum_{i=1}^{\lfloor Tb_N\rfloor}\zeta_i\,\delta_{i/b_N}.$$</div>
<p>Jointly with CY46, $\Pi_N$ converges in distribution, in the weak topology of finite point measures on $[0,T]$, to $\Pi$. Conditional on the entire Brownian path on $[0,T]$, $\Pi$ is a Poisson point measure of intensity $R_\lambda(t)\,dt$. Equivalently, for every continuous $f\ge0$,</p>
<div class="math-display">$$\mathbb E\!\left[e^{-\int f\,d\Pi}\mid B\right]
=\exp\!\left[-\int_0^T(1-e^{-f(t)})R_\lambda(t)\,dt\right].$$</div>
<p>Thus counts on disjoint deterministic time intervals are conditionally independent Poisson variables with means given by the corresponding queue areas. These are counts in exploration time; ordering components by size requires a further excursion argument.</p>
<p><em>Proof.</em> Let $\mathcal H_N$ be the complete transcript of the exploration using only tests to undiscovered vertices. Its query choices depend only on answers already obtained. For each possible transcript the event specifying it fixes exactly the tested edge bits. Product independence therefore leaves all untested bits independent Bernoulli($p_N$), conditionally on that transcript. The candidate edge sets defining the $\zeta_i$ are disjoint and determined by it. Hence, conditionally on $\mathcal H_N$, the variables $\zeta_i$ are independent with laws $\operatorname{Bin}(a_i,p_N)$.</p>
<p>For $f\ge0$ as in the statement, this gives the exact formula</p>
<div class="math-display">$$\mathbb E\!\left[e^{-\int f\,d\Pi_N}\mid\mathcal H_N\right]
=\prod_{i\le\lfloor Tb_N\rfloor}\left[1-p_N(1-e^{-f(i/b_N)})\right]^{a_i}.$$</div>
<p>Its logarithm differs from $-p_N\sum_i a_i(1-e^{-f(i/b_N)})$ by at most $Cp_N^2\sum_i a_i$, for all large $N$. FOTE implies</p>
<div class="math-display">$$\mathbb E\left[p_N\sum_{i\le\lfloor Tb_N\rfloor}a_i\right]
\le p_NH_N\,\mathbb E\max_{k\le H_N}A_k=O_T(1).$$</div>
<p>Thus the logarithmic error tends to zero in $L^1$. Also $|a_i-A_{i-1}|\le1$, $Np_N\to1$, and CY46 and its queue-area consequence yield, jointly with the three exploration processes,</p>
<div class="math-display">$$p_N\sum_{i\le\lfloor Tb_N\rfloor}a_i(1-e^{-f(i/b_N)})
\ \xrightarrow{\ d\ }\ \int_0^T(1-e^{-f(t)})R_\lambda(t)\,dt.$$</div>
<p>Multiply the conditional Laplace formula by any bounded continuous function of the scaled exploration paths and take expectations. The preceding bounds and convergence give the claimed limiting conditional Laplace functional.</p>
<p>For completeness, the uniform first-moment bound on $\Pi_N([0,T])$ makes these point measures tight: on a compact interval, point measures with at most a fixed number of atoms form a compact set. Together with CY46 this gives joint tightness. The mixed Laplace functionals identify every subsequential joint limit uniquely, so the whole sequence converges. The limiting intensity has a continuous density and therefore no atoms at deterministic interval endpoints, which justifies the assertion about interval counts. $\square$</p>
<p>The source comparison is <a href="https://doi.org/10.1214/aop/1024404421">Aldous (1997), Theorem 3 and Section 2.2</a>. The proof here uses discrete conditional moments and an exact conditional binomial formula for the marks. Convergence of ranked component sizes and surpluses, including control of components encountered at arbitrarily late exploration times, remains to be established separately.</p>


## The excursions of the limiting walk {#section-critical-excursion-regularity}

<p>Keep $W_\lambda(t)=B(t)+\lambda t-t^2/2$, $I_\lambda(t)=\min_{s\le t}W_\lambda(s)$ and $R_\lambda=W_\lambda-I_\lambda$. An excursion is a connected component $(a,b)$ of $\{t:R_\lambda(t)>0\}$; its length is $b-a$. Before sorting these lengths, we need to know that the discrete record intervals really converge to them.</p>

<a id="tag-2N9T" data-assertion="proposition" data-title="Parabolically drifted Brownian motion has separated excursion levels and distinct positive excursion lengths"></a>
<p>Almost surely $W_\lambda(t)\to-\infty$, the zero set of $R_\lambda$ has Lebesgue measure zero, and every excursion has a finite right endpoint. At each excursion $(a,b)$,</p>
<div class="math-display">$$I_\lambda(b+\eta)<I_\lambda(b)\quad(\eta>0),\qquad
I_\lambda(a-\eta)>I_\lambda(a)\quad(0<\eta<a).$$</div>
<p>There are infinitely many excursions, their positive lengths are pairwise distinct, and for each fixed $d>0$ the probability that any excursion has length exactly $d$ is zero. For every deterministic $t>0$, $\mathbb P(R_\lambda(t)=0)=0$.</p>
<p><em>Proof.</em> On each bounded interval the law of $W_\lambda$ is mutually absolutely continuous with Brownian law: the added function has square-integrable derivative $\lambda-t$, so the Cameron–Martin theorem applies. For Brownian motion, time reversal identifies $B(t)-\min_{s\le t}B(s)$ in law with its maximum on $[0,t]$. The reflection principle shows that this maximum has no atom at zero. Absolute continuity and Fubini prove both the deterministic-time assertion and the zero-set assertion for $R_\lambda$.</p>
<p>For Brownian motion, the right endpoint of the excursion containing a fixed rational $q$ with positive reflected height is the first subsequent hitting time of the level $\min_{s\le q}B(s)$. It is a stopping time. By the strong Markov property, Brownian motion goes strictly below that level arbitrarily soon afterwards. Every excursion contains a rational, so this holds simultaneously at all right endpoints. Absolute continuity on bounded intervals transfers the assertion to $W_\lambda$.</p>
<p>The left-endpoint claim follows from this right-endpoint property and the null zero set. If the running minimum were constant on $[a-\eta,a]$, choose $q$ in that interval with $R_\lambda(q)>0$. Its excursion ends at some $d\le a$. If $d<a$, the running minimum drops before $a$, a contradiction. If $d=a$, the immediate drop after $d$ contradicts the positive excursion starting at $a$. This also shows that successive excursions start at strictly decreasing minimum levels.</p>
<p>To exclude equal lengths, take rational points $r<q$ in two different excursions, the first completed before $q$. At time $q$, its length $L$ and the left endpoint $a_q$ of the excursion containing $q$ are determined by the past. Equality of the two lengths would force</p>
<div class="math-display">$$W_\lambda(a_q+L)=I_\lambda(q),\qquad a_q+L>q.$$</div>
<p>Conditionally on the past at $q$, the time increment $a_q+L-q$ is fixed and positive, and the displayed future value has a Gaussian density. The event has conditional probability zero. A countable union over $r,q$ proves distinctness. Replacing $L$ by a fixed $d$ proves the fixed-length assertion.</p>
<p>Finally, Gaussian maximal bounds and Borel–Cantelli give $B(t)=o(t^2)$ almost surely. Hence $W_\lambda(t)\to-\infty$, so no excursion can continue forever. If there were only finitely many excursions, the reflected process would vanish on a terminal interval, contradicting its null zero set. $\square$</p>

## Matching record intervals to excursions {#section-critical-record-matching}

<a id="tag-59NH" data-assertion="proposition" data-title="Uniform convergence and small record drops match every macroscopic record interval to a limiting excursion"></a>
<p>Let $f_n,f$ be continuous functions on $[0,\infty)$, with $f_n\to f$ uniformly on bounded intervals and $f(t)\to-\infty$. Write $I(t)=\min_{s\le t}f(s)$. Suppose $\{f=I\}$ has Lebesgue measure zero, and after each right endpoint $b$ of an excursion of $f-I$ the running minimum immediately decreases: $I(b+\eta)<I(b)$ for all $\eta>0$.</p>
<p>For each $n$, let $0=t_{n,0}<t_{n,1}<\cdots\to\infty$ be a locally finite partition such that every endpoint is a running minimum of $f_n$ and</p>
<div class="math-display">$$0<f_n(t_{n,j})-f_n(t_{n,j+1})\le h_n,\qquad h_n\to0.$$</div>
<p>Fix $T,d>0$ such that no limiting excursion starts at $T$ or has length $d$. For all sufficiently large $n$, the intervals $(t_{n,j},t_{n,j+1})$ with left endpoint less than $T$ and length greater than $d$ are in bijection with the excursions $(a,b)$ of $f-I$ having $a<T$ and $b-a>d$. The endpoints of each matched interval converge to $a,b$.</p>
<p>If, in addition, locally finite point measures $\pi_n$ converge weakly on bounded intervals to $\pi$, and $\pi$ charges no limiting excursion endpoint, then the counts $\pi_n((t_{n,j},t_{n,j+1}])$ on these matched intervals converge to $\pi((a,b))$.</p>
<p><em>Proof.</em> First bound the right endpoints of intervals whose left endpoints are at most $T$. Choose $S>T$ with $f(S)<\min_{[0,T]}f-1$. If one of the discrete intervals starting before $T$ extended beyond $S$, the running-minimum property at its right endpoint would imply</p>
<div class="math-display">$$f_n(S)\ge f_n(t_{n,j+1})\ge f_n(t_{n,j})-h_n
\ge\min_{[0,T]}f_n-h_n,$$</div>
<p>contradicting uniform convergence. Thus all these right endpoints are bounded by $S$ eventually.</p>
<p>Consider any subsequence of intervals whose endpoints converge to $u<v$. Their endpoint levels differ by at most $h_n$, so $f(u)=f(v)=I(u)=I(v)$, and $f\ge f(u)$ throughout $[u,v]$. There cannot be a zero of $f-I$ at an interior point $z$. Otherwise choose a point of positive reflected height between $u$ and $z$, using the null zero set. The excursion containing it ends before or at $z$, and the immediate decrease after that endpoint contradicts $I(v)=I(u)$. Therefore $(u,v)$ is one limiting excursion.</p>
<p>Conversely, fix an excursion $(a,b)$ and a point $q\in(a,b)$. For large $n$ it lies inside one partition interval: an endpoint would have zero reflected height, whereas $f(q)-I(q)>0$. Uniform convergence and continuity keep both endpoints a positive distance from $q$. Their right endpoints are bounded by the first argument. Every subsequential endpoint limit must therefore be an excursion containing $q$, and hence must equal $(a,b)$. This proves convergence of its containing interval.</p>
<p>There are only finitely many limiting excursions of length greater than $d$ starting before $T$, since they are disjoint and have bounded endpoints. They give distinct matched intervals eventually. Any extra discrete interval would have a subsequential limit of positive length, hence would converge to an additional limiting excursion. The excluded boundary values $T,d$ rule out entering or leaving through a cutoff. This proves the bijection. Weak convergence of point measures gives the final assertion: convergent endpoints that carry no limiting atoms can be enclosed between arbitrarily close fixed endpoints, and the intervening limiting mass tends to zero. $\square$</p>
<p>For the exploration walk, the partition endpoints are completed-component times divided by $N^{2/3}$, and every drop is $h_N=N^{-1/3}$. After all vertices are processed, the path and partition may be continued by descending segments with this same drop; this does not affect any fixed time interval for large $N$. The preceding lemma therefore applies to CY46. The limit marks in GGL3 charge no excursion endpoint: conditionally on the Brownian path their intensity is absolutely continuous, and there are only countably many endpoints.</p>

## Components explored after a late time {#section-critical-late-components}

<p>Return to $p_N=(1+\lambda_NN^{-1/3})/N$, with $\lambda_N\to\lambda$. A component's exploration start is the number of vertices processed before its root is selected. For $T>0$, put $H_N=\lfloor TN^{2/3}\rfloor$ and let $\tau_N(T)$ be the first completed-component time at or after $H_N$, taking $\tau_N(T)=N$ if necessary.</p>

<a id="tag-CH8I" data-assertion="proposition" data-title="The unexplored critical random graph has a vanishing squared component-mass tail after late exploration times"></a>
<p>For fixed $T>\max\{\lambda,0\}$ and all sufficiently large $N$, conditionally on the history at $\tau_N(T)$,</p>
<div class="math-display">$$\mathbb E\!\left[\sum_{\mathcal C:\,\mathrm{start}(\mathcal C)\ge H_N}|\mathcal C|^2
\,\middle|\,\mathcal F_{\tau_N(T)}\right]
\le\frac{N-H_N}{1-(N-H_N)p_N}.$$</div>
<p>In particular,</p>
<div class="math-display">$$\limsup_{N\to\infty}\mathbb E\!\left[N^{-4/3}
\sum_{\mathcal C:\,\mathrm{start}(\mathcal C)\ge H_N}|\mathcal C|^2\right]
\le\frac1{T-\lambda}.$$</div>
<p>For each fixed $T>0$, $\tau_N(T)/N^{2/3}$ converges in distribution to the right endpoint of the excursion of $R_\lambda$ containing $T$, and is therefore tight.</p>
<p><em>Proof.</em> At $\tau_N(T)$ the queue is empty. Conditional on its stopped exploration history, the $M=N-\tau_N(T)$ undiscovered vertices induce an independent $G(M,p_N)$: none of their mutual edges has been tested. These are exactly the components whose exploration starts are at least $H_N$. If $M=0$ their contribution is zero. Otherwise a cluster exploration is dominated by a branching process with offspring $\operatorname{Bin}(M,p_N)$, whose expected total progeny is $1/(1-Mp_N)$ whenever $Mp_N<1$. One can realize the domination by adding independent unused trials at every exploration step to bring its number of trials up to $M$.</p>
<p>Summing expected rooted cluster sizes gives the expected sum of component squares, at most $M/(1-Mp_N)$. This expression increases with $M$ below $1/p_N$, and $M\le N-H_N$. The denominator is positive eventually because</p>
<div class="math-display">$$N^{1/3}\bigl[1-(N-H_N)p_N\bigr]
=\frac{H_N}{N^{2/3}}\bigl(1+\lambda_NN^{-1/3}\bigr)-\lambda_N
\longrightarrow T-\lambda>0.$$</div>
<p>This proves the conditional estimate and its normalized limit. The conditioning is only on the stopped history, not on a later event about the remaining component sizes.</p>
<p>For the completion time, use a representation of CY46 with uniform convergence on compact intervals. By 2N9T, a fixed $T>0$ lies strictly inside one limiting excursion almost surely. The containing record interval converges to that excursion by the proof of 59NH. Its right endpoint is $\tau_N(T)/N^{2/3}$ eventually; replacing $T$ by $H_N/N^{2/3}$ changes nothing, since both lie in a compact subinterval of the same limiting excursion. The finite limiting endpoint gives the asserted convergence and tightness. $\square$</p>

## Ranked critical components and their surpluses {#section-critical-ranked-components}

<p>Order the components of $G(N,p_N)$ by decreasing size, breaking ties by their least vertex label. Write $L_{N,j}$ for their sizes and $S_{N,j}$ for their surpluses, with zeros appended after the last component. Let $\ell^2_\downarrow$ denote the nonnegative decreasing square-summable sequences with their usual $\ell^2$ norm.</p>

<a id="tag-M7BY" data-assertion="theorem" data-title="Critical Erdős–Rényi component sizes converge in square-summable rank order jointly with their surplus counts"></a>
<p>For every sequence $\lambda_N\to\lambda\in\mathbb R$, at $p_N=(1+\lambda_NN^{-1/3})/N$,</p>
<div class="math-display">$$\left((N^{-2/3}L_{N,j})_{j\ge1},(S_{N,j})_{j\ge1}\right)
\ \xrightarrow{\ d\ }\
\left((\ell_j)_{j\ge1},(Z_j)_{j\ge1}\right)
\quad\text{in }\ell^2_\downarrow\times\mathbb N_0^{\mathbb N},$$</div>
<p>where the second factor has its product topology. Here $(\ell_j)$ are the excursion lengths of $R_\lambda$ in decreasing order. They are positive, distinct and square-summable almost surely. If $(a_j,b_j)$ is the excursion of length $\ell_j$, then, conditionally on the Brownian path, the $Z_j$ are independent Poisson variables with means</p>
<div class="math-display">$$\int_{a_j}^{b_j}R_\lambda(t)\,dt.$$</div>
<p>The limiting late-excursion mass also satisfies</p>
<div class="math-display">$$\mathbb E\sum_{(a,b):\,a>T}(b-a)^2\le\frac1{T-\lambda}
\qquad\bigl(T>\max\{\lambda,0\}\bigr).$$</div>
<p><em>Proof.</em> The joint path and mark limits CY46/GGL3 hold on every bounded interval. Tightness on successive integer intervals gives their joint version in the local uniform and locally weak topologies. By the Skorokhod representation theorem, we may work on a probability space where both convergences hold almost surely on every compact interval with no boundary atom. By 2N9T, each fixed positive time is outside the reflected zero set almost surely. The limit mark measure charges neither the chosen integer boundaries nor any excursion endpoint.</p>
<p>Fix deterministic $T,d>0$. The probability that an excursion starts at $T$ or has length $d$ is zero. Lemma 59NH therefore matches the finitely many components with scaled start less than $T$ and scaled size greater than $d$ to the corresponding limiting excursions, with both lengths and surplus counts converging. Random bounds on their right endpoints cause no difficulty: the coupled convergence holds on all compact intervals. This proves the joint limit with these two cutoffs.</p>
<p>To bound the limiting late mass, first retain only excursions with start in $(T,U)$ and length greater than $d$. Their squared lengths are limits of squared scaled component sizes with starts beyond $H_N$. Fatou's lemma and CH8I bound the expectation of their sum by $1/(T-\lambda)$. Let $U$ increase to infinity and $d$ decrease to zero through deterministic sequences. Monotone convergence proves the displayed bound. Excursions starting before a fixed $T$ are contained before the first zero after $T$, which is finite almost surely. Their lengths have finite total sum, so their squared lengths do too. The late bound thus proves square summability of all lengths. There are infinitely many positive lengths by 2N9T, and square summability allows them to be placed in decreasing order; that order has no ties.</p>
<p>We now remove the cutoffs in $\ell^2$. Among components starting before $H_N$, those with size at most $dN^{2/3}$ have normalized squared mass bounded by</p>
<div class="math-display">$$N^{-4/3}\sum_{\substack{\mathrm{start}(\mathcal C)<H_N\\|\mathcal C|\le dN^{2/3}}}
|\mathcal C|^2
\le d\,\frac{\tau_N(T)}{N^{2/3}}.$$</div>
<p>The completion times are tight by CH8I. All later components have normalized squared mass tending uniformly to zero in probability as $T\to\infty$, by CH8I and Markov's inequality. A cutoff at scaled start $T$ differs from one at $H_N$ by at most one discrete time step; under the coupling this step lies inside the component containing $T$ eventually, so the retained collections agree. The same small-length bound holds for the limiting excursions, using their finite total length before the excursion containing $T$ ends, and their late squared mass has the bound just proved.</p>
<p>Deleting coordinates and then sorting changes a nonnegative square-summable vector by at most the $\ell^2$ norm of the deleted coordinates. Indeed, match retained coordinates to themselves and deleted coordinates to zeros; sorting minimizes squared matching cost, as follows by swapping each inverted pair. Apply this to the two truncated size vectors. First choose $T$ large, next a high-probability bound for the completion time at $T$, and then $d$ small. Their deletion errors are arbitrarily small in probability, whereas the finite retained vectors converge. The converging-together argument proves the full $\ell^2$ size limit.</p>
<p>For any fixed number of ranks $K$, the limiting first $K$ lengths are positive and distinct. With probability arbitrarily close to one, they all occur before a sufficiently large deterministic $T$ and exceed a sufficiently small deterministic $d$. Choose a positive lower bound for the limiting $K$th length on a high-probability event. The deletion estimates make the norm of the omitted size vector smaller than half that bound with high probability, so an omitted discrete component cannot displace one of those ranks. The positive gaps between the retained limiting lengths fix their order eventually. The finite matched surplus counts therefore converge in the correct order along with the full size vector. This holds for every $K$. It gives tightness and convergence in the countable product of the discrete surplus coordinates, jointly with the $\ell^2$ size vector. Finally, disjoint excursions are disjoint sets for the conditional Poisson point measure of GGL3; their conditional means are their queue areas, proving the stated law. $\square$</p>
<p>This completes the fixed-parameter critical-window component and surplus limit, including the $\ell^2$ topology. It does not assert convergence of moments from distributional convergence, or a coupling as $\lambda$ varies. The comparison is <a href="https://doi.org/10.1214/aop/1024404421">Aldous (1997), Corollary 2 and Section 2.3</a>; the stopped-remainder estimate here supplies the late-component control directly.</p>



## Coalescing a square-summable collection {#section-coalescent-construction}

<p>Put $E=\ell^2_\downarrow$. For $x\in E$, give each pair $i<j$ an independent exponential variable $\xi_{ij}$ of mean one, and join $i,j$ at time $t$ when $\xi_{ij}\le tx_ix_j$. A component has mass equal to the sum of its vertex weights. Write $X(x,t)$ for the component masses in decreasing order and $S(x,t)$ for their sum of squares. Zero weights can be discarded. Connectivity always means connectivity by a finite path.</p>

<a id="tag-3G0K" data-assertion="theorem" data-title="Independent edge clocks define the multiplicative coalescent for every square-summable initial mass sequence"></a>
<p>For every $x\in E$, almost surely $X(x,t)\in E$ for every finite $t\ge0$. Its transition kernels $P_t(x,\cdot)$ form a Markov semigroup. In a finite state, each pair of components of masses $u,v$ merges at rate $uv$. If $b=\|x\|_2^2$ and $tb<1$, then</p>
<div class="math-display">$$\mathbb E S(x,t)\le\frac{b}{1-tb}.$$</div>
<p>In the common-clock construction, restriction to the first $k$ vertices gives $S(x^{[k]},t)\uparrow S(x,t)$ and $X(x^{[k]},t)\to X(x,t)$ in $\ell^2$.</p>
<p><em>Proof.</em> We first record a deterministic comparison. If a weighted graph is enlarged by adding edges or vertices or increasing weights, let $a$ and $c$ be its old and new ranked component masses. Provided $\|c\|_2<\infty$,</p>
<div class="math-display">$$\|c-a\|_2^2\le\|c\|_2^2-\|a\|_2^2.$$</div>
<p>Inside a new component of mass $w$, let the old masses be $a_1\ge a_2\ge\cdots$, with $\sum_i a_i\le w$. Match $w$ to $a_1$ and all other old masses to zero. Since $\sum_i a_i^2\le a_1\sum_i a_i\le wa_1$, this matching costs at most $w^2-\sum_i a_i^2$. Sum over new components and rank: decreasing order minimizes squared matching cost. The same argument applies to countable lists by taking finite truncations.</p>
<p>For the expectation bound, expand</p>
<div class="math-display">$$S(x,t)=\sum_{i,j}x_ix_j\mathbf1_{\{i\leftrightarrow j\}}.$$</div>
<p>Every connection has a self-avoiding path. A path of $q$ edges has probability at most the product of its $q$ rates times $t^q$. After multiplying by the two endpoint weights and summing, each vertex along the path contributes its squared weight. Dropping the distinctness restrictions bounds the contribution by $t^qb^{q+1}$. The term $q=0$ is $b$. Tonelli's theorem and the geometric series give the claim, including countably many vertices.</p>
<p>For arbitrary $t$, choose $k$ so that $t\sum_{i>k}x_i^2<1$. The tail graph has square-summable component masses almost surely by that bound. Add the first $k$ vertices one at a time. Conditional on the current graph, a new vertex of mass $u$ attaches independently to its components of masses $z_j$ with probabilities $1-e^{-tuz_j}$. The total attached mass $A$ satisfies</p>
<div class="math-display">$$\mathbb E(A\mid(z_j))\le tu\sum_jz_j^2<\infty.$$</div>
<p>Thus $A<\infty$ almost surely. The new sum of squares is at most $(u+A)^2+\sum_jz_j^2$, so it remains finite. This proves finiteness at each fixed $t$. Apply it at every positive integer and use monotonicity to obtain finiteness at all finite times on one event.</p>
<p>At a deterministic time $s$, condition on the entire revealed edge-clock history. Every edge between distinct current components is still absent. Exponential memorylessness leaves its residual clock independent of the others. Between components $C,D$, the sum of their edge rates is</p>
<div class="math-display">$$\sum_{i\in C,j\in D}x_ix_j
=\left(\sum_{i\in C}x_i\right)\left(\sum_{j\in D}x_j\right).$$</div>
<p>Both masses are finite. Infinite products of the no-edge probabilities therefore give an exponential clock with this rate; disjoint component pairs use disjoint original edges. The future component law depends only on the current masses. This proves the Markov property and the semigroup identity, as well as the finite merger rates.</p>
<p>Finally, the indicators of connectivity in the first $k$ vertices increase to the full connectivity indicators: any finite path is eventually included. The double sum for $S$ therefore converges monotonically. The deterministic comparison then gives the claimed $\ell^2$ convergence of the restrictions. $ \square$</p>

## Adding small components {#section-coalescent-attachment}

<a id="tag-5HM7" data-assertion="proposition" data-title="A bipartite attachment estimate controls the effect of a small squared-mass remainder"></a>
<p>Take two finite or countable lists of nonnegative masses $(u_i)$ and $(v_j)$, with $a=\sum_i u_i^2<\infty$ and $b=\sum_jv_j^2<\infty$. Join only pairs from opposite lists, independently, with probabilities $1-e^{-tu_iv_j}$. Let $Q$ be the sum of squared component masses in the resulting graph. For every $t\ge0$ and $\varepsilon>0$,</p>
<div class="math-display">$$\mathbb P(Q>a+\varepsilon)
\le \frac{\bigl[1+t(a+\varepsilon)\bigr]^2b}{\varepsilon}.$$</div>
<p><em>Proof.</em> First take finite lists. Begin with all the $u$ vertices isolated and add the $v$ vertices successively. Just before adding mass $v$, let the current component masses be $w_C$, and let $u_C\le w_C$ be the mass in $C$ coming from the first list. The new vertex attaches to these components independently, with indicators $I_C$ satisfying $\mathbb P(I_C=1\mid\text{past})=1-e^{-tvu_C}\le tvw_C$. The exact increase in the sum of squares is</p>
<div class="math-display">$$\Delta Q=v^2+2v\sum_Cw_CI_C
+\sum_{C\ne D}w_Cw_DI_CI_D.$$</div>
<p>The first term counts the new vertex even if it attaches to nothing. Conditional independence gives</p>
<div class="math-display">$$\mathbb E(\Delta Q\mid\text{past})
\le v^2(1+2tQ+t^2Q^2)=v^2(1+tQ)^2.$$</div>
<p>Stop at the first value above $a+\varepsilon$, or after the last vertex if this never happens. Before each counted increment, $Q\le a+\varepsilon$. Summing the conditional expectations bounds the expected stopped increase above $a$ by $[1+t(a+\varepsilon)]^2b$. On the crossing event that increase exceeds $\varepsilon$. Markov's inequality proves the result.</p>
<p>For countable lists, truncate both lists. Their initial squared mass is at most $a$; stop each finite construction at the same level $a+\varepsilon$. The preceding argument still bounds the crossing probability by the displayed expression, since crossing requires an increase of at least $\varepsilon$. The sums of squared component masses increase to $Q$ by finite-path connectivity, so the bound passes to the limit.</p>
<p>The constant term in the numerator cannot be discarded. With one vertex of mass one on each side, $t=1/10$ and $\varepsilon=1/2$, one always has $Q\ge2>a+\varepsilon$. Replacing $[1+t(a+\varepsilon)]^2$ by $2t(a+\varepsilon)+t^2(a+\varepsilon)^2$ would give the false upper bound $129/200$ for this probability. $ \square$</p>
<p>We will apply this conditionally, after first exploring all edges within each of two collections. Their component masses become the two lists above. Cross-collection edges remain independent, and their aggregate rates are products of component masses.</p>

## Continuity of the coalescent law {#section-coalescent-feller}

<a id="tag-7HLE" data-assertion="theorem" data-title="The multiplicative-coalescent transition law is jointly continuous in time and square-summable initial masses"></a>
<p>If $x_n\to x$ in $E$ and $t_n\to t\ge0$, then</p>
<div class="math-display">$$X(x_n,t_n)\ \xrightarrow{\ d\ }\ X(x,t)\qquad\text{in }E.$$</div>
<p>In particular, $P_t$ sends bounded continuous functions on $E$ to bounded continuous functions. The graphical process has a version with right-continuous paths and left limits in $E$.</p>
<p><em>Proof.</em> A small initial squared mass stays small for any fixed time: by 3G0K, if $\|y_n\|_2\to0$, then $S(y_n,t)\to0$ in probability. The same estimate at small times gives, for $b=\|x\|_2^2$ and $hb<1$,</p>
<div class="math-display">$$\mathbb E\bigl[S(x,h)-b\bigr]\le\frac{hb^2}{1-hb}.$$</div>
<p>Apply the Markov property at a fixed time $t$ and then condition on $X(x,t)$. Its squared norm is finite almost surely, so the bound, capped at probability one, shows that $S(x,t+h)-S(x,t)\to0$ in probability as $h\downarrow0$. This supplies the right continuity in probability needed below without assuming the Feller property.</p>
<p>Fix $t>0$. Use the same $\xi_{ij}$ for every initial sequence. Every finite open path for $x$ remains open for $x_n$ eventually, since almost surely no clock equals its limiting threshold. Fatou's lemma applied to the double sum in 3G0K gives</p>
<div class="math-display">$$\liminf_n S(x_n,t)\ge S(x,t)\quad\text{almost surely}.$$</div>
<p>For the reverse bound, first suppose $x\ne0$. Fix $c>1$ and choose $k$ among its positive coordinates. For large $n$, $x_{n,i}\le cx_i$ for $i\le k$. Dominate the graph for $x_n$ by a graph whose initial masses are the entire list $cx$ together with a separate copy of $(x_{n,i})_{i>k}$. The first $k$ vertices of $x_n$ embed in the first list and its remaining vertices in the second; their weights and edge rates only increase.</p>
<p>Explore the two lists separately. Their squared component masses are $A=S(cx,t)$ and $B_{n,k}=S((x_{n,i})_{i>k},t)$. Since $x_n\to x$ in $\ell^2$,</p>
<div class="math-display">$$\lim_{k\to\infty}\limsup_n
\mathbb P(B_{n,k}>\delta)=0\qquad(\delta>0).$$</div>
<p>If $x$ has only finitely many positive coordinates, take $k$ to be that number and let $n\to\infty$. Conditional on the two explored graphs, 5HM7 bounds the increase above $A$ caused by combining them. On $\{A\le M,\ B_{n,k}\le\delta\}$ its probability of exceeding $\varepsilon$ is at most $[1+t(M+\varepsilon)]^2\delta/\varepsilon$. Take the upper limit in $n$, then let $k$ tend to infinity, then let $\delta$ decrease to zero and $M$ increase to infinity. Thus the added list has a vanishing effect in probability.</p>
<p>Consequently, for each bounded continuous increasing $\varphi:[0,\infty)\to\mathbb R$,</p>
<div class="math-display">$$\limsup_n\mathbb E\varphi(S(x_n,t))
\le\mathbb E\varphi(S(cx,t)).$$</div>
<p>The common-clock scaling identity is $S(cx,t)=c^2S(x,c^2t)$. The right continuity in probability already proved lets $c\downarrow1$ in the last bound. Combined with the almost-sure lower bound, this proves $S(x_n,t)\to S(x,t)$ in probability in the original common-clock coupling. One explicit way to see this is to take $\varphi(s)=s/(1+s)$: the negative part of the difference tends to zero by bounded convergence, while the expectation bound forces its positive part to tend to zero too. Inverting $\varphi$ at the finite limiting value gives the asserted convergence of $S$. If $x=0$, the small-mass estimate gives the conclusion directly.</p>
<p>To recover convergence of the ranked vectors, restrict all graphs to their first $k$ vertices. Their finitely many edge indicators stabilize almost surely and their weights converge, so $X(x_n^{[k]},t)\to X(x^{[k]},t)$. The deterministic comparison gives</p>
<div class="math-display">$$\|X(x_n,t)-X(x_n^{[k]},t)\|_2^2
\le S(x_n,t)-S(x_n^{[k]},t).$$</div>
<p>For fixed $k$, the right side converges in probability to $S(x,t)-S(x^{[k]},t)$, which decreases to zero as $k\to\infty$. The same bound applies to $x$. The triangle inequality proves $X(x_n,t)\to X(x,t)$ in probability under this coupling, and hence the fixed-time Feller assertion.</p>
<p>For $t_n\to t>0$, use the exact identity</p>
<div class="math-display">$$X(x_n,t_n)=t_n^{-1/2}X(\sqrt{t_n}\,x_n,1).$$</div>
<p>The fixed-time result and continuity of scalar multiplication give joint continuity. At $t=0$, the numbers $b_n=\|x_n\|_2^2$ are bounded. The small-time expectation bound and the deterministic comparison show that $X(x_n,t_n)-x_n\to0$ in probability in $\ell^2$, which proves this endpoint as well.</p>
<p>Finally, on every bounded time interval the increasing function $S(x,\cdot)$ is bounded. The deterministic comparison makes the vectors $X(x,s)$ Cauchy as $s$ approaches any time from either side. Their limits exist in the closed space $E$. Taking right limits gives a path with right continuity and left limits. At each fixed time it agrees almost surely with the graphical value, by the right continuity in probability above. It is therefore a version of the same process. $ \square$</p>

## Several parameters in the critical window {#section-critical-parameter-laws}

<p>Let $\mu_\lambda$ be the law in $E$ of the ranked excursion lengths of $B(s)+\lambda s-s^2/2$ above its running minimum. The Brownian motions used to define these separate marginal laws need not be coupled. To identify the joint law as $\lambda$ varies, we use the edge clocks.</p>

<a id="tag-Z8T1" data-assertion="theorem" data-title="Critical complete-graph component sizes converge at every finite collection of window parameters to the standard multiplicative coalescent"></a>
<p>Give all edges of the complete graph independent uniform variables and include an edge at parameter $\lambda$ when its variable is at most $p_N(\lambda)=N^{-1}+\lambda N^{-4/3}$. Let $\mathbf L_N(\lambda)$ be the decreasing component-size vector multiplied by $N^{-2/3}$. For every finite list $\lambda_1<\cdots<\lambda_m$,</p>
<div class="math-display">$$\bigl(\mathbf L_N(\lambda_1),\ldots,\mathbf L_N(\lambda_m)\bigr)
\ \xrightarrow{\ d\ }\ \bigl(\mathbf X(\lambda_1),\ldots,\mathbf X(\lambda_m)\bigr)
\quad\text{in }E^m,$$</div>
<p>where the first limit state has law $\mu_{\lambda_1}$ and the successive transitions are $P_{\lambda_{j+1}-\lambda_j}$. These laws are consistent for all real parameter lists, and define an eternal Markov process with marginals $\mu_\lambda$, the standard multiplicative coalescent.</p>
<p><em>Proof.</em> Write each uniform edge variable as $1-e^{-\xi}$, with $\xi$ exponential of mean one. Assign each vertex mass $N^{-2/3}$. The uniform-edge graph at $\lambda$ is exactly the edge-clock graph at coalescent time</p>
<div class="math-display">$$q_N(\lambda)=N^{4/3}\bigl[-\log(1-p_N(\lambda))\bigr]
=N^{1/3}+\lambda+O(N^{-2/3}),$$</div>
<p>uniformly on bounded parameter intervals. Thus, conditionally on the state at $\lambda_j$, the transition to $\lambda_{j+1}$ is exactly $P_{q_N(\lambda_{j+1})-q_N(\lambda_j)}$. The time difference tends to $\lambda_{j+1}-\lambda_j$.</p>
<p>The one-time convergence $\mathbf L_N(\lambda_1)\Rightarrow\mu_{\lambda_1}$ is M7BY. Joint continuity of the transition kernels in 7HLE now proves the finite-list assertion by induction. For clarity, if initial states converge weakly, couple them so that they converge almost surely. Along every such sequence of states and convergent time increments, 7HLE gives weak convergence of the next-state laws. Testing against a bounded continuous function of the past states and the next state, and using bounded convergence, passes each transition to the limit. Repeating this argument gives the full vector.</p>
<p>In particular, comparison with M7BY at the second time gives the entrance-law identity</p>
<div class="math-display">$$\mu_\lambda P_h=\mu_{\lambda+h}\qquad(\lambda\in\mathbb R,\ h\ge0).$$</div>
<p>This identity and the semigroup property make the finite-list laws consistent when a time is removed or inserted. The Kolmogorov extension theorem gives a process indexed by all of $\mathbb R$ with these laws, and their transition factorization gives the Markov property. $ \square$</p>
<p>This is convergence of finite-dimensional distributions in the $\ell^2$ state space. It does not yet prove convergence in a topology on paths, the joint evolution of the surplus counts, or a representation of all parameter values using one Brownian path. The source comparison is <a href="https://doi.org/10.1214/aop/1024404421">Aldous (1997), Proposition 5, Section 4.2 and Corollary 24</a>. The construction and continuity arguments above also supply the coalescent input used in the <a href="/tag/7VHT/">hierarchical renormalization map</a>.</p>



## Short-time changes after a stopping time {#section-coalescent-stopped-increments}

<p>The finite-dimensional law above can be strengthened to a law on paths. The useful control is on the squared mass $S(t)=\|X(t)\|_2^2$: it increases at every merger and bounds the squared distance between two states.</p>

<a id="tag-O3IS" data-assertion="proposition" data-title="The squared-mass estimate controls coalescent increments uniformly after bounded stopping times"></a>
<p>Let $X$ be a multiplicative coalescent with a possibly random finite initial list of masses, independent of its future edge clocks. Put $S(t)=\|X(t)\|_2^2$, and let $\tau$ be a bounded stopping time for its natural filtration. On the event $hS(\tau)<1$, for $h>0$ and $\eta>0$,</p>
<div class="math-display">$$\mathbb P\!\left(
\sup_{0\le u\le h}\|X(\tau+u)-X(\tau)\|_2>\eta
\,\middle|\,\mathcal F_\tau\right)
\le\frac{hS(\tau)^2}{[1-hS(\tau)]\eta^2}.$$</div>
<p>In particular, on $\{S(\tau)\le M\}$ and for $0<h\le(2M)^{-1}$, the right side is at most $2hM^2/\eta^2$, for every $M>0$.</p>
<p><em>Proof.</em> Conditional on the initial masses, the finite exponential-clock construction is a finite-state continuous-time Markov chain. Its strong Markov property gives the coalescent started from $X(\tau)$ after time $\tau$; the same assertion holds for a random initial list by conditioning. The deterministic comparison in 3G0K gives, simultaneously for $0\le u\le h$,</p>
<div class="math-display">$$\|X(\tau+u)-X(\tau)\|_2^2
\le S(\tau+u)-S(\tau)\le S(\tau+h)-S(\tau).$$</div>
<p>Writing $b=S(\tau)$, the conditional expectation of the last difference is at most $hb^2/(1-hb)$ by 3G0K. Conditional Markov inequality proves the claim. A zero state stays zero, so it causes no exception. $ \square$</p>

## Tightness from an increasing quadratic bound {#section-coalescent-path-tightness}

<p>We use the usual Skorokhod $J_1$ topology on $D([0,T],F)$, where $(F,d)$ is a complete separable metric space. It allows a small increasing change of time to align jumps. For a path $y$, let $w'(y,\delta)$ be the infimum of the largest oscillation on the intervals of a partition of $[0,T]$ whose interval lengths exceed $\delta$. Intervals are closed on the left and open on the right, except that the last includes $T$.</p>

<a id="tag-R8LD" data-assertion="proposition" data-title="Marginal tightness and stopped increments give path tightness when an increasing process bounds squared distances"></a>
<p>Let $Y_n$ be adapted $F$-valued càdlàg processes on $[0,T]$, with the usual filtration conditions, and let $R_n$ be nonnegative adapted increasing càdlàg processes such that almost surely</p>
<div class="math-display">$$d(Y_n(s),Y_n(t))^2\le R_n(t)-R_n(s)
\qquad(0\le s\le t\le T).$$</div>
<p>Suppose that the laws of $R_n(T)$ are tight and, for every deterministic $t\in[0,T]$, the laws of $Y_n(t)$ are tight in $F$. Suppose also that for every $M,\eta>0$ there are $C,h_0>0$ such that, for all $n$, all stopping times $\tau\le T$ and $0<h<h_0$,</p>
<div class="math-display">$$\mathbf1_{\{R_n(\tau)\le M\}}
\mathbb P\!\left(
\sup_{0\le u\le h}d\bigl(Y_n((\tau+u)\wedge T),Y_n(\tau)\bigr)>\eta
\,\middle|\,\mathcal F_\tau\right)\le Ch.$$</div>
<p>Then the laws of $Y_n$ are tight in $D([0,T],F)$ with its $J_1$ topology.</p>
<p><em>Proof.</em> Fix $M,\eta>0$. Starting at time zero, record each first exit from the ball of radius $\eta$ about the state at the previous recorded time. These are stopping times. At every genuine exit the distance from the previous recorded state is at least $\eta$, so $R_n$ has increased by at least $\eta^2$. On $\{R_n(T)\le M\}$ there are therefore at most $\lfloor M/\eta^2\rfloor$ such exits before $T$.</p>
<p>A gap of at most $h$ between two consecutive recorded times forces a displacement greater than $\eta/2$ within $h$ of the earlier time. The conditional hypothesis and a union bound over at most $1+\lfloor M/\eta^2\rfloor$ intervals show that the probability of such a short gap, together with $R_n(T)\le M$, is $O_{M,\eta}(h)$, uniformly in $n$. The hypothesis at the deterministic time $T-h$ also gives, except on an event with the same order of probability,</p>
<div class="math-display">$$\sup_{T-h\le t\le T}d(Y_n(t),Y_n(T-h))\le\eta.$$</div>
<p>Between consecutive exits the path stays within $\eta$ of its recorded state. If the final interval has length at most $h$, merge it with the preceding interval. The last display bounds the oscillation on the merged interval by $4\eta$; all other intervals have oscillation at most $2\eta$. If there was no exit, use the whole interval. Thus, for sufficiently small $h$ compared with $T$,</p>
<div class="math-display">$$\sup_n\mathbb P\bigl(w'(Y_n,h)>4\eta\bigr)
\le\sup_n\mathbb P(R_n(T)>M)+O_{M,\eta}(h).$$</div>
<p>Letting first $h\downarrow0$ and then $M\uparrow\infty$ gives the required oscillation bound.</p>
<p>We also need compact containment in $F$; a bound on distance from one point would not suffice in an infinite-dimensional space. Choose $\eta_j\downarrow0$ and $h_j>0$ so that $w'(Y_n,h_j)\le4\eta_j$ outside an event of probability at most $\varepsilon2^{-j-2}$, uniformly in $n$. A deterministic grid of mesh less than $h_j/2$, including both endpoints, meets every interval of a qualifying partition. Tightness at its finitely many times gives a compact set $K_j$ containing all these grid values outside another event of probability at most $\varepsilon2^{-j-2}$. Choose a finite $\eta_j$-net $F_j$ for $K_j$.</p>
<p>On these two events' complement, the entire path is within $6\eta_j$ of $F_j$. The harmless extra $\eta_j$ allows a partition arbitrarily close to the infimum defining $w'$. The set</p>
<div class="math-display">$$K=\bigcap_{j\ge1}\{z:d(z,F_j)\le6\eta_j\}$$</div>
<p>is closed and totally bounded, hence compact because $F$ is complete. A union bound shows that the entire range of each $Y_n$ lies in $K$ with probability at least $1-\varepsilon$. Compact containment and the oscillation bound give tightness by the Skorokhod compactness criterion. This proof establishes compact containment explicitly, rather than treating bounded subsets of $F$ as compact. $ \square$</p>

## Convergence of finite coalescents as paths {#section-coalescent-finite-approximation}

<a id="tag-GRSC" data-assertion="theorem" data-title="Finite initial mass approximations converge to the square-summable multiplicative coalescent in Skorokhod path space"></a>
<p>Let $\nu_n,\nu$ be probability laws on $E=\ell^2_\downarrow$, with $\nu_n\Rightarrow\nu$, and suppose $\nu_n$ is supported on finite mass lists. Start a multiplicative coalescent $X_n$ with law $\nu_n$, using independent future clocks. Let $X$ have initial law $\nu$ and the càdlàg version of the kernels in 7HLE. Then, for every $T>0$,</p>
<div class="math-display">$$X_n\ \xrightarrow{\ d\ }\ X
\qquad\text{in }D([0,T],E)\text{ with the }J_1\text{ topology}.$$</div>
<p><em>Proof.</em> The Feller property and the Markov transition argument in Z8T1 give convergence at every finite list of deterministic times. In particular, the laws of $X_n(t)$ are tight for each $t$, and $S_n(T)=\|X_n(T)\|_2^2$ is tight. Apply R8LD with $R_n=S_n$. The deterministic distance comparison is 3G0K, and O3IS gives its stopped maximal-increment hypothesis. Hence the path laws are tight.</p>
<p>The candidate limit has no jump at any fixed positive time. To see this directly, condition on its initial state $x$. For a fixed $t>0$, almost surely no edge clock equals $tx_ix_j$. Every finite path present at $t$ is then already present at some earlier time. Monotone convergence in the double-sum formula for $S$ gives $S(x,s)\uparrow S(x,t)$ as $s\uparrow t$. The distance comparison gives $X(x,s)\to X(x,t)$ in $\ell^2$. The càdlàg version agrees with the graphical values at fixed times and on a countable dense set, so the same left continuity holds for that version. At zero it is right-continuous by construction. Conditioning can now be removed.</p>
<p>The standard identification theorem for tight Skorokhod laws therefore applies: convergence of the finite-dimensional laws to this stochastically continuous càdlàg process identifies every subsequential limit. Equivalently, identify a subsequential law on a dense set of its continuity times using the finite-dimensional limits; these coordinates determine a càdlàg path law. The entire sequence consequently converges. $ \square$</p>
<p>No uniform bound on the total initial mass is required. The terminal squared masses are tight because of the already-proved one-time continuity, and the short-time argument is localized by that squared mass.</p>

## The critical-window process limit {#section-critical-window-path-law}

<a id="tag-TIGK" data-assertion="theorem" data-title="The ranked critical Erdős–Rényi size process converges on every bounded parameter interval in Skorokhod l2 path space"></a>
<p>Fix $a<b$ and use the common-uniform-edge coupling of Z8T1. For all sufficiently large $N$, let $\mathbf L_N(\lambda)$ be the ranked component sizes of $G(N,N^{-1}+\lambda N^{-4/3})$, multiplied by $N^{-2/3}$. Then</p>
<div class="math-display">$$\bigl(\mathbf L_N(\lambda)\bigr)_{\lambda\in[a,b]}
\ \xrightarrow{\ d\ }\ \bigl(\mathbf X(\lambda)\bigr)_{\lambda\in[a,b]}
\quad\text{in }D([a,b],E)\text{ with }J_1,$$</div>
<p>where $\mathbf X$ is the standard multiplicative coalescent. In particular,</p>
<div class="math-display">$$\int_a^b N^{-4/3}\sum_{\mathcal C\text{ at }\lambda}|\mathcal C|^2\,d\lambda
\ \xrightarrow{\ d\ }\ \int_a^b\|\mathbf X(\lambda)\|_2^2\,d\lambda.$$</div>
<p><em>Proof.</em> At parameter $a$, M7BY gives $\mathbf L_N(a)\Rightarrow\mu_a$ in $E$, and every initial list is finite. After that time, exponential memorylessness identifies the future with a finite multiplicative coalescent $Y_N$, started from this random state. If $T=b-a$, the exact parameterization is</p>
<div class="math-display">$$\mathbf L_N(a+s)=Y_N(u_N(s)),\qquad
u_N(s)=q_N(a+s)-q_N(a),\qquad 0\le s\le T.$$</div>
<p>The time change is deterministic and strictly increasing. Since</p>
<div class="math-display">$$u_N'(s)=\frac1{1-p_N(a+s)}=1+O(N^{-1}),$$</div>
<p>uniformly for $s\in[0,T]$, it converges uniformly to the identity. GRSC gives convergence of $Y_N$ on the slightly longer interval $[0,T+1]$. Extend $u_N$ linearly from its value at $T$ to the value $T+1$ at $T+1$. For large $N$ this is an increasing homeomorphism uniformly close to the identity. Composing with it preserves the $J_1$ limit. Restriction to $[0,T]$ also preserves convergence, since the limiting coalescent has no fixed jump at $T$, as proved in GRSC. Translation by $a$ proves the process statement.</p>
<p>For the integral, deterministic $J_1$ convergence of $E$-valued paths implies convergence at each continuity time of the limiting path and a common bound on their norms over the compact interval. A càdlàg path has only countably many discontinuities. Dominated convergence therefore gives convergence of the integrals of the squared norms, so the continuous mapping theorem proves the second assertion. Both conclusions are distributional; convergence of their expectations would require additional uniform integrability. $ \square$</p>
<p>This completes the size-process limit on bounded critical-parameter intervals. The argument uses the written construction and finite-dimensional limit, with the compactness step supplied above. It does not identify a joint process for the surplus counts or represent all parameter values by one Brownian path.</p>



## Susceptibility at the complete-graph window scale {#section-er-window-susceptibility}

<p>The path limit above can be passed to moments once its terminal squared mass is uniformly integrable. We obtain the required bounds from the finite triangle theorem, using a small susceptibility reference level rather than assuming a triangle estimate at $1/N$.</p>

<a id="tag-A40L" data-assertion="proposition" data-title="Complete-graph susceptibility is uniformly bounded on the volume-third scale throughout a bounded critical window"></a>
<p>For every $\Lambda\ge0$ there is a finite $K_\Lambda$ such that, for every $N\ge2$ and $|\lambda|\le\Lambda$ with $p_N(\lambda)=N^{-1}+\lambda N^{-4/3}\in[0,1]$,</p>
<div class="math-display">$$\chi_N(\lambda):=\mathbb E_{p_N(\lambda)}|C_o|\le K_\Lambda N^{1/3}.$$</div>
<p><em>Proof.</em> It suffices to consider sufficiently large $N$, depending on $\Lambda$; the remaining finitely many sizes satisfy $\chi_N\le N$. Set $\alpha=1/10$ and $H=\alpha N^{1/3}$. For large $N$, $100\le H<N$ and there is a parameter $p_0\in(0,1/2]$ with $\chi(p_0)=H$. Indeed, the susceptibility is a continuous increasing polynomial, equals one at zero, and at $1/2$ is at least $1+(N-1)/2>H$.</p>
<p>The exact complete-graph formula <a href="/tag/R2Y7/">R2Y7</a> gives</p>
<div class="math-display">$$T_{p_0}^3(x,y)\le\mathbf1_{\{x=y\}}+\frac{H^3}{N}
=\mathbf1_{\{x=y\}}+\alpha^3,$$</div>
<p>and $\alpha^3<1/100$. Thus $p_0$ meets the hypotheses of <a href="/tag/CAZQ/">the finite-window susceptibility bound</a>. We also have</p>
<div class="math-display">$$(N-1)p_0\ge1-H^{-1}.$$</div>
<p>If $(N-1)p_0\ge1$ this is immediate. Otherwise the path-counting row-sum bound gives $H\le[1-(N-1)p_0]^{-1}$, which rearranges to the same inequality.</p>
<p>Write $p=p_N(\lambda)$. If $p\le p_0$, monotonicity gives $\chi(p)\le H$. If $p>p_0$, then $p\le1/2$ for large $N$ and its additive displacement obeys</p>
<div class="math-display">$$0<\varepsilon=(N-1)(p-p_0)
\le(\Lambda+\alpha^{-1})N^{-1/3}.$$</div>
<p>CAZQ, with reference level $H=\alpha N^{1/3}$, now gives</p>
<div class="math-display">$$\chi(p)\le C_\alpha[1+(\Lambda+\alpha^{-1})^2]N^{1/3}.$$</div>
<p>Increase the constant to cover the case $p\le p_0$ and the finitely many excluded sizes. $ \square$</p>
<p>No limiting susceptibility estimate is used to choose $p_0$, so this argument does not assume the uniform integrability that it is intended to prove.</p>

## Moments of the critical ranked sizes {#section-critical-ranked-moments}

<a id="tag-1DEZ" data-assertion="theorem" data-title="The critical ranked-size law converges against every continuous function of polynomial growth in the l2 norm"></a>
<p>Let $\lambda_N\to\lambda$, and let $\mathbf L_N(\lambda_N)$ be the ranked component-size vector multiplied by $N^{-2/3}$. If $F:E\to\mathbb R$ is continuous and $|F(x)|\le C(1+\|x\|_2^q)$ for some finite $C,q>0$, then</p>
<div class="math-display">$$\mathbb EF(\mathbf L_N(\lambda_N))
\longrightarrow\mathbb EF(\mathbf X(\lambda)).$$</div>
<p>In particular, for every real $r\ge1$,</p>
<div class="math-display">$$N^{-(2r-1)/3}\mathbb E_{p_N(\lambda_N)}|C_o|^r
\longrightarrow
\mathbb E\sum_{i\ge1}X_i(\lambda)^{r+1}<\infty.$$</div>
<p>The susceptibility limit is uniform on every compact interval:</p>
<div class="math-display">$$\sup_{\lambda\in[a,b]}
\left|N^{-1/3}\chi_N(\lambda)-\mathbb E\|\mathbf X(\lambda)\|_2^2\right|
\longrightarrow0.$$</div>
<p><em>Proof.</em> A40L and <a href="/tag/YN7V/">YN7V</a> give, for every $\Lambda,q>0$,</p>
<div class="math-display">$$\sup_{\substack{N\ge2,\ |\theta|\le\Lambda\\p_N(\theta)\in[0,1]}}
\mathbb E\|\mathbf L_N(\theta)\|_2^q<\infty.$$</div>
<p>Apply this with an exponent larger than $q$. The resulting uniform integrability, together with the $\ell^2$ convergence in M7BY, proves the expectation limit by truncating $F$ outside large norm balls. Fatou's lemma gives finite moments of every order for the limiting norm as well, uniformly for $\lambda$ in a bounded interval.</p>
<p>For $s\ge2$, the function $x\mapsto\sum_i x_i^s=\|x\|_s^s$ is continuous on $E$ and bounded by $\|x\|_2^s$. Its continuity follows from $\|x-y\|_s\le\|x-y\|_2$. Transitivity and counting vertices in each cluster give</p>
<div class="math-display">$$\mathbb E\sum_iL_{N,i}(\lambda_N)^{r+1}
=N^{-2(r+1)/3}\mathbb E\sum_C|C|^{r+1}
=N^{-(2r-1)/3}\mathbb E|C_o|^r.$$</div>
<p>Taking $s=r+1$ proves the second assertion. The same argument gives all positive moments and mixed polynomial moments of any fixed vector of ranked sizes.</p>
<p>Put $f(\lambda)=\mathbb E\|\mathbf X(\lambda)\|_2^2$. The coalescent is stochastically continuous at every deterministic parameter, by 7HLE and GRSC. Its uniformly bounded higher moments on compact parameter intervals therefore make $f$ continuous. Both $f$ and $f_N(\lambda)=N^{-1/3}\chi_N(\lambda)$ are nondecreasing. Pointwise convergence of $f_N$ to the continuous function $f$ is uniform on $[a,b]$: choose a finite grid on which the increments of $f$ are small, and trap each $f_N(\lambda)$ between its values at the adjacent grid points. This proves the last display. $ \square$</p>

## Expectations of critical path functionals {#section-critical-path-moments}

<a id="tag-KCRC" data-assertion="theorem" data-title="Critical size-path convergence also holds for expectations of polynomially bounded path functionals"></a>
<p>Fix $a<b$. Let $\Phi:D([a,b],E)\to\mathbb R$ be Borel measurable, continuous in the $J_1$ topology at almost every path of $\mathbf X$, and suppose</p>
<div class="math-display">$$|\Phi(x)|\le C\left(1+\sup_{\lambda\in[a,b]}\|x(\lambda)\|_2^q\right)$$</div>
<p>for some finite $C,q>0$. Then $\mathbb E\Phi(\mathbf L_N)\to\mathbb E\Phi(\mathbf X)$. In particular, if</p>
<div class="math-display">$$I_N=\int_a^bN^{-4/3}\sum_{\mathcal C\text{ at }\lambda}|\mathcal C|^2\,d\lambda,
\qquad I=\int_a^b\|\mathbf X(\lambda)\|_2^2\,d\lambda,$$</div>
<p>then, for every real $r>0$,</p>
<div class="math-display">$$\mathbb EI_N^r\longrightarrow\mathbb EI^r<\infty,
\qquad
N^{-1/3}\int_a^b\chi_N(\lambda)\,d\lambda
\longrightarrow\int_a^b\mathbb E\|\mathbf X(\lambda)\|_2^2\,d\lambda.$$</div>
<p><em>Proof.</em> Mergers only increase the sum of squared component masses, so</p>
<div class="math-display">$$\sup_{\lambda\in[a,b]}\|\mathbf L_N(\lambda)\|_2
=\|\mathbf L_N(b)\|_2.$$</div>
<p>The right side has uniformly bounded moments of every order by A40L and YN7V. It therefore supplies uniform integrability for $\Phi(\mathbf L_N)$; the limiting variable is integrable by the same bound and Fatou's lemma. Apply the almost-sure-continuity form of the continuous mapping theorem to TIGK, and then truncate, to obtain the expectation limit.</p>
<p>The squared-norm integral is a continuous function on $D([a,b],E)$ with $J_1$, as shown in TIGK, and is at most $(b-a)\sup_\lambda\|x(\lambda)\|_2^2$. Its $r$th power consequently satisfies the hypotheses for every $r>0$. This proves the moment limit. For $r=1$, Tonelli and the cluster-partition identity give $\mathbb EI_N=N^{-1/3}\int_a^b\chi_N(\lambda)\,d\lambda$ and $\mathbb EI=\int_a^bf(\lambda)\,d\lambda$, proving the last formula. $ \square$</p>
<p>Thus the earlier distributional limit of the integrated squared mass now includes convergence of all its positive moments. These arguments concern component sizes. They do not add a joint path theorem for surplus counts or an exponential-moment assertion.</p>



## New cycle edges in the critical window {#section-critical-cycle-proposals}

<p>A new edge either joins two components or has endpoints already connected. In the latter case it raises the graph's total surplus by one. We count these latter arrivals on a fixed parameter interval $(a,b]$, using the common-uniform-edge coupling. Let $\Xi_N$ be their point measure in the parameter $\lambda$, and put $C_N(t)=\Xi_N((a,t])$ for $a\le t\le b$. If $e_N(t)$ and $k_N(t)$ are the numbers of edges and components, then</p>
<div class="math-display">$$C_N(t)=e_N(t)-e_N(a)+k_N(t)-k_N(a).$$</div>
<p>This counts the increase in total surplus after $a$; it does not count the surplus already present at $a$.</p>

<a id="tag-6TZO" data-assertion="proposition" data-title="Poisson edge proposals couple critical cycle births to a conditional Poisson process with a vanishing rejection error"></a>
<p>Fix $a<b$, and take $N$ sufficiently large that $0<p_N(a)<p_N(b)<1$. Write $S_N(\lambda)=\|\mathbf L_N(\lambda)\|_2^2$ and</p>
<div class="math-display">$$u_N(\lambda)=N^{4/3}\log\frac{1-p_N(a)}{1-p_N(\lambda)},
\qquad u_N'(\lambda)=\frac1{1-p_N(\lambda)}.$$</div>
<p>There is a coupling of $\Xi_N$ with a point measure $Q_N$ such that, conditionally on the entire size path $\mathbf L_N$ on $[a,b]$, $Q_N$ is Poisson with intensity</p>
<div class="math-display">$$r_N(\lambda)\,d\lambda
=\frac12\bigl[S_N(\lambda)-N^{-1/3}\bigr]u_N'(\lambda)\,d\lambda,$$</div>
<p>and $\Xi_N\le Q_N$. Moreover,</p>
<div class="math-display">$$\mathbb P(\Xi_N\ne Q_N)
\le\mathbb E\bigl[Q_N([a,b])-\Xi_N([a,b])\bigr]
\le N^{-4/3}u_N(b)\binom N2 p_N(b)
=O_{a,b}(N^{-1/3}).$$</div>
<p><em>Proof.</em> Start with $G(N,p_N(a))$. In the time variable $u$, give each unordered pair of distinct vertices an independent Poisson process of rate $\delta_N^2$, where $\delta_N=N^{-2/3}$. At its first proposal after time zero, add the edge if it was initially absent; ignore every proposal on an edge already present. This has the exact original graph-process law, since the chance that an initially absent edge is still absent at time $u$ is $e^{-\delta_N^2u}$ and</p>
<div class="math-display">$$(1-p_N(a))e^{-\delta_N^2u_N(\lambda)}=1-p_N(\lambda).$$</div>
<p>A proposal joining different components merges them. A proposal inside one component is recorded in $Q_N$, whether or not the proposed edge was already present. If the current component orders are $s_1,s_2,\ldots$, the merger rate for components $i,j$ is $\delta_N^2s_is_j$, while the total internal-proposal rate is</p>
<div class="math-display">$$\delta_N^2\sum_i\binom{s_i}{2}
=\frac12\left[\sum_i(\delta_Ns_i)^2-N\delta_N^2\right]
=\frac12(S_N-N^{-1/3}).$$</div>
<p>The finite partition process is autonomous: internal proposals do not change it. More explicitly, its joint generator with the internal-proposal count is the sum of the merger generator and the operator that raises the count at this last rate. We may therefore construct the partition chain first, and generate internal proposals using an independent Poisson random measure with its path-dependent intensity. The finite-state chain, with this counting coordinate, has the same transition rates as the original construction and is nonexplosive. This proves the conditional Poisson assertion given the partition path. The intensity depends only on the ranked sizes, so conditioning on the size path gives the same assertion. The value at the finitely many merger times is immaterial to the intensity measure.</p>
<p>Every rejected proposal has endpoints already connected, and every non-rejected internal proposal is exactly a cycle-closing edge. Thus $Q_N-\Xi_N$ counts proposals on edges already present. Its expected total is</p>
<div class="math-display">$$\delta_N^2\int_0^{u_N(b)}\mathbb E e_N(u)\,du
\le\delta_N^2u_N(b)\binom N2p_N(b).$$</div>
<p>Here the integral uses the predictable number of present edges; changing its value at jump times does not affect it. Since $u_N(b)=O_{a,b}(1)$ and $\binom N2p_N(b)=O_{a,b}(N)$, the claimed bound follows. $ \square$</p>
<p>The subtraction of $N^{-1/3}$ accounts for the absence of loops at the original vertices. It disappears in the limit. The limiting rates agree with <a href="https://arxiv.org/pdf/1212.5493v1">Bhamidi–Budhiraja–Wang, Section 2.3.2</a>: distinct masses merge at their product, and a component of mass $x$ gains a surplus edge at rate $x^2/2$. Their Section 4 allows loops and multiple edges; the rejection estimate above gives the comparison needed for the simple graph.</p>

## The cycle-birth point process {#section-critical-cycle-birth-law}

<a id="tag-6248" data-assertion="theorem" data-title="Critical cycle-closing edges converge jointly with the size path to Poisson marks of half its squared norm"></a>
<p>On every fixed $[a,b]$,</p>
<div class="math-display">$$\bigl(\mathbf L_N,\Xi_N\bigr)
\ \xrightarrow{\ d\ }\ (\mathbf X,\Xi)
\quad\text{in }D([a,b],E)\times\mathcal M_{\rm p}([a,b]),$$</div>
<p>where the first factor has $J_1$ and the second has the weak topology of finite point measures. Conditional on the entire path $\mathbf X$, the measure $\Xi$ is Poisson with intensity $\frac12\|\mathbf X(\lambda)\|_2^2\,d\lambda$. Equivalently, for continuous $f\ge0$,</p>
<div class="math-display">$$\mathbb E\!\left[e^{-\int f\,d\Xi}\mid\mathbf X\right]
=\exp\!\left[-\frac12\int_a^b(1-e^{-f(\lambda)})
\|\mathbf X(\lambda)\|_2^2\,d\lambda\right].$$</div>
<p>Also $(\mathbf L_N,C_N)\Rightarrow(\mathbf X,C)$ in the product of the two $J_1$ path spaces, where $C(t)=\Xi((a,t])$.</p>
<p><em>Proof.</em> First replace $\Xi_N$ by $Q_N$ using 6TZO. Its conditional Laplace functional is $\exp[-\int(1-e^{-f})r_N]$. The derivative $u_N'$ tends uniformly to one, and $N^{-1/3}\to0$. For any deterministic sequence of paths converging in $J_1$, their norms have a common finite bound, and their values converge at every continuity time of the limit. Dominated convergence therefore shows that</p>
<div class="math-display">$$\frac12\int_a^b(1-e^{-f(\lambda)})
\bigl[S_N(\lambda)-N^{-1/3}\bigr]u_N'(\lambda)\,d\lambda
\ \xrightarrow{\ d\ }\
\frac12\int_a^b(1-e^{-f(\lambda)})\|\mathbf X(\lambda)\|_2^2\,d\lambda,$$</div>
<p>jointly with the size path, by TIGK. Multiplying the conditional Laplace functional by any bounded continuous function of that path consequently gives the stated limiting mixed Laplace functional.</p>
<p>To justify identification by these functionals, the mass paths are tight by TIGK. The counts of $Q_N$ have uniformly bounded means: their conditional means are at most a constant times $S_N(b)$, whose expectations are bounded by A40L. On a compact interval, point measures with a bounded number of atoms form a compact set. Thus the pairs are tight, and their mixed Laplace functionals identify every subsequential joint law. The limiting intensity is finite because the coalescent path has bounded norm on $[a,b]$. Conditional on the path it is absolutely continuous, so $\Xi$ is simple and has no atoms at $a$ or $b$. This proves the joint point-measure limit. The coupling error in 6TZO transfers it to $\Xi_N$.</p>
<p>Finally, if finite point measures converge weakly to a simple point measure with no endpoint atoms, their total masses are eventually equal and their atoms can be matched in increasing order with convergent positions. An increasing piecewise-linear change of time aligning those positions proves $J_1$ convergence of their cumulative counting paths. Apply this at $\Xi$ to obtain the last assertion. This is the product of two path topologies; no stronger joint time-alignment assertion is needed. $ \square$</p>

## Moments of the new cycle count {#section-critical-cycle-birth-moments}

<a id="tag-M7RY" data-assertion="corollary" data-title="The critical cycle increment has mixed-Poisson moment limits governed by the integrated squared component mass"></a>
<p>Put $C_N=C_N(b)$, $C=C(b)$, and retain the squared-mass integrals $I_N,I$ of KCRC. Then $(I_N,C_N)\Rightarrow(I,C)$, and conditionally on $I$, the variable $C$ is Poisson with mean $I/2$. For every real $q>0$, $\mathbb EC_N^q\to\mathbb EC^q<\infty$. All mixed polynomial moments of $I_N,C_N$ converge as well. In particular, for integers $m\ge1$, with $(c)_m=c(c-1)\cdots(c-m+1)$,</p>
<div class="math-display">$$\begin{aligned}
\mathbb E(C_N)_m&\longrightarrow2^{-m}\mathbb EI^m,\\
\mathbb EC_N&\longrightarrow\tfrac12\mathbb EI,\\
\operatorname{Var}(C_N)&\longrightarrow\tfrac12\mathbb EI+\tfrac14\operatorname{Var}(I),\\
\operatorname{Cov}(C_N,I_N)&\longrightarrow\tfrac12\operatorname{Var}(I).
\end{aligned}$$</div>
<p><em>Proof.</em> The integral and total point count are continuous at the limiting pair in 6248, so the joint limit follows. The conditional law of $C$ given the size path depends on that path only through $I$, which proves the asserted law given $I$.</p>
<p>For uniform integrability, the conditional mean of $Q_N([a,b])$ is bounded by $c_{a,b}S_N(b)$. Every integer moment of a Poisson variable is a polynomial with nonnegative coefficients in its mean, as follows by expanding its power in falling factorials. A40L and YN7V give uniformly bounded moments of $S_N(b)$ of every order. Hence all moments of $Q_N([a,b])$, and therefore of $C_N\le Q_N([a,b])$, are uniformly bounded. Also $I_N\le(b-a)S_N(b)$. Hölder's inequality now supplies uniform integrability for every mixed polynomial, using larger moment orders. Truncation passes these expectations to the joint limit and also proves convergence of all real positive moments of $C_N$.</p>
<p>For the formulas, condition on $I$. Poisson falling-factorial moments give $\mathbb E[(C)_m\mid I]=(I/2)^m$, while conditional variance and expectation both equal $I/2$. The laws of total variance and covariance give the remaining identities. $ \square$</p>
<p>These results determine the new cycle births over a bounded parameter interval, jointly with the entire size path. They do not attach the initial surplus counts to components through subsequent mergers. That remaining step requires control of the marked initial state and its small-component tail; the fixed-parameter product-topology statement M7BY alone does not supply it.</p>




## A weighted surplus bound for the remaining graph {#section-critical-weighted-surplus-tail}

<p>Write $\sigma(\mathcal C)=|E(\mathcal C)|-|\mathcal C|+1$ for the surplus of a connected component. The quantity needed for the marked state space is $\sum_{\mathcal C}|\mathcal C|\sigma(\mathcal C)$. Counting cycles bounds this quantity in a subcritical graph, and the unexplored graph becomes subcritical after a sufficiently late exploration time.</p>

<a id="tag-RJJ9" data-assertion="proposition" data-title="A cycle count bounds the size-weighted surplus of a subcritical random graph and the late critical exploration remainder"></a>
<p>For $G(m,p)$ with $\mu=mp<1$ and $m\ge0$,</p>
<div class="math-display">$$
\mathbb E\sum_{\mathcal C}|\mathcal C|\sigma(\mathcal C)
\le \frac{\mu^3}{2(1-\mu)^2}.
$$</div>
<p>Consequently, for the critical graph with $\lambda_N\to\lambda$ and the exploration convention of CH8I,</p>
<div class="math-display">$$
\limsup_{N\to\infty}\mathbb E\!\left[
N^{-2/3}\sum_{\mathcal C:\,\mathrm{start}(\mathcal C)\ge\lfloor TN^{2/3}\rfloor}
|\mathcal C|\sigma(\mathcal C)\right]
\le \frac1{2(T-\lambda)^2}
\qquad(T>\max\{\lambda,0\}).
$$</div>
<p><em>Proof.</em> In a connected finite graph, choose a spanning tree. Each edge outside it gives a distinct simple cycle, so the surplus is at most the number of simple cycles. For each possible unoriented simple cycle $\gamma$ of length $r\ge3$, let $\mathcal C(\gamma)$ be the component containing it when all its edges are open. Thus</p>
<div class="math-display">$$
\sum_{\mathcal C}|\mathcal C|\sigma(\mathcal C)
\le \sum_\gamma \mathbf1_{\{\gamma\text{ open}\}}|\mathcal C(\gamma)|.
$$</div>
<p>Conditional on $\gamma$ being open, all other edges retain their independent Bernoulli laws. Every vertex connected to $\gamma$ can be reached by a path starting at a vertex of $\gamma$, with no other vertex on $\gamma$. Such a path uses none of the prescribed cycle edges. Counting these paths, including the length-zero paths, gives</p>
<div class="math-display">$$
\mathbb E\bigl[|\mathcal C(\gamma)|\mid\gamma\text{ open}\bigr]
\le r\sum_{j\ge0}(mp)^j=\frac r{1-\mu}.
$$</div>
<p>There are $(m)_r/(2r)$ possible unoriented cycles of length $r$, where $(m)_r=m(m-1)\cdots(m-r+1)$. Their probability of being open is $p^r$. Summing the preceding estimate therefore gives</p>
<div class="math-display">$$
\mathbb E\sum_{\mathcal C}|\mathcal C|\sigma(\mathcal C)
\le \frac1{2(1-\mu)}\sum_{r=3}^{m}(m)_r p^r
\le \frac1{2(1-\mu)}\sum_{r\ge3}\mu^r
=\frac{\mu^3}{2(1-\mu)^2}.
$$</div>
<p>The empty graph contributes zero; the argument also covers $p=0$.</p>
<p>Now stop the critical exploration at $\tau_N(T)$, the first completed-component time at or after $H_N=\lfloor TN^{2/3}\rfloor$. Conditional on its history, the remaining graph is $G(M,p_N)$ with $M=N-\tau_N(T)\le N-H_N$, exactly as in CH8I. Its components are precisely those in the displayed late sum. The function $u^3/[2(1-u)^2]$ increases on $[0,1)$, so the conditional expectation is bounded by this function at $\mu_N=(N-H_N)p_N$. For sufficiently large $N$ it is subcritical, and</p>
<div class="math-display">$$
N^{1/3}(1-\mu_N)\longrightarrow T-\lambda,\qquad \mu_N\longrightarrow1.
$$</div>
<p>Multiply the bound by $N^{-2/3}$ and take the upper limit. No event concerning the future sizes or surpluses is included in the conditioning. $ \square$</p>

## The critical marked state in a weighted metric {#section-critical-weighted-marked-law}

<p>Let $\mathcal U$ consist of pairs $(x,y)$ with $x\in\ell^2_\downarrow$, $y_i\in\mathbb N_0$, $y_i=0$ whenever $x_i=0$, and $\sum_i x_i y_i<\infty$. Equip it with</p>
<div class="math-display">$$
d_{\mathcal U}((x,y),(x',y'))
=\|x-x'\|_2+\sum_{i\ge1}|x_i y_i-x'_i y'_i|.
$$</div>
<p>This is the metric in <a href="https://arxiv.org/pdf/1212.5493v1">Bhamidi–Budhiraja–Wang, (2.8)</a>. We retain M7BY's least-vertex rule for finite size ties; the limiting sizes are distinct. Equivalently, the metric is inherited from the embedding $(x,y)\mapsto(x,(x_i y_i)_i)$ into $\ell^2_\downarrow\times\ell^1$.</p>

<a id="tag-1QUE" data-assertion="theorem" data-title="Critical Erdős–Rényi sizes and surpluses converge in the size-weighted marked metric"></a>
<p>For every $\lambda_N\to\lambda\in\mathbb R$, the convergence in M7BY strengthens to</p>
<div class="math-display">$$
\bigl((N^{-2/3}L_{N,i})_i,(S_{N,i})_i\bigr)
\ \xrightarrow{\ d\ }\ ((\ell_i)_i,(Z_i)_i)
\qquad\text{in }(\mathcal U,d_{\mathcal U}).
$$</div>
<p>In particular, the Brownian marked state belongs to $\mathcal U$ almost surely, and</p>
<div class="math-display">$$
N^{-2/3}\sum_{\mathcal C}|\mathcal C|\sigma(\mathcal C)
\ \xrightarrow{\ d\ }\ \sum_i\ell_i Z_i<\infty.
$$</div>
<p>The latter is a distributional assertion. No convergence of its expectations is asserted. The limiting late-excursion contribution satisfies the additional bound</p>
<div class="math-display">$$
\mathbb E\sum_{(u,v):\,u>T}(v-u)\Pi((u,v))
\le \frac1{2(T-\lambda)^2}
\qquad(T>\max\{\lambda,0\}),
$$</div>
<p>where $\Pi$ is the exploration mark measure of GGL3.</p>
<p><em>Proof.</em> First match excursions whose start is in $(T,U)$ and whose length exceeds a fixed $d>0$. Their lengths and mark counts converge jointly by 59NH and GGL3. Fatou's lemma and RJJ9 bound the expectation of the limiting weighted sum by $1/[2(T-\lambda)^2]$. Increase $U$ to infinity and decrease $d$ to zero. The cutoffs carry no limiting boundary excursion almost surely, by 2N9T, and monotone convergence proves the late bound.</p>
<p>All excursions starting before $T$ end before the first zero after $T$. This time is finite almost surely. On that random compact interval the total number of marks is finite, and the excursion lengths are bounded. Their weighted mark sum is therefore finite. Together with the late bound, this proves $\sum_i\ell_iZ_i<\infty$.</p>
<p>To control small finite components, set $x_{N,i}=N^{-2/3}L_{N,i}$ and $y_{N,i}=S_{N,i}$. Split the weighted sum over components of mass at most $d$ according to whether their exploration starts before $H_N$ or afterwards. The second part has the expectation bound RJJ9. On $\{\tau_N(T)\le\lfloor UN^{2/3}\rfloor\}$ the first is at most</p>
<div class="math-display">$$
d\,\Pi_N([0,U]).
$$</div>
<p>For fixed $T$, the completion times are tight by CH8I. For fixed $U$, the mark counts are tight by GGL3. Given a positive error tolerance, choose $T$ large to control the late sum by Markov's inequality, then $U$ large to contain the completion time with high probability, and finally $d$ small to control the early sum. Hence, for every $\eta>0$,</p>
<div class="math-display">$$
\lim_{d\downarrow0}\limsup_{N\to\infty}
\mathbb P\!\left(\sum_{i:\,x_{N,i}\le d}x_{N,i}y_{N,i}>\eta\right)=0.
$$</div>
<p>We need a tail in rank, not just in size. M7BY makes $\sum_i x_{N,i}^2$ tight. Since $x_{N,K+1}>d$ implies $\sum_i x_{N,i}^2>(K+1)d^2$, the last display gives</p>
<div class="math-display">$$
\lim_{K\to\infty}\limsup_{N\to\infty}
\mathbb P\!\left(\sum_{i>K}x_{N,i}y_{N,i}>\eta\right)=0.
$$</div>
<p>Indeed, first fix a small $d$ and then increase $K$. This step allows components to be reordered without treating their marks as an unweighted summable sequence.</p>
<p>Use M7BY to couple the full size and product-mark vectors so that the size vectors converge in $\ell^2$ and each mark coordinate converges almost surely. The integer mark coordinates are then eventually equal at each fixed rank, and the products $x_{N,i}y_{N,i}$ converge for every fixed $i$. Their rank tails are negligible in probability by the preceding estimate. The limiting products have a vanishing $\ell^1$ tail because their sum is finite. Splitting the $\ell^1$ distance at rank $K$ proves convergence of the product vectors in $\ell^1$ in probability. Thus the coupled $d_{\mathcal U}$ distance tends to zero in probability, which gives the asserted weak convergence. Summation is continuous in $\ell^1$, proving the scalar conclusion. $ \square$</p>

## Surplus inherited through later mergers {#section-critical-inherited-surplus}

<p>Once the initial marked tail is controlled, it must remain small as its components merge. For this purpose, keep only chosen initial marks and create no new ones. Their counts add at mergers. This describes the contribution of old surplus even when the graph also acquires new cycle edges.</p>

<a id="tag-NH8N" data-assertion="proposition" data-title="An initially negligible size-weighted mark tail stays negligible through bounded coalescent time intervals"></a>
<p>Start a finite multiplicative coalescent from masses $x_i\ge0$ carrying nonnegative marks $r_i$, with $r_i=0$ when $x_i=0$. For each current block $B$, write $X_B=\sum_{i\in B}x_i$, $R_B=\sum_{i\in B}r_i$, and put</p>
<div class="math-display">$$
S(t)=\sum_B X_B(t)^2,\qquad
H(t)=\sum_B X_B(t)R_B(t),\qquad
\tau_M=\inf\{t:S(t)>M\}.
$$</div>
<p>For $M,T,\eta>0$,</p>
<div class="math-display">$$
\mathbb EH(T\wedge\tau_M)\le e^{MT}H(0),\qquad
\mathbb P\!\left(\sup_{0\le t\le T}H(t)>\eta,\ S(T)\le M\right)
\le\frac{e^{MT}H(0)}{\eta}.
$$</div>
<p>The second bound also holds for countably many initial masses $x\in\ell^2$ with $\sum_i x_i r_i<\infty$, in the edge-clock construction of 3G0K. In that construction $H(t)$ is finite almost surely on every bounded time interval. The bound applies to marks selected from any specified initial tail.</p>
<p>In particular, in the common-edge critical graph process on $[a,b]$, retain only surplus marks belonging to initial components of rank greater than $K$ at parameter $a$. If $H_{N,K}(\lambda)$ is their size-weighted contribution at parameter $\lambda$, with sizes normalized by $N^{-2/3}$, then</p>
<div class="math-display">$$
\lim_{K\to\infty}\limsup_{N\to\infty}
\mathbb P\!\left(\sup_{\lambda\in[a,b]}H_{N,K}(\lambda)>\eta\right)=0
\qquad(\eta>0).
$$</div>
<p><em>Proof.</em> Both $S$ and $H$ increase at mergers. If blocks with masses $u,v$ and marks $r,s$ merge, the increment of $H$ is $us+vr$, and the merger rate is $uv$. Thus its generator satisfies the exact identity</p>
<div class="math-display">$$
\mathcal L H
=\sum_{B<D}X_BX_D(X_BR_D+X_DR_B)
=SH-\sum_B X_B^3R_B
\le SH.
$$</div>
<p>Before $\tau_M$ the last expression is at most $MH$. Dynkin's formula stopped at $\tau_M$, followed by Gronwall's inequality, gives $\mathbb EH(t\wedge\tau_M)\le e^{Mt}H(0)$. The jump crossing $M$ is included in the stopped value; its drift is evaluated in the state before that jump. If $S(0)>M$, the stopping time is zero and the estimate is immediate. On $\{S(T)\le M\}$ no crossing occurs before $T$. Monotonicity of $H$ and Markov's inequality give the probability bound.</p>
<p>For countably many masses, restrict the edge-clock graph to its first $n$ vertices and retain their marks. The resulting $S^{[n]}(T)$ increases to the finite $S(T)$ by 3G0K. Also</p>
<div class="math-display">$$
H^{[n]}(T)
=\sum_{i,j\le n}r_i x_j\,
\mathbf1_{\{i\leftrightarrow j\text{ using vertices }1,\ldots,n\}}
\uparrow
\sum_{i,j\ge1}r_i x_j\,\mathbf1_{\{i\leftrightarrow j\}}
=H(T).
$$</div>
<p>Every connection has a finite witnessing path, which justifies the monotone limit. Since $\{S(T)\le M\}\subseteq\{S^{[n]}(T)\le M\}$, the finite probability bounds pass to this limit with $H^{[n]}(0)\le H(0)$. Letting $\eta\to\infty$ and then $M\to\infty$ proves $H(T)<\infty$ almost surely. Monotonicity and integer terminal times give finiteness simultaneously on all bounded intervals. Replacing $r_i$ by $r_i\mathbf1_{\{i>K\}}$ gives the same bound with initial value $\sum_{i>K}x_i r_i$. This tends to zero, so the inherited tail vanishes uniformly on $[0,T]$ in probability.</p>
<p>For the critical graph, condition on the graph at $a$. Its subsequent component partition is the finite coalescent under the exact deterministic time change in 6TZO. For all sufficiently large $N$ its elapsed time up to $b$ is at most $2(b-a)$. The marks under consideration are inherited initial surpluses; later internal edges do not alter them. Consequently, for every $d,M>0$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbb P\!\left(\sup_{\lambda\in[a,b]}H_{N,K}(\lambda)>\eta\right)
&\le \mathbb P\bigl(H_{N,K}(a)>d\bigr)
+\mathbb P\bigl(S_N(b)>M\bigr)
+\frac{e^{2M(b-a)}d}{\eta}.
\end{aligned}
$$</div>
<p>The initial rank-tail estimate is 1QUE; the terminal squared masses are tight by TIGK. First choose $M$ large, then $d$ small, and finally $K$ large, taking the upper limit in $N$ at the displayed bound. This proves the last assertion. $ \square$</p>
<p>The source comparison is <a href="https://arxiv.org/pdf/1212.5493v1">Bhamidi–Budhiraja–Wang, Proposition 4.5 and Lemmas 4.6–4.7</a>, which treat inherited surplus. The direct linear drift estimate here also gives a quantitative bound for a selected initial tail. These results settle initial weighted-tail control and its persistence through mergers. A full ranked marked-process limit still needs the joint identification of component ancestry and the allocation of new cycle marks, together with its path-topology argument.</p>



## Following specified components {#section-coalescent-labelled-components}

<p>For a vertex label $i$ of the edge-clock graph, let $A_i(x,t)$ be the mass of its component. Retaining the label records its ancestry when other components merge into it. This information is not contained in convergence of the ranked mass vector alone.</p>

<a id="tag-V90S" data-assertion="proposition" data-title="Common edge clocks preserve the masses, connections and ranks of finitely many positive-mass labels under l2 approximation"></a>
<p>Suppose $x^{(n)}\to x$ in $\ell^2_\downarrow$ and $t_n\to t\ge0$, with $t_n\ge0$. Use the common exponential clocks of 3G0K. For every finite collection of labels with $x_i>0$, their component masses at $t_n$ converge in probability to their component masses at $t$, and their pairwise connectivity indicators converge in probability. If the positive component masses at $t$ are almost surely distinct, each such label also has the same component rank in the two graphs with probability tending to one.</p>
<p><em>Proof.</em> Write $S_n=S(x^{(n)},t_n)$, and let $S_n^{[k]}$ be the squared mass after restriction to labels $1,\ldots,k$. For a retained label, write $a_{n,i}^{[k]}$ for its component mass in that restriction. The following deterministic bound is useful:</p>
<div class="math-display">$$
0\le A_i(x^{(n)},t_n)-a_{n,i}^{[k]}
\le\frac{S_n-S_n^{[k]}}{2a_{n,i}^{[k]}}.
$$</div>
<p>Indeed, inside the full component containing the retained component of mass $a$, write $A$ for its total mass and $c_j$ for the masses of its other restricted components. Then $\sum_jc_j\le A-a$, and its contribution to the squared-mass difference is at least $A^2-a^2-\sum_jc_j^2\ge2a(A-a)$. All other contributions are nonnegative.</p>
<p>For fixed $k$, the restricted edge indicators stabilize almost surely and their masses converge. The common-clock proof of 7HLE gives $S(x^{(n)},s)\to S(x,s)$ in probability at each fixed $s$. It also applies to $t_n$: squeeze between fixed times $t-h$ and $t+h$, then let $h\downarrow0$, using the absence of fixed-time jumps proved in GRSC and right continuity in probability. At zero use the small-time bound in 3G0K. Thus $S_n\to S(x,t)$ in probability, and for fixed $k$ the difference $S_n-S_n^{[k]}$ converges in probability to $S(x,t)-S(x^{[k]},t)$. The latter decreases to zero as $k\to\infty$. Since $a_{n,i}^{[k]}\ge x_i^{(n)}\to x_i>0$, the displayed bound proves convergence of labelled component masses.</p>
<p>If two labels are connected in the limit, one finite path witnesses this and persists eventually. If they are disconnected in the limit but connected in the approximating full graph, their restricted components are separate for each fixed sufficiently large $k$ and all sufficiently large $n$. Joining these two components costs at least $2a_{n,i}^{[k]}a_{n,j}^{[k]}$ in the squared-mass difference. This is bounded away from zero, whereas that difference becomes arbitrarily small in probability by first taking $n\to\infty$ and then $k\to\infty$. This proves the connectivity assertion.</p>
<p>Finally, a positive component mass has a finite rank in a square-summable list. If it differs from every other mass, its gaps to the adjacent ranks are positive. Convergence of the ranked vectors in $\ell^2$, together with convergence of the labelled mass, identifies this rank with probability tending to one. Localizing on a positive lower bound for these random gaps justifies the same argument when the limiting masses are random. A finite union handles all chosen labels. $ \square$</p>

## A Poisson construction carrying the marks {#section-augmented-coalescent-construction}

<p>For this construction, order equal masses by decreasing mark count, and let $\mathcal U^0$ be the resulting subset of $\mathcal U$. This makes the ranked state independent of the names of its vertices. The critical limiting masses have no ties; the finite-graph tie convention will be addressed below.</p>
<p>Give each unordered pair $i<j$ an independent unit-rate Poisson process, and put an edge between them at each point divided by $x_ix_j$. Give each vertex a separate unit-rate process whose points, divided by $x_i^2/2$, give loops. A zero rate produces no points. All processes are independent. The first point on each non-loop pair gives precisely the common exponential-clock graph of 3G0K. Further points create multiple edges. A proposal is a <em>birth</em> if it is a loop or its endpoints were already connected strictly before its arrival. Record its time and an endpoint label, so that the resulting mark can be followed through later mergers.</p>

<a id="tag-KBJ8" data-assertion="theorem" data-title="Countable Poisson proposals construct the augmented coalescent and finite restrictions capture all new births with high probability"></a>
<p>For $(x,y)\in\mathcal U^0$, give initial vertex $i$ its $y_i$ old marks and add one mark at each birth. At every finite time the ranked mass/mark state $Z((x,y),t)$ belongs to $\mathcal U^0$ almost surely. These constructions define measurable Markov kernels $Q_t$ satisfying $Q_{s+t}=Q_sQ_t$. In a finite state, masses $u,v$ merge at rate $uv$, their marks add, and a mass $u$ gains a new mark at rate $u^2/2$.</p>
<p>Let $Q_x(T)$ count births by time $T$, and let $Q_x^{[k]}(T)$ count births in the induced construction on the first $k$ labels, using the same Poisson processes. Then $Q_x^{[k]}(T)\uparrow Q_x(T)<\infty$ almost surely. With $S(s)=S(x,s)$ and $S^{[k]}(s)=S(x^{[k]},s)$, for $M,T>0$,</p>
<div class="math-display">$$
\mathbb P\bigl(Q_x(T)\ne Q_x^{[k]}(T)\bigr)
\le \mathbb P(S(T)>M)
+\frac12\int_0^T\mathbb E\min\{M,S(s)-S^{[k]}(s)\}\,ds.
$$</div>
<p>If $x^{(n)}\to x$ in $\ell^2_\downarrow$, the same constructions satisfy</p>
<div class="math-display">$$
\lim_{k\to\infty}\limsup_{n\to\infty}
\mathbb P\bigl(Q_{x^{(n)}}(T)\ne Q_{x^{(n)}}^{[k]}(T)\bigr)=0.
$$</div>
<p><em>Proof.</em> First take finitely many vertices. In a component of mass $u$, the sum of the rates of all its internal pair proposals and loops is</p>
<div class="math-display">$$
\sum_{\substack{i<j\\i,j\text{ in the component}}}x_ix_j
+\frac12\sum_{i\text{ in the component}}x_i^2
=\frac{u^2}{2}.
$$</div>
<p>Between two different components the rate is the product of their masses. Every birth of a restriction is also a birth of the full graph: its preceding connecting path remains present. The discrepancy count is therefore increasing, and its predictable rate is exactly $(S-S^{[k]})/2$. Stop at the first time $S>M$. Before this time the rate is at most $\min\{M,S-S^{[k]}\}/2$. Compensation and Markov's inequality give the displayed estimate, with $\mathbb P(S(T)>M)$ accounting for a crossing. The same argument for the total count gives</p>
<div class="math-display">$$
\mathbb P(Q_x(T)>L,\ S(T)\le M)\le\frac{MT}{2L}
\qquad(L>0).
$$</div>
<p>For countably many vertices, take increasing finite restrictions. Every birth in the full proposal graph has a finite preceding path, unless it is a loop, and hence occurs as a birth in a sufficiently large restriction. Thus the birth counts increase to the full count. Since the full $S(T)$ is finite by 3G0K, the last bound, first with $L\to\infty$ and then $M\to\infty$, proves finiteness of that count. The discrepancy estimate passes from a larger finite restriction to the full graph by monotone convergence. In particular, for a fixed graph all births up to $T$ eventually occur in its restrictions, with the same proposal identities and times.</p>
<p>For the uniform approximation assertion, use common unit-rate Poisson processes; their first points are the common exponentials in 7HLE. For each fixed $k,s$, the difference $S(x^{(n)},s)-S((x^{(n)})^{[k]},s)$ converges in probability to $S(x,s)-S(x^{[k]},s)$. The integrand capped at $M$ is bounded, so its expectations and time integrals converge. The limiting difference decreases to zero as $k\to\infty$. Also $S(x^{(n)},T)\to S(x,T)$ in probability. Take the upper limit in $n$, then $k\to\infty$, and finally $M\to\infty$ through continuity points of the terminal squared-mass law. This proves the assertion.</p>
<p>Inherited marks have finite weighted sum by NH8N. New marks have weighted sum at most $\sqrt{S(T)}Q_x(T)$ at every time up to $T$. Hence all marked states have finite weighted sum, simultaneously on bounded intervals. Every positive-mass component has only finitely many marks. The construction is measurable: connections have finite witnesses, masses and marks are nonnegative countable sums, and ranking with the stated tie rule is measurable.</p>
<p>At a deterministic time, independent Poisson increments leave the future proposal processes independent of the past. Superposing them between current components gives rate $uv$, and superposing those within one component gives rate $u^2/2$. These rates are finite for every component or pair. The superpositions for distinct pairs and internal components use disjoint original processes. The future therefore has the same construction started from the current ranked masses and mark counts. This proves the Markov and semigroup assertions also for countably many components. It does not assert continuity of the kernels or a topology on their paths. $ \square$</p>

## Joint convergence with inherited and new marks {#section-augmented-coalescent-finite-times}

<a id="tag-4DZC" data-assertion="theorem" data-title="Finite marked initial approximations converge jointly at fixed observation times whose limiting component masses have no ties"></a>
<p>Let $z_n=(x^{(n)},y^{(n)})\in\mathcal U^0$ have finitely many positive masses, and suppose $z_n\to z=(x,y)$ in $d_{\mathcal U}$, with $x_i>0$ for every $i$. Fix $0<t_1<\cdots<t_m$, and suppose the positive component masses of $Z(z,t_j)$ are almost surely distinct for every $j$. If $t_{n,j}\ge0$ and $t_{n,j}\to t_j$, then, under the common unit-rate Poisson construction,</p>
<div class="math-display">$$
\max_{1\le j\le m}
d_{\mathcal U}\bigl(Z(z_n,t_{n,j}),Z(z,t_j)\bigr)
\ \xrightarrow{\ \mathbb P\ }\ 0.
$$</div>
<p>The initial states may be included in the joint vector. The no-ties assumption is imposed at the observation times; no assertion is made here that it holds for every initial state or every random time.</p>
<p><em>Proof.</em> The mass vectors converge in probability at all the observation times by the common-clock argument in V90S. It remains to match the mass-times-mark sequences. Throughout the following decomposition keep each graph's full-state rank order when separating contributions from different marks.</p>
<p>Fix a finite initial rank $k$. Because $x_i>0$, convergence of $x_i^{(n)}y_i^{(n)}$ and $x_i^{(n)}$ implies $y_i^{(n)}=y_i$ eventually for $i\le k$. These are finitely many old marks. By V90S, their carrying components have convergent masses and eventually matching ranks, in probability, at all observation times. Thus their contribution to the $\ell^1$ distance of the weighted mark sequences tends to zero.</p>
<p>The old marks with initial labels greater than $k$ contribute a negligible error. Indeed, $d_{\mathcal U}(z_n,z)\to0$ implies</p>
<div class="math-display">$$
\lim_{k\to\infty}\limsup_{n\to\infty}
\sum_{i>k}x_i^{(n)}y_i^{(n)}=0.
$$</div>
<p>Apply NH8N on an interval $[0,T]$ containing all the observation times. The terminal squared masses are tight by 7HLE. First localize them at a large $M$, then take the initial weighted tail small. The old tail is consequently negligible uniformly over $[0,T]$, for both the approximating and limiting constructions. At the fixed full-state ranks, these discarded marks form a nonnegative weighted sequence whose $\ell^1$ norm is exactly their transported contribution. No reordering after deletion is needed.</p>
<p>For new marks, KBJ8 shows that, with probability tending to one as $k$ increases after $n$, every birth up to $T$ occurs already in the first-$k$ restriction. The same holds for the limiting graph. On a fixed finite set of labels, the unit-rate Poisson processes contain only finitely many relevant points before $T$ for all large $n$. The corresponding physical proposal times converge as their rates converge. Almost surely no two limiting proposal times coincide and none is an observation time. Their order, and hence their classification as births or mergers, therefore agrees eventually, including at the varying times $t_{n,j}$.</p>
<p>Match these births by their Poisson point identities, recording an endpoint label of each. There are finitely many, and all recorded labels are at most $k$. Their component ranks and masses at the observation times converge by V90S. The weighted mark sequences they contribute therefore converge in $\ell^1$ in probability. This follows first when the finite number of proposals is bounded by a deterministic constant, and then without the bound by tightness of the finite-restriction count.</p>
<p>Combining the finitely many old marks, the negligible old tail and the matched new marks proves convergence of the full weighted sequences. The argument uses label ancestry rather than comparing ranks in a truncated graph with ranks in the full graph. A finite union over observation times finishes the proof. $ \square$</p>

## Ranked sizes and surpluses at several critical parameters {#section-critical-augmented-parameter-law}

<p>Write $\nu_\lambda$ for the Brownian marked-state law in 1QUE. For the next statement, sort equal-size finite components by decreasing surplus; ties remaining after that do not change the mass/mark vector.</p>

<a id="tag-JSGY" data-assertion="theorem" data-title="Critical Erdős–Rényi sizes and surpluses converge jointly at every finite list of parameters to the standard augmented coalescent"></a>
<p>In the common-uniform-edge graph process, let $Z_N(\lambda)$ be the ranked vector of $N^{-2/3}$ times the component sizes and their surplus counts. For every finite list $\lambda_0<\cdots<\lambda_m$,</p>
<div class="math-display">$$
\bigl(Z_N(\lambda_0),\ldots,Z_N(\lambda_m)\bigr)
\ \xrightarrow{\ d\ }\
\bigl(Z(\lambda_0),\ldots,Z(\lambda_m)\bigr)
\qquad\text{in }\mathcal U^{m+1},
$$</div>
<p>where the first limit state has law $\nu_{\lambda_0}$ and the successive transitions are $Q_{\lambda_j-\lambda_{j-1}}$ from KBJ8. These laws are consistent, with</p>
<div class="math-display">$$
\nu_\lambda Q_h=\nu_{\lambda+h}\qquad(\lambda\in\mathbb R,\ h\ge0).
$$</div>
<p>They define the finite-dimensional laws of the standard augmented multiplicative coalescent. The same convergence holds with the least-vertex tie rule of M7BY.</p>
<p><em>Proof.</em> The case of one parameter is 1QUE, with the tie comparison below. For two or more parameters, first compare the simple graph with the Poisson construction. Start at $a=\lambda_0$ with its actual graph, and give each original vertex mass $\delta_N=N^{-2/3}$. After time zero, propose each unordered non-loop edge at rate $\delta_N^2$ and each loop at rate $\delta_N^2/2$. In the simple graph, accept only the first proposal on an absent non-loop edge. In the augmented construction, record every internal proposal, including loops and proposals on edges already present, as a new mark. Both constructions have exactly the same component partition. Aggregate the initial components: distinct masses merge at their product, and the full internal-proposal rate of a component of mass $u$ is $u^2/2$. Thus the augmented process is precisely KBJ8 started from $Z_N(a)$.</p>
<p>Use the exact clock change</p>
<div class="math-display">$$
u_N(\lambda)=N^{4/3}\log\frac{1-p_N(a)}{1-p_N(\lambda)},
\qquad u_N(\lambda)\longrightarrow\lambda-a.
$$</div>
<p>For $b=\lambda_m$, the expected number of extra marks in the augmented construction is at most</p>
<div class="math-display">$$
\delta_N^2u_N(b)
\left[\binom N2p_N(b)+\frac N2\right]
=O_{a,b}(N^{-1/3}).
$$</div>
<p>The first term bounds repeated proposals using the predictable number of present edges, as in 6TZO; the second counts loops. Hence, with probability tending to one, the simple and augmented marked states agree throughout this interval. Initial surplus marks agree exactly.</p>
<p>By 1QUE, $Z_N(a)\Rightarrow\nu_a$ in the weighted metric. This remains true after changing the finite tie rule. To check it, retain components above a fixed positive mass cutoff. Their limiting masses are distinct, so their rank order eventually agrees under both rules. The weighted mark sum of the remaining small components is negligible by 1QUE, and their mass vector is unchanged by the rule. Let the cutoff decrease to zero.</p>
<p>Couple the initial states to converge almost surely, using their embedding in $\ell^2_\downarrow\times\ell^1$, and take independent common future Poisson processes. Almost surely every coordinate of the limiting initial mass vector is positive. At each later observation time the limiting mass vector has law $\mu_{\lambda_j}$ by Z8T1, so its positive masses are distinct almost surely by 2N9T. Conditional on the coupled initial states, 4DZC therefore applies for almost every realization. Bounded convergence removes the conditioning. The varying observation times are $u_N(\lambda_j)$, so this proves the joint limit for the augmented approximations. The preceding error probability transfers it to the simple graph.</p>
<p>Comparison with 1QUE at the later parameter gives $\nu_\lambda Q_h=\nu_{\lambda+h}$. The semigroup property of KBJ8 then makes the finite-dimensional laws consistent when a parameter is inserted or removed. The marked state space is a Borel subspace of $\ell^2_\downarrow\times\ell^1$ under the stated embedding, so the Kolmogorov extension theorem supplies the eternal Markov process with these laws. Finally, applying the tie-rule comparison at each of the finitely many parameters gives the least-vertex version as well. $ \square$</p>
<p>This identifies the joint evolution at every finite set of parameters, including which components inherit old surplus and receive new cycle marks. It does not prove convergence in a marked path space or represent all parameters using one Brownian path. The source comparison is <a href="https://arxiv.org/pdf/1212.5493v1">Bhamidi–Budhiraja–Wang, Section 4.2</a>; the proof here uses labelled components, the transported initial tail and a stopped birth-discrepancy estimate, with the simple-graph comparison written explicitly.</p>




## Exponentially growing size-path observables {#section-critical-exponential-observables}

<p>The polynomial moment theorem can now be strengthened using the explicit coefficient bound <a href="/tag/81TZ/">81TZ</a>. Fix $a<b$, choose $\Lambda\ge\max\{|a|,|b|\}$, and let $K_\Lambda$ be the susceptibility constant in A40L. Write</p>
<div class="math-display">$$
\kappa_\Lambda=\max\{K_\Lambda,K_\Lambda^4\},
\qquad r_\Lambda=(8\kappa_\Lambda)^{-1/2}.
$$</div>

<a id="tag-NROY" data-assertion="theorem" data-title="Critical size paths converge against observables of sufficiently small exponential growth in their maximum l2 norm"></a>
<p>For $0\le r<r_\Lambda$, the critical size paths satisfy</p>
<div class="math-display">$$
\mathbb E\exp\!\left(r\sup_{\lambda\in[a,b]}
\|\mathbf L_N(\lambda)\|_2\right)
\le\frac{2}{1-8\kappa_\Lambda r^2},
\qquad
\mathbb E\exp\!\left(r\sup_{\lambda\in[a,b]}
\|\mathbf X(\lambda)\|_2\right)
\le\frac{2}{1-8\kappa_\Lambda r^2}.
$$</div>
<p>The finite bound holds for every $N\ge2$ for which the whole parameter interval is admissible. If a Borel function $\Phi:D([a,b],E)\to\mathbb R$ is $J_1$-continuous at almost every limiting path and</p>
<div class="math-display">$$
|\Phi(x)|\le A\exp\!\left(r\sup_{\lambda\in[a,b]}\|x(\lambda)\|_2\right)
$$</div>
<p>for some finite $A$ and $0\le r<r_\Lambda$, then
$\mathbb E\Phi(\mathbf L_N)\to\mathbb E\Phi(\mathbf X)$.</p>
<p>In particular, with the squared-mass integrals $I_N,I$ of KCRC,</p>
<div class="math-display">$$
\mathbb E e^{\theta\sqrt{I_N}}\longrightarrow
\mathbb E e^{\theta\sqrt I}<\infty
\qquad\left(0\le\theta<r_\Lambda/\sqrt{b-a}\right).
$$</div>
<p><em>Proof.</em> The squared norm increases when components merge, so the supremum in either process is its norm at $b$. A40L and 81TZ give the finite bound. The terminal-state convergence in TIGK and Fatou's lemma give the limiting bound.</p>
<p>Choose $r'$ strictly between $r$ and $r_\Lambda$. If $r>0$, the preceding estimate at $r'$ bounds a moment of $|\Phi(\mathbf L_N)|$ of order $r'/r>1$; hence these variables are uniformly integrable. For $r=0$ they are bounded. The almost-sure-continuity form of the continuous mapping theorem, followed by uniform integrability, proves the expectation limit.</p>
<p>On a $J_1$-convergent sequence the paths have uniformly bounded norms, and their values converge at every continuity time of the limit. Dominated convergence therefore makes $x\mapsto\int_a^b\|x(\lambda)\|_2^2\,d\lambda$ continuous. Its square root is at most $\sqrt{b-a}\sup_\lambda\|x(\lambda)\|_2$, proving the last assertion. $ \square$</p>

## Exponential square-root bounds for new cycles {#section-critical-cycle-root-exponential}

<p>Let $C_N=C_N(b)$ and $C=C(b)$ count the new cycle births after $a$, as in M7RY. These counts exclude the surplus already present at $a$.</p>

<a id="tag-L1PJ" data-assertion="theorem" data-title="Integrated squared mass and new cycle counts have convergent joint exponential square-root transforms"></a>
<p>For $\alpha,\beta\ge0$ with $(\alpha+\beta)\sqrt{b-a}<r_\Lambda$,</p>
<div class="math-display">$$
\mathbb E e^{\alpha\sqrt{I_N}+\beta\sqrt{C_N}}
\longrightarrow
\mathbb E e^{\alpha\sqrt I+\beta\sqrt C}<\infty.
$$</div>
<p>More precisely, put</p>
<div class="math-display">$$
D_\beta=1+\beta\int_0^\infty e^{\beta u-u^2}\,du.
$$</div>
<p>For all sufficiently large $N$, and also for the limiting pair, the expectation above is at most</p>
<div class="math-display">$$
\frac{2D_\beta}
{1-8\kappa_\Lambda(b-a)(\alpha+\beta)^2}.
$$</div>
<p><em>Proof.</em> We first record a bound uniform in a Poisson mean $v\ge0$. If $P_v$ is Poisson with mean $v$, Chernoff's inequality gives, for $u\ge0$,</p>
<div class="math-display">$$
\mathbb P\!\left(\sqrt{P_v}-\sqrt v>u\right)\le e^{-u^2}.
$$</div>
<p>When $v=0$ this is immediate. For $v>0$, optimize the exponential Markov bound at a real threshold $q\ge v$ to obtain exponent $q\log(q/v)-q+v$. This is at least $(\sqrt q-\sqrt v)^2$: putting $w=\sqrt{q/v}\ge1$, their difference is $2vw(w\log w-w+1)\ge0$. Apply this at $q=(\sqrt v+u)^2$; integer thresholds only improve the bound. Integrating the tail of $(\sqrt{P_v}-\sqrt v)_+$ yields</p>
<div class="math-display">$$
\mathbb E e^{\beta\sqrt{P_v}}\le D_\beta e^{\beta\sqrt v}.
$$</div>
<p>The integral defining $D_\beta$ is finite for every finite $\beta\ge0$.</p>
<p>Use the loop-free proposal coupling of 6TZO. Conditionally on the size path, its total count $Q_N([a,b])$ is Poisson with mean</p>
<div class="math-display">$$
J_N=\frac12\int_a^b
\bigl[S_N(\lambda)-N^{-1/3}\bigr]u_N'(\lambda)\,d\lambda.
$$</div>
<p>For large $N$, $u_N'\le2$, so $J_N\le(b-a)S_N(b)$.
Also $I_N\le(b-a)S_N(b)$ and $C_N\le Q_N([a,b])$. Conditional expectation and the Poisson bound therefore give</p>
<div class="math-display">$$
\mathbb E e^{\alpha\sqrt{I_N}+\beta\sqrt{C_N}}
\le D_\beta\,
\mathbb E e^{(\alpha+\beta)\sqrt{b-a}\,\|\mathbf L_N(b)\|_2}.
$$</div>
<p>NROY proves the displayed quantitative bound. In the limit, the conditional mean of $C$ is $I/2$ by 6248, and $I\le(b-a)\|\mathbf X(b)\|_2^2$, so the same bound applies.</p>
<p>Choose $p>1$ such that $p(\alpha+\beta)\sqrt{b-a}<r_\Lambda$. The same estimate at $p\alpha,p\beta$ gives uniform integrability of the exponential variables; if both parameters vanish, the assertion is immediate. The joint convergence $(I_N,C_N)\Rightarrow(I,C)$ from M7RY and continuity of the exponential square-root function now give convergence of expectations. $ \square$</p>
<p>These bounds concern square roots of the integrated mass and the new cycle count. No positive exponential moment of $I$ or $C$ themselves is deduced from them.</p>

## The mixed moments determine the cycle law {#section-critical-cycle-moment-determinacy}

<a id="tag-NM14" data-assertion="corollary" data-title="The mixed moments uniquely determine the joint law of integrated squared mass and new critical cycle births"></a>
<p>The law of $(I,C)$ on $[0,\infty)^2$ is uniquely determined by its mixed moments
$\mathbb E[I^jC^k]$, $j,k\ge0$. In particular the moment limits in M7RY identify this joint law among all probability laws on the nonnegative quadrant, without first assuming that the second coordinate is integer-valued.</p>
<p><em>Proof.</em> L1PJ gives $\mathbb E e^{\varepsilon(\sqrt I+\sqrt C)}<\infty$ for a sufficiently small $\varepsilon>0$. Let $(I',C')$ be any nonnegative pair with the same mixed moments. Tonelli's theorem and the nonnegative even series show that</p>
<div class="math-display">$$
\mathbb E\!\left[\cosh(\varepsilon\sqrt{I'})
                   \cosh(\varepsilon\sqrt{C'})\right]
=\sum_{j,k\ge0}
\frac{\varepsilon^{2j+2k}\mathbb E[I^jC^k]}{(2j)!(2k)!}
=\mathbb E\!\left[\cosh(\varepsilon\sqrt I)
                   \cosh(\varepsilon\sqrt C)\right]<\infty.
$$</div>
<p>Since $e^{u+v}\le4\cosh u\cosh v$ for $u,v\ge0$, the competing pair has the same kind of exponential square-root integrability.</p>
<p>Give each square root an independent uniform sign, independent of the pair. Every mixed moment of the resulting signed vectors is zero if either exponent is odd; their even mixed moments are the specified moments of $(I,C)$ and $(I',C')$. Exponential integrability of the sum of absolute coordinates makes their moment generating functions equal to their absolutely convergent Taylor series in a neighborhood of the origin. Those series agree. Uniqueness of the moment generating function, or its one-dimensional uniqueness applied to every linear projection followed by Cramér–Wold, identifies the signed-vector laws. Squaring their coordinates recovers the original laws. $ \square$</p>
<p>The argument uses the growth of the moments as well as their existence. The quantitative input is 81TZ, obtained by summing the cluster-partition bound; no new source passage or formal verification is asserted here.</p>




## Ordinary exponential moments of critical squared mass {#section-critical-squared-mass-mgf}

<p>For the complete graph, the cubic largest-component tail <a href="/tag/PMEN/">PMEN</a> supplies more than the general susceptibility argument. Combined with <a href="/tag/1NYQ/">the cluster-product bound</a>, it gives ordinary exponential moments of the squared norm, at every positive parameter.</p>

<a id="tag-7CDV" data-assertion="theorem" data-title="Critical complete-graph squared mass has uniformly bounded exponential moments of every positive order, with expectation convergence for exponentially growing path observables"></a>
<p>Fix $\Lambda\ge0$. For every $t\ge0$ there is a finite $F_\Lambda(t)$ such that</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
\mathbb E e^{t\|\mathbf L_N(\lambda)\|_2^2}
\le F_\Lambda(t),
\qquad
\sup_{|\lambda|\le\Lambda}
\mathbb E e^{t\|\mathbf X(\lambda)\|_2^2}
\le F_\Lambda(t).
$$</div>
<p>Consequently, fix $[a,b]\subseteq[-\Lambda,\Lambda]$, $a<b$. If $\Phi$ is Borel measurable on $D([a,b],E)$, is $J_1$-continuous at almost every limiting path, and satisfies</p>
<div class="math-display">$$
|\Phi(x)|\le A\exp\!\left(t\sup_{\lambda\in[a,b]}\|x(\lambda)\|_2^2\right)
$$</div>
<p>for some finite $A,t\ge0$, then
$\mathbb E\Phi(\mathbf L_N)\to\mathbb E\Phi(\mathbf X)$.
In particular, $\mathbb E e^{t I_N}\to\mathbb E e^{t I}<\infty$ for every $t\ge0$.</p>
<p><em>Proof.</em> Write $R_N=N^{-2/3}L_1$ and $S_N=\|\mathbf L_N\|_2^2$. We first obtain constants $A_\Lambda,c,C>0$ with</p>
<div class="math-display">$$
\mathbb P_{p_N(\lambda)}(R_N>u)\le Ce^{-cu^3}
\qquad(u\ge A_\Lambda,\ |\lambda|\le\Lambda),
$$</div>
<p>uniformly over admissible $N$. For large $N$, dominate the graph by
$G(N,p_N(\Lambda))$ and apply PMEN with $\varepsilon=\Lambda N^{-1/3}\le1$.
If $u\ge\max\{16,16\Lambda,1\}$, then $k=\lfloor uN^{2/3}\rfloor+1$ meets all the lower thresholds of PMEN. When $k>N$ the event is empty; otherwise its bound is at most $Ce^{-cu^3}$. For the finitely many smaller $N$, $R_N\le N^{1/3}$ deterministically. Enlarging $A_\Lambda$ covers them too. This also handles $\Lambda=0$ and all negative window parameters by monotonicity.</p>
<p>For $q\ge0$, integration of the tail gives</p>
<div class="math-display">$$
\mathbb E e^{qR_N^2}
\le B_\Lambda(q):=
e^{qA_\Lambda^2}
+2qC\int_{A_\Lambda}^\infty u e^{qu^2-cu^3}\,du<\infty.
$$</div>
<p>The cubic term dominates the quadratic term for every fixed $q$. At $q=0$ the bound is one. Meanwhile A40L and the $m=2$ case of YN7V give the explicit uniform estimate</p>
<div class="math-display">$$
\mathbb ES_N^2\le D_\Lambda:=K_\Lambda^2+3K_\Lambda^5.
$$</div>
<p>Indeed, the two partitions of two positions contribute $N^2M^2$ and $3NM^5$ before division by $N^{8/3}$. Apply 1NYQ with $a=N^{2/3}$. One valid choice is therefore</p>
<div class="math-display">$$
F_\Lambda(t)=
\exp\!\left\{t\sqrt{D_\Lambda B_\Lambda(2t)}\right\}.
$$</div>
<p>Fixed-parameter convergence and Fatou's lemma give the same bound for every limiting state, with the same constants throughout the interval.</p>
<p>The squared norm increases at mergers, so its path supremum is the terminal value for both processes. The estimate at any larger exponential parameter bounds a moment of $|\Phi(\mathbf L_N)|$ of order greater than one when $t>0$. For $t=0$ the variables are bounded. Uniform integrability and TIGK thus prove the expectation convergence. Finally the integral functional is $J_1$-continuous by the argument in NROY, and $I_N\le(b-a)S_N(b)$, with the same limiting inequality. Apply the result to the exponential of that integral. $ \square$</p>
<p>The additional input is the complete-graph cubic tail. The square-root estimate 81TZ continues to apply under the much more general uniform-susceptibility hypothesis.</p>

## Ordinary transforms of integrated mass and new cycles {#section-critical-joint-mgf}

<a id="tag-ME2X" data-assertion="theorem" data-title="Integrated critical squared mass and new cycle increments have convergent exponential transforms at every real pair of parameters"></a>
<p>For every $\alpha,\beta\in\mathbb R$,</p>
<div class="math-display">$$
\mathbb E e^{\alpha I_N+\beta C_N}
\longrightarrow
\mathbb E e^{\alpha I+\beta C}
=\mathbb E\exp\!\left[\left(\alpha+\frac{e^\beta-1}{2}\right)I\right]
<\infty.
$$</div>
<p>More generally, expectations converge for every continuous
$G:[0,\infty)^2\to\mathbb R$ satisfying
$|G(u,v)|\le A e^{r(u+v)}$ for finite $A,r\ge0$.
For $\alpha,\beta\ge0$ and all sufficiently large $N$,</p>
<div class="math-display">$$
\mathbb E e^{\alpha I_N+\beta C_N}
\le F_\Lambda\bigl((b-a)(\alpha+e^\beta-1)\bigr),
$$</div>
<p>where $\Lambda\ge\max\{|a|,|b|\}$ and $F_\Lambda$ is the bound in 7CDV. The same bound holds for the limiting pair.</p>
<p><em>Proof.</em> In the coupling of 6TZO, $C_N\le Q_N([a,b])$, and conditionally on the size path this proposal count is Poisson with mean $J_N$. As in L1PJ, for large $N$ one has</p>
<div class="math-display">$$
J_N\le(b-a)S_N(b),\qquad I_N\le(b-a)S_N(b).
$$</div>
<p>For nonnegative $\alpha,\beta$, condition on that path to obtain</p>
<div class="math-display">$$
\mathbb E e^{\alpha I_N+\beta C_N}
\le\mathbb E e^{\alpha I_N+(e^\beta-1)J_N}
\le\mathbb E e^{(b-a)(\alpha+e^\beta-1)S_N(b)}.
$$</div>
<p>This is bounded by 7CDV for every finite pair of parameters. In the limit, 6248 gives the conditional law $C\mid I\sim\operatorname{Poisson}(I/2)$, which proves the transform identity and the same bound. If a coefficient is negative, its positive part dominates the corresponding integrand, so all these transforms are still integrable.</p>
<p>Applying the finite bound at larger positive parameters gives uniform integrability of $G(I_N,C_N)$, and of each real exponential in the statement. The joint weak convergence in M7RY then gives convergence of expectations. The finitely many small admissible $N$ excluded from the proposal bound do not affect this conclusion. These cycle counts are increments over $(a,b]$; no initial surplus is included. $ \square$</p>

## Entire transforms and their derivatives {#section-critical-entire-transforms}

<a id="tag-0Y6N" data-assertion="corollary" data-title="The joint critical mass and cycle moment generating functions are entire and converge with all derivatives locally uniformly"></a>
<p>For complex $z,w$, put</p>
<div class="math-display">$$
M_N(z,w)=\mathbb E e^{zI_N+wC_N},\qquad
M(z,w)=\mathbb E e^{zI+wC}
=\mathbb E\exp\!\left[\left(z+\frac{e^w-1}{2}\right)I\right].
$$</div>
<p>These functions are entire on $\mathbb C^2$. For every pair of nonnegative integers $j,k$,</p>
<div class="math-display">$$
\partial_z^j\partial_w^k M_N(z,w)
=\mathbb E[I_N^jC_N^k e^{zI_N+wC_N}]
\longrightarrow
\mathbb E[I^jC^k e^{zI+wC}]
=\partial_z^j\partial_w^k M(z,w)
$$</div>
<p>uniformly on every compact subset of $\mathbb C^2$.</p>
<p><em>Proof.</em> ME2X bounds $\mathbb E e^{r(I_N+C_N)}$ uniformly for all sufficiently large $N$, for every fixed $r\ge0$, and gives the corresponding finite limit expectation. Each remaining finite graph has bounded mass and cycle count. On a complex compact set, every differentiated integrand is bounded by a polynomial in $I_N,C_N$ times $e^{r(I_N+C_N)}$ for some finite $r$. A larger exponential absorbs that polynomial. Differentiation under the expectation is therefore justified locally at every order, proving entire dependence and the derivative formulas. The conditional Poisson series, absolutely integrable under the same bound, proves the complex transform identity.</p>
<p>For completeness, the convergence is uniform, not just pointwise. Fix a compact set of complex parameters and a derivative order. Restrict the nonnegative pair $(u,v)$ using a continuous cutoff that is one on $u+v\le L$ and zero on $u+v\ge L+1$. The resulting integrands are bounded continuous functions of the pair and are uniformly Lipschitz in the complex parameters on the chosen compact set. Joint weak convergence gives convergence at each parameter; a finite parameter net makes it uniform. The discarded part is bounded uniformly in $N$ by</p>
<div class="math-display">$$
A_{j,k} e^{-L}\,
\mathbb E e^{(r+2)(I_N+C_N)},
$$</div>
<p>after using $u^jv^k\le A_{j,k}e^{u+v}$. The same estimate holds for the limit. Let $L\to\infty$ to prove locally uniform convergence of the derivatives. $ \square$</p>
<p>These upgrades settle ordinary exponential moments and transforms for squared mass and new cycle increments in the complete-graph window. They use the previously proved size-path and conditional-Poisson laws; convergence of the full ranked marked path and a common-Brownian representation remain separate.</p>




## Total weighted surplus after stopping times {#section-weighted-surplus-stopped}

<p>The total weighted surplus is insensitive to the ordering of equal-sized components. It therefore admits a path argument before the full ranked mark vector does. Write</p>
<div class="math-display">$$
H(t)=\sum_i X_i(t)Y_i(t),\qquad S(t)=\sum_iX_i(t)^2,
$$</div>
<p>for the augmented coalescent of KBJ8. Here $Y_i$ includes both inherited marks and new births. Both $S$ and $H$ increase.</p>

<a id="tag-0DWE" data-assertion="proposition" data-title="A stopped drift bound controls total weighted surplus and gives joint size and weighted-surplus path tightness"></a>
<p>For a finite augmented coalescent, the generator of $H$ is</p>
<div class="math-display">$$
\mathcal L H
=SH-\sum_i X_i^3Y_i+\frac12\sum_iX_i^3
\le SH+\frac12S^{3/2}.
$$</div>
<p>Let $\tau$ be a bounded stopping time. On $\{S(\tau)\le M,\ H(\tau)\le M\}$, for $M,\eta>0$ and $0<h\le(2M)^{-1}$,</p>
<div class="math-display">$$
\mathbb P\!\left(H(\tau+h)-H(\tau)>\eta
             \,\middle|\,\mathcal F_\tau\right)
\le 2Mh+\frac h\eta
       \left[2M(M+\eta)+\frac12(2M)^{3/2}\right].
$$</div>
<p>Consequently, consider a sequence of finite augmented coalescents on $[0,T]$. If their $(X_n(t),H_n(t))$ laws are tight for every deterministic $t$, and $S_n(T)+H_n(T)$ is tight, their joint paths are tight in
$D([0,T],\ell^2_\downarrow\times[0,\infty))$ with a single $J_1$ time change for both coordinates.</p>

<p><em>Proof.</em> When masses $u,v$ with marks $r,s$ merge, $H$ increases by $us+vr$, at rate $uv$. Summing gives $SH-\sum_iX_i^3Y_i$, as in NH8N. A birth in a component of mass $u$ increases $H$ by $u$, at rate $u^2/2$. This gives the remaining term. Finally $\sum_iX_i^3\le\sqrt S\sum_iX_i^2=S^{3/2}$.</p>
<p>Condition on the state at $\tau$ and measure elapsed time from there. The mass process does not depend on the marks. The squared-mass expectation bound used in O3IS gives</p>
<div class="math-display">$$
\mathbb E[S(\tau+h)-S(\tau)\mid\mathcal F_\tau]
\le \frac{hS(\tau)^2}{1-hS(\tau)}
\le 2hM^2.
$$</div>
<p>Since $S$ is increasing, the conditional probability that it exceeds $2M$ before $\tau+h$ is at most $2Mh$. Stop also when $H-H(\tau)$ first exceeds $\eta$. Before either crossing, the generator bound is at most
$2M(M+\eta)+(2M)^{3/2}/2$. Stopped Dynkin's formula therefore bounds the expected increment of $H$ at this stopping time, capped by $\tau+h$, by $h$ times this constant. The crossing jump is included; its drift is evaluated in the state before the jump. On the event that $H$ crosses its threshold without an earlier squared-mass crossing, this nonnegative increment exceeds $\eta$. Markov's inequality and the squared-mass crossing bound prove the displayed estimate. The finite construction is nonexplosive: its total mass is fixed, so the total proposal rate is bounded. Conditioning first on a finite initial state, or localizing that state, justifies the stopped formula for random initial data.</p>
<p>For tightness use the complete separable state-space metric</p>
<div class="math-display">$$
d((x,h),(x',h'))=
\left(\|x-x'\|_2^2+|h-h'|\right)^{1/2}.
$$</div>
<p>It induces the usual product topology. The square root of absolute distance is a metric, and combining it with the $\ell^2$ metric by the Euclidean norm proves the triangle inequality. With $R_n=S_n+H_n$, monotonicity and 3G0K give</p>
<div class="math-display">$$
d((X_n(s),H_n(s)),(X_n(t),H_n(t)))^2
\le R_n(t)-R_n(s)\qquad(s\le t).
$$</div>
<p>On $\{R_n(\tau)\le M\}$ both localized bounds apply. A $d$-displacement greater than $\varepsilon$ forces either an $\ell^2$ displacement greater than $\varepsilon/\sqrt2$, controlled by O3IS, or an $H$-increment greater than $\varepsilon^2/2$, controlled above. Both probabilities are $O_{M,\varepsilon}(h)$, uniformly over stopping times. The tightness criterion R8LD now applies in the product state space. In particular it supplies compact containment as well as the oscillation bound. $ \square$</p>

## A path limit for total weighted surplus {#section-critical-weighted-surplus-path}

<a id="tag-EURS" data-assertion="theorem" data-title="Critical component sizes and total size-weighted surplus converge jointly in Skorokhod path space"></a>
<p>Fix $a<b$ and use the common-edge critical Erdős–Rényi process. Put</p>
<div class="math-display">$$
H_N(\lambda)=N^{-2/3}\sum_{\mathcal C\text{ at }\lambda}
                      |\mathcal C|\sigma(\mathcal C),
$$</div>
<p>where $\sigma(\mathcal C)$ is the full surplus of the component, including cycles already present at $a$. Start the augmented coalescent at $a$ with law $\nu_a$, and put $H(\lambda)=\sum_iX_i(\lambda)Y_i(\lambda)$ in its graphical construction. This process has an increasing càdlàg version, finite on bounded intervals, and</p>
<div class="math-display">$$
(\mathbf L_N,H_N)\ \xrightarrow{\ d\ }\ (\mathbf X,H)
\quad\text{in }D([a,b],\ell^2_\downarrow\times[0,\infty))
\text{ with }J_1.
$$</div>
<p>Thus the same time change aligns both coordinates. Jointly with this path limit,</p>
<div class="math-display">$$
\left(\int_a^b\|\mathbf L_N(\lambda)\|_2^2\,d\lambda,\qquad
      \int_a^b H_N(\lambda)\,d\lambda\right)
\ \xrightarrow{\ d\ }\
\left(\int_a^b\|\mathbf X(\lambda)\|_2^2\,d\lambda,\qquad
      \int_a^b H(\lambda)\,d\lambda\right).
$$</div>
<p>No expectation convergence for the weighted-surplus integral is asserted.</p>

<p><em>Proof.</em> First consider the candidate limiting process. NH8N and KBJ8 make $H$ finite on bounded intervals; it increases because both mergers and births have nonnegative increments. We check continuity in probability at each fixed time, which will also fix the choice of version.</p>
<p>Condition on an initial state $(x,y)$ of law $\nu_a$. All its masses are positive almost surely. Given a bounded elapsed interval, discard initial marks after rank $k$. By NH8N their total weighted contribution is uniformly negligible in probability as $k\to\infty$. The remaining initial marks are finite in number. By KBJ8, with probability tending to one, all new births on the interval occur already in the first-$k$ restriction. They too are finite in number and can be named by their proposal and endpoint labels.</p>
<p>For a sequence of deterministic times $t_j\to t$, V90S with the constant initial mass sequence implies convergence in probability of the mass carrying any fixed positive-mass label. For the finitely many retained initial marks, summing these carrying masses proves continuity in probability of their contribution. For the new marks, no proposal occurs at the fixed time $t$ almost surely: there are only countably many original Poisson processes, each with an atomless arrival law. On the event that all births belong to the finite restriction, the set born before $t_j$ therefore eventually agrees with that before $t$. Their carrying masses converge in probability by the same labelled argument. Localizing the finite number of births and then removing the initial-tail and restriction errors proves $H(t_j)\to H(t)$ in probability. At the initial time the identical argument is one-sided and there are no pre-existing new births. Conditioning can be removed by bounded convergence.</p>
<p>An increasing, locally bounded function has finite right limits and left limits. Define the right-limit version using rational times in a slightly longer interval. Continuity in probability shows that it equals the graphical $H$ almost surely at each fixed time. This version is càdlàg and has no jump at any deterministic time. Together with the càdlàg size process of GRSC, it supplies the candidate joint path and its stochastic continuity. The modification preserves every finite-dimensional law in JSGY.</p>
<p>For the approximations, start the finite Poisson augmented construction from the actual graph at $a$, and run it in coalescent time. At every deterministic elapsed time its marked law converges by the argument of 4DZC and JSGY; the limiting mass law has no ties at that time. The map</p>
<div class="math-display">$$
(x,y)\longmapsto\left(x,\sum_i x_i y_i\right)
$$</div>
<p>is continuous from the weighted state space into the product state space. Its finite-dimensional laws therefore converge to those just identified. In particular the product-state marginals and the terminal values $S_N+H_N$ are tight. Apply 0DWE to obtain joint path tightness, including on a slightly longer elapsed interval than $[0,b-a]$. Stochastic continuity of the candidate and convergence of the finite-dimensional laws identify every subsequential path limit. This is the same Skorokhod identification argument as in GRSC, now applied to the two coordinates together.</p>
<p>Return to the original parameter using the deterministic clock
$u_N(\lambda)=N^{4/3}\log[(1-p_N(a))/(1-p_N(\lambda))]$. It is increasing and converges uniformly to $\lambda-a$, with derivative tending uniformly to one. The time-change argument in TIGK transfers the joint limit; the candidate has no jump at the deterministic terminal time. By JSGY the expected number of loops and repeated-edge marks added only by the Poisson construction is $O_{a,b}(N^{-1/3})$. Except on an event with this vanishing probability, the simple and augmented graphs have identical component sizes and surplus counts throughout $[a,b]$. This transfers the entire path law to the simple graph. The value of $H_N$ is independent of any rule for ordering equal-sized components.</p>
<p>Finally, $J_1$ convergence gives uniformly bounded ranges and convergence at almost every time of a limiting càdlàg path. The norm-square and second-coordinate functions are continuous; they are bounded on these ranges. Dominated convergence in a Skorokhod representation proves joint convergence of the two integrals and their joint convergence with the paths. $ \square$</p>
<p>The theorem controls the full scalar weighted sum, including inherited surplus. It does not identify a $J_1$ topology for the entire ranked sequence of surplus counts. That problem and a common-Brownian representation across all parameters remain separate.</p>


## Moments before the exploration reaches late components {#section-critical-early-surplus-moments}

<p>The path limit EURS does not by itself justify taking expectations of total weighted surplus. The late-component estimate RJJ9 controls its mean remainder. For the early components we need a moment bound, including the random time at which their exploration finishes.</p>
<p>Fix $\Lambda\ge0$, and consider $G(N,p_N(\lambda))$ for $|\lambda|\le\Lambda$ and $p_N(\lambda)\in[0,1]$. Retain the exploration variables above. For $U\ge0$, put</p>
<div class="math-display">$$
m_N(U)=\min\{N,\lceil UN^{2/3}\rceil\},\qquad
Z_N(U)=\sum_{i\le m_N(U)}\zeta_i,\qquad
R_N=N^{-2/3}L_1.
$$</div>
<p>Thus $Z_N(U)$ counts surplus edges revealed by this deterministic exploration time. For $T\ge0$ let</p>
<div class="math-display">$$
E_N(T)=N^{-2/3}
\sum_{\mathcal C:\,\mathrm{start}(\mathcal C)<\lfloor TN^{2/3}\rfloor}
|\mathcal C|\sigma(\mathcal C).
$$</div>

<a id="tag-U59P" data-assertion="proposition" data-title="Exploration surplus counts have polynomial moment bounds and early size-weighted surplus has uniformly bounded moments"></a>
<p>For every integer $r\ge1$ there is $C_{\Lambda,r}<\infty$ such that, for every $U\ge0$,</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
\mathbb E Z_N(U)^r
\le C_{\Lambda,r}(1+U)^{2r}.
$$</div>
<p>For each fixed $T\ge0$ and integer $r\ge1$, one also has</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
\mathbb E E_N(T)^r<\infty.
$$</div>

<p><em>Proof.</em> First take $N$ large enough that $Np_N(\lambda)\le2$ throughout the interval. Write $m=m_N(U)$ and $W_m=\max_{k\le m}|M_k|$. Integrating the maximal bound N9DF gives, for $m\ge1$,</p>
<div class="math-display">$$
\mathbb EW_m^r\le C_r(m^{r/2}+1).
$$</div>
<p>Indeed, its tail is bounded by the sum of $2e^{-u^2/(8m)}$ and $2e^{-u/8}$; integrating $r u^{r-1}$ times these two tails proves the estimate. Within any active component the drift bound used in FOTE gives</p>
<div class="math-display">$$
\max_{k\le m}A_k\le1+\Lambda N^{-1/3}m+2W_m.
$$</div>
<p>Since $m\le(1+U)N^{2/3}$, it follows that</p>
<div class="math-display">$$
\mathbb E\left(N^{-1/3}\max_{k\le m}A_k\right)^r
\le C_{\Lambda,r}(1+U)^r.
$$</div>
<p>The case $m=0$ contributes zero.</p>
<p>Condition on the complete discovery transcript, as in GGL3. The unused edge bits remain independent, so $Z_N(U)$ is binomial with number of trials $K_N(U)=\sum_{i\le m}(A_{i-1}-1)_+$. Its conditional mean obeys</p>
<div class="math-display">$$
p_NK_N(U)\le \frac{2m}{N}\max_{k\le m}A_k
\le 2(1+U)N^{-1/3}\max_{k\le m}A_k.
$$</div>
<p>For a binomial variable of mean $v$, its $j$th falling-factorial moment is at most $v^j$. Expanding the $r$th power in falling factorials therefore bounds its $r$th moment by $C_r(1+v^r)$. The preceding queue estimate proves the first assertion. The finitely many smaller $N$ are covered by increasing the constant, since $Z_N(U)\le\binom N2$ for every admissible $\lambda$ and every $U$.</p>
<p>Every component starting before $\lfloor TN^{2/3}\rfloor$ finishes by time $\lfloor TN^{2/3}\rfloor+L_1$, or by time $N$ if earlier. Its normalized mass is at most $R_N$. Consequently, pathwise,</p>
<div class="math-display">$$
E_N(T)\le R_N Z_N(T+R_N+1).
$$</div>
<p>The cubic largest-component tail, uniformly over the critical interval as in 7CDV, gives constants $A,c,C>0$ such that $\mathbb P(R_N\ge j)\le Ce^{-cj^3}$ for integers $j\ge A$. On $\{j\le R_N<j+1\}$, the last display is at most $(j+1)Z_N(T+j+2)$. Cauchy–Schwarz and the first assertion at order $2r$ give</p>
<div class="math-display">$$
\mathbb E E_N(T)^r
\le \sum_{j\ge0}(j+1)^r
       \bigl(\mathbb EZ_N(T+j+2)^{2r}\bigr)^{1/2}
       \mathbb P(R_N\ge j)^{1/2}
\le C_{\Lambda,r}\sum_{j\ge0}(j+1)^r
       (T+j+3)^{2r}\mathbb P(R_N\ge j)^{1/2}.
$$</div>
<p>The last series is uniformly finite: its first finitely many terms are bounded directly, and its remaining polynomial factors are dominated by the cubic exponential tail. No independence between the largest component and the exploration marks is assumed. $ \square$</p>

## First moments of total weighted surplus {#section-critical-weighted-surplus-expectations}

<a id="tag-O4TX" data-assertion="theorem" data-title="Critical total weighted surplus is uniformly integrable, with uniform first-moment limits and expectation convergence for linearly growing marked-path observables"></a>
<p>For every $\Lambda\ge0$, the family</p>
<div class="math-display">$$
\left\{H_N(\lambda):
N\ge2,\ |\lambda|\le\Lambda,\ p_N(\lambda)\in[0,1]\right\}
$$</div>
<p>is uniformly integrable. Write $h(\lambda)=\mathbb EH(\lambda)$ for the weighted-surplus limit in EURS. This is finite and continuous, and</p>
<div class="math-display">$$
\sup_{|\lambda|\le\Lambda}
\left|\mathbb EH_N(\lambda)-h(\lambda)\right|\longrightarrow0.
$$</div>
<p>Here all parameters in the supremum are admissible for sufficiently large $N$. More generally, if $\lambda_N\to\lambda$, then $\mathbb EH_N(\lambda_N)\to h(\lambda)$. In the Brownian exploration description of $\nu_\lambda$,</p>
<div class="math-display">$$
h(\lambda)=
\mathbb E\sum_{(u,v)\text{ excursion of }R_\lambda}
          (v-u)\int_u^v R_\lambda(t)\,dt<\infty.
$$</div>
<p>Finally, fix $[a,b]\subseteq[-\Lambda,\Lambda]$, $a<b$. If $\Phi$ is Borel measurable on the joint size/weighted-surplus path space, is $J_1$-continuous at almost every limiting path, and satisfies</p>
<div class="math-display">$$
|\Phi(x,h)|\le A\left(1+
   \sup_{a\le t\le b}\|x(t)\|_2^q+
   \sup_{a\le t\le b}h(t)\right)
$$</div>
<p>for finite $A\ge0$ and $q>0$, then
$\mathbb E\Phi(\mathbf L_N,H_N)\to\mathbb E\Phi(\mathbf X,H)$.
In particular,</p>
<div class="math-display">$$
\mathbb E\int_a^b H_N(\lambda)\,d\lambda
\longrightarrow \int_a^b h(\lambda)\,d\lambda
=\mathbb E\int_a^b H(\lambda)\,d\lambda<\infty.
$$</div>

<p><em>Proof.</em> Decompose $H_N=E_N(T)+B_N(T)$ according to whether exploration starts before or after $\lfloor TN^{2/3}\rfloor$. Both terms are nonnegative. The proof of RJJ9 is uniform over $|\lambda|\le\Lambda$: for $T>\Lambda$, dominate the remaining binomial mean by
$(N-\lfloor TN^{2/3}\rfloor)p_N(\Lambda)$. Thus</p>
<div class="math-display">$$
\limsup_{N\to\infty}\sup_{|\lambda|\le\Lambda}
\mathbb EB_N(T)\le\frac1{2(T-\Lambda)^2}.
$$</div>
<p>For fixed $T$, U59P bounds the second moments of $E_N(T)$ uniformly. For $K>0$,</p>
<div class="math-display">$$
\mathbb E(H_N-K)_+
\le \mathbb E(E_N(T)-K)_++\mathbb EB_N(T).
$$</div>
<p>Take the supremum over $\lambda$, then the upper limit in $N$, then $K\to\infty$. The first term tends to zero, and the second is bounded by $1/[2(T-\Lambda)^2]$. Let $T\to\infty$. This gives uniform integrability: equivalently,
$H_N\mathbf1_{\{H_N>2K\}}\le2(H_N-K)_+$, and the finitely many smaller $N$ have deterministic bounds uniform in their admissible parameters.</p>
<p>The moving-parameter weighted-state convergence 1QUE implies
$H_N(\lambda_N)\Rightarrow H(\lambda)$ whenever $\lambda_N\to\lambda$. Uniform integrability now gives convergence of means and finiteness of $h(\lambda)$. To see that $h$ is continuous, use the augmented process on any compact interval containing the parameters under consideration. Its increasing càdlàg weighted sum is continuous at each fixed time almost surely by EURS. It is bounded on that interval by its terminal value, which has finite mean by the result just proved. Dominated convergence therefore gives continuity of $h$. If uniform convergence of the means on $[-\Lambda,\Lambda]$ failed, a sequence of offending parameters would have a convergent subsequence. The moving-parameter mean limit and continuity of $h$ contradict that failure.</p>
<p>Conditionally on the Brownian exploration path, each excursion's surplus is Poisson with mean equal to the area under that excursion, by GGL3 and 1QUE. Tonelli's theorem identifies the mean weighted sum with the displayed sum of length times area. The preceding mean bound proves its finiteness; finiteness of the random weighted sum alone would not have sufficed.</p>
<p>For the path assertion, both the squared norm and the weighted sum are increasing. Hence their suprema are their terminal values. The powers of $\|\mathbf L_N(b)\|_2$ are uniformly integrable by 1DEZ (or 7CDV), and $H_N(b)$ is uniformly integrable by the first part. Their sum dominates $|\Phi(\mathbf L_N,H_N)|$, so these observables are uniformly integrable. EURS and the continuous mapping theorem, followed by truncation, give convergence of expectations. The time integral is continuous in $J_1$ by the same bounded-range argument used in EURS and is at most $(b-a)H_N(b)$. Tonelli's theorem gives the final identity. $ \square$</p>
<p>This establishes first moments of inherited as well as new weighted surplus. It does not claim higher moments or positive exponential moments of $H_N$ from the late first-moment estimate. The topology for the entire ranked surplus path remains separate.</p>


## Weighted-surplus moments below order two {#section-critical-weighted-surplus-fractional-moments}

<p>The early and late estimates used for O4TX also give quantitative tails. The cutoff must now depend on the tail level, so we first keep its dependence explicit and remove the upper limit in $N$ from the late estimate.</p>

<a id="tag-WPKA" data-assertion="theorem" data-title="Critical size-weighted surplus has uniform moments of every order below two and uniform convergence of these moments on compact parameter intervals"></a>
<p>Fix $\Lambda\ge0$. For every integer $r\ge2$, there is $C_{\Lambda,r}<\infty$ such that, for all $s\ge1$,</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
\mathbb P\bigl(H_N(\lambda)>s\bigr)
\le C_{\Lambda,r}s^{-\beta_r},\qquad
\beta_r=\frac{2r}{r+1}.
$$</div>
<p>Consequently, for every $0<q<2$, this family has uniformly bounded $q$th moments, and its $q$th powers are uniformly integrable. The limiting moment
$h_q(\lambda)=\mathbb EH(\lambda)^q$ is finite and continuous, and</p>
<div class="math-display">$$
\sup_{|\lambda|\le\Lambda}
\left|\mathbb EH_N(\lambda)^q-h_q(\lambda)\right|\longrightarrow0.
$$</div>
<p>The supremum in the last display is taken for sufficiently large $N$, when every parameter in the interval is admissible. The same moments converge along every sequence $\lambda_N\to\lambda$.</p>

<p><em>Proof.</em> Write $H_N=E_N(T)+B_N(T)$ as in O4TX. The series at the end of the proof of U59P, together with
$T+j+3\le(1+T)(j+3)$, gives</p>
<div class="math-display">$$
\mathbb E E_N(T)^r\le C_{\Lambda,r}(1+T)^{2r}
\qquad(T\ge0).
$$</div>
<p>The constant is uniform in $N$ and $\lambda$: the remaining series is a polynomial in $j$ times the square root of the uniform cubic tail. The finitely many small $N$ were already included in U59P.</p>
<p>For the late term, let $k=\lfloor TN^{2/3}\rfloor$. If $k\ge N$, it is zero. Otherwise set $\mu=(N-k)p_N(\lambda)$. Since $\lambda\le\Lambda$ and $\Lambda\ge0$,</p>
<div class="math-display">$$
N^{1/3}(1-\mu)
\ge \frac{k}{N^{2/3}}-\Lambda+\frac{\Lambda k}{N}
\ge T-\Lambda-1.
$$</div>
<p>Thus $0\le\mu<1$ whenever $T>\Lambda+1$. Stop at the first completed component at or after $k$. Conditional on the exploration so far, the remaining graph is independent with at most $N-k$ vertices. The finite bound in RJJ9, and monotonicity of $u^3/[2(1-u)^2]$, give</p>
<div class="math-display">$$
\mathbb EB_N(T)
\le N^{-2/3}\frac{\mu^3}{2(1-\mu)^2}
\le\frac1{2(T-\Lambda-1)^2}
\qquad(T>\Lambda+1).
$$</div>
<p>This holds for every admissible $N,\lambda$, including the case where the remainder is empty. It is a finite-$N$ bound, so $T$ may depend on the tail level.</p>
<p>If $H_N>s$, at least one of $E_N(T),B_N(T)$ exceeds $s/2$. Markov's inequality at orders $r$ and one therefore yields, for $T\ge2(\Lambda+1)$,</p>
<div class="math-display">$$
\mathbb P(H_N>s)
\le C_{\Lambda,r}\frac{(1+T)^{2r}}{s^r}
     +\frac4{sT^2}.
$$</div>
<p>Take $T=2(\Lambda+1)s^{(r-1)/(2r+2)}$. For $s\ge1$, both terms are bounded by a constant times $s^{-2r/(r+1)}$, proving the tail estimate.</p>
<p>Given $q<2$, choose $r$ with $\beta_r>q$. Integrating the tail gives, uniformly in $N,\lambda$,</p>
<div class="math-display">$$
\mathbb EH_N^q\le1+\frac{qC_{\Lambda,r}}{\beta_r-q},\qquad
\mathbb E\!\left[H_N^q\mathbf1_{\{H_N>K\}}\right]
\le \frac{\beta_r C_{\Lambda,r}}{\beta_r-q}K^{q-\beta_r}
\quad(K\ge1).
$$</div>
<p>For the second inequality, split the tail integral at $K$ and include the term $K^q\mathbb P(H_N>K)$. This proves uniform integrability of the powers, not just boundedness of their means.</p>
<p>By 1QUE, $H_N(\lambda_N)\Rightarrow H(\lambda)$ whenever $\lambda_N\to\lambda$. Uniform integrability of the $q$th powers gives the moving-parameter moment limit and finiteness of $h_q$. In the common augmented process on a compact interval, $H$ is increasing and has no jump at a deterministic time by EURS. Its $q$th power is dominated by the integrable terminal $q$th power. Dominated convergence therefore makes $h_q$ continuous. Uniform convergence on $[-\Lambda,\Lambda]$ follows as in O4TX: any sequence of parameters contradicting it has a convergent subsequence, to which the moving-parameter limit applies. $\square$</p>
<p>The exponents $\beta_r$ approach two from below. This argument gives no second-moment bound at the endpoint $q=2$.</p>

## Mixed size and weighted-surplus expectations {#section-critical-weighted-surplus-mixed-expectations}

<a id="tag-JTVN" data-assertion="theorem" data-title="Critical joint size and weighted-surplus path expectations converge under exponential squared-size growth and surplus growth of order below two"></a>
<p>Fix $a<b$, $0<q<2$, and finite $A,\theta\ge0$. Let $\Phi$ be a real-valued Borel function on the joint path space in EURS, continuous in $J_1$ at almost every limiting path, and suppose that</p>
<div class="math-display">$$
|\Phi(x,h)|\le
A\exp\!\left(\theta\sup_{a\le t\le b}\|x(t)\|_2^2\right)
\left(1+\sup_{a\le t\le b}h(t)^q\right).
$$</div>
<p>Then the expectations are finite and</p>
<div class="math-display">$$
\mathbb E\Phi(\mathbf L_N,H_N)
\longrightarrow \mathbb E\Phi(\mathbf X,H).
$$</div>
<p>In particular, write</p>
<div class="math-display">$$
I_N=\int_a^b\|\mathbf L_N(t)\|_2^2\,dt,\qquad
J_N=\int_a^b H_N(t)\,dt,
$$</div>
<p>and let $I,J$ be the corresponding limiting integrals. For every real $t$ and every nonnegative integer $m$,</p>
<div class="math-display">$$
\mathbb E[e^{tI_N}J_N^q]\longrightarrow\mathbb E[e^{tI}J^q]<\infty,
\qquad
\mathbb E[I_N^mJ_N^q]\longrightarrow\mathbb E[I^mJ^q]<\infty.
$$</div>

<p><em>Proof.</em> Put $S_N=\|\mathbf L_N(b)\|_2^2$. Both coordinates controlling the growth bound increase, so their suprema occur at $b$. Choose $\varepsilon>0$ and $v>1$ such that $q(1+\varepsilon)v<2$, and let $u=v/(v-1)$. Hölder's inequality gives</p>
<div class="math-display">$$
\mathbb E|\Phi(\mathbf L_N,H_N)|^{1+\varepsilon}
\le A^{1+\varepsilon}
\left(\mathbb Ee^{\theta(1+\varepsilon)uS_N}\right)^{1/u}
\left(\mathbb E(1+H_N(b)^q)^{(1+\varepsilon)v}\right)^{1/v}.
$$</div>
<p>The first factor is uniformly bounded by 7CDV, which permits every fixed nonnegative exponential parameter. The second is uniformly bounded by WPKA, since its highest weighted-surplus power is strictly below two. The same bounds hold for the limit. Hence these observables are uniformly integrable. The joint path convergence EURS and the continuous mapping theorem give convergence in distribution of $\Phi$; truncation then gives convergence of expectations. Independence of the size and surplus coordinates is not needed.</p>
<p>The two integrals are jointly continuous in $J_1$: convergence holds at almost every time and the ranges of a convergent sequence of paths are uniformly bounded. Moreover,</p>
<div class="math-display">$$
0\le I_N\le(b-a)S_N,\qquad
0\le J_N\le(b-a)H_N(b).
$$</div>
<p>For the exponential example use $\theta=(b-a)\max\{t,0\}$ in the growth bound. For the polynomial example use that every fixed power of a nonnegative real number is bounded by a constant times its exponential. The same argument applies to the limiting integrals, proving both assertions. $\square$</p>
<p>The exponential weight here concerns squared component size. The surplus coordinate has growth of order strictly below two; neither a positive exponential moment of total weighted surplus nor its second moment is asserted.</p>


## All moments of total weighted surplus {#section-critical-weighted-surplus-all-moments}

<p>The restriction $q<2$ in WPKA comes from using only a first-moment bound on the late contribution. We can remove it by combining the squared-mass moment estimate with the conditional law of the surplus edges, one exploration interval at a time.</p>
<p>Fix $\Lambda\ge0$ and retain $H_N$, $E_N(T)$ and $B_N(T)$ from O4TX. All bounds below are uniform over $N\ge2$ and $|\lambda|\le\Lambda$ for which $p_N(\lambda)\in[0,1]$. Let $\|Z\|_r=(\mathbb E|Z|^r)^{1/r}$.</p>

<a id="tag-QKHG" data-assertion="theorem" data-title="Critical total size-weighted surplus has uniformly bounded moments of every positive order, with an Lr bound on the late exploration remainder"></a>
<p>For every integer $r\ge1$ there is $C_{\Lambda,r}<\infty$ such that</p>
<div class="math-display">$$
\|B_N(T)\|_r\le C_{\Lambda,r}T^{-1/2}
\qquad\bigl(T\ge2(\Lambda+1)\bigr).
$$</div>
<p>Consequently, for every real $q>0$,</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
\mathbb EH_N(\lambda)^q<\infty.
$$</div>
<p>The $L^1$ estimate here is weaker than RJJ9's sharper mean bound; it is the control of arbitrary moment orders that is new.</p>

<p><em>Proof.</em> Put $b=N^{2/3}$, $c=N^{1/3}$, $R_N=L_1/b$, and</p>
<div class="math-display">$$
Q_N(U)=c^{-1}\max_{0\le k\le\min\{N,\lceil Ub\rceil\}}A_k.
$$</div>
<p>We first sharpen the queue estimate used in U59P. If the component active at time $k$ started just after $s$, then $k-s\le L_1$. The componentwise drift inequality from FOTE therefore gives, for every deterministic $m\le N$,</p>
<div class="math-display">$$
\max_{k\le m}A_k
\le1+\Lambda N^{-1/3}L_1+2\max_{k\le m}|M_k|.
$$</div>
<p>Only the duration of that component enters the positive drift term. For large $N$, the conditional offspring means are at most two. Integrate N9DF as in U59P and use the uniform moments of $R_N$ from the cubic tail in 7CDV. For every integer $j\ge1$, this gives</p>
<div class="math-display">$$
\mathbb E Q_N(U)^j\le C_{\Lambda,j}(1+U)^{j/2}
\qquad(U\ge0).
$$</div>
<p>The finitely many smaller $N$ are covered by the deterministic bound $A_k\le N$. We also need the random horizon</p>
<div class="math-display">$$
Q_N^*(T)=Q_N(2T+R_N+1).
$$</div>
<p>On $\{\ell\le R_N<\ell+1\}$ it is at most $Q_N(2T+\ell+2)$. Cauchy–Schwarz, the last estimate at order $2j$, and the cubic tail give</p>
<div class="math-display">$$
\mathbb E Q_N^*(T)^j
\le\sum_{\ell\ge0}
 \bigl(\mathbb E Q_N(2T+\ell+2)^{2j}\bigr)^{1/2}
 \mathbb P(R_N\ge\ell)^{1/2}
\le C_{\Lambda,j}(1+T)^{j/2}.
$$</div>
<p>This argument uses no independence between the horizon and the queue.</p>
<p>Next let $S_N^{\mathrm{late}}(T)$ be $b^{-2}$ times the sum of squared sizes of components starting at or after $\lfloor Tb\rfloor$. Take $T\ge2(\Lambda+1)$. If $\lfloor Tb\rfloor\ge N$, this quantity is zero. Otherwise stop at the first completed component at or after that cutoff. Conditional on this exploration, the remaining graph is $G(m,p_N)$ with $m\le N-\lfloor Tb\rfloor$. The finite-$N$ calculation in WPKA implies</p>
<div class="math-display">$$
1-mp_N\ge (T-\Lambda-1)N^{-1/3}
\ge \frac{T}{2N^{1/3}}.
$$</div>
<p>Path counting bounds its susceptibility at every vertex by
$D=(1-mp_N)^{-1}\le2N^{1/3}/T$. Apply YN7V to this conditional graph; if it is empty, its squared-mass sum is zero. A partition with $k$ blocks in the $j$th moment contributes at most a constant depending on $j$ times</p>
<div class="math-display">$$
N^{-4j/3}N^k
\left(\frac{2N^{1/3}}T\right)^{4j-3k}
=2^{4j-3k}T^{-(4j-3k)}.
$$</div>
<p>Since $1\le k\le j$ and $T\ge1$, summing the finitely many partitions and removing the conditioning gives</p>
<div class="math-display">$$
\mathbb E\bigl[S_N^{\mathrm{late}}(T)^j\bigr]
\le C_j T^{-j}\qquad(j\ge1).
$$</div>
<p>The full discovery transcript will be used below for the surplus marks. It is not used in this conditional squared-mass estimate, where revealing the future components would destroy the independent remaining-graph law.</p>
<p>Let $D_N(T)$ be the normalized weighted surplus of components with start times in
$[\lfloor Tb\rfloor,\lfloor2Tb\rfloor)$. Every such component finishes by
$\lfloor2Tb\rfloor+L_1$, or by $N$ if earlier. Now condition on the complete discovery transcript, which determines all component sizes, their start times and the queue. By GGL3 the unqueried surplus-edge bits remain independent Bernoulli($p_N$). Write</p>
<div class="math-display">$$
D_N(T)=\sum_e w_e\xi_e,
$$</div>
<p>where $e$ ranges over surplus-edge candidates in these components and $w_e=|\mathcal C(e)|/b$. With $S=S_N^{\mathrm{late}}(T)$, their maximum weight $R$ and conditional mean $V$ satisfy</p>
<div class="math-display">$$
R\le\sqrt S,\qquad
V=p_N\sum_e w_e
\le Np_N Q_N^*(T)S
\le(1+\Lambda)Q_N^*(T)S.
$$</div>
<p>For the middle inequality, a component of size $k$ has at most $k$ times the maximum queue size many candidate edges. Its contribution to $\sum_e w_e$ is therefore at most $k^2 cQ_N^*(T)/b$. Summing and using $bc=N$ proves the bound.</p>
<p>For any finite sum of independent Bernoulli variables with nonnegative weights at most $R$, expansion of its $r$th moment gives</p>
<div class="math-display">$$
\mathbb E[D_N(T)^r\mid\text{discovery transcript}]
\le \sum_{k=1}^r
 \left\{\begin{matrix}r\\k\end{matrix}\right\}R^{r-k}V^k.
$$</div>
<p>Here the coefficient counts partitions of $r$ positions into $k$ nonempty blocks. Positions selecting the same edge form a block. For a block of size $d$, use $w_e^d\le R^{d-1}w_e$; then discard the distinctness restriction between the selected edges. Their sums factor into $V^k$. If there are no candidate edges, both sides are zero, with zeroth powers interpreted as one.</p>
<p>Substituting the bounds on $R,V$ and applying Cauchy–Schwarz after removing the conditioning yields</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E D_N(T)^r
&\le C_{\Lambda,r}\sum_{k=1}^r
 \mathbb E\!\left[Q_N^*(T)^k S^{(r+k)/2}\right]\\
&\le C_{\Lambda,r}\sum_{k=1}^r
 \bigl(\mathbb E Q_N^*(T)^{2k}\bigr)^{1/2}
 \bigl(\mathbb ES^{r+k}\bigr)^{1/2}
\le C_{\Lambda,r}T^{-r/2}.
\end{aligned}
$$</div>
<p>Indeed, the two factors in each term contribute $T^{k/2}$ and $T^{-(r+k)/2}$. No independence between the queue, the late squared mass and the marks is assumed.</p>
<p>The intervals with cutoffs $T,2T,4T,\ldots$ partition the late components, so
$B_N(T)=\sum_{i\ge0}D_N(2^iT)$. For each finite graph this sum is eventually zero. Minkowski's inequality gives</p>
<div class="math-display">$$
\|B_N(T)\|_r
\le\sum_{i\ge0}\|D_N(2^iT)\|_r
\le C_{\Lambda,r}\sum_{i\ge0}(2^iT)^{-1/2}
\le C'_{\Lambda,r}T^{-1/2}.
$$</div>
<p>Finally fix $T=2(\Lambda+1)$ and write $H_N=E_N(T)+B_N(T)$. U59P bounds every integer moment of the first term; the new estimate bounds those of the second. This proves the assertion for integer orders. For a real $q>0$, take an integer $r\ge q$ and use $\mathbb EH_N^q\le(\mathbb EH_N^r)^{q/r}$. $\square$</p>

## Moment and covariance limits for weighted surplus {#section-critical-weighted-surplus-all-expectations}

<a id="tag-DK7F" data-assertion="theorem" data-title="All positive weighted-surplus moments and exponentially size-weighted path expectations converge in the critical window"></a>
<p>For every $q>0$, $h_q(\lambda)=\mathbb EH(\lambda)^q$ is finite and continuous. The powers $H_N(\lambda)^q$ are uniformly integrable on compact critical parameter intervals, and</p>
<div class="math-display">$$
\sup_{|\lambda|\le\Lambda}
\left|\mathbb EH_N(\lambda)^q-h_q(\lambda)\right|
\longrightarrow0\qquad(\Lambda\ge0).
$$</div>
<p>All parameters in the supremum are admissible for sufficiently large $N$. The same moment limit holds along every $\lambda_N\to\lambda$. In particular, the variances converge uniformly on compact parameter intervals.</p>
<p>More generally, fix $a<b$ and a real-valued Borel function $\Phi$ on the joint path space of EURS. Suppose it is $J_1$-continuous at almost every limiting path and, for some finite $A,\theta\ge0$ and $q>0$,</p>
<div class="math-display">$$
|\Phi(x,h)|\le A
\exp\!\left(\theta\sup_{a\le t\le b}\|x(t)\|_2^2\right)
\left(1+\sup_{a\le t\le b}h(t)^q\right).
$$</div>
<p>Then $\mathbb E\Phi(\mathbf L_N,H_N)\to\mathbb E\Phi(\mathbf X,H)$, with finite expectations. Thus the conclusions of JTVN hold for every $q>0$: with its notation $I_N,J_N,I,J$, for every real $t$ and nonnegative integer $m$,</p>
<div class="math-display">$$
\mathbb E[e^{tI_N}J_N^q]\longrightarrow\mathbb E[e^{tI}J^q]<\infty,
\qquad
\mathbb E[I_N^mJ_N^q]\longrightarrow\mathbb E[I^mJ^q]<\infty.
$$</div>
<p>In particular, $\operatorname{Var}(J_N)\to\operatorname{Var}(J)$ and
$\operatorname{Cov}(I_N,J_N)\to\operatorname{Cov}(I,J)$.</p>

<p><em>Proof.</em> For fixed $q>0$, QKHG bounds a moment of order strictly greater than $q$, giving uniform integrability of the $q$th powers. Apply the moving-parameter law 1QUE. As in WPKA, continuity of $h_q$ follows from the absence of fixed-time jumps in EURS and domination by the terminal $q$th power on a compact interval. Compactness then upgrades the moving-parameter moment limit to uniform convergence. The cases $q=1,2$, and continuity and boundedness of their limits on compact intervals, give uniform variance convergence.</p>
<p>For the path assertion put $S_N=\|\mathbf L_N(b)\|_2^2$. Monotonicity of the squared norm and weighted surplus, followed by Hölder, gives the uniform square-moment bound</p>
<div class="math-display">$$
\mathbb E|\Phi(\mathbf L_N,H_N)|^2
\le A^2\left(\mathbb Ee^{4\theta S_N}\right)^{1/2}
          \left(\mathbb E(1+H_N(b)^q)^4\right)^{1/2}<C.
$$</div>
<p>The first factor is bounded by 7CDV and the second by QKHG. The corresponding limiting factors are finite as well. EURS and the continuous mapping theorem give convergence in distribution of $\Phi$, while this square-moment bound gives uniform integrability. Hence the expectations converge.</p>
<p>The integral observables satisfy the growth and continuity conditions exactly as in JTVN: $I_N\le(b-a)S_N$, $J_N\le(b-a)H_N(b)$, and integration is continuous along a $J_1$-convergent sequence of these paths. Taking the first and second moments of $J_N$, and the product $I_NJ_N$, proves the variance and covariance assertions, using the size-integral mean limit for $I_N$. $\square$</p>
<p>This removes the moment-order restriction in the preceding results. It does not establish positive exponential moments of total weighted surplus, or a topology for the full ranked marked path.</p>


## Surplus as a measure on component sizes {#section-surplus-size-measure-control}

<p>The scalar $H=\sum_i x_i y_i$ does not say which component sizes carry the surplus. Retain that information in the finite measure</p>
<div class="math-display">$$
\mathcal M(x,y)=\sum_i x_i y_i\,\delta_{x_i}
\quad\text{on }[0,\infty).
$$</div>
<p>Its total mass is $H$. Components of equal size contribute at the same point. We give the space $\mathcal M_f([0,\infty))$ of finite nonnegative measures its weak topology, metrized by</p>
<div class="math-display">$$
\beta(\mu,\nu)=
\sup_{\substack{\|f\|_\infty\le1\\\operatorname{Lip}(f)\le1}}
\left|\int f\,d\mu-\int f\,d\nu\right|.
$$</div>
<p>This bounded-Lipschitz metric is complete. Indeed, a Cauchy sequence has bounded total masses, and comparison with one sufficiently late term, using Lipschitz cutoffs outside compact intervals, makes the sequence uniformly tight. A weakly convergent subsequence then exists, and convergence in $\beta$ and the Cauchy property give convergence of the whole sequence. On finite measures this metric induces weak convergence against bounded continuous functions.</p>
<p>Use the complete separable product space</p>
<div class="math-display">$$
\mathcal E=\ell^2_\downarrow\times\mathcal M_f([0,\infty)),\qquad
d((x,\mu),(x',\nu))=
\left(\|x-x'\|_2^2+\beta(\mu,\nu)\right)^{1/2}.
$$</div>

<a id="tag-GZ95" data-assertion="proposition" data-title="The size-weighted surplus measure is continuous on weighted marked states and its coalescent increments are controlled by squared mass and total weighted surplus"></a>
<p>The map $(x,y)\mapsto(x,\mathcal M(x,y))$ is continuous from the weighted marked-state space of 1QUE to $\mathcal E$. For a finite augmented coalescent, write $\mu(t)=\mathcal M(X(t),Y(t))$, $S(t)=\|X(t)\|_2^2$, $H(t)=\mu(t)([0,\infty))$ and $R=S+H$. Then, pathwise,</p>
<div class="math-display">$$
d((X(s),\mu(s)),(X(t),\mu(t)))^2
\le F(R(t))-F(R(s))\qquad(s\le t),
\quad F(r)=r+\frac23r^{3/2}.
$$</div>
<p>Consequently, a sequence of finite augmented coalescents is tight in
$D([0,T],\mathcal E)$ with $J_1$ if its $\mathcal E$-valued marginals are tight at every deterministic time and its terminal values $R(T)$ are tight.</p>

<p><em>Proof.</em> Set $z_i=x_i y_i$. Convergence in the weighted metric means convergence of $x$ in $\ell^2$ and of $z$ in $\ell^1$. For each finite set of indices the atom locations and weights converge. The mass of the omitted atoms is $\sum_{i>k}z_i$, which is uniformly small as $k\to\infty$ along a convergent sequence. This proves convergence in $\beta$. No separation of equal-size atoms is needed. The product metric is complete because the two factors are complete; its triangle inequality follows by combining the metrics $\|x-x'\|_2$ and $\sqrt{\beta(\mu,\nu)}$ by the Euclidean norm.</p>
<p>Consider a merger of masses $u,v$ carrying marks $r,s$. The old measure has contributions $ur\delta_u+vs\delta_v$, and the new contribution is
$(u+v)(r+s)\delta_{u+v}$. The increase in $H$ is $\Delta H=us+vr$. For any test function in the definition of $\beta$, moving the two old weights and adding the new weight gives</p>
<div class="math-display">$$
\left|\int f\,d(\mu_{\mathrm{after}}-\mu_{\mathrm{before}})\right|
\le urv+vsu+us+vr
\le(1+\sqrt{S_{\mathrm{before}}})\Delta H.
$$</div>
<p>For the last inequality, write $urv+vsu=u(vr)+v(us)$ and use $u,v\le\sqrt{S_{\mathrm{before}}}$. A surplus birth at mass $u$ adds $u\delta_u$, whose $\beta$-distance from zero is $u=\Delta H$.</p>
<p>There are finitely many proposals on a bounded interval in the finite construction. Sum these bounds and use
$\|X(t)-X(s)\|_2^2\le S(t)-S(s)$ from 3G0K. At each jump,</p>
<div class="math-display">$$
\Delta S+(1+\sqrt{R_{\mathrm{before}}})\Delta H
\le(1+\sqrt{R_{\mathrm{before}}})\Delta R
\le F(R_{\mathrm{after}})-F(R_{\mathrm{before}}).
$$</div>
<p>The triangle inequality for $\beta$ and telescoping prove the pathwise bound.</p>
<p>For tightness apply R8LD with increasing control $F(R)$. To check its stopped-increment hypothesis, work on $\{R(\tau)\le M\}$. Choose $0<\eta\le1$ such that
$(1+\sqrt{M+1})\eta\le\varepsilon^2$. If $R((\tau+h)\wedge T)-R(\tau)\le\eta$, the pathwise bound keeps every intervening $d$-displacement at most $\varepsilon$. Otherwise either $S$ or $H$ has increased by more than $\eta/2$. The conditional squared-mass expectation used in O3IS and the stopped estimate 0DWE bound this probability by $C_{M,\eta}h$, uniformly in the initial finite state. Since $F(r)\ge r$, this also proves the localized estimate required on $\{F(R(\tau))\le M\}$. Terminal tightness and marginal tightness supply the other hypotheses of R8LD. $\square$</p>

## A path limit for surplus across component sizes {#section-critical-surplus-size-measure-path}

<p>In the common-edge critical graph, define</p>
<div class="math-display">$$
\mu_N(\lambda)=
N^{-2/3}\sum_{\mathcal C\text{ at }\lambda}
 |\mathcal C|\sigma(\mathcal C)\,
 \delta_{N^{-2/3}|\mathcal C|}.
$$</div>
<p>All surplus is included, including cycles present at the initial parameter. For the augmented coalescent define
$\mu(\lambda)=\sum_iX_i(\lambda)Y_i(\lambda)\delta_{X_i(\lambda)}$.</p>

<a id="tag-EAQD" data-assertion="theorem" data-title="Critical component sizes and the measure of size-weighted surplus converge jointly as paths, with convergence of polynomially surplus-growing expectations"></a>
<p>Fix $a<b$. The process $(\mathbf X,\mu)$ has a càdlàg version in $\mathcal E$, with no jump at a deterministic parameter, and</p>
<div class="math-display">$$
(\mathbf L_N,\mu_N)\ \xrightarrow{\ d\ }\ (\mathbf X,\mu)
\quad\text{in }D([a,b],\mathcal E)\text{ with }J_1.
$$</div>
<p>There is one time change for the two coordinates. The finite-dimensional laws are obtained by applying GZ95's map to the marked laws in JSGY. In particular, the total-mass projection of the second coordinate is the weighted-surplus process $H$ of EURS.</p>
<p>If a real-valued Borel functional $\Phi$ on this path space is $J_1$-continuous at almost every limiting path and, for finite $A,\theta\ge0$ and $q>0$,</p>
<div class="math-display">$$
|\Phi(x,\mu)|\le A
\exp\!\left(\theta\sup_{a\le t\le b}\|x(t)\|_2^2\right)
\left(1+\sup_{a\le t\le b}\mu(t)([0,\infty))^q\right),
$$</div>
<p>then its expectations converge to the finite limiting expectation.</p>

<p><em>Proof.</em> Start the finite augmented Poisson construction at the actual marked graph at $a$, and first work in elapsed coalescent time, on a slightly longer interval than $[0,b-a]$. The argument of 4DZC and JSGY at varying elapsed times, followed by continuity of the map in GZ95, gives convergence and hence tightness of the $\mathcal E$-valued marginals. Its terminal $R=S+H$ is tight by 1QUE and the same Poisson comparison used in EURS. GZ95 therefore gives path tightness.</p>
<p>Consider a subsequential path limit $Y=(X,\widetilde\mu)$. The state map
$(x,\mu)\mapsto(x,\mu([0,\infty)))$ is continuous, since the test function one is allowed in $\beta$. Its path projection consequently has the law of $(\mathbf X,H)$ in EURS, with time origin shifted by $a$. Thus
$R(t)=\|X(t)\|_2^2+\widetilde\mu(t)([0,\infty))$ has no jump at a deterministic time.</p>
<p>In a Skorokhod representation of the convergent subsequence, use its common time changes in the pathwise bound of GZ95 and pass to the limit. The map
$(x,\mu)\mapsto F(\|x\|_2^2+\mu([0,\infty)))$ is continuous, so</p>
<div class="math-display">$$
d(Y(s),Y(t))^2\le F(R(t))-F(R(s))\qquad(s\le t).
$$</div>
<p>Taking $s\uparrow t$ shows that $Y$ cannot jump when $R$ is continuous. In particular $Y$ has no fixed-time jumps, including at the deterministic terminal time. Evaluation at every finite list of deterministic times is therefore almost surely continuous for this limit. The finite-dimensional convergence already obtained from JSGY identifies these laws as those of the graphical pair $(\mathbf X,\mu)$. They determine a unique law on the càdlàg path space, so every subsequential limit has that law.</p>
<p>This also gives a càdlàg version of the graphical pair itself. On a countable dense set of times, including the endpoints, its joint law equals that of the càdlàg limit. Take the corresponding right limits. The finite-dimensional laws are continuous in probability at each fixed time, because they agree with the limit's laws and it has no fixed-time jumps. The resulting extension therefore agrees almost surely with the graphical pair at each fixed time.</p>
<p>Return to the graph parameter with the increasing clock
$u_N(\lambda)=N^{4/3}\log[(1-p_N(a))/(1-p_N(\lambda))]$. It converges uniformly to $\lambda-a$, with derivative tending uniformly to one. As in EURS, the longer time interval and absence of a fixed terminal jump justify this deterministic time change. By JSGY, the probability of any extra loop or repeated-edge surplus mark in the augmented construction throughout $[a,b]$ tends to zero. On its complement, sizes and all component surpluses agree with the simple graph at every time, so the measures agree too. This transfers the path limit to $(\mathbf L_N,\mu_N)$.</p>
<p>For the expectation assertion, the two quantities controlling growth are increasing and hence bounded by their terminal values. As in DK7F, Hölder, 7CDV and QKHG give</p>
<div class="math-display">$$
\mathbb E|\Phi(\mathbf L_N,\mu_N)|^2
\le A^2
\left(\mathbb Ee^{4\theta\|\mathbf L_N(b)\|_2^2}\right)^{1/2}
\left(\mathbb E(1+H_N(b)^q)^4\right)^{1/2}<C.
$$</div>
<p>The limiting factors are finite as well. Uniform integrability and the continuous mapping theorem now give convergence of expectations. $\square$</p>
<p>For example, let $f_1,\ldots,f_m$ be bounded continuous functions on $[0,\infty)$. Jointly with the size path, the processes</p>
<div class="math-display">$$
\int f_j\,d\mu_N(\lambda)
=N^{-2/3}\sum_{\mathcal C\text{ at }\lambda}
 |\mathcal C|\sigma(\mathcal C)
 f_j(N^{-2/3}|\mathcal C|)
$$</div>
<p>converge in $J_1$ to $\int f_j\,d\mu(\lambda)$, with one time change for all coordinates. All joint polynomial moments of their time integrals and the squared-size integral $I_N$ converge. Indeed, these integrals are continuous under the path convergence, are bounded in absolute value by
$(b-a)\|f_j\|_\infty H_N(b)$, and their polynomial products satisfy the preceding growth bound.</p>
<p>At any deterministic limiting parameter the positive component sizes are distinct almost surely, and
$Y_i(\lambda)=\mu(\lambda)(\{X_i(\lambda)\})/X_i(\lambda)$. Thus the measure retains the individual surplus counts at those times. When sizes coincide it adds their surplus weights at the same point. The theorem does not assert $J_1$ convergence of the entire ranked surplus sequence in the metric of 1QUE.</p>


## A lower tail bound for weighted surplus {#section-weighted-surplus-large-tail}

<p>All polynomial moments exist by QKHG and DK7F. Positive exponential moments behave differently. Write
$H(\lambda)=\sum_i\ell_iY_i$ for the Brownian marked limit in 1QUE.</p>

<a id="tag-7E7T" data-assertion="proposition" data-title="Critical weighted surplus has a stretched-exponential lower tail and no positive exponential moment"></a>
<p>For every $\Lambda\ge0$, there are $c,C>0$ and $x_0<\infty$ such that</p>
<div class="math-display">$$
\mathbb P(H(\lambda)\ge x)\ge c\exp(-Cx^{3/4})
\qquad(|\lambda|\le\Lambda,\ x\ge x_0).
$$</div>
<p>Consequently, for every $\theta>0$ and $\alpha>3/4$,</p>
<div class="math-display">$$
\mathbb E e^{\theta H(\lambda)^\alpha}=\infty,
\qquad
\inf_{|\lambda|\le\Lambda}
\mathbb E e^{\theta H_N(\lambda)^\alpha}\longrightarrow\infty.
$$</div>
<p>In the second assertion $N$ is sufficiently large that every displayed parameter is admissible. Moreover, for some $c'>0$ and $q_0<\infty$,</p>
<div class="math-display">$$
\|H(\lambda)\|_q\ge c'q^{4/3}
\qquad(|\lambda|\le\Lambda,\ q\ge q_0).
$$</div>
<p>For $a<b$, the integrated weighted surplus
$J=\int_a^bH(\lambda)\,d\lambda$ also satisfies
$\mathbb Ee^{\theta J^\alpha}=\infty$ for $\theta>0$, $\alpha>3/4$, and
$\|J\|_q\ge c_{a,b}q^{4/3}$ for all sufficiently large $q$.</p>

<p><em>Proof.</em> Fix $|\lambda|\le\Lambda$ and use the Brownian representation at this one parameter. Set
$W_\lambda(t)=B(t)+\lambda t-t^2/2$ and
$R_\lambda(t)=W_\lambda(t)-\min_{s\le t}W_\lambda(s)$.
For $L\ge L_0=\max\{2,2\Lambda\}$ consider the event</p>
<div class="math-display">$$
E_L=\left\{5L^2\le B(L)\le6L^2,\quad
\min_{0\le u\le L}(B(L+u)-B(L))\ge-L^2\right\}.
$$</div>
<p>The two conditions are independent. The normal density gives probability at least
$L^{3/2}(2\pi)^{-1/2}e^{-18L^3}$ for the first. By reflection, the second has probability
$2\Phi(L^{3/2})-1\ge p_0:=2\Phi(1)-1>0$, where $\Phi$ is the standard normal distribution function. Hence</p>
<div class="math-display">$$
\mathbb P(E_L)\ge\frac{p_0}{\sqrt{2\pi}}e^{-18L^3}.
$$</div>
<p>On $E_L$, throughout $[L,2L]$ we have $B(t)\ge4L^2$ and therefore
$W_\lambda(t)\ge2L^2-2\Lambda L\ge L^2$. The running minimum is at most $W_\lambda(0)=0$, so $R_\lambda(t)\ge L^2$. This entire interval lies in one excursion, whose length $\ell$ is at least $L$ and whose area $A$ is at least $L^3$.</p>
<p>Select this excursion using the Brownian path alone. Conditional on that path, GGL3 assigns it a Poisson mark $Y$ of mean $A$. Since $A\ge8$, Chebyshev's inequality gives
$\mathbb P(Y\ge A/2\mid B)\ge1-4/A\ge1/2$. On this further event its contribution to $H$ is at least $\ell A/2\ge L^4/2$. Thus, with $c_0=p_0/(2\sqrt{2\pi})$,</p>
<div class="math-display">$$
\mathbb P(H(\lambda)\ge L^4/2)\ge c_0e^{-18L^3}.
$$</div>
<p>The excursions and their areas are finite almost surely by the Brownian construction in 2N9T; selecting an excursion before looking at the marks preserves its conditional Poisson law. Taking $L=(2x)^{1/4}$ proves the first assertion, with $x_0=L_0^4/2$ and $C=18\cdot2^{3/4}$.</p>
<p>For $q\ge18L_0^3$, take $L=(q/18)^{1/3}$ in the same bound. Then</p>
<div class="math-display">$$
\|H(\lambda)\|_q
\ge\frac12(q/18)^{4/3}c_0^{1/q}e^{-1}
\ge\frac{c_0}{2e\,18^{4/3}}q^{4/3}.
$$</div>
<p>Also
$\mathbb Ee^{\theta H^\alpha}\ge e^{\theta x^\alpha}\mathbb P(H\ge x)$, which tends to infinity with $x$ when $\alpha>3/4$. The finite-graph weighted surplus is increasing in the common-edge coupling: a merger of sizes $u,v$ and surplus counts $r,s$ increases its unscaled value by $us+vr$, and an internal edge increases it by the component size. Hence the infimum over $|\lambda|\le\Lambda$ is attained at $-\Lambda$. Apply 1QUE there to the bounded continuous functions
$h\mapsto\min\{M,e^{\theta h^\alpha}\}$ and then let $M\to\infty$. This proves uniform divergence of the finite expectations.</p>
<p>Finally, EURS gives an increasing version of $H$, so
$J\ge(b-a)H(a)$. The moment and exponential assertions for $J$ follow immediately. $\square$</p>
<p>This is a lower bound only. It does not give a matching upper tail estimate or decide which exponential moments of $H^{3/4}$ are finite. The argument uses a Brownian representation at a fixed parameter, not a common Brownian representation of the parameter-indexed coalescent.</p>

## The surplus Laplace transform at its boundary {#section-weighted-surplus-laplace-boundary}

<p>Fix $a<b$, and retain the notation</p>
<div class="math-display">$$
I_N=\int_a^b\|\mathbf L_N(\lambda)\|_2^2\,d\lambda,
\quad J_N=\int_a^bH_N(\lambda)\,d\lambda,
\qquad
I=\int_a^b\|\mathbf X(\lambda)\|_2^2\,d\lambda,
\quad J=\int_a^bH(\lambda)\,d\lambda.
$$</div>
<p>Here $J$ includes inherited surplus. It is different from the count of new cycles in 0Y6N.</p>

<a id="tag-B7V7" data-assertion="theorem" data-title="Joint size and weighted-surplus Laplace transforms converge with all derivatives up to the closed surplus half-plane, but the surplus Taylor series at zero has radius zero"></a>
<p>Define, for $z\in\mathbb C$ and $\operatorname{Re}w\ge0$,</p>
<div class="math-display">$$
\mathcal L_N(z,w)=\mathbb E e^{zI_N-wJ_N},
\qquad
\mathcal L(z,w)=\mathbb E e^{zI-wJ}.
$$</div>
<p>The limit is entire in $z$ for each such $w$, and jointly holomorphic on
$\mathbb C\times\{\operatorname{Re}w>0\}$. For every pair of nonnegative integers $m,n$,</p>
<div class="math-display">$$
\mathbb E[I_N^m(-J_N)^n e^{zI_N-wJ_N}]
\longrightarrow
\mathbb E[I^m(-J)^n e^{zI-wJ}]
$$</div>
<p>uniformly on every compact subset of
$\mathbb C\times\{\operatorname{Re}w\ge0\}$. These expressions are the mixed derivatives in the interior, with continuous extensions to the boundary.</p>
<p>The function $w\mapsto\mathcal L(0,w)$ on the nonnegative real axis has right derivatives of every order at zero, equal to
$(-1)^n\mathbb EJ^n$. Nevertheless its Taylor series there has radius zero. In particular it has no holomorphic extension to a neighborhood of zero, and
$\mathbb Ee^{-wJ}=\infty$ for every negative real $w$.</p>

<p><em>Proof.</em> Put $T=b-a$. Monotonicity gives
$I_N\le T\|\mathbf L_N(b)\|_2^2$ and $J_N\le TH_N(b)$, with the same bounds in the limit. By 7CDV and QKHG, Hölder's inequality bounds, uniformly in $N$,</p>
<div class="math-display">$$
\mathbb E[I_N^mJ_N^n e^{BI_N}]<C_{B,m,n}
\qquad(B\ge0;\ m,n\ge0).
$$</div>
<p>The limiting expectation is finite as well. Size powers are absorbed into a slightly larger exponential; the remaining surplus powers have all moments. For fixed $z,w$ in the closed domain, apply DK7F to the real and imaginary parts of the integral functional
$I^m(-J)^ne^{zI-wJ}$. Integration is continuous under the joint $J_1$ convergence in EURS, and the displayed bound supplies the required growth control. This proves pointwise convergence.</p>
<p>For local uniformity, take a compact set of parameters and let $B$ bound zero and their real $z$-coordinates. The segment between any two parameter points stays in the closed half-plane. Integration along this segment yields</p>
<div class="math-display">$$
\left|I^mJ^n\left(e^{zI-wJ}-e^{z'I-w'J}\right)\right|
\le I^mJ^n e^{BI}
\left(|z-z'|I+|w-w'|J\right).
$$</div>
<p>The same estimate holds at finite $N$. The preceding moment bounds make the expectations uniformly Lipschitz on the compact set. A finite parameter net upgrades pointwise convergence to uniform convergence, for every $m,n$.</p>
<p>Dominated differentiation gives the stated holomorphy and identifies the derivatives in the interior. The same moment domination gives their continuous boundary values and all right derivatives at real $w=0$. Finite-$N$ transforms are entire in both variables because the graph has finitely many vertices and edges, so $I_N,J_N$ are bounded.</p>
<p>By 7E7T, for all sufficiently large integers $n$,
$(\mathbb EJ^n)^{1/n}\ge c_{a,b}n^{4/3}$. Since $(n!)^{1/n}\le n$,</p>
<div class="math-display">$$
\left(\frac{\mathbb EJ^n}{n!}\right)^{1/n}
\ge c_{a,b}n^{1/3}\longrightarrow\infty.
$$</div>
<p>The Taylor radius is therefore zero. Any holomorphic extension would have these same Taylor coefficients, which is impossible. Divergence for negative real $w$ is 7E7T with $\alpha=1$. $\square$</p>


## Poisson approximation with size weights {#section-weighted-surplus-poisson-kernel}

<p>At a fixed critical parameter, the discovery transcript determines the component sizes and the number of unused surplus-edge candidates in each component. It does not reveal those candidate bits. Their conditional law is independent Bernoulli by GGL3. To retain this conditional information in the limit, it is convenient to use the weighted surplus coordinates themselves.</p>
<p>Let $\ell^1_+$ be the nonnegative summable sequences. For probability measures on this space with finite first moment, write</p>
<div class="math-display">$$
W_1(P,Q)=\inf\mathbb E\|Z-Z'\|_1,
$$</div>
<p>where the infimum is over couplings with laws $P,Q$. Given
a nonnegative square-summable sequence $x$ and $v\in\ell^1_+$ with $v_i=0$ whenever $x_i=0$, define the probability kernel</p>
<div class="math-display">$$
\mathcal P(x,v)=\operatorname{Law}\bigl((x_iP_i)_i\bigr),
\qquad P_i\text{ independent},\quad
P_i\sim\operatorname{Poisson}(v_i/x_i)\quad(x_i>0).
$$</div>
<p>Zero-mass coordinates are set to zero. The random sequence belongs to $\ell^1_+$ almost surely, since its expected norm is $\sum_i v_i<\infty$.</p>

<a id="tag-OPH4" data-assertion="proposition" data-title="Weighted Bernoulli surplus admits a quantitative Poisson coupling and the Poisson kernel is continuous in first Wasserstein distance at positive mass sequences"></a>
<p>For finitely many nonnegative masses $x_i$, nonnegative integers $K_i$, and $0\le p\le1$, let $Y_i$ be independent $\operatorname{Bin}(K_i,p)$ variables and set $v_i=x_i pK_i$. Then</p>
<div class="math-display">$$
W_1\!\left(\operatorname{Law}((x_iY_i)_i),\mathcal P(x,v)\right)
\le p\sum_i v_i.
$$</div>
<p>Moreover, if $x^{(n)}\to x$ in $\ell^2$ and $v^{(n)}\to v$ in $\ell^1$, all pairs satisfy the preceding zero-coordinate condition, and $x_i>0$ for every $i$, then</p>
<div class="math-display">$$
W_1\bigl(\mathcal P(x^{(n)},v^{(n)}),\mathcal P(x,v)\bigr)
\longrightarrow0.
$$</div>

<p><em>Proof.</em> Couple a Bernoulli($p$) variable $\xi$ to $P\sim\operatorname{Poisson}(p)$ as follows. Set $\xi=1$ when $P\ge1$. When $P=0$, set $\xi=1$ with probability
$(p-1+e^{-p})/e^{-p}$, using an independent randomization. This is a valid probability for $0\le p\le1$, and $\mathbb P(\xi=1)=p$. The discrepancy is</p>
<div class="math-display">$$
\mathbb E|\xi-P|
=2(p-1+e^{-p})\le p^2.
$$</div>
<p>Use independent copies for every candidate edge. Summing them within each component gives the required binomial and Poisson variables, and</p>
<div class="math-display">$$
\mathbb E\sum_i x_i|Y_i-P_i|
\le p^2\sum_i x_iK_i=p\sum_i v_i.
$$</div>
<p>For continuity, first retain $k$ coordinates. Their limiting masses are positive, so their Poisson parameters
$a_i^{(n)}=v_i^{(n)}/x_i^{(n)}$ converge to $a_i=v_i/x_i$. Use a common rate-one Poisson process at times $a_i^{(n)},a_i$ for each coordinate. Its expected absolute increment is $|a_i^{(n)}-a_i|$, and hence</p>
<div class="math-display">$$
\mathbb E\left|x_i^{(n)}P_i(a_i^{(n)})-x_iP_i(a_i)\right|
\le |x_i^{(n)}-x_i|a_i^{(n)}
   +x_i|a_i^{(n)}-a_i|\longrightarrow0.
$$</div>
<p>Couple the remaining coordinates in any way. Their expected contribution to the distance is at most
$\sum_{i>k}(v_i^{(n)}+v_i)$. Convergence in $\ell^1$ makes this arbitrarily small by first increasing $k$ and then $n$. $\square$</p>

## The conditional surplus law and its variance {#section-critical-surplus-conditional-law}

<p>Let $\mathcal D_N$ be the complete discovery transcript at
$p_N=(1+\lambda_NN^{-1/3})/N$, where $\lambda_N\to\lambda$. In decreasing component order, put</p>
<div class="math-display">$$
x_{N,i}=N^{-2/3}|\mathcal C_i|,\qquad
z_{N,i}=x_{N,i}\sigma(\mathcal C_i),\qquad
v_{N,i}=x_{N,i}p_NK_{N,i},
$$</div>
<p>where $K_{N,i}$ is the number of unused surplus-edge candidates in $\mathcal C_i$. Thus
$v_{N,i}=\mathbb E[z_{N,i}\mid\mathcal D_N]$.
Write $\mathcal Q_N=\operatorname{Law}(z_N\mid\mathcal D_N)$, regarded as a random probability measure on $\ell^1_+$ with its $W_1$ metric.</p>
<p>For the limiting Brownian excursions, let $\ell_i$ be their ranked lengths and $A_i$ their areas. Conditional on the Brownian path $B$, take independent $Y_i\sim\operatorname{Poisson}(A_i)$, and put</p>
<div class="math-display">$$
v_i=\ell_i A_i,\qquad z_i=\ell_iY_i,
\qquad V=\sum_i v_i,\quad H=\sum_i z_i,\quad
U=\sum_i\ell_i v_i=\sum_i\ell_i^2A_i.
$$</div>
<p>Here $V<\infty$ almost surely by O4TX, and $U\le\ell_1V<\infty$.</p>

<a id="tag-OWBW" data-assertion="theorem" data-title="Critical weighted surplus and its conditional mean converge jointly with the conditional law in first Wasserstein distance, yielding the excursion and mark decomposition of variance"></a>
<p>With $\mathcal P_1(\ell^1_+)$ denoting the probability measures of finite first moment,</p>
<div class="math-display">$$
(x_N,v_N,z_N,\mathcal Q_N)
\ \xrightarrow{\ d\ }\
(\ell,v,z,\mathcal P(\ell,v))
\quad\text{in }
\ell^2_\downarrow\times\ell^1_+\times\ell^1_+
\times\mathcal P_1(\ell^1_+).
$$</div>
<p>The last coordinate uses $W_1$. For $|\lambda_N|\le\Lambda$, its finite Poisson approximation has the quantitative bound</p>
<div class="math-display">$$
\mathbb E W_1\bigl(\mathcal Q_N,\mathcal P(x_N,v_N)\bigr)
\le p_N\mathbb EH_N=O_\Lambda(N^{-1}),
\qquad H_N=\sum_i z_{N,i}.
$$</div>
<p>Put $S_N=\|x_N\|_2^2$, $V_N=\sum_i v_{N,i}$ and
$U_N=\sum_i x_{N,i}v_{N,i}$, with $S=\|\ell\|_2^2$ in the limit. All joint polynomial moments of $(S_N,H_N,V_N,U_N)$ converge to those of $(S,H,V,U)$. In particular,</p>
<div class="math-display">$$
\begin{aligned}
\operatorname{Var}(H_N)
 &=(1-p_N)\mathbb EU_N+\operatorname{Var}(V_N)\\
 &\longrightarrow \mathbb EU+\operatorname{Var}(V)
 =\operatorname{Var}(H),
\qquad
\operatorname{Cov}(H,V)=\operatorname{Var}(V).
\end{aligned}
$$</div>
<p>The limiting conditional moment generating function is finite at every real $t$ and is given by</p>
<div class="math-display">$$
\mathbb E[e^{tH}\mid B]
=\exp\!\left(\sum_i A_i(e^{t\ell_i}-1)\right).
$$</div>
<p>It extends to an entire function of $t$ for almost every Brownian path. Its conditional cumulants are
$\kappa_r(H\mid B)=\sum_i\ell_i^r A_i$ for integers $r\ge1$.</p>

<p><em>Proof.</em> We first retain finitely many ranks. In the excursion matching argument of M7BY and 59NH, the queue paths converge uniformly on compact intervals and the matched excursion endpoints converge. The number $K_{N,i}$ is the sum of the surplus candidate counts over that component. At each exploration step that count differs from the active queue size by at most one, as in GGL3. Since $Np_N\to1$, the corresponding Riemann sum therefore gives</p>
<div class="math-display">$$
p_NK_{N,i}\ \xrightarrow{\ d\ }\ A_i
$$</div>
<p>jointly for every finite set of ranks, with their sizes and marks. To justify the random integration endpoints, first confine these excursions to a deterministic compact interval with arbitrarily high probability and use uniform convergence there. The at-most-one errors total at most $p_N|\mathcal C_i|=O_{\mathbb P}(N^{-1/3})$ at each retained rank. The limiting positive lengths are distinct, so their ranks eventually match. These are the same moving-parameter exploration limits used in M7BY.</p>
<p>It remains to control the conditional-mean tail. There is a useful identity that avoids conditioning on any unexplored remainder:</p>
<div class="math-display">$$
\mathbb E\sum_{i>k}v_{N,i}
=\mathbb E\sum_{i>k}z_{N,i}
\longrightarrow
\mathbb E\sum_{i>k}z_i
=\mathbb E\sum_{i>k}v_i.
$$</div>
<p>For fixed $k$, the middle convergence follows from 1QUE and the uniform integrability in O4TX: the weighted rank tail is a continuous nonnegative functional bounded by $H_N$. The last expectation tends to zero as $k\to\infty$, since $V$ is integrable. Markov's inequality now makes the $\ell^1$ tails of $v_N$ negligible. Together with the weighted-mark tails in 1QUE and the size tails in M7BY, finite-rank convergence proves the joint limit of $(x_N,v_N,z_N)$.</p>
<p>Conditionally on $\mathcal D_N$, the component surplus counts are independent binomials with parameters $K_{N,i},p_N$. OPH4 gives the displayed $W_1$ bound after averaging, because
$\mathbb EV_N=\mathbb EH_N$. O4TX bounds this mean uniformly on compact parameter intervals. The same lemma makes
$(x,v)\mapsto\mathcal P(x,v)$ continuous at the limiting pair, whose masses are all positive. The continuous mapping theorem and the vanishing Poisson approximation error give joint convergence of the random kernels as well. Given $B$, the limiting weighted marks have precisely this kernel, by GGL3.</p>
<p>Summation is continuous in $\ell^1$. The functional
$(x,v)\mapsto\sum_i x_i v_i$ is also continuous in the product topology, since</p>
<div class="math-display">$$
\left|\sum_i x_i^{(n)}v_i^{(n)}-\sum_i x_iv_i\right|
\le\|x^{(n)}-x\|_\infty\|v^{(n)}\|_1
  +\|x\|_\infty\|v^{(n)}-v\|_1.
$$</div>
<p>Thus the four scalar quantities converge jointly in distribution. Conditional Jensen gives
$\mathbb EV_N^q\le\mathbb EH_N^q$ for $q\ge1$, and $U_N\le\sqrt{S_N}V_N$. QKHG and 7CDV therefore bound every moment of each of the four quantities, uniformly in $N$. Hölder's inequality bounds a higher moment of every polynomial in them. Uniform integrability proves convergence of all joint polynomial moments.</p>
<p>The conditional mean of $H_N$ is $V_N$, and its conditional variance is</p>
<div class="math-display">$$
\sum_i x_{N,i}^2K_{N,i}p_N(1-p_N)=(1-p_N)U_N.
$$</div>
<p>In the limit, independence of the Poisson marks gives conditional mean $V$ and conditional variance $U$. These calculations can first be made for finitely many ranks and then passed to the limit in conditional $L^2$, since the sums defining $V,U$ are finite. Total variance gives the two decompositions, and the moment convergence passes the finite one to the limit. Finally,
$\mathbb E[HV]=\mathbb E[V\mathbb E(H\mid B)]=\mathbb EV^2$, proving the covariance identity.</p>
<p>For the transform, independence gives the formula for every finite rank cutoff. If $R=\ell_1$ and $t\in\mathbb C$, then</p>
<div class="math-display">$$
\sum_i A_i|e^{t\ell_i}-1|
\le |t|e^{|t|R}\sum_i\ell_iA_i
=|t|e^{|t|R}V<\infty.
$$</div>
<p>For positive real $t$, monotone convergence gives the full conditional moment generating function and its finiteness; negative or complex $t$ then follow by domination. The bound is uniform on compact subsets of the complex plane, so the conditional transform is entire. Termwise differentiation of its logarithm gives the cumulants. $\square$</p>
<p>The variance term $\mathbb EU$ comes from the random cycle marks given the exploration; $\operatorname{Var}(V)$ comes from the random excursion geometry. Conditioning is on that geometry, not merely on the component sizes. Although every conditional exponential moment is finite, averaging over the geometry makes every positive exponential moment of $H$ infinite by 7E7T. The theorem concerns a fixed parameter, or a convergent sequence of parameters; it makes no assertion about a path of conditional kernels across the critical window.</p>


## The exact surplus drift in the simple graph {#section-critical-surplus-exact-drift}

<p>Give each edge of the complete graph an independent uniform arrival threshold, and retain it when that threshold is at most
$p_N(\lambda)=(1+\lambda N^{-1/3})/N$. This fixes the graph process and its natural filtration as $\lambda$ increases. For a current component of size $k_i$ and surplus $y_i$, put
$x_i=N^{-2/3}k_i$, and write</p>
<div class="math-display">$$
S_N=\sum_i x_i^2,\qquad H_N=\sum_i x_i y_i,
\qquad
\mathcal B_N=S_NH_N-\sum_i x_i^3y_i+\frac12\sum_i x_i^3.
$$</div>

<a id="tag-WVGG" data-assertion="proposition" data-title="The finite simple-graph weighted-surplus drift has an exact correction to the augmented-coalescent drift"></a>
<p>At every parameter with $0<p_N(\lambda)<1$, the drift of $H_N$ per unit $\lambda$ is</p>
<div class="math-display">$$
b_N(\lambda)=
\frac{\mathcal B_N(\lambda)
-\frac32N^{-2/3}S_N(\lambda)+N^{-1}
-N^{-4/3}H_N(\lambda)}{1-p_N(\lambda)}.
$$</div>
<p>In particular, on any closed interval $[a,b]$ of such parameters,</p>
<div class="math-display">$$
M_N(t)=H_N(t)-H_N(a)-\int_a^t b_N(u)\,du
$$</div>
<p>is a square-integrable martingale. For every fixed bounded critical parameter interval,</p>
<div class="math-display">$$
\mathbb E\sup_{a\le t\le b}
|b_N(t)-\mathcal B_N(t)|=O_{a,b}(N^{-2/3}).
$$</div>
<p>The last estimate holds for all sufficiently large $N$.</p>

<p><em>Proof.</em> A closed edge has conditional opening rate
$N^{-4/3}/(1-p_N)$ per unit parameter. Between distinct components $i,j$ there are $k_i k_j$ such edges. Opening one merges the components and increases $H_N$ by $x_i y_j+x_j y_i$, giving total merger drift</p>
<div class="math-display">$$
\frac1{1-p_N}\sum_{i<j}x_ix_j(x_i y_j+x_j y_i)
=\frac{S_NH_N-\sum_i x_i^3y_i}{1-p_N}.
$$</div>
<p>Inside component $i$, exactly $k_i-1+y_i$ edges are already present. Its number of closed internal edges is therefore</p>
<div class="math-display">$$
\binom{k_i}{2}-(k_i-1+y_i)
=\frac12k_i^2-\frac32k_i+1-y_i.
$$</div>
<p>Each opening increases $H_N$ by $x_i$. Multiply by the edge rate and sum. Since $\sum_i x_i=N^{1/3}$, the internal drift is</p>
<div class="math-display">$$
\frac{\frac12\sum_i x_i^3-\frac32N^{-2/3}S_N
+N^{-1}-N^{-4/3}H_N}{1-p_N}.
$$</div>
<p>Adding the two expressions proves the formula, including singleton components, whose internal-edge count is zero. The finite-state jump process is nonexplosive and $H_N$ is bounded for fixed $N$. Its compensator identity proves the martingale assertion. The integral may use the state just before a jump; this gives the same integral with respect to $du$.</p>
<p>All terms in the merger sum are nonnegative, and
$0\le\mathcal B_N\le S_NH_N+S_N^{3/2}/2$. On a fixed critical interval, $p_N=O(N^{-1})$ uniformly, and $S_N,H_N$ increase. Thus</p>
<div class="math-display">$$
\sup_{[a,b]}|b_N-\mathcal B_N|
\le C_{a,b}\left[
N^{-1}\bigl(S_N(b)H_N(b)+S_N(b)^{3/2}\bigr)
+N^{-2/3}S_N(b)+N^{-1}+N^{-4/3}H_N(b)
\right].
$$</div>
<p>QKHG and 7CDV bound the expectation of the bracketed terminal quantities, using Hölder for the product. This proves the final estimate. $\square$</p>

## The limiting martingale and the derivative of the mean {#section-critical-surplus-mean-derivative}

<p>Use the joint size and surplus-measure process $(\mathbf X,\mu)$ of EAQD. Write
$S=\|\mathbf X\|_2^2$, $H=\mu([0,\infty))$, and define</p>
<div class="math-display">$$
\mathcal B(x,\mu)=
\|x\|_2^2\mu([0,\infty))-
\int_0^\infty u^2\,\mu(du)+\frac12\sum_i x_i^3.
$$</div>
<p>At an actual marked state, $\mu=\sum_i x_i y_i\delta_{x_i}$, so the integral is $\sum_i x_i^3y_i$. It is finite because the support of $\mu$ lies in $[0,\|x\|_2]$.</p>

<a id="tag-83JM" data-assertion="theorem" data-title="Critical weighted surplus has a compensated martingale limit and its mean converges with its first parameter derivative"></a>
<p>For every $a<b$,</p>
<div class="math-display">$$
M(t)=H(t)-H(a)-\int_a^t\mathcal B(\mathbf X(u),\mu(u))\,du
\qquad(a\le t\le b)
$$</div>
<p>is a square-integrable càdlàg martingale with respect to the completed right-continuous natural filtration of $(\mathbf X,\mu)$ on $[a,b]$. The finite martingales $M_N$ converge to $M$ jointly with the size and surplus-measure paths in $J_1$, using one time change for all coordinates.</p>
<p>The mean $h(\lambda)=\mathbb EH(\lambda)$ is continuously differentiable on $\mathbb R$, with</p>
<div class="math-display">$$
h'(\lambda)=
\mathbb E\!\left[
S(\lambda)H(\lambda)-\sum_i X_i(\lambda)^3Y_i(\lambda)
+\frac12\sum_i X_i(\lambda)^3\right]>0.
$$</div>
<p>If $h_N(\lambda)=\mathbb EH_N(\lambda)$, then, for every $\Lambda\ge0$,</p>
<div class="math-display">$$
\sup_{|\lambda|\le\Lambda}
\bigl(|h_N(\lambda)-h(\lambda)|+
      |h_N'(\lambda)-h'(\lambda)|\bigr)
\longrightarrow0.
$$</div>
<p>Every parameter here lies in the interior of the finite graph's admissible range for sufficiently large $N$.</p>

<p><em>Proof.</em> We first check continuity of the drift. The subset of EAQD's state space given by</p>
<div class="math-display">$$
\mathcal E_*=
\{(x,\nu):\operatorname{supp}\nu\subseteq[0,\|x\|_2]\}
$$</div>
<p>is closed. Indeed, along a converging sequence the norm bounds converge, and weak convergence cannot put mass outside their limiting interval. On such a sequence all supports lie in one compact interval. The integral of $u^2$ is therefore continuous: replace $u^2$ outside that interval by a bounded continuous extension and use weak convergence. Also $\sum_i x_i^3$ is continuous in $\ell^2$, by factoring the difference of cubes and applying Cauchy–Schwarz. Consequently $\mathcal B$ is continuous on $\mathcal E_*$, and</p>
<div class="math-display">$$
0\le\mathcal B(x,\nu)
\le \|x\|_2^2\nu([0,\infty))+\frac12\|x\|_2^3.
$$</div>
<p>All finite and limiting paths lie in this closed subspace.</p>
<p>In a Skorokhod representation of EAQD's path convergence, the state values converge at every continuity time of the limiting path. The drift values converge at those times by the preceding continuity. The norms and total measure masses have a common finite bound along each convergent sequence of paths, so the drifts are bounded as well. Dominated convergence gives uniform convergence of their time integrals. WVGG's error estimate then replaces the finite drift $\mathcal B_N$ by $b_N$, in probability uniformly after integration. The compensators are continuous paths; adding them to the total-mass coordinate preserves the common $J_1$ time change. This proves the joint convergence including $M_N$.</p>
<p>To pass the martingale identity, fix $a\le t_1<\cdots<t_k\le s<t\le b$ and multiply $M_N(t)-M_N(s)$ by a bounded continuous function of the state values at $t_1,\ldots,t_k$. Its expectation is zero by WVGG. The limiting state has no deterministic jump by EAQD, so joint path convergence gives convergence of this product in distribution. Moreover, for all large $N$ the supremum of $|M_N|$ is bounded by a constant times</p>
<div class="math-display">$$
1+H_N(b)+(b-a)
\bigl(S_N(b)H_N(b)+S_N(b)^{3/2}\bigr).
$$</div>
<p>QKHG and 7CDV bound the second moment of this expression uniformly. Thus the products are uniformly integrable and their limiting expectations are zero. A monotone-class argument extends the identity to the natural past sigma-field, since càdlàg paths are determined by their values at a countable dense set of times. The same moment bounds hold for $M$. Its right continuity and uniform integrability extend the identity to the right-continuous completion of that filtration. This proves that $M$ is square-integrable and a martingale.</p>
<p>Taking expectations between two deterministic parameters gives</p>
<div class="math-display">$$
h(t)-h(s)=\int_s^t
\mathbb E\mathcal B(\mathbf X(u),\mu(u))\,du.
$$</div>
<p>The integrand is continuous in $u$. At a fixed parameter the state has no jump almost surely, and the continuity of $\mathcal B$ gives convergence along any sequence of nearby parameters. On a containing compact interval, the drift is dominated by
$S(b)H(b)+S(b)^{3/2}/2$, which is integrable. Dominated convergence proves the claimed continuity. The fundamental theorem of calculus gives the derivative formula. Its merger term is nonnegative, while $\sum_iX_i^3>0$ almost surely by 2N9T. Hence $h'(\lambda)>0$ at every parameter.</p>
<p>For finite $N$, the mean is a polynomial in $p_N$ times the fixed size normalization, and WVGG gives $h_N'(\lambda)=\mathbb Eb_N(\lambda)$. Along any $\lambda_N\to\lambda$, 1QUE implies convergence of $(x_N,(x_{N,i}y_{N,i})_i)$ in $\ell^2\times\ell^1$. The map to the drift is continuous in these coordinates as well, since
$\sum_i x_i^2 z_i$ is continuous when $x$ converges in $\ell^2$ and $z$ in $\ell^1$. QKHG and 7CDV give uniform integrability of the drifts. Thus
$\mathbb E\mathcal B_N(\lambda_N)\to h'(\lambda)$, and the error estimate of WVGG gives
$h_N'(\lambda_N)\to h'(\lambda)$. Compactness and continuity of $h'$ upgrade this moving-parameter limit to uniform convergence on $[-\Lambda,\Lambda]$. Uniform convergence of the means is O4TX. $\square$</p>
<p>The derivative also has a formula involving only excursion geometry. At a fixed parameter let $\ell_i,A_i$ be the Brownian excursion lengths and areas, put $S=\sum_i\ell_i^2$ and $V=\sum_i\ell_iA_i$, and condition as in OWBW. Then</p>
<div class="math-display">$$
h'(\lambda)=
\mathbb E\!\left[
SV-\sum_i\ell_i^3A_i+\frac12\sum_i\ell_i^3\right].
$$</div>
<p>The difference $SV-\sum_i\ell_i^3A_i$ is nonnegative and is the expected increase due to mergers. The last term is the expected increase due to new cycle marks. All terms are integrable by the moment bounds above.</p>


## Drift of surplus across component sizes {#section-surplus-profile-drift}

<p>To follow the location of surplus, test the measure $\mu=\sum_i x_i y_i\delta_{x_i}$ against a function $f$. We allow every locally Lipschitz $f:[0,\infty)\to\mathbb R$ for which there are finite $C,m\ge0$ such that</p>
<div class="math-display">$$
\sup_{0\le u\le R}|f(u)|+\operatorname{Lip}(f|_{[0,R]})
\le C(1+R^m)\qquad(R\ge1).
$$</div>
<p>This class includes bounded Lipschitz functions and every polynomial. Put $g(u)=uf(u)$ and, on the closed state space $\mathcal E_*$ of 83JM, define</p>
<div class="math-display">$$
\begin{aligned}
F_f(x,\mu)&=\int f(u)\,\mu(du),\\
\Gamma_f(x;u)&=
\sum_j x_j\bigl[g(u+x_j)-g(u)\bigr]
-u\bigl[g(2u)-g(u)\bigr],\\
\mathcal B_f(x,\mu)&=
\int\Gamma_f(x;u)\,\mu(du)
+\frac12\sum_i x_i^3f(x_i).
\end{aligned}
$$</div>
<p>The subtracted term removes a component's merger with itself. It remains well defined when several components have equal size: the size sequence records their multiplicities, while the measure combines their surplus weights.</p>

<a id="tag-LX6L" data-assertion="proposition" data-title="Surplus profile tests have a continuous drift on size-measure states and an exact finite simple-graph correction"></a>
<p>The series defining $\Gamma_f$ converges absolutely and uniformly on bounded $u$-intervals for each $x\in\ell^2_\downarrow$. Both $F_f$ and $\mathcal B_f$ are continuous on $\mathcal E_*$. On an actual marked state, $\mathcal B_f$ is the absolutely convergent sum of the merger and surplus-birth increments of $F_f$, weighted by the augmented-coalescent rates.</p>
<p>For the common-edge critical Erdős–Rényi graph with $p_N(\lambda)=(1+\lambda N^{-1/3})/N$, write $F_{N,f}=F_f(x_N,\mu_N)$. Its exact drift per unit parameter is</p>
<div class="math-display">$$
b_{N,f}=
\frac{1}{1-p_N}\left[
\mathcal B_f(x_N,\mu_N)
-\frac32N^{-2/3}\sum_i x_{N,i}^2 f(x_{N,i})
+N^{-4/3}\sum_i x_{N,i}f(x_{N,i})
-N^{-4/3}F_{N,f}
\right].
$$</div>
<p>On every fixed critical interval $[a,b]$,</p>
<div class="math-display">$$
\mathbb E\sup_{a\le t\le b}
\left|b_{N,f}(t)-\mathcal B_f(x_N(t),\mu_N(t))\right|
=O_{f,a,b}(N^{-2/3}).
$$</div>

<p><em>Proof.</em> For masses $u,v$ with marks $r,s$, a merger changes $F_f$ by</p>
<div class="math-display">$$
r[g(u+v)-g(u)]+s[g(u+v)-g(v)].
$$</div>
<p>Its rate is $uv$. Collecting the terms carrying the marks of component $i$, with $z_i=x_i y_i$, gives
$z_i\sum_{j\ne i}x_j[g(x_i+x_j)-g(x_i)]$. Summing over $i$ is exactly the integral of $\Gamma_f$. A new surplus mark in component $i$ changes $F_f$ by $x_if(x_i)$ at rate $x_i^2/2$, giving the last term in $\mathcal B_f$.</p>
<p>Here the countable merger sum is absolutely convergent. To see this before rearranging it, set $R=\max\{1,\|x\|_2\}$, and let $A,L$ be the supremum norm and Lipschitz constant of $f$ on $[0,2R]$. The increase of total weighted surplus at the same merger is $\Delta H=us+vr$. Transporting the old weights and adding that increase, as in GZ95, gives</p>
<div class="math-display">$$
|\Delta F_f|\le A\Delta H+Luv(r+s)
\le(A+LR)\Delta H.
$$</div>
<p>Thus the sum of the absolute merger contributions is at most
$(A+LR)(SH-\sum_i x_i^3y_i)$. The absolute birth contribution is at most $A\sum_i x_i^3/2$. Both are finite.</p>
<p>For continuity on all of $\mathcal E_*$, note that $g$ is Lipschitz on $[0,2R]$ with constant at most $K=A+2RL$. For $0\le u\le R$ the tail of the series in $\Gamma_f$ is bounded uniformly by
$K\sum_{j>k}x_j^2$. The same estimate holds uniformly along an $\ell^2$-convergent sequence. Its finite-coordinate sums converge uniformly on $[0,R]$, so the full kernels do too. The diagonal term is continuous in $u$. Weak convergence of the measures, their bounded total masses and their common compact support now give convergence of the integrals. The same compact-support argument proves continuity of $F_f$. The cubic birth sum is continuous by finite-coordinate convergence and the tail bound
$A R\sum_{i>k}x_i^2$.</p>
<p>In particular, writing $H=\mu([0,\infty))$ and $S=\|x\|_2^2$, the definitions on $\mathcal E_*$ satisfy</p>
<div class="math-display">$$
|F_f|\le AH,\qquad
|\mathcal B_f|\le 2KSH+\frac12 A S^{3/2}.
$$</div>
<p>These are polynomial bounds in $\sqrt S$ and $H$, by the hypothesis on $f$. Uniform convergence on any other bounded $u$-interval follows by taking a larger $R$.</p>
<p>In the simple graph the merger drift has the factor $(1-p_N)^{-1}$. For births, use the closed internal-edge count
$(k_i^2-3k_i+2)/2-y_i$ from WVGG, multiply by the increment $x_if(x_i)$ and the per-edge rate $N^{-4/3}/(1-p_N)$, and sum. This gives the displayed exact formula.</p>
<p>For the error estimate, throughout $[a,b]$ use
$R=\max\{1,\sqrt{S_N(b)}\}$ to bound $A,L,K$ for every state. Also</p>
<div class="math-display">$$
\left|\sum_i x_{N,i}^2f(x_{N,i})\right|\le A S_N,\qquad
\left|\sum_i x_{N,i}f(x_{N,i})\right|\le A N^{1/3},
\qquad |F_{N,f}|\le A H_N.
$$</div>
<p>Since $p_N=O(N^{-1})$ uniformly, the difference from $\mathcal B_f$ is bounded by $O_{f,a,b}(N^{-2/3})$ times a fixed polynomial in $S_N(b)$ and $H_N(b)$. Its expectation is bounded by QKHG and 7CDV. $\square$</p>

## Martingales and mean equations for the surplus profile {#section-surplus-profile-martingales}

<p>Let $(\mathbf X,\mu)$ be the limiting critical Erdős–Rényi size/measure process of EAQD, and retain the finite processes and test class of LX6L.</p>

<a id="tag-E4JW" data-assertion="theorem" data-title="Surplus measure tests satisfy limiting martingale equations and compact uniform convergence of their mean derivatives, including polynomial surplus profiles"></a>
<p>For every $f$ in the preceding class and every $a<b$,</p>
<div class="math-display">$$
M_f(t)=F_f(\mathbf X(t),\mu(t))-F_f(\mathbf X(a),\mu(a))
-\int_a^t\mathcal B_f(\mathbf X(u),\mu(u))\,du
$$</div>
<p>is a square-integrable càdlàg martingale in the completed right-continuous natural filtration of $(\mathbf X,\mu)$. The finite simple-graph martingales obtained using $F_{N,f}$ and $b_{N,f}$ converge to it jointly with that state process in $J_1$. For any finite collection of test functions, one time change works for all coordinates.</p>
<p>The functions
$m_f(\lambda)=\mathbb E F_f(\mathbf X(\lambda),\mu(\lambda))$ and
$m_{N,f}(\lambda)=\mathbb E F_{N,f}(\lambda)$ satisfy</p>
<div class="math-display">$$
m_f'(\lambda)=\mathbb E\mathcal B_f(\mathbf X(\lambda),\mu(\lambda)),
\qquad m_f\in C^1(\mathbb R),
$$</div>
<p>and, for every $\Lambda\ge0$,</p>
<div class="math-display">$$
\sup_{|\lambda|\le\Lambda}
\left(|m_{N,f}(\lambda)-m_f(\lambda)|
+|m_{N,f}'(\lambda)-m_f'(\lambda)|\right)\longrightarrow0.
$$</div>
<p>These limits use sufficiently large $N$, when the whole compact parameter interval lies in $0<p_N<1$.</p>
<p>For polynomial profiles put
$F_r=\int u^r\,\mu(du)=\sum_iX_i^{r+1}Y_i$ and
$P_k=\sum_iX_i^k$ for $k\ge2$. Then, for every integer $r\ge0$,</p>
<div class="math-display">$$
\frac{d}{d\lambda}\mathbb E F_r(\lambda)
=\mathbb E\left[
\sum_{k=1}^{r+1}\binom{r+1}{k}P_{k+1}F_{r+1-k}
-(2^{r+1}-1)F_{r+2}+\frac12P_{r+3}
\right].
$$</div>
<p>Every term is integrable. This derivative is strictly positive. The same compact uniform convergence of the finite means and derivatives holds for each such profile.</p>

<p><em>Proof.</em> LX6L gives the exact finite drift, so the compensated finite processes are martingales. Their states lie in $\mathcal E_*$, where both test function and drift are continuous. Along the common $J_1$ time changes of EAQD, state norms and total measure masses are bounded uniformly for each convergent sequence of paths. The supports therefore lie in one compact interval, even for an unbounded polynomial $f$. Continuity gives convergence of the profile coordinates in $J_1$ and of the drift values at almost every time. The bounds in LX6L give uniform convergence of their time integrals by dominated convergence. Its finite correction vanishes after integration in probability. The compensators are continuous, so the compensated coordinates retain the common time change. This argument applies to any finite list of functions.</p>
<p>On a fixed interval, the supremum of each finite profile and drift is bounded by a polynomial in $S_N(b)$ and $H_N(b)$. The same holds for $\sup|M_{N,f}|$. QKHG and 7CDV bound all required moments of these polynomials uniformly. In particular, products of martingale increments with bounded continuous functions of finitely many past state values are uniformly integrable. The limiting state has no fixed-time jumps, so their expectations pass to the limit and remain zero. The natural-filtration and right-continuous-completion argument in 83JM now proves the stated square-integrable martingale property.</p>
<p>Taking expectations yields the integral of the mean drift between two parameters. The mean drift is continuous: state paths have no fixed-time jumps, $\mathcal B_f$ is continuous on $\mathcal E_*$, and a polynomial in the terminal $S,H$ supplies integrable domination on a containing compact interval. This proves the derivative formula for $m_f$.</p>
<p>For any sequence $\lambda_N\to\lambda$, 1QUE and the continuous size/measure map GZ95 give convergence of the states. The bounds in LX6L, QKHG and 7CDV give uniform integrability of the profile and its drift. Hence their expectations converge, and the finite correction gives
$m_{N,f}'(\lambda_N)\to m_f'(\lambda)$. The analogous mean limit holds too. Continuity of the limiting mean and derivative, followed by compactness, proves both uniform limits.</p>
<p>For $f(u)=u^r$, expand $g(u+v)-g(u)=(u+v)^{r+1}-u^{r+1}$ in the kernel:</p>
<div class="math-display">$$
\Gamma_f(x;u)=
\sum_{k=1}^{r+1}\binom{r+1}{k}u^{r+1-k}P_{k+1}
-(2^{r+1}-1)u^{r+2}.
$$</div>
<p>Integrating against $\mu$ and adding the birth term gives the displayed hierarchy. Only size powers of order at least two occur. The inequalities
$P_k\le S^{k/2}$ and $F_r\le S^{r/2}H$ prove finiteness of all expectations in it. Each merger increases $F_r$, and the birth term has expectation $\mathbb E P_{r+3}/2>0$, because there are positive limiting masses. Thus the derivative is strictly positive. $\square$</p>
<p>For example,
$(\mathbb E F_1)'=\mathbb E[2P_2F_1+P_3F_0-3F_3+P_4/2]$.
These equations retain correlations between component sizes and surplus. They do not form a closed system for the means alone. A bounded test concentrated on a range of sizes need not have an increasing expectation: mergers can carry its surplus mass out of that range.</p>


## Quadratic rates of the surplus profiles {#section-surplus-quadratic-rates}

<p>Retain the test class of LX6L. For a marked state $(x,y)$ write $z_i=x_i y_i$, $S=\sum_i x_i^2$ and $H=\sum_i z_i$. Zero-mass coordinates have zero marks. With $g_f(u)=uf(u)$, denote the merger increment of the profile by</p>
<div class="math-display">$$
D_f(i,j)=y_i[g_f(x_i+x_j)-g_f(x_i)]
       +y_j[g_f(x_i+x_j)-g_f(x_j)].
$$</div>
<p>The corresponding quadratic rate, when absolutely convergent, is</p>
<div class="math-display">$$
\mathcal Q_{f,h}(x,y)=
\sum_{i<j}x_i x_jD_f(i,j)D_h(i,j)
+\frac12\sum_i x_i^4 f(x_i)h(x_i).
$$</div>
<p>The two terms come from mergers and new cycle marks.</p>

<a id="tag-VM8H" data-assertion="proposition" data-title="Surplus profiles have exact finite predictable covariance rates; countable quadratic rates require an additional squared-mark sum"></a>
<p>For $x\in\ell^2_\downarrow$ and $H<\infty$, the additional condition</p>
<div class="math-display">$$
K=\sum_i x_i y_i^2<\infty
$$</div>
<p>makes every $\mathcal Q_{f,h}$ absolutely convergent. More precisely, put $R=\max\{1,\sqrt S\}$, let $A_f,L_f$ be the supremum norm and Lipschitz constant of $f$ on $[0,2R]$, and set $C_f=A_f+RL_f$; use the same notation for $h$. With $P_k=\sum_i x_i^k$,</p>
<div class="math-display">$$
|\mathcal Q_{f,h}|
\le C_fC_h(P_3K+SH^2)+\frac12A_fA_hS^2.
$$</div>
<p>If $x$ is nonzero, finiteness of $\mathcal Q_{1,1}$ is equivalent to finiteness of $K$, and in that case</p>
<div class="math-display">$$
\mathcal Q_{1,1}
=P_3K+\left(\sum_i x_i^2y_i\right)^2
-2\sum_i x_i^4y_i^2+\frac12P_4.
$$</div>
<p>For the common-edge critical Erdős–Rényi graph, with $p_N(\lambda)=(1+\lambda N^{-1/3})/N$, the predictable covariation rate of the finite martingales of E4JW, in the graph filtration, is exactly</p>
<div class="math-display">$$
q_{N,f,h}=\frac{1}{1-p_N}\left[
\mathcal Q_{f,h}(x_N,y_N)
-\frac32N^{-2/3}\sum_i x_{N,i}^3 f(x_{N,i})h(x_{N,i})
+N^{-4/3}\sum_i x_{N,i}^2 f(x_{N,i})h(x_{N,i})
-N^{-4/3}\sum_i x_{N,i}^2y_{N,i}f(x_{N,i})h(x_{N,i})
\right].
$$</div>
<p>Predictable versions use the pre-jump state. Thus the finite covariance $v_{N,f,h}=\operatorname{Cov}(F_{N,f},F_{N,h})$ satisfies, throughout $0<p_N<1$,</p>
<div class="math-display">$$
v_{N,f,h}'=
\operatorname{Cov}(F_{N,f},b_{N,h})
+\operatorname{Cov}(F_{N,h},b_{N,f})
+\mathbb E q_{N,f,h}.
$$</div>

<p><em>Proof.</em> The increase of weighted surplus at a merger is
$d_{ij}=x_jy_i+x_i y_j$. LX6L gives $|D_f(i,j)|\le C_f d_{ij}$. Expanding its square gives</p>
<div class="math-display">$$
\sum_{i<j}x_i x_jd_{ij}^2
=P_3\sum_i x_i y_i^2
+\left(\sum_i x_i^2y_i\right)^2
-2\sum_i x_i^4y_i^2.
$$</div>
<p>One may first do this on finite restrictions and pass to the limit. The two last sums are finite under $H<\infty$:
$\sum_i x_i^2y_i\le\sqrt S\,H$ and
$\sum_i x_i^4y_i^2=\sum_i x_i^2z_i^2\le SH^2$.
When $K<\infty$ this proves the bound, absolute convergence and the formula for $\mathcal Q_{1,1}$, after adding the birth contribution. If $K=\infty$ and $P_3>0$, the finite-restriction identity tends to infinity, since its other terms remain bounded. This proves necessity as well.</p>
<p>For the simple-graph formula, an internal missing edge in a component of size $k_i$ and surplus $y_i$ has increment product $x_i^2f(x_i)h(x_i)$. Multiply it by the count $(k_i^2-3k_i+2)/2-y_i$ and the edge hazard $N^{-4/3}/(1-p_N)$. Cross-component edges give the merger sum divided by $1-p_N$. This proves the stated rate. The finite jump product formula gives</p>
<div class="math-display">$$
\frac{d}{d\lambda}\mathbb E[F_{N,f}F_{N,h}]
=\mathbb E[F_{N,f}b_{N,h}+F_{N,h}b_{N,f}+q_{N,f,h}].
$$</div>
<p>Subtract the derivative of the product of the two means to obtain the covariance identity. All finite-graph expectations are finite sums and are differentiable in the interior of the parameter range. $\square$</p>

<p>The distinction between $K$ and $H$ matters. The state $x_i=4^{-i}$, $y_i=2^i$, $i\ge1$, has $x\in\ell^2$ and $H=1$, but $K=\infty$. Thus the weighted marked-state convergence alone does not justify passing instantaneous quadratic rates to a countable limit. Equal-size aggregation loses information too: marks $(2,0)$ and $(1,1)$ on two mass-one components give the same surplus measure, but their quadratic merger rates against an unmarked mass-two component are $32$ and $16$. These observations concern the general state space; they make no assertion that the critical Erdős–Rényi law has infinite $K$.</p>

## Realized quadratic variation of the surplus profile {#section-surplus-profile-quadratic-variation}

<p>The path limit nevertheless determines realized quadratic variation. This uses the variation of each profile along the actual process, rather than a bound on every possible instantaneous jump.</p>

<a id="tag-XT0C" data-assertion="theorem" data-title="Critical surplus profile martingales have convergent realized quadratic covariations, with finite-variation paths and all mixed moments"></a>
<p>Let $(\mathbf X,\mu)$ be the limiting critical Erdős–Rényi process of EAQD, and use the profiles and martingales of E4JW on a fixed interval $[a,b]$. Each $F_f$ has finite variation there, as does $M_f$. Put $R=1+\sqrt{S(b)}$, and define $A_f,L_f,C_f$ as in VM8H with this $R$. Then, simultaneously for $a\le s<t\le b$,</p>
<div class="math-display">$$
\operatorname{Var}_{(s,t]}F_f
\le C_f\bigl(H(t)-H(s)\bigr).
$$</div>
<p>The martingales have no continuous local-martingale part. Their realized quadratic covariations are the absolutely convergent jump sums</p>
<div class="math-display">$$
[M_f,M_h]_t
=\sum_{a<u\le t}\Delta F_f(u)\Delta F_h(u).
$$</div>
<p>For any finite list of tests, the analogous finite-graph jump sums converge jointly with the state and compensated profile paths in $J_1$, using one time change for all coordinates. At any finite list of deterministic times, all mixed polynomial moments of the profiles, martingales and realized quadratic covariations converge.</p>
<p>Writing $A_{f,h}(t)=[M_f,M_h]_t$, we have</p>
<div class="math-display">$$
\operatorname{Var}_{(a,b]} A_{f,h}
\le C_fC_h\bigl(H(b)-H(a)\bigr)^2.
$$</div>
<p>Moreover $M_fM_h-A_{f,h}$ is a martingale in the completed right-continuous natural filtration of the size/measure pair. Consequently, for deterministic $a\le s<t\le b$,</p>
<div class="math-display">$$
\mathbb E\!\left[(M_f(t)-M_f(s))(M_h(t)-M_h(s))
 \,\middle|\,\mathcal F_s\right]
=\mathbb E[A_{f,h}(t)-A_{f,h}(s)\mid\mathcal F_s],
\qquad
\mathbb E\sup_{a\le t\le b}|M_f(t)|^2
\le4\,\mathbb E A_{f,f}(b).
$$</div>
<p>The finite expectations of realized covariations, and of products of compensated increments, converge to the corresponding limiting expectations.</p>

<p><em>Proof.</em> In a finite graph, LX6L bounds every merger increment by $C_f\Delta H$ in absolute value; a birth satisfies the same bound because its increment is $x_if(x_i)$ and $\Delta H=x_i$. On the whole interval, a single $C_f$, chosen from a bound on the terminal squared mass, works at every jump. Summing gives the variation bound on every subinterval.</p>
<p>In EAQD's Skorokhod coupling the terminal squared masses converge. Thus, for all large $N$, the fixed random value $R=1+\sqrt{S(b)}$ bounds every finite mass on $[a,b]$. E4JW gives uniform convergence of the time-changed profile and surplus paths. Apply the finite variation bound to every partition after this common time change, and pass to the limit. Taking the supremum over partitions proves the displayed bound. Applying the argument on subintervals gives it simultaneously for all $s,t$; equivalently one can first use a countable dense set of endpoints and then right continuity.</p>
<p>The integral compensator in E4JW is continuous and has finite variation. Hence $M_f$ is a finite-variation semimartingale. Its continuous local-martingale part is zero, and its quadratic covariation is the sum of the products of its jumps, which are exactly the jumps of $F_f$. Absolute convergence follows from the variation bounds. More precisely,
$|\Delta F_f|\le C_f\Delta H$, so summing
$|\Delta F_f\Delta F_h|\le C_fC_h(\Delta H)^2$
gives the claimed total-variation bound for $A_{f,h}$.</p>
<p>The jump sums are continuous under the convergence at hand. To see the needed deterministic fact, let $u_{N,f}$ be the finite profile after the common time change, and suppose $\|u_{N,f}-F_f\|_\infty=\delta_{N,f}\to0$. Left limits satisfy the same bound, so at every time</p>
<div class="math-display">$$
|\Delta u_{N,f}-\Delta F_f|\le2\delta_{N,f}.
$$</div>
<p>Sum over the union of their jump times. For every upper endpoint, the difference between the two cumulative cross-jump sums is bounded in absolute value by</p>
<div class="math-display">$$
2\delta_{N,f}\operatorname{Var}_{(a,b]}u_{N,h}
+2\delta_{N,h}\operatorname{Var}_{(a,b]}F_f.
$$</div>
<p>The variations are uniformly bounded, by the first part of the proof. This bound tends to zero uniformly in the upper endpoint and proves the common-clock $J_1$ convergence of all realized covariations.</p>
<p>The finite profiles, martingales and realized covariations have suprema bounded by fixed polynomials in $S_N(b),H_N(b)$, using the preceding variation estimate and LX6L's drift bound. QKHG and 7CDV give uniform bounds for every moment of these polynomials. The limiting state has no jump at any deterministic time, so neither do its profile martingales or their jump sums. Evaluation at finitely many deterministic times is therefore valid in the joint convergence, and uniform integrability proves convergence of all mixed polynomial moments.</p>
<p>For finite graphs the jump product formula makes $M_{N,f}M_{N,h}-A_{N,f,h}$ a martingale. Multiply an increment of this identity by a bounded continuous function of finitely many past size/measure states. Joint path convergence and the polynomial moment bounds pass its expectation to the limit. The monotone-class and right-continuous-completion argument of 83JM gives the asserted limiting martingale. The conditional increment formula follows by using the martingale property of $M_f,M_h$; Doob's $L^2$ inequality gives the maximal estimate. $\square$</p>

<p>The realized sum $[M_f,M_h]$ records jumps that occur. Its predictable compensator is $\langle M_f,M_h\rangle$, which exists because these martingales are square-integrable. Identifying that compensator with the time integral of VM8H's countable rate would require further control of the squared-mark sum and its tails. No such density formula, or convergence of the derivatives of the limiting profile covariances, is asserted here.</p>


## Quadratic rates controlled by a later surplus moment {#section-surplus-rate-future-control}

<p>The condition isolated in VM8H can be checked under the critical law by looking forward in time. The comparison also controls the tails of the rates, which is what their limiting equations require. For a set $I$ of current component indices, put</p>
<div class="math-display">$$
D_I(x,y)=\sum_{i\in I}\sum_{j\ne i}x_i x_j^3y_i^2.
$$</div>
<p>Let $H^I(t+\delta)$ be the size-weighted contribution at time $t+\delta$ of the marks in those components at time $t$. These marks are transported by mergers; marks born after $t$ are excluded.</p>

<a id="tag-4W2Z" data-assertion="proposition" data-title="A future weighted-surplus second moment controls present quadratic rates and their small-component tails under the critical law"></a>
<p>For the countable augmented coalescent, and conditionally on its state at time $t$,</p>
<div class="math-display">$$
D_I(x,y)\le(\delta^{-1}+S)\,
\mathbb E[H^I(t+\delta)^2\mid\mathcal G_t],
\qquad\delta>0.
$$</div>
<p>Here $\mathcal G_t$ may be the full graphical past, $S=\sum_i x_i^2$, and the inequality allows infinite expectations. The same inequality holds for the common-edge critical simple graph, with $\delta$ measured in its critical parameter, whenever the interval is admissible.</p>
<p>At every fixed parameter of the critical limiting law, $K=\sum_iX_iY_i^2<\infty$ almost surely. For every compact interval $J$, every $r\ge1$, and every pair of tests $f,h$ from LX6L,</p>
<div class="math-display">$$
\sup_{\lambda\in J}\mathbb E|\mathcal Q_{f,h}(\lambda)|^r<\infty,
\qquad
\sup_{\substack{N\ge N_J\\\lambda\in J}}
\mathbb E|\mathcal Q_{f,h}(x_N(\lambda),y_N(\lambda))|^r<\infty.
$$</div>
<p>The integer $N_J$ is chosen so that $J+[0,1]$ is admissible. If $\mathcal Q_{f,h}^{[k]}$ keeps only merger pairs and birth terms whose indices are at most $k$, then</p>
<div class="math-display">$$
\begin{aligned}
\lim_{k\to\infty}\limsup_{N\to\infty}\sup_{\lambda\in J}
\mathbb E|\mathcal Q_{f,h}(x_N,y_N)
          -\mathcal Q_{f,h}^{[k]}(x_N,y_N)|^r&=0,\\
\lim_{k\to\infty}\sup_{\lambda\in J}
\mathbb E|\mathcal Q_{f,h}(\lambda)
          -\mathcal Q_{f,h}^{[k]}(\lambda)|^r&=0.
\end{aligned}
$$</div>
<p>No moment bound for $K$ itself is asserted.</p>

<p><em>Proof.</em> Conditional on the current components, a direct edge between components $i,j$ appears in the next $\delta$ coalescent units with probability $1-e^{-\delta x_ix_j}$. Since $x_ix_j\le S$,</p>
<div class="math-display">$$
1-e^{-\delta x_ix_j}\ge\frac{\delta x_ix_j}{1+\delta x_ix_j}
\ge\frac{\delta x_ix_j}{1+\delta S}.
$$</div>
<p>In the simple graph the exact elapsed coalescent time is
$\int_t^{t+\delta}(1-p_N(u))^{-1}\,du\ge\delta$, so this lower bound still holds. If $B$ ranges over future components, expanding nonnegative sums gives</p>
<div class="math-display">$$
\begin{aligned}
H^I(t+\delta)^2
&\ge\sum_B\left(\sum_{j\in B}x_j\right)^2
             \left(\sum_{i\in I\cap B}y_i\right)^2\\
&\ge\sum_{i\in I}\sum_j x_j^2y_i^2
       \mathbf1_{\{i,j\text{ lie in the same future component}\}}.
\end{aligned}
$$</div>
<p>Direct edges imply the connections in the last line. Taking conditional expectations and dropping the diagonal proves the first inequality, by Tonelli also for countably many components.</p>
<p>Write $D=D_{\mathbb N}$. The scalar quadratic merger rate is the sum of its two square terms, equal to $D$, and their cross term, at most $D$. Hence</p>
<div class="math-display">$$
\mathcal Q_{1,1}\le2D+\frac12S^2
\le2(\delta^{-1}+S)\mathbb E[H(t+\delta)^2\mid\mathcal G_t]+\frac12S^2.
$$</div>
<p>For the critical limiting process, JSGY identifies the future law with the critical law at the later parameter. Its second moment is finite by QKHG. Thus $D<\infty$ almost surely. Since
$D=P_3K-\sum_iX_i^4Y_i^2$ and the subtracted sum is finite under $H<\infty$, positivity of $P_3$ gives $K<\infty$.</p>
<p>Set the elapsed time to one. Conditional Jensen, followed by monotonicity of $S$, gives for every $r\ge1$</p>
<div class="math-display">$$
\mathbb E D_I^r
\le\mathbb E\!\left[(1+S(t+1))^r H^I(t+1)^{2r}\right].
$$</div>
<p>For all marks, $H^I(t+1)\le H(t+1)$. QKHG and 7CDV therefore bound every moment of $D$ and $\mathcal Q_{1,1}$ uniformly on compact parameter intervals, in both the finite graphs and the limit. LX6L's increment bound gives
$|\mathcal Q_{f,h}|\le C_fC_h\mathcal Q_{1,1}$, where $C_fC_h$ grows polynomially in $\sqrt S$. Hölder's inequality proves the asserted rate moment bounds.</p>
<p>Now select only marks with initial rank greater than $m$. The initial weighted tails tend to zero in probability, uniformly on compact parameter intervals, by the moving-parameter form of 1QUE. NH8N transports this negligibility through the next unit interval. For finite graphs its exact elapsed coalescent time is at most two for all large $N$. Its stopping estimate is uniform in the initial parameter: first bound the terminal $S$, then make the initial weighted tail small. The limiting construction obeys the same estimate. Since the transported tail is bounded by the full future $H$, the all-moment bounds upgrade convergence in probability to convergence of every moment. The preceding conditional-Jensen bound, with Hölder for the factor involving $S$, yields</p>
<div class="math-display">$$
\lim_{m\to\infty}\limsup_{N\to\infty}\sup_{\lambda\in J}
\mathbb E D_{\{i>m\}}(x_N,y_N)^r=0,
$$</div>
<p>and the same assertion for the limiting laws. Uniformity for the initial limiting laws follows as well: 1QUE makes $\lambda\mapsto\nu_\lambda$ weakly continuous in weighted marked states, by approximation with finite graphs. A failure of compact uniformity would give a convergent sequence of offending parameters and contradict that moving-parameter convergence.</p>
<p>It remains to control pairs whose marked component is among the first $m$ but whose other component lies far out in the mass tail. For $k\ge m$, put
$K_m=\sum_{i\le m}x_i y_i^2$ and $P_3^{>k}=\sum_{j>k}x_j^3$. Then</p>
<div class="math-display">$$
\sum_{\substack{i\ne j\\\max\{i,j\}>k}}x_i x_j^3y_i^2
\le D_{\{i>m\}}+K_mP_3^{>k}.
$$</div>
<p>For fixed $m$, the variables $K_m$ are tight under the critical laws and their finite approximations: their first $m$ masses and marks converge, and the limiting masses are positive. The mass vectors form a tight family in $\ell^2$, so $P_3^{>k}$ vanishes in probability uniformly as $k\to\infty$. Thus the displayed tail tends to zero in probability, first choosing $m$ large and then $k$ large. The square-increment inequality bounds the absolute merger tail of $\mathcal Q_{f,h}$ by twice this tail times $C_fC_h$. The birth tail is at most $A_fA_h\sum_{i>k}x_i^4/2$ and vanishes in the same way. Finally each absolute rate tail is bounded by $C_fC_h\mathcal Q_{1,1}$, whose moments of every order have just been bounded. Uniform integrability upgrades the tail convergence to the stated $L^r$ assertions. $\square$</p>

## Predictable covariations in the critical limit {#section-surplus-predictable-covariations}

<p>The next result supplies the predictable rate left unidentified in XT0C. At a state with positive distinct masses recover $Y_i=\mu(\{X_i\})/X_i$. Evaluate $\mathcal Q_{f,h}$ there when the recovered marked state has finite $K$, and give it value zero on other states. This is a Borel version. By 2N9T, 1QUE and 4W2Z it agrees with the marked-state rate at every fixed parameter almost surely, hence at almost every parameter along a path. Its values on the exceptional states do not affect the integrals below.</p>

<a id="tag-GJB6" data-assertion="theorem" data-title="Critical surplus profile martingales have explicit predictable covariations and compact uniform convergence of covariance derivatives"></a>
<p>For the critical Erdős–Rényi profile martingales of E4JW, in the completed right-continuous natural filtration of the size/measure pair,</p>
<div class="math-display">$$
\langle M_f,M_h\rangle_t
=\int_a^t\mathcal Q_{f,h}(\mathbf X(u),\mathbf Y(u))\,du.
$$</div>
<p>The finite predictable covariations $\int_a^\cdot q_{N,f,h}(u)\,du$ converge uniformly in distribution to this continuous process, jointly with the state, profile martingales and realized covariations of XT0C. The assertion holds for any finite list of tests. Moreover, with $v_{f,h}(\lambda)=\operatorname{Cov}(F_f(\lambda),F_h(\lambda))$,</p>
<div class="math-display">$$
v_{f,h}\in C^1(\mathbb R),\qquad
v_{f,h}'=
\operatorname{Cov}(F_f,\mathcal B_h)
+\operatorname{Cov}(F_h,\mathcal B_f)
+\mathbb E\mathcal Q_{f,h}.
$$</div>
<p>Every term is finite. On each compact interval $J$,</p>
<div class="math-display">$$
\sup_{\lambda\in J}
\left(|v_{N,f,h}(\lambda)-v_{f,h}(\lambda)|
     +|v_{N,f,h}'(\lambda)-v_{f,h}'(\lambda)|\right)
\longrightarrow0.
$$</div>
<p>For total weighted surplus this reads
$(\operatorname{Var}H)'=2\operatorname{Cov}(H,\mathcal B_1)+\mathbb E\mathcal Q_{1,1}$,
with the scalar rate given in VM8H. No sign is asserted for the variance derivative.</p>

<p><em>Proof.</em> First take any $\lambda_N\to\lambda$. By 1QUE the weighted marked states converge. Each finite-rank rate $\mathcal Q_{f,h}^{[k]}$ is continuous at a limiting state whose first $k$ masses are positive. The uniform rate-tail bounds of 4W2Z therefore give convergence of the full rate jointly with the state. Their higher-moment bounds give convergence of its moments and of products with polynomially bounded profile and drift quantities. The same truncation argument proves continuity of these expectations as the limiting parameter varies. Compact uniformity follows by taking a convergent subsequence of any purported counterexample.</p>
<p>We next pass the rate integrals through the path limit. In a Skorokhod coupling for EAQD, attach each finite graph path with its conditional law given its size/measure path. At almost every time the limiting masses are positive and distinct. To recover a fixed mark, isolate $X_i$ in an interval containing no other limiting mass and with endpoints outside the measure's support. Convergence in $\ell^2$ puts exactly the $i$th finite mass there eventually: finite coordinates converge and the tail masses are uniformly small. Weak measure convergence gives $x_{N,i}y_{N,i}\to X_iY_i$, and positivity gives convergence of $y_{N,i}$. This holds for every compatible allocation of finite marks, including states with finite size ties. Thus each truncated rate converges at almost every time in this coupling.</p>
<p>The uniform higher moments in 4W2Z give uniform integrability on the product of the probability space and $[a,b]$. Truncated rates therefore converge in the mean of their time-integrated absolute difference. Their tails are uniformly small in that same mean, so</p>
<div class="math-display">$$
\mathbb E\int_a^b
|\mathcal Q_{f,h}(x_N(u),y_N(u))
 -\mathcal Q_{f,h}(\mathbf X(u),\mathbf Y(u))|\,du
\longrightarrow0.
$$</div>
<p>This implies uniform convergence in probability of their cumulative integrals. VM8H's exact finite correction and the uniform moments in 4W2Z also give</p>
<div class="math-display">$$
\sup_{\lambda\in J}
\|q_{N,f,h}(\lambda)-\mathcal Q_{f,h}(x_N(\lambda),y_N(\lambda))\|_r
=O_{f,h,J,r}(N^{-2/3})
\qquad(r\ge1).
$$</div>
<p>Indeed, $p_N=O(N^{-1})$, while the three correction sums are bounded by $A_fA_hS_N^{3/2}$, $A_fA_hS_N$ and $A_fA_h\sqrt{S_N}H_N$. These are pointwise $L^r$ bounds uniform in the parameter, not bounds on a pathwise supremum of the instantaneous rate. They remove the finite correction after integration and prove the joint convergence of compensators.</p>
<p>For finite graphs,
$M_{N,f}M_{N,h}-\int_a^\cdot q_{N,f,h}(u)\,du$
is a martingale. The rate moment bounds also bound all moments of these integrals, by Jensen's inequality in time. Together with E4JW, this supplies uniform integrability for the martingale identity multiplied by bounded continuous functions of finitely many past state values. Joint convergence passes the identity to the limit. The monotone-class and right-continuous-completion argument of 83JM gives it in the stated limiting filtration. The integral is adapted, continuous and of integrable variation, and is increasing when $f=h$. It is therefore the predictable bracket; polarization gives the cross bracket.</p>
<p>Finally integrate VM8H's finite product-mean identity between two parameters. The rate convergence just proved, LX6L's drift continuity and the moment bounds pass every expectation to the limit. The resulting integrand
$\mathbb E[F_f\mathcal B_h+F_h\mathcal B_f+\mathcal Q_{f,h}]$
is continuous by the moving-parameter argument at the start of the proof. Hence the limiting product mean is $C^1$. Subtract the derivative of the product of means, using E4JW, to obtain the covariance equation. Along every $\lambda_N\to\lambda$, the same argument gives convergence of the finite derivative formula, and of the finite covariance itself. Compactness now yields the two uniform limits. $\square$</p>


## Higher jump moments of weighted surplus {#section-surplus-higher-jump-moments}

<p>The future-moment comparison also controls large jumps of every polynomial order. Write $\eta_{ij}=x_jy_i+x_iy_j$ for the increase of $H$ at a merger, and, for $r\ge1$, put</p>
<div class="math-display">$$
\mathcal J_r=\sum_{i<j}x_ix_j\eta_{ij}^{\,r}
              +\frac12\sum_i x_i^{r+2},
\qquad
D_{r,I}=\sum_{i\in I}\sum_{j\ne i}x_i x_j^{r+1}y_i^r.
$$</div>
<p>The second term in $\mathcal J_r$ accounts for new cycle marks. Let $\mathcal J_r^{[k]}$ retain only merger pairs and birth terms with all indices at most $k$.</p>

<a id="tag-BH5K" data-assertion="proposition" data-title="All weighted-surplus jump moments have compact uniform moment bounds and vanishing rank tails under the critical law"></a>
<p>In the graphical settings of 4W2Z, with the same inherited contribution $H^I(t+\delta)$,</p>
<div class="math-display">$$
D_{r,I}\le(\delta^{-1}+S)\,
       \mathbb E[H^I(t+\delta)^r\mid\mathcal G_t],
\qquad
\mathcal J_r\le2^{r-1}D_{r,\mathbb N}+\frac12P_{r+2}.
$$</div>
<p>Here $P_s=\sum_i x_i^s$. Both inequalities allow infinite values. Under the critical Erdős–Rényi law, for every $r,q\ge1$ and compact parameter interval $J$, $\mathcal J_r$ has uniformly bounded $q$th moments, both in the limit and in all sufficiently large finite graphs. Moreover,</p>
<div class="math-display">$$
\begin{aligned}
\lim_{k\to\infty}\limsup_{N\to\infty}\sup_{\lambda\in J}
 \mathbb E\!\left(\mathcal J_r(x_N,y_N)-\mathcal J_r^{[k]}(x_N,y_N)\right)^q&=0,\\
\lim_{k\to\infty}\sup_{\lambda\in J}
 \mathbb E\!\left(\mathcal J_r(\lambda)-\mathcal J_r^{[k]}(\lambda)\right)^q&=0.
\end{aligned}
$$</div>

<p><em>Proof.</em> For nonnegative numbers and $r\ge1$, $(\sum a_i)^r\ge\sum a_i^r$. Apply this first to the future components and then to their masses and inherited marks. It gives</p>
<div class="math-display">$$
H^I(t+\delta)^r\ge
 \sum_{i\in I}\sum_j x_j^r y_i^r
 \mathbf1_{\{i,j\text{ lie in the same future component}\}}.
$$</div>
<p>The direct-edge bound in 4W2Z and conditional Tonelli prove the first inequality. The second follows from $(a+b)^r\le2^{r-1}(a^r+b^r)$; summing the two directed terms over unordered merger pairs gives $D_{r,\mathbb N}$.</p>
<p>With $\delta=1$, conditional Jensen and monotonicity of $S$ yield</p>
<div class="math-display">$$
\mathbb E D_{r,I}^{\,q}
 \le\mathbb E\!\left[(1+S(t+1))^q H^I(t+1)^{rq}\right].
$$</div>
<p>QKHG and 7CDV bound this expectation for all marks, uniformly on compact intervals. Also $P_{r+2}\le S^{(r+2)/2}$. This proves the moment bounds. For marks with initial rank greater than $m$, NH8N and 1QUE make the inherited contribution one unit later negligible in probability, uniformly in the parameter. Its domination by the full later $H$ upgrades this to convergence of every moment. Hölder in the last display therefore gives $D_{r,\{i>m\}}\to0$ in every $L^q$, with the same compact uniformity. The limiting family and the finite exact clock are handled exactly as in 4W2Z.</p>
<p>For $k\ge m$, the remaining directed tail satisfies</p>
<div class="math-display">$$
\sum_{\substack{i\ne j\\\max\{i,j\}>k}}x_i x_j^{r+1}y_i^r
 \le D_{r,\{i>m\}}+
       \left(\sum_{i\le m}x_i y_i^r\right)
       \left(\sum_{j>k}x_j^{r+1}\right).
$$</div>
<p>The first factor in parentheses is tight for fixed $m$ by positive-mass finite-coordinate convergence. The second tends to zero uniformly in probability by tightness in $\ell^2$, since $r+1\ge2$. Choose $m$ first and then $k$. The same power inequality controls the merger tail of $\mathcal J_r$; the birth tail vanishes by the mass tail. Higher moments of the full $\mathcal J_r$ give uniform integrability and hence the asserted $L^q$ limits. $\square$</p>

## Evolution of nonlinear surplus observables {#section-surplus-nonlinear-generator}

<p>Fix tests $f_1,\ldots,f_d$ from LX6L and let $Z=(F_{f_1},\ldots,F_{f_d})$. For a marked state write $z=Z(x,y)$, and denote its merger and birth increments by</p>
<div class="math-display">$$
\begin{aligned}
a_{ij}^{(\ell)}
 &=y_i[g_{f_\ell}(x_i+x_j)-g_{f_\ell}(x_i)]
   +y_j[g_{f_\ell}(x_i+x_j)-g_{f_\ell}(x_j)],\\
b_i^{(\ell)}&=x_i f_\ell(x_i).
\end{aligned}
$$</div>
<p>For $\Phi\in C^1(\mathbb R^d)$ whose gradient has polynomial growth, define</p>
<div class="math-display">$$
\mathcal A\Phi(x,y)=
 \sum_{i<j}x_ix_j[\Phi(z+a_{ij})-\Phi(z)]
 +\frac12\sum_i x_i^2[\Phi(z+b_i)-\Phi(z)].
$$</div>
<p>On size/measure states use the Borel recovery of positive distinct masses from GJB6, evaluating this series when it converges absolutely and assigning zero otherwise. The exceptional values have no effect on the critical time integrals.</p>

<a id="tag-KP1O" data-assertion="theorem" data-title="Polynomially growing smooth functions of critical surplus profiles satisfy a convergent jump martingale problem and C1 expectation equations"></a>
<p>The series defining $\mathcal A\Phi$ converges absolutely almost surely at each fixed critical parameter, has moments of every positive order uniformly on compact parameter intervals, and has the same properties uniformly for sufficiently large finite graphs. On every $[a,b]$,</p>
<div class="math-display">$$
M^\Phi_t=\Phi(Z(t))-\Phi(Z(a))
               -\int_a^t\mathcal A\Phi(\mathbf X(u),\mathbf Y(u))\,du
$$</div>
<p>is a square-integrable càdlàg martingale in the completed right-continuous natural filtration of the size/measure pair. The finite graph-filtration martingales, with their exact finite generators, converge jointly with that pair to $M^\Phi$ in the common $J_1$ time change; their compensators converge uniformly in distribution. This holds for any finite list of such functions. Furthermore,</p>
<div class="math-display">$$
u_\Phi(\lambda)=\mathbb E\Phi(Z(\lambda))\in C^1(\mathbb R),
\qquad
u_\Phi'(\lambda)=\mathbb E\mathcal A\Phi(\mathbf X(\lambda),\mathbf Y(\lambda)),
$$</div>
<p>and the finite expectations and their first derivatives converge uniformly on every compact parameter interval.</p>
<p>For example, define the absolutely convergent mixed jump moments</p>
<div class="math-display">$$
\mathcal C_\alpha=
 \sum_{i<j}x_ix_j a_{ij}^{\alpha}
 +\frac12\sum_i x_i^2 b_i^{\alpha},
\qquad \alpha\in\mathbb N^d,\quad|\alpha|\ge1.
$$</div>
<p>For a polynomial $\Phi$, its finite Taylor expansion gives the exact hierarchy</p>
<div class="math-display">$$
\frac{d}{d\lambda}\mathbb E\Phi(Z)
 =\sum_{1\le|\alpha|\le\deg\Phi}
   \frac1{\alpha!}\mathbb E[\partial^\alpha\Phi(Z)\mathcal C_\alpha].
$$</div>
<p>Here vector powers are coordinatewise. In one dimension $\mathcal C_1=\mathcal B_f$ and $\mathcal C_2=\mathcal Q_{f,f}$, recovering the earlier mean and second-moment equations.</p>
<p>The joint characteristic function has the evolution equation</p>
<div class="math-display">$$
\begin{aligned}
\partial_\lambda\mathbb E e^{\,i\theta\cdot Z}
 &=\mathbb E[e^{\,i\theta\cdot Z}\Psi(\theta;x,y)],\\
\Psi(\theta;x,y)
 &=\sum_{i<j}x_ix_j(e^{\,i\theta\cdot a_{ij}}-1)
    +\frac12\sum_i x_i^2(e^{\,i\theta\cdot b_i}-1).
\end{aligned}
$$</div>
<p>The series is absolutely convergent. Finite characteristic functions and their first parameter derivatives converge uniformly when both the parameter and $\theta$ range over compact sets. The expectation on the right retains the dependence of the jump rates on the full marked state; this equation alone does not assert that $Z$ is Markov.</p>

<p><em>Proof.</em> Choose an integer $m\ge0$ with $\|\nabla\Phi(w)\|\le c(1+\|w\|^m)$. The mean-value formula gives</p>
<div class="math-display">$$
|\Phi(z+v)-\Phi(z)|
 \le c'\big[(1+\|z\|^m)\|v\|+\|v\|^{m+1}\big].
$$</div>
<p>LX6L supplies a constant $C(S)$, bounded by a polynomial in $1+\sqrt S$, such that $\|a_{ij}\|\le C(S)\eta_{ij}$, $\|b_i\|\le C(S)x_i$, and $\|z\|\le C(S)H$. Consequently the sum of the absolute generator terms is at most</p>
<div class="math-display">$$
c'\big[(1+\|z\|^m)C(S)\mathcal J_1
                   +C(S)^{m+1}\mathcal J_{m+1}\big].
$$</div>
<p>BH5K and the size and surplus moment bounds prove integrability of every order. The same inequality restricted to indices beyond $k$, followed by Hölder and BH5K's tail bounds, makes the absolute generator tails vanish in every $L^q$, uniformly on compact parameter intervals.</p>
<p>The finite correction must be made before taking the limit. Set
$\Delta_i\Phi=\Phi(z+b_i)-\Phi(z)$. There are $k_i k_j$ closed edges between different components and $(k_i^2-3k_i+2)/2-y_i$ closed internal edges. In critical time each closed edge has rate $N^{-4/3}/(1-p_N)$. Thus the exact finite generator is</p>
<div class="math-display">$$
\mathcal A_N\Phi
 =\frac{1}{1-p_N}\left[
    \mathcal A\Phi-\frac32N^{-2/3}\sum_i x_i\Delta_i\Phi
      +N^{-4/3}\sum_i(1-y_i)\Delta_i\Phi\right].
$$</div>
<p>The mean-value bound and $x_i\le\sqrt S$ give
$|\Delta_i\Phi|\le G(S,H)x_i$ for a polynomially bounded $G$. Therefore the absolute values of the three sums with factors $x_i$, $1$, and $y_i$ are bounded by $GS$, $GN^{1/3}$, and $GH$, respectively; here $\sum_i x_i=N^{1/3}$ in the finite graph. Since $p_N=O(N^{-1})$, for every $q\ge1$</p>
<div class="math-display">$$
\sup_{\lambda\in J}
 \|\mathcal A_N\Phi-\mathcal A\Phi(x_N,y_N)\|_q
 =O_{\Phi,f_1,\ldots,f_d,J,q}(N^{-2/3}).
$$</div>
<p>This compares the exact and augmented generators at the same finite state; it is not a rate of convergence to the limiting generator.</p>
<p>Along any $\lambda_N\to\lambda$, 1QUE gives convergence of $z$ and of each finite set of positive-mass coordinates and marks. The truncated generators therefore converge. Their uniform tails and higher moments give convergence of the full generators and their expectations. Applying the same argument to the limiting parameter family proves continuity of the limiting expectation; compactness makes the convergence uniform.</p>
<p>For paths use the EAQD coupling and attach the finite graphs by their conditional laws given the size/measure paths, as in GJB6. At almost every time, isolation of finitely many positive distinct masses recovers their individual marks. Thus the finite-rank generators converge there. Their moment bounds give uniform integrability on probability space times $[a,b]$, and the generator tails are uniformly small in that product space. Hence the time integral of the absolute difference between the augmented finite and limiting generators tends to zero in mean. The exact finite correction also tends to zero after integration, proving uniform convergence in probability of the compensators.</p>
<p>Continuous composition of the common $J_1$ limit gives convergence of $\Phi(Z_N)$ and hence of the martingales. Their suprema have moments of every order: $\sup_t\|Z_N(t)\|$ is bounded by a polynomial in $S_N(b)$ times $H_N(b)$, while Jensen in time bounds the compensator moments. Finite martingale identities therefore pass against bounded continuous functions of finitely many past size/measure states. The monotone-class and right-continuous-completion argument of 83JM proves the claimed limiting martingale property.</p>
<p>Integrating the finite identity $u_{N,\Phi}'=\mathbb E\mathcal A_N\Phi$ and passing expectations to the limit now gives $u_\Phi'=\mathbb E\mathcal A\Phi$, with a continuous right-hand side. The moving-parameter convergence proves uniform convergence of both $u_{N,\Phi}$ and its derivative on compact intervals. The polynomial identity is the exact finite Taylor formula inside an absolutely convergent sum. For characteristic functions apply the result to the real and imaginary parts of $e^{i\theta\cdot z}$. The estimate $|e^{i\theta\cdot v}-1|\le\|\theta\|\|v\|$ gives absolute convergence and bounds uniform on compact $\theta$ sets. The same moving-parameter proof, now also allowing $\theta_N\to\theta$, gives the last uniform convergence claim. $\square$</p>


## A sharper tail for squared component mass {#section-critical-squared-mass-sharp-tail}

<p>Large squared mass forces a large component to appear after a short further evolution. Applying the generator to its reciprocal makes this precise. Write $S=\sum_i x_i^2$ and $R=\max_i x_i$.</p>

<a id="tag-X92C" data-assertion="proposition" data-title="A reciprocal-mass stopping estimate gives a uniform stretched-exponential tail of power three halves for critical squared mass"></a>
<p>For a finite multiplicative coalescent starting with $S\ge s>0$, let
$\tau=\inf\{t\ge0:R(t)\ge\sqrt s/2\}$. Then
$\mathbb E\tau\le2/s$, and therefore
$\mathbb P(\tau\le4/s)\ge1/2$. The same probability bound holds in the common-edge critical simple graph, with time measured in its critical parameter, whenever the following interval of length $4/s$ is admissible with $p_N<1$.</p>
<p>Consequently, for every $\Lambda<\infty$ there are $c,C,s_0>0$ such that</p>
<div class="math-display">$$
\begin{aligned}
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
 \mathbb P(S_N(\lambda)\ge s)&\le Ce^{-cs^{3/2}},\\
\sup_{|\lambda|\le\Lambda}\mathbb P(S(\lambda)\ge s)&\le Ce^{-cs^{3/2}}
\qquad(s\ge s_0).
\end{aligned}
$$</div>
<p>In particular, for some $\varepsilon_\Lambda>0$, the expectations of
$\exp(\varepsilon_\Lambda S_N^{3/2})$ and
$\exp(\varepsilon_\Lambda S^{3/2})$ are uniformly bounded over these parameters. Also $\|S_N\|_q,\|S\|_q\le C_\Lambda q^{2/3}$ for $q\ge1$.</p>

<p><em>Proof.</em> A merger changes $S$ by $2x_ix_j$. Before $\tau$ every mass is less than $r=\sqrt s/2$, so, with $P_4=\sum_i x_i^4$,</p>
<div class="math-display">$$
\begin{aligned}
\mathcal L(S^{-1})
 &=-\sum_{i<j}\frac{2x_i^2x_j^2}{S(S+2x_ix_j)}\\
 &\le-\frac{S^2-P_4}{S(S+2r^2)}
 \le-\frac{S-r^2}{S+2r^2}\le-\frac12.
\end{aligned}
$$</div>
<p>Here $P_4\le r^2S$ and $S\ge s=4r^2$. If the initial state already meets the threshold, $\tau=0$. Otherwise the stopped generator identity and nonnegativity give, for every $T>0$,</p>
<div class="math-display">$$
0\le\mathbb E[S(\tau\wedge T)^{-1}]
 \le S(0)^{-1}-\frac12\mathbb E(\tau\wedge T).
$$</div>
<p>Letting $T\to\infty$ proves the expected hitting-time bound. In the finite simple graph, mergers have rates $x_ix_j/(1-p_N)$ and internal edges leave $S$ unchanged. Its stopped drift is thus at most $-1/2$ too. Taking $T=4/s$ gives
$T\mathbb P(\tau>T)\le\mathbb E(\tau\wedge T)\le2/s$, which only uses that admissible interval.</p>
<p>Condition at parameter $\lambda$ on the event $S_N(\lambda)\ge s$. Monotonicity of the largest component and the conditional hitting bound imply</p>
<div class="math-display">$$
\mathbb P(S_N(\lambda)\ge s)
 \le2\mathbb P\!\left(R_N(\lambda+4/s)\ge\frac{\sqrt s}{2}\right).
$$</div>
<p>For $s\ge1$ and all sufficiently large $N$, the later parameter lies in the admissible compact interval $[-\Lambda,\Lambda+4]$. The cubic largest-component bound in 7CDV proves the first tail estimate, with a harmless change of threshold to handle weak inequalities. For the finitely many smaller $N$, use $S_N\le N^{2/3}$ and enlarge $s_0$. Fixed-parameter weak convergence transfers the bound to the limit by Portmanteau, again slightly reducing the threshold. Tail integration proves the exponential-power bound for any sufficiently small positive $\varepsilon_\Lambda$. It also bounds the $q$th moment by a constant times
$c^{-2q/3}\Gamma(1+2q/3)$, proving the displayed moment growth. $\square$</p>

## Matching upper tails for weighted surplus {#section-weighted-surplus-sharp-upper-tail}

<p>At a fixed critical parameter, retain the Brownian representation of 1QUE and write</p>
<div class="math-display">$$
Q_\lambda=\sup_{t\ge0}R_\lambda(t),\qquad
V_\lambda=\sum_i\ell_i A_i,\qquad
H(\lambda)=\sum_i\ell_iY_i.
$$</div>
<p>Here $\ell_i$ and $A_i$ are excursion lengths and areas, and conditionally on the whole Brownian path the $Y_i$ are independent Poisson variables with means $A_i$. Since $A_i\le Q_\lambda\ell_i$, one has $V_\lambda\le Q_\lambda S(\lambda)$.</p>

<a id="tag-J2VQ" data-assertion="theorem" data-title="Critical weighted surplus has matching tail power three quarters, sharp polynomial moment growth, and a positive finite exponential-power threshold"></a>
<p>For every $\Lambda<\infty$ there are $c_1,c_2,C_1,C_2,x_0>0$ such that</p>
<div class="math-display">$$
c_1e^{-C_1x^{3/4}}
 \le\mathbb P(H(\lambda)\ge x)
 \le C_2e^{-c_2x^{3/4}}
 \qquad(|\lambda|\le\Lambda,\ x\ge x_0).
$$</div>
<p>Thus $\|H(\lambda)\|_q$ is bounded above and below by positive constant multiples of $q^{4/3}$, uniformly on the interval for all sufficiently large $q$. Every exponential moment of $H^\alpha$ is finite when $0<\alpha<3/4$. At the endpoint,</p>
<div class="math-display">$$
0<c_\Lambda\le
 \theta_*(\lambda):=\sup\{\theta\ge0:
             \mathbb E e^{\theta H(\lambda)^{3/4}}<\infty\}
 \le C_\Lambda<\infty.
$$</div>
<p>The exact threshold and integrability at $\theta=\theta_*(\lambda)$ are not determined here. For $\alpha>3/4$ all positive exponential moments diverge, as in 7E7T.</p>
<p>For any fixed $a<b$, the integral $J=\int_a^bH(\lambda)\,d\lambda$ has the same tail power, moment growth and positive finite endpoint threshold, with constants depending on $a,b$. Moreover, the joint laws of $(S(\lambda),H(\lambda))$ and of
$(I,J)$, where $I=\int_a^bS(\lambda)\,d\lambda$, are determined among probability laws on $[0,\infty)^2$ by their mixed moments.</p>
<p>The surplus upper bounds in this theorem concern the limiting law. Uniform finite-$N$ exponential-power bounds for $H_N$ are not asserted.</p>

<p><em>Proof.</em> We first show that the global Brownian queue has the uniform bound</p>
<div class="math-display">$$
\mathbb P(Q_\lambda>h)\le C e^{-ch^{3/2}}
\qquad(|\lambda|\le\Lambda,\ h\ge h_0).
$$</div>
<p>Take $h_0$ large enough that $T=\lceil\sqrt h\rceil\ge4\Lambda+1$, $T\le2\sqrt h$, and $h\ge\Lambda^2$. For $0\le t\le T$, the parabolic drift increment over any interval of length $u$ is at most $\Lambda u-u^2/2\le\Lambda^2/2$. Hence</p>
<div class="math-display">$$
\sup_{t\le T}R_\lambda(t)
 \le2\sup_{t\le T}|B(t)|+\frac{\Lambda^2}{2}.
$$</div>
<p>The reflection bound makes the probability that this exceeds $h$ at most
$4\exp[-h^2/(32T)]\le4e^{-h^{3/2}/64}$.</p>
<p>For a deterministic $t\ge n\ge T$, reverse the Brownian increments on $[0,t]$. In distribution,</p>
<div class="math-display">$$
R_\lambda(t)=
 \sup_{0\le u\le t}
 \left[\widetilde B(u)+(\lambda-t)u+\frac{u^2}{2}\right]
 \le\sup_{u\ge0}\left[\widetilde B(u)-\frac n4u\right].
$$</div>
<p>The last supremum has tail $e^{-2(n/4)v}$ at level $v\ge0$. This follows by stopping the exponential martingale
$\exp(2aB(u)-2a^2u)$ at the first time $B(u)-au=v$. The stopped martingale is bounded by $e^{2av}$ and tends to zero on paths that do not hit, so dominated convergence gives the formula, with $a=n/4$. In particular,
$\mathbb P(R_\lambda(t)>h/2)\le e^{-nh/4}$.</p>
<p>Divide $[n,n+1]$ into $n^2$ intervals of length $n^{-2}$. If $t_j$ is a left endpoint, the deterministic drift is decreasing on this interval, so</p>
<div class="math-display">$$
\sup_{t_j\le t\le t_j+n^{-2}}R_\lambda(t)
 \le R_\lambda(t_j)
      +2\sup_{0\le u\le n^{-2}}|B(t_j+u)-B(t_j)|.
$$</div>
<p>A union bound and reflection therefore bound the probability of exceeding $h$ somewhere after $T$ by</p>
<div class="math-display">$$
\sum_{n\ge T}n^2
 \left(e^{-nh/4}+4e^{-n^2h^2/32}\right)
 \le C e^{-cTh}\le C e^{-ch^{3/2}}.
$$</div>
<p>For example, when $h,n\ge1$, replace the second exponential by $e^{-nh/32}$, split off $e^{-Th/64}$, and sum the remaining convergent series uniformly in $h$. Together with the initial interval this proves the queue bound, including $Q_\lambda<\infty$ almost surely.</p>
<p>Since $V_\lambda\le Q_\lambda S(\lambda)$, X92C and the queue bound give</p>
<div class="math-display">$$
\mathbb P(V_\lambda>x)
 \le\mathbb P(Q_\lambda>\sqrt x)
      +\mathbb P(S(\lambda)>\sqrt x)
 \le C e^{-cx^{3/4}}
$$</div>
<p>for large $x$, uniformly in $\lambda$. No independence is used. Now condition on the Brownian path. On the event
$R:=\max_i\ell_i\le x^{1/4}$, the inequality
$e^u-1\le(e-1)u$ for $0\le u\le1$ gives</p>
<div class="math-display">$$
\mathbb E[e^{x^{-1/4}H}\mid B]
 =\exp\!\left(\sum_i A_i(e^{x^{-1/4}\ell_i}-1)\right)
 \le\exp((e-1)x^{-1/4}V_\lambda).
$$</div>
<p>The identity follows first for finitely many marks and then by monotone convergence; the upper bound is finite. If also
$V_\lambda\le x/[2(e-1)]$, conditional exponential Markov gives probability at most $e^{-x^{3/4}/2}$ for $H\ge x$. Since $R^2\le S$,</p>
<div class="math-display">$$
\mathbb P(H\ge x)
 \le\mathbb P(S>x^{1/2})
      +\mathbb P\!\left(V_\lambda>\frac{x}{2(e-1)}\right)
      +e^{-x^{3/4}/2}
 \le C e^{-cx^{3/4}}.
$$</div>
<p>The lower bound is 7E7T. Integrating the upper tail gives
$\|H\|_q\le Cq^{4/3}$, and 7E7T gives the matching lower bound. Tail integration also gives uniform finiteness of
$\mathbb E e^{\theta H^{3/4}}$ for sufficiently small positive $\theta$. For sufficiently large $\theta$, the lower tail bound forces divergence. If $\alpha<3/4$, absorb $\theta H^\alpha$ into an arbitrarily small positive multiple of $H^{3/4}$ plus a constant. This proves all the asserted exponential-power conclusions.</p>
<p>In the common process, monotonicity gives
$(b-a)H(a)\le J\le(b-a)H(b)$. It transfers the two tail bounds, moment growth and threshold conclusions to $J$. Only fixed-parameter Brownian representations were used to bound the endpoint laws.</p>
<p>Finally, X92C and the surplus upper bound imply
$\mathbb E e^{\varepsilon(\sqrt S+\sqrt H)}<\infty$ for some $\varepsilon>0$, by Hölder. Since $I\le(b-a)S(b)$ and $J\le(b-a)H(b)$, the same holds for $\sqrt I+\sqrt J$. The signed-square-root argument in NM14 then proves joint moment determinacy: the mixed moments determine an integrable product of hyperbolic cosines, hence an exponential moment for any competing pair; independent signs give identical analytic moment generating functions near the origin, and squaring recovers the original laws. This is compatible with the zero Taylor radius of the ordinary surplus transform in B7V7. $\square$</p>


## A global finite exploration-queue bound {#section-critical-finite-queue-tail}

<p>To obtain a uniform finite-graph surplus estimate, the queue must be controlled over the entire exploration. Let $A_k$ be the breadth-first queue of FOTE and put
$Q_N=N^{-1/3}\max_{0\le k\le N}A_k$.</p>

<a id="tag-N81A" data-assertion="proposition" data-title="The full critical complete-graph exploration queue has a uniform stretched-exponential tail of power three halves"></a>
<p>For every $0\le\Lambda<\infty$ there are $c,C,h_0>0$ such that</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
 \mathbb P(Q_N>h)\le Ce^{-ch^{3/2}}
 \qquad(h\ge h_0).
$$</div>
<p>Consequently, for some $\varepsilon_\Lambda>0$, the expectations of
$\exp(\varepsilon_\Lambda Q_N^{3/2})$ are uniformly bounded, and
$\|Q_N\|_q\le C_\Lambda q^{2/3}$ for $q\ge1$.</p>

<p><em>Proof.</em> Write $c_N=N^{1/3}$, and abbreviate it to $c_*$ within this proof. The number of undiscovered vertices tested at step $i$ is at most $N-i$: when the queue is empty the new root is removed first, and otherwise the active queue already contains at least one vertex. Use a fresh row of $N-i$ independent Bernoulli($p_N$) variables at step $i$, taking its first $n_i$ entries for the actual discoveries and filling the rest with independent dummy trials. Then</p>
<div class="math-display">$$
\eta_i\le\xi_i,\qquad
\xi_i\sim\operatorname{Bin}(N-i,p_N),
$$</div>
<p>and the $\xi_i$ are independent. Adaptive assignment of the tested edges preserves the original graph law. The actual queue obeys
$A_i=(A_{i-1}-1)_++\eta_i$. Thus, starting from zero, it is dominated by
$Z_i=(Z_{i-1}-1)_++\xi_i$. If</p>
<div class="math-display">$$
U_k=\sum_{i=1}^k(\xi_i-1),\qquad
\mathcal R_k=U_k-\min_{0\le j\le k}U_j,
$$</div>
<p>the recursion gives $Z_k\le1+\mathcal R_k$. Independence belongs to the dominating rows, not to the original exploration increments.</p>
<p>For $h_0\le h\le c_*^2$, with $h_0$ sufficiently large depending on $\Lambda$, we prove
$\mathbb P(\max_k\mathcal R_k>hc_*)\le Ce^{-ch^{3/2}}$.
The actual queue satisfies $Q_N\le c_*^2$ deterministically, so this and the preceding additive one imply the desired tail after changing the threshold by a fixed factor. The case $h>c_*^2$ for $Q_N$ is empty.</p>
<p>In the indicated range $c_*\ge\sqrt h$, so $h_0$ can ensure
$1/(2N)\le p_N\le2/N$. Write</p>
<div class="math-display">$$
\mu_i=(N-i)p_N,\qquad
M_k=\sum_{i=1}^k(\xi_i-\mu_i),\qquad
D_k=\mathbb E U_k=\frac{\lambda k}{c_*}
                       -\frac{p_N k(k+1)}2.
$$</div>
<p>Since $\mu_i\le2$, both the forward centered increments and every fixed finite reversal satisfy the exponential bound
$\mathbb E e^{\theta(\xi_i-\mu_i)}\le e^{2\theta^2}$ for $|\theta|\le1$, as in N9DF.</p>
<p>For $j<k$ and $m=k-j$,</p>
<div class="math-display">$$
D_k-D_j\le\frac{\Lambda m}{c_*}
                         -\frac{m^2}{4c_*^3}
                    \le\Lambda^2c_*.
$$</div>
<p>Set $T=\lceil\sqrt h\rceil$ and $K=\min\{N,\lceil Tc_*^2\rceil\}$, choosing $h_0$ so that $T\ge8\Lambda+1$ and $h\ge2\Lambda^2$. Then
$\max_{k\le K}\mathcal R_k\le2\max_{k\le K}|M_k|+\Lambda^2c_*$.
N9DF bounds the probability that this exceeds $hc_*$ by $Ce^{-ch^{3/2}}$: indeed $K\le3\sqrt h\,c_*^2$, and both
$(hc_*)^2/K$ and $hc_*$ are bounded below by constant multiples of $h^{3/2}$.</p>
<p>For the late part fix an integer $n$ with $T\le n<c_*$ and a deterministic $k\ge\lfloor nc_*^2\rfloor$. For $0\le m\le k$,</p>
<div class="math-display">$$
D_k-D_{k-m}
 \le m\left(\frac{\Lambda}{c_*}
                      -\frac{p_N(k+1)}2\right)
 \le-\frac{n}{8c_*}m.
$$</div>
<p>The process $\widetilde M_m=M_k-M_{k-m}$ has independent centered binomial increments. With $\theta=n/(16c_*)\le1$, the process
$\exp\{\theta\widetilde M_m-2\theta^2m\}$ is a nonnegative supermartingale. Since $2\theta^2=\theta n/(8c_*)$, stopping at a crossing gives</p>
<div class="math-display">$$
\mathbb P(\mathcal R_k>hc_*/2)\le e^{-nh/32}.
$$</div>
<p>No reversal of the dependent discovery martingale has been used.</p>
<p>Cover the integer times from $\lfloor nc_*^2\rfloor$ to
$\min\{N,\lfloor(n+1)c_*^2\rfloor\}$ by cells of at most
$L_n=\lceil c_*^2/n^2\rceil$ steps. There are at most $3n^2$ cells, and $L_n\le2c_*^2/n^2$. The mean walk $D$ is decreasing throughout this block. If $k_j$ is a cell's left endpoint,</p>
<div class="math-display">$$
\max_{k_j\le k\le k_j+L_n}\mathcal R_k
 \le\mathcal R_{k_j}
       +2\max_{0\le m\le L_n}|M_{k_j+m}-M_{k_j}|,
$$</div>
<p>where the last cell is truncated at $N$ or the block endpoint. N9DF bounds the probability that the second term exceeds $hc_*/2$ by
$2\exp[-c_0\min\{n^2h^2,hc_*\}]\le2e^{-c_1nh}$, since $h\ge1$ and $n<c_*$. Together with the bound at the left endpoint, a union bound gives a late failure probability at most</p>
<div class="math-display">$$
C\sum_{n\ge T}n^2e^{-c_1nh}
 \le C'e^{-c_2Th}\le C'e^{-c_2h^{3/2}}.
$$</div>
<p>The initial interval and these blocks cover every step through $N$. Tail integration gives the two moment conclusions. $\square$</p>

## Uniform surplus tails and fractional-exponential limits {#section-finite-weighted-surplus-sharp-tail}

<a id="tag-65IO" data-assertion="theorem" data-title="Critical finite-graph weighted surplus has a uniform tail of power three quarters and convergent fractional-exponential expectations"></a>
<p>For every $0\le\Lambda<\infty$ there are $c,C,x_0>0$ such that</p>
<div class="math-display">$$
\sup_{\substack{N\ge2,\ |\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
 \mathbb P(H_N(\lambda)\ge x)\le Ce^{-cx^{3/4}}
 \qquad(x\ge x_0).
$$</div>
<p>In particular, $\|H_N(\lambda)\|_q\le C_\Lambda q^{4/3}$ for every $q\ge1$, uniformly over these graphs. For some $\varepsilon_\Lambda>0$,</p>
<div class="math-display">$$
\sup_{N,\lambda}\mathbb E e^{\varepsilon_\Lambda H_N(\lambda)^{3/4}}<\infty,
\qquad
\sup_{|\lambda|\le\Lambda}\mathbb E e^{\varepsilon_\Lambda H(\lambda)^{3/4}}<\infty.
$$</div>
<p>For every $0\le\theta<\varepsilon_\Lambda$,</p>
<div class="math-display">$$
\sup_{|\lambda|\le\Lambda}
 \left|\mathbb E e^{\theta H_N(\lambda)^{3/4}}
       -\mathbb E e^{\theta H(\lambda)^{3/4}}\right|
 \longrightarrow0.
$$</div>
<p>Here $N$ is large enough that the whole interval is admissible. The same compact uniform convergence holds with exponent $\theta H_N^\alpha$ for every $0<\alpha<3/4$ and every fixed $\theta\ge0$.</p>
<p>There are also $\eta_\Lambda,\vartheta_\Lambda>0$ with the following path consequence. Fix $[a,b]\subseteq[-\Lambda,\Lambda]$. If a real Borel functional $\Phi$ on the joint size/surplus path space of EURS is $J_1$-continuous at almost every limiting path and satisfies</p>
<div class="math-display">$$
|\Phi(x,h)|\le A\exp\left\{
 \eta_\Lambda\left(\sup_{a\le t\le b}\|x(t)\|_2^2\right)^{3/2}
 +\vartheta_\Lambda\left(\sup_{a\le t\le b}h(t)\right)^{3/4}
 \right\},
$$</div>
<p>then $\mathbb E\Phi(\mathbf L_N,H_N)\to\mathbb E\Phi(\mathbf X,H)$, with finite expectations. In particular, for $T=b-a>0$,
$I_N=\int_a^b S_N(t)\,dt$ and $J_N=\int_a^bH_N(t)\,dt$,</p>
<div class="math-display">$$
\mathbb E e^{u I_N^{3/2}+v J_N^{3/4}}
 \longrightarrow
 \mathbb E e^{u I^{3/2}+v J^{3/4}}<\infty
$$</div>
<p>whenever $u,v\ge0$, $uT^{3/2}\le\eta_\Lambda$ and
$vT^{3/4}\le\vartheta_\Lambda$.</p>

<p><em>Proof.</em> Condition on the actual full discovery transcript from GGL3. The surplus-edge indicators remain independent Bernoulli($p_N$). For a candidate edge in component $\mathcal C$, assign weight
$w_e=|\mathcal C|/N^{2/3}$. The conditional mean $V_N$ and maximum weight $R_N$ satisfy</p>
<div class="math-display">$$
V_N=p_N\sum_e w_e
 \le Np_N Q_NS_N\le(1+\Lambda)Q_NS_N,
\qquad R_N^2\le S_N.
$$</div>
<p>Indeed, a component of size $k$ has at most $k\max_i A_i$ candidate edges. Summing their weights gives the displayed product. The dummy rows used for queue domination are not included in this conditioning. X92C and N81A, with a union bound and no independence assumption, imply</p>
<div class="math-display">$$
\mathbb P(V_N>x)\le Ce^{-cx^{3/4}}
$$</div>
<p>for large $x$, uniformly in the admissible graphs. On $R_N\le x^{1/4}$, set $t=x^{-1/4}$. The conditional product formula gives</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E[e^{tH_N}\mid\text{discovery transcript}]
 &=\prod_e[1+p_N(e^{tw_e}-1)]\\
 &\le\exp\left(p_N\sum_e(e^{tw_e}-1)\right)
 \le\exp((e-1)tV_N).
\end{aligned}
$$</div>
<p>Thus on the further event $V_N\le x/[2(e-1)]$, conditional exponential Markov bounds the probability of $H_N\ge x$ by $e^{-x^{3/4}/2}$. Adding the exceptional events, using $R_N^2\le S_N$, proves the upper tail. Tail integration gives the moment growth and a sufficiently small uniform exponential parameter. The limiting bound follows either from J2VQ or by truncation and 1QUE.</p>
<p>For $\theta<\varepsilon_\Lambda$, choose $p>1$ with $p\theta<\varepsilon_\Lambda$. The uniform exponential bound gives uniform integrability, so the moving-parameter convergence in 1QUE passes the expectation along every $\lambda_N\to\lambda$. The limiting expectation is continuous in $\lambda$: EURS has no fixed-time jumps and the terminal exponential on a compact interval is an integrable dominating variable. A compactness argument gives the asserted uniform convergence. For $\alpha<3/4$, absorb $p\theta h^\alpha$ into a sufficiently small multiple of $h^{3/4}$ plus a constant and use the same argument.</p>
<p>Finally, choose $\eta_\Lambda,\vartheta_\Lambda$ so that the bounds in X92C and the present theorem hold at $4\eta_\Lambda$ and $4\vartheta_\Lambda$. Monotonicity puts both path suprema at the terminal time. Hölder gives</p>
<div class="math-display">$$
\mathbb E|\Phi(\mathbf L_N,H_N)|^2
 \le A^2
 \left(\mathbb E e^{4\eta_\Lambda S_N(b)^{3/2}}\right)^{1/2}
 \left(\mathbb E e^{4\vartheta_\Lambda H_N(b)^{3/4}}\right)^{1/2}
 \le C.
$$</div>
<p>The same holds in the limit. Uniform integrability and EURS prove convergence of expectations. The integral functionals are continuous under the joint $J_1$ convergence, and
$I_N\le TS_N(b)$, $J_N\le TH_N(b)$, giving the stated example. $\square$</p>
<p>This supplies the finite-graph upper bound left separate in J2VQ. It does not identify the largest admissible exponential parameter, prove convergence at that boundary, or assert parameter differentiability of fractional-exponential expectations.</p>


## The queue on the whole exploration interval {#section-critical-global-queue-law}

<p>Extend the linearly interpolated queue $\widehat A_N$ of CY46 by zero after
$N^{1/3}$. It is an element of $C_0([0,\infty))$, the continuous functions tending to zero at infinity, equipped with the uniform norm. Keep the ranked vectors $x_N,v_N,z_N$ and conditional surplus kernel $\mathcal Q_N$ of OWBW.</p>

<a id="tag-ZFGF" data-assertion="theorem" data-title="The entire critical exploration queue converges uniformly in law, jointly with ranked sizes, weighted surpluses and their conditional law"></a>
<p>For every $\lambda_N\to\lambda$, the reflected Brownian queue $R_\lambda$ belongs to $C_0([0,\infty))$ almost surely, and</p>
<div class="math-display">$$
(\widehat A_N,x_N,v_N,z_N,\mathcal Q_N)
 \ \xrightarrow{\ d\ }\
(R_\lambda,\ell,v,z,\mathcal P(\ell,v))
$$</div>
<p>in
$C_0([0,\infty))\times\ell^2_\downarrow\times\ell^1_+\times\ell^1_+
\times\mathcal P_1(\ell^1_+)$, with $W_1$ on the last factor. In particular, with
$Q_N=\|\widehat A_N\|_\infty$ and $Q=\|R_\lambda\|_\infty$, the laws of $Q_N$ converge to that of $Q$ in every finite Wasserstein distance $W_q$, $q\ge1$. All joint polynomial moments of
$(Q_N,S_N,H_N,V_N,U_N)$ converge to those of $(Q,S,H,V,U)$.</p>
<p>The estimate needed to pass from compact intervals to the whole half-line is the following. There are absolute $c,C>0$ such that, for every $0\le\Lambda<\infty$ and $\delta>0$, all sufficiently large integers $T$ satisfy</p>
<div class="math-display">$$
\begin{aligned}
\limsup_{N\to\infty}\ \sup_{|\lambda|\le\Lambda}
 \mathbb P\!\left(\sup_{t\ge T}\widehat A_N(t)>\delta\right)
 &\le C\sum_{n\ge T}n^2e^{-cn\delta},\\
\sup_{|\lambda|\le\Lambda}
 \mathbb P\!\left(\sup_{t\ge T}R_\lambda(t)>\delta\right)
 &\le C\sum_{n\ge T}n^2e^{-cn\delta}.
\end{aligned}
$$</div>
<p>The first supremum is taken only for large $N$, when the whole parameter interval is admissible. Both right sides tend to zero as $T\to\infty$.</p>

<p><em>Proof.</em> Use the independent-row domination from N81A, writing
$c_*=N^{1/3}$, $\mathcal R_k$ for its reflected walk, and $M_k,D_k$ for its centered and mean parts. Fix $\delta>0$ and put $h=\delta/2$. For large $N$, $1/c_*\le\delta/2$ and $p_N\in[1/(2N),2/N]$ uniformly for $|\lambda|\le\Lambda$. Thus an actual queue height exceeding $\delta$ forces $\mathcal R_k>hc_*$ at one of the adjacent interpolation endpoints.</p>
<p>Only the late part of N81A is needed. Choose the integer $T$ so that
$T\ge8\Lambda+1$ and $Th\ge1$. For $T\le n<c_*$ and every deterministic
$k\ge\lfloor nc_*^2\rfloor$, the reversed independent rows give</p>
<div class="math-display">$$
\mathbb P(\mathcal R_k>hc_*/2)\le e^{-nh/32}.
$$</div>
<p>On the block from $\lfloor nc_*^2\rfloor$ to
$\min\{N,\lfloor(n+1)c_*^2\rfloor\}$, use cells of
$\lceil c_*^2/n^2\rceil$ steps. There are at most $3n^2$ cells. The deterministic drift is decreasing, and the centered oscillation bound is</p>
<div class="math-display">$$
2\exp[-c_0\min\{n^2h^2,hc_*\}]
 \le2e^{-c_1nh},
$$</div>
<p>because $nh\ge1$ and $n<c_*$. These arguments do not require the large-height assumption used for the early interval in N81A. Summing the cell bounds over $n\ge T$ proves the finite-queue estimate. The blocks include the interpolation endpoint immediately to the left of $T$; if $c_*\le T$, the queue is already zero.</p>
<p>For the Brownian queue, use the late-time argument of J2VQ with the fixed height $\delta$. Once $n\ge4\Lambda+1$, the reversed-increment comparison gives
$\mathbb P(R_\lambda(t)>\delta/2)\le e^{-n\delta/4}$ for deterministic $t\ge n$. Subdivide $[n,n+1]$ into $n^2$ cells. Reflection within a cell is bounded by its initial height plus twice the absolute Brownian increment supremum, whose failure probability is at most
$4e^{-n^2\delta^2/32}$. When $n\delta\ge1$, summing again gives the second display. For each rational $\delta>0$, the events
$\{\sup_{t\ge T}R_\lambda(t)>\delta\}$ decrease with $T$ and their probabilities tend to zero. Hence $R_\lambda(t)\to0$ almost surely.</p>
<p>To make the topology argument explicit, multiply a path by a continuous cutoff which is one on $[0,T]$ and zero on $[T+1,\infty)$. CY46 gives convergence of the cut-off paths in $C_0$. The uniform distance to the original path is at most its supremum after $T$, which the preceding estimates make negligible. The converging-together argument proves convergence in $C_0$.</p>
<p>The same truncation works jointly with the ranked coordinates. The finite-rank proof in OWBW retains the queue path on any prescribed compact interval: excursion endpoints, areas and marks are obtained from the same joint exploration limit. Its $\ell^2$ size tails and $\ell^1$ mean and mark tails are unchanged when a compact queue coordinate is retained. OPH4 then adds the conditional kernel. First apply this joint compact-interval convergence and then remove the queue cutoff using the two tail bounds. This identifies the joint limit on the same Brownian geometry, rather than coupling its marginals afterwards.</p>
<p>The supremum is continuous in the uniform norm. N81A supplies uniform moments of every order for $Q_N$, while OWBW supplies them for $S_N,H_N,V_N,U_N$. Hölder gives a higher moment for any polynomial in these variables, so uniform integrability proves the joint moment assertion. Weak convergence and convergence of the $q$th absolute moments give convergence in $W_q$ on the real line. $\square$</p>

## Component shapes and the conditional surplus mean {#section-critical-excursion-shape-law}

<p>A component's queue shape retains more information than its size and surplus. If component $i$ has $k_i$ vertices and begins at exploration time $a_{N,i}$, put</p>
<div class="math-display">$$
e_{N,i}(u)=\widehat A_N(a_{N,i}+x_{N,i}u),
 \qquad 0\le u\le1,\qquad x_{N,i}=k_i/N^{2/3}.
$$</div>
<p>The queue is zero at both endpoints. Let $\mathcal E$ be the space of nonnegative continuous functions on $[0,1]$ which vanish at both endpoints, with its uniform norm. Define a finite measure on $[0,\infty)\times\mathcal E$ by</p>
<div class="math-display">$$
\nu_N=\sum_i x_{N,i}^2\,\delta_{(x_{N,i},e_{N,i})}.
$$</div>
<p>For each limiting excursion $(a_i,a_i+\ell_i)$ of $R_\lambda$, set
$e_i(u)=R_\lambda(a_i+\ell_i u)$ and
$\nu=\sum_i\ell_i^2\delta_{(\ell_i,e_i)}$.</p>

<a id="tag-GDPT" data-assertion="theorem" data-title="Squared-mass-weighted component shapes converge jointly with the full queue, with an exact finite queue-area correction and convergence of growing geometric observables"></a>
<p>Along every $\lambda_N\to\lambda$, the joint convergence in ZFGF remains true after adjoining $\nu_N\Rightarrow\nu$ in the weak topology of finite measures. If $f$ is a continuous real function on $[0,\infty)\times\mathcal E$ satisfying</p>
<div class="math-display">$$
|f(x,e)|\le C(1+x^a+\|e\|_\infty^b)
\qquad(a,b\ge0),
$$</div>
<p>then $\int f\,d\nu_N\Rightarrow\int f\,d\nu$, jointly for finitely many such functions and with the coordinates of ZFGF. All joint polynomial moments of these integrals and $(Q_N,S_N,H_N,V_N,U_N)$ converge.</p>
<p>Two useful examples are the weighted average and maximum heights</p>
<div class="math-display">$$
G_N=\int\!\left(\int_0^1e(u)\,du\right)d\nu_N(x,e),
\qquad
D_N=\int\|e\|_\infty\,d\nu_N(x,e).
$$</div>
<p>Writing $c_N=N^{1/3}$, the conditional surplus mean satisfies the exact identity</p>
<div class="math-display">$$
V_N=(Np_N)\bigl(G_N-c_N^{-1}S_N+c_N^{-2}\bigr).
$$</div>
<p>Consequently $\|V_N-G_N\|_q=O_{\Lambda,q}(N^{-1/3})$ for every fixed $q\ge1$, uniformly over admissible graphs with $|\lambda|\le\Lambda$. The limits are</p>
<div class="math-display">$$
G=\sum_i\ell_i\int_{a_i}^{a_i+\ell_i}R_\lambda(t)\,dt=V,
\qquad
D=\sum_i\ell_i^2\sup_{a_i\le t\le a_i+\ell_i}R_\lambda(t).
$$</div>
<p>For each finite $\Lambda$, there is $\varepsilon_\Lambda>0$ such that, whenever
$|\lambda_N|\le\Lambda$ and $\lambda_N\to\lambda$,</p>
<div class="math-display">$$
\begin{aligned}
&\mathbb E\exp\{rQ_N^{3/2}+sS_N^{3/2}
                 +tH_N^{3/4}+uG_N^{3/4}+vD_N^{3/4}\}\\
&\hspace{1em}\longrightarrow
 \mathbb E\exp\{rQ^{3/2}+sS^{3/2}
                 +tH^{3/4}+uV^{3/4}+vD^{3/4}\}<\infty
\end{aligned}
$$</div>
<p>for all $r,s,t,u,v\in[0,\varepsilon_\Lambda]$.</p>

<p><em>Proof.</em> For each fixed rank, the excursion matching used in OWBW gives convergence of the two endpoints as well as the length. Joint uniform convergence of the queue on a compact interval containing these endpoints implies
$\|e_{N,i}-e_i\|_\infty\to0$ under that coupling: apply uniform continuity of the limiting queue to the affine changes of time. These compact intervals contain any fixed finite set of excursions with probability arbitrarily close to one.</p>
<p>The finite-rank measures therefore converge weakly. The total mass discarded after rank $m$ is $\sum_{i>m}x_{N,i}^2$, whose tail is negligible by the $\ell^2$ size convergence. The limiting tail has the same property. This proves the finite-measure convergence, jointly with the other coordinates. It does not require summability of the unweighted excursion heights or mark counts.</p>
<p>For a function $f$ as in the statement, every component has
$x_{N,i}\le\sqrt{S_N}$ and $\|e_{N,i}\|_\infty\le Q_N$. Hence its discarded integral is bounded in absolute value by</p>
<div class="math-display">$$
C(1+S_N^{a/2}+Q_N^b)\sum_{i>m}x_{N,i}^2.
$$</div>
<p>The first factor is tight and the second has a negligible rank tail. Finite-rank convergence proves convergence of the full integral. Moreover
$|\int f\,d\nu_N|\le CS_N(1+S_N^{a/2}+Q_N^b)$, so the uniform moments in ZFGF and Hölder give uniform integrability for every mixed polynomial under consideration.</p>
<p>For the exact identity, consider one component of size $k$. Its queue starts and ends at zero. The trapezoidal integral of its linear interpolation equals the sum of the queue sizes immediately before its $k$ exploration steps, divided by $N$. After normalizing time to $[0,1]$,</p>
<div class="math-display">$$
\int_0^1e(u)\,du=\frac1{kc_N}\sum_{\text{steps in the component}}A_{j-1}.
$$</div>
<p>At the first step the queue is zero; before each of the other $k-1$ steps it is positive. GGL3 therefore gives the exact candidate count</p>
<div class="math-display">$$
K=\sum_{\text{steps}}(A_{j-1}-1)_+
  =\sum_{\text{steps}}A_{j-1}-(k-1).
$$</div>
<p>Multiply by $p_Nk/N^{2/3}$ and sum over components. Since
$\sum_i k_i=N$ and $\sum_i k_i^2=N^{4/3}S_N$, this gives the asserted identity, including singleton components. Also $G_N,D_N\le Q_NS_N$ and $Np_N=1+\lambda/c_N$. The uniform moments of $Q_N,S_N$ now give the stated $L^q$ error. The limiting formula for $G$ is simply the change of variable along each excursion; its area is the $A_i$ used in OWBW, so $G=\sum_i\ell_iA_i=V$.</p>
<p>Finally,</p>
<div class="math-display">$$
G_N^{3/4},D_N^{3/4}
 \le (Q_NS_N)^{3/4}
 \le \tfrac12(Q_N^{3/2}+S_N^{3/2}).
$$</div>
<p>N81A, X92C and 65IO give a uniform exponential bound for a sufficiently small positive multiple of
$Q_N^{3/2}+S_N^{3/2}+H_N^{3/4}$, by Hölder. Choose $\varepsilon_\Lambda$ small enough that the square of every exponential in the statement is covered by that bound. The convergence in law already proved and uniform integrability pass the expectations. The same estimates hold for the limit. $\square$</p>
<p>These are statements about the complete exploration at one critical parameter, allowing a convergent sequence of parameters. They do not assert a joint Brownian representation across parameters, convergence of a path of conditional kernels, or convergence in the full ranked marked-state path topology.</p>


## Higher Wasserstein distances for the surplus law {#section-surplus-higher-wasserstein}

<p>For $q\ge1$, write
$W_q(P,Q)^q=\inf\mathbb E\|Z-Z'\|_1^q$ and let
$\mathcal P_q(\ell^1_+)$ be the probability measures with finite $q$th moment, equipped with this distance. The Poisson kernel $\mathcal P(x,v)$ remains the one in OPH4.</p>

<a id="tag-WYUD" data-assertion="theorem" data-title="The weighted conditional surplus law converges in every finite Wasserstein distance, with a higher-moment Bernoulli–Poisson coupling bound"></a>
<p>For the finite weighted binomial law of OPH4, put
$R=\max_i x_i$ and $V=\sum_i v_i$. For every integer $r\ge1$,</p>
<div class="math-display">$$
W_r\!\left(\operatorname{Law}((x_iY_i)_i),\mathcal P(x,v)\right)^r
 \le C_r\sum_{k=1}^r R^{r-k}(pV)^k.
$$</div>
<p>The all-zero case has distance zero. Under the continuity assumptions of OPH4,
$\mathcal P(x^{(n)},v^{(n)})\to\mathcal P(x,v)$ in $W_q$ for every finite $q\ge1$.</p>
<p>Consequently, for each fixed $q\ge1$, the joint critical-graph convergence in ZFGF and GDPT holds with the conditional kernel in $\mathcal P_q(\ell^1_+)$ instead of $\mathcal P_1(\ell^1_+)$. Its finite Poisson approximation satisfies</p>
<div class="math-display">$$
\sup_{\substack{|\lambda|\le\Lambda\\p_N(\lambda)\in[0,1]}}
\mathbb E\,W_q\bigl(\mathcal Q_N,\mathcal P(x_N,v_N)\bigr)^q
 \le \frac{C_{\Lambda,q}}N.
$$</div>
<p>This is an error bound for replacing the finite conditional binomials by Poisson variables on the same finite exploration geometry. It is not a rate of convergence to the Brownian geometry.</p>

<p><em>Proof.</em> In the single-edge coupling of OPH4, let
$D=|\xi-P|$. When $P\ge1$, $D=P-1$; when $P=0$, a discrepancy of one has unconditional probability $p-1+e^{-p}$. Therefore, for every integer $j\ge1$,</p>
<div class="math-display">$$
\mathbb ED^j
 =p-1+e^{-p}
   +e^{-p}\sum_{m\ge2}(m-1)^j\frac{p^m}{m!}
 \le a_jp^2,\qquad 0\le p\le1,
$$</div>
<p>where $a_j=\frac12+\sum_{m\ge2}(m-1)^j/m!<\infty$ is sufficient. The sharper first-moment bound is $\mathbb ED\le p^2$.</p>
<p>Use independent couplings for every candidate edge $e$, with component weight $w_e$. The $\ell^1$ distance between the two weighted component vectors is at most
$T=\sum_e w_eD_e$. Expanding its $r$th moment, group the $r$ factors by the distinct edges they use. A group of size $j$ contributes at most</p>
<div class="math-display">$$
\sum_e w_e^j\mathbb ED_e^j
 \le a_jR^{j-1}p^2\sum_e w_e
 =a_jR^{j-1}pV.
$$</div>
<p>For a partition into $k$ groups, dropping the distinct-edge restriction only increases the nonnegative sum. The powers of $R$ total $r-k$. Summing the finitely many partitions proves the stated bound.</p>
<p>The kernel itself has all moments. For an integer $r\ge1$, the cumulants of the nonnegative sum $\|Z\|_1$, where $Z\sim\mathcal P(x,v)$, are
$\sum_i x_i^{j-1}v_i\le R^{j-1}V$. The moment-partition formula, first for finitely many coordinates and then by monotone convergence, gives</p>
<div class="math-display">$$
\mathbb E_{\mathcal P(x,v)}\|Z\|_1^r
 \le c_r\sum_{k=1}^r R^{r-k}V^k.
$$</div>
<p>If $x^{(n)}\to x$ in $\ell^2$ and $v^{(n)}\to v$ in $\ell^1$, the corresponding $R_n,V_n$ are bounded. OPH4 gives weak convergence of the kernels, while the preceding bound at an integer $r>q$ makes their $q$th norm powers uniformly integrable. Their $q$th moments therefore converge. The characterization of $W_q$ convergence by weak convergence and convergence of the $q$th norm moments proves kernel continuity.</p>
<p>In the critical graph, condition on the discovery transcript and use the explicit independent-edge coupling above. Its unconditional error moments satisfy</p>
<div class="math-display">$$
\mathbb ET^r
 \le C_r\sum_{k=1}^r
 p_N^k\,\mathbb E[R_N^{r-k}V_N^k]
 =O_{\Lambda,r}(N^{-1}),
 \qquad R_N=\max_i x_{N,i}.
$$</div>
<p>Here $R_N\le\sqrt{S_N}$, $p_N\le(1+\Lambda)/N$, and OWBW bounds every mixed moment needed. The same estimate holds for $\mathbb ET$. For $1<q<r$, Hölder interpolation gives</p>
<div class="math-display">$$
\mathbb ET^q
 \le(\mathbb ET)^{(r-q)/(r-1)}
     (\mathbb ET^r)^{(q-1)/(r-1)}
 =O_{\Lambda,q,r}(N^{-1}).
$$</div>
<p>Since $W_q(\mathcal Q_N,\mathcal P(x_N,v_N))^q
\le\mathbb E[T^q\mid\mathcal D_N]$, this proves the bound for every real $q\ge1$. The conditional Poisson kernel is continuous at the limiting pair, whose masses are positive. Its joint convergence with the geometry follows by continuous mapping; the vanishing $W_q$ approximation error then replaces it by $\mathcal Q_N$. $\square$</p>

## Conditional analytic transforms and finite cumulants {#section-surplus-conditional-analytic-limit}

<p>Given the full discovery transcript, define the random entire function</p>
<div class="math-display">$$
F_N(z)=\mathbb E[e^{zH_N}\mid\mathcal D_N]
 =\prod_i\bigl[1+p_N(e^{zx_{N,i}}-1)\bigr]^{K_{N,i}},
 \qquad z\in\mathbb C.
$$</div>
<p>The limiting conditional transform from OWBW is</p>
<div class="math-display">$$
F(z)=\exp L(z),\qquad
L(z)=\sum_i A_i(e^{z\ell_i}-1).
$$</div>
<p>Use uniform convergence on compact subsets of $\mathbb C$ as the topology on entire functions.</p>

<a id="tag-L3KC" data-assertion="theorem" data-title="The conditional surplus transforms converge as random entire functions, and exact Bernoulli corrections give all conditional cumulant limits"></a>
<p>Along every $\lambda_N\to\lambda$, $F_N\Rightarrow F$ in this topology, jointly with the geometry and conditional kernel in WYUD, for any fixed finite Wasserstein order. Every finite collection of complex derivatives converges jointly in the same compact-open topology.</p>
<p>For an integer $r\ge1$, let $\kappa_{N,r}$ be the conditional $r$th cumulant of $H_N$ and put</p>
<div class="math-display">$$
T_{N,r}=\sum_i x_{N,i}^{r-1}v_{N,i},\qquad
b_r(p)=\sum_{k=1}^r(-1)^{k-1}(k-1)!
           \left\{\begin{matrix}r\\k\end{matrix}\right\}p^{k-1},
$$</div>
<p>where the braces denote Stirling numbers of the second kind. Then, including $p_N=0$,</p>
<div class="math-display">$$
\kappa_{N,r}=b_r(p_N)T_{N,r},\qquad
\kappa_r=\sum_i\ell_i^{r-1}v_i=\sum_i\ell_i^rA_i.
$$</div>
<p>For every fixed $r\ge1$ and $q\ge1$,</p>
<div class="math-display">$$
\|\kappa_{N,r}-T_{N,r}\|_q
 =O_{\Lambda,r,q}(N^{-1})
 \qquad(|\lambda|\le\Lambda).
$$</div>
<p>Finite collections of these conditional cumulants converge jointly with the preceding objects, and all their mixed polynomial moments with
$(Q_N,S_N,H_N,V_N,U_N)$ converge. For example,
$b_1=1$, $b_2=1-p$, $b_3=(1-p)(1-2p)$ and
$b_4=(1-p)(1-6p+6p^2)$.</p>

<p><em>Proof.</em> For compatible $(x,v)$ define</p>
<div class="math-display">$$
L_{x,v}(z)=\sum_i v_i f_z(x_i),\qquad
f_z(u)=
\begin{cases}
(e^{zu}-1)/u,&u>0,\\
z,&u=0.
\end{cases}
$$</div>
<p>The identity $f_z(u)=z\int_0^1e^{zsu}\,ds$ removes the apparent singularity. For $0\le u\le M$ and $|z|\le a$,
$|f_z(u)|\le ae^{aM}$ and
$|\partial_u f_z(u)|\le a^2e^{aM}/2$.
Thus $L_{x,v}$ is entire and the map $(x,v)\mapsto L_{x,v}$ is continuous from $\ell^2\times\ell^1$ to the compact-open topology: if the masses in both pairs are at most $M$,</p>
<div class="math-display">$$
\sup_{|z|\le a}|L_{x',v'}(z)-L_{x,v}(z)|
 \le ae^{aM}\|v'-v\|_1
   +\tfrac12a^2e^{aM}\|v\|_1\|x'-x\|_\infty.
$$</div>
<p>Normal convergence of the defining series on each disk justifies holomorphy. At the limiting pair this function is $L$.</p>
<p>Fix a disk of radius $a>0$. On the event</p>
<div class="math-display">$$
p_N(e^{aR_N}-1)\le\tfrac12,
 \qquad R_N=\max_i x_{N,i},
$$</div>
<p>each factor in $F_N$ has an analytic logarithm given by the power series for $\log(1+u)$. The sum of these logarithms vanishes at zero and satisfies</p>
<div class="math-display">$$
\begin{aligned}
\sup_{|z|\le a}|\log F_N(z)-L_{x_N,v_N}(z)|
 &\le2p_N^2\sum_iK_{N,i}
                 \sup_{|z|\le a}|e^{zx_{N,i}}-1|^2\\
 &\le2p_Na^2e^{2aR_N}U_N.
\end{aligned}
$$</div>
<p>The event has probability tending to one, since $R_N$ is tight and $p_N\to0$. The upper bound tends to zero in probability, since $(R_N,U_N)$ is tight. Also
$\sup_{|z|\le a}|L_{x_N,v_N}(z)|\le ae^{aR_N}V_N$ is tight. Exponentiating therefore gives
$\sup_{|z|\le a}|F_N(z)-\exp L_{x_N,v_N}(z)|\to0$ in probability. Apply this on integer-radius disks and use continuity of $(x,v)\mapsto\exp L_{x,v}$ to obtain the joint entire-function limit. Cauchy's formula on a slightly larger disk gives continuity of each differentiation operator and the derivative conclusion. No global logarithm of the finite transform is needed.</p>
<p>For the cumulants, expand at the origin:</p>
<div class="math-display">$$
\log[1+p(e^t-1)]
 =\sum_{k\ge1}\frac{(-1)^{k-1}}k p^k(e^t-1)^k.
$$</div>
<p>The $r$th derivative at zero of $(e^t-1)^k$ is
$k!\left\{\begin{smallmatrix}r\\k\end{smallmatrix}\right\}$, and it vanishes when $k>r$. Thus the Bernoulli cumulant is $p\,b_r(p)$. Conditional independence of all candidate edges, with their component weights, gives
$\kappa_{N,r}=p_Nb_r(p_N)\sum_iK_{N,i}x_{N,i}^r
=b_r(p_N)T_{N,r}$. This polynomial identity includes both endpoint probabilities without division by $p_N$.</p>
<p>On $[0,1]$, $|b_r(p)-1|\le c_rp$. Also
$T_{N,r}\le R_N^{r-1}V_N$; the uniform moments in OWBW prove the displayed $L^q$ error. For each fixed $r$, the map
$(x,v)\mapsto\sum_i x_i^{r-1}v_i$ is continuous on the relevant product space, using the uniform bound on the masses and $\ell^1$ convergence. Its limit is the Poisson conditional cumulant in OWBW. These quantities and $\kappa_{N,r}$ have uniform moments of every order. Joint convergence and Hölder therefore pass all the stated mixed polynomial moments. $\square$</p>
<p>This convergence concerns random conditional transforms. It does not give convergence of their positive-real expectations: for every real $t>0$,
$\mathbb EF_N(t)=\mathbb E e^{tH_N}\to\infty$ and
$\mathbb EF(t)=\mathbb E e^{tH}=\infty$, by 7E7T. It also makes no assertion about a path of conditional kernels across the critical window.</p>
