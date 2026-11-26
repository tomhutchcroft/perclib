---
{
  "id": "branching-processes",
  "title": "Galton–Watson branching processes",
  "subtitle": "Extinction, total progeny and the critical generating function",
  "kind": "model",
  "category": "Models",
  "summary": "Generating functions determine extinction and expected total progeny. Critical nondegeneracy and lattice support must be kept separate when interpreting the mean-field picture.",
  "context": ["Start from one individual: $Z_0=1$.", "Each individual has an independent copy of a nonnegative integer-valued offspring variable $\\xi$, with finite mean $m$.", "The offspring law is the same in every generation."],
  "related": ["exploration", "susceptibility", "subcritical-bound", "regular-variation"],
  "sourceIds": ["hutchcroft-book", "perclib-offspring-generating-function", "perclib-laplace-tail", "perclib-offspring-transform", "perclib-quadratic-recursion"],
  "aliases": ["Galton–Watson", "offspring", "extinction", "total progeny", "mean field", "generating function"],
  "prototypeUses": []
}
---

## Extinction as a fixed point {#section-extinction}

<a id="tag-NCWZ" data-assertion="definition" data-title="Galton–Watson process and total progeny"></a><p>Given independent copies $\xi_{n,j}$ of $\xi$, let</p><div class="math-display">$$Z_0=1,\qquad Z_{n+1}=\sum_{j=1}^{Z_n}\xi_{n,j},\qquad T=\sum_{n=0}^{\infty}Z_n\in\mathbb N\cup\{\infty\}.$$</div><p>The empty sum is zero, so zero is absorbing. Each generation is finite almost surely. Write $\phi(s)=\mathbb E[s^\xi]$ for $0\leq s\leq1$, with $0^0=1$, and $m=\mathbb E\xi$.</p>

<a id="tag-8TFY" data-assertion="proposition" data-title="Extinction probability is the least generating-function fixed point"></a><p>The extinction probability $q=\mathbb P(\exists n:Z_n=0)$ is the least solution of $\phi(s)=s$ in $[0,1]$.</p><p><em>Proof.</em> Put $q_n=\mathbb P(Z_n=0)$. The child subtrees are independent copies of the original process, so $q_0=0$ and $q_{n+1}=\phi(q_n)$. The events $\{Z_n=0\}$ increase, giving $q_n\uparrow q$. Continuity of $\phi$ yields $q=\phi(q)$. If $r\in[0,1]$ is any fixed point, monotonicity of $\phi$ and induction give $q_n\leq r$, hence $q\leq r$.</p>

<a id="tag-BFM4" data-assertion="theorem" data-title="Extinction criterion with the deterministic critical exception"></a><p>If $m&lt;1$, extinction is almost sure. If $m=1$, extinction is almost sure unless $\xi=1$ almost surely; in that exceptional case $Z_n=1$ for every $n$ and extinction never occurs. If $m&gt;1$, survival has positive probability.</p><p><em>Proof.</em> For $0\leq s&lt;1$, the elementary inequality $s^k\geq1-k(1-s)$ gives $\phi(s)\geq1-m(1-s)&gt;s$ when $m&lt;1$. Thus one is the only fixed point. When $m=1$ and the law is not concentrated at one, it assigns positive probability to some $k\geq2$, where the same inequality is strict. Again $\phi(s)&gt;s$ for $s&lt;1$. The deterministic exception is immediate from the recursion. Finally, if $m&gt;1$, the left derivative $\phi'(1)=m$ implies $\phi(s)-s&lt;0$ for $s&lt;1$ sufficiently close to one. Since $\phi(0)\geq0$, continuity gives a fixed point below one, so the least fixed point is below one.</p><p>The statement here includes the deterministic critical exception explicitly.</p>

## Expected total progeny {#section-expectation}

<a id="tag-UKY4" data-assertion="proposition" data-title="Mean generation sizes and expected total progeny"></a><p>For every $n\geq0$, $\mathbb E Z_n=m^n$. Consequently</p><div class="math-display">$$\mathbb E T=\begin{cases}(1-m)^{-1},&amp;m&lt;1,\\ \infty,&amp;m\geq1.\end{cases}$$</div><p><em>Proof.</em> Conditional on the population in generation $n$, its members have mean $m$ offspring each. Thus $\mathbb E[Z_{n+1}\mid Z_n]=mZ_n$, and induction gives the generation means. Tonelli's theorem then gives $\mathbb E T=\sum_{n\geq0}m^n$.</p><p>At a nondegenerate critical law, $T$ is finite almost surely but has infinite expectation. There is no contradiction: extinction determines whether $T$ is finite, not whether its distribution is integrable. The subcritical formula is the branching-process reference for the <a href="#/susceptibility">susceptibility</a> exponent.</p>

## The critical square-root singularity {#section-critical-transform}

<a id="tag-OVG9" data-assertion="proposition" data-title="Critical total-progeny generating-function asymptotic"></a><p>Suppose $m=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Let $F(s)=\mathbb E[s^T]$. Then, as $s\uparrow1$,</p><div class="math-display">$$1-F(s)\sim\sqrt{\frac{2(1-s)}{\sigma^2}}.$$</div><p><em>Proof.</em> Extinction is almost sure, so $T&lt;\infty$ almost surely and $F(s)\uparrow1$. Decomposing the tree at its root gives $F(s)=s\phi(F(s))$ for $0\leq s&lt;1$. Finite second moment gives</p><div class="math-display">$$\phi(1-u)=1-u+\frac{\sigma^2}{2}u^2+o(u^2).$$</div><p>Indeed, $\phi''(s)=\mathbb E[\xi(\xi-1)s^{\xi-2}]$ for $0&lt;s&lt;1$, with the terms for $\xi&lt;2$ taken as zero. It increases to $\mathbb E[\xi(\xi-1)]=\sigma^2$ as $s\uparrow1$, and integrating twice gives the expansion. Set $t=1-s$ and $u=1-F(s)$. The functional equation becomes</p><div class="math-display">$$t(1-u)=(1-t)\left(\frac{\sigma^2}{2}u^2+o(u^2)\right).$$</div><p>Since $t,u\to0$ and $u&gt;0$ for $s&lt;1$, division by $u^2$ gives $t/u^2\to\sigma^2/2$.</p><p>This is a transform asymptotic. The two-sided tail order is proved below without a Tauberian theorem. The <a href="/tag/PVM9/">exact tail equivalent</a>, $\mathbb P(T\geq n)\sim\sqrt{2/(\pi\sigma^2)}\,n^{-1/2}$, follows from the <a href="/articles/regular-variation/">Laplace–tail theorem</a>. A point-probability asymptotic requires a separate local result with the appropriate lattice support. For the critical law $\mathbb P(\xi=0)=\mathbb P(\xi=2)=1/2$, every finite family tree has odd total size: its number of edges is twice its number of parents, while also equalling $T-1$. Hence $\mathbb P(T=n)=0$ for every even $n$. Thus an unqualified all-integer point-probability estimate cannot hold for this law.</p>


## Critical survival to generation n {#section-generation-survival}

<a id="tag-8WO7" data-assertion="proposition" data-title="Critical survival probability with finite nonzero variance"></a><p>Under the same assumptions $m=1$ and $0&lt;\sigma^2&lt;\infty$,</p><div class="math-display">$$\mathbb P(Z_n&gt;0)\sim\frac{2}{\sigma^2 n}.$$</div><p><em>Proof.</em> Write $r_n=\mathbb P(Z_n&gt;0)$. Extinction gives $r_n\downarrow0$, and the offspring decomposition gives $r_{n+1}=1-\phi(1-r_n)$. The second-order expansion therefore yields</p><div class="math-display">$$r_{n+1}=r_n-\frac{\sigma^2}{2}r_n^2+o(r_n^2).$$</div><p>Each $r_n$ is positive: the offspring law gives positive probability to at least one child, and a lineage can continue for any fixed finite number of generations. Since $r_{n+1}/r_n\to1$,</p><div class="math-display">$$\frac1{r_{n+1}}-\frac1{r_n}=\frac{r_n-r_{n+1}}{r_nr_{n+1}}\longrightarrow\frac{\sigma^2}{2}.$$</div><p>Summing these increments and taking their arithmetic mean gives $1/(nr_n)\to\sigma^2/2$.</p>

## Population size conditional on survival {#section-yaglom}

<a id="tag-AYHV" data-assertion="theorem" data-title="Yaglom's exponential population limit with finite offspring variance"></a>
<p>For a Galton–Watson process started from one ancestor, suppose $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Put $a=\sigma^2/2$. Conditional on $Z_n&gt;0$,</p>
<div class="math-display">$$\frac{Z_n}{n}\ \Longrightarrow\ Y,\qquad
\mathbb P(Y&gt;x)=e^{-x/a}\quad(x\geq0).$$</div>
<p>The conditional means also converge to $a$, and the conditional laws of $Z_n/n$ are uniformly integrable. No third moment or aperiodicity assumption is needed.</p>
<p><em>Proof.</em> Write $\phi$ for the offspring generating function and $Q_n=\mathbb P(Z_n&gt;0)$. Fix $\lambda&gt;0$, and for $0\leq k\leq n$ set</p>
<div class="math-display">$$u_{k,n}=1-\mathbb E[e^{-\lambda Z_k/n}].$$</div>
<p>The branching property gives $u_{k+1,n}=1-\phi(1-u_{k,n})$, starting at $u_{0,n}=1-e^{-\lambda/n}$. Criticality implies $0&lt;u_{k,n}\leq u_{0,n}$, and the finite-variance expansion gives</p>
<div class="math-display">$$\frac1{u_{k+1,n}}-\frac1{u_{k,n}}=a+o(1),$$</div>
<p>where the error is uniform in $0\leq k&lt;n$: every argument is at most $u_{0,n}\to0$. Summing yields $1/u_{n,n}=1/u_{0,n}+n(a+o(1))$, hence</p>
<div class="math-display">$$nu_{n,n}\longrightarrow\frac{\lambda}{1+a\lambda}.$$</div>
<p>By <a href="/tag/8WO7/">the survival asymptotic</a>, $nQ_n\to1/a$. Removing the mass at zero therefore gives</p>
<div class="math-display">$$\mathbb E[e^{-\lambda Z_n/n}\mid Z_n&gt;0]
=1-\frac{u_{n,n}}{Q_n}\longrightarrow\frac1{1+a\lambda}.$$</div>
<p>The limiting Laplace transform is that of the stated exponential law and is continuous at zero, proving weak convergence. Since $\mathbb E Z_n=1$, the conditional mean is $1/(nQ_n)\to a=\mathbb E Y$. For nonnegative laws, weak convergence together with convergence of these means implies uniform integrability: subtract the convergent expectations of $\min(Z_n/n,K)$ from the means, then send $K\to\infty$.</p>
<p>The normalization concerns population in one generation, rather than total progeny. In particular, the exponential limit here and the <a href="/tag/0OEW/">size-biased finite-progeny limit</a> describe different observables.</p>

## Total-progeny tail order {#section-progeny-tail}

<a id="tag-MIFH" data-assertion="proposition" data-title="Critical total-progeny tail has order inverse square root"></a><p>If $m=1$ and $0&lt;\sigma^2&lt;\infty$, there are constants $c,C&gt;0$ such that, for all sufficiently large integers $n$,</p><div class="math-display">$$c n^{-1/2}\leq\mathbb P(T\geq n)\leq C n^{-1/2}.$$</div><p><em>Proof.</em> Set $G(t)=\mathbb E[1-e^{-tT}]$. The transform asymptotic and $1-e^{-t}\sim t$ give $G(t)\sim a\sqrt t$, where $a=\sqrt{2/\sigma^2}$. On $\{T\geq n\}$, $1-e^{-T/n}\geq1-e^{-1}$, so</p><div class="math-display">$$\mathbb P(T\geq n)\leq\frac{G(1/n)}{1-e^{-1}}\leq C n^{-1/2}.$$</div><p>Increasing $C$ if necessary makes the bound hold for every $n\geq1$. For a fixed large constant $L$, split according to $T&lt;n$ and $T\geq n$ and use $1-e^{-x}\leq x$:</p><div class="math-display">$$G\!\left(\frac1{Ln}\right)\leq\frac{\mathbb E[T\wedge n]}{Ln}+\mathbb P(T\geq n)\leq\frac{2C}{L\sqrt n}+\mathbb P(T\geq n).$$</div><p>The last step uses $\mathbb E[T\wedge n]=\sum_{k=1}^n\mathbb P(T\geq k)\leq2C\sqrt n$. For sufficiently large $n$, the left-hand side is at least $a/(2\sqrt{Ln})$. Choose $\sqrt L&gt;4C/a$; subtracting the first term leaves a positive constant times $n^{-1/2}$. This proves the lower bound without a local limit theorem and is compatible with periodic support.</p>

## A near-critical thinning family {#section-thinning}

<a id="tag-XXQK" data-assertion="proposition" data-title="Near-critical survival under independent offspring thinning"></a>
<p>Let $\eta$ be a nonnegative integer-valued random variable with $\mu=\mathbb E\eta&gt;1$ and $\mathbb E\eta^2&lt;\infty$. Write $\nu=\mathbb E[\eta(\eta-1)]$. For $p\in[0,1]$, let $\xi_p$, conditional on $\eta$, have distribution $\operatorname{Binomial}(\eta,p)$, and let $\rho(p)$ be the survival probability of the Galton–Watson process with offspring law $\xi_p$. Then $0&lt;\nu&lt;\infty$, the threshold is $p_c=1/\mu$, and</p>
<div class="math-display">$$\rho(p)=0\quad(p\leq p_c),\qquad\rho(p)&gt;0\quad(p&gt;p_c),\qquad\rho(p)\sim\frac{2\mu^3}{\nu}(p-p_c)\quad(p\downarrow p_c).$$</div>
<p><em>Proof.</em> Put $\phi(s)=\mathbb E[s^\eta]$. Conditional binomial expectation gives the offspring generating function $\phi_p(s)=\phi(1-p+ps)$, with mean $p\mu$ and second factorial moment $p^2\nu$. Since $\mu&gt;1$, the law of $\eta$ gives positive mass to some value at least two, so $\nu&gt;0$. At $p_c&lt;1$, the thinned law has $\mathbb P(\xi_{p_c}=0)=\mathbb E[(1-p_c)^\eta]&gt;0$ and is not the deterministic one-child law. The <a href="/tag/BFM4/">extinction criterion</a> therefore gives the first two assertions, including extinction at the threshold.</p>
<p>Let $q(p)=1-\rho(p)$. By the <a href="/tag/8TFY/">fixed-point characterization</a>, $q(p)=\phi(1-p+pq(p))$. As $p\downarrow p_c$, every subsequential limit $q_*$ of $q(p)$ satisfies $q_*=\phi(1-p_c+p_cq_*)$, by continuity. The critical offspring generating function has no fixed point below one, so $q_*=1$. Compactness of $[0,1]$ now gives $\rho(p)\to0$.</p>
<p>Finite second moment gives $\phi''(s)\uparrow\nu$ as $s\uparrow1$. Integrating twice yields the expansion</p>
<div class="math-display">$$\phi(1-t)=1-\mu t+\frac\nu2t^2+o(t^2).$$</div>
<p>Apply it with $t=p\rho(p)$ in the extinction equation. For $p&gt;p_c$ the survival probability is positive, so division by it gives</p>
<div class="math-display">$$\mu p-1=\frac\nu2p^2\rho(p)+o(\rho(p)).$$</div>
<p>Since $p\to1/\mu$ and $\nu&gt;0$, this implies $\rho(p)/(\mu p-1)\to2\mu^2/\nu$, proving the stated equivalent.</p>
<p>The critical offspring variance is $\sigma_c^2=p_c^2\nu$, so the same equivalent reads $\rho(p)\sim2(p\mu-1)/\sigma_c^2$. Below criticality the existing <a href="/tag/UKY4/">total-progeny expectation</a> is exactly $(1-p\mu)^{-1}$. For a deterministic potential offspring count $\eta=2$, the survival coefficient is eight, agreeing with the <a href="/articles/binary-tree-percolation/">binary-tree formula</a> at $p_c=1/2$.</p>
<p>This is a precise family version of the near-critical calculation. It uses an $o(t^2)$ remainder from one fixed generating function, not an $O(t^3)$ remainder requiring a third-moment bound. For an arbitrary family of offspring laws whose mean approaches one, pointwise finite second moments alone do not supply the uniform Taylor control or convergence of extinction roots used here.</p>

## Varying the offspring law {#section-varying-laws}

<a id="tag-N9P5" data-assertion="proposition" data-title="Near-critical survival with uniformly integrable squared offspring"></a>
<p>Let $\xi_j$ be nonnegative integer-valued offspring variables with means $m_j&gt;1$ tending to one. Suppose $\xi_j$ converges in distribution to $\xi$, where $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$, and suppose their squares are uniformly integrable:</p>
<div class="math-display">$$\lim_{R\to\infty}\sup_j\mathbb E[\xi_j^2\mathbf1_{\{\xi_j&gt;R\}}]=0.$$</div>
<p>If $\rho_j$ is the survival probability for offspring law $\xi_j$, then</p>
<div class="math-display">$$\rho_j\sim\frac{2(m_j-1)}{\sigma^2}\sim\frac{2(m_j-1)}{\mathbb E[\xi_j(\xi_j-1)]}.$$</div>
<p><em>Proof.</em> Write $\phi_j(s)=\mathbb E[s^{\xi_j}]$ and $\phi(s)=\mathbb E[s^\xi]$. Convergence in distribution gives pointwise convergence of these generating functions on $[0,1]$. Also $|\phi_j(s)-\phi_j(t)|\leq m_j|s-t|$, and the means are bounded. Thus whenever $s_j\to s$, we have $\phi_j(s_j)\to\phi(s)$. Every subsequential limit of the extinction probabilities $q_j=1-\rho_j$ is consequently a fixed point of $\phi$. The limiting law is critical and nondegenerate, so its only fixed point is one. It follows that $\rho_j\to0$.</p>
<p>Put $b_j=\mathbb E[\xi_j(\xi_j-1)]$. Truncating the expectations at a fixed integer $R$ and using uniform integrability on the remaining tail gives $b_j\to\mathbb E[\xi(\xi-1)]=\sigma^2$. The same truncation makes the second-order expansion uniform. Indeed, with the summands for $\xi_j&lt;2$ understood as zero,</p>
<div class="math-display">$$0\leq b_j-\phi_j''(1-u)=\mathbb E\!\left[\xi_j(\xi_j-1)\bigl(1-(1-u)^{\xi_j-2}\bigr)\right].$$</div>
<p>On $\{\xi_j\leq R\}$ the expression is bounded by $R^2[1-(1-u)^R]$, independently of $j$; the complementary expectation is bounded by $\mathbb E[\xi_j^2\mathbf1_{\{\xi_j&gt;R\}}]$. First choose $R$ large, then let $u\downarrow0$. Integrating twice therefore gives, uniformly in $j$,</p>
<div class="math-display">$$\phi_j(1-u)=1-m_ju+\frac{b_j}{2}u^2+o(u^2).$$</div>
<p>Insert $u=\rho_j$ into $1-\rho_j=\phi_j(1-\rho_j)$. Since $m_j&gt;1$, the extinction criterion gives $\rho_j&gt;0$, and division by $\rho_j$ yields $m_j-1=(b_j/2+o(1))\rho_j$. The two equivalents follow from $b_j\to\sigma^2&gt;0$.</p>
<p>No coupling or monotonicity of the offspring laws is required. Independent thinning of one square-integrable potential offspring variable satisfies the tail condition because the thinned count is bounded by that variable. A uniform moment bound of order $2+\delta$, for any $\delta&gt;0$, is another sufficient condition, since its squared tail is at most $R^{-\delta}\sup_j\mathbb E\xi_j^{2+\delta}$.</p>

<a id="tag-Q4NA" data-assertion="proposition" data-title="Finite second moments alone do not imply a near-critical survival asymptotic"></a>
<p>For integers $j\geq2$, let $\xi_j=j$ with probability $1/[j(j-1)]$ and $\xi_j=1$ otherwise. Then</p>
<div class="math-display">$$m_j=1+\frac1j,\qquad\mathbb E[\xi_j(\xi_j-1)]=1,\qquad\mathbb E\xi_j^2=2+\frac1j,\qquad\rho_j=1.$$</div>
<p><em>Proof.</em> The moment formulas follow directly from the two masses. Every individual has at least one child, so the process never becomes extinct. Thus the expression $2(m_j-1)/\mathbb E[\xi_j(\xi_j-1)]=2/j$ tends to zero although survival is certain. Here $\xi_j$ converges to the deterministic one-child law, and the squares are not uniformly integrable: for $j&gt;R$, their tail expectation is $j/(j-1)$. Even bounded second moments and a positive limiting second factorial moment do not prevent the second moment from escaping to increasingly rare large offspring counts.</p>
<p>These statements make explicit the family hypotheses behind the near-critical expansion. The example does not contradict the expansion for one fixed generating function; it prevents applying that expansion uniformly to an arbitrary varying family.</p>

## The joint mean and ghost-field limit {#section-crossover}

<a id="tag-DGVA" data-assertion="theorem" data-title="Near-critical total-progeny ghost crossover with uniformly integrable squared offspring"></a>
<p>Let $\xi_j$ be nonnegative integer-valued offspring variables converging in distribution to $\xi$, where $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Assume that $(\xi_j^2)$ is uniformly integrable. Put $\varepsilon_j=\mathbb E\xi_j-1$, let $T_j$ be the total progeny from one ancestor, and, for $h&gt;0$, set</p>
<div class="math-display">$$M_j(h)=1-\mathbb E[e^{-hT_j};\,T_j&lt;\infty].$$</div>
<p>Thus infinite progeny contributes one to the ghost probability. For every sequence $h_j&gt;0$ tending to zero,</p>
<div class="math-display">$$M_j(h_j)\sim
\frac{\varepsilon_j+\sqrt{\varepsilon_j^2+2\sigma^2h_j}}{\sigma^2}.$$
</div>
<p>The means may approach one from either side or equal one. No relation between the rates of decay of $h_j$ and $\varepsilon_j^2$ is assumed.</p>
<p><em>Proof.</em> Write $\phi_j$ for the offspring generating function. Root decomposition gives</p>
<div class="math-display">$$1-M_j(h)=e^{-h}\phi_j(1-M_j(h)).$$</div>
<p>The bounded-mean continuity argument in <a href="/tag/N9P5/">N9P5</a> applies without the supercritical restriction: every subsequential limit of $1-M_j(h_j)$ is a fixed point of the limiting critical generating function. Its only fixed point is one, so $u_j=M_j(h_j)\to0$. Uniform integrability gives $\varepsilon_j\to0$ and, by the same truncated second-derivative argument,</p>
<div class="math-display">$$\phi_j(1-u_j)=1-(1+\varepsilon_j)u_j+a_ju_j^2,
\qquad a_j\longrightarrow\sigma^2/2.$$</div>
<p>Multiplying the root equation by $e^{h_j}$ now gives the exact relation</p>
<div class="math-display">$$a_ju_j^2-\varepsilon_ju_j
=(e^{h_j}-1)(1-u_j)=c_jh_j,\qquad c_j\longrightarrow1.$$</div>
<p>This quadratic comparison remains stable when the positive root is much smaller than $|\varepsilon_j|$. To see this directly, let $r_j&gt;0$ solve $(\sigma^2/2)r_j^2-\varepsilon_jr_j=h_j$. If $a_j/(\sigma^2/2)$ and $c_j$ lie in $[1-\eta,1+\eta]$, substitution into the two bounding quadratics gives</p>
<div class="math-display">$$\frac{1-\eta}{1+\eta}r_j\leq u_j\leq
\frac{1+\eta}{1-\eta}r_j\qquad(0&lt;\eta&lt;1).$$</div>
<p>Each quadratic has exactly one positive root, since its constant term is negative. Letting $\eta\downarrow0$ proves the equivalent, uniformly in the sign and relative size of $\varepsilon_j$.</p>
<p>If $\varepsilon_j^2=o(h_j)$, this is the critical square-root law $M_j(h_j)\sim\sqrt{2h_j/\sigma^2}$. If $h_j=o(\varepsilon_j^2)$, it gives $M_j(h_j)\sim h_j/|\varepsilon_j|$ on the subcritical side and $M_j(h_j)\sim2\varepsilon_j/\sigma^2$ on the supercritical side. The latter is the survival contribution. These are positive-field limits: with the literal empty ghost field, $M_j(0)=0$, while $M_j(0+)=\mathbb P(T_j=\infty)$.</p>
<p>The <a href="/articles/size-biased-laws/#section-branching-cutoff">finite-progeny scaling law</a> below isolates the finite clusters on both sides. The crossover is a transform statement; it does not assert an all-integer local probability estimate.</p>

## Exact finite-progeny probabilities {#section-dwass}

<a id="tag-RL1L" data-assertion="theorem" data-title="Dwass's formula for total progeny from one ancestor"></a>
<p>For independent copies $\xi_1,\ldots,\xi_n$ of the offspring variable and each integer $n\geq1$,</p>
<div class="math-display">$$\mathbb P(T=n)=\frac1n\mathbb P\!\left(\sum_{i=1}^n\xi_i=n-1\right).$$</div>
<p>The identity holds on either side of criticality. If survival has positive probability, it describes the finite part of the total-progeny law.</p>
<p><em>Proof.</em> Explore the family tree one individual at a time, placing its children at the end of the queue. Before the queue first empties, its size after $k$ individuals have been explored is $1+S_k$, where $S_0=0$ and $S_k=\sum_{i=1}^k(\xi_i-1)$. The unexplored offspring counts are independent with the original law, so they may be sampled in advance as an infinite independent sequence. Hence $T=n$ exactly when $S_k\geq0$ for $k&lt;n$ and $S_n=-1$.</p>
<p>Fix an integer sequence $a_1,\ldots,a_n$ with $a_i\geq-1$ and sum $-1$, and write $s_k=\sum_{i=1}^ka_i$. Exactly one of its $n$ cyclic starting positions has all its proper partial sums nonnegative. To see this, let $j$ be the first index attaining the minimum of $s_0,\ldots,s_{n-1}$, and start after $j$. Before wrapping around, the proper sums are $s_i-s_j\geq0$. If $j&gt;0$, then $s_j\leq-1$, so the sum at the old endpoint is $-1-s_j\geq0$. After wrapping, a proper sum has the form $-1-s_j+s_i$ with $i&lt;j$; this is nonnegative because $s_i&gt;s_j$ and both are integers. Conversely, nonnegative proper sums for a start after $j$ force $s_i\geq s_j$ for later indices and $s_i&gt;s_j$ for earlier ones. Thus $j$ must be precisely that first minimum.</p>
<p>Apply this observation to $a_i=\xi_i-1$. The joint law is invariant under each cyclic rotation. On the event $S_n=-1$, the sum of the indicators that the $n$ starting positions give a valid queue path is one; outside that event it is zero. Taking expectations, each of the $n$ indicators has expectation $\mathbb P(T=n)$, which proves the formula. This counts starting positions, so no assumption that the rotations are distinct is needed.</p>

<a id="tag-AGPB" data-assertion="corollary" data-title="Exact periodic progeny law for zero-or-two offspring"></a>
<p>If $\mathbb P(\xi=0)=\mathbb P(\xi=2)=1/2$, then for $k\geq0$,</p>
<div class="math-display">$$\mathbb P(T=2k+1)=\frac{1}{k+1}\binom{2k}{k}2^{-(2k+1)},\qquad\mathbb P(T=2k+2)=0.$$</div>
<p>Consequently, along odd $n\to\infty$,</p>
<div class="math-display">$$\mathbb P(T=n)\sim\sqrt{\frac2\pi}\,n^{-3/2},$$</div>
<p>whereas over all integers $n\to\infty$,</p>
<div class="math-display">$$\mathbb P(T\geq n)\sim\sqrt{\frac2\pi}\,n^{-1/2}.$$</div>
<p><em>Proof.</em> A sum of $n$ offspring counts is even, so Dwass's formula vanishes for even $n$. For $n=2k+1$, it requires exactly $k$ of those counts to equal two and gives $(2k+1)^{-1}\binom{2k+1}{k}2^{-(2k+1)}$, which is the displayed Catalan expression. Stirling's formula makes this asymptotic to $1/(2\sqrt\pi\,k^{3/2})$, giving the odd-size equivalent. Critical extinction leaves no mass at infinity. Summing over $k\geq\lceil(n-1)/2\rceil$ and using $\sum_{k\geq K}k^{-3/2}\sim2K^{-1/2}$ gives the tail equivalent.</p>
<p>This calculation resolves the support issue for local probabilities without assuming a local limit theorem. The point-mass equivalent holds only on odd sizes, but the tail equivalent holds on all sizes. The offspring law here differs from the $\operatorname{Binomial}(2,1/2)$ law of the critical <a href="/articles/binary-tree-percolation/">binary-tree percolation cluster</a>, which permits one child and has no such parity restriction.</p>

## Conditioned plane trees and contours {#section-contours}

<a id="tag-NT0R" data-assertion="proposition" data-title="Conditioned plane-tree weights and the geometric contour law"></a>
<p>For a finite rooted ordered tree $t$, let $d_t(v)$ count the children of $v$. A Galton–Watson tree with offspring law $\mu$ has</p>
<div class="math-display">$$\mathbb P(\mathcal T=t)=\prod_{v\in t}\mu(d_t(v)).$$</div>
<p>Conditioning on $T=n$ divides these weights by $\mathbb P(T=n)$, when positive. For $\mu(k)=2^{-k-1}$, the conditioned tree is uniform among ordered trees with $n$ vertices. Its depth-first contour, recording distance from the root while traversing each edge in both directions, is uniform among nonnegative simple-walk bridges of length $2(n-1)$.</p>
<p><em>Proof.</em> Independence gives the product. Since $\sum_v d_t(v)=n-1$, the geometric weight is $2^{-(2n-1)}$, independent of shape. Contours correspond bijectively to nonnegative bridges: an upward step creates the next child; a downward step returns to its parent. Each bridge has the same simple-random-walk probability.</p>
<p>General offspring laws need not give uniform contours. For zero-or-two offspring and $n=3$, only the two-leaf tree is possible, whereas the three-vertex chain is another ordered tree.</p>
<p>A continuum-tree description requires a separate limit theorem. <a href="https://arxiv.org/pdf/math/0511515v1">Le Gall, Theorem 1.15 and §1.6</a>, uses an exponential-moment assumption in its proof and $\mu(1)&gt;0$ to permit conditioning at every size. Neither contour convergence nor diameter scaling is proved here.</p>

## The fixed-point argument without a finite-mean assumption {#section-generating-source}

<p>For this section allow $m=\sum_{k\geq0}kp_k\in[0,\infty]$, where $(p_k)$ is any probability law on the nonnegative integers. The series $\phi(s)=\sum_kp_ks^k$ converges uniformly on $[0,1]$, since each term is bounded by $p_k$. It is therefore continuous there; termwise comparison and convexity give monotonicity and convexity, and $\phi(1)=1$. The iterates from zero increase to a fixed point $q$, and induction bounds every iterate by every fixed point in $[0,1]$. Thus $q$ is the least fixed point, without a moment assumption.</p>
<p>The source proves the criterion in <a href="/tag/BFM4/">BFM4</a> directly. If $m\leq1$ and $p_1\ne1$, then $p_0&gt;0$: otherwise the offspring number is at least one almost surely and has mean at most one, forcing it to equal one. For $0\leq s&lt;1$, Bernoulli's inequality, with its excess at zero retained, gives</p>
<div class="math-display">$$s^k-s\geq-(k-1)(1-s)s+\mathbf1_{\{k=0\}}(1-s)^2.$$</div>
<p>Summing against $p_k$ yields</p>
<div class="math-display">$$\phi(s)-s\geq(1-m)(1-s)s+p_0(1-s)^2&gt;0.$$</div>
<p>Consequently one is the only fixed point. If $p_1=1$, instead, $\phi(s)=s$ and the iterates from zero stay at zero. This is the deterministic critical exception, not a failure of the least-fixed-point characterization.</p>
<p>When $m&gt;1$, choose a finite $N$ with $\sum_{k&lt;N}kp_k&gt;1$ and set</p>
<div class="math-display">$$g(s)=\sum_{k&lt;N}p_k\sum_{i=0}^{k-1}s^i.$$</div>
<p>This polynomial satisfies $g(1)&gt;1$, hence $g(s)&gt;1$ for $s&lt;1$ sufficiently close to one. Nonnegativity of the omitted terms then gives</p>
<div class="math-display">$$1-\phi(s)=\sum_kp_k(1-s^k)\geq(1-s)g(s)&gt;1-s.$$</div>
<p>Thus $\phi(s)&lt;s$. Continuity between zero and this $s$ produces a fixed point below one, so $q&lt;1$. Only a finite truncation of the mean was used; the argument covers $m=\infty$ without differentiating at one.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-analytic/">twenty-three-contract inventory</a> records this analytic argument, including the examples $p_1=1$ with $q=0$ and binomial offspring with parameters $2,3/4$, for which $m=3/2$ and $q=1/9$. The file defines no random process. Its connection to <a href="/tag/8TFY/">8TFY</a> still requires the branching construction and the identity $\mathbb P(Z_n=0)=\phi^{\circ n}(0)$.</p>


## What the Laplace-to-tail argument proves {#section-laplace-tail-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-tails/">new Laplace-tail source</a> implements the analytic step of <a href="/tag/MIFH/">MIFH</a> for any measurable $T\in\mathbb N\cup\{\infty\}$ on a probability space. Its sole asymptotic input is $G(t)/\sqrt t\to a\in(0,\infty)$, where $G(t)=\mathbb E[1-e^{-tT}]$. The branching construction and the transform asymptotic that provide this input remain separate.</p>
<p>The truncation estimate in the source retains the exact tail index:</p>
<div class="math-display">$$G(t)\leq t\sum_{j=1}^m\mathbb P(T\geq j)+\mathbb P(T\geq m+1).$$</div>
<p>It follows by using $1-e^{-tT}\leq tT$ when $T\leq m$, and bounding the deficit by one otherwise. Both cases include the possibility of infinite $T$. Replacing the last tail by the larger probability at $m$ gives the form used in the proof above. The source obtains an upper bound for every $n\geq1$ and a positive lower bound for sufficiently large $n$, using the same choice $t=1/(Ln)$. The upper bound tends to zero and hence also proves $T&lt;\infty$ almost surely; this is a conclusion, not an extra hypothesis.</p>
<p>These estimates give two-sided order $n^{-1/2}$. They do not identify an exact tail constant or the probabilities at individual integers. To witness the asymptotic hypothesis, the source uses the probability generating function $1-\sqrt{1-z}$: its nonnegative coefficients sum to one, and its Laplace deficit is $\sqrt{1-e^{-t}}\sim\sqrt t$. This witness validates the analytic hypotheses without identifying that law with the general offspring model.</p>


## The analytic transform equation {#section-transform-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-transforms/">offspring-transform source</a> proves the analytic part of <a href="/tag/OVG9/">OVG9</a> without constructing the branching process. For a mean-one offspring law, $0\leq x\leq y\leq1$ gives</p>
<div class="math-display">$$0\leq\phi(y)-\phi(x)\leq\mathbb E[\xi](y-x)=y-x.$$</div>
<p>Thus $x\mapsto s\phi(x)-x$ is strictly decreasing when $0\leq s&lt;1$. Its values at zero and one have opposite weak signs, with the value at one strictly negative. Continuity gives exactly one zero $F(s)\in[0,1)$. Comparing this equation at two values of $s$ proves that $F$ is nondecreasing. In the nondegenerate critical case, $\phi(x)&gt;x$ for $x&lt;1$, so for each fixed $x&lt;1$ and $s$ sufficiently close to one, $s\phi(x)&gt;x$ and hence $F(s)&gt;x$. This proves $F(s)\to1$.</p>
<p>The second-order expansion needs no third moment. For each integer $k\geq0$ and $0&lt;u\leq1$,</p>
<div class="math-display">$$0\leq\frac{(1-u)^k-1+ku}{u^2}\leq\frac{k(k-1)}2,$$</div>
<p>and the quotient tends to the upper bound as $u\downarrow0$. The fixed-$k$ limit follows, for example, by trapping $(1-u)^k$ between its quadratic and cubic Taylor polynomials on $[0,1]$. Averaging the displayed quotient uses domination by the integrable second factorial moment, not by the cubic remainder. It yields $\phi(1-u)=1-u+\sigma^2u^2/2+o(u^2)$. Substitution into the root equation now gives the square-root asymptotic exactly as above.</p>
<p>The unique root exists even for the deterministic law $\xi=1$, but then it is zero for every $s&lt;1$. Nondegeneracy is therefore necessary for the convergence to one; positive variance supplies it in OVG9. The source verifies the critical binary example with $\phi(x)=(1+x^2)/2$ and $F(s)=(1-\sqrt{1-s^2})/s$ for $s&gt;0$, with $F(0)=0$. Identifying a selected root with $\mathbb E[s^T]$ still uses the branching decomposition. The source's analytic theorem does not replace that step.</p>


## Uniformity in the generation array {#section-recursion-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-limits/">quadratic-recursion source</a> isolates the analytic parts of <a href="/tag/8WO7/">8WO7</a> and <a href="/tag/AYHV/">AYHV</a>. The expansion of $\psi$ first gives $g(u):=1/\psi(u)-1/u\to a$ as $u\downarrow0$. For a single positive orbit converging to zero, telescoping and arithmetic averaging then give the survival constant. Convergence of that orbit to zero is an input to this analytic theorem.</p>
<p>For the generation array, the bound $0&lt;u_{k,n}\leq u_{0,n}\to0$ controls every summand at once:</p>
<div class="math-display">$$\left|\frac1n\sum_{k=0}^{n-1}g(u_{k,n})-a\right|\leq\sup_{0&lt;u\leq u_{0,n}}|g(u)-a|\longrightarrow0.$$</div>
<p>This yields the stated transform limit for each fixed $\lambda&gt;0$. The source stops at that limit and the normalized expression $1-u_{n,n}/Q_n$; the branching property, extinction, identification of the exponential law and convergence of conditional means are additional steps in the article. No uniformity as $\lambda\to\infty$ is asserted. In the last analytic quotient, the positive limit $nQ_n\to1/a$ itself ensures that $Q_n$ is nonzero eventually.</p>



## The local critical progeny law {#section-critical-local-law}

<a id="tag-NOKH" data-assertion="theorem" data-title="Critical progeny has a local equivalent on its offspring lattice"></a>
<p>Suppose $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Let</p>
<div class="math-display">$$h=\gcd\{k\geq1:\mathbb P(\xi=k)&gt;0\}.$$</div>
<p>For total progeny $T$ from one ancestor,</p>
<div class="math-display">$$\mathbb P(T=n)=0\quad\text{if }n\not\equiv1\pmod h,\qquad
\mathbb P(T=n)\sim\frac{h}{\sqrt{2\pi\sigma^2}}\,n^{-3/2}
\quad\text{as }n\to\infty\text{ through }n\equiv1\pmod h.$$</div>
<p>In particular every sufficiently large admissible size has positive probability. Small admissible sizes may be absent. No third moment, exponential moment, or positive probability of one child is required.</p>
<p><em>Proof.</em> The assumptions force $\mathbb P(\xi=0)&gt;0$: otherwise $\xi\geq1$ almost surely and mean one would make its variance zero. Thus $h$ is the maximal lattice span of the offspring law, with lattice offset zero. Put $S_n=\xi_1+\cdots+\xi_n$ for independent offspring counts. Since $S_n$ is a multiple of $h$, <a href="/tag/RL1L/">Dwass's formula</a> gives the asserted zeros.</p>
<p>Write $\psi(\theta)=\mathbb E e^{i\theta\xi}$ and $\varphi(\theta)=e^{-i\theta}\psi(\theta)$. Centering and the finite second moment give</p>
<div class="math-display">$$\varphi(\theta)=1-\frac{\sigma^2\theta^2}{2}+o(\theta^2)
\qquad(\theta\to0).$$</div>
<p>This expansion needs only a second moment. For $Y=\xi-1$, divide the remainder in the second-order expansion of $e^{i\theta Y}$ by $\theta^2$ and use dominated convergence: it tends to zero pointwise and is bounded by a constant times $Y^2$. It follows that, for some $c,\delta&gt;0$ with $\delta&lt;\pi/h$,</p>
<div class="math-display">$$|\varphi(\theta)|\leq e^{-c\theta^2}\qquad(|\theta|\leq\delta).$$</div>
<p>Moreover $|\psi(\theta)|=1$ only if all phases $e^{ik\theta}$ on the offspring support agree. The atom at zero makes their common value one. By the definition of $h$ and Bézout's identity applied to a finite subset with the same gcd, this happens exactly when $h\theta\in2\pi\mathbb Z$. Continuity therefore gives</p>
<div class="math-display">$$\sup_{\delta\leq|\theta|\leq\pi/h}|\varphi(\theta)|=\rho&lt;1.$$</div>
<p>For $n\equiv1\pmod h$, Fourier inversion for the integer-valued variable $S_n/h$ yields</p>
<div class="math-display">$$\begin{aligned}
\mathbb P(S_n=n-1)
&=\frac{h}{2\pi}\int_{-\pi/h}^{\pi/h}\psi(\theta)^n e^{-i(n-1)\theta}\,d\theta\\
&=\frac{h}{2\pi}\int_{-\pi/h}^{\pi/h}\varphi(\theta)^n e^{i\theta}\,d\theta.
\end{aligned}$$</div>
<p>The portion with $|\theta|\geq\delta$, multiplied by $\sqrt n$, tends to zero by the bound $\rho^n$. In the remaining integral set $t=\sqrt n\,\theta$. For each fixed $t$,</p>
<div class="math-display">$$\varphi(t/\sqrt n)^n e^{it/\sqrt n}\longrightarrow e^{-\sigma^2t^2/2}.$$</div>
<p>After extending the integrand by zero outside $|t|\leq\delta\sqrt n$, its absolute value is bounded by $e^{-ct^2}$. Dominated convergence gives</p>
<div class="math-display">$$\sqrt n\,\mathbb P(S_n=n-1)
\longrightarrow\frac{h}{2\pi}\int_{\mathbb R}e^{-\sigma^2t^2/2}\,dt
=\frac{h}{\sqrt{2\pi\sigma^2}}.$$</div>
<p>Dividing by $n$ in Dwass's formula proves the local equivalent. Its positive constant also proves eventual positivity on the admissible progression.</p>
<p>The span factor is essential. For zero-or-two offspring it gives $h=2$, $\sigma^2=1$, and the constant $\sqrt{2/\pi}$ from AGPB. For $\operatorname{Binomial}(2,1/2)$ offspring, $h=1$ and $\sigma^2=1/2$, so the constant is $1/\sqrt\pi$ on all sufficiently large sizes. A one-child atom is sufficient for span one, but not necessary: the critical law with probabilities $3/5,1/5,1/5$ at $0,2,3$ also has span one, although total size two is impossible.</p>
<p>This supplies the general local theorem with lattice support. The generating-function singularity alone was not used to infer point probabilities. Summing the local equivalent over the progression, whose spacing is $h$, cancels the span factor and recovers the all-integer tail constant $\sqrt{2/(\pi\sigma^2)}$ in <a href="/tag/PVM9/">PVM9</a>; critical extinction leaves no mass at infinity. This is a written proof, not a new compiled correspondence for the transform or tail modules.</p>



## Trees encoded by an excursion {#section-excursion-tree}

<a id="tag-OO12" data-assertion="definition" data-title="Excursion-coded metric tree and its mass measure"></a>
<p>Let $f:[0,1]\to[0,\infty)$ be continuous with $f(0)=f(1)=0$. Put</p>
<div class="math-display">$$m_f(s,t)=\min_{s\wedge t\leq u\leq s\vee t}f(u),\qquad
d_f(s,t)=f(s)+f(t)-2m_f(s,t).$$</div>
<p>Identify $s$ and $t$ when $d_f(s,t)=0$. The resulting compact metric tree is denoted $\mathcal T_f$, with quotient map $\pi_f$, root $\rho_f=\pi_f(0)$, and probability measure $\nu_f=(\pi_f)_*\operatorname{Leb}_{[0,1]}$. If $e$ is a standard Brownian excursion of duration one, we use the Brownian continuum random tree $\mathcal T_{2e}$, with this root and mass measure. The alternative convention $\mathcal T_e$ divides all distances by two and leaves total mass one.</p>
<p>The triangle inequality follows by splitting the interval between three times at the middle time and taking its smaller minimum. Continuity makes the quotient compact. Its root-to-$\pi_f(t)$ segment can be parametrized by height: for $0\leq h\leq f(t)$ take the last $s\leq t$ with $f(s)=h$. The resulting classes have pairwise distance equal to the difference of their heights. For two times $s\leq t$, these segments coincide up to height $m_f(s,t)$ and separate above it, giving a path of length $d_f(s,t)$. At any height $h$, the components of $\{u:f(u)&gt;h\}$ encode the distinct branches above that height. A path leaving one such branch must pass through its height-$h$ attachment point. This forces the displayed path, so the quotient is a real tree. These observations also allow excursions with interior zeros and the zero function.</p>

## Contours, distances and vertex mass {#section-contour-metric-transfer}

<p>For rooted compact metric spaces with probability measures, use the rooted Gromov–Hausdorff–Prokhorov distance $d_{\mathrm{GHP}}^\bullet$: embed both spaces isometrically in a common metric space, take the maximum of their Hausdorff distance, their roots' distance and the Prokhorov distance of their measures, then take the infimum over embeddings. The Prokhorov distance is at most $\varepsilon$ whenever a coupling places all but $\varepsilon$ of its mass on pairs at distance at most $\varepsilon$.</p>
<a id="tag-LHWC" data-assertion="proposition" data-title="Uniform contour approximation controls the rooted metric tree and uniform vertex mass"></a>
<p>For excursions $f,g$ as in <a href="/tag/OO12/">OO12</a>,</p>
<div class="math-display">$$d_{\mathrm{GHP}}^\bullet
\bigl((\mathcal T_f,\rho_f,\nu_f),(\mathcal T_g,\rho_g,\nu_g)\bigr)
\leq 2\|f-g\|_\infty.$$</div>
<p>Let $t$ be an ordered rooted tree with $n\geq2$ vertices, graph distance $d_t$, uniform vertex measure $\mu_t$, and usual unit-speed contour $C_t$ on $[0,2(n-1)]$. Give every edge length $a&gt;0$ and write $c(u)=aC_t(2(n-1)u)$. Then for every such excursion $f$,</p>
<div class="math-display">$$d_{\mathrm{GHP}}^\bullet
\bigl((V(t),a d_t,\rho_t,\mu_t),(\mathcal T_f,\rho_f,\nu_f)\bigr)
\leq a+\frac1n+2\|c-f\|_\infty.$$</div>
<p><em>Proof.</em> Pair $\pi_f(u)$ with $\pi_g(u)$ for every $u$. This is a correspondence covering both spaces and pairing their roots. Since the minima differ by at most $\|f-g\|_\infty$, its distortion is at most $4\|f-g\|_\infty$. A correspondence of distortion at most $2\delta$ can be realized in a common metric space with each paired distance at most $\delta$: use the original metrics on either side and the cross-distance</p>
<div class="math-display">$$D(x,y)=\inf_{(x',y')\in R}
\bigl(d_X(x,x')+\delta+d_Y(y',y)\bigr).$$</div>
<p>For $\delta&gt;0$, the distortion bound verifies the triangle inequalities that cross between the two spaces twice, so neither original metric is shortened. In this embedding the Hausdorff and root distances are at most $\delta$. Coupling the two projections of one uniform time also puts their mass measures within Prokhorov distance $\delta$. Take $\delta&gt;2\|f-g\|_\infty$ and decrease it to that value.</p>
<p>For the second assertion, replace every edge of $t$ by a line segment of length $a$, obtaining its metric realization $\overline t$. During the contour, the minimum height between two visits is the height of their common ancestor. Thus $\mathcal T_c$ is isometric to $\overline t$. Its mass measure $\nu_c$ is normalized length measure: every edge is traversed twice at the same speed.</p>
<p>Uniform length measure is not uniform vertex measure. To compare them, choose a nonroot vertex uniformly, then choose a point uniformly on the edge joining it to its parent. The point has law $\nu_c$ and is within distance $a$ of the chosen vertex. The uniform nonroot measure differs from $\mu_t$ in total variation by exactly $1/n$. Hence their Prokhorov distance in $\overline t$ is at most $a+1/n$. Every point of $\overline t$ is within $a/2$ of a vertex, and the roots agree. Therefore the rooted measured distance from the vertex tree to $(\mathcal T_c,\rho_c,\nu_c)$ is at most $a+1/n$. Combine this with the first assertion and the triangle inequality.</p>

## The conditioned tree as a metric space {#section-conditioned-crt}

<a id="tag-A7TR" data-assertion="theorem" data-title="Finite-variance conditioned Galton–Watson trees converge to the Brownian continuum random tree"></a>
<p>Suppose that $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Let $\mathcal T_n$ have the Galton–Watson tree law conditioned to have $n$ vertices, let $\rho_n$ be its root, and let $\mu_n$ give mass $1/n$ to each vertex. As $n\to\infty$ through sizes for which this conditioning has positive probability,</p>
<div class="math-display">$$
\bigl(V(\mathcal T_n),\tfrac{\sigma}{\sqrt n}d_{\mathcal T_n},\rho_n,\mu_n\bigr)
\xrightarrow{\ d\ }
(\mathcal T_{2e},\rho_{2e},\nu_{2e})
$$</div>
<p>in rooted Gromov–Hausdorff–Prokhorov distance. Writing $H_n$ for the maximum distance from the root and $D_n$ for the diameter, we also have joint convergence</p>
<div class="math-display">$$
\left(\frac{\sigma H_n}{\sqrt n},\frac{\sigma D_n}{\sqrt n}\right)
\xrightarrow{\ d\ }
\left(2\max_{0\leq t\leq1}e(t),\operatorname{diam}(\mathcal T_{2e})\right).
$$</div>
<p><em>Proof using the conditioned-contour invariance theorem.</em> The probabilistic input is the functional convergence</p>
<div class="math-display">$$
\left(\frac{\sigma}{\sqrt n}C_n(2(n-1)t):0\leq t\leq1\right)
\xrightarrow{\ d\ }(2e(t):0\leq t\leq1)
\quad\text{in }C[0,1].
$$</div>
<p>We use <a href="https://www.stat.berkeley.edu/~aldous/Papers/CRT3.pdf">Aldous, <em>The continuum random tree III</em>, Theorem 23, pp. 280–281</a>, with Technical remark 2 for the sublattice case. His contour convention pads the usual traversal by a zero interval at each endpoint. Removing these intervals is a deterministic time change tending uniformly to the identity, so the continuous limiting path is unchanged. This finite-variance invariance theorem is a cited input here; it is not a consequence of the progeny tail estimate or of a simple-walk contour law for general offspring distributions.</p>
<p>Apply <a href="/tag/LHWC/">LHWC</a> to these contours. The coding map is continuous in the uniform norm, and the distance from each coded measured tree to the uniformly weighted vertex tree is at most $\sigma/\sqrt n+1/n$. The continuous mapping theorem and this vanishing deterministic error prove the metric and mass convergence. Height and diameter are continuous under rooted Hausdorff convergence: when the Hausdorff and root errors are at most $\varepsilon$, their changes are at most $2\varepsilon$. On the coded tree they equal $\max f$ and $\max_{s,t}d_f(s,t)$, respectively. This proves the joint limit.</p>
<p>The limit height and diameter are finite and strictly positive almost surely. Consequently, for each $\varepsilon&gt;0$ there are $0&lt;c_\varepsilon&lt;C_\varepsilon&lt;\infty$ such that, for every sufficiently large admissible $n$,</p>
<div class="math-display">$$
\mathbb P\!\left(c_\varepsilon\sqrt n\leq H_n\leq D_n
\leq C_\varepsilon\sqrt n\right)\geq1-\varepsilon.
$$</div>
<p>Choose upper and lower continuity points of the positive finite limiting variables and use the joint convergence. This is the precise typical-diameter statement needed for the continuum-tree picture. It does not assert convergence of unbounded moments.</p>
<p>The support restriction is substantive. By <a href="/tag/NOKH/">NOKH</a>, if $h=\gcd\{k\geq1:\mathbb P(\xi=k)&gt;0\}$, for all sufficiently large $n$, the conditioning has positive probability exactly when $n=1\pmod h$. The zero-or-two law therefore uses odd $n$; there is no additional factor $h$ in the metric normalization. For geometric offspring $\mathbb P(\xi=k)=2^{-k-1}$, <a href="/tag/NT0R/">NT0R</a> identifies the conditioned law with uniform ordered trees and $\sigma^2=2$. Equivalently their distances scaled by $(2n)^{-1/2}$ converge to $\mathcal T_e$.</p>
<p>This extends the earlier contour discussion by supplying the metric and mass deduction from an explicitly cited invariance theorem. <a href="https://arxiv.org/pdf/math/0511515v1">Le Gall's Theorem 1.15</a> presents a shorter proof with an extra moment assumption; that proof restriction is not required for the theorem used here. The normalization $\mathcal T_{2e}$ agrees with the separate <a href="/tag/45EB/">reduced-tree mass-mixture calculation</a>. The present limit concerns a branching tree conditioned on total size; a Euclidean percolation scaling limit needs additional arguments.</p>
