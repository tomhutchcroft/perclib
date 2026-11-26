---
{
  "id": "integrated-lower-tails",
  "title": "Integrated lower tails from moment bounds",
  "subtitle": "Choosing the susceptibility scale before truncating",
  "kind": "method",
  "category": "Methods",
  "summary": "A first/second-moment estimate retains a fixed fraction of the mean below a suitable cutoff. A continuous unbounded family of means and a cubic moment bound then give a square-root lower bound at a dominating endpoint law.",
  "context": [
    "Nonnegative random variables with finite positive first moment and finite second moment.",
    "The family theorem assumes a continuous unbounded mean and stochastic domination by an endpoint variable.",
    "Percolation sharpness, moment bounds and parameter continuity are separate inputs to that application."
  ],
  "related": [
    "susceptibility",
    "sharpness",
    "universal-tightness",
    "cutoff-families"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "perclib-size-bias-truncation",
    "perclib-discrete-layer-cake",
    "perclib-tail-comparison",
    "perclib-train10-layercake",
    "perclib-train10-paleyzygmund",
    "hutchcroft-lrp-3"
  ],
  "aliases": [
    "integrated lower tail",
    "Aizenman-Barsky",
    "truncated mean",
    "moment ratio",
    "critical volume tail"
  ],
  "prototypeUses": []
}
---

## Retaining part of the mean {#section-truncation}

<a id="tag-LLGA" data-assertion="proposition" data-title="Truncated mean bound at the second-to-first moment scale"></a><p>Let $X\geq0$ have $\mu=\mathbb E X\in(0,\infty)$ and $\nu=\mathbb E X^2&lt;\infty$. For every $\lambda&gt;1$,</p><div class="math-display">$$\mathbb E\!\left[X\mathbf1_{\{X\leq\lambda\nu/\mu\}}\right]\geq(1-\lambda^{-1})\mu,\qquad \mathbb E[X\wedge N]\geq(1-\lambda^{-1})\mu\quad\text{if }N\geq\lambda\nu/\mu.$$</div><p><em>Proof.</em> With $L=\lambda\nu/\mu&gt;0$, the pointwise bound $X\mathbf1_{\{X&gt;L\}}\leq X^2/L$ gives</p><div class="math-display">$$\mathbb E[X\mathbf1_{\{X&gt;L\}}]\leq\frac\nu L=\frac\mu\lambda.$$</div><p>Subtract this from $\mathbb E X$. For $N\geq L$, $X\wedge N\geq X\mathbf1_{\{X\leq L\}}$, proving the second assertion.</p><p>The ratio $\nu/\mu$ is the mean under volume bias, but this proof needs only the displayed moment estimate. It bounds the mass retained by truncation; it does not say that $X$ is usually close to its mean.</p>

## Interpolating to an endpoint law {#section-family}

<a id="tag-F75G" data-assertion="theorem" data-title="Conditional integrated square-root lower bound from cubic moments"></a><p>Let $I=[t_0,t_c)$ be a nonempty real interval, allowing $t_c=\infty$. For $t\in I$, let $X_t\geq0$ satisfy</p><div class="math-display">$$0&lt;\mu(t)=\mathbb E X_t&lt;\infty,\qquad \mathbb E X_t^2\leq C\mu(t)^3$$</div><p>for a fixed $C&gt;0$. Suppose $\mu$ is continuous and unbounded on $I$, and suppose a nonnegative extended random variable $X_*$ stochastically dominates every $X_t$. Then, for every real $N\geq2C\mu(t_0)^2$,</p><div class="math-display">$$\mathbb E[X_*\wedge N]\geq\frac1{2\sqrt{2C}}\sqrt N.$$</div><p>If $X_*$ is integer-valued, allowing infinity, this gives for every integer $N$ in the same range</p><div class="math-display">$$\sum_{n=1}^N\mathbb P(X_*\geq n)\geq\frac1{2\sqrt{2C}}\sqrt N.$$</div><p><em>Proof.</em> Continuity and unboundedness allow a choice of $t\in I$ with $\mu(t)=\sqrt{N/(2C)}$: take a parameter with mean above the target and apply the intermediate value theorem between it and $t_0$. At this parameter,</p><div class="math-display">$$\frac{2\mathbb E X_t^2}{\mu(t)}\leq2C\mu(t)^2=N.$$</div><p>The truncation bound with $\lambda=2$ gives $\mathbb E[X_t\wedge N]\geq\mu(t)/2$. Stochastic domination gives $\mathbb E[X_*\wedge N]\geq\mathbb E[X_t\wedge N]$, proving the first claim. For integer-valued $X_*$, apply the <a href="/tag/CSY8/">tail-sum identity</a> to $X_*\wedge N$.</p><p>Only continuity of the first moment was used. There is no assumption that the second moment, or its ratio to the first moment, varies continuously. Unboundedness also need not be monotone for the intermediate-value argument, although percolation couplings normally provide monotonicity.</p>

## The percolation application and its inputs {#section-percolation}

<p>For a root cluster below a critical parameter, take $X_t=|K_o|$ under the parameter-$t$ law and $X_*$ to be its critical-law counterpart. A monotone coupling supplies endpoint domination. To apply the theorem with $C=1$, one must also establish finite subcritical susceptibility, continuity and unboundedness of that susceptibility, and the tree-graph second-moment bound</p><div class="math-display">$$\mathbb E_t|K_o|^2\leq\chi(t)^3.$$</div><p>The abstract theorem then gives the integrated lower bound with constant $1/(2\sqrt2)$. It does not establish those inputs, choose the correct critical parameter for a model, or show that the endpoint law exists in a given parametrization. In particular, finiteness of susceptibility at each subcritical parameter alone does not supply its unboundedness or continuity.</p><p>The same truncation estimate can be combined with the moment-ratio scale. The argument here instead chooses the susceptibility scale directly, so it avoids an additional continuity claim about that ratio. This is a conditional formulation of the proof mechanism, rather than an unconditional assertion for every transitive weighted graph.</p><p>The conclusion concerns a sum of tail probabilities. It should not be reported as a pointwise lower bound $\mathbb P(X_*\geq N)\geq cN^{-1/2}$: the truncation estimate and interpolation argument do not prove that statement. Nor is $\mathbb E[X_*\wedge N]$ the susceptibility with the infinite-cluster contribution deleted; it retains the value $N$ on $\{X_*=\infty\}$.</p>

## Critical integrated tails and a bounded field range {#section-critical-field}

<a id="tag-36PN" data-assertion="theorem" data-title="Universal integrated critical tail and saturated square-root field lower bound"></a>
<p>Consider independent bonds on a nonempty countable vertex set, with symmetric finite nonnegative off-diagonal weights preserved by a transitive group and probabilities $1-e^{-\beta J(x,y)}$. Assume $0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty$ and $\beta_c&lt;\infty$. At criticality write $T=|K_o|$, allowing $T=\infty$, and $M(h)=\mathbb E_{\beta_c}[1-e^{-hT}]$ for $h&gt;0$. Then</p>
<div class="math-display">$$\mathbb E_{\beta_c}[T\wedge N]\geq\frac{\sqrt N}{2\sqrt2}\qquad(N\geq1),$$</div>
<p>and, for every $h&gt;0$,</p>
<div class="math-display">$$M(h)\geq\frac{1-e^{-1}}{2\sqrt2}\min\{\sqrt h,1\}.$$</div>
<p><em>Proof.</em> The row-sum bound gives $\beta_c\geq1/L&gt;0$. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness proof</a> gives finite susceptibility below $\beta_c$, and <a href="/tag/5LNL/">right-openness and endpoint divergence</a> give $\chi_\beta\uparrow\infty$ as $\beta\uparrow\beta_c$. Susceptibility is continuous on $[0,\beta_c)$: the quantitative right-openness estimate gives right-continuity, while monotone coupling and finite path witnesses give left-continuity. At zero, $\chi_0=1$.</p>
<p>Transitivity and the <a href="/tag/Y84V/">tree-graph bound</a> give $\mathbb E_\beta|K_o|^2\leq\chi_\beta^3$ below criticality. The critical cluster volume stochastically dominates all these subcritical volumes. Apply <a href="/tag/F75G/">the interpolation theorem</a> with $t_0=0$ and cubic-moment constant one. It gives the first bound for $N\geq2$. For $1\leq N&lt;2$, use $T\geq1$.</p>
<p>Concavity on $[0,1]$ and monotonicity afterwards give $1-e^{-t}\geq(1-e^{-1})\min\{t,1\}$ for $t\geq0$. Thus for $0&lt;h\leq1$, including the infinite-cluster contribution,</p>
<div class="math-display">$$M(h)\geq(1-e^{-1})h\,\mathbb E_{\beta_c}[T\wedge h^{-1}]\geq\frac{1-e^{-1}}{2\sqrt2}\sqrt h.$$</div>
<p>For $h\geq1$, monotonicity gives $M(h)\geq M(1)$, completing the proof.</p>
<p>This supplies the percolation inputs for the stated countable transitive summable model with finite critical intensity. The integrated bound is not, by itself, a pointwise lower bound on $\mathbb P_{\beta_c}(T\geq N)$, and it does not imply $T&lt;\infty$ almost surely.</p>
<p>The field conclusion gives a small-field form of <a href="https://arxiv.org/pdf/1502.03050v3#page=5">Proposition 1.3 of arXiv:1502.03050v3</a> under explicit hypotheses. Its printed all-positive-field square-root bound cannot hold literally, since $M(h)\leq1$. Saturation makes the displayed conclusion valid for every positive field. This proof uses moment interpolation; it does not establish the source's separate parameter-derivative inequality.</p>


## Recovering a pointwise lower bound {#section-pointwise}

<a id="tag-MBV2" data-assertion="proposition" data-title="Pointwise square-root lower tail from integrated lower and pointwise upper bounds"></a>
<p>Let $(p_n)_{n\geq1}$ be a nonnegative nonincreasing sequence. Suppose that for constants $c,C&gt;0$ and an integer $N_0\geq1$,</p>
<div class="math-display">$$\sum_{k=1}^N p_k\geq c\sqrt N\quad(N\geq N_0),\qquad p_n\leq Cn^{-1/2}\quad(n\geq1).$$</div>
<p>Choose an integer $A\geq2$ such that $c\sqrt A\geq4C$. Then</p>
<div class="math-display">$$p_n\geq\frac{c}{2\sqrt A}\,n^{-1/2}\qquad(n\geq N_0).$$</div>
<p><em>Proof.</em> Apply the integrated bound at $An$. The upper bound controls the first $n$ terms, while monotonicity controls all later terms by $p_n$:</p>
<div class="math-display">$$c\sqrt{An}\leq\sum_{k=1}^{An}p_k\leq C\sum_{k=1}^{n}k^{-1/2}+(A-1)np_n\leq2C\sqrt n+Anp_n.$$</div>
<p>By the choice of $A$, the first term on the right is at most $c\sqrt{An}/2$. Subtract it and divide by $An$.</p>
<p>An eventual pointwise upper bound suffices: increase $C$ to cover the finitely many initial terms. The upper bound is essential to this argument because it prevents the integrated lower bound from being supplied entirely by smaller cluster sizes. No regular variation or differentiability of the tail is used.</p>

## Susceptibility and critical-tail equivalence {#section-equivalence}

<a id="tag-UPMK" data-assertion="theorem" data-title="Equivalence of mean-field susceptibility and endpoint cluster tails"></a>
<p>Consider independent bonds on a nonempty countable vertex set with symmetric finite weights $J(u,v)\geq0$ and probabilities $1-e^{-\beta J(u,v)}$. Suppose a transitive group of vertex permutations preserves the weights, and</p>
<div class="math-display">$$M=\sum_{v\ne o}J(o,v)\in(0,\infty).$$</div>
<p>Let $0\leq a&lt;b&lt;\infty$, with $b&gt;0$, and assume $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$ but $\chi(b)=\infty$. Then the following statements are equivalent:</p>
<div class="math-display">$$\chi(\beta)\asymp(b-\beta)^{-1}\quad\text{as }\beta\uparrow b;\qquad \mathbb P_b(|K_o|\geq n)\asymp n^{-1/2}\quad\text{as }n\to\infty.$$</div>
<p>Here $\asymp$ means upper and lower bounds by fixed positive multiples in the indicated limit. In either case there is no infinite cluster at intensity $b$. The endpoint assumptions are explicit; this theorem does not identify $b$ with a percolation threshold.</p>
<p><em>Proof.</em> The <a href="/tag/MXGM/">susceptibility derivative and endpoint argument</a> gives continuity of $\chi$ on $(a,b)$, divergence as $\beta\uparrow b$, and</p>
<div class="math-display">$$\chi(\beta)\geq\frac1{M(b-\beta)}\qquad(a&lt;\beta&lt;b).$$</div>
<p>Choose $\beta_0\in(a,b)$. The <a href="/tag/Y84V/">tree-graph bound</a> gives $\mathbb E_\beta|K_o|^2\leq\chi(\beta)^3$ on $[\beta_0,b)$. Monotone coupling makes the endpoint cluster size dominate every earlier one. Thus <a href="/tag/F75G/">interpolation to an endpoint law</a> applies with cubic-moment constant one, giving</p>
<div class="math-display">$$\sum_{k=1}^N\mathbb P_b(|K_o|\geq k)\geq\frac1{2\sqrt2}\sqrt N$$</div>
<p>for all sufficiently large $N$.</p>
<p>Now suppose the susceptibility estimate holds. Its upper bound and the <a href="/tag/QS3L/">entropy comparison corollary</a>, with logarithmic exponent zero, give $\mathbb P_b(|K_o|\geq n)\leq Cn^{-1/2}$ for large $n$. Increase $C$ to cover all $n\geq1$. The preceding proposition upgrades the integrated lower bound to a matching pointwise lower bound. The upper bound tends to zero, so the endpoint cluster is almost surely finite.</p>
<p>Conversely, a square-root endpoint tail upper bound is uniform in the root by transitivity. The <a href="/tag/1EJP/">tail-to-susceptibility theorem</a> gives $\chi(\beta)\leq C'/(b-\beta)$ for $0&lt;\beta&lt;b$. Combine this with the susceptibility lower bound above. In fact this direction only needs the endpoint upper tail, not its matching lower bound.</p>
<p>This proves the susceptibility/critical-tail part of the mean-field equivalences, including a pointwise-upgrade argument. The <a href="#section-four-conditions">four-condition theorem below</a> adds the derivative and second-moment implications, retaining the same endpoint hypotheses.</p>

## The four mean-field conditions {#section-four-conditions}

<a id="tag-9PE0" data-assertion="theorem" data-title="Four equivalent mean-field conditions under explicit endpoint hypotheses"></a>
<p>Under the model and endpoint hypotheses of <a href="/tag/UPMK/">the preceding equivalence theorem</a>, the following four conditions are equivalent:</p>
<div class="math-display">$$\begin{aligned}
\chi(\beta)&\asymp(b-\beta)^{-1}&&\text{as }\beta\uparrow b,\\
\mathbb P_b(|K_o|\geq n)&\asymp n^{-1/2}&&\text{as }n\to\infty,\\
\chi'(\beta)&\asymp\chi(\beta)^2&&\text{for almost every }\beta\text{ sufficiently close to }b\text{ from below},\\
\mathbb E_\beta|K_o|^2&\asymp\chi(\beta)^3&&\text{as }\beta\uparrow b.
\end{aligned}$$</div>
<p>The derivative condition means that fixed positive comparison constants work off a single null set in an interval $(b-\varepsilon_0,b)$. The other parameter-dependent conditions are pointwise on such an interval.</p>
<p><em>Proof.</em> The first two conditions are equivalent by the preceding theorem. The susceptibility condition gives the endpoint lower tail, and <a href="/tag/LZCK/">entropy comparison at the cutoff scale</a> then gives $\mathbb E_\beta|K_o|^2\geq\kappa\chi(\beta)^3$ near $b$ for some $\kappa&gt;0$. The tree-graph bound supplies the opposite inequality. This proves the first condition implies the fourth.</p>
<p>Conversely, suppose the fourth holds. Since $\chi(\beta)\to\infty$ as $\beta\uparrow b$, eventually $\chi\geq4/(c_0\kappa)$. The <a href="/tag/Z9K8/">summed tail derivative bound</a> gives</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{c_0\kappa}{8\beta}\chi(\beta)^2\geq\frac{c_0\kappa}{8b}\chi(\beta)^2$$</div>
<p>almost everywhere sufficiently close to $b$. The universal upper derivative bound $\chi'\leq M\chi^2$ proves the third condition.</p>
<p>Finally, suppose the third condition holds, with lower constant $d&gt;0$. Local absolute continuity of $1/\chi$ gives $(1/\chi)'\leq-d$ almost everywhere near $b$. Integrate from $\beta$ to $t&lt;b$, then let $t\uparrow b$, using $\chi(t)\to\infty$. This yields $1/\chi(\beta)\geq d(b-\beta)$, hence</p>
<div class="math-display">$$\chi(\beta)\leq\frac1{d(b-\beta)}.$$</div>
<p>The universal susceptibility lower bound supplies the reverse estimate and proves the first condition. These implications close the cycle.</p>
<p>This establishes the four-condition mechanism. It assumes finite susceptibility below $b$, divergence at $b$, and a finite positive weight row, and gives derivatives their almost-everywhere meaning. Identifying $b$ with the critical parameter of a particular model still requires the corresponding endpoint and sharpness results. The earlier <a href="/tag/4GNM/">exploration-score inequality</a> gives an additional direct route from the derivative condition to the second-moment lower bound.</p>

## Truncation with extended thresholds {#section-truncation-source}

<p>The source proves a version of <a href="/tag/LLGA/">LLGA</a> for an arbitrary measure and an extended nonnegative variable. It requires only $\mu=\int X\,dP&lt;\infty$, allowing $\mu=0$, $\nu=\int X^2\,dP=\infty$, and extended thresholds. The case $\mu=0$ is immediate. For $\mu&gt;0$, split the finite first moment as</p>
<div class="math-display">$$A=\int_{\{X\leq t\}}X\,dP,\qquad B=\int_{\{X&gt;t\}}X\,dP,\qquad A+B=\mu.$$</div>
<p>The elementary estimate $tB\leq\nu$, together with $t\geq\lambda\nu/\mu$ and $\lambda&gt;1$, gives $\lambda B\leq\mu$. The source handles $t=\infty$ first, when $B=0$. For finite $t$, the hypotheses force the factors needed for cancellation to be positive and finite. Subtraction from the finite quantity $\mu$ then gives $A\geq(1-\lambda^{-1})\mu$. The minimum truncation follows from $X\mathbf1_{\{X\leq t\}}\leq X\wedge t$.</p>
<p>If $\mu&gt;0$ and $\nu=\infty$, the threshold condition forces $t=\infty$; it gives no finite cutoff. Likewise, allowing $\lambda=\infty$ merely includes the full-mean endpoint. The finite positive-mean, finite-second-moment statement above is the useful form for the interpolation argument. These truncation contracts neither supply a continuous parameter family nor prove the critical lower-tail conclusion without its other hypotheses.</p>


## Discrete moments and tail sums {#section-discrete-moments}

<p>The new discrete layer-cake source extends the <a href="/tag/CSY8/">tail-sum identity</a> used in F75G to every positive integer moment. If $X$ is measurable with values in $\mathbb N\cup\{\infty\}$ and $k\geq1$, then, for any measure $\mu$,</p>
<div class="math-display">$$\int X^k\,d\mu
=\sum_{j=0}^{\infty}\bigl((j+1)^k-j^k\bigr)\,\mu(X\geq j+1).$$</div>
<p>Indeed, at each point the truncated power is the telescoping sum</p>
<div class="math-display">$$(X\wedge n)^k
=\sum_{j=0}^{n-1}\bigl((j+1)^k-j^k\bigr)\mathbf1_{\{X\geq j+1\}}.$$</div>
<p>Integrate this finite sum and let $n\to\infty$. All terms are nonnegative, so monotone convergence applies even when the moment is infinite. At $X=\infty$, the truncated value is $n^k$; no infinite value is discarded. The restriction $k\geq1$ is essential for this formula: when $k=0$ all the successive differences vanish, whereas the zeroth moment need not vanish.</p>
<p>The same <a href="/coverage/sources/perclib-3978a2f-tails/">source inventory</a> records the sequence proof of <a href="/tag/MBV2/">MBV2</a>. It uses only the stated integrated lower bound, pointwise upper bound and monotonicity from index one. In particular, the integer multiplier $A$ and the factor $2\sqrt A$ are retained. The source also permits zero constants and the zero sequence, in which case the conclusion is simply zero. A positive lower-tail estimate still requires the positive constant in the statement above.</p>


## Real exponents in the tail integral {#section-real-layer-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-foundations/">real-moment layer-cake source</a> extends the integer-power identity above to every real $p&gt;0$. For a measurable $T$ with values in $\mathbb N\cup\{\infty\}$ and any measure $\mu$,</p>
<div class="math-display">$$\int T^p\,d\mu=\sum_{n\geq0}\bigl((n+1)^p-n^p\bigr)\mu(T\geq n+1).$$</div>
<p>The coefficients are nonnegative. The pointwise series telescopes at each finite value of $T$ and diverges at infinity; Tonelli then gives the identity without a moment or finite-measure assumption. Truncation at an integer $N$ gives the finite first-moment sum through threshold $N$, including the empty sum when $N=0$.</p>
<p>For a measurable nonnegative real variable $X$ and $t\geq0$, the same source gives</p>
<div class="math-display">$$\int X\mathbf1_{\{X&gt;t\}}\,d\mu=t\,\mu(X&gt;t)+\int_t^\infty\mu(X&gt;s)\,ds.$$</div>
<p>The boundary term belongs to the truncated moment. By contrast, the integral of $X\wedge t$ is the tail integral from zero to $t$. Keeping these quantities separate is necessary in the moment-truncation arguments.</p>

## The second-moment probability estimate {#section-second-moment-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-foundations/">Paley–Zygmund source</a> complements the retained-mean estimate with a probability bound. Write $m=\mathbb E X&lt;\infty$ for a measurable nonnegative variable on a probability space and set $A=\{X&gt;\theta m\}$, where $0\leq\theta&lt;1$. Splitting the expectation over $A$ and its complement gives $\mathbb E[X\mathbf1_A]\geq(1-\theta)m$. Cauchy–Schwarz therefore yields</p>
<div class="math-display">$$(1-\theta)^2m^2\leq\mathbb P(A)\,\mathbb E X^2.$$</div>
<p>The multiplicative form allows an infinite second moment. Division gives a useful lower probability bound when that moment is positive and finite. At $\theta=0$ the event is $X&gt;0$; the finite-mean assumption remains in the source theorem. Its underlying Cauchy–Schwarz inequality on a measurable event holds for arbitrary measures and extended nonnegative integrals.</p>
<p>For a root cluster in a countable independent-bond model, a uniform susceptibility bound $\chi(x)\leq M&lt;\infty$ gives $\mathbb E|K_o|^2\leq\chi(o)M^2$ by the <a href="/tag/Y84V/">tree-graph estimate</a>. Since $1\leq\chi(o)&lt;\infty$, cancellation gives</p>
<div class="math-display">$$(1-\theta)^2\chi(o)\leq\mathbb P\bigl(|K_o|&gt;\theta\chi(o)\bigr)M^2.$$</div>
<p>This conclusion needs no transitivity. It concerns one fixed law and does not supply the continuous, unbounded family of means used in <a href="/tag/F75G/">the endpoint interpolation argument</a>.</p>


## A cap at an arbitrary intensity {#section-offcritical-cap}

<a id="tag-XU1Y" data-assertion="theorem" data-title="Universal capped cluster mean at finite or infinite susceptibility"></a>
<p>Let a countable independent intensity model be invariant under a transitive group action, with symmetric nonnegative finite weights and finite off-diagonal weight row. For every finite $\beta\geq0$ and real $m\geq1$,</p>
<div class="math-display">$$\mathbb E_\beta\min\{|K_o|,m\}\geq\frac12\min\left\{\chi_\beta,\sqrt{m/2}\right\}.$$</div>
<p>The assertion allows $\chi_\beta=\infty$. The cap is always a finite random variable.</p>
<p><em>Proof.</em> If $1\leq m&lt;2$, the cluster contains its root and the left side is at least one, which suffices. Suppose $m\geq2$ and write $t=\sqrt{m/2}\geq1$. At any parameter $s$ with finite susceptibility, the <a href="/tag/Y84V/">tree-graph inequality</a> gives $\mathbb E_s|K_o|^2\leq\chi_s^3$. The <a href="/tag/LLGA/">truncated-mean bound</a> therefore implies</p>
<div class="math-display">$$\mathbb E_s\min\{|K_o|,2\chi_s^2\}\geq\chi_s/2.$$</div>
<p>If $\chi_\beta\leq t$, apply this directly at $s=\beta$ and increase the cap to $m$. Otherwise choose $s\leq\beta$ with $\chi_s=t$. Here is the justification even when $\chi_\beta$ is infinite. If the weight row is zero, all clusters are singletons and there is nothing to prove. For a positive row, <a href="/tag/5LNL/">finite susceptibility is right-open and right-continuous</a>. Finite path witnesses and monotone convergence give left-continuity at every finite-susceptibility parameter. Thus susceptibility is continuous on its interval of finiteness, starting at $\chi_0=1$; if that interval has a finite endpoint, susceptibility tends to infinity there. The intermediate value theorem supplies the required $s$, including $s=0$ when $t=1$. Monotonicity in intensity and the last display now give $\mathbb E_\beta\min\{|K_o|,m\}\geq t/2$.</p>
<p>This proves Proposition III.3.7 with the finite-row convention and the infinite-susceptibility case explicit. No critical-tail asymptotic, finite critical parameter, or continuity of the second moment is needed.</p>



## Choosing the moment-ratio scale {#section-analytic-ratio-interpolation}

<a id="tag-7GS6" data-assertion="corollary" data-title="Subcritical analytic moments justify moment-ratio interpolation at every scale"></a>
<p>Consider the countable transitive intensity model with $0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty$. Let</p>
<div class="math-display">$$b_\chi=\sup\{\beta\geq0:\chi(\beta)&lt;\infty\}&lt;\infty,\qquad
\zeta(\beta)=\frac{\mathbb E_\beta|K_o|^2}{\mathbb E_\beta|K_o|}\quad(0\leq\beta&lt;b_\chi).$$</div>
<p>The function $\zeta$ is real analytic on $[0,b_\chi)$, with an extension across zero, $\zeta(0)=1$, and $\zeta(\beta)\to\infty$ as $\beta\uparrow b_\chi$. For every real $N\geq2$, some $\beta\in[0,b_\chi)$ satisfies $2\zeta(\beta)=N$. Consequently,</p>
<div class="math-display">$$\mathbb E_{b_\chi}[|K_o|\wedge N]\geq\frac{\sqrt N}{2\sqrt2}\qquad(N\geq2).$$</div>
<p><em>Proof.</em> By <a href="/tag/5LNL/">right-openness and threshold divergence</a>, susceptibility is finite at every $\beta&lt;b_\chi$ and tends to infinity at the endpoint. Transitivity makes it a uniform bound over roots. Hence <a href="/tag/VYTG/">the analytic moment theorem</a> applies at each such parameter. The first moment is at least one, so the second moment divided by the first is real analytic. At zero every cluster is a singleton, giving $\zeta(0)=1$. Jensen's inequality gives $\zeta(\beta)\geq\chi(\beta)$, and therefore divergence at $b_\chi$.</p>
<p>For $N&gt;2$, choose $b&lt;b_\chi$ with $\zeta(b)&gt;N/2$ and apply the intermediate value theorem on $[0,b]$. For $N=2$, take $\beta=0$. No monotonicity of the ratio is needed. At the selected parameter, <a href="/tag/LLGA/">the moment-ratio truncation bound</a> and endpoint stochastic domination give</p>
<div class="math-display">$$\mathbb E_{b_\chi}[|K_o|\wedge N]\geq\frac12\chi(\beta).
$$</div>
<p>The <a href="/tag/Y84V/">tree-graph second-moment bound</a> gives $\zeta(\beta)\leq\chi(\beta)^2$. Thus $\chi(\beta)\geq\sqrt{N/2}$, as required.</p>
<p>The <a href="/tag/RDF0/">finite-set characterization</a> identifies $b_\chi$ with the percolation threshold under these hypotheses. This completes the moment-ratio route. The earlier susceptibility-scale proof remains valid without the analytic expansion. Infinite critical clusters are allowed in the capped expectation, and the conclusion remains an integrated tail bound.</p>


## Pointwise lower tails with a logarithmic loss {#section-logarithmic-pointwise}

<a id="tag-QW2L" data-assertion="proposition" data-title="An integrated square-root lower bound and a logarithmic upper bound give a reciprocal logarithmic lower bound"></a>
<p>Let $(p_n)_{n\geq1}$ be nonnegative and nonincreasing. Suppose that for some $c,C&gt;0$, $a\geq0$ and integer $N_0\geq1$,</p>
<div class="math-display">$$\sum_{j=1}^N p_j\geq c\sqrt N\quad(N\geq N_0),\qquad
p_n\leq C n^{-1/2}\log^a(e n)\quad(n\geq1).$$</div>
<p>Then $p_n\geq c' n^{-1/2}\log^{-a}(e n)$ for $n\geq N_0$, with $c'&gt;0$ depending only on $c,C,a$.</p>
<p><em>Proof.</em> Choose $A\geq2$ with $c\sqrt A\geq4C$, and for a fixed $n\geq N_0$ put $N=\lceil A n\log^{2a}(e n)\rceil$. Monotonicity and the upper bound give</p>
<div class="math-display">$$c\sqrt N\leq\sum_{j=1}^N p_j
\leq2C\sqrt n\log^a(e n)+(N-n)p_n
\leq\frac c2\sqrt N+N p_n.$$</div>
<p>Here $\sum_{j=1}^n j^{-1/2}\leq2\sqrt n$, and the choice of $A$ gives the last inequality. Thus $p_n\geq c/(2\sqrt N)$. Since $N\leq(A+1)n\log^{2a}(e n)$, the desired constant is $c'=c/(2\sqrt{A+1})$. An eventual upper bound suffices after increasing $C$ to cover its finitely many exceptional terms.</p>
<p>The integrated estimate alone does not supply this pointwise conclusion. The logarithmic upper bound controls the mass below $n$; the enlarged scale $N$ forces the remaining mass to come from the tail.</p>
