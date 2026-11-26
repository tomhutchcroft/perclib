---
{
  "id": "open-degree-laws",
  "title": "Open degrees and isolation",
  "subtitle": "First moments, incident products and finite-count concentration",
  "kind": "theorem",
  "category": "General theory",
  "summary": "The expected open degree is an off-diagonal probability row. Independent bonds give generating functions, isolation and degree-finiteness criteria, as well as binomial laws and concentration for finite counts.",
  "context": ["Independent pair coordinates with probabilities $q_{xy}=q_{yx}\\in[0,1]$; the associated simple graph discards loops.", "Finite-coordinate identities allow any vertex set. Full degree and isolation statements use countably many vertices.", "Counts and nonnegative expectations may be infinite."],
  "related": ["product-model", "finite-transcripts", "displacement-kernels", "boundary-laws", "susceptibility"],
  "sourceIds": ["perclib-degree", "perclib-degree-generating", "perclib-first-moment", "perclib-concentration", "perclib-infinite-degree"],
  "aliases": ["open degree", "degree distribution", "probability generating function", "isolated vertex", "Poisson-binomial", "expected boundary size", "binomial count", "Hoeffding inequality", "sub-Gaussian count"],
  "prototypeUses": ["product-model", "finite-transcripts"]
}
---

## Degrees and pair coordinates {#section-counts}

<a id="tag-PMHN" data-assertion="definition" data-title="Open degree and incident-coordinate counts"></a>
<p>The open degree of a vertex $v$ is</p>
<div class="math-display">$$D_v=\bigl|\{w\ne v:\{v,w\}\text{ is open}\}\bigr|\in\mathbb N\cup\{\infty\}.$$</div>
<p>For a finite set of vertices $F$, let $N_F(v)$ count the open pair coordinates $\{v,w\}$ with $w\in F$. Thus $N_F(v)$ counts a possible diagonal coordinate when $v\in F$; the degree inside $F$ is $N_{F\setminus\{v\}}(v)$. Distinct choices of $w$ give distinct unordered pair coordinates.</p>
<p>For $w\ne v$, adjacency is precisely the event that $\{v,w\}$ is open, a measurable cylinder of probability $q_{vw}$. Self-adjacency is impossible even if the diagonal coordinate has probability one.</p>

## First moments {#section-first-moments}

<a id="tag-SZLN" data-assertion="theorem" data-title="The expected open degree and its first-moment bound"></a>
<p>On a countable vertex set, $D_v$ is measurable and</p>
<div class="math-display">$$\mathbb E_q D_v=R_v,\qquad R_v=\sum_{w\ne v}q_{vw}\in[0,\infty].$$</div>
<p>For every integer $k\geq1$, $k\mathbb P_q(D_v\geq k)\leq R_v$. In particular, a finite row $R_v$ implies $D_v&lt;\infty$ almost surely.</p>
<p><em>Proof.</em> The degree is the sum of the measurable adjacency indicators. Countability makes this a measurable extended nonnegative sum, and Tonelli gives the expectation identity. Integrating $k\mathbf1_{\{D_v\geq k\}}\leq D_v$ gives the bound. If $R_v&lt;\infty$, letting $k\to\infty$ excludes infinite degree.</p>

<a id="tag-TOTD" data-assertion="proposition" data-title="Expected counts of finite pair sets and outgoing boundaries"></a>
<p>For a finite set $E$ of unordered pair coordinates,</p>
<div class="math-display">$$\mathbb E_q\bigl|\{e\in E:e\text{ is open}\}\bigr|=\sum_{e\in E}q_e.$$</div>
<p>This identity requires no countability of the vertex set. It counts diagonal coordinates if they are included in $E$. For a finite vertex set $\Lambda$ inside a countable vertex set, let $B_\Lambda$ count the open ordered pairs $(x,y)$ with $x\in\Lambda$ and $y\notin\Lambda$. Then</p>
<div class="math-display">$$\mathbb E_q B_\Lambda=\sum_{x\in\Lambda}\sum_{y\notin\Lambda}q_{xy}.$$</div>
<p><em>Proof.</em> Write each count as a sum of its coordinate indicators and integrate. The first sum is finite and the second is countable and nonnegative. Every boundary pair has distinct endpoints. Each crossing unordered bond has exactly one orientation pointing out of $\Lambda$, so no factor of two appears.</p>
<p>These first-moment arguments use the marginal probabilities, not independence. Independence enters the product formulas below.</p>

## Finite generating functions {#section-generating}

<a id="tag-TEYJ" data-assertion="theorem" data-title="The generating function for finitely many incident coordinates"></a>
<p>For every finite vertex set $F$ and $s\in[0,\infty]$,</p>
<div class="math-display">$$\mathbb E_q\bigl[s^{N_F(v)}\bigr]=\prod_{w\in F}(1-q_{vw}+s q_{vw}).$$</div>
<p>The formula uses nonnegative extended arithmetic, with $s^0=1$ even for $s=0$ or $s=\infty$, and $0\cdot\infty=0$. In particular,</p>
<div class="math-display">$$\mathbb P_q(N_F(v)=0)=\prod_{w\in F}(1-q_{vw}).$$</div>
<p><em>Proof.</em> The contribution of one coordinate is $s$ if it is open and one otherwise, so its expectation is $s q_{vw}+1-q_{vw}$. The distinct incident pair coordinates are independent, and the product of their contributions is $s^{N_F(v)}$. Factor their nonnegative expectation. At $s=0$, $0^{N_F(v)}$ is the indicator of $N_F(v)=0$. Empty products and the empty count both give one.</p>
<p>For the degree restricted to $F$, replace $F$ by $F\setminus\{v\}$. On two vertices with off-diagonal bond probability $t$, the degree generating function is $1-t+st$, regardless of either diagonal probability.</p>

## Exhaustion and isolation {#section-isolation}

<a id="tag-TYZP" data-assertion="theorem" data-title="Generating functions along increasing finite sets"></a>
<p>Let $F_n$ be an increasing sequence of finite vertex sets, and put $N=\lim_n N_{F_n}(v)$, allowing infinity. For $0\leq s\leq1$,</p>
<div class="math-display">$$\mathbb E_q[s^N]=\lim_{n\to\infty}\prod_{w\in F_n}(1-q_{vw}+s q_{vw})=\inf_n\prod_{w\in F_n}(1-q_{vw}+s q_{vw}).$$</div>
<p>Here $s^\infty=0$ for $s&lt;1$, while $1^\infty=1$. Only the union of the $F_n$ needs to be countable; the ambient vertex set may be arbitrary.</p>
<p><em>Proof.</em> The counts increase to $N$. With the stated endpoint conventions, $s^{N_{F_n}(v)}$ decreases pointwise to $s^N$ and is bounded by one. Bounded convergence and the finite product formula give the limit. The products are decreasing, so their limit is their infimum.</p>

<a id="tag-UNJ6" data-assertion="corollary" data-title="The isolation product and when it is positive"></a>
<p>On a countable vertex set,</p>
<div class="math-display">$$\mathbb P_q(D_v=0)=\prod_{w\ne v}(1-q_{vw}),$$</div>
<p>where the product is the decreasing limit over any finite exhaustion of the other vertices. This probability is positive if and only if $R_v&lt;\infty$ and $q_{vw}&lt;1$ for every $w\ne v$.</p>
<p><em>Proof.</em> Apply the exhaustion formula at $s=0$, removing $v$ from each finite set. If some $q_{vw}=1$, its factor is zero. Otherwise the finite products equal the exponentials of the negative partial sums of $-\log(1-q_{vw})$. The bound $-\log(1-t)\geq t$ shows that a positive product requires $\sum_{w\ne v}q_{vw}&lt;\infty$. Conversely, a finite sum has only finitely many terms greater than $1/2$. Their factors have positive product, while the remaining logarithms have finite sum because $-\log(1-t)\leq2t$ for $0\leq t\leq1/2$. The whole product is therefore positive.</p>
<p>On a one-vertex graph the product is empty and isolation has probability one, even if its diagonal coordinate is certainly open. No condition on diagonal probabilities belongs in the isolation criterion.</p>

## Finite or infinite degree {#section-finiteness}

<a id="tag-XJ74" data-assertion="proposition" data-title="The incident-row criterion determines degree finiteness almost surely"></a>
<p>For every vertex $v$ of a countable product bond model,</p>
<div class="math-display">$$\mathbb P_q(D_v&lt;\infty)=\begin{cases}1,&amp;R_v&lt;\infty,\\0,&amp;R_v=\infty.\end{cases}$$</div>
<p>These conclusions hold simultaneously at all vertices.</p>
<p><em>Proof.</em> The finite-row case follows from the first moment. For the other case fix $0&lt;s&lt;1$ and exhaust the other vertices by finite sets $F_n$. Since $1-u\leq e^{-u}$,</p>
<div class="math-display">$$\mathbb E_q[s^{D_v}]=\lim_n\prod_{w\in F_n}\bigl(1-(1-s)q_{vw}\bigr)\leq\lim_n\exp\!\left(-(1-s)\sum_{w\in F_n}q_{vw}\right)=0.$$</div>
<p>The nonnegative variable $s^{D_v}$ is strictly positive whenever $D_v$ is finite, so $D_v=\infty$ almost surely. A countable intersection gives the simultaneous assertion.</p>
<p>Infinite expectation alone would not give infinite degree almost surely without independence; the product formula supplies that step. Nor does finite degree imply a finite cluster: nearest-neighbour bonds that are all open on $\mathbb Z$ give degree two and an infinite cluster at every vertex.</p>
<p>The pinned <a href="/sources/perclib-degree/">first-moment module</a> supplies the adjacency, measurability and expectation identities. The <a href="/sources/perclib-degree-generating/">generating-function module</a> supplies the finite product, its decreasing limit and the isolation formula. Positivity of the infinite product and the infinite-row half of the degree criterion are additional deductions here. Source inspection does not create compiled tag associations or independent correspondence reviews.</p>

## The law of a finite coordinate count {#section-finite-counts}

<p>Let $I$ be any index set, let $(X_i)_{i\in I}$ be independent Bernoulli variables with parameters $p_i\in[0,1]$, and fix a finite deterministic set $F\subseteq I$. Write</p>
<div class="math-display">$$N_F=\sum_{i\in F}X_i,\qquad n=|F|,\qquad \mu_F=\sum_{i\in F}p_i.$$</div>
<p>The count is measurable and bounded, with $\mathbb E N_F=\mu_F$ by linearity. No countability of $I$ is needed. This is the same indicator argument used for <a href="/tag/TOTD/">finite bond counts</a>. More generally, the extended cardinality of any set $S$ is the sum of its membership indicators, with the nonnegative sum defined as the supremum of finite partial sums. That deterministic identity does not by itself justify interchanging an integral with an uncountable sum.</p>

<a id="tag-CPD6" data-assertion="theorem" data-title="Finite independent-coordinate counts and their binomial specialization"></a>
<p>For every integer $0\leq k\leq n$,</p>
<div class="math-display">$$\mathbb P(N_F=k)=\sum_{\substack{A\subseteq F\\|A|=k}}\prod_{i\in A}p_i\prod_{i\in F\setminus A}(1-p_i).$$</div>
<p>If $p_i=p$ for every $i\in F$, this becomes</p>
<div class="math-display">$$\mathbb P(N_F=k)=\binom nk p^k(1-p)^{n-k}.$$</div>
<p>For $k&gt;n$ the probability is zero. Empty products and zeroth powers equal one; thus the empty count is zero almost surely, and the formulas include $p=0$ and $p=1$.</p>
<p><em>Proof.</em> Partition the event by the subset $A$ of open coordinates in $F$. Independence gives the probability of each assignment, and these assignments are disjoint. In the homogeneous case every subset of size $k$ has the same weight and there are $\binom nk$ such subsets. Coordinates outside $F$ have no effect on the law, even if their probabilities differ from $p$.</p>

## Concentration about the mean {#section-concentration}

<a id="tag-XSA6" data-assertion="theorem" data-title="Exponential-moment and Hoeffding bounds for a finite independent count"></a>
<p>For every real $\lambda$,</p>
<div class="math-display">$$\mathbb E\exp\bigl(\lambda(N_F-\mu_F)\bigr)\leq\exp(n\lambda^2/8).$$</div>
<p>If $n\geq1$, then for every $t\geq0$,</p>
<div class="math-display">$$\mathbb P(N_F-\mu_F\geq t)\leq e^{-2t^2/n},\qquad \mathbb P(\mu_F-N_F\geq t)\leq e^{-2t^2/n}.$$</div>
<p>Consequently $\mathbb P(|N_F-\mu_F|\geq t)\leq\min\{1,2e^{-2t^2/n}\}$. When $F$ is empty, $N_F-\mu_F=0$: each of the one-sided events has probability one at $t=0$ and zero at $t&gt;0$.</p>
<p><em>Proof.</em> For a single Bernoulli variable of parameter $p$, put</p>
<div class="math-display">$$g(\lambda)=\log\bigl((1-p)e^{-\lambda p}+p e^{\lambda(1-p)}\bigr).$$</div>
<p>Then $g(0)=g'(0)=0$ and $g''(\lambda)=r_\lambda(1-r_\lambda)\leq1/4$, where $r_\lambda=pe^\lambda/(1-p+pe^\lambda)$. The denominator is positive, including at the deterministic endpoints. Taylor's integral remainder gives $g(\lambda)\leq\lambda^2/8$ for both signs of $\lambda$. Independence now factors the centered exponential moment over $F$, giving the first bound.</p>
<p>For $\lambda\geq0$, exponential Markov gives</p>
<div class="math-display">$$\mathbb P(N_F-\mu_F\geq t)\leq\exp(-\lambda t+n\lambda^2/8).$$</div>
<p>Choose $\lambda=4t/n$; at $t=0$ the claimed bound is simply one. Apply the same argument to $\mu_F-N_F$, using the exponential-moment bound at negative parameters, for the lower tail. A union bound and the bound by one give the two-sided estimate.</p>
<p>These statements apply to any finite deterministic set of pair coordinates. For degree inside a finite vertex set $A$, use $F=\{\{v,w\}:w\in A\setminus\{v\}\}$, so that $n=|A\setminus\{v\}|$ and $\mu_F=\sum_{w\in A\setminus\{v\}}q_{vw}$. A finite collection of boundary pairs is another instance. The entire boundary of a finite vertex set can be infinite and is not covered by a finite-$n$ bound.</p>
<p>The choice of coordinates is essential. A set selected from observed answers need not have the original product law conditional on that selection. Nor are the indicators that vertices belong to a cluster independent. Thus this count estimate does not give a cluster-volume concentration bound. The <a href="/sources/perclib-concentration/">pinned concentration module</a> supplies the one-sided finite-count bounds and homogeneous law; the displayed assignment formula and two-sided bound are their elementary expository extensions.</p>


## An infinite intensity row at one vertex {#section-infinite-intensity}

<a id="tag-VNRG" data-assertion="theorem" data-title="One divergent intensity row forces zero rooted and global critical intensities"></a>
<p>Let $V$ be countable and let $J_{xy}\geq0$ be finite symmetric intensities on distinct pairs. If</p>
<div class="math-display">$$\sum_{y\ne v}J_{vy}=\infty$$</div>
<p>at one vertex $v$, then for every fixed finite $\beta&gt;0$, the profile $q_{xy}(\beta)=1-e^{-\beta J_{xy}}$ gives $v$ infinite degree and an infinite cluster almost surely. Consequently the <a href="/tag/1C8G/">rooted critical intensity</a> at $v$ and the global critical intensity both equal zero.</p>
<p><em>Proof.</em> For $t\geq0$, concavity of $1-e^{-t}$ on $[0,1]$ and monotonicity beyond one give</p>
<div class="math-display">$$1-e^{-t}\geq(1-e^{-1})\min\{t,1\}.$$</div>
<p>The sum of $\beta J_{vy}$ diverges. Its truncation at one still diverges: either infinitely many terms are at least one, or only finitely many finite terms have changed. Applying the displayed inequality term by term proves $\sum_{y\ne v}q_{vy}(\beta)=\infty$. The <a href="/tag/XJ74/">independent degree criterion</a> gives infinite degree, and every open neighbour belongs to the cluster of $v$. Every positive intensity therefore lies in both defining percolation sets, whose infima are zero. At zero intensity all off-diagonal bonds are closed and clusters are singletons.</p>
<p>Only the row at $v$ is assumed infinite. No translation invariance or condition on other rows is used, and the conclusion does not assert that every other rooted threshold vanishes. Individual finiteness of the intensities is essential to the truncation step: a single infinite summand would not imply infinitely many open neighbours. For a displacement kernel the <a href="/tag/R01V/">row identity</a> gives the hypothesis at every root, recovering <a href="/tag/K38T/">K38T</a>.</p>
<p>The <a href="/sources/perclib-infinite-degree/">source proof</a> obtains the infinite-degree assertion from the second Borel–Cantelli lemma instead of the generating function used in XJ74. The events that distinct neighbours are joined to $v$ use distinct unordered pairs, hence are independent; their probabilities have divergent sum, so infinitely many occur almost surely. Reindexing the off-diagonal row by the other vertices makes this application exact. The source's non-vacuity examples are a constant probability-$1/2$ profile and a constant intensity-one kernel on $\mathbb N$. The deterministic truncation and row identities do not need countability; the probability statements do.</p>
