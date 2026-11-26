---
{
  "id": "integrated-susceptibility",
  "title": "Integrating susceptibility inequalities",
  "subtitle": "Reciprocals, the linear error term, and logarithmic losses",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Finite-volume pivotal bounds give the upper susceptibility differential inequality and a lower bound at a susceptibility blow-up. An explicit reverse inequality gives the triangle upper bound and logarithmic losses.",
  "context": [
    "The probabilistic bounds use independent bonds with probabilities $1-e^{-\\beta J(u,v)}$ and symmetric nonnegative weights.",
    "The reciprocal triangle bound has its own explicitly stated function and endpoint hypotheses.",
    "Its reverse differential inequality remains an input."
  ],
  "related": [
    "triangle-condition",
    "susceptibility",
    "sharpness"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "perclib-boundary-susceptibility",
    "perclib-susceptibility-derivative",
    "perclib-susceptibility-regularity",
    "perclib-independent-layer",
    "perclib-independent-layer-intensity",
    "perclib-logarithmic-corrections",
    "perclib-susceptibility-endpoint",
    "perclib-free-group-tree",
    "perclib-train10-models-longrange-finitesusceptibility",
    "perclib-train10-percolation-bond-localconvergence",
    "hutchcroft-lrp-3"
  ],
  "aliases": [
    "integrated triangle bound",
    "reciprocal susceptibility",
    "logarithmic susceptibility bound"
  ],
  "prototypeUses": [
    "triangle-condition"
  ]
}
---

## A finite-volume derivative bound {#section-finite-derivative}

<p>We use the finite BK inequality: under an independent bond law, the probability that two increasing events have disjoint open-edge witnesses is at most the product of their probabilities. The pivotal calculation below is on a finite graph; the passage to infinite volume is made afterwards.</p>
<a id="tag-TAVM" data-assertion="proposition" data-title="Finite-volume susceptibility derivative bound"></a>
<p>Let $F$ be a nonempty finite vertex set with independent edges of probabilities $1-e^{-\beta J(u,v)}$, where $J(u,v)=J(v,u)\geq0$ is finite for $u\neq v$. Write $\tau_F(u,v)$ for connectivity using only vertices of $F$, and set</p>
<div class="math-display">$$\chi_F(u)=\sum_{v\in F}\tau_F(u,v),\qquad M_F=\max_{u\in F}\chi_F(u),\qquad R_F=\max_{u\in F}\sum_{v\in F\setminus\{u\}}J(u,v).$$</div>
<p>For every root $o\in F$ and every $\beta&gt;0$,</p>
<div class="math-display">$$0\leq\chi_F'(o)\leq R_F\chi_F(o)M_F.$$</div>
<p><em>Proof.</em> The finite-coordinate <a href="#/russo-formula">Russo formula</a> gives</p>
<div class="math-display">$$\frac{d}{d\beta}\tau_F(o,x)=\sum_{\{u,v\}\in\binom{F}{2}}J(u,v)\,\mathbb P_\beta\bigl(\{u,v\}\text{ is closed and pivotal for }o\leftrightarrow x\bigr).$$</div>
<p>Indeed, the derivative of an edge probability is $J(u,v)e^{-\beta J(u,v)}$, and pivotality does not depend on that edge's state. If the edge is closed pivotal, its endpoints lie in the distinct clusters of $o$ and $x$, in one of the two possible orders. Paths within those clusters give disjoint witnesses. BK therefore bounds the probability in the sum by</p>
<div class="math-display">$$\tau_F(o,u)\tau_F(v,x)+\tau_F(o,v)\tau_F(u,x).$$</div>
<p>Sum over $x$ and combine the two orientations of each unordered edge:</p>
<div class="math-display">$$\chi_F'(o)\leq\sum_{u\in F}\tau_F(o,u)\sum_{v\in F\setminus\{u\}}J(u,v)\chi_F(v)\leq R_F M_F\chi_F(o).$$</div>
<p>Nonnegativity follows either from the same derivative formula or from monotone coupling. The closed-edge factor in the Russo identity is essential; it has not been replaced by an unconditional pivotal probability with the same coefficient.</p>

## Infinite volume and a susceptibility blow-up {#section-lower-bound}

<a id="tag-MXGM" data-assertion="theorem" data-title="Susceptibility derivative and lower blow-up bound for a transitive intensity model"></a>
<p>Let $V$ be countable, with symmetric nonnegative off-diagonal weights $J(u,v)$ preserved by a transitive group of permutations. Assume</p>
<div class="math-display">$$0&lt;R=\sum_{v\neq o}J(o,v)&lt;\infty.$$</div>
<p>Use independent edges of probabilities $1-e^{-\beta J(u,v)}$, and write $\chi(\beta)=\sum_v\mathbb P_\beta(o\leftrightarrow v)$, which does not depend on $o$. Suppose $0\leq a&lt;b&lt;\infty$ and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$. Then $\chi$ is locally Lipschitz on $(a,b)$ and</p>
<div class="math-display">$$0\leq\chi'(\beta)\leq R\chi(\beta)^2\qquad\text{for almost every }\beta\in(a,b).$$</div>
<p>If additionally $\chi(b)=\infty$, then</p>
<div class="math-display">$$\chi(\beta)\geq\frac1{R(b-\beta)}\qquad(a&lt;\beta&lt;b).$$</div>
<p><em>Proof.</em> Exhaust $V$ by finite sets $F$ containing $o$. Every open connection has a finite path witness, so $\chi_F(o,\beta)\uparrow\chi(\beta)$. The finite-volume row sum is at most $R$, and $\chi_F(v,\beta)\leq\chi(\beta)$ for every $v\in F$, by inclusion in the full cluster and transitivity of the full law. Thus, for $a&lt;s&lt;t&lt;b$, the finite-volume estimate gives</p>
<div class="math-display">$$0\leq\chi_F(o,t)-\chi_F(o,s)\leq R\int_s^t\chi(u)^2\,du.$$</div>
<p>The right side is finite, since $\chi(u)\leq\chi(t)$. Passing to the limit at both endpoints yields the same integral inequality for $\chi$. On each compact subinterval this makes $\chi$ Lipschitz, with constant at most $R$ times the square of its right-endpoint value. Differentiating the integral inequality gives the asserted almost-everywhere bound.</p>
<p>For the endpoint claim, finite-volume continuity and monotonicity give</p>
<div class="math-display">$$\sup_{a&lt;\beta&lt;b}\chi(\beta)=\sup_F\sup_{a&lt;\beta&lt;b}\chi_F(o,\beta)=\sup_F\chi_F(o,b)=\chi(b)=\infty.$$</div>
<p>Hence $\chi(\beta)\to\infty$ as $\beta\uparrow b$. Since $\chi\geq1$, its reciprocal is locally absolutely continuous and satisfies $(1/\chi)'\geq-R$ almost everywhere. Integrating from $\beta$ to $t&lt;b$ gives</p>
<div class="math-display">$$\frac1{\chi(\beta)}\leq\frac1{\chi(t)}+R(t-\beta).$$</div>
<p>Let $t\uparrow b$ and take reciprocals. This proves the lower bound. In particular, no differentiation of an infinite connection sum was used before establishing local regularity.</p>
<p>This is the upper differential inequality and reciprocal argument. Applying it with $b=\beta_c$ still requires subcritical finiteness, a finite positive critical parameter and $\chi(\beta_c)=\infty$. Those model-specific facts are not consequences of the differential inequality alone. No triangle condition is used in this part.</p>

## The two-cluster derivative identity {#section-two-clusters}

<a id="tag-4800" data-assertion="theorem" data-title="Two-cluster susceptibility derivative identity on a countable group"></a>
<p>Under the hypotheses of the preceding theorem, suppose $V$ is a countable group with identity $o$ and $J(gu,gv)=J(u,v)$ for every $g,u,v$. Let $K_x$ be the full open cluster of $x$. For almost every $\beta\in(a,b)$,</p>
<div class="math-display">$$\begin{aligned}\chi'(\beta)&=\sum_{y\neq o}J(o,y)\,\mathbb E_\beta\!\left[|K_o|\,|K_y|\,\mathbf1_{\{o\not\leftrightarrow y\}}\right]\\&=\sum_{y\neq o}\sum_{z,w}J(o,y)\,\mathbb P_\beta(o\leftrightarrow z,\ y\leftrightarrow w,\ o\not\leftrightarrow y).\end{aligned}$$</div>
<p>These nonnegative sums are finite and bounded by $R\chi(\beta)^2$. The two clusters in the expectation belong to the same percolation configuration; they are not independent.</p>
<p><em>Proof.</em> Before applying BK, the finite-volume pivotal formula gives the exact identity</p>
<div class="math-display">$$\chi_F'(o,\beta)=\sum_{\substack{u,v\in F\\u\neq v}}\sum_{x\in F}J(u,v)\,\mathbb P_\beta(o\leftrightarrow_F u,\ v\leftrightarrow_F x,\ o\not\leftrightarrow_F v).$$</div>
<p>The event on the right says precisely that opening the edge from the root's cluster to the other cluster connects $o$ to $x$. It already forces that edge to be closed, and the oriented sum counts its unique endpoint in the root's cluster.</p>
<p>For each fixed $(u,v,x)$, its indicator converges to the corresponding full-volume indicator as $F$ exhausts $V$. Each connection is witnessed by a finite path. BK bounds the summand, uniformly in $F$, by</p>
<div class="math-display">$$J(u,v)\tau_\beta(o,u)\tau_\beta(v,x).$$</div>
<p>The sum of these bounds is $R\chi(\beta)^2$. Dominated convergence for the countable sum therefore gives $\chi_F'(o,\beta)\to S(\beta)$, where</p>
<div class="math-display">$$S(\beta)=\sum_{u\neq v}\sum_xJ(u,v)\,\mathbb P_\beta(o\leftrightarrow u,\ v\leftrightarrow x,\ o\not\leftrightarrow v).$$</div>
<p>On every compact interval $[s,t]\subset(a,b)$, the derivatives are bounded by $R\chi(t)^2$. Integrating the finite-volume identity and passing to the limit consequently yields $\chi(t)-\chi(s)=\int_s^tS(\beta)\,d\beta$. Thus $\chi'=S$ almost everywhere.</p>
<p>It remains to move the distinguished vertex. In each summand apply the translation by $u^{-1}$, and set $z=u^{-1}$, $y=u^{-1}v$ and $w=u^{-1}x$. This is a bijection between the indexing triples, with $y\neq o$, and invariance gives</p>
<div class="math-display">$$S(\beta)=\sum_{y\neq o}\sum_{z,w}J(o,y)\,\mathbb P_\beta(z\leftrightarrow o,\ y\leftrightarrow w,\ z\not\leftrightarrow y).$$</div>
<p>On $z\leftrightarrow o$, the last condition is equivalent to $o\not\leftrightarrow y$. Tonelli's theorem then turns the sums over $z,w$ into the product of cluster volumes, proving both displayed equalities.</p>
<p>This proves the two-cluster identity for translation-invariant models on countable groups. The general unimodular version requires the appropriate mass-transport identity. The next estimate bounds the loss from the independent-cluster value $R\chi^2$ by conditioning on the first cluster; the identity itself does not remove that loss.</p>

## Deleting a revealed cluster {#section-deletion}

<p>At a fixed parameter, write $\tau^S(y,w)$ for the probability of connecting $y$ to $w$ using only vertices of $V\setminus S$, with the same independent edge probabilities as in the full model. Set this quantity to zero if either endpoint belongs to $S$. The next two estimates hold for any independent bond profile on a countable vertex set.</p>
<a id="tag-7902" data-assertion="proposition" data-title="Connection loss on deleting a deterministic vertex set"></a>
<p>For every deterministic $S\subseteq V$ and vertices $y,w$,</p>
<div class="math-display">$$0\leq\tau(y,w)-\tau^S(y,w)\leq\sum_{c\in S}\tau(y,c)\tau(c,w).$$</div>
<p><em>Proof.</em> Couple the deleted and full graphs by retaining the same edges outside $S$. If $y$ and $w$ are connected in the full graph but not in the deleted graph, a simple open path between them visits $S$. Split it at its first such vertex $c$. The two path segments have disjoint edge sets, so BK and a union bound give the upper bound. A segment may be empty when $c$ is an endpoint. On a countable graph the same argument follows by finite-edge exhaustion, since each connection has a finite witness. The lower bound follows from inclusion of the deleted graph.</p>

<a id="tag-J1LW" data-assertion="theorem" data-title="Five-factor bound for the loss of two distinct cluster connections"></a>
<p>Fix $x$ with $K_x$ finite almost surely. For arbitrary $y,z,w$, define</p>
<div class="math-display">$$Q(x,z;y,w)=\mathbb P(x\leftrightarrow z,\ y\leftrightarrow w,\ x\not\leftrightarrow y).$$</div>
<p>Then</p>
<div class="math-display">$$Q(x,z;y,w)=\mathbb E\!\left[\mathbf1_{\{z\in K_x\}}\tau^{K_x}(y,w)\right]$$</div>
<p>and</p>
<div class="math-display">$$0\leq\tau(x,z)\tau(y,w)-Q(x,z;y,w)\leq\sum_{a,c}\tau(x,a)\tau(a,z)\tau(a,c)\tau(y,c)\tau(c,w).$$</div>
<p>The right side is a nonnegative extended sum. Repeated marked vertices are allowed.</p>
<p><em>Proof.</em> For each finite set $S$ containing $x$, the event $K_x=S$ depends only on edges with at least one endpoint in $S$: those within $S$ must connect every vertex to $x$, and all boundary edges must be closed. Edges with both endpoints outside $S$ retain their independent product law conditional on this event whenever it has positive probability. As the finite subsets of a countable set form a countable family and $K_x$ is finite almost surely, summing over $S$ gives the expectation identity.</p>
<p>Subtract this identity from $\mathbb E[\mathbf1_{\{z\in K_x\}}\tau(y,w)]$. The deterministic deletion bound and Tonelli give</p>
<div class="math-display">$$\begin{aligned}0&\leq\tau(x,z)\tau(y,w)-Q(x,z;y,w)\\&\leq\sum_c\mathbb P(x,z,c\text{ lie in one cluster})\,\tau(y,c)\tau(c,w).\end{aligned}$$</div>
<p>The three-point case of the <a href="#/multipoint-trees">tree-graph inequality</a> bounds the cluster probability by $\sum_a\tau(x,a)\tau(a,z)\tau(a,c)$. Substitution proves the five-factor bound. Thus the two BK applications concern paths in a single product law at a time; no disjoint-occurrence claim is made across two independently sampled configurations.</p>

## The weighted open-triangle error {#section-weighted-error}

<a id="tag-4960" data-assertion="corollary" data-title="Susceptibility lower derivative bound with a weighted open-triangle error"></a>
<p>In the countable-group intensity model of the two-cluster identity, define, for $\beta\in(a,b)$,</p>
<div class="math-display">$$\Lambda(\beta)=\sum_{y\neq o}J(o,y)T_\beta^3(o,y).$$</div>
<p>Then $\Lambda(\beta)&lt;\infty$ and, for almost every $\beta\in(a,b)$,</p>
<div class="math-display">$$\chi'(\beta)\geq\bigl(R-\Lambda(\beta)\bigr)\chi(\beta)^2.$$</div>
<p>In particular, if $\sup_{y\neq o}T_\beta^3(o,y)\leq\delta&lt;1$ throughout an interval, then $\chi'(\beta)\geq R(1-\delta)\chi(\beta)^2$ for almost every $\beta$ in that interval.</p>
<p><em>Proof.</em> Finite susceptibility implies that $K_o$ is finite almost surely. Apply the five-factor inequality with $x=o$, multiply by $J(o,y)$, and sum over $y\neq o,z,w$. The two-cluster identity identifies the sum of $J(o,y)Q(o,z;y,w)$ with $\chi'(\beta)$ almost everywhere, while the independent-product term sums to $R\chi(\beta)^2$. The error sums exactly to</p>
<div class="math-display">$$\begin{aligned}&\sum_{y\neq o,z,w,a,c}J(o,y)\tau_\beta(o,a)\tau_\beta(a,z)\tau_\beta(a,c)\tau_\beta(y,c)\tau_\beta(c,w)\\&\qquad=\chi(\beta)^2\sum_{y\neq o}J(o,y)\sum_{a,c}\tau_\beta(o,a)\tau_\beta(a,c)\tau_\beta(c,y)=\chi(\beta)^2\Lambda(\beta).\end{aligned}$$</div>
<p>Here transitivity gives both terminal row sums equal to $\chi(\beta)$, and Tonelli justifies every rearrangement. Also $T_\beta^3(o,y)\leq\chi(\beta)^2$, by bounding its last factor by one and summing the first two, so $\Lambda(\beta)\leq R\chi(\beta)^2&lt;\infty$. All terms being subtracted are therefore finite. Finally $\Lambda\leq R\delta$ under the stated uniform bound.</p>
<p>This supplies a precise five-factor comparison and its weighted summation for the cluster coupling. The bound involves all weighted neighbours of $o$, including nearby ones. <a href="#/connection-kernels">Open-triangle decay at large separation</a> does not make this weighted error small by itself. The surgery that moves endpoints apart, and its constants, remain to be justified separately.</p>

## The reciprocal estimate {#section-reciprocal}

<a id="tag-TC6Q" data-assertion="theorem" data-title="Integrated quantitative susceptibility bound"></a>
<p>Let $0\leq\beta_0&lt;\beta_c&lt;\infty$. Suppose $\chi:(\beta_0,\beta_c)\to(0,\infty)$ is nondecreasing and locally absolutely continuous, and $D:(\beta_0,\beta_c)\to[1,\infty)$ is measurable and finite-valued. Assume that, for almost every $\beta$ in this interval,</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{\chi(\beta)(\chi(\beta)-D(\beta))}{3\beta^2D(\beta)^2}.$$</div>
<p>Then, for every $\beta\in(\beta_0,\beta_c)$,</p>
<div class="math-display">$$\chi(\beta)\leq\left(1+\frac{\beta_c-\beta}{3\beta\beta_c}\right)\left[\int_\beta^{\beta_c}\frac{ds}{3s^2D(s)^2}\right]^{-1}.$$</div>
<p>The integral in brackets is finite and strictly positive. No limit assumption on $\chi$ at $\beta_c$ is needed for this upper bound.</p>
<p><em>Proof.</em> Set $y=1/\chi$. On each compact subinterval, positivity and continuity bound $\chi$ away from zero, so the reciprocal is absolutely continuous and the chain rule gives</p>
<div class="math-display">$$y'(s)\leq-\frac1{3s^2D(s)^2}+\frac{y(s)}{3s^2D(s)}\quad\text{for almost every }s.$$</div>
<p>Fix $\beta&lt;t&lt;\beta_c$. Since $\chi$ is nondecreasing, $y(s)\leq y(\beta)$ for $s\geq\beta$. Integrating the preceding inequality and using $y(t)\geq0$ therefore gives</p>
<div class="math-display">$$\int_\beta^t\frac{ds}{3s^2D(s)^2}\leq y(\beta)-y(t)+\int_\beta^t\frac{y(s)}{3s^2D(s)}\,ds\leq y(\beta)\left(1+\int_\beta^t\frac{ds}{3s^2D(s)}\right).$$</div>
<p>Let $t\uparrow\beta_c$. Nonnegativity permits monotone convergence in both integrals, and $D\geq1$ gives</p>
<div class="math-display">$$\int_\beta^{\beta_c}\frac{ds}{3s^2D(s)}\leq\frac13\left(\frac1\beta-\frac1{\beta_c}\right).$$</div>
<p>The other integrand is positive everywhere and bounded above by $1/(3\beta^2)$ on an interval of positive finite length. Its integral is therefore strictly positive and finite. Dividing and taking the reciprocal proves the bound.</p>
<p>The linear term in the differential inequality cannot simply be dropped: $\chi(\chi-D)$ is smaller than $\chi^2$. The reciprocal calculation retains that term and accounts for it in the displayed prefactor.</p>

## Bounded and logarithmic diagrams {#section-growth}

<a id="tag-W9IY" data-assertion="corollary" data-title="Susceptibility upper bounds from bounded or logarithmic diagram control"></a>
<p>Under the preceding hypotheses, suppose there are $C&gt;0$, $a\geq0$ and $0&lt;\varepsilon_0&lt;\min(e^{-1},\beta_c-\beta_0)$ such that</p>
<div class="math-display">$$D(\beta_c-u)\leq C\bigl(\log(1/u)\bigr)^a\qquad(0&lt;u&lt;\varepsilon_0).$$</div>
<p>Then there are $C'&gt;0$ and $\varepsilon_1&gt;0$ such that</p>
<div class="math-display">$$\chi(\beta_c-\varepsilon)\leq C'\varepsilon^{-1}\bigl(\log(1/\varepsilon)\bigr)^{2a}\qquad(0&lt;\varepsilon&lt;\varepsilon_1).$$</div>
<p>In particular, a bounded $D$ near $\beta_c$ gives $\chi(\beta_c-\varepsilon)=O(\varepsilon^{-1})$.</p>
<p><em>Proof.</em> Take $\varepsilon$ small enough that the hypotheses apply and $\varepsilon&lt;\min(1/2,\beta_c/2)$. Restrict the reciprocal integral to $s\in[\beta_c-\varepsilon,\beta_c-\varepsilon/2]$. There $s\leq\beta_c$ and</p>
<div class="math-display">$$D(s)\leq C\bigl(\log(2/\varepsilon)\bigr)^a\leq C\,2^a\bigl(\log(1/\varepsilon)\bigr)^a.$$</div>
<p>Consequently,</p>
<div class="math-display">$$\int_{\beta_c-\varepsilon}^{\beta_c}\frac{ds}{3s^2D(s)^2}\geq\frac{\varepsilon}{6\beta_c^2C^2\,2^{2a}(\log(1/\varepsilon))^{2a}}.$$</div>
<p>The prefactor in the integrated bound is bounded as $\varepsilon\downarrow0$, which proves the claimed estimate. Bounded diagrams are the case $a=0$.</p>
<p>A matching lower bound needs separate hypotheses, such as those of the susceptibility blow-up result above. If $D$ is bounded and one also knows $\chi(\beta_c-\varepsilon)\geq c\varepsilon^{-1}$ near the endpoint for some $c&gt;0$, then the two estimates give $\chi(\beta_c-\varepsilon)\asymp\varepsilon^{-1}$. Neither that lower bound nor equality in a logarithmic exponent follows from the upper estimate alone.</p>

## Integrating the corrected quadratic bound {#section-corrected-reciprocal}

<a id="tag-6PGV" data-assertion="theorem" data-title="Integral and logarithmic susceptibility bounds from the corrected quadratic inequality"></a>
<p>Let $0\leq\beta_0&lt;\beta_c&lt;\infty$. Suppose $\chi:(\beta_0,\beta_c)\to(0,\infty)$ is nondecreasing and locally absolutely continuous, and $D:(\beta_0,\beta_c)\to[1,\infty)$ is measurable and finite-valued. If</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{(\chi(\beta)-D(\beta))_+^2}{3\beta^2D(\beta)^2}\qquad\text{for almost every }\beta,$$</div>
<p>then, for every $\beta\in(\beta_0,\beta_c)$,</p>
<div class="math-display">$$\chi(\beta)\leq\left(1+\frac{2(\beta_c-\beta)}{3\beta\beta_c}\right)\left[\int_\beta^{\beta_c}\frac{ds}{3s^2D(s)^2}\right]^{-1}.$$</div>
<p>In particular, if $D(\beta_c-u)\leq C(\log(1/u))^a$ for all sufficiently small $u&gt;0$, with $C&gt;0$ and $a\geq0$, then</p>
<div class="math-display">$$\chi(\beta_c-\varepsilon)=O\!\left(\varepsilon^{-1}(\log(1/\varepsilon))^{2a}\right)\qquad(\varepsilon\downarrow0).$$</div>
<p>No endpoint divergence of $\chi$ is assumed.</p>
<p><em>Proof.</em> Put $y=1/\chi$. The reciprocal is locally absolutely continuous. Since $(1-z)_+^2\geq1-2z$ for every $z\geq0$, the hypothesis gives</p>
<div class="math-display">$$y'(s)\leq-\frac{(1-D(s)y(s))_+^2}{3s^2D(s)^2}\leq-\frac1{3s^2D(s)^2}+\frac{2y(s)}{3s^2D(s)}$$</div>
<p>almost everywhere. Fix $\beta&lt;t&lt;\beta_c$. Monotonicity gives $0&lt;y(s)\leq y(\beta)$ for $s\geq\beta$, so integration yields</p>
<div class="math-display">$$\int_\beta^t\frac{ds}{3s^2D(s)^2}\leq y(\beta)-y(t)+2\int_\beta^t\frac{y(s)}{3s^2D(s)}\,ds\leq y(\beta)\left(1+2\int_\beta^t\frac{ds}{3s^2D(s)}\right).$$</div>
<p>Let $t\uparrow\beta_c$ and use $D\geq1$. The last integral is at most $(1/\beta-1/\beta_c)/3$. The integral on the left is finite and strictly positive, because its integrand is positive and bounded on an interval of positive finite length. Rearrangement proves the first bound.</p>
<p>For the logarithmic consequence, restrict that integral to $s\in[\beta_c-\varepsilon,\beta_c-\varepsilon/2]$. For sufficiently small $\varepsilon$, the denominator there is at most $3\beta_c^2C^2(\log(2/\varepsilon))^{2a}$. Thus the integral is at least a positive constant times $\varepsilon(\log(1/\varepsilon))^{-2a}$, while the prefactor stays bounded.</p>
<p>Taking $D$ to be the triangle diagram applies this calculation to the <a href="/tag/4KBG/">corrected quadratic susceptibility inequality</a>, whenever its hypotheses and the stated regularity hold. The bounded-diagram case gives the susceptibility upper bound of order $(\beta_c-\beta)^{-1}$; a matching lower bound still requires its own endpoint argument. This recovers the logarithmic upper-bound consequence without using the false stronger numerator. The earlier conditional integral theorem retains its original hypothesis and prefactor.</p>

## Stability under an independent added layer {#section-sprinkling}

<a id="tag-MLLO" data-assertion="theorem" data-title="An independent sparse layer preserves uniformly finite susceptibility"></a>
<p>On a nonempty countable vertex set, let red and blue bonds be mutually independent product configurations with symmetric off-diagonal probabilities $q_0$ and $s$. Write $\chi_0(v)$ for red susceptibility and $\chi(v)$ for susceptibility in their union. Suppose</p>
<div class="math-display">$$M=\sup_v\chi_0(v)&lt;\infty,\qquad\delta=\sup_v\sum_{w\ne v}s(v,w)&lt;\infty,\qquad\delta M&lt;1.$$</div>
<p>Then $\chi(v)\leq\chi_0(v)/(1-\delta M)$ at every vertex. Transitivity is not required.</p>
<p><em>Proof.</em> For ghost intensity $h&gt;0$, write $G_v(h)$ for the union ghost probability and $G^*(h)=\sup_vG_v(h)\leq1$. All red clusters are finite almost surely. The <a href="/tag/BEJT/">independent-layer ghost comparison</a>, together with $1-e^{-hx}\leq hx$, gives</p>
<div class="math-display">$$G_v(h)\leq h\chi_0(v)+\delta\chi_0(v)G^*(h).$$</div>
<p>Taking the supremum and rearranging yields $G^*(h)\leq hM/(1-\delta M)$. Substituting back into the rooted inequality gives $G_v(h)\leq h\chi_0(v)/(1-\delta M)$. Finally $(1-e^{-hT})/h\uparrow T$ as $h\downarrow0$ for any extended nonnegative cluster volume $T$, including $T=\infty$. Monotone convergence proves the susceptibility bound. The rearrangement used only finite ghost probabilities; it did not subtract infinite susceptibilities.</p>

<a id="tag-5LNL" data-assertion="theorem" data-title="Finite susceptibility is right-open and diverges at its finite threshold"></a>
<p>Let a countable independent intensity model be invariant under a transitive group action, with symmetric finite nonnegative off-diagonal weights $J$ and</p>
<div class="math-display">$$0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty,\qquad q_\beta(x,y)=1-e^{-\beta J(x,y)}.$$</div>
<p>If $\chi_\beta&lt;\infty$ and $0\leq\varepsilon&lt;1/(L\chi_\beta)$, then</p>
<div class="math-display">$$\chi_{\beta+\varepsilon}\leq\frac{\chi_\beta}{1-\varepsilon L\chi_\beta}&lt;\infty.$$</div>
<p>Consequently, if $b_\chi=\sup\{\beta\geq0:\chi_\beta&lt;\infty\}$ is finite, then $b_\chi\geq1/L$, $\chi_{b_\chi}=\infty$, and $\chi_\beta\to\infty$ as $\beta\uparrow b_\chi$.</p>
<p><em>Proof.</em> Add to the intensity-$\beta$ model an independent layer with probabilities $1-e^{-\varepsilon J(x,y)}\leq\varepsilon J(x,y)$. The union has intensity $\beta+\varepsilon$, while its blue row is at most $\varepsilon L$. Apply MLLO with $M=\chi_\beta$. This also proves right-continuity at each finite-susceptibility parameter by monotonicity and squeezing.</p>
<p>The <a href="/tag/E771/">row-sum bound</a>, with diagonal weights taken to be zero, gives finite susceptibility for $\beta L&lt;1$. Thus $b_\chi\geq1/L$. Monotonicity and the definition of the supremum imply finiteness at every $\beta&lt;b_\chi$. If susceptibility were finite at $b_\chi$, the first part would extend finiteness to a larger parameter, a contradiction. Under monotone coupling, each finite path present at a positive parameter is present at some smaller parameter almost surely, since each edge probability is continuous and there are countably many edges. Hence the connection probabilities increase to their endpoint values as $\beta\uparrow b_\chi$. Tonelli over the connected vertices now gives $\chi_\beta\uparrow\chi_{b_\chi}=\infty$.</p>
<p>For the normalized power-law model in <a href="/tag/7F5O/">7F5O</a>, the off-diagonal kernel is summable. If its susceptibility threshold $b_\chi$ is finite, this theorem supplies both endpoint assumptions of that bootstrap at $b=b_\chi$, and hence of the <a href="/tag/26NT/">high-dimensional volume-tail result</a>. The finite-set proof below identifies $b_\chi$ with the percolation threshold. Its finiteness requires a separate model argument, supplied next for kernels containing a lattice plane.</p>

## A finite threshold from planar contours {#section-peierls}

<a id="tag-NUJY" data-assertion="theorem" data-title="Peierls bound and nontriviality of the lattice transition"></a>
<p>For independent nearest-neighbour bonds on $\mathbb Z^2$, suppose each edge is open with probability at least $1-q$. If $0\leq q&lt;1/3$, then</p>
<div class="math-display">$$\mathbb P(|K_0|=\infty)\geq1-\frac{6q}{(1-3q)^2}.$$</div>
<p>In particular, this probability is at least $1/9$ when $q\leq1/12$. Homogeneous nearest-neighbour bond percolation on $\mathbb Z^d$, $d\geq2$, therefore satisfies</p>
<div class="math-display">$$\frac1{2d-1}\leq p_c(\mathbb Z^d)\leq\frac{11}{12}&lt;1.$$</div>
<p><em>Proof.</em> If $K_0$ is finite, let $H$ be the finite set of dual edges crossing its edge boundary. Every corresponding primal edge is closed. At each dual vertex, the degree in $H$ is even: on walking around the corresponding primal face, membership in $K_0$ changes an even number of times. Hence $H$ decomposes into edge-disjoint simple dual cycles.</p>
<p>The positive horizontal ray from zero crosses an odd number of edges of $H$. Indeed, its successive primal vertices start in $K_0$ and eventually stay outside it. Some cycle in the decomposition therefore crosses this ray an odd number of times. The ray avoids dual vertices, so the Jordan curve theorem says that this cycle surrounds zero. This argument also handles boundaries that touch themselves at dual vertices; the whole boundary need not be a simple cycle.</p>
<p>A simple dual cycle of length $n$ surrounding zero has a crossing of the positive ray at $(m+1/2,0)$ with $0\leq m&lt;n$. To see the bound on $m$, the cycle also has a vertex with negative first coordinate, and its coordinate span is at most its length. Encode the cycle by its first crossing along the ray, one of the two orientations of that crossing edge, and the following $n-1$ steps. Each step has at most three choices, since immediate reversal is forbidden. Thus there are at most $2n3^{n-1}\leq2n3^n$ such cycles. Independence bounds the probability that any specified one is closed by $q^n$, even when the bond probabilities differ. A union bound gives</p>
<div class="math-display">$$\mathbb P(|K_0|&lt;\infty)\leq\sum_{n\geq1}2n(3q)^n=\frac{6q}{(1-3q)^2}.$$</div>
<p>At $q=1/12$ the right side is $8/9$. A coordinate plane in $\mathbb Z^d$ gives the same upper bound on $p_c$ for every $d\geq2$.</p>
<p>For the lower bound, a vertex of an infinite cluster in a graph of maximum degree $\Delta\geq2$ starts an open simple path of every finite length. There are at most $\Delta(\Delta-1)^{n-1}$ such paths of length $n$, so their total probability is at most $\Delta p[(\Delta-1)p]^{n-1}$. It tends to zero when $p&lt;1/(\Delta-1)$. Taking $\Delta=2d$ completes the proof.</p>
<p>This proves nontriviality, with an explicit, deliberately crude upper bound. It does not identify the square-lattice threshold or determine behaviour at criticality.</p>

<a id="tag-EBVV" data-assertion="corollary" data-title="Finite susceptibility threshold for summable kernels containing a lattice plane"></a>
<p>Let $d\geq2$ and let $J$ be a symmetric translation-invariant intensity kernel on $\mathbb Z^d$ with finite off-diagonal row sum $L=\sum_{y\ne0}J(y)&gt;0$. Suppose $J(e_1),J(e_2)\geq j&gt;0$. For probabilities $1-e^{-\beta J(y-x)}$, write $\beta_c$ for the infinite-cluster threshold and $b_\chi$ for the susceptibility threshold of <a href="/tag/5LNL/">5LNL</a>. Then</p>
<div class="math-display">$$0&lt;\frac1L\leq b_\chi\leq\beta_c\leq\frac{\log12}{j}&lt;\infty,\qquad\chi_{b_\chi}=\infty.$$</div>
<p><em>Proof.</em> At $\beta=(\log12)/j$, retain only the nearest-neighbour edges of the coordinate plane spanned by $e_1,e_2$. Each retained edge is open with probability at least $11/12$. NUJY gives an infinite cluster at zero with probability at least $1/9$, also in the full model. Thus $\beta_c\leq(\log12)/j$. Whenever the infinite-cluster probability is positive, susceptibility is infinite; monotonicity then gives $b_\chi\leq\beta_c$. The row-sum lower bound and endpoint divergence follow from 5LNL.</p>
<p>For the normalized kernel $J(y)=\|y\|_2^{-d-\alpha}/(d+\alpha)$, $y\ne0$, with $\alpha&gt;0$, the row sum is finite by summing over lattice shells, and one may take $j=1/(d+\alpha)$. Hence $b_\chi\leq(d+\alpha)\log12$. In dimensions $d\geq2$ with $d&gt;3\alpha$, the endpoint hypotheses of <a href="/tag/7F5O/">the cutoff bootstrap</a> are consequently satisfied at $b=b_\chi$; its <a href="/tag/26NT/">volume-tail consequence</a> applies there. Equality $b_\chi=\beta_c$ follows from the finite-set proof below. This plane argument gives no finite-threshold conclusion in dimension one.</p>

## One-dimensional long-range thresholds {#section-one-dimensional}

<a id="tag-65PY" data-assertion="theorem" data-title="A growing-block construction gives a finite threshold below the one-dimensional marginal exponent"></a>
<p>Let $J$ be a symmetric translation-invariant kernel on $\mathbb Z$ with finite off-diagonal row sum $L&gt;0$. Suppose that, for some $c&gt;0$ and $0&lt;\alpha&lt;1$,</p>
<div class="math-display">$$J(r)\geq c|r|^{-1-\alpha}\qquad(r\ne0).$$</div>
<p>Then independent bond percolation with probabilities $1-e^{-\beta J(y-x)}$ has $0&lt;\beta_c&lt;\infty$.</p>
<p><em>Proof.</em> For $n\geq1$, put $N_n=2^{n+1}$, $L_0=M_0=1$, and</p>
<div class="math-display">$$L_n=\prod_{i=1}^nN_i=2^{n(n+3)/2},\qquad M_n=\prod_{i=1}^n(N_i-1).$$</div>
<p>Partition $\mathbb Z$ into aligned intervals of $L_n$ vertices. Each level-$n$ block consists of $N_n$ level-$(n-1)$ blocks. A level-zero block is good, with its singleton as selected connected set. At higher levels, declare a block good when at most one child is bad and every pair of good children's selected sets is joined by an open edge. Select the union of those sets. It is connected inside the block and has at least $M_n$ vertices. All choices and tests use edges with both endpoints in the block.</p>
<p>The selected sets keep a positive fraction of their blocks:</p>
<div class="math-display">$$\frac{M_n}{L_n}=\prod_{i=1}^n(1-N_i^{-1})\geq1-\sum_{i=1}^nN_i^{-1}\geq\frac12.$$</div>
<p>Let $q_n$ be the probability that a level-$n$ block is bad. The child tests are independent, since they use disjoint internal edge sets. Conditional on them and their selected sets, edges between different children remain independent with their original probabilities. For any two good children, the probability of no edge between their selected sets is at most</p>
<div class="math-display">$$\exp\!\left(-\frac{\beta cM_{n-1}^2}{L_n^{1+\alpha}}\right)\leq e^{-\beta A_n},\qquad A_n=\frac{cL_{n-1}^{1-\alpha}}{4N_n^{1+\alpha}}.$$</div>
<p>Indeed, there are at least $M_{n-1}^2$ candidate edges, each of length less than $L_n$. A union bound over pairs of bad children and over unjoined good pairs gives</p>
<div class="math-display">$$q_n\leq N_n^2q_{n-1}^2+N_n^2e^{-\beta A_n},\qquad q_0=0.$$</div>
<p>Since $\alpha&lt;1$, the logarithm of $A_n$ grows quadratically with positive leading coefficient. Thus</p>
<div class="math-display">$$\beta_0=(\log2)\sup_{n\geq1}\frac{4n+11}{A_n}&lt;\infty.$$</div>
<p>For $\beta\geq\beta_0$, induction gives $q_n\leq2^{-2n-8}$. In fact, under the preceding bound on $q_{n-1}$, the two terms in the recursion are at most $2^{-2n-10}$ and $2^{-2n-9}$, respectively. Their sum is smaller than the desired bound.</p>
<p>With probability at least $1-\sum_{n\geq1}2^{-2n-8}&gt;0$, every block containing zero in this nested partition is good. On that event its selected sets are nested, contain zero, and have sizes at least $M_n\to\infty$. They lie in one open cluster, which is therefore infinite. This proves $\beta_c\leq\beta_0$. The row-sum bound gives $\beta_c\geq1/L&gt;0$.</p>
<p>If the lower bound on $J(r)$ holds only for sufficiently large $|r|$, restrict to a sublattice $m\mathbb Z$ with $m$ beyond that cutoff. Its rescaled kernel satisfies the displayed bound at every nonzero integer, with $c$ replaced by $cm^{-1-\alpha}$, so the same conclusion follows. The growing number of children is essential to this construction: discarding a fixed positive fraction at every level would not preserve the density estimate. At $\alpha=1$, $A_n$ no longer grows, so this proof gives no finite threshold at the marginal exponent.</p>

<a id="tag-JK7V" data-assertion="theorem" data-title="Finite total crossing intensity forces one-dimensional clusters to be finite"></a>
<p>For a symmetric translation-invariant intensity kernel on $\mathbb Z$, suppose</p>
<div class="math-display">$$B=\sum_{r\geq1}rJ(r)&lt;\infty.$$</div>
<p>At every finite intensity $\beta\geq0$, all open clusters are finite almost surely. In particular $\beta_c=\infty$.</p>
<p><em>Proof.</em> Let $C_j$ be the event that no open edge crosses the cut between $j$ and $j+1$. Exactly $r$ edges of length $r$ cross this cut. Independence and convergence of the intensity sum give</p>
<div class="math-display">$$\mathbb P_\beta(C_j)=e^{-\beta B}=:p&gt;0.$$</div>
<p>The cuts are dependent, but their covariance is explicit. For $k\geq1$, exactly $(r-k)_+$ edges of length $r$ cross both cuts at zero and at $k$. Set $B_k=\sum_{r&gt;k}(r-k)J(r)$. The total intensity of edges crossing at least one of the two cuts is $2B-B_k$, so</p>
<div class="math-display">$$\operatorname{Cov}(\mathbf1_{C_0},\mathbf1_{C_k})=e^{-2\beta B}\bigl(e^{\beta B_k}-1\bigr)\longrightarrow0.$$</div>
<p>Here $B_k\leq\sum_{r&gt;k}rJ(r)\to0$.</p>
<p>Consequently the variance of $N^{-1}\sum_{j=1}^N\mathbf1_{C_j}$ tends to zero: expand it as the sum of covariances and use their Cesàro convergence to zero. Its mean is $p$. Chebyshev's inequality implies that the probability of no cut in $\{1,\ldots,N\}$ tends to zero. By stationarity the same holds for any fixed shifted interval. Taking a countable union over starting points shows that there are cuts arbitrarily far to the right almost surely. The identical argument applies to the left.</p>
<p>Every vertex is therefore enclosed between two closed cuts. No open path can cross either cut, so its cluster is contained in the finite interval between them. This proves the assertion simultaneously for all vertices.</p>
<p>For $J(r)\asymp |r|^{-1-\alpha}$, the hypothesis holds when $\alpha&gt;1$. Together with 65PY, this proves the non-marginal one-dimensional alternatives of the qualitative phase diagram. The case $\alpha=1$, including finite-threshold existence and discontinuity, remains separate. These arguments do not prove absence of an infinite cluster at criticality when $\alpha&lt;1$.</p>

## The finite-set criterion and sharpness {#section-finite-set}

<p>Let $V$ be countable, with a transitive group preserving symmetric nonnegative off-diagonal intensities $J$, and assume $0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty$. Write $q_\beta(x,y)=1-e^{-\beta J(x,y)}$. For a finite set $S\ni o$, set</p>
<div class="math-display">$$\varphi_\beta(S)=\sum_{x\in S,\ y\notin S}q_\beta(x,y)\tau_\beta^S(o,x),$$</div>
<p>where $\tau_\beta^S$ uses paths inside $S$. The sum is finite since it is at most $\beta |S|L$. This is the weighted version of the <a href="/tag/6EIM/">finite-set boundary influence</a>.</p>

<p>This bound is the cardinality-numerator consequence of the <a href="/articles/boundary-laws/">finite-size criterion YLZV</a>. We give an alternative proof using ghost fields.</p>
<p>If $\varphi_\beta(S)&lt;1$, then</p>
<div class="math-display">$$\chi_\beta\leq\frac{|S|}{1-\varphi_\beta(S)}&lt;\infty.$$</div>
<p><em>Proof.</em> Add independent green marks of probability $1-e^{-h}$ at every vertex, and put $G(h)=\mathbb E_\beta[1-e^{-h|K_o|}]\leq1$, with $1-e^{-h\infty}=1$. If $o$ reaches a green vertex outside $S$, take a simple open path to it and split the path at its first exit edge $(x,y)$ from $S$. The internal connection to $x$, the open exit edge and the remaining connection from $y$ to a green vertex have disjoint witnesses, including the mark at the last vertex. BK in the product of bond and mark coordinates, followed by a union bound, gives</p>
<div class="math-display">$$\mathbb P(o\leftrightarrow\mathcal G\setminus S)\leq\sum_{x\in S,y\notin S}\tau_\beta^S(o,x)q_\beta(x,y)G(h)=\varphi_\beta(S)G(h).$$</div>
<p>Transitivity makes the ghost probability at $y$ equal to $G(h)$. Countable BK here follows by finite-coordinate exhaustion of the path and mark witnesses. A green vertex inside $S$ exists with probability $1-e^{-h|S|}$. Thus $G(h)\leq\varphi_\beta(S)G(h)+1-e^{-h|S|}$. Both sides are finite, so rearrangement is legitimate. Divide by $h$ and let $h\downarrow0$; monotone convergence gives the stated bound, including exclusion of an infinite cluster.</p>

<p>The <a href="/articles/finite-size-sharpness/">wired derivative theorem HATE</a> gives the following inequality. We recall its argument for this application.</p>
<p>For a finite $\Lambda\ni o$, let $f_\Lambda(\beta)=\mathbb P_\beta(o\leftrightarrow V\setminus\Lambda)$. Then for $\beta&gt;0$,</p>
<div class="math-display">$$f_\Lambda'(\beta)\geq\frac{1-f_\Lambda(\beta)}{\beta}\min_{o\in S\subseteq\Lambda}\varphi_\beta(S).$$</div>
<p><em>Proof.</em> Replace the exterior by one vertex $\partial$. Keep the bonds inside $\Lambda$ and give $(x,\partial)$ intensity $\sum_{y\notin\Lambda}J(x,y)$. These finite intensities define a finite product model with exactly the required exit probability: the boundary bond is open when at least one of the original bonds from $x$ to the exterior is open. Distinct boundary bonds use disjoint original coordinates.</p>
<p>In this finite graph, let $\mathscr S$ be the vertices of $\Lambda$ not connected to $\partial$. The event $\mathscr S=S$ says that every edge from $S$ to its complement is closed and that every vertex in $\Lambda\setminus S$ connects to $\partial$ in the complement. It depends on no edge internal to $S$. Consequently the internal edges retain their product law on conditioning on this event.</p>
<p>The intensity form of Russo's formula sums $J(e)$ times the probability that $e$ is closed and pivotal. On $\mathscr S=S$ with $o\in S$, a boundary edge from $x\in S$ is closed pivotal exactly when $o$ connects to $x$ inside $S$. Edges elsewhere cannot be closed pivotal. Therefore</p>
<div class="math-display">$$f_\Lambda'(\beta)=\sum_{o\in S\subseteq\Lambda}\mathbb P_\beta(\mathscr S=S)\sum_{x\in S,y\notin S}J(x,y)\tau_\beta^S(o,x).$$</div>
<p>The terms with $y\notin\Lambda$ are the expanded intensities of the aggregated boundary bonds. In particular, the displayed identity involves no differentiation of an infinite product. Since $\beta J(x,y)\geq q_\beta(x,y)$, the inner sum is at least $\varphi_\beta(S)/\beta$. Finally $\sum_{S\ni o}\mathbb P_\beta(\mathscr S=S)=1-f_\Lambda(\beta)$, proving the inequality.</p>

<p>The following argument recalls the <a href="/articles/finite-size-sharpness/">sharpness theorem L0TE</a> and <a href="/articles/finite-size-sharpness/">susceptibility characterization RDF0</a>, supplying the <a href="/tag/DYUM/">weighted sharpness statement</a> in this application. Here is the threshold argument, including the possibility of an infinite threshold. Define</p>
<div class="math-display">$$\widetilde\beta_c=\sup\{\beta\geq0:\varphi_\beta(S)&lt;1\text{ for some finite }S\ni o\}.$$</div>
<p>The certificate set is downward closed because every $\varphi_\beta(S)$ is nondecreasing in $\beta$. It contains $[0,1/L)$ by taking $S=\{o\}$. For every $\beta&lt;\widetilde\beta_c$, a certificate at a larger parameter is also a certificate at $\beta$; the ghost-field certificate bound gives finite susceptibility. Hence $b_\chi,\beta_c\geq\widetilde\beta_c$. If $\widetilde\beta_c=\infty$, all finite parameters have finite susceptibility and both thresholds are infinite.</p>
<p>Otherwise, for $\beta&gt;\widetilde\beta_c$ every finite $S\ni o$ has $\varphi_\beta(S)\geq1$. By the wired derivative inequality, $(\beta f_\Lambda(\beta))'\geq1$ throughout this interval. Integrating from $t\in(\widetilde\beta_c,\beta)$ and using $f_\Lambda(t)\geq0$ gives $f_\Lambda(\beta)\geq1-t/\beta$. Let $t\downarrow\widetilde\beta_c$ and then exhaust $V$ by finite $\Lambda$. The exit events decrease to the event that $K_o$ is infinite, since every finite cluster is contained in some member of the exhaustion. Thus</p>
<div class="math-display">$$\theta(\beta)\geq1-\frac{\widetilde\beta_c}{\beta}\qquad(\beta&gt;\widetilde\beta_c).$$</div>
<p>It follows that $\beta_c\leq\widetilde\beta_c$. Since positive infinite-cluster probability forces infinite susceptibility, $b_\chi\leq\beta_c$ as well. All three thresholds are equal. At a finite threshold, <a href="/tag/5LNL/">right-openness</a> gives $\chi_{\beta_c}=\infty$; the argument does not determine $\theta(\beta_c)$.</p>
<p>At every subcritical parameter, transitivity makes the finite susceptibility uniform. The <a href="/tag/XLWI/">weighted exponential-moment bound</a> then gives exponential cluster-volume tails, for example</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|\geq n)\leq\frac{\sqrt2\chi_\beta}{n}\exp\!\left(-\frac{n}{4\chi_\beta^2}\right)\qquad(n\geq1).$$</div>
<p>The prefactor is retained: a bound $e^{-cn}$ with $c&gt;0$ cannot hold at $n=1$. This completes the finite-set and outside-exploration proof in the countable transitive summable setting. For the normalized power-law model, EBVV and 65PY give $b_\chi=\beta_c&lt;\infty$ whenever $d&gt;3\alpha$: use the plane for $d\geq2$, and the growing-block construction for $d=1$, where $\alpha&lt;1/3$. This identifies the parameter in the high-dimensional cutoff and volume-tail conclusions with the percolation threshold in every allowed dimension. No exponential decay in Euclidean distance is claimed for an infinite-range kernel.</p>

## Nearest-neighbour consequences {#section-nearest-consequences}

<a id="tag-IU3W" data-assertion="proposition" data-title="Supercritical lower bound in the homogeneous bond probability"></a>
<p>For homogeneous nearest-neighbour bond percolation on an infinite connected locally finite transitive graph with $p_c&lt;1$,</p>
<div class="math-display">$$\theta(p)\geq\frac{p-p_c}{p(1-p_c)}\qquad(p_c&lt;p\leq1).$$</div>
<p><em>Proof.</em> Write $\varphi_p(S)=p\sum_{x\in S,y\notin S,\,x\sim y}\tau_p^S(o,x)$. The intensity substitution $\beta=-\log(1-p)$ identifies this with the finite-set functional above. Hence $\varphi_p(S)\geq1$ for every finite $S\ni o$ when $p&gt;p_c$.</p>
<p>For the finite-volume exit probability $f_\Lambda(p)$, repeat the wired-boundary calculation recalled above. Now Russo's formula weights a closed-pivotal event by $1/(1-p)$, giving</p>
<div class="math-display">$$f_\Lambda'(p)\geq\frac{1-f_\Lambda(p)}{p(1-p)}\qquad(p_c&lt;p&lt;1).$$</div>
<p>Here only finitely many boundary edges occur, and they may be kept as separate coordinates. Since all those edges can be closed with positive probability, $f_\Lambda(p)&lt;1$. Integrating from $t\in(p_c,p)$ yields</p>
<div class="math-display">$$1-f_\Lambda(p)\leq(1-f_\Lambda(t))\frac{t(1-p)}{p(1-t)}\leq\frac{t(1-p)}{p(1-t)}.$$</div>
<p>Let $t\downarrow p_c$ and exhaust the graph by $\Lambda$. At $p=1$ the graph is connected and infinite, so $\theta(1)=1$.</p>

<a id="tag-468P" data-assertion="proposition" data-title="Lower semicontinuity of the bond threshold under local graph convergence"></a>
<p>Let $(G_n,o_n)$ and $(G,o)$ be infinite connected locally finite transitive graphs. Suppose every fixed-radius rooted ball of $G_n$ is eventually isomorphic to that of $G$. For homogeneous nearest-neighbour bond percolation,</p>
<div class="math-display">$$\liminf_{n\to\infty}p_c(G_n)\geq p_c(G).$$</div>
<p><em>Proof.</em> Fix $0\leq p&lt;p_c(G)$. The finite-set characterization gives a finite $S\ni o$ with $\varphi_p^G(S)&lt;1$. Choose $R$ with $S\subseteq B_R(o)$. A rooted isomorphism on radius $R+1$ transports $S$, every internal edge and every incident boundary edge. It therefore preserves both the restricted connection probabilities and the finite boundary sum: $\varphi_p^{G_n}(S_n)=\varphi_p^G(S)&lt;1$ for all large $n$. The certificate bound gives finite susceptibility on $G_n$, so $p\leq p_c(G_n)$. Let $p\uparrow p_c(G)$.</p>
<p>These are the nearest-neighbour and local-convergence consequences discussed in <a href="https://arxiv.org/pdf/1502.03050v3#page=3">Section 1.2 of arXiv:1502.03050v3</a>. The parameter here is the edge probability $p$, not the unbounded intensity $\beta$. The local argument proves only the displayed lower semicontinuity; it supplies no upper semicontinuity or statement about current locality results.</p>

## Scope of the application {#section-source}

<p>The argument above supplies the calculus passage conditional on the displayed differential inequality and regularity assumptions. For a percolation application, $D$ is the triangle diagram, whose diagonal term is one, but the probabilistic differential inequality and its graph hypotheses must first be established.</p>
<p>The planar comparison above proves finiteness of the critical parameter for its specified kernels. The finite-set argument also establishes sharpness in the stated transitive summable setting. The quantitative triangle theorem remains separate. Local regularity is proved for the transitive intensity model where susceptibility is finite; the reciprocal triangle estimate separately states the analytic regularity it needs. It also does not replace a slowly divergent diagram by a bounded one: the loss of $(\log(1/\varepsilon))^{2a}$ is retained.</p>

<p>A separate <a href="/tag/4KBG/">quadratic triangle bound</a> now supplies a probabilistic lower derivative estimate under mass transport. It suffices for the bounded-triangle susceptibility exponent but has a weaker numerator than the hypothesis of the integrated quantitative estimate above. The two formulas are not interchangeable.</p>

<p>The <a href="/tag/MTYL/">normalized-line counterexample</a> rules out the stronger formula as a bound valid at every positive subcritical intensity. The conditional calculus statements above remain implications under their displayed hypotheses; they are not evidence that the stronger formula holds throughout a percolation parameter interval.</p>


## Scope of the deterministic deletion bound {#section-deletion-source}

<p>The source implementation of <a href="/tag/7902/">7902</a> allows an arbitrary deterministic $S\subseteq V$, including an infinite set, and does not require either endpoint to lie outside $S$. If $y\in S$, then $\tau^S(y,w)=0$, while the term indexed by $c=y$ on the right is $\tau(y,y)\tau(y,w)=\tau(y,w)$. The case $w\in S$ is the same. Empty path segments are legitimate disjoint witnesses in these cases. When $S=\varnothing$, the deleted graph is the whole graph and the inequality is an equality.</p>
<p>No finite-susceptibility hypothesis enters this comparison. The sum over $S$ is nonnegative and may be infinite. Countability is needed when taking the union over possible path-intersection vertices and applying countable BK; the deterministic path decomposition itself does not need it. The deleted susceptibility bound $\sum_w\tau^S(y,w)\leq\chi(y)$ follows by summing the event inclusion, still with infinite values allowed.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-boundary/">new boundary-source inventory</a> records this deterministic-set argument separately from the conditional law of the complement of a revealed cluster. That conditional law and the five-factor estimate J1LW require the additional exploration and tree-graph arguments already given above; they are not consequences supplied by the deletion module alone.</p>

## Endpoint and ambient scope of the finite-volume derivative {#section-derivative-source}

<p>The source proof of <a href="/tag/TAVM/">TAVM</a> works inside a finite set $F$ of an arbitrary ambient vertex type. Restriction to the finitely many unordered pairs in $F$ gives a finite product law, so no countability assumption on the ambient space is needed. Pivotality supplies a simple path after opening the pivotal edge. Removing that edge splits the path into two finite open witnesses in the original configuration, one for each of the two connection events. The witnesses share no edges, although their endpoints may coincide.</p>
<p>The source writes the Russo term for an unordered edge $e$ as $J_e e^{-\beta J_e}\mathbb P_\beta(e\text{ pivotal})$. This equals $J_e\mathbb P_\beta(e\text{ closed and pivotal})$, since pivotality does not inspect the state of $e$. It bounds the unconditional pivotal probability by the sum for the two orientations and then uses $e^{-\beta J_e}\leq1$. Summing those two orientations over unordered edges gives precisely the ordered sum over $u\ne v$ in the proof of TAVM, with no additional factor two. Loops cannot be pivotal and contribute nothing.</p>
<p>The same finite-product calculation gives a right derivative at $\beta=0$. There every off-diagonal bond is closed, and a single opened edge joins $o$ to another vertex only when that edge is incident to $o$. Thus</p>
<div class="math-display">$$\left.\frac{d}{d\beta^+}\chi_F(o,\beta)\right|_{\beta=0}
=\sum_{v\in F\setminus\{o\}}J(o,v)\leq R_F,$$</div>
<p>consistent with $\chi_F(o,0)=M_F(0)=1$. For $F=\{o\}$ the derivative is zero at every intensity. For two vertices with proper-edge weight $j$, $\chi_F(o,\beta)=2-e^{-\beta j}$ and its derivative is $je^{-\beta j}$, including the right derivative at zero. Diagonal weights do not enter either example. The source extends the parameter to negative real numbers by replacing it with its nonnegative part, so at zero it asserts only the derivative within $[0,\infty)$; the ordinary two-sided derivative is asserted for $\beta&gt;0$.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-susceptibility/">eleven-contract derivative inventory</a> ends at this finite-volume upper bound. The passage to infinite volume, the two-cluster identity, and the lower derivative estimates above have additional arguments and are not exports of that file.</p>


## Reciprocal control by subdivision {#section-regularity-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-susceptibility-layer/">Train 8 source</a> extends the earlier finite-volume derivative implementation to the local regularity and reciprocal estimate in <a href="/tag/MXGM/">MXGM</a>. It first integrates the finite-volume bound and then takes the supremum over an exhaustion. Throughout this passage, the full susceptibility is finite on the open interval under consideration; monotonicity bounds the integrand on every compact subinterval. No derivative of an infinite sum is assumed.</p>
<p>There is a useful direct proof of the reciprocal estimate. Fix $a&lt;s&lt;t&lt;b$ and put $C=R\chi(t)^2$. For $s\leq u\leq v\leq t$, the integrated inequality and monotonicity give</p>
<div class="math-display">$$0\leq\chi(v)-\chi(u)\leq R(v-u)\chi(v)^2\leq C(v-u).$$</div>
<p>Since $\chi(u)\geq1$, we also have $\chi(v)/\chi(u)\leq1+C(v-u)$. Dividing the first bound by $\chi(u)\chi(v)$ therefore yields</p>
<div class="math-display">$$\frac1{\chi(u)}-\frac1{\chi(v)}
\leq R(v-u)+RC(v-u)^2.$$</div>
<p>Divide $[s,t]$ into $N$ equal intervals and add these inequalities. The left side telescopes, while the quadratic errors sum to $RC(t-s)^2/N$. Letting $N\to\infty$ proves $\chi(s)^{-1}-\chi(t)^{-1}\leq R(t-s)$. More generally, this subdivision argument removes any uniform quadratic error in a one-sided increment bound; it requires no continuity assumption on the function being compared.</p>
<p>The source proves almost-everywhere differentiability separately by applying the one-dimensional Lipschitz differentiation theorem on a countable family of compact subintervals covering $(a,b)$. At any point where the derivative exists, the displayed increment bound and continuity at that point give $0\leq\chi'\leq R\chi^2$. These source conclusions allow $R=0$ as well as positive finite $R$. They do not yet export the endpoint blow-up clause of MXGM, whose additional argument above uses $\chi(b)=\infty$. The earlier eleven-contract inventory remains a record of the shorter source at its older revision.</p>

## The small-field limit in the layer bound {#section-layer-limit-source}

<p>The implementation of <a href="/tag/MLLO/">MLLO</a> proves the same susceptibility estimate by a slightly different limiting argument. Under its hypotheses, write $T$ for the union-cluster volume at $v$ and $K=\chi_0(v)/(1-\delta M)&lt;\infty$. The ghost estimate gives, for every $h&gt;0$,</p>
<div class="math-display">$$\mathbb P(T=\infty)\leq G_v(h)\leq hK.$$</div>
<p>Letting $h\downarrow0$ first proves $T&lt;\infty$ almost surely. The elementary inequality $hT e^{-hT}\leq1-e^{-hT}$ then gives $\mathbb E[T e^{-hT}]\leq K$. Fatou along $h_n=1/(n+1)$ yields $\mathbb E T\leq K$, because $T e^{-h_nT}\to T$ at each finite value of $T$. The order matters: with the source convention $\infty\cdot0=0$, the latter convergence fails at $T=\infty$. The direct monotone-convergence proof of MLLO above uses $(1-e^{-hT})/h$ and includes infinite volumes without this preliminary step.</p>
<p>The bound permits a uniform finite upper bound $M$ for red susceptibility and an upper bound $\delta$ for the blue rows, rather than requiring either to be the exact supremum. At any chosen root, $M\geq\chi_0(v)\geq1$, so $\delta M&lt;1$ also forces $\delta&lt;\infty$. No transitivity is used. Only the red root cluster's almost-sure finiteness is needed for the more general <a href="/tag/BEJT/">ghost comparison</a>; a finite red mean enters when deriving MLLO.</p>
<p>For <a href="/tag/5LNL/">5LNL</a>, transitivity turns finite rooted susceptibility into a uniform bound, and the independent intensity-$\varepsilon$ layer has probability rows at most $\varepsilon L$. The new source exports the quantitative step, its finite-susceptibility consequence, existence of a positive admissible step, and $b_\chi\geq L^{-1}$. Its extended-value formulation also allows $L=0$: all proper intensities then vanish, $\chi_\beta=1$ at every finite parameter, and $b_\chi=\infty$. The finite-threshold divergence argument in 5LNL remains an additional prose argument, not an export of this source file.</p>


## The finite endpoint in the logarithmic bound {#section-log-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-scales/">logarithmic source</a> implements <a href="/tag/6PGV/">6PGV</a> with a finite real endpoint, a positive nondecreasing locally absolutely continuous function and a measurable finite-valued $D\geq1$. The parameter called the critical point in the application is only an endpoint in this analytic theorem.</p>
<p>The endpoint passage discards the nonnegative terminal reciprocal; it does not require that reciprocal to tend to zero. The integral is finite because its integrand is at most $1/(3\beta^2)$ on the interval starting at the fixed positive $\beta$, and it is strictly positive because $D$ is finite. A logarithmic bound on $D$ then gives the power $2a$ through its square in the denominator. Thus this source proves an upper bound under a differential inequality, without proving critical divergence or supplying the percolation inequality itself.</p>


## The endpoint clauses now supplied by the source {#section-endpoint-source}

<p>The separate <a href="/coverage/sources/perclib-f51f639-endpoints/">Train 9 endpoint module</a> now proves the endpoint clauses of <a href="/tag/5LNL/">5LNL</a> and <a href="/tag/MXGM/">MXGM</a> that were outside the earlier source exports described above. If the susceptibility threshold $b_\chi$ is finite and its susceptibility were finite, right-openness would give another finite-susceptibility parameter strictly above the supremum. This contradiction proves $\chi(b_\chi)=\infty$.</p>
<p>For the quantitative conclusion, suppose $\chi$ is finite on $(a,b)$ and infinite at $b$. A finite-domain susceptibility can exceed any prescribed constant at $b$; its continuity keeps it large just below $b$. Since it is bounded above by the full susceptibility, there are parameters $t\uparrow b$ with $\chi(t)$ arbitrarily large. This step needs no transitivity or row-sum bound. Under the transitivity and positive finite row sum $R$ of MXGM, the reciprocal inequality then gives</p>
<div class="math-display">$$\frac1{\chi(\beta)}\leq R(b-\beta),\qquad a&lt;\beta&lt;b.$$</div>
<p>The source supplies a concrete model satisfying these endpoint hypotheses: the unit-intensity Cayley graph of the free group of rank two. Left multiplication preserves its kernel, and its intensity row is positive and finite. For $\beta\geq1$, each edge has probability at least $1/2$. The $2^n$ positive words of length $n$ are distinct vertices with connection probability at least $2^{-n}$, so summing over all lengths proves infinite susceptibility. The row bound gives a nonempty interval of finite susceptibility, and right-openness identifies a finite positive endpoint. No exact value of this endpoint, or equality with a percolation threshold in general, is needed for the witness.</p>


## Sharpness for displacement kernels {#section-model-sharpness-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-cutoff-locality/">long-range sharpness source</a> now applies the transitive theorem to displacement kernels on countable additive groups. Finite total displacement mass gives summable rows by translation; the same translations identify the root and global thresholds. Susceptibility is therefore finite at every vertex at every finite intensity strictly below the global threshold.</p>
<p>The lattice specialization covers the sup-norm power kernel with exponent $d+\alpha$, for $d\geq1$ and $\alpha&gt;0$, and retains the lower bound on the threshold from the reciprocal total mass. Its hierarchical specialization uses the sufficient condition $2L^d r\leq1$ for the geometric kernel. The general group theorem can instead use the exact summability condition from the <a href="/articles/hierarchical-lattice/#section-full-radial">radial sum</a>. Neither specialization identifies the threshold or settles critical percolation.</p>

## The extra layer in local convergence {#section-local-convergence-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-cutoff-locality/">local-convergence source</a> implements the certificate transport in <a href="/tag/468P/">468P</a>. Internal connections depend only on bonds inside the certificate $S$, but its boundary functional also sees every bond incident to $S$. A rooted isomorphism on a ball one layer larger than a ball containing $S$ captures these bonds on both graphs. The source proves the equality of boundary functionals before applying sharpness.</p>
<p>The threshold conclusion is stated in intensity, as $\beta_c(G,o)\leq\liminf_n\beta_c(G_n,o_n)$. The source allows a connected locally finite limit without assuming it transitive; its contraction-supremum inequality supplies a finite certificate below the root threshold. The approximating graphs are locally finite and transitive, so the transported strict contraction forces their thresholds above the chosen parameter. All vertex sets are countable in this statement.</p>
<p>For the infinite transitive graphs in 468P, the change of parameter $p=1-e^{-\beta}$ gives the displayed probability-threshold conclusion. This increasing continuous map includes $\beta=\infty$ by assigning $p=1$, so infinite intensity thresholds cause no endpoint loss. The argument supplies lower semicontinuity only.</p>

## Transporting two distinct clusters through an added layer {#section-two-cluster-transport}

<a id="tag-5FCO" data-assertion="theorem" data-title="An independent intensity increment controls the growth of two distinct clusters"></a>
<p>Let $k_0\leq k_1$ be nonnegative finite edge intensities on a countable vertex set, with independent opening probabilities $1-e^{-k_i(e)}$. Suppose the larger law has uniformly bounded susceptibility $L=\sup_x\mathbb E_1|K_x|&lt;\infty$, and put</p>
<div class="math-display">$$\Delta=\sup_u\sum_{v\ne u}(k_1(u,v)-k_0(u,v))&lt;\infty,\qquad
\rho_i(u,v)=\mathbb E_i[|K_u||K_v|\mathbf1_{\{u\nleftrightarrow v\}}].$$</div>
<p>Then, for every pair of roots,</p>
<div class="math-display">$$\rho_1(u,v)\leq(1+\Delta L)^2\rho_0(u,v).$$</div>
<p><em>Proof.</em> First take a finite graph. Construct the larger configuration by adding to the smaller one an independent layer with intensities $\delta=k_1-k_0$. Reveal the two smaller clusters $U=K_u^0$ and $V=K_v^0$. If they coincide, the two roots also belong to the same larger cluster, so their contribution vanishes. Otherwise, all smaller-law edges leaving either set are closed, and the smaller-law edges with both endpoints outside $U\cup V$ retain their independent original laws. The added layer is still independent of this information.</p>
<p>On the event that the larger root clusters are distinct, an open path from $u$ to $x\notin U$ has a last exit from $U$, say along $\{a,b\}$ with $a\in U$. This edge must come from the added layer. The remaining path lies outside $U\cup V$: it never returns to $U$ by the choice of exit, and cannot meet $V$ because the larger clusters are distinct. The same construction applies to a path from $v$ to $z\notin V$. The two resulting witnesses use disjoint edge coordinates, since they lie in distinct larger clusters. If $x\in U$ or $z\in V$, use an empty witness for the corresponding connection.</p>
<p>Conditional on $U,V$, BK on the remaining product coordinates and a union bound over the exit edges therefore give</p>
<div class="math-display">$$\begin{aligned}
&\mathbb P(u\nleftrightarrow_1v,\ u\leftrightarrow_1x,\ v\leftrightarrow_1z\mid U,V)\\
&\quad\leq
\left[\mathbf1_{\{x\in U\}}+\sum_{a\in U}\sum_{b\notin U\cup V}\delta(a,b)\tau_1(b,x)\right]
\left[\mathbf1_{\{z\in V\}}+\sum_{c\in V}\sum_{d\notin U\cup V}\delta(c,d)\tau_1(d,z)\right].
\end{aligned}$$</div>
<p>Here $1-e^{-\delta(e)}\leq\delta(e)$ bounds the added-edge probability. The continuation starts at the outside endpoint of that edge. Deleting $U\cup V$ only lowers its connection probability, so the full-law factors displayed above are valid upper bounds. Sum over $x,z$: the two brackets have sums at most $|U|(1+\Delta L)$ and $|V|(1+\Delta L)$. Averaging proves the finite-graph inequality.</p>
<p>For a countable graph, exhaust its edges by finite sets. The larger full clusters are finite almost surely, and the restricted clusters at either root eventually equal their full counterparts. The products are dominated by $|K_u^1||K_v^1|$, which is integrable: the <a href="/tag/Y84V/">uniform tree-graph bound</a> gives finite second moments, and Cauchy–Schwarz bounds the product. Dominated convergence therefore passes both sides to the limit. The uniform susceptibility and increment row bounds apply to every restriction.</p>
<p>The continuation endpoints and the row-summation index in the source's display (III.3.15) need correction; see the <a href="/errata/hutchcroft-lrp-3/#added-layer-endpoints">provisional entry</a>. The aggregate estimate above is the form used for cutoff derivatives.</p>



## The inverse-square density constraint {#section-marginal-density-input}

<a id="tag-67W9" data-assertion="theorem" data-title="A positive one-dimensional percolation density requires a large inverse-square tail coefficient"></a>
<p>Consider independent translation-invariant bonds on $\mathbb Z$, with symmetric opening probabilities $q(k)&lt;1$ for every $k\ne0$. Put $L_q=\limsup_{n\to\infty}n^2q(n)&lt;\infty$ and $\theta=\mathbb P(|K_0|=\infty)$. Then</p>
<div class="math-display">$$\theta&gt;0\quad\Longrightarrow\quad L_q\theta^2\geq1.$$</div>
<p>This is the independent-model statement of <a href="https://doi.org/10.1007/BF01205489">Aizenman–Newman, Proposition 1.1, pp. 613–614, equations (1.5)–(1.6)</a>. Their regularity assumption is $q(k)&lt;1$. A complete proof is given below.</p>
<p><em>Idea of the proof.</em> Suppose $\theta&gt;0$ and $L_q\theta^2&lt;1$, and choose $\theta'&gt;\theta$ and $L'&gt;L_q$ with $L'\theta'^2&lt;1$; then $q(n)\leq L'/n^2$ for all large $n$. Two adjacent intervals of length $N$, each containing a connected set of density at most about $\theta'$, are joined directly by an open edge with probability roughly $1-N^{-L'\theta'^2}$, since the sum of $n^{-2}$ over pairs of points in the two intervals grows like $\theta'^2\log N$. Because the exponent $L'\theta'^2$ is less than one, these failures are frequent on all scales. A renormalization inequality for the probability that a block of length $3K$ is not crossed by open paths made of edges of length at most $K$ shows that this probability stays bounded below along a geometric sequence of scales. Together with the positive probability, guaranteed by $q(k)&lt;1$ and $\sum_kq(k)&lt;\infty$, that no long edge leaves a large interval, this keeps the probability that some vertex is connected to infinity bounded away from one, contradicting the zero–one law for the existence of an infinite cluster. This sketch follows the shorter proof of Theorem 1(ii) in <a href="https://arxiv.org/html/2011.04642v2">Duminil-Copin–Garban–Tassion, Section 2.4 and Lemma 3</a>, written there for the kernel of the next theorem, inverse-square weights with a separate nearest-neighbour parameter. The proposition and its original renormalization proof are in Aizenman–Newman, cited above.</p>
:::details Proof
<p>Each edge $\{x,y\}$, $x\ne y$, is open with probability $q(y-x)$, independently of all other edges; symmetry of $q$ makes this well defined, and every translation $x\mapsto x+a$ preserves the law $\mathbb P$. Write $[a,b)=\{a,a+1,\ldots,b-1\}$ for integers $a&lt;b$, and call $|y-x|$ the length of $\{x,y\}$. Suppose, for a contradiction, that $\theta&gt;0$ and $L_q\theta^2&lt;1$.</p>
<p><em>Step 0: constants.</em> Choose $L'&gt;L_q$ and $\bar\theta&gt;\theta$ with $s:=L'\bar\theta^2&lt;1$. Since $L'&gt;L_q$, there is $n_0\geq1$ with</p>
<div class="math-display">$$q(n)\leq\frac{L'}{n^2}\leq\frac12\qquad(n\geq n_0).$$</div>
<p>For $R\geq1$ put $\theta_R=\mathbb P(0\leftrightarrow\mathbb Z\setminus[-R,R))$. These events decrease in $R$, and their intersection is $\{|K_0|=\infty\}$, since the cluster $K_0$ meets $\mathbb Z\setminus[-R,R)$ for every $R$ exactly when it is infinite: every finite set lies in some $[-R,R)$. Hence $\theta_R\downarrow\theta$, and we fix $R$ with $\theta_R&lt;\bar\theta$. Fix an integer $K_*\geq\max\{n_0,2R\}$ with</p>
<div class="math-display">$$\theta_R^2+\frac{4R^2L'}{25K_*^2}\leq\bar\theta^2,$$</div>
<p>and an integer $C_*\geq15$ such that $(1-e^{-1})e^{-1-40L'}C^{1-s}/9\geq1$ for every $C\geq C_*$; this is possible because $s&lt;1$. Two elementary bounds are used repeatedly. If $K\geq n_0$, then</p>
<div class="math-display">$$\sum_{k&gt;K}q(k)\leq L'\sum_{k&gt;K}\frac1{k^2}\leq L'\int_K^\infty\frac{dx}{x^2}=\frac{L'}K.$$</div>
<p>If $0\leq t\leq\frac12$, then $-\log(1-t)=\sum_{j\geq1}t^j/j\leq t+\frac{t^2}2\sum_{j\geq0}t^j\leq t+t^2\leq2t$. Consequently, for $K\geq n_0$ and any set $E$ of edges of length greater than $K$, independence gives $\mathbb P(\text{all edges of }E\text{ closed})=\prod_{e\in E}(1-q_e)\geq\exp(-2\sum_{e\in E}q_e)$, the infinite product being the limit of the finite ones.</p>
<p><em>Step 1: crossings.</em> For an integer $K\geq1$, call an edge <em>short</em> if its length is at most $K$. For $i\in\mathbb Z$ put $\alpha_i=3K(i-1)$, $\beta_i=3K(i+1)$ and $B^i_{3K}=[\alpha_i,\beta_i)$. The block $B^i_{3K}$ is <em>$K$-crossed</em> if some $x&lt;\alpha_i$ is joined to some $y\geq\beta_i$ by an open path of short edges. Put</p>
<div class="math-display">$$\bar p(K)=1-\mathbb P(B^0_{3K}\text{ is }K\text{-crossed}).$$</div>
<p>By translation invariance, each $B^i_{3K}$ fails to be $K$-crossed with probability $\bar p(K)$. Let $W_i=[3Ki-4K,3Ki+4K)$. <em>Claim: $B^i_{3K}$ is $K$-crossed if and only if some open path of short edges with all its vertices in $W_i$ joins a vertex below $\alpha_i$ to a vertex at least $\beta_i$; in particular the event is determined by the short edges with both endpoints in $W_i$.</em> Let $v_0,\ldots,v_m$ be an open path of short edges with $v_0&lt;\alpha_i$ and $v_m\geq\beta_i$. Let $t$ be the first index with $v_t\geq\beta_i$ and $s$ the last index below $t$ with $v_s&lt;\alpha_i$. Then $v_{s+1},\ldots,v_{t-1}\in[\alpha_i,\beta_i)$. Since $\beta_i-\alpha_i=6K&gt;K$, the edge $\{v_s,v_t\}$ cannot be short, so $t\geq s+2$, and then $v_s\geq v_{s+1}-K\geq\alpha_i-K$ and $v_t\leq v_{t-1}+K&lt;\beta_i+K$. The subpath $v_s,\ldots,v_t$ lies in $[\alpha_i-K,\beta_i+K)=W_i$. The converse is trivial. The windows $W_i$, $i\in3\mathbb Z$, are pairwise disjoint, since their centres are at distance at least $9K$ and each has length $8K$.</p>
<p><em>Step 2: the renormalization inequality. Claim: for all integers $K\geq K_*$ and $C\geq C_*$,</em></p>
<div class="math-display">$$\bar p(CK)\geq\min\{\bar p(K),C^{-1}\}.$$</div>
<p>Fix such $K$ and $C$. Call an edge <em>long</em> if its length lies in $(K,CK]$. For an edge $\{x,y\}$ let $A_x^y$ be the event that $x$ is joined to $\mathbb Z\setminus[x-R,x+R)$ by an open path of edges of length at most $CK$ that does not use $\{x,y\}$. Following such a path up to its first exit from $[x-R,x+R)$ shows that $A_x^y$ is determined by the finitely many edges of length at most $CK$, other than $\{x,y\}$, that have an endpoint in $[x-R,x+R)$; it is increasing. A <em>bridge</em> is an open long edge $\{x,y\}$ for which $A_x^y$ and $A_y^x$ both occur.</p>
<p>Let $m=\lfloor(C-3)/9\rfloor$ and $I=\{3j:j\in\mathbb Z,\ |j|\leq m\}$. For $i\in I$ we have $|i|\leq C/3-1$, so $B^i_{3K}\subseteq[-CK,CK)$; moreover $|I|=2m+1$ satisfies $C/9\leq(2C-15)/9\leq|I|\leq C$, using $C\geq15$. Put $V_i=[3Ki-5K,3Ki+5K)\supseteq W_i$. For $i\in I$, call $B^i_{3K}$ <em>bridged</em> if (a) some bridge $\{x,y\}$ has $x&lt;\alpha_i$ and $y\geq\beta_i$, or (b) some open long edge has an endpoint in $V_i$. Let $U$ be the random set of $i\in I$ for which $B^i_{3K}$ is not bridged.</p>
<p>(i) <em>If $B^0_{3CK}$ is $CK$-crossed, then for every $i\in I$ the block $B^i_{3K}$ is bridged or $K$-crossed.</em> Take an open path $v_0,\ldots,v_{m'}$ with $v_0&lt;-3CK$ and $v_{m'}\geq3CK$, all of whose edges have length at most $CK$, and choose it with the fewest edges, so that its vertices are distinct. Define $t$ and $s$ for the block $B^i_{3K}$ as in Step 1, so that $v_s&lt;\alpha_i$, $v_t\geq\beta_i$ and $v_{s+1},\ldots,v_{t-1}\in[\alpha_i,\beta_i)$. If $t=s+1$, the edge $\{v_s,v_t\}$ has length at least $6K&gt;K$ and at most $CK$, so it is an open long edge. Since $v_s\geq v_t-CK\geq\beta_i-CK&gt;-2CK$, the path $v_s,v_{s-1},\ldots,v_0$ ends at distance greater than $CK\geq R$ from $v_s$, and it does not use $\{v_s,v_t\}$ because $v_t$ is not among $v_0,\ldots,v_s$; so $A_{v_s}^{v_t}$ occurs. Likewise $v_t\leq v_s+CK&lt;\alpha_i+CK&lt;2CK$, and the path $v_t,\ldots,v_{m'}$ gives $A_{v_t}^{v_s}$. So $\{v_s,v_t\}$ is a bridge as in (a). If $t\geq s+2$, every edge of $v_s,\ldots,v_t$ has an endpoint in $[\alpha_i,\beta_i)\subseteq V_i$. If one of them is long, (b) holds. Otherwise all are short and $B^i_{3K}$ is $K$-crossed.</p>
<p>(ii) <em>For every $J\subseteq I$,</em></p>
<div class="math-display">$$\mathbb P\bigl(U=J,\ B^j_{3K}\text{ is }K\text{-crossed for all }j\in J\bigr)=\mathbb P(U=J)\,(1-\bar p(K))^{|J|}.$$</div>
<p>Let $S_J$ be the set of short edges with both endpoints in $\bigcup_{j\in J}W_j$. We show that $\{U=J\}$ is unchanged when the states of the edges in $S_J$ are altered. Let $\omega,\tilde\omega$ agree off $S_J$, and suppose $U(\omega)=J$. No edge of $S_J$ is long, so the open long edges are the same in both configurations, and by (b) in $\omega$ none of them has an endpoint in $\bigcup_{j\in J}V_j$. Let $\{x,y\}$ be an open long edge. An edge with an endpoint $u\in[x-R,x+R)$ satisfies $|u-x|\leq R\leq K$ while $x\notin V_j=[3Kj-5K,3Kj+5K)$, hence $u\notin[3Kj-4K,3Kj+4K)=W_j$ for every $j\in J$, and so the edge is not in $S_J$. Thus $A_x^y$ and $A_y^x$ have the same value in $\omega$ and $\tilde\omega$, the two configurations have the same bridges, and conditions (a) and (b) have the same value for every $i\in I$. So $U(\tilde\omega)=J$, and by symmetry the event $\{U=J\}$ is invariant under changes in $S_J$. A product-measurable event with this invariance is measurable with respect to the coordinates outside $S_J$ (it is the preimage of a section). By Step 1, the crossing events for $j\in J$ are determined by the disjoint sets of short edges inside the windows $W_j$, all contained in $S_J$. Independence of the disjoint families of coordinates (those outside $S_J$, and for each $j\in J$ the short edges inside $W_j$) gives the identity.</p>
<p>(iii) <em>Reduction to $\mathbb E|U|$.</em> By (i), if $B^0_{3CK}$ is $CK$-crossed then every block with index in $U$ is $K$-crossed. Summing (ii) over the finitely many $J\subseteq I$,</p>
<div class="math-display">$$1-\bar p(CK)\leq\mathbb E\bigl[(1-\bar p(K))^{|U|}\bigr].$$</div>
<p>Put $t=\min\{\bar p(K),C^{-1}\}$. Since $|U|\leq|I|\leq C$, we have $t|U|\leq1$. Convexity gives $e^{-u}\leq1-(1-e^{-1})u$ for $u\in[0,1]$, so $(1-\bar p(K))^{|U|}\leq(1-t)^{|U|}\leq e^{-t|U|}\leq1-(1-e^{-1})t|U|$, and</p>
<div class="math-display">$$\bar p(CK)\geq(1-e^{-1})\,t\,\mathbb E|U|.$$</div>
<p>(iv) <em>Bridge probabilities.</em> Let $\{x,y\}$ be an edge with $x&lt;\alpha_i$, $y\geq\beta_i$ and $d=y-x\leq CK$, so $d\geq6K$. The events $A_x^y$ and $A_y^x$ do not involve the edge $\{x,y\}$, so</p>
<div class="math-display">$$\mathbb P(\{x,y\}\text{ is a bridge})=q(d)\,\mathbb P(A_x^y\cap A_y^x).$$</div>
<p>The boxes $Q_x=[x-R,x+R)$ and $Q_y=[y-R,y+R)$ are disjoint. Let $E'$ be the set of edges of length at most $CK$, other than $\{x,y\}$, with one endpoint in $Q_x$ and the other in $Q_y$, and let $G$ be the event that all edges of $E'$ are closed. Let $\hat A_x$ be the event that $x$ is joined to $\mathbb Z\setminus Q_x$ by an open path of edges of length at most $CK$, none in $E'\cup\{\{x,y\}\}$, each with an endpoint in $Q_x$; define $\hat A_y$ likewise. On $G$, the initial segment up to the first exit of a path realizing $A_x^y$ realizes $\hat A_x$, so $A_x^y\cap A_y^x\cap G\subseteq\hat A_x\cap\hat A_y$. An edge with an endpoint in each box lies in $E'\cup\{\{x,y\}\}$, so $\hat A_x$ and $\hat A_y$ are determined by disjoint sets of edges and are independent. Each is contained in a translate of $\{0\leftrightarrow\mathbb Z\setminus[-R,R)\}$, so has probability at most $\theta_R$. An edge of $E'$ has length at least $d-2R+1&gt;5K\geq n_0$, because $R\leq K/2$, and $|E'|\leq4R^2$. Hence</p>
<div class="math-display">$$\mathbb P(A_x^y\cap A_y^x)\leq\mathbb P(G^c)+\mathbb P(\hat A_x)\mathbb P(\hat A_y)\leq\frac{4R^2L'}{25K^2}+\theta_R^2\leq\bar\theta^2,$$</div>
<p>by the choice of $K_*$. Therefore $\mathbb P(\{x,y\}\text{ is not a bridge})\geq1-t_d$ with $t_d=\bar\theta^2q(d)\leq\bar\theta^2L'/d^2=s/d^2\leq1/36$.</p>
<p>(v) <em>Lower bound on $\mathbb P(i\in U)$.</em> For $i\in I$, the event $\{i\in U\}$ is the intersection of the events $\{e\text{ is not a bridge}\}$, over the finitely many edges $e=\{x,y\}$ with $x&lt;\alpha_i$, $y\geq\beta_i$, $y-x\leq CK$, and $\{e\text{ is closed}\}$, over the finitely many long edges $e$ with an endpoint in $V_i$. A bridge is an intersection of increasing events, so all these events are decreasing, and an intersection of decreasing events is decreasing. Applying the <a href="/tag/F4CV/">Harris inequality for decreasing events</a> repeatedly,</p>
<div class="math-display">$$\mathbb P(i\in U)\geq\prod_{\substack{x&lt;\alpha_i,\ y\geq\beta_i\\ y-x\leq CK}}(1-t_{y-x})\prod_{\substack{e\text{ long}\\ e\cap V_i\neq\varnothing}}(1-q_e).$$</div>
<p>For $d\geq6K$ there are exactly $d-6K$ pairs with $x&lt;\alpha_i$, $y\geq\beta_i$ and $y-x=d$. With the bound $-\log(1-t)\leq t+t^2$ of Step 0, together with $t_d\leq s/d^2$, $t_d^2\leq d^{-4}$ and $(d-6K)/d^2\leq1/d\leq\int_{d-1}^d dx/x$,</p>
<div class="math-display">$$-\sum_{d=6K}^{CK}(d-6K)\log(1-t_d)\leq s\sum_{d=6K+1}^{CK}\frac{d-6K}{d^2}+\sum_{d\geq6}\frac{d}{d^4}\leq s\int_{6K}^{CK}\frac{dx}x+\int_5^\infty\frac{dx}{x^3}\leq s\log C+1.$$</div>
<p>Every long edge meeting $V_i$ has the form $\{x,x+k\}$ with $x\in V_i$ and $K&lt;|k|\leq CK$; listing each such pair once can only lower the product, so by Step 0 the second product is at least $\exp(-2\cdot10K\cdot2L'/K)=e^{-40L'}$. Hence</p>
<div class="math-display">$$\mathbb P(i\in U)\geq e^{-1-40L'}C^{-s},\qquad\mathbb E|U|\geq\frac C9\,e^{-1-40L'}C^{-s}.$$</div>
<p>(vi) Combining with (iii) and the choice of $C_*$,</p>
<div class="math-display">$$\bar p(CK)\geq(1-e^{-1})\frac{e^{-1-40L'}C^{1-s}}{9}\,t\geq t=\min\{\bar p(K),C^{-1}\}.$$</div>
<p><em>Step 3: iteration.</em> Put $C=C_*$, $K_0=K_*$ and $K_n=C^nK_0$. Every open path of short edges, for the scale $K_0$, from a vertex below $-3K_0$ to a vertex at least $3K_0$ uses a short edge $\{u,w\}$ with $u&lt;0\leq w$. There are exactly $k$ such edges of length $k$, and $q(k)&lt;1$ for every $k$, so</p>
<div class="math-display">$$\bar p(K_0)\geq\prod_{k=1}^{K_0}(1-q(k))^k&gt;0.$$</div>
<p>This is the only use of the hypothesis $q(k)&lt;1$. Put $\delta=\min\{\bar p(K_0),C^{-1}\}&gt;0$. If $\bar p(K_n)\geq\delta$, Step 2 with $K=K_n\geq K_*$ gives $\bar p(K_{n+1})\geq\min\{\bar p(K_n),C^{-1}\}\geq\delta$. By induction $\bar p(K_n)\geq\delta$ for every $n\geq0$.</p>
<p><em>Step 4: contradiction.</em> For $K\geq n_0$, let $D_K$ be the event that every edge of length greater than $K$ with an endpoint in $[-9K,9K)$ is closed. Counting each such edge at least once as $\{x,x+k\}$ with $x\in[-9K,9K)$ and $|k|&gt;K$, Step 0 gives $\mathbb P(D_K)\geq\exp(-2\cdot18K\cdot2L'/K)=e^{-72L'}$. The event $D_K$ is determined by edges of length greater than $K$, while by Step 1 the events that $B^{2}_{3K}$ and $B^{-2}_{3K}$ are not $K$-crossed are determined by the short edges inside the disjoint windows $W_2=[2K,10K)$ and $W_{-2}=[-10K,-2K)$. Hence</p>
<div class="math-display">$$\mathbb P\bigl(D_K,\ \text{neither }B^{2}_{3K}\text{ nor }B^{-2}_{3K}\text{ is }K\text{-crossed}\bigr)=\mathbb P(D_K)\,\bar p(K)^2\geq e^{-72L'}\bar p(K)^2.$$</div>
<p>On this event no $x\in[-3K,3K)$ has an infinite cluster. Indeed, if $|K_x|=\infty$, then $K_x$ has a vertex outside $[-9K,9K)$; follow an open path from $x$ to it up to its first vertex $v$ outside $[-9K,9K)$. Every edge of this path has an endpoint in $[-9K,9K)$, so on $D_K$ all are short. If $v\geq9K=\beta_2$, the path joins $x&lt;3K=\alpha_2$ to $v$ and $B^2_{3K}$ is $K$-crossed; if $v&lt;-9K=\alpha_{-2}$, it joins $v$ to $x\geq-3K=\beta_{-2}$ and $B^{-2}_{3K}$ is $K$-crossed. Applying this with $K=K_n$ and Step 3,</p>
<div class="math-display">$$\mathbb P\bigl(\exists x\in[-3K_n,3K_n):|K_x|=\infty\bigr)\leq1-e^{-72L'}\delta^2&lt;1\qquad(n\geq0).$$</div>
<p>The events on the left increase to the event $\mathcal I$ that some cluster is infinite, so $\mathbb P(\mathcal I)\leq1-e^{-72L'}\delta^2$. But $\mathbb P(\mathcal I)\geq\theta&gt;0$, and by the <a href="/tag/H0OC/">zero–one law for the infinite cluster</a> $\mathbb P(\mathcal I)=1$. This contradiction proves $L_q\theta^2\geq1$ whenever $\theta&gt;0$.</p>
<p>The argument is the proof of Theorem 1(ii) in Duminil-Copin–Garban–Tassion, Section 2.4, with Step 2 in place of their Lemma 3, adapted as follows. Their opening probabilities are $1-e^{-\beta/n^2}$ for $n\geq2$, so their exponent $\beta\theta^2$ becomes $s=L'\bar\theta^2$ here; since the bound $q(n)\leq L'/n^2$ holds only for $n\geq n_0$, every estimate on long edges requires $K\geq n_0$, and since $L'&gt;L_q$ is arbitrary the conclusion involves the upper limit $L_q$. Their nearest-neighbour parameter enters the estimates only through $\bar p(K_0)&gt;0$, which here comes from $q(k)&lt;1$ for $k\leq K_0$; apart from their effect on $\theta$ and $\theta_R$, the values of $q$ below $n_0$ play no other role. The probability that an edge joins the boxes around the endpoints of a bridge is bounded by $4R^2L'/(25K^2)$ from the tail of $q$; any bound tending to zero as $K\to\infty$ would do. Connection events in the definition of a bridge use only edges of length at most $CK$, so that each is determined by finitely many edges, and the conditioning on long edges in their proof is replaced by the invariance argument of (ii). The constants $e^{-1-40L'}$, $e^{-72L'}$ and $C/9$ replace their unspecified constants.</p>
:::

## Existence with a strengthened nearest-neighbour interaction {#section-marginal-existence-input}

<a id="tag-JZG4" data-assertion="theorem" data-title="An inverse-square tail above one percolates after a finite nearest-neighbour enhancement"></a>
<p>On $\mathbb Z$, open bonds independently with probability $1-e^{-b/|i-j|^2}$ when $|i-j|\geq2$ and $1-e^{-\lambda}$ when $|i-j|=1$. For every $b&gt;1$, some finite $\lambda&gt;0$ gives a positive probability of an infinite root cluster. This is <a href="https://arxiv.org/html/2011.04642v2#S2.SS1">Duminil-Copin–Garban–Tassion, Theorem 1(i)</a>; a complete proof is given below. A local numerical correction to the source's block estimate is recorded <a href="/errata/dgt-long-range-2023/#block-square-integral">provisionally</a> and proved in PAFY; the proof below uses only PAFY's integral identity, not the source's Lemma 2 numerics.</p>
<p><em>Idea of the proof.</em> Blocks of length $2K$ are called good when they contain an open cluster, using only edges inside the block, with at least $2\theta K$ vertices. A block of length $2CK$ is covered by $2C-1$ overlapping blocks of length $2K$. When $\theta&gt;3/4$, the large clusters of two overlapping good blocks meet, so a run of good blocks yields one large cluster. Two disjoint bad blocks have probability of order $C^2$ times the square of the bad-block probability. A single bad spot near the boundary costs only a small loss of density. A bad spot far from the boundary must be bridged by one long edge between the large clusters on either side, and by the <a href="/tag/PAFY/">inverse-square block integral</a> the probability that no such edge is open is at most a negative power of the number of blocks on each side, with exponent close to $b\theta^2&gt;1$. Choosing the ratios between consecutive scales to grow geometrically, the bad-block probabilities decay along the scales, the density losses are summable, and a large $\lambda$ makes the first scale good with high probability. The argument follows the block construction of <a href="https://arxiv.org/html/2011.04642v2">Duminil-Copin–Garban–Tassion, Section 2.3</a>; as they recall, the theorem is due to Newman and Schulman for large $b$ and to Imbrie and Newman for every $b&gt;1$.</p>
:::details Proof
<p>Write $\mathbb P$ for the product law of the statement. Every edge of length at least two is open with probability $1-e^{-b/r^2}$, where $r$ is its length. For integers $K\geq1$ and $i\in\mathbb Z$, put</p>
<div class="math-display">$$B_K^i=\{K(i-1),K(i-1)+1,\ldots,K(i+1)-1\},$$</div>
<p>an interval of $2K$ vertices. For $\theta\in(0,1]$, call $B_K^i$ <em>$\theta$-good</em> if the configuration restricted to edges with both endpoints in $B_K^i$ has a cluster with at least $2\theta K$ vertices, and <em>bad</em> otherwise. This event depends only on the edges inside $B_K^i$, which all have length at most $2K-1$. Translation by $Ki$ maps $B_K^0$ to $B_K^i$ and preserves $\mathbb P$, so all blocks of one scale are bad with the same probability. If $\theta&gt;1/2$, a good block has exactly one such cluster, its <em>large cluster</em>, since two disjoint ones would have more than $2K$ vertices.</p>
<p><em>Step 1: merging.</em> Let $\theta&gt;3/4$ and let $B_K^i,B_K^{i+1}$ be good. Their intersection $\{Ki,\ldots,K(i+1)-1\}$ has $K$ vertices, and each large cluster misses at most $2K-2\theta K$ vertices of its block, so each contains at least $(2\theta-1)K$ vertices of the intersection. Since $2(2\theta-1)K&gt;K$, the two large clusters share a vertex, and their union is connected by open edges. By induction, for any run of consecutive good blocks $B_K^j,\ldots,B_K^{j'}$ the union of their large clusters is connected using open edges inside $B_K^j\cup\cdots\cup B_K^{j'}$.</p>
<p><em>Step 2: parameters.</em> Fix $b&gt;1$. Choose $\theta_\infty\in(\max\{3/4,b^{-1/2}\},1)$, put $s=b\theta_\infty^2&gt;1$, and choose $a\in(1/s,1)$. Choose a power of two $C$ so large that</p>
<div class="math-display">$$x\geq2x^a+5\ \text{ and }\ x^a\geq7\quad(x\geq C),\qquad C\geq32,\qquad C^{as-1}\geq32\cdot7^s,\qquad\frac{2C^{a-1}}{1-2^{a-1}}\leq1-\theta_\infty.$$</div>
<p>This is possible because $a&lt;1$ and $as&gt;1$. For $n\geq0$ put $C_n=2^nC$, $m_n=\lceil C_n^a\rceil$, $K_0=1$, $K_{n+1}=C_nK_n$, $\theta_0=1$ and $\theta_{n+1}=\theta_n-(m_n+1)/C_n$. Then $7\leq m_n\leq C_n^a+1$, so $2m_n+3\leq C_n$, and $m_n+1\leq2C_n^a$. Hence</p>
<div class="math-display">$$\theta_n\geq1-\sum_{k\geq0}\frac{2C_k^a}{C_k}=1-\frac{2C^{a-1}}{1-2^{a-1}}\geq\theta_\infty&gt;\frac34\qquad(n\geq0).$$</div>
<p>Finally set $\lambda=3\log C$. Write $p_n$ for the probability that $B_{K_n}^0$ is not $\theta_n$-good.</p>
<p><em>Step 3: one renormalization step.</em> Fix $n\geq0$ and abbreviate $K=K_n$, $C'=C_n$, $m=m_n$, $\theta=\theta_n$. The blocks $B_K^i$ with $-C'+1\leq i\leq C'-1$ are contained in $B_{C'K}^0=B_{K_{n+1}}^0$ and cover it. The $C'$ indices $i\equiv C'+1\pmod2$ in this range give disjoint blocks that tile $B_{C'K}^0$; call them the <em>tiling</em> blocks. Let $\mathcal F$ be the $\sigma$-field generated by the edges of length at most $2K-1$. All goodness events of scale $K$ are $\mathcal F$-measurable, and the edges of length at least $2K$ are independent of $\mathcal F$. Let $H$ be the union of the following events.</p>
<p>(i) No block $B_K^i$, $|i|\leq C'-1$, is bad.</p>
<p>(ii) Some block is bad, no two bad blocks are disjoint, and, with $i_0$ the smallest bad index, $i_0&lt;-C'+1+2m$ or $i_0+1+2m&gt;C'-1$.</p>
<p>(iii) Some block is bad, no two bad blocks are disjoint, $-C'+1\leq i_0-2m$ and $i_0+1+2m\leq C'-1$, and the event $\mathcal E$ below occurs.</p>
<p>Two blocks $B_K^i,B_K^j$ are disjoint exactly when $|i-j|\geq2$. So when no two bad blocks are disjoint, every bad index lies in $\{i_0,i_0+1\}$. In case (iii), put $I_j=B_K^{i_0-2j}$ and $J_k=B_K^{i_0+1+2k}$ for $1\leq j,k\leq m$; these are good blocks inside $B_{C'K}^0$, and</p>
<div class="math-display">$$I_j=\{K(i_0-1-2j),\ldots,K(i_0+1-2j)-1\},\qquad J_k=\{K(i_0+2k),\ldots,K(i_0+2k+2)-1\}.$$</div>
<p>Let $U$ be the union of the large clusters of the $I_j$ and $W$ the union of the large clusters of the $J_k$; both are $\mathcal F$-measurable. Let $\mathcal E$ be the event that some edge $\{x,y\}$ with $x\in U$, $y\in W$ is open.</p>
<p><em>Claim: on $H$, the block $B_{C'K}^0$ is $\theta_{n+1}$-good; if moreover $B_K^0$ is good, the large cluster of $B_{C'K}^0$ contains that of $B_K^0$.</em> In case (i), Step 1 makes the union of all large clusters connected. It contains the large clusters of the $C'$ tiling blocks, which are disjoint, so it has at least $2\theta KC'\geq2\theta_{n+1}K_{n+1}$ vertices. In case (ii), suppose first $i_0&lt;-C'+1+2m$. Since $2m+2\leq C'$, the indices $i_0+2,\ldots,C'-1$ include $0$, and they are all good. Step 1 makes the union of their large clusters connected. The tiling indices not in this run lie in $[-C'+1,i_0+1]\subseteq[-C'+1,-C'+1+2m]$, which contains $m+1$ tiling indices. So the union has at least $2\theta K(C'-m-1)\geq2K_{n+1}(\theta-(m+1)/C')=2\theta_{n+1}K_{n+1}$ vertices, using $\theta\leq1$. The case $i_0+1+2m&gt;C'-1$ is symmetric, with the good run $-C'+1,\ldots,i_0-1$ containing $0$ because $i_0\geq C'-1-2m\geq1$, and with at most $m+1$ tiling indices in $[i_0,C'-1]$. In case (iii), put $i_1=i_0+1$ if $B_K^{i_0+1}$ is good and $i_1=i_0+2$ otherwise. The good runs $-C'+1,\ldots,i_0-1$ and $i_1,\ldots,C'-1$ are nonempty, each yields a connected union by Step 1, the first contains $U$ and the second $W$, and the open edge of $\mathcal E$ joins them. The resulting connected set contains the large clusters of all good blocks, among them the $C'-1$ good tiling blocks (only one of $i_0,i_0+1$ is a tiling index), so it has at least $2\theta K(C'-1)\geq2\theta_{n+1}K_{n+1}$ vertices. All edges used lie inside $B_{C'K}^0$. In each case the connected set lies in one restricted cluster with at least $2\theta_{n+1}K_{n+1}$ vertices, which is the large cluster of $B_{C'K}^0$ because $\theta_{n+1}&gt;1/2$. In cases (i) and (iii) the connected set contains the large cluster of every good block, and in case (ii) the run contains the index $0$; so it contains the large cluster of $B_K^0$ whenever that block is good.</p>
<p><em>Bridging estimate.</em> In case (iii), if $x\in I_j$ and $y\in J_k$, then $3K&lt;y-x&lt;K(2j+2k+3)$. So the edges between $U$ and $W$ are distinct, have length greater than $3K\geq2$, are independent of $\mathcal F$, and</p>
<div class="math-display">$$\sum_{x\in U,\,y\in W}\frac1{(y-x)^2}\geq\sum_{j,k=1}^m\frac{(2\theta K)^2}{K^2(2j+2k+3)^2}=\theta^2\sum_{j,k=1}^m\frac1{(j+k+3/2)^2}.$$</div>
<p>On $[j,j+1]\times[k,k+1]$ one has $x+y+3/2\geq j+k+3/2$; substituting $x=1+u$, $y=1+v$ and applying the <a href="/tag/PAFY/">block integral identity</a> with $a=7/2$ and $A=m$,</p>
<div class="math-display">$$\sum_{j,k=1}^m\frac1{(j+k+3/2)^2}\geq\int_0^m\!\!\int_0^m\frac{du\,dv}{(7/2+u+v)^2}=\log\frac{(7/2+m)^2}{\frac72(7/2+2m)}\geq\log\frac{7/2+m}{7}\geq\log\frac m7,$$</div>
<p>using $7/2+2m\leq2(7/2+m)$. Since $m\geq7$ and $\theta\geq\theta_\infty$, on the $\mathcal F$-measurable event formed by the conditions of case (iii) other than $\mathcal E$,</p>
<div class="math-display">$$\mathbb P(\mathcal E^c\mid\mathcal F)=\exp\Bigl(-b\sum_{x\in U,\,y\in W}(y-x)^{-2}\Bigr)\leq\Bigl(\frac7m\Bigr)^{b\theta^2}\leq\Bigl(\frac7m\Bigr)^{s}.$$</div>
<p><em>Probability of $H^c$.</em> On $H^c$, either two disjoint blocks are bad, or for some index $i_0$ the block $B_K^{i_0}$ is bad, the $\mathcal F$-measurable conditions of case (iii) hold, and $\mathcal E$ fails. Disjoint blocks depend on disjoint edge sets, and there are at most $\binom{2C'-1}2\leq2C'^2$ pairs. Conditioning on $\mathcal F$ in the second alternative,</p>
<div class="math-display">$$\mathbb P(H^c)\leq2C'^2p_n^2+(2C'-1)p_n\Bigl(\frac7m\Bigr)^s\leq2C_n^2p_n^2+2\cdot7^sC_n^{1-as}p_n,$$</div>
<p>since $m\geq C_n^a$. By the claim, $p_{n+1}\leq\mathbb P(H^c)$.</p>
<p><em>Step 4: induction.</em> Claim: $p_n\leq C_n^{-3}$ for all $n\geq0$. For $n=0$, $B_1^0=\{-1,0\}$ is $1$-good exactly when its nearest-neighbour edge is open, so $p_0=e^{-\lambda}=C^{-3}$. If $p_n\leq C_n^{-3}$, then $2C_n^2p_n^2\leq2C_n^{-4}\leq C_n^{-3}/16$ since $C_n\geq32$, and $2\cdot7^sC_n^{1-as}p_n\leq C_n^{-3}/16$ since $C_n^{as-1}\geq32\cdot7^s$. Hence $\mathbb P(H_n^c)\leq C_n^{-3}/8=C_{n+1}^{-3}$, where $H_n$ denotes the event $H$ of step $n$, and so $p_{n+1}\leq C_{n+1}^{-3}$.</p>
<p><em>Step 5: an infinite cluster.</em> Let $G$ be the event that $B_1^0$ is $1$-good and $H_n$ occurs for every $n\geq0$. Then</p>
<div class="math-display">$$\mathbb P(G^c)\leq p_0+\sum_{n\geq0}C_{n+1}^{-3}=\sum_{n\geq0}C^{-3}8^{-n}=\frac{8}{7C^3}&lt;1.$$</div>
<p>On $G$, induction with the claim shows that every $B_{K_n}^0$ is $\theta_n$-good and that its large cluster $S_n$ satisfies $S_n\subseteq S_{n+1}$. Each $S_n$ is connected by open edges and $|S_n|\geq2\theta_nK_n\geq\frac32K_n\to\infty$. Since $0\in B_1^0=S_0$, the set $\bigcup_nS_n$ is an infinite set of vertices joined to $0$ by open edges. Hence $\mathbb P(|K_0|=\infty)\geq\mathbb P(G)&gt;0$ for the finite parameter $\lambda=3\log C$.</p>
:::

## The marginal transition for comparable kernels {#section-marginal-transition}

<a id="tag-NLDF" data-assertion="theorem" data-title="Comparable inverse-square intensity kernels percolate at their critical intensity"></a>
<p>Let $J:\mathbb Z\setminus\{0\}\to[0,\infty)$ be symmetric and finite, with</p>
<div class="math-display">$$0&lt;\liminf_{n\to\infty}n^2J(n)\leq L:=\limsup_{n\to\infty}n^2J(n)&lt;\infty.$$</div>
<p>For independent bonds with opening probabilities $1-e^{-\beta J(i-j)}$, put $\theta(\beta)=\mathbb P_\beta(|K_0|=\infty)$ and $\beta_c=\inf\{\beta:\theta(\beta)&gt;0\}$. Then</p>
<div class="math-display">$$\frac1L&lt;\beta_c&lt;\infty,\qquad
\theta(\beta_c)\geq\frac1{\sqrt{\beta_cL}}&gt;0.$$</div>
<p>For every $\beta\geq\beta_c$, $\theta(\beta)\geq(\beta L)^{-1/2}$. Thus the density jumps from zero to a positive value at criticality. The hypotheses allow arbitrary finite modifications of the short-range intensities, including zeros there; an exact tail limit is not needed.</p>
<p><em>Proof from JZG4 and 67W9.</em> Choose $a&gt;0$ and an integer $h\geq1$ such that $J(k)\geq a/k^2$ whenever $|k|\geq h$. On the sublattice $h\mathbb Z$, the intensity of a bond between indices at distance $j$ is at least $\beta a/(h^2j^2)$. Fix $b&gt;1$ and choose the finite $\lambda$ supplied by JZG4. If</p>
<div class="math-display">$$\beta\geq\frac{h^2}{a}\max\{b,\lambda\},$$</div>
<p>the model restricted to $h\mathbb Z$ dominates that percolating model: the inequality with $\lambda$ handles index distance one, and the inequality with $b$ handles every larger distance. Ordered coupling gives $\theta(\beta)&gt;0$, proving finiteness of the threshold.</p>
<p>Since $J(n)\to0$, for every finite $\beta&gt;0$ the tail coefficient of the opening probabilities is</p>
<div class="math-display">$$\limsup_{n\to\infty}n^2(1-e^{-\beta J(n)})=\beta L.$$</div>
<p>Apply 67W9 to obtain $\beta L\theta(\beta)^2\geq1$ whenever $\theta(\beta)&gt;0$. In particular no positive intensity below $1/L$ percolates. Monotonicity and the definition of the finite threshold imply $\theta(\beta)&gt;0$ for every $\beta&gt;\beta_c$.</p>
<p>The row sum $Q=\sum_{k\ne0}J(k)$ is finite. By <a href="/tag/0OQL/">0OQL</a>, $\theta$ is right-continuous, so letting $\beta\downarrow\beta_c$ gives the stated positive critical density and its bound. Finally, the origin is isolated with probability $e^{-\beta Q}$; hence $\theta(\beta)\leq1-e^{-\beta Q}&lt;1$ at every finite intensity. The critical inequality therefore forces $\beta_cL&gt;1$. Below $\beta_c$ the density is zero by definition.</p>
<p>This supplies the marginal $d=\alpha=1$ assertion; both JZG4 and 67W9 are proved on this page. In particular the normalized kernel $J(k)=|k|^{-2}$ has $1&lt;\beta_c&lt;\infty$, not a critical intensity identified as one. The number one in JZG4 concerns a tail coefficient with an independently adjustable nearest-neighbour parameter.</p>

## The block integral and its constant {#section-marginal-integral-repair}

<a id="tag-PAFY" data-assertion="proposition" data-title="The inverse-square block integral retains logarithmic growth with a corrected constant"></a>
<p>For $a&gt;0$ and $A\geq0$,</p>
<div class="math-display">$$\int_0^A\!\int_0^A\frac{dx\,dy}{(a+x+y)^2}
=\log\frac{(a+A)^2}{a(a+2A)}.$$</div>
<p>If $K,m\geq2$ are integers, $M=\lfloor Km/2\rfloor$, and $u,v\geq M$ are integers, then</p>
<div class="math-display">$$\sum_{i=1}^{u}\sum_{j=1}^{v}\frac1{(6K+i+j)^2}
\geq\log\frac{m}{64}.$$</div>
<p><em>Proof.</em> Integrating first in $y$ gives $(a+x)^{-1}-(a+x+A)^{-1}$, and the second integration gives the logarithm. Restrict the discrete sum to $1\leq i,j\leq M$. On $[i-1,i]\times[j-1,j]$, $6K+x+y+2\geq6K+i+j$, and $6K+2\leq8K$. Hence</p>
<div class="math-display">$$\sum_{i,j=1}^{M}\frac1{(6K+i+j)^2}
\geq\int_0^M\!\int_0^M\frac{dx\,dy}{(6K+x+y+2)^2}
\geq\log\frac{(8K+M)^2}{8K(8K+2M)}.$$</div>
<p>For $t&gt;0$, $(1+t)^2/(1+2t)\geq t/2$. With $t=M/(8K)$, the last expression is at least $\log(M/(16K))$. Since $M\geq Km/4$, this is at least $\log(m/64)$.</p>
<p>Consequently, if a block-joining argument has reached a failure estimate $\exp(-sD)$ with $s&gt;1$ and $D$ bounded below by this sum, then its valid upper bound is $(64/m)^s$. The tail $\sum_{m\geq m_0}(64/m)^s$ tends to zero as $m_0\to\infty$. Enlarging the minimum block-separation constant therefore preserves the required summable error, and also works uniformly when $s$ ranges over a compact interval above one.</p>
<p>The <a href="/errata/dgt-long-range-2023/#block-square-integral">provisional source erratum</a> concerns the displayed square-integral evaluation in the proof of Lemma 2. The correction above also retains the floor when the number $Km/2$ is not an integer. It changes a numerical estimate, not the decay exponent. No other step of the renormalization proof is certified by this calculation.</p>



## The qualitative power-law phase diagram {#section-power-law-classification}

<a id="tag-XP2Y" data-assertion="theorem" data-title="Qualitative phase classification for eventually comparable lattice kernels"></a>
<p>Let $d\geq1$, $\alpha&gt;0$, and let $J:\mathbb Z^d\setminus\{0\}\to[0,\infty)$ be symmetric and finite. Assume that for some $0&lt;c\leq C&lt;\infty$ and $r_0\geq1$,</p>
<div class="math-display">$$c|z|^{-d-\alpha}\leq J(z)\leq C|z|^{-d-\alpha}\qquad(|z|\geq r_0).$$</div>
<p>For independent bonds of probabilities $1-e^{-\beta J(y-x)}$, put $\theta(\beta)=\mathbb P_\beta(|K_0|=\infty)$ and $\beta_c=\inf\{\beta\geq0:\theta(\beta)&gt;0\}$, with $\inf\varnothing=\infty$. Then</p>
<div class="math-display">$$\begin{cases}
0&lt;\beta_c&lt;\infty,&d\geq2\text{ or }(d=1,\ 0&lt;\alpha\leq1),\\
\beta_c=\infty,&d=1,\ \alpha&gt;1.
\end{cases}$$</div>
<p>If $\alpha&lt;d$, there are no infinite clusters at $\beta_c$, $\theta$ is continuous there, and the rooted vertex-cluster law is continuous there in total variation. If $d=\alpha=1$, the density instead jumps at $\beta_c$: with $L_\infty=\limsup_{n\to\infty}n^2J(n)$,</p>
<div class="math-display">$$\beta_cL_\infty&gt;1,\qquad \theta(\beta_c)\geq(\beta_cL_\infty)^{-1/2}&gt;0.$$</div>
<p>Whenever $\beta_c$ is finite, $\chi_{\beta_c}=\infty$. This theorem makes no assertion about critical percolation in the remaining range $d\geq2$, $\alpha\geq d$.</p>
<p><em>Proof.</em> The upper envelope and $\alpha&gt;0$ make $Q=\sum_{z\ne0}J(z)$ finite; the lower envelope makes it positive. The row-sum bound gives $\beta_c\geq Q^{-1}&gt;0$.</p>
<p>If $d\geq2$, choose an integer $h\geq r_0$ and retain only bonds between nearest neighbours of the embedded plane $h\mathbb Z e_1+h\mathbb Z e_2$. Their intensities are at least $j=ch^{-d-\alpha}&gt;0$. At $\beta=(\log12)/j$, <a href="/tag/NUJY/">the planar contour bound</a> gives a positive probability of an infinite root cluster. Thus the full model has a finite threshold even when all its unit-length bonds are absent.</p>
<p>For $d=1$ and $\alpha&lt;1$, <a href="/tag/AKFN/">the eventual-envelope theorem</a> gives finiteness of the threshold. For $d=\alpha=1$, <a href="/tag/NLDF/">the inverse-square theorem</a> gives finiteness and the displayed critical-density bounds. For $d=1$ and $\alpha&gt;1$, the sum $\sum_{n\geq1}nJ(n)$ is finite. <a href="/tag/JK7V/">The closed-cut argument</a> then traps every cluster in a finite interval at each finite intensity, proving $\beta_c=\infty$.</p>
<p>In every dimension with $\alpha&lt;d$, AKFN excludes critical percolation. Summability and <a href="/tag/0OQL/">the finite-cluster continuity theorem</a> give continuity of both $\theta$ and the rooted-cluster law at that parameter, including approach from above. At a finite threshold, <a href="#section-finite-set">the finite-set sharpness argument</a> identifies the susceptibility threshold with $\beta_c$, and <a href="/tag/5LNL/">right-openness of finite susceptibility</a> forces $\chi_{\beta_c}=\infty$.</p>
<p>These conclusions assemble the qualitative one-dimensional alternatives. They are unchanged by any finite modification of displacement intensities that leaves them finite and nonnegative, though the value of $\beta_c$ may change. The discontinuous case follows from NLDF, and so from JZG4 and 67W9, both proved on this page. Total-variation convergence controls bounded cluster observables; the infinite critical susceptibility explains why it gives no convergence of all moments.</p>


## Diagram bounds expressed in susceptibility {#section-self-diagram}

<a id="tag-GQJY" data-assertion="proposition" data-title="Integrating a corrected differential inequality with a susceptibility-dependent diagram bound"></a>
<p>Let $b&lt;\infty$, let $y:(a,b)\to[1,\infty)$ be locally absolutely continuous with $y(t)\to\infty$ as $t\uparrow b$, and let $D:(a,b)\to[1,\infty)$ be measurable. Suppose that, almost everywhere sufficiently near $b$,</p>
<div class="math-display">$$y'(t)\geq k\frac{(y(t)-D(t))_+^2}{D(t)^2}$$</div>
<p>for a fixed $k&gt;0$. If $D(t)\leq C\log(e y(t))$ near $b$, then, as $\varepsilon\downarrow0$,</p>
<div class="math-display">$$y(b-\varepsilon)\leq C_1\varepsilon^{-1}\log^2(1/\varepsilon),\qquad D(b-\varepsilon)\leq C_2\log(1/\varepsilon).$$</div>
<p>If instead $D(t)\leq C y(t)^q$ near $b$, where $0\leq q&lt;1/2$, then</p>
<div class="math-display">$$y(b-\varepsilon)\leq C_3\varepsilon^{-1/(1-2q)}.$$</div>
<p>All constants may depend on the stated data; these are eventual bounds at a finite endpoint.</p>
<p><em>Proof.</em> In either case $D/y\to0$, so $y-D\geq y/2$ on a terminal interval. In the logarithmic case, $y'\geq c y^2/\log^2(e y)$ almost everywhere there. Put</p>
<div class="math-display">$$F(u)=\int_u^\infty\frac{\log^2(e v)}{v^2}\,dv
=\frac{\log^2(e u)+2\log(e u)+2}{u}\qquad(u\geq1).$$</div>
<p>The chain rule gives $(F\circ y)'\leq-c$ on each compact subinterval. Integrate from $t$ to $s&lt;b$, then let $s\uparrow b$. Since $F(y(s))\to0$,</p>
<div class="math-display">$$c(b-t)\leq F(y(t)).$$</div>
<p>The elementary bound $F(u)\leq C_4u^{-1/2}$ first yields $y(b-\varepsilon)\leq C_5\varepsilon^{-2}$. Hence $\log(e y(b-\varepsilon))\leq C_6\log(1/\varepsilon)$ for small $\varepsilon$. Substitute this into the exact expression for $F$ to obtain the asserted bound on $y$, and then into the hypothesis on $D$. The preliminary polynomial bound is what justifies changing the argument of the logarithm.</p>
<p>In the power case, $y'\geq c y^{2-2q}$. Set $r=1-2q&gt;0$. The chain rule gives $(y^{-r})'\leq-rc$ almost everywhere, so integration and endpoint divergence give $y(t)^{-r}\geq rc(b-t)$. Taking the negative power $-1/r$ proves the assertion, including $q=0$.</p>
<p>This is an analytic consequence of the squared positive-part inequality. It does not assume the stronger numerator $y(y-D)$, nor an independent polynomial estimate on $y$.</p>
