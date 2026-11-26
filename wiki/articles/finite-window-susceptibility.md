---
{
  "id": "finite-window-susceptibility",
  "title": "Susceptibility in the finite critical window",
  "subtitle": "Marked clusters control the expectation above the reference point",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A differential inequality for the second moment of the marked volume controls susceptibility above the reference point. It completes the finite-window expectation bound and gives moments of the largest component.",
  "context": [
    "Independent bond percolation on a finite connected simple vertex-transitive graph, with degree $m$ and $N$ vertices.",
    "Marks are independent Bernoulli variables with parameter $\\gamma$.",
    "The triangle condition is imposed only at the reference parameter $p_c$."
  ],
  "related": [
    "finite-triangle-window",
    "finite-graph-criticality",
    "cluster-partitions",
    "ghost-fields"
  ],
  "sourceIds": [
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "positive-window susceptibility",
    "marked cluster second moment",
    "finite-window component moments"
  ],
  "prototypeUses": []
}
---

## Marked volume and susceptibility {#section-marked-volume}

<p>Let $S=|C_o|$, $\chi(p)=\mathbb E_pS$, and mark each vertex independently with probability $\gamma\in(0,1)$. Write $q=1-\gamma$, let $G$ be the set of marked vertices, and put</p>
<div class="math-display">$$M=\mathbb P_{p,\gamma}(o\leftrightarrow G),\qquad Z=\sum_x\mathbf1_{\{x\leftrightarrow G\}},\qquad Q=\mathbb E_{p,\gamma}Z^2.$$</div>
<p>The two parts of the susceptibility are</p>
<div class="math-display">$$\chi_0=\mathbb E_p[S q^S],\qquad \chi_1=\mathbb E_p[S(1-q^S)],\qquad \chi=\chi_0+\chi_1.$$</div>
<p>Controlling the largest component in probability does not by itself control this expectation. The variable $Z$ supplies the missing estimate. The argument below follows the marked-volume strategy of the <a href="https://arxiv.org/pdf/math/0401069">finite-graph paper</a>, Section 8 and Appendix A.3, with the decoupling proved directly by exposing a cluster.</p>

<a id="tag-6AEH" data-assertion="proposition" data-title="Marked-volume and damped-cluster moment bounds on a finite transitive graph"></a>
<p>For every $p\in[0,1]$ and $0<\gamma<1$,</p>
<div class="math-display">$$N\chi_1\le Q\le N^2M^2+N\chi_1,\qquad \chi_1\le\gamma\chi^3,$$</div>
<div class="math-display">$$\chi_0\le\frac q\gamma M,\qquad B:=\mathbb E_p[S^2q^S]\le\frac q\gamma\chi_1.$$</div>
<p><em>Proof.</em> In a fixed bond configuration the distinct clusters form a partition. In the expansion of $Z^2$, pairs in the same marked cluster contribute $\sum_C|C|^2\mathbf1_{\{C\cap G\ne\varnothing\}}$. Its expectation is $N\chi_1$. All other terms are nonnegative, proving the lower bound.</p>
<p>For a pair in different marked clusters, expose $C_x=A$ and its marks. Conditional on this cluster and on its containing a mark, the bonds within $V\setminus A$ and the marks there retain their product law. A vertex $y\notin A$ is marked-connected in that induced graph with probability at most $M$, by coupling with the full graph. Thus $\mathbb P(x\leftrightarrow G,y\leftrightarrow G,x\not\leftrightarrow y)\le M^2$. Summing gives the upper bound for $Q$.</p>
<p>The scalar inequalities</p>
<div class="math-display">$$1-q^s\le\gamma s,\qquad \gamma s q^s\le q(1-q^s)\qquad(s\ge1)$$</div>
<p>give all three remaining bounds, except for $\mathbb ES^2\le\chi^3$. For that estimate sum the <a href="/tag/L82Q/">three-point tree inequality</a> over its two terminal vertices:</p>
<div class="math-display">$$\mathbb E_pS^2=\sum_{x,y}\mathbb P_p(o\leftrightarrow x,o\leftrightarrow y)\le\sum_{z,x,y}T_p(o,z)T_p(z,x)T_p(z,y)=\chi^3.$$</div>
<p>The second scalar inequality follows from $1-q^s=\gamma\sum_{j=0}^{s-1}q^j\ge\gamma s q^{s-1}$. Apply it once as written and once after multiplying by $s$.</p>

## Exposing an unmarked cluster {#section-differential}

<a id="tag-F8QD" data-assertion="theorem" data-title="A differential inequality for the second moment of marked volume"></a>
<p>At fixed $0<\gamma<1$, for $0\le p<1$, with the right derivative at zero,</p>
<div class="math-display">$$(1-p)\,\partial_p Q\le NmMB+2m\chi_0Q\le\frac{3mq}{\gamma}MQ.$$</div>
<p><em>Proof.</em> All expectations are polynomials. Apply the finite product derivative formula to $Z^2$, and express each summand using the configuration in which the edge is closed. Opening a closed edge changes $Z$ only when exactly one endpoint belongs to a marked cluster. Orient such an edge as $(u,v)$, with $u\leftrightarrow G$ and $v\not\leftrightarrow G$. If $s_v=|C_v|$, opening it increases $Z$ by $s_v$, and increases $Z^2$ by $s_v^2+2s_vZ$. Hence the exact identity is</p>
<div class="math-display">$$(1-p)\partial_pQ=\sum_{(u,v):\,u\sim v}\mathbb E_{p,\gamma}\!\left[\mathbf1_{\{u\leftrightarrow G,\ v\not\leftrightarrow G\}}(s_v^2+2s_vZ)\right].$$</div>
<p>There is no extra factor of two: a contributing unoriented edge has exactly one orientation of this kind. The edge is automatically closed when its endpoints have these different marking statuses.</p>
<p>Condition on $C_v=A$ and on $A$ having no mark. This fixes its boundary bonds closed and its internal marks absent, but leaves an independent bond-and-mark configuration on $V\setminus A$. For every increasing event there, its conditional probability is at most its probability in the full graph. In particular, for each fixed adjacent pair $(u,v)$,</p>
<div class="math-display">$$\mathbb E[\mathbf1_{\{u\leftrightarrow G,\ v\not\leftrightarrow G\}}s_v^2]\le MB,$$</div>
<p>and, for each $x$,</p>
<div class="math-display">$$\mathbb E[\mathbf1_{\{u\leftrightarrow G,\ x\leftrightarrow G,\ v\not\leftrightarrow G\}}s_v]\le\chi_0\,\mathbb P_{p,\gamma}(u\leftrightarrow G,x\leftrightarrow G).$$</div>
<p>If $u$ or $x$ lies in $A$, the relevant conditional probability is zero. Otherwise the simultaneous connections on the right are increasing events in the induced complement; they need not be disjoint. Summing the first inequality over the $Nm$ oriented edges gives $NmMB$. Summing the second over $x$ and the edges gives $m\chi_0Q$, since every $u$ has $m$ neighbors. This proves the first differential bound.</p>
<p>Finally $NB\le(q/\gamma)N\chi_1\le(q/\gamma)Q$ and $\chi_0\le(q/\gamma)M$. Substitution gives the second bound. In particular the proof does not discard the condition that $C_v$ has no mark.</p>

## Transport from the triangle reference point {#section-transport}

<p>Fix $p_c\in(0,1/2]$, put $H=\chi(p_c)$, and suppose $H\ge100$ and</p>
<div class="math-display">$$T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+a\qquad(x,y\in V),\qquad a\le\frac1{100}.$$</div>
<p>These are the hypotheses of the <a href="/tag/KQN9/">finite field bound</a>. No triangle bound is assumed above $p_c$.</p>

<a id="tag-RT85" data-assertion="theorem" data-title="An explicit susceptibility bound from finite marked-volume transport"></a>
<p>For $p_c\le p\le1/2$, write $\varepsilon=m(p-p_c)$. For every $0<\gamma\le1/2$,</p>
<div class="math-display">$$\chi(p)\le\frac{\sqrt{96}}{\sqrt\gamma}+\frac{96\varepsilon}{\gamma}+\gamma(48N+H^3)\exp\!\left(\frac{6\sqrt{96}\,\varepsilon}{\sqrt\gamma}+\frac{576\varepsilon^2}{\gamma}\right).$$</div>
<p><em>Proof.</em> The inverse-field argument in <a href="/tag/1T2M/">1T2M</a>, before converting the field to a root tail, gives</p>
<div class="math-display">$$M(p,\gamma)\le\sqrt{48h}+96\varepsilon\le\sqrt{96\gamma}+96\varepsilon,\qquad h=-\log(1-\gamma)\le2\gamma.$$</div>
<p>Thus $\chi_0\le M/\gamma$ gives the first two terms of the desired estimate. At $p_c$, the preceding moment bounds and $M(p_c,\gamma)^2\le48\gamma$ give</p>
<div class="math-display">$$Q(p_c,\gamma)\le\gamma N(48N+H^3).$$</div>
<p>Since $Q>0$, integrate its logarithmic derivative. The function $M(t,\gamma)/(1-t)$ is nondecreasing in $t$, so</p>
<div class="math-display">$$Q(p,\gamma)\le Q(p_c,\gamma)\exp\!\left(\frac{3\varepsilon q}{\gamma(1-p)}M(p,\gamma)\right)\le Q(p_c,\gamma)\exp\!\left(\frac{6\varepsilon}{\gamma}M(p,\gamma)\right).$$</div>
<p>Now use $\chi_1\le Q/N$, substitute the field bound, and add $\chi_0$. The parameter is the additive displacement $m(p-p_c)$ throughout.</p>

## Susceptibility on both sides of the window {#section-window}

<a id="tag-CAZQ" data-assertion="theorem" data-title="Finite susceptibility is at most a volume-third term plus the squared positive displacement term"></a>
<p>Under the preceding hypotheses, suppose $H=\lambda N^{1/3}$, with $\lambda>0$. Then for $p_c\le p\le1/2$,</p>
<div class="math-display">$$\chi(p)\le C_\lambda\bigl(N^{1/3}+\varepsilon^2N\bigr),\qquad C_\lambda=1+20000(48+\lambda^3),\qquad\varepsilon=m(p-p_c).$$</div>
<p>Consequently, if $\Lambda\ge0$ and $p_-=p_c-\Lambda/(mN^{1/3})\ge0$, $p_+=p_c+\Lambda/(mN^{1/3})\le1/2$, then throughout $p\in[p_-,p_+]$,</p>
<div class="math-display">$$(\lambda^{-1}+\Lambda)^{-1}N^{1/3}\le\chi(p)\le\max\{\lambda,C_\lambda(1+\Lambda^2)\}N^{1/3}.$$</div>
<p><em>Proof.</em> Put $\eta=\max\{\varepsilon,N^{-1/3}\}$. If $\eta\le1/200$, take $\gamma=10000\eta^2\le1/4$ in the preceding estimate. Since $\sqrt{96}<10$, its exponential factor is less than $2$: the exponent is at most</p>
<div class="math-display">$$6\left(\frac{\sqrt{96}}{100}+\frac{96}{10000}\right)<\frac23<\log2.$$</div>
<p>The first two terms sum to at most $1/\eta$. Therefore</p>
<div class="math-display">$$\chi(p)\le\eta^{-1}+20000(48+\lambda^3)\eta^2N\le C_\lambda(N^{1/3}+\varepsilon^2N).$$</div>
<p>Here $\eta^{-1}\le N^{1/3}$ and $\eta^2N=\max\{\varepsilon^2N,N^{1/3}\}$. If $\eta>1/200$, the deterministic bound $\chi\le N<40000\eta^2N$ gives the same conclusion, since $C_\lambda>40000$. This case avoids choosing a mark probability outside $[0,1]$.</p>
<p>For the lower bound in the window apply <a href="/tag/F5Y5/">F5Y5</a> at $p_-$, then use monotonicity. For the upper bound use $\chi(p)\le H$ below $p_c$, and the new estimate with $\varepsilon\le\Lambda N^{-1/3}$ above it. All constants are uniform in the graph size; they are not optimized.</p>

## Moments of the largest component {#section-component-moments}

<a id="tag-KSAO" data-assertion="corollary" data-title="Largest-component moments through order two and uniform integrability below order two"></a>
<p>Under the bounded-window hypotheses just stated, for every $0<r\le2$ there are positive finite constants $c_r,C_r$, depending only on $\lambda,\Lambda,r$, such that</p>
<div class="math-display">$$c_rN^{2r/3}\le\mathbb E_pL_1^r\le C_rN^{2r/3}\qquad(p_-\le p\le p_+).$$</div>
<p>Also $\mathbb E_p\sum_C|C|^2=N\chi(p)$ is bounded above and below by positive constant multiples of $N^{4/3}$. For any family of graphs and parameters satisfying the same hypotheses, the variables $(L_1/N^{2/3})^r$ are uniformly integrable for every fixed $0<r<2$.</p>
<p><em>Proof.</em> The <a href="/tag/TUD2/">cluster partition identity</a> gives</p>
<div class="math-display">$$L_1^2\le\sum_C|C|^2=\sum_x|C_x|,\qquad \mathbb E_pL_1^2\le N\chi(p)\le K N^{4/3},$$</div>
<p>where $K=\max\{\lambda,C_\lambda(1+\Lambda^2)\}$. Concavity of $t^{r/2}$ gives the upper bound for $r\le2$. The component-window theorem <a href="/tag/CBIL/">CBIL</a> supplies a constant $D=D(\lambda,\Lambda)$. With $A=\max\{1,2D\}$ it gives $\mathbb P(L_1\ge N^{2/3}/A)\ge1/2$, hence $\mathbb EL_1^r\ge N^{2r/3}/(2A^r)$. The assertion for the sum of squared sizes follows from the same partition identity and the two-sided susceptibility bounds.</p>
<p>Finally put $X=L_1/N^{2/3}$. For $R>0$ and $r<2$,</p>
<div class="math-display">$$\mathbb E[X^r\mathbf1_{\{X>R\}}]\le R^{r-2}\mathbb EX^2\le KR^{r-2}\longrightarrow0.$$</div>
<p>This proves the stated uniform integrability. A bound on the second moment alone does not establish uniform integrability of $X^2$, or moments of order greater than two.</p>



## Moments of the total squared component mass {#section-total-squared-mass-moments}

<p>The susceptibility bound also controls every moment of the total squared component mass. The additional ingredient is to expose distinct clusters successively; no independence of their sizes is assumed.</p>

<a id="tag-YN7V" data-assertion="theorem" data-title="A uniform susceptibility bound controls every polynomial moment of the total squared component mass"></a>
<p>Consider independent bond percolation on a finite nonempty vertex set of size $N$. Put $M=\max_v\mathbb E|C_v|$, and let $\mathcal P_m$ denote the set of partitions of $\{1,\ldots,m\}$. For every integer $m\ge1$,</p>
<div class="math-display">$$\mathbb E\left(\sum_C|C|^2\right)^m
\le\sum_{\pi\in\mathcal P_m}
N^{|\pi|}M^{4m-3|\pi|}
\prod_{B\in\pi}(4|B|-5)!!,$$</div>
<p>where $(-1)!!=1$. Consequently, if $M\le K N^{1/3}$, then for every real $q>0$ there is a finite constant $C_{K,q}$ such that</p>
<div class="math-display">$$\mathbb E\left(N^{-4/3}\sum_C|C|^2\right)^q\le C_{K,q}.$$</div>
<p><em>Proof.</em> For integers $r\ge2$, write $U_r=\mathbb E\sum_C|C|^r$. Counting each cluster once at each of its vertices, and applying <a href="/tag/Y84V/">the tree-graph moment bound</a>, gives</p>
<div class="math-display">$$U_r=\sum_v\mathbb E|C_v|^{r-1}
\le N(2r-5)!!\,M^{2r-3}.$$</div>
<p>We first show that, for any $r_1,\ldots,r_k\ge2$, the ordered sum over distinct clusters satisfies</p>
<div class="math-display">$$\mathbb E\sum_{C_1,\ldots,C_k\ {\rm distinct}}
\prod_{j=1}^k|C_j|^{r_j}\le\prod_{j=1}^k U_{r_j}.$$</div>
<p>Use induction, simultaneously for every induced subgraph of the original model, with the constants $U_r$ always taken in the original graph. Conditional on a specified set $A$ being a cluster of an induced graph, the bonds in its complement retain their independent laws. The induction hypothesis bounds the expected contribution of the remaining $k-1$ distinct clusters by $\prod_{j=2}^kU_{r_j}$. Sum over $A$, with weight $|A|^{r_1}\mathbb P(A\text{ is a cluster})$. The resulting first factor is at most $U_{r_1}$: under the natural coupling, adding vertices and bonds can only increase $\sum_C|C|^{r_1}$. This also proves the induction base. The complement is allowed to be empty, in which case a nonempty cluster sum is zero.</p>
<p>Expand the $m$th power of $\sum_C|C|^2$, and group its ordered $m$-tuples according to which positions select the same cluster. A partition $\pi$ contributes an ordered distinct-cluster sum with exponents $2|B|$, with the blocks ordered by their least elements. Its expectation is at most $\prod_{B\in\pi}U_{2|B|}$. Substituting the preceding bound proves the formula.</p>
<p>If $M\le K N^{1/3}$, each term has volume exponent $|\pi|+(4m-3|\pi|)/3=4m/3$. This proves the normalized bound for integer $m$. For real $q>0$, choose an integer $m\ge q$ and apply $\mathbb EZ^q\le(\mathbb EZ^m)^{q/m}$. $ \square$</p>
<p>In particular the preceding finite-window susceptibility theorem gives all positive moments of $N^{-4/3}\sum_C|C|^2$, and hence all positive moments of $L_1/N^{2/3}$, uniformly under its bounded-window hypotheses. These moment bounds are stronger than the second-moment consequences stated earlier. They do not by themselves identify a limiting law.</p>




## Exponential control of the square-root mass {#section-squared-mass-exponential}

<p>Keeping the dependence on the moment order in YN7V gives an exponential bound at the square-root scale. The partition sum costs only a geometric factor after division by $(2m)!$.</p>

<a id="tag-81TZ" data-assertion="theorem" data-title="Uniform susceptibility gives an explicit exponential moment for the square root of total squared component mass"></a>
<p>In the finite independent bond model of YN7V, put</p>
<div class="math-display">$$
T=\sum_C|C|^2,\qquad
M=\max_v\mathbb E|C_v|,\qquad H=\max\{NM,M^4\}.
$$</div>
<p>For every integer $m\ge1$ and every $0\le\theta<1/\sqrt8$,</p>
<div class="math-display">$$
\mathbb ET^m\le(8H)^m(2m)!,
\qquad
\mathbb E\exp\!\left(\theta\sqrt{T/H}\right)
\le\frac{2}{1-8\theta^2}.
$$</div>
<p>In particular, for $u\ge0$,</p>
<div class="math-display">$$
\mathbb P(T\ge Hu^2)\le\min\{1,4e^{-u/4}\}.
$$</div>
<p>If $M\le K N^{1/3}$, set $\kappa=\max\{K,K^4\}$. Then</p>
<div class="math-display">$$
\mathbb E\exp\!\left(\theta N^{-2/3}\sqrt T\right)
\le\frac{2}{1-8\kappa\theta^2}
\qquad\left(0\le\theta<(8\kappa)^{-1/2}\right).
$$</div>
<p><em>Proof.</em> For a partition with $k$ blocks, the scale in YN7V is
$N^kM^{4m-3k}=(NM)^k(M^4)^{m-k}\le H^m$. Also, for $s\ge1$,</p>
<div class="math-display">$$
(4s-5)!!\le(4s-1)!!
=\frac{(4s)!}{2^{2s}(2s)!}
\le4^s(2s)!.
$$</div>
<p>The last inequality is $\binom{4s}{2s}\le2^{4s}$. Let
$B_m=\sum_{\pi\in\mathcal P_m}\prod_{B\in\pi}(2|B|)!$, with $B_0=1$.
Choosing the block containing the first element gives</p>
<div class="math-display">$$
B_m=\sum_{s=1}^m\binom{m-1}{s-1}(2s)!\,B_{m-s}.
$$</div>
<p>We claim $B_m\le2^m(2m)!$. Inductively, division by $2^m(2m)!$ bounds the last sum by</p>
<div class="math-display">$$
\sum_{s=1}^m2^{-s}
\frac{\binom{m-1}{s-1}}{\binom{2m}{2s}}
\le\sum_{s=1}^m2^{-s}<1.
$$</div>
<p>For the binomial comparison, an $s$-element subset of an $m$-element set embeds among the $2s$-element subsets of two disjoint copies by taking both copies of each chosen element; moreover $\binom{m-1}{s-1}\le\binom ms$. The induction begins at $m=0$. Applying the two coefficient bounds to YN7V proves $\mathbb ET^m\le(8H)^m(2m)!$.</p>
<p>Set $R=\sqrt{T/H}$. Since $e^{\theta R}\le2\cosh(\theta R)$, the nonnegative series and the even-moment bound give</p>
<div class="math-display">$$
\mathbb E e^{\theta R}
\le2\sum_{m\ge0}\frac{\theta^{2m}\mathbb ER^{2m}}{(2m)!}
\le2\sum_{m\ge0}(8\theta^2)^m.
$$</div>
<p>This proves the exponential estimate without assuming integrability beforehand. Markov's inequality at $\theta=1/4$ gives the tail bound. Finally $H\le\kappa N^{4/3}$, so monotonicity gives the normalized estimate. $ \square$</p>
<p>The conclusion controls the exponential of the $\ell^2$ norm of the normalized component-size vector. It does not claim an exponential moment for its squared norm.</p>




## Products over distinct clusters {#section-cluster-exponential-product}

<p>The distinct-cluster argument in YN7V also bounds products of general cluster weights. This allows a largest-component tail to control the exponential of the total squared mass.</p>

<a id="tag-1NYQ" data-assertion="proposition" data-title="Superadditive cluster weights bound multiplicative cluster functionals by the exponential of their first cluster sum"></a>
<p>Consider independent bonds on a finite nonempty set of $N$ vertices. Let $f:\{0,\ldots,N\}\to[0,\infty)$ satisfy $f(0)=0$ and
$f(u+v)\ge f(u)+f(v)$ whenever $u+v\le N$. Put $U_f=\mathbb E\sum_C f(|C|)$. Then</p>
<div class="math-display">$$
\mathbb E\prod_C\bigl(1+f(|C|)\bigr)
\le \sum_{k=0}^N\frac{U_f^k}{k!}\le e^{U_f}.
$$</div>
<p>In particular, for $a>0$, $t\ge0$, and</p>
<div class="math-display">$$
S_a=a^{-2}\sum_C|C|^2,\qquad R_a=a^{-1}\max_C|C|,
$$</div>
<p>one has</p>
<div class="math-display">$$
\mathbb E e^{tS_a}
\le \exp\!\left\{\mathbb E\sum_C
                  \bigl(e^{t|C|^2/a^2}-1\bigr)\right\}
\le \exp\!\left\{t(\mathbb ES_a^2)^{1/2}
                     (\mathbb E e^{2tR_a^2})^{1/2}\right\}.
$$</div>
<p><em>Proof.</em> Adding a vertex or an edge cannot decrease $\sum_C f(|C|)$: a new singleton contributes a nonnegative term, and a merger increases the sum by superadditivity. Thus every induced subgraph has expected cluster sum at most $U_f$, using the natural coupling with the original graph.</p>
<p>For every induced subgraph $H$ and integer $k\ge0$, we claim</p>
<div class="math-display">$$
\mathbb E_H\!\sum_{C_1,\ldots,C_k\ {\rm distinct}}
                 \prod_{j=1}^k f(|C_j|)\le U_f^k.
$$</div>
<p>The sum is over ordered clusters, and for $k=0$ it is one, even in the empty graph. Proceed by induction on $k$, simultaneously for all $H$. Conditional on a nonempty set $A$ being a cluster of $H$, the edges with both endpoints in $H\setminus A$ retain their independent laws: the conditioning concerns only edges within $A$ and its boundary. The expected remaining ordered product is at most $U_f^{k-1}$ by induction. Sum over $A$ with weight $f(|A|)$ times its cluster probability. The first factor is the expected cluster sum in $H$, at most $U_f$. This proves the claim, including zero-probability cluster events by summing only events of positive probability.</p>
<p>Expand the finite product $\prod_C(1+f(|C|))$. Its terms choosing $k$ clusters form $1/k!$ times the ordered sum just bounded. This gives the first display. No independence between cluster sizes has been used.</p>
<p>Take $f(s)=e^{t(s/a)^2}-1$. It is nonnegative and superadditive, since $(u+v)^2\ge u^2+v^2$ and $e^{x+y}-1\ge(e^x-1)+(e^y-1)$ for $x,y\ge0$. Also $e^x-1\le xe^x$, so</p>
<div class="math-display">$$
\sum_C\bigl(e^{t|C|^2/a^2}-1\bigr)
\le t S_a e^{tR_a^2}.
$$</div>
<p>Cauchy–Schwarz proves the last bound. All random variables here are bounded on a finite graph; no exponential integrability is assumed in an infinite-volume limit. $ \square$</p>
