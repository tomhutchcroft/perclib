---
{
  "id": "finite-set-hyperscaling",
  "title": "Finite-set hyperscaling bounds",
  "subtitle": "Comparing the largest intersection with the sum of squared intersections",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "A global cluster tail and a rooted damping estimate control the largest-cluster quantile and averaged connectivity in every finite observation set. Exponent inequalities require separate asymptotic assumptions. The power-law applications close the spatial and edge-weight bootstrap arguments, including the critical endpoint.",
  "context": [
    "Clusters are full-graph clusters intersected with a finite nonempty observation set; paths may leave the set.",
    "The global volume-tail exponent satisfies $\\delta>1$.",
    "The rooted exponential damping estimate is an explicit input from universal tightness."
  ],
  "related": [
    "universal-tightness",
    "critical-exponents",
    "susceptibility",
    "hierarchical-two-point",
    "stopped-exploration",
    "integrated-susceptibility"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "perclib-marked-edge-splitting",
    "hutchcroft-powerlaw-2021",
    "perclib-amplitude-contraction",
    "perclib-window-hyperscaling",
    "perclib-damped-window-tails",
    "perclib-train10-models-longrange-quantilemoments",
    "hutchcroft-hierarchical-volumes-2022"
  ],
  "aliases": [
    "hyperscaling",
    "averaged connectivity",
    "fractal dimension",
    "largest-cluster quantile",
    "upper critical dimension"
  ],
  "prototypeUses": []
}
---

## The finite-set estimate {#section-finite-set}

<a id="tag-WRHL" data-assertion="theorem" data-title="Finite-set hyperscaling from global tails and rooted damping"></a>
<p>Consider random clusters on a countable vertex set. Suppose $\delta&gt;1$, $C&gt;0$, and</p>
<div class="math-display">$$\sup_x\mathbb P(|K_x|\geq n)\leq Cn^{-1/\delta}\qquad(n\geq1).$$</div>
<p>For a finite nonempty set $\Lambda$, put $Z=\max_{x\in\Lambda}|K_x\cap\Lambda|$ and $M=\min\{m\geq1:\mathbb P(Z\geq m)\leq e^{-1}\}$. Assume the rooted damping estimate</p>
<div class="math-display">$$\mathbb P(|K_x\cap\Lambda|\geq\lambda M)\leq e^{1-\lambda/9}\mathbb P(|K_x\cap\Lambda|\geq M)\qquad(x\in V,\ \lambda\geq1).$$</div>
<p>Set</p>
<div class="math-display">$$L=C\left(\frac{\delta}{\delta-1}+9e^{8/9}\right),\qquad C_1=(4eL)^{\delta/(\delta+1)},\qquad C_2=L(4eL)^{(\delta-1)/(\delta+1)}.$$</div>
<p>Then</p>
<div class="math-display">$$M\leq C_1|\Lambda|^{\delta/(\delta+1)},\qquad \frac1{|\Lambda|}\sum_{v\in\Lambda}\mathbb P(x\leftrightarrow v)\leq C_2|\Lambda|^{-2/(\delta+1)}\quad(x\in V).$$</div>
<p>No transitivity is needed once the two displayed probability bounds hold uniformly in the root. The clusters must be those of a common random partition, so that their intersections partition $\Lambda$.</p>
<p><em>Proof.</em> Write $X_x=|K_x\cap\Lambda|$ and $\alpha=1/\delta\in(0,1)$. For $n\leq M$, the global bound gives $\mathbb P(X_x\geq n)\leq Cn^{-\alpha}$. For $n&gt;M$, rooted damping gives $\mathbb P(X_x\geq n)\leq C M^{-\alpha}e^{1-n/(9M)}$. Hence the integer tail-sum identity yields</p>
<div class="math-display">$$\begin{aligned}
\mathbb E X_x&\leq C\sum_{n=1}^M n^{-\alpha}+CeM^{-\alpha}\sum_{n&gt;M}e^{-n/(9M)}\\
&\leq\frac{C}{1-\alpha}M^{1-\alpha}+CeM^{-\alpha}\int_M^\infty e^{-t/(9M)}\,dt
=L M^{1-\alpha}.
\end{aligned}$$</div>
<p>The first sum is bounded by $1+\int_1^M t^{-\alpha}\,dt\leq M^{1-\alpha}/(1-\alpha)$. In the second sum the integrand is decreasing, giving the stated integral comparison.</p>
<p>For every configuration, let $C_i$ be the distinct full clusters meeting $\Lambda$. Counting ordered pairs gives</p>
<div class="math-display">$$\sum_{u,v\in\Lambda}\mathbf1_{\{u\leftrightarrow v\}}=\sum_i|C_i\cap\Lambda|^2\geq Z^2.$$</div>
<p>The quantile definition alone gives $M\geq2$ and $\mathbb P(Z\geq M-1)&gt;e^{-1}$, so $\mathbb E Z^2\geq M^2/(4e)$. Taking expectations in the pair identity and applying the bound on $\mathbb E X_u$ gives</p>
<div class="math-display">$$\frac{M^2}{4e}\leq\sum_{u\in\Lambda}\mathbb E X_u\leq|\Lambda|L M^{1-\alpha}.$$</div>
<p>Divide by $M^{1-\alpha}$ to obtain $M^{1+\alpha}\leq4eL|\Lambda|$, proving the first estimate. For any root $x$, insert it into $\sum_{v\in\Lambda}\mathbb P(x\leftrightarrow v)=\mathbb E X_x\leq L M^{1-\alpha}$ and divide by $|\Lambda|$. This gives the second estimate with the displayed constant.</p>
<p>The rooted damping estimate is the <a href="/tag/21D4/">universal-tightness input</a>. Its splitting argument is proved <a href="#section-rooted-damping">below</a>, separately from this calculation. Conversely, no separate lower-tail theorem for $Z$ is needed here: the elementary quantile property supplies the required second-moment lower bound. The restriction $\delta&gt;1$ is used in summing the small-size tail; the borderline $\delta=1$ requires a different logarithmic estimate.</p>

## Passing to exponents {#section-exponents}

<a id="tag-7VCS" data-assertion="corollary" data-title="Hyperscaling exponent inequalities from finite-set bounds"></a>
<p>Suppose the preceding hypotheses hold for a family of finite sets $\Lambda_R$, $R\to\infty$, and for some $d&gt;0$ and finite real $d_f,s$,</p>
<div class="math-display">$$|\Lambda_R|=R^{d+o(1)},\qquad M(\Lambda_R)=R^{d_f+o(1)},\qquad \sum_{v\in\Lambda_R}\mathbb P(o\leftrightarrow v)=R^{s+o(1)}.$$</div>
<p>Then</p>
<div class="math-display">$$\frac{d_f}{d}\leq\frac{\delta}{\delta+1},\qquad s\leq d\frac{\delta-1}{\delta+1}.$$</div>
<p>If $s=2-\eta$ is the chosen averaged two-point exponent, the latter inequality is $2-\eta\leq d(\delta-1)/(\delta+1)$. In particular, $\delta=2$ and $s=2$ require $d\geq6$.</p>
<p><em>Proof.</em> Take logarithms of the two finite-set inequalities, divide by $\log R$, and let $R\to\infty$. Fixed multiplicative constants contribute zero in this limit. The first gives $d_f\leq d\delta/(\delta+1)$. Multiplying the averaged-connectivity estimate by $|\Lambda_R|$ before taking logarithms gives $s\leq d(\delta-1)/(\delta+1)$. Substitute the stated values for the final assertion.</p>
<p>These conclusions assume the three asymptotic laws; they do not prove that the exponents exist. A pointwise two-point exponent may imply the displayed averaged law under suitable spatial hypotheses, but that implication must be established separately. Likewise, $d_f$ here describes the quantile scale, not an almost-sure fractal dimension assigned to an individual cluster.</p>
<p>Under transitivity, a logarithmic cluster-tail exponent with finite $\delta&gt;1$ also suffices for these exponent inequalities if rooted damping is available. For every $\delta'&gt;\delta$, the logarithmic tail law gives $\mathbb P(|K_o|\geq n)\leq C_{\delta'}n^{-1/\delta'}$, with transitivity making this uniform in the root. Apply the inequalities with $\delta'$ and then let $\delta'\downarrow\delta$. This limiting argument concerns exponents only and does not turn a logarithmic tail law into a fixed two-sided power comparison.</p>

## Source scope {#section-source}

<p>The global tail and rooted damping remain distinct hypotheses. The proof uses the quantile definition in place of the lower-tail half of universal tightness, and keeps the averaged two-point asymptotic separate from any pointwise spatial claim.</p>

## Splitting a connected witness {#section-splitting}

<a id="tag-DMI0" data-assertion="proposition" data-title="Marked tree splitting with a prescribed root covered"></a>
<p>Let $T$ be a finite tree and $A$ a set of $N$ marked vertices. If $k\geq1$ is an integer and $N\geq3^k$, its edges admit a partition into $m\geq3^{k-1}+1$ nonempty connected pieces such that every piece has between $3^{-k}N$ and $3^{1-k}N$ marked endpoints, with the upper bound strict. Their endpoint sets cover every vertex of $T$. In particular, any prescribed root belongs to at least one piece.</p>
<p><em>Proof.</em> We first split a tree with $n\geq3$ marked vertices into two pieces, each having between $n/3$ and $\lceil2n/3\rceil$ marked endpoints. Choose a vertex $v$ for which every component of $T\setminus\{v\}$ contains at most $n/2$ marks. Such a vertex exists: moving toward a component containing more than half the marks strictly decreases the sum of distances to the marked vertices.</p>
<p>Put $w=\mathbf1_{\{v\in A\}}$. The components at $v$ have integer masses at most $\lfloor n/2\rfloor$, with sum $n-w$. We select some of them whose total mass $s$ lies in the integer interval</p>
<div class="math-display">$$
L=\max\{\lceil n/3\rceil-w,\lfloor n/3\rfloor\}
\ \leq s\leq
U=\min\{\lceil2n/3\rceil-w,\lfloor2n/3\rfloor\}.
$$</div>
<p>Indeed, $\lfloor n/2\rfloor\leq U$, $2L-2\leq U$, and $n-w\geq L$, as is checked by writing $n=3q+r$, $r\in\{0,1,2\}$. If one component has mass at least $L$, take it. Otherwise add components until the sum first reaches $L$; the sum is at most $2L-2$. Give the selected branches, including their edges to $v$, to the first piece and all other branches to the second. Both are nonempty and connected. Their marked endpoint counts are $s+w$ and $n-s$, which have the required bounds. The possible shared mark at $v$ is included in both counts.</p>
<p>Now put $t=3^{-k}N\geq1$. Starting with the whole tree, split any piece having at least $3t$ marked endpoints by this construction. Each child has at least $t$ marks. A split strictly decreases the number of marks in either child, since $\lceil2n/3\rceil&lt;n$ for integer $n\geq3$; alternatively, each split increases the number of nonempty parts of the finite edge set. Thus the procedure terminates. Every final piece has marked mass in $[t,3t)$, and their endpoint sets still cover the tree. Since they cover $A$, $3tm&gt;N$, giving $m&gt;3^{k-1}$. Endpoint sets may overlap; the edge sets do not.</p>

## Rooted damping from BK {#section-rooted-damping}

<a id="tag-12NL" data-assertion="theorem" data-title="Maximum and rooted intersection tails from finite witness splitting"></a>
<p>Consider independent bond percolation on a countable graph, with arbitrary edge probabilities, and a finite nonempty observation set $\Lambda$. Write $X_u=|K_u\cap\Lambda|$, $Z=\max_{x\in\Lambda}X_x$, and $M=\min\{n\geq1:\mathbb P(Z\geq n)\leq e^{-1}\}$. Then, for every real $\lambda\geq1$ and integer $k\geq1$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbb P(Z\geq3^k\lambda)&\leq\mathbb P(Z\geq\lambda)^{3^{k-1}+1},\\
\mathbb P(X_u\geq3^k\lambda)&\leq\mathbb P(X_u\geq\lambda)\mathbb P(Z\geq\lambda)^{3^{k-1}}\qquad(u\in V).
\end{aligned}
$$</div>
<p>Consequently, for $r\geq1$ and $0&lt;\varepsilon\leq1$,</p>
<div class="math-display">$$
\mathbb P(Z\geq rM)\leq e^{-r/9},\qquad
\mathbb P(X_u\geq rM)\leq e^{1-r/9}\mathbb P(X_u\geq M),\qquad
\mathbb P(Z&lt;\varepsilon M)\leq27\varepsilon.
$$</div>
<p><em>Proof.</em> First take a finite graph. On $X_u\geq3^k\lambda$, choose a spanning tree of the open cluster of $u$, marking its vertices in $\Lambda$. The splitting lemma supplies at least $3^{k-1}+1$ disjoint open edge sets. Each connects at least $\lambda$ marked vertices and therefore witnesses $Z\geq\lambda$. At least one contains $u$ and witnesses $X_u\geq\lambda$. Keep that piece and any $3^{k-1}$ others. BK bounds their disjoint occurrence by the product in the second inequality. The first follows in the same way from any cluster attaining the maximum, without prescribing a root. No union bound over choices of pieces is needed: their existence is precisely disjoint occurrence.</p>
<p>For a countable graph, exhaust the edge set by finite sets and keep $\Lambda\cup\{u\}$ as vertices. Every connection used here has a finite path, so the threshold events increase to those in the full graph. Passing to the limit proves both inequalities without local finiteness or summability assumptions. Paths may leave $\Lambda$.</p>
<p>If $1\leq r\leq9$, monotonicity and the quantile definition give the maximum bound, while $e^{1-r/9}\geq1$ gives the rooted bound. If $r\geq9$, take $k=\lfloor\log_3 r\rfloor$ and $\lambda=M$. Then $3^k\leq r$ and $3^{k-1}&gt;r/9$; the two amplification inequalities and $\mathbb P(Z\geq M)\leq e^{-1}$ give the asserted bounds, in fact a slightly smaller rooted factor.</p>
<p>For the lower tail, the claim is immediate if $27\varepsilon\geq1$ or $\varepsilon M\leq1$. Otherwise put $k=\lfloor\log_3(1/\varepsilon)\rfloor-1$ and $\lambda=(M-1)/3^k$. Then $k\geq1$, $\lambda\geq\varepsilon M&gt;1$, and $3^{k-1}&gt;1/(27\varepsilon)$. Since $M\geq2$ and $\mathbb P(Z\geq M-1)&gt;e^{-1}$, amplification gives, with $p=\mathbb P(Z\geq\varepsilon M)$,</p>
<div class="math-display">$$
e^{-1}&lt;\mathbb P(Z\geq M-1)\leq\mathbb P(Z\geq\lambda)^{3^{k-1}+1}\leq p^{1/(27\varepsilon)}.
$$</div>
<p>Hence $1-p\leq1-e^{-27\varepsilon}\leq27\varepsilon$.</p>
<p>This proves the rooted damping hypothesis used in the <a href="#section-finite-set">finite-set estimate</a>. Applied with the whole finite block as the observation set and all exterior edges removed, it also supplies rooted damping in <a href="/tag/655W/">the hierarchical sibling recursion</a>. The argument uses the marked-tree and BK mechanism; published locators are <a href="https://arxiv.org/pdf/2008.11197v2#page=14">Theorems 2.2–2.3 and Lemma 2.4, pp. 14–18</a>. The centroid construction above gives a separate proof of the splitting step. These are prose proofs, not claims of Lean compilation or reviewed source correspondence.</p>

## Bounds from window tails alone {#section-window-tails}

<a id="tag-UVQ6" data-assertion="theorem" data-title="Finite-window hyperscaling with explicit tail-exponent constants"></a>
<p>In independent bond percolation on a countable graph, let $\Lambda$ be finite and nonempty. Suppose $A&gt;0$, $0\leq\theta&lt;1$, and</p>
<div class="math-display">$$\mathbb P(|K_u\cap\Lambda|\geq n)\leq An^{-\theta}\qquad(u\in V,\ n\geq1).$$</div>
<p>With $M$ the largest-intersection quantile, put $H_\theta=(1-\theta)^{-1}+9e^{8/9}$. Then</p>
<div class="math-display">$$
M\leq(4eH_\theta A|\Lambda|)^{1/(1+\theta)},\qquad
\sum_{v\in\Lambda}\mathbb P(u\leftrightarrow v)
\leq H_\theta(4eH_\theta)^{(1-\theta)/(1+\theta)}A^{2/(1+\theta)}|\Lambda|^{(1-\theta)/(1+\theta)}.
$$</div>
<p>In particular, for $0\leq\theta\leq1/2$ the second prefactor can be replaced by the universal constant $4e(2+9e^{8/9})^2$. The assumption concerns intersections with this one window, not full-cluster volumes; it includes roots outside $\Lambda$.</p>
<p><em>Proof.</em> Write $X_u=|K_u\cap\Lambda|$. The <a href="/tag/12NL/">rooted-tail bound</a> supplies exponential damping above $M$. Summing the assumed tail up to $M$ and the damped tail afterwards gives, also when $\theta=0$,</p>
<div class="math-display">$$
\mathbb E X_u\leq A\sum_{n=1}^M n^{-\theta}+AeM^{-\theta}\sum_{n&gt;M}e^{-n/(9M)}
\leq A H_\theta M^{1-\theta}.
$$</div>
<p>The first sum is at most $M^{1-\theta}/(1-\theta)$, and the second is bounded by its decreasing-integrand comparison on $[M,\infty)$. As in <a href="/tag/WRHL/">the pair-count argument</a>, the partition identity and quantile minimality give</p>
<div class="math-display">$$
\frac{M^2}{4e}\leq\mathbb E Z^2\leq\sum_{x\in\Lambda}\mathbb E X_x
\leq |\Lambda|A H_\theta M^{1-\theta}.
$$</div>
<p>This proves the quantile estimate. Substitute it into the bound on $\mathbb E X_u=\sum_{v\in\Lambda}\mathbb P(u\leftrightarrow v)$ to obtain the second estimate. For $\theta\leq1/2$, $H_\theta\leq H=2+9e^{8/9}$ and $0\leq(1-\theta)/(1+\theta)\leq1$, so its prefactor is at most $H(4eH)$.</p>
<p>A uniform full-cluster tail implies the displayed window-tail hypothesis by inclusion. On a transitive model, a tail bound at one root is uniform in the root. This gives the probability inequality quoted in <a href="https://arxiv.org/pdf/2103.17013v1#page=16">Theorem 2.14</a>, with a constant independent of $\theta\in[0,1/2]$. The integer threshold is $n\geq1$; the source's displayed use of $n$ with a quantifier on a different variable is not copied here.</p>

## Keeping the polynomial tail under damping {#section-polynomial-damping}

<a id="tag-MJEP" data-assertion="corollary" data-title="Polynomial window tails with exponential damping and fractional moments"></a>
<p>In independent bond percolation on a countable graph, fix a finite nonempty window $\Lambda$ and any root $u$. Let $X=|K_u\cap\Lambda|$ and let $M$ be the largest-intersection quantile of $\Lambda$. If $A&gt;0$, $0\leq\theta&lt;1$, and $\mathbb P(X\geq n)\leq An^{-\theta}$ for every integer $n\geq1$, then</p>
<div class="math-display">$$\mathbb P(X\geq n)\leq eA\left(\frac{18}{n}\right)^\theta e^{-n/(18M)}\qquad(n\geq1).$$</div>
<p>For every real $p&gt;\theta$, this implies</p>
<div class="math-display">$$\mathbb E X^p\leq eA\,18^p p\,\Gamma(p-\theta)M^{p-\theta}.$$</div>
<p>The polynomial-tail assumption is needed only at this root. The scale $M$ still concerns the maximum over the window, not a quantile of $X$.</p>
<p><em>Proof.</em> For $n\leq18M$, the multiplier $e18^\theta e^{-n/(18M)}$ is at least one, so the assumed polynomial bound suffices. For $n&gt;18M$, <a href="/tag/12NL/">rooted damping</a> gives</p>
<div class="math-display">$$\mathbb P(X\geq n)\leq eAM^{-\theta}e^{-n/(9M)}.$$</div>
<p>Set $x=n/(18M)&gt;1$. Since $x^\theta e^{-x}\leq1$, the last expression is at most $eAM^{-\theta}x^{-\theta}e^{-x}$, which is the desired bound.</p>
<p>For $t&gt;0$, integer-valuedness and the fact that $s^{-\theta}e^{-s/(18M)}$ decreases give</p>
<div class="math-display">$$\mathbb P(X&gt;t)=\mathbb P(X\geq\lfloor t\rfloor+1)\leq eA18^\theta t^{-\theta}e^{-t/(18M)}.$$</div>
<p>Integrate against $pt^{p-1}\,dt$ and substitute $s=t/(18M)$. The integral at zero converges because $p&gt;\theta$; the exponential handles infinity. This gives the displayed gamma factor. In particular, $p=1$ yields $\mathbb E X\leq18eA\Gamma(1-\theta)M^{1-\theta}$.</p>
<p>The tail estimate is the assertion of <a href="https://arxiv.org/pdf/2008.11197v2#page=18">Corollary 2.6</a>; the first-moment case is the estimate used in its proof of Theorem 2.5. The fractional-moment conclusion records the same integration for $p&gt;\theta$. It makes no claim of a matching lower bound or an asymptotic moment formula.</p>

## Closing a power-law amplitude bootstrap {#section-amplitude-bootstrap}

<a id="tag-C9N6" data-assertion="proposition" data-title="Uniform tail amplitude from a two-scale contraction"></a>
<p>Fix real numbers $d&gt;0$, $0&lt;\alpha&lt;d$, $C_0&gt;0$ and an integer $r_0\geq1$, and put</p>
<div class="math-display">$$\theta=\frac{d-\alpha}{2d+\alpha},\qquad D=C_0\bigl((r_0+1)^{\alpha/2}+1\bigr),\qquad B=\max\{1,D^{(1+\theta)/(2\theta)}\}.$$</div>
<p>Let $p:\mathbb N_{\geq1}\to[0,1]$ satisfy $p(1)=1$ and $\sum_{n\geq1}p(n)&lt;\infty$. Assume that whenever $A\geq1$ satisfies $p(n)\leq An^{-\theta}$ for all $n\geq1$, one has, for all integers $n\geq1$ and $r\geq r_0$,</p>
<div class="math-display">$$p(n)^2\leq C_0\left[A r^{\alpha/2}n^{-(1+2\theta)/2}+A^{2/(1+\theta)}r^{-2d\theta/(1+\theta)}\right].$$</div>
<p>Assume also that $p$ is nonincreasing. Then $p(n)\leq Bn^{-\theta}$ for all $n\geq1$. The bound depends only on $d,\alpha,C_0,r_0$, not on $\sum_n p(n)$.</p>
<p><em>Proof.</em> Since $0&lt;\theta&lt;1/2$, monotonicity gives $np(n)\leq\sum_kp(k)$ and hence</p>
<div class="math-display">$$1\leq M:=\sup_{n\geq1}n^\theta p(n)&lt;\infty.$$</div>
<p>The supremum need not be attained. Its definition nevertheless gives $p(n)\leq Mn^{-\theta}$ for every $n$, so the assumed estimate applies with $A=M$. Set $s=(1-2\theta)/\alpha$ and choose the integer $r=\lceil r_0n^s\rceil$. Then $n^s\leq r\leq(r_0+1)n^s$. The identity $d(1-2\theta)=\alpha(1+\theta)$ makes both powers of $n$ in the estimate equal to $-2\theta$. Since $M\geq1$ and $2/(1+\theta)&gt;1$, it follows that</p>
<div class="math-display">$$p(n)^2\leq D M^{2/(1+\theta)}n^{-2\theta}.$$</div>
<p>Take square roots and then the supremum over $n$. This yields $M\leq\sqrt D\,M^{1/(1+\theta)}$. Dividing by the positive power of $M$ gives $M\leq D^{(1+\theta)/(2\theta)}\leq B$, as claimed.</p>
<p>In particular, consider independent bond percolation on a countable graph with root $o$, indexed by $0&lt;\beta\leq b&lt;\infty$. Suppose each edge probability $q_e(\beta)$ is nondecreasing and satisfies $q_e(\beta)\uparrow q_e(b)$ as $\beta\uparrow b$. If $\mathbb E_\beta|K_o|&lt;\infty$ for every $\beta&lt;b$, and the displayed two-term implication holds for $p_\beta(n)=\mathbb P_\beta(|K_o|\geq n)$ with the same constants for all such $\beta$, then</p>
<div class="math-display">$$\mathbb P_b(|K_o|\geq n)\leq Bn^{-\theta}\qquad(n\geq1).$$</div>
<p>Indeed, tail summation gives the required summability below $b$. Couple the bonds by independent uniforms $U_e$, declaring $e$ open when $U_e&lt;q_e(\beta)$. An open edge at $b$ is open at some smaller parameter, and any finite collection of such edges is simultaneously open sufficiently near $b$. The event $|K_o|\geq n$ has a finite witness: paths from $o$ to $n$ distinct vertices. Thus, along any sequence $\beta_k\uparrow b$, these events increase to their event at $b$. Continuity from below carries the uniform tail bound to the endpoint. No continuity of the infinite-cluster event is asserted.</p>
<p>This isolates the amplitude contraction and endpoint passage in <a href="https://arxiv.org/pdf/2008.11197v2#page=29">Section 4 of the power-law paper</a>. The first term in the assumed squared-tail estimate is linear in $A$, while the second has power $2/(1+\theta)$; taking the square root only after bounding both terms preserves the contraction. The proposition does not derive that estimate from the graph, identify $b$ with the percolation threshold, or establish subcritical finite susceptibility. Those are separate inputs, so this conditional closure is not a proof of the paper's full critical-tail theorem.</p>

## The greedy source proof of splitting {#section-greedy-source}

<p>The source gives a second proof of <a href="/tag/DMI0/">DMI0</a> which does not use acyclicity. Let $E$ be a finite loopless edge set, connected on its endpoints, and let $A$ consist of $N$ marked endpoints. Put $w=N/3^k\geq1$, and write $W(P)$ for the number of marks incident to edges of a piece $P$. The induction partitions $E$ into completed connected pieces and at most one remaining connected piece incident to a chosen root. Each completed piece has weight at least $w$ and either weight less than $2w$ or weight at most two. The remaining piece has weight less than $w$.</p>
<p>To carry out the induction, remove an edge $xc$ incident to the root. In the remaining graph, take the component of $c$ and the other edges. If any other edges remain, their endpoints are connected to $x$; deleting one edge from a connected graph creates at most two components. Apply induction to these smaller edge sets. Attach $xc$ to the remaining piece at $c$, or keep it as a single-edge piece if there is no remainder there. Attaching it introduces at most one new marked endpoint. A single edge has at most two marks. Complete this piece if its weight reaches $w$; otherwise merge it with the remaining piece at $x$, which shares that endpoint, and again complete the union if it reaches $w$.</p>
<p>These operations preserve the invariant because $W(P\cup Q)\leq W(P)+W(Q)$, and adjoining an edge at an existing endpoint increases weight by at most one. In particular, two remaining pieces have combined weight less than $2w$. The allowance for a single edge of weight two handles the endpoint $w=1$; it must not be replaced by a strict bound below $2w$.</p>
<p>At the end, merge a nonempty remainder with a completed piece that it touches. Such a piece exists: otherwise the remainder would carry all $N\geq w$ marks despite having weight below $w$; connectedness then supplies a first crossing from the remainder to a completed piece. The union is connected and has weight at least $w$ and less than $3w$. The same upper bound holds for all other completed pieces, including a piece of weight at most two because $w\geq1$.</p>
<p>The resulting pieces partition every edge of $E$, so they cover every endpoint, including a prescribed unmarked root. Marks may occur in more than one piece. Consequently the counting step is an inequality, not an equality:</p>
<div class="math-display">$$N\leq\sum_P W(P)&lt;3w\,m,$$</div>
<p>which gives $m&gt;3^{k-1}$ and hence at least $3^{k-1}+1$ pieces. For a finite tree with $N\geq3^k\geq3$, every vertex is an edge endpoint, recovering DMI0 exactly. The source's more general connected-edge statement is useful in the <a href="/articles/window-tightness-interfaces/#section-source-proof">direct finite-witness BK proof</a>, where taking a spanning tree is unnecessary.</p>
<p>The <a href="/coverage/sources/perclib-caed44f-tightness/">nine-contract splitting inventory</a> records this alternative argument separately from the preserved centroid proof. Both keep the strict upper marked-mass bound and root coverage needed by the provisional source correction.</p>


## Spatial two-cluster estimates {#section-spatial-bootstrap}

<a id="tag-XHZD" data-assertion="proposition" data-title="Power-law amplitude improvement on the lattice"></a>
<p>Let $d\geq1$ be an integer and let $J:\mathbb Z^d\setminus\{0\}\to(0,\infty)$ be symmetric, with $L=\sum_{z\ne0}J(z)&lt;\infty$. Suppose that, for some $0&lt;\alpha&lt;d$, $c&gt;0$ and integer $r_0\geq1$,</p>
<div class="math-display">$$J(z)\geq c\|z\|_1^{-d-\alpha}\qquad(\|z\|_1\geq r_0).$$</div>
<p>Use independent bonds of probabilities $1-e^{-\beta J(y-x)}$, and put $\theta=(d-\alpha)/(2d+\alpha)\in(0,1/2)$. There is a constant $C\geq1$, depending on the kernel parameters but not on $\beta$ or $A$, such that for every $0\leq\beta&lt;\beta_c$ and $A\geq1$,</p>
<div class="math-display">$$\bigl[\mathbb P_\beta(|K_0|\geq n)\leq An^{-\theta}\text{ for every integer }n\geq1\bigr]\quad\Longrightarrow\quad\mathbb P_\beta(|K_0|\geq n)\leq C A^{1/(1+\theta)}n^{-\theta}\quad(n\geq1).$$</div>
<p><em>Proof.</em> Replace $J$ by $J/L$ and $\beta$ by $\beta L$. This preserves the bond law and makes the off-diagonal row sum one; the lower-envelope constant becomes $c/L$. We work in this normalization. If $\beta\leq1/2$, path counting gives $\chi_\beta\leq(1-\beta)^{-1}\leq2$, so Markov's inequality proves the claim with $C=2$. Henceforth $\beta\geq1/2$; constants may depend on $d,\alpha,c/L,r_0$.</p>
<p>Write $f(n)=\mathbb P_\beta(|K_0|\geq n)$, $\tau(x)=\mathbb P_\beta(0\leftrightarrow x)$, and let $S_{x,n}$ be the event that $0$ and $x$ lie in distinct clusters of size at least $n$. Below $\beta_c$ both clusters are finite almost surely, and their intervening edge is necessarily closed. The translation action satisfies vertex mass transport by reindexing $x$ as $-x$, and each unoriented edge orbit has two edges incident to the root. All bond probabilities lie in $(0,1)$. Thus <a href="/tag/75N0/">the two-cluster volume bound</a> gives</p>
<div class="math-display">$$\sum_{x\ne0}(e^{\beta J(x)}-1)\mathbb P_\beta(S_{x,n})^2\leq C_1 A^2 n^{-1-2\theta}.$$</div>
<p>Let $Q_R=[-R,R]^d\cap\mathbb Z^d$ and $D_R=Q_R\setminus Q_{r_0-1}$, where the integer $R\geq2r_0$. Then $|D_R|$ is bounded above and below by positive constants times $R^d$. On $D_R$ the envelope applies, $\|x\|_1\leq dR$ and $e^{\beta J(x)}-1\geq\beta J(x)\geq c_1R^{-d-\alpha}$. Weighted Cauchy–Schwarz therefore yields</p>
<div class="math-display">$$\begin{aligned}
\frac1{|D_R|}\sum_{x\in D_R}\mathbb P_\beta(S_{x,n})
&\leq\frac1{|D_R|}\left(\sum_{x\ne0}(e^{\beta J(x)}-1)\mathbb P_\beta(S_{x,n})^2\right)^{1/2}
\left(\sum_{x\in D_R}\frac1{e^{\beta J(x)}-1}\right)^{1/2}\\
&\leq C_2 A n^{-1/2-\theta}R^{\alpha/2}.
\end{aligned}$$</div>
<p>The full-volume tail bound holds at every root by translation invariance. It bounds every window tail as well, so <a href="/tag/UVQ6/">finite-set hyperscaling</a>, applied directly to $D_R$, gives</p>
<div class="math-display">$$\frac1{|D_R|}\sum_{x\in D_R}\tau(x)\leq C_3 A^{2/(1+\theta)}R^{-2d\theta/(1+\theta)}.$$</div>
<p>Harris's inequality and the alternative that the two large clusters coincide give $f(n)^2\leq\mathbb P_\beta(S_{x,n})+\tau(x)$. Averaging over $D_R$ proves</p>
<div class="math-display">$$f(n)^2\leq C_4\left[A n^{-1/2-\theta}R^{\alpha/2}+A^{2/(1+\theta)}R^{-2d\theta/(1+\theta)}\right].$$</div>
<p>Choose $R=\lceil2r_0n^{(1-2\theta)/\alpha}\rceil$. It lies between $n^{(1-2\theta)/\alpha}$ and $(2r_0+1)n^{(1-2\theta)/\alpha}$. The identity $d(1-2\theta)=\alpha(1+\theta)$ makes both powers of $n$ equal to $-2\theta$. Since $A\geq1$ and $2/(1+\theta)&gt;1$, the last display is at most $C_5 A^{2/(1+\theta)}n^{-2\theta}$. Taking square roots proves the implication.</p>
<p>This supplies the probabilistic input left open in <a href="/tag/C9N6/">the earlier conditional closure</a>. The squared estimate contains $A^2$, and its Cauchy–Schwarz consequence contains $A$. These powers suffice for the contraction. The discrepancy with the displayed powers in the arXiv and publisher-HTML proofs of Lemma 4.1 is recorded in the <a href="/errata/hutchcroft-powerlaw-2021/">version-specific errata</a>; no sharper two-ghost constant is needed here.</p>

## The critical power-law bound {#section-critical-powerlaw}

<a id="tag-KXV3" data-assertion="theorem" data-title="Critical cluster tails under a power-law lower envelope"></a>
<p>Under the hypotheses of <a href="/tag/XHZD/">the preceding lemma</a>, the critical intensity satisfies $0&lt;\beta_c&lt;\infty$. There is $B&lt;\infty$ such that, for every $0\leq\beta\leq\beta_c$, integer $n\geq1$ and real $R\geq1$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_0|\geq n)\leq Bn^{-\theta},\qquad \frac1{|Q_R|}\sum_{x\in Q_R}\mathbb P_\beta(0\leftrightarrow x)\leq B R^{-2(d-\alpha)/3},\qquad\theta=\frac{d-\alpha}{2d+\alpha}.$$</div>
<p>There are almost surely no infinite clusters at $\beta_c$.</p>
<p><em>Proof.</em> The row-sum bound gives $\beta_c\geq1/L&gt;0$. The <a href="/tag/DYUM/">sharpness theorem</a>, including its infinite-threshold case, gives $\chi_\beta&lt;\infty$ for every finite $\beta&lt;\beta_c$. Consequently</p>
<div class="math-display">$$1\leq A_\beta:=\sup_{n\geq1}n^\theta\mathbb P_\beta(|K_0|\geq n)\leq\chi_\beta&lt;\infty.$$</div>
<p>The supremum need not be attained at an integer, but it is an admissible amplitude. The preceding lemma gives $A_\beta\leq C A_\beta^{1/(1+\theta)}$, hence $A_\beta\leq C^{(1+\theta)/\theta}=:B_0$, uniformly below criticality.</p>
<p>This already forces $\beta_c&lt;\infty$. Otherwise the uniform estimate would hold at every finite intensity. Choose an integer $n$ with $B_0n^{-\theta}&lt;1$, and fix $n-1$ distinct nonzero vertices. All the edges from the origin to these vertices have positive intensity, so the probability that they are all open tends to one as $\beta\to\infty$. On that event $|K_0|\geq n$, contradicting the uniform bound.</p>
<p>Couple all intensities by independent uniforms, with a bond open when $U_e&lt;1-e^{-\beta J(e)}$. Each bond open at the finite parameter $\beta_c$ is open at some smaller parameter. The event $|K_0|\geq n$ has a finite witness, namely paths to $n$ distinct vertices, so along any sequence $\beta_k\uparrow\beta_c$ its indicators increase to the critical indicator. Continuity from below transfers the uniform bound to $\beta_c$. Letting $n\to\infty$ shows that the root cluster is finite almost surely. Translation invariance and a countable union give the assertion for every cluster.</p>
<p>Finally apply UVQ6 at any $\beta\leq\beta_c$, with the uniform amplitude $B_0$ and observation set $Q_R$. Its normalized connection sum is at most a constant times $|Q_R|^{-2\theta/(1+\theta)}$. Since $|Q_R|$ is comparable to $R^d$ for $R\geq1$ and $2d\theta/(1+\theta)=2(d-\alpha)/3$, this is the displayed spatial bound after enlarging $B$.</p>
<p>The cluster-tail exponent and critical-continuity conclusion are those of <a href="https://arxiv.org/pdf/2008.11197v2#page=2">Theorem 1.1</a>. Its displayed equation (1.3) uses the weaker radius exponent $2(d-\alpha)/(3d)$; the estimate proved here implies that bound too, since $d\geq1$ and $R\geq1$. We have retained the volume-to-radius conversion explicitly. No pointwise two-point decay or existence of critical exponents is asserted. Integrability together with the lower envelope forces $\alpha&gt;0$: summing the envelope over disjoint dyadic annuli would otherwise diverge. Thus writing $0&lt;\alpha&lt;d$ makes an implicit restriction in the source explicit.</p>

## Many edges above each weight threshold {#section-weight-threshold}

<a id="tag-58BJ" data-assertion="theorem" data-title="Critical cluster tails from the edge-weight counting function"></a>
<p>Let $G=(V,E)$ be a countable simple graph with positive edge weights $J(e)$, preserved by a transitive group satisfying the vertex mass-transport principle of <a href="/tag/M9TT/">M9TT</a>. Suppose $L=\sum_{e\ni o}J(e)&lt;\infty$ and, for some $1/2&lt;a&lt;1$, $c&gt;0$ and $\varepsilon_0&gt;0$,</p>
<div class="math-display">$$N(\varepsilon):=\bigl|\{x:\{o,x\}\in E,\ J(\{o,x\})\geq\varepsilon\}\bigr|\geq c\varepsilon^{-a}\qquad(0&lt;\varepsilon\leq\varepsilon_0).$$</div>
<p>For independent bonds with probabilities $1-e^{-\beta J(e)}$, there are $0&lt;\beta_c&lt;\infty$ and $B&lt;\infty$ such that, for every integer $n\geq1$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|\geq n)\leq Bn^{-\theta},\qquad \theta=\frac{2a-1}{a+1}\in(0,1/2),\qquad 0\leq\beta\leq\beta_c,\ n\geq1.$$</div>
<p>In particular there are almost surely no infinite clusters at criticality.</p>
<p><em>Proof.</em> Replace $J$ by $J/L$ and $\beta$ by $\beta L$; the threshold-count parameters become $cL^{-a}$ and $\varepsilon_0/L$. We work with the resulting unit row sum. The small-intensity bound again handles $\beta\leq1/2$. Fix $1/2\leq\beta&lt;\beta_c$ and an amplitude $A\geq1$ with $f(n):=\mathbb P_\beta(|K_o|\geq n)\leq An^{-\theta}$. Each edge orbit has finitely many edges at $o$: its edges all have the same positive weight, and the row sum is finite. Hence 75N0 applies, giving a square-sum bound $C A^2n^{-1-2\theta}$ for the two-cluster coefficients.</p>
<p>Set $D_\varepsilon=\{x:\{o,x\}\in E,\ J(\{o,x\})\geq\varepsilon\}$. Simplicity identifies these vertices with the indicated root edges, and summability gives $|D_\varepsilon|\leq1/\varepsilon$. As before let $S_{x,n}$ denote two distinct clusters of size at least $n$. Cauchy–Schwarz and $e^{\beta J(e)}-1\geq\varepsilon/2$ give</p>
<div class="math-display">$$\frac1{|D_\varepsilon|}\sum_{x\in D_\varepsilon}\mathbb P_\beta(S_{x,n})\leq C_1 A n^{-1/2-\theta}(\varepsilon|D_\varepsilon|)^{-1/2}\leq C_2 A n^{-1/2-\theta}\varepsilon^{-(1-a)/2}.$$</div>
<p>By UVQ6 and the same lower bound on $|D_\varepsilon|$,</p>
<div class="math-display">$$\frac1{|D_\varepsilon|}\sum_{x\in D_\varepsilon}\mathbb P_\beta(o\leftrightarrow x)\leq C_3 A^{2/(1+\theta)}\varepsilon^{2a\theta/(1+\theta)}.$$</div>
<p>Harris's inequality now gives</p>
<div class="math-display">$$f(n)^2\leq C_4\left[A n^{-1/2-\theta}\varepsilon^{-(1-a)/2}+A^{2/(1+\theta)}\varepsilon^{2a\theta/(1+\theta)}\right].$$</div>
<p>Take $\varepsilon=\min\{1,\varepsilon_0\}n^{-(1-2\theta)/(1-a)}$. The identity $a(1-2\theta)=(1-a)(1+\theta)$ makes both powers of $n$ equal to $-2\theta$. Since $A\leq A^{2/(1+\theta)}$, taking square roots yields $f(n)\leq C_5 A^{1/(1+\theta)}n^{-\theta}$. The constants are independent of $A$, $\beta$ and $n$.</p>
<p>Sharpness gives finite susceptibility below $\beta_c$, so the best-amplitude argument in <a href="/tag/KXV3/">the lattice proof</a> gives a uniform tail. It also proves that $\beta_c$ is finite: $N(\varepsilon)\to\infty$ as $\varepsilon\downarrow0$, so the root has arbitrarily large finite stars of positive-intensity edges, whose probability of being open tends to one as $\beta\to\infty$. The same finite-witness coupling passes to $\beta_c$ and excludes infinite clusters. Positivity of $\beta_c$ follows from the row-sum bound.</p>
<p>This proves <a href="https://arxiv.org/pdf/2008.11197v2#page=4">Theorem 1.2</a> with the needed mass-transport property stated explicitly. In the bootstrap, the power $\varepsilon^{-(1-a)/2}$ must be retained through the scale choice. Replacing it by $\varepsilon^{-1/2}$ loses the balance of exponents. This second intermediate discrepancy occurs in both the arXiv proof and the publisher HTML, and is recorded separately in the errata. Neither discrepancy changes the theorem's conclusion.</p>

## The earlier square-root contraction {#section-elementary-bootstrap}

<a id="tag-BWH0" data-assertion="proposition" data-title="Elementary power-law bootstrap below one quarter of the dimension"></a>
<p>Let $d\geq1$ be an integer and let $J:\mathbb Z^d\setminus\{0\}\to[0,\infty)$ be symmetric and summable, with $J(z)\geq c\|z\|_1^{-d-\alpha}$ for $\|z\|_1\geq r_0$, where $c&gt;0$, the integer $r_0\geq1$, and $0&lt;\alpha&lt;d/4$. Put $\eta=(d-4\alpha)/(4d)\in(0,1/4)$. There is $B&lt;\infty$ such that, for every integer $n\geq1$,</p>
<div class="math-display">$$0&lt;\beta_c&lt;\infty,\qquad\mathbb P_\beta(|K_0|\geq n)\leq Bn^{-\eta}\qquad(0\leq\beta\leq\beta_c,\ n\geq1).$$</div>
<p><em>Proof.</em> Normalize the off-diagonal row to one and retain only edges of positive intensity. Their probabilities are in $(0,1)$ for every finite $\beta&gt;0$; zero-intensity coordinates play no role in connectivity. Apply the weighted part of 75N0 with tail exponent zero and amplitude one. For a finite symmetric displacement set $F$ with $s_F=\sum_{z\in F}J(z)&gt;0$, use the invariant weights $w_F(\{x,x+z\})=J(z)\mathbf1_{\{z\in F\}}/s_F$. Their rows are normalized and their square-root row sums are finite. Multiplying the resulting inequality by $\sqrt{s_F}\leq1$ and exhausting the displacement set gives</p>
<div class="math-display">$$\sum_{z\ne0}\sqrt{J(z)(e^{\beta J(z)}-1)}\,\mathbb P_\beta(S_{z,n})\leq C_0n^{-1/2}\qquad(0&lt;\beta&lt;\beta_c).$$</div>
<p>This limiting argument does not assume that $\sum_z\sqrt{J(z)}$ is finite. For $\beta\geq1/2$, division by the lower envelope on $D_R=Q_R\setminus Q_{r_0-1}$ gives $|D_R|^{-1}\sum_{z\in D_R}\mathbb P_\beta(S_{z,n})\leq C_1R^\alpha n^{-1/2}$. If $f(n)\leq An^{-\eta}$, the elementary truncated-mean bound gives</p>
<div class="math-display">$$\sum_{z\in D_R}\mathbb P_\beta(0\leftrightarrow z)\leq\mathbb E_\beta\min\{|K_0|,|D_R|\}=\sum_{k=1}^{|D_R|}f(k)\leq\frac{A}{1-\eta}|D_R|^{1-\eta}.$$</div>
<p>Harris and averaging therefore yield $f(n)^2\leq C_2[R^\alpha n^{-1/2}+A R^{-d\eta}]$. Choose $R=\lceil2r_0 n^{2/d}\rceil$. Both powers are $n^{-2\eta}$, so $f(n)\leq C_3\sqrt A\,n^{-\eta}$. Small intensities again use $\chi_\beta\leq2$. Sharpness makes $A_\beta=\sup_n n^\eta f_\beta(n)$ finite, and $A_\beta\leq C_3\sqrt{A_\beta}$ bounds it uniformly by $C_3^2$. The finite-star and finite-witness arguments above prove finiteness of $\beta_c$ and the critical endpoint bound.</p>
<p>This is the mechanism of <a href="https://arxiv.org/pdf/2008.11197v2#page=8">Proposition 1.4</a>. It uses neither the finite-set hyperscaling estimate nor a positive tail exponent in the two-ghost input. The numerical two-ghost constant here is weaker than the paper's constant 42, which is immaterial for this contraction. Allowing zero intensities at short displacements causes no singular environment probabilities on the retained host.</p>


## A summable model on every countable group {#section-group-kernel}

<a id="tag-S01U" data-assertion="corollary" data-title="A nontrivial long-range transition on every countably infinite group"></a>
<p>Let $G$ be a countably infinite group, fix a bijection $\sigma:G\to\{1,2,\ldots\}$ and choose $1&lt;s&lt;2$. Define</p>
<div class="math-display">$$j(g)=\sigma(g)^{-s}+\sigma(g^{-1})^{-s}\quad(g\ne e),\qquad J(x,y)=j(yx^{-1})\quad(x\ne y).$$</div>
<p>The independent bond model with probabilities $1-e^{-\beta J(x,y)}$ has $0&lt;\beta_c&lt;\infty$ and satisfies, for some $B&lt;\infty$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_e|\geq n)\leq Bn^{-(2-s)/(1+s)}\qquad(0\leq\beta\leq\beta_c,\ n\geq1\text{ an integer}).$$</div>
<p><em>Proof.</em> Inversion symmetry makes the intensity symmetric, and the off-diagonal row is at most $2\sum_{k\geq1}k^{-s}&lt;\infty$. Right translations preserve $yx^{-1}$ and act transitively. For a nonnegative invariant vertex transport, $m(e,g)=F(g)$ and $m(g,e)=F(g^{-1})$; inversion reindexes the sum, proving mass transport.</p>
<p>For $0&lt;\varepsilon\leq4^{-s}$, every $g\ne e$ with $\sigma(g)\leq\varepsilon^{-1/s}$ has $j(g)\geq\varepsilon$. Removing the identity discards at most one vertex, and therefore</p>
<div class="math-display">$$\bigl|\{g\ne e:j(g)\geq\varepsilon\}\bigr|\geq\lfloor\varepsilon^{-1/s}\rfloor-1\geq\tfrac12\varepsilon^{-1/s}.$$</div>
<p>Apply <a href="/tag/58BJ/">the weight-threshold theorem</a> with $a=1/s$. Its tail exponent is $(2a-1)/(a+1)=(2-s)/(1+s)$. The model has infinitely many possible neighbours, and no finite generating set or Euclidean growth assumption has been used.</p>
<p>This proves the construction in <a href="https://arxiv.org/pdf/2008.11197v2#page=4">Remark 1.3</a>, using the wiki's right-translation convention. It establishes a long-range model on the group, not a percolation theorem for a chosen finite-degree Cayley graph.</p>


## Extending the partition beyond a finite marked core {#section-infinite-splitting}

<a id="tag-RZSW" data-assertion="proposition" data-title="Marked splitting with vertex coverage on an infinite locally finite graph"></a>
<p>Let $G=(V,E)$ be a connected locally finite graph, let $A\subseteq V$ be finite with $N=|A|$, and let $k\geq1$ be an integer with $N\geq3^k$. There are $m\geq3^{k-1}+1$ pairwise edge-disjoint nonempty sets $E_1,\ldots,E_m\subseteq E$, each spanning a connected subgraph, such that their endpoint sets $V_i$ satisfy</p>
<div class="math-display">$$\bigcup_{i=1}^m V_i=V,\qquad 3^{-k}N\leq|A\cap V_i|&lt;3^{1-k}N\quad(1\leq i\leq m).$$</div>
<p>If $G$ is a tree, the $E_i$ may be chosen to partition all its edges. The pieces may be infinite; the number of pieces and their marked endpoint counts are finite.</p>
<p><em>Proof.</em> Choose a spanning tree $T$ of $G$. For instance, root $G$ and choose for each other vertex one edge to a vertex at distance one less from the root; the chosen edges form a spanning tree. Local finiteness makes the distance balls finite, so this is a construction on a countable vertex set.</p>
<p>Let $T_0$ be the finite subtree of $T$ formed by the paths joining one fixed point of $A$ to the other points of $A$. It contains every mark. Apply <a href="/tag/DMI0/">the finite marked-tree partition</a> to $T_0$, obtaining connected edge pieces $F_1,\ldots,F_m$ whose endpoint sets cover $V(T_0)$ and whose marked counts have the required bounds.</p>
<p>Each component $H$ of $T\setminus V(T_0)$ attaches to $T_0$ by exactly one edge, at a vertex $v_H$. There is an attachment because $T$ is connected; two attachments would give a cycle using the path in $T_0$. Choose a piece $F_i$ incident to $v_H$, and add to it the attaching edge and every edge of $H$. Such a piece exists because the finite partition covers all core vertices.</p>
<p>These attachments preserve connectedness and edge disjointness, and cover every edge of $T$. They add no marks: all marks are in $T_0$, and each attachment meets $T_0$ only at a vertex already belonging to its assigned piece. Hence the marked counts and the number of pieces are unchanged. The resulting edge sets cover every vertex of $T$, and therefore of $G$. If $G=T$, they partition all of $E$.</p>
<p>This proves the infinite-graph formulation of <a href="https://link.springer.com/article/10.1007/s00440-021-01043-7">Lemma 2.4</a> from the finite splitting result, without carrying out an infinite splitting recursion. It preserves coverage of an unmarked prescribed root. For probabilistic BK applications one still uses finite open witnesses, as in 12NL; an infinite piece is not silently substituted for a finite certificate.</p>


## Endpoint passage by finite witnesses {#section-amplitude-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-limits/">amplitude source</a> proves the endpoint part of <a href="/tag/C9N6/">C9N6</a> under coordinatewise convergence of edge probabilities alone. Enumerate the possible edges and restrict to increasing finite sets $F_j$. For a fixed integer $n$, the event $|K_o|\geq n$ is the union of the corresponding restricted events, since paths to finitely many vertices use only finitely many edges. Each restricted probability is a polynomial in finitely many edge probabilities. Their supremum is therefore lower semicontinuous in the product topology.</p>
<p>Consequently, if $q(\beta)\to q(b)$ coordinatewise as $\beta\uparrow b$ and the tail probabilities below $b$ are at most $Bn^{-\theta}$, then the same bound holds at $b$. Monotonicity in $\beta$ is useful for the coupling proof above but is not required by this source argument. The endpoint is positive and finite; no transitivity is used, and neither finite susceptibility nor a finite mean cluster size is required at the endpoint.</p>
<p>Below $b$, summability is used to make the amplitude $\sup_{n\geq1}n^\theta p(n)$ finite before applying the contraction. The source chooses $r=\max\{r_0,\lceil n^{(1+\theta)/d}\rceil\}$, which satisfies the same two radius bounds used above and gives the same explicit constant $D$. The two-scale inequality itself remains an input.</p>


## Partition counting and the source hypotheses {#section-partition-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-windows/">window source</a> separates the partition argument from rooted damping. For every function $f$ of a trace size, the deterministic identity is $\sum_{x\in\Lambda}f(X_x)=\sum_D|D|f(|D|)$, where $D$ ranges over distinct nonempty cluster traces. Taking $f(s)=s^p$ gives the <a href="/tag/LQ6Y/">maximum-moment inequality</a>. Quantile minimality supplies its lower bound, including $p=0$ in the source. Neither step uses independence or exponential damping.</p>
<p>The passage from a polynomial tail to an upper bound on $\mathbb E X_u$ does use rooted damping. The source first states that implication at an arbitrary integer scale $M\geq1$, then specializes to the largest-intersection quantile. The subsequent bound on $M$ uses the tail assumption for every root in the window; the exported estimate for the connection sum at an arbitrary root uses that root's tail as well. This is why UVQ6 states a uniform assumption over all vertices. No transitivity is required when those uniform estimates are supplied directly.</p>

## Fractional moments and exponent matching {#section-fractional-source}

<p>For <a href="/tag/MJEP/">MJEP</a>, only the selected root's polynomial tail is needed. The source passes to real thresholds using $\{X\geq t\}=\{X\geq\lceil t\rceil\}$ for $t&gt;0$. Since $t^{-\theta}e^{-t/(18M)}$ decreases, the integer estimate gives the required real-threshold bound. Integration against $pt^{p-1}\,dt$ produces $\Gamma(p-\theta)$; the strict condition $p&gt;\theta$ is the integrability condition at zero, even though the window variable itself is bounded.</p>
<p>The exponent implications in <a href="/tag/7VCS/">7VCS</a> and <a href="/tag/DEZI/">DEZI</a> are separate analytic results. Existing logarithmic limits suffice for the former. The latter assumes the stronger two-sided comparisons and both matching relations stated in the article. Its source works with numerical functions, so a probabilistic application must still identify those functions with the indicated moments and tails.</p>


## Why lattice quantiles use a doubled window {#section-doubled-window-source}

<p>For translation-invariant bond percolation on $\mathbb Z^d$, let $B_n$ be the sup-norm ball of integer radius $n\geq0$, and let $M_n$ be the largest-intersection quantile in $B_n$. The <a href="/coverage/sources/perclib-dfbc5b4-moments-ghost/">lattice averaging source</a> proves, for every real $p&gt;0$,</p>
<div class="math-display">$$\mathbb E|K_0\cap B_{2n}|^p\geq\frac{(M_n-1)^{p+1}}{e(2n+1)^d}.$$</div>
<p>To see the doubling, suppose some cluster has at least $m$ vertices in $B_n$. Each of these vertices $x$ has at least those $m$ cluster vertices in $x+B_{2n}$, since differences of points in $B_n$ lie in $B_{2n}$. Hence</p>
<div class="math-display">$$m\mathbf1_{\{\max_{x\in B_n}|K_x\cap B_n|\geq m\}}
\leq\sum_{x\in B_n}\mathbf1_{\{|K_x\cap(x+B_{2n})|\geq m\}}.$$</div>
<p>Take expectations, translate each summand to the root, and use quantile minimality at $m=M_n-1\geq1$. This gives the tail bound $(M_n-1)/e\leq(2n+1)^d\mathbb P(|K_0\cap B_{2n}|\geq M_n-1)$, and the moment bound follows. No independence between the translated windows is needed.</p>
<p>The same lower bound holds for the full-cluster moment, even if it is infinite. All connections here use the ambient graph: the windows restrict the counted vertices, not the paths. For real radii, the lattice ball equals the ball at its integer floor, and $|B_r|/(2r)^d\to1$. These geometric facts do not supply any moment localization or upper bound; those are separate inputs in applications such as <a href="/tag/AS7A/">AS7A</a>.</p>



## A lower envelope with missing short bonds {#section-tail-envelope}

<a id="tag-AKFN" data-assertion="corollary" data-title="Critical nonpercolation under an eventual power-law lower bound"></a>
<p>Let $d\geq1$ and $0&lt;\alpha&lt;d$. Suppose $J:\mathbb Z^d\setminus\{0\}\to[0,\infty)$ is symmetric, has finite row sum, and satisfies</p>
<div class="math-display">$$J(z)\geq c|z|^{-d-\alpha}\qquad(|z|\geq r_0)$$</div>
<p>for some $c&gt;0$ and finite $r_0\geq1$. Open bonds independently with probabilities $1-e^{-\beta J(y-x)}$, and let $\beta_c$ be the infinite-root-cluster threshold. Then $0&lt;\beta_c&lt;\infty$, and for some $B&lt;\infty$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_0|\geq n)\leq Bn^{-(d-\alpha)/(2d+\alpha)}\qquad(0\leq\beta\leq\beta_c,\ n\geq1).$$</div>
<p>There are almost surely no infinite clusters at $\beta_c$. No positivity is required of the finitely many intensities with $|z|&lt;r_0$.</p>
<p><em>Proof.</em> Work on the graph whose edges are exactly the pairs with positive intensity; deleting zero-intensity coordinates does not change a cluster. Translations preserve this graph and its weights. They satisfy mass transport: for a nonnegative diagonally translation-invariant function $m$,</p>
<div class="math-display">$$\sum_xm(0,x)=\sum_xm(-x,0)=\sum_xm(x,0).$$</div>
<p>The graph is connected. Indeed, each coordinate vector is the difference of two sufficiently long integer vectors, both of positive intensity, and therefore is a sum of two permitted steps.</p>
<p>Set $a=d/(d+\alpha)\in(1/2,1)$ and $R_\varepsilon=(c/\varepsilon)^{1/(d+\alpha)}$. For small $\varepsilon&gt;0$, every lattice point with $r_0\leq|z|\leq R_\varepsilon$ has $J(z)\geq\varepsilon$. A fixed inner ball removes only finitely many points from this expanding ball, so</p>
<div class="math-display">$$\bigl|\{z:J(z)\geq\varepsilon\}\bigr|\geq c_1R_\varepsilon^d=c_2\varepsilon^{-a}.$$</div>
<p>Apply <a href="/tag/58BJ/">the edge-weight counting theorem</a> on the positive-edge graph. Its exponent is $(2a-1)/(a+1)=(d-\alpha)/(2d+\alpha)$, giving the tail estimate and both threshold bounds. Letting $n\to\infty$ and then taking a countable union over roots excludes every infinite cluster at criticality.</p>
<p>This supplies the nonnegative-kernel case of critical continuity. The earlier KXV3 retains its strictly positive-kernel statement. The extension uses a lower bound on the number of sufficiently heavy edges, rather than a comparison between the critical parameters of two different kernels.</p>



## From a spatial average to a volume tail {#section-spatial-average-tail}

<a id="tag-GW20" data-assertion="theorem" data-title="A spatial susceptibility bound controls the cluster-volume tail"></a>
<p>Let $d\geq1$ be an integer and let $J:\mathbb Z^d\setminus\{0\}\to(0,\infty)$ be symmetric and summable, and open bonds independently with probabilities $1-e^{-\beta J(y-x)}$, where $\beta&gt;0$. Suppose $\chi_\beta&lt;\infty$ and, for constants $c&gt;0$, $\alpha&gt;0$, $B&gt;0$ and $0\leq\gamma&lt;d$,</p>
<div class="math-display">$$J(x)\geq c\|x\|_\infty^{-d-\alpha}\quad(x\ne0),\qquad
\sum_{x\in Q_r}\tau_\beta(x)\leq B r^\gamma\quad(r\geq1),\qquad
Q_r=[-r,r]^d\cap\mathbb Z^d.$$</div>
<p>Set $\kappa=d-\gamma$, $\theta=\kappa/[2(\kappa+\alpha)]\in(0,1/2)$ and $b=c\beta$. There is $C=C(d,\alpha,\gamma)&lt;\infty$ such that</p>
<div class="math-display">$$\mathbb P_\beta(|K_0|\geq n)\leq C\bigl(b^{-1/2}+\sqrt B\bigr)n^{-\theta}\qquad(n\geq1).$$</div>
<p>The constant is independent of $J,\beta,c$ and $B$.</p>
<p><em>Proof.</em> Write $f(n)=\mathbb P_\beta(|K_0|\geq n)$ and define its least power-law amplitude by</p>
<div class="math-display">$$M=\sup_{n\geq1}n^\theta f(n).$$</div>
<p>It is finite: Markov's inequality gives $n^\theta f(n)\leq\chi_\beta n^{\theta-1}\leq\chi_\beta$. Also $M\geq1$. This is the only use of finite susceptibility until the endpoint application below.</p>
<p>Let $S_{x,n}$ be the event that $0$ and $x$ lie in distinct clusters, both of size at least $n$, and put $S_{0,n}=\varnothing$. Every cluster is finite almost surely, by translation invariance and $\chi_\beta&lt;\infty$. In $S_{x,n}$ the intervening edge is necessarily closed. The translation action on the complete lattice graph has vertex mass transport, by reindexing $x$ as $-x$, and each unoriented displacement orbit has two edges incident to the origin. The deterministic bond probabilities belong to $(0,1)$. Thus the already proved <a href="/tag/BYEO/">two-cluster bound</a> applies and gives</p>
<div class="math-display">$$\sum_{x\ne0}(e^{\beta J(x)}-1)\mathbb P_\beta(S_{x,n})^2
\leq\frac{40000M^2}{(1-2\theta)^2}n^{-1-2\theta}.$$</div>
<p>No independence between the two cluster events is asserted. Harris gives a lower bound for their joint occurrence; when both occur, either their clusters are distinct or $0\leftrightarrow x$. Consequently</p>
<div class="math-display">$$f(n)^2\leq\mathbb P_\beta(S_{x,n})+\tau_\beta(x).$$</div>
<p>For integer $r\geq1$, weighted Cauchy–Schwarz and $e^{\beta J(x)}-1\geq b r^{-d-\alpha}$ on $Q_r\setminus\{0\}$ give</p>
<div class="math-display">$$\begin{aligned}
\frac1{|Q_r|}\sum_{x\in Q_r}\mathbb P_\beta(S_{x,n})
&\leq\frac{200M n^{-1/2-\theta}}{(1-2\theta)|Q_r|}
\left(\sum_{x\in Q_r\setminus\{0\}}\frac1{e^{\beta J(x)}-1}\right)^{1/2}\\
&\leq C_1 M b^{-1/2}n^{-1/2-\theta}r^{\alpha/2}.
\end{aligned}$$</div>
<p>The term at zero is omitted before taking reciprocals. Averaging the Harris bound and using $|Q_r|\geq r^d$ therefore yields</p>
<div class="math-display">$$f(n)^2\leq C_2\left[M b^{-1/2}n^{-1/2-\theta}r^{\alpha/2}+B r^{-\kappa}\right].$$</div>
<p>Choose $r=\lceil n^{1/(\kappa+\alpha)}\rceil$. It is between $n^{1/(\kappa+\alpha)}$ and twice that quantity. Both terms then have power $n^{-2\theta}$, since</p>
<div class="math-display">$$-\frac12-\theta+\frac{\alpha}{2(\kappa+\alpha)}=-2\theta,
\qquad -\frac{\kappa}{\kappa+\alpha}=-2\theta.$$</div>
<p>Taking the supremum over $n$ and enlarging the constant gives a finite quadratic inequality</p>
<div class="math-display">$$M^2\leq C_3(Mb^{-1/2}+B).$$</div>
<p>Its positive root is at most $C_3b^{-1/2}+\sqrt{C_3B}$. This proves the result. In particular the initial estimate $M\leq\chi_\beta$ has disappeared from the final bound; no uniform susceptibility estimate was assumed.</p>



## Tightness of the cluster-size vector {#section-norm-tightness}

<p>Consider independent bond percolation on a countable graph, with arbitrary edge probabilities, and a finite nonempty observation set $\Lambda$. Let $\mathscr C$ be the partition of $\Lambda$ into its nonempty intersections with full clusters. Paths may leave $\Lambda$. Put</p>
<div class="math-display">$$S_p=\sum_{C\in\mathscr C}|C|^p,\qquad Z_p=S_p^{1/p}\quad(1\leq p&lt;\infty),\qquad Z_\infty=\max_{C\in\mathscr C}|C|.$$</div>
<p>The estimates in this section need no cluster-tail hypothesis, transitivity or finite susceptibility.</p>

<a id="tag-3109" data-assertion="theorem" data-title="Uniform tightness of every norm of the cluster-size vector"></a>
<p>For every $1\leq p\leq\infty$, real $\lambda\geq1$ and integer $k\geq1$,</p>
<div class="math-display">$$\mathbb P(Z_p\geq3^k\lambda)\leq\mathbb P(Z_p\geq\lambda)^{3^{k-1}+1}.$$</div>
<p>In particular the constants $a=162e$ and $c=(18e)^{-1}$ work simultaneously for every graph, window, edge profile and norm index in</p>
<div class="math-display">$$\mathbb P(Z_p\geq u\mathbb E Z_p)\leq a e^{-cu}\quad(u\geq1),\qquad
\mathbb P(Z_p&lt;\varepsilon\mathbb E Z_p)\leq a\varepsilon\quad(0&lt;\varepsilon\leq1).$$</div>
<p>For every real $r\geq1$ one also has</p>
<div class="math-display">$$\mathbb E Z_p^r\leq D_r(\mathbb E Z_p)^r,\qquad D_r=e(18e)^r\Gamma(r+1).$$</div>
<p><em>Proof.</em> First suppose the graph is finite and $p&lt;\infty$. In each open component meeting $\Lambda$ in $b\geq3^k$ vertices, choose a spanning tree and apply <a href="/tag/DMI0/">the marked-tree splitting theorem</a>. Keep $m=3^{k-1}+1$ pieces, each with at least $b/3^k$ marked endpoints. For each $i\leq m$, form a spanning subgraph $H_i$ by taking the $i$th piece from every such component and retaining all vertices as isolated vertices when no selected edge meets them. The $H_i$ have disjoint edge sets.</p>
<p>The selected pieces from different original components cannot meet. A component with $b&lt;3^k$ marked vertices contributes $b$ isolated marks to each $H_i$, and $b\geq3^{-pk}b^p$. The large components contribute at least $3^{-pk}b^p$ through their selected pieces. Consequently</p>
<div class="math-display">$$\sum_{C\in\mathscr C(H_i,\Lambda)}|C|^p\geq3^{-pk}S_p\qquad(1\leq i\leq m).$$</div>
<p>On $Z_p\geq3^k\lambda$, each edge set of $H_i$ therefore witnesses $Z_p\geq\lambda$. Opening more edges can only merge parts and increase $S_p$. The witnesses may share vertices; their edges are disjoint, which is exactly what BK requires. Repeated BK proves the first inequality. Isolated marked vertices require no open-edge certificate, so the argument also covers an empty selected edge set. For $p=\infty$ the inequality is already proved in <a href="/tag/12NL/">12NL</a>.</p>
<p>For a countable graph, exhaust its edges by finite sets, retaining all marked vertices. In any configuration, finitely many finite paths suffice to connect every pair of marks that is connected in the full graph. The induced partition of $\Lambda$ thus eventually agrees with the full partition. This proves convergence even for thresholds equal to an atom of $Z_p$, and passes the amplification inequality to the countable graph.</p>
<p>Write $Z=Z_p$ and set</p>
<div class="math-display">$$b=\inf\{x\geq0:\mathbb P(Z\geq x)\leq e^{-1}\}.$$</div>
<p>There are only finitely many possible partitions of $\Lambda$, so $Z$ has finite support. Also $Z\geq1$. Hence $b\geq1$, $\mathbb P(Z\geq b)\geq e^{-1}$, and $\mathbb P(Z\geq2b)\leq e^{-1}$. The last inequality need not be strict. For $x\geq6$, choose $k=\lfloor\log_3(x/2)\rfloor\geq1$. Then $2\cdot3^k\leq x$ and $3^{k-1}&gt;x/18$, so amplification at $\lambda=2b$ gives $\mathbb P(Z\geq xb)\leq e^{-x/18}$. Enlarging the prefactor handles $0\leq x&lt;6$:</p>
<div class="math-display">$$\mathbb P(Z\geq xb)\leq e e^{-x/18}\qquad(x\geq0),\qquad b/e\leq\mathbb E Z\leq18e b.$$</div>
<p>For the lower tail, it suffices to consider $0&lt;\delta&lt;1/3$ and $\delta b&gt;1$; otherwise $\mathbb P(Z&lt;\delta b)\leq9\delta$ is immediate. Take $k=\lfloor\log_3(1/\delta)\rfloor$. Then $b/3^k\geq\delta b&gt;1$ and $m=3^{k-1}+1&gt;(9\delta)^{-1}$. Amplification yields</p>
<div class="math-display">$$e^{-1}\leq\mathbb P(Z\geq b)
\leq\mathbb P(Z\geq b/3^k)^m
\leq\mathbb P(Z\geq\delta b)^m.$$</div>
<p>It follows that $\mathbb P(Z&lt;\delta b)\leq1-e^{-1/m}\leq9\delta$. Combining this with the two bounds on $\mathbb E Z/b$ gives the stated mean-normalized tails, with constants independent of $p$. Finally tail integration gives</p>
<div class="math-display">$$\mathbb E Z^r\leq e(18b)^r\Gamma(r+1)
\leq e(18e)^r\Gamma(r+1)(\mathbb E Z)^r.$$</div>
<p>This proves the norm extension of the maximum estimate without repeating its tree-splitting proof. The positive-integer restriction on $k$ and the weak quantile inequality are recorded among the <a href="/errata/hutchcroft-hierarchical-volumes-2022/">source boundary corrections</a>.</p>

## Powers and mixed moments {#section-norm-moments}

<a id="tag-25TW" data-assertion="theorem" data-title="Moment comparisons with the dependence on the exponents retained"></a>
<p>In the same independent percolation model, for real $p,k\geq1$,</p>
<div class="math-display">$$\mathbb E S_p^k\leq D_{pk}(\mathbb E S_p)^k.$$</div>
<p>For every finite list $p_1,\ldots,p_r\geq1$ there is a constant $C_{p_1,\ldots,p_r}$, independent of the graph, window and edge probabilities, such that</p>
<div class="math-display">$$\prod_{i=1}^r\mathbb E S_{p_i}\leq
\mathbb E\prod_{i=1}^r S_{p_i}
\leq C_{p_1,\ldots,p_r}\prod_{i=1}^r\mathbb E S_{p_i}.$$</div>
<p>Let $M=\min\{m\geq1:\mathbb P(Z_\infty\geq m)\leq e^{-1}\}$ be the integer maximum quantile. For real $p,q\geq1$, there is likewise $C_{p,q}$ such that</p>
<div class="math-display">$$\mathbb E S_{p+q}\leq\mathbb E[S_pZ_\infty^q]\leq C_{p,q}M^q\mathbb E S_p.$$</div>
<p>For fixed indices, the variables $S_p/\mathbb E S_p$ and all finite products of these normalized variables are uniformly integrable over this entire class of models.</p>
<p><em>Proof.</em> Apply 3109 with exponent $pk$ and use Jensen's inequality $(\mathbb E Z_p)^p\leq\mathbb E Z_p^p=\mathbb E S_p$. For the mixed upper bound, Hölder gives</p>
<div class="math-display">$$\mathbb E\prod_i S_{p_i}\leq\prod_i(\mathbb E S_{p_i}^r)^{1/r}
\leq\left(\prod_i D_{rp_i}^{1/r}\right)\prod_i\mathbb E S_{p_i}.$$</div>
<p>Each $S_{p_i}$ is nonnegative and increasing under opening bonds. Iterated Harris gives the lower bound. The pointwise inequality $S_{p+q}\leq S_pZ_\infty^q$ follows by bounding each component's $q$th power by the maximum's. The maximum tail from 12NL implies</p>
<div class="math-display">$$\mathbb E Z_\infty^{2q}\leq e\,9^{2q}\Gamma(2q+1)M^{2q}.$$</div>
<p>Indeed its exponential bound applies above $M$, and a prefactor $e$ covers the smaller thresholds. Cauchy–Schwarz and the first assertion now prove the last comparison, with $C_{p,q}=[D_{2p}e\,9^{2q}\Gamma(2q+1)]^{1/2}$. The same Hölder argument applied to squared products bounds their second moments after normalization. This gives uniform integrability, with constants depending on the prescribed indices.</p>
<p>That dependence cannot be removed as in the displayed bound (3.12) of the source. On two vertices with one edge open with probability $2^{-p}$, the variable $S_p$ equals $2$ when closed and $2^p$ when open. Thus</p>
<div class="math-display">$$\mathbb E S_p=3-2^{1-p}\leq3,\qquad
\mathbb E S_p^2=4(1-2^{-p})+2^p\geq2^p,\qquad
\frac{\mathbb E S_p^2}{(\mathbb E S_p)^2}\geq\frac{2^p}{9}.$$</div>
<p>This also occurs inside a fixed critical hierarchical model: take $L=2$, $d=1$, $0&lt;\alpha&lt;1$, and the level-one block at time $t=-\log(1-2^{-p})$. For sufficiently large integer $p$, $0&lt;t&lt;t_1$, with the model and its critical intensity held fixed. Hence no universal $C$ gives the source's $C^k k!$ bound for every $p,k$ and intermediate time. The replacement above is sufficient for its fixed-index comparisons; the diagnosis and repair remain <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional</a>.</p>
