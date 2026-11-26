---
{
  "id": "sle-hull-boundary",
  "title": "The dimension of SLE hull boundaries",
  "subtitle": "Localized derivative moments, boundary coverings, and zero area",
  "kind": "method",
  "category": "General theory",
  "summary": "Derivative moments in bounded windows control a dyadic grid above the real axis. Hölder continuity and Koebe distortion turn this sum into a covering bound for the hull boundary, giving zero area at every fixed time and completing the space-filling argument above kappa eight.",
  "context": [
    "We use ordinary chordal SLE, with Loewner coefficient two and driving function square root of kappa times standard Brownian motion.",
    "The derivative martingale and fixed-time Hölder theorem have already been proved. Koebe distortion and the quarter theorem are classical conformal inputs.",
    "The boundary theorem is for each fixed time. It includes kappa eight without using a trace theorem at that parameter. Space filling at eight still needs the separate trace-construction theorem.",
    "These are upper bounds. The global expected Whitney-sum threshold, its divergence at and below the threshold, and a Hausdorff lower bound are not proved here."
  ],
  "related": ["sle-derivative-estimates", "sle-trace-covering", "sle-space-filling", "sle-trace-generation"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE hull boundary dimension", "SLE zero-area boundary", "SLE boundary covering"],
  "prototypeUses": []
}
---

## Moments above a positive image height {#section-height-moments}

<p>Write $F=\widehat f_1$, where $\widehat f_t(z)=g_t^{-1}(z+U_t)$ is the centered inverse Loewner map. For $\kappa&gt;0$ and $0\leq b\leq1+4/\kappa$, put</p>
<div class="math-display">$$a=2b+\frac{\kappa b(1-b)}2,
\qquad \lambda=4b+\frac{\kappa b(1-2b)}2.$$</div>

<a id="tag-EG6U" data-assertion="proposition" data-title="A positive lower bound on image height gives a fixed-time inverse-derivative moment bound"></a>
<p>For $x\in\mathbb R$, $0&lt;y\leq1$ and $0&lt;h\leq1$,</p>
<div class="math-display">$$\mathbb E\!\left[(y|F'(x+iy)|)^a
\mathbf1_{\{\operatorname{Im}F(x+iy)\geq h\}}\right]
\leq C_{h,a,\lambda}\left(1+\frac{x^2}{y^2}\right)^b y^\lambda,
\qquad C_{h,a,\lambda}=\max\{h^{a-\lambda},5^{(a-\lambda)/2}\}.$$</div>
<p><em>Proof.</em> By <a href="/tag/HHBC/">HHBC</a>, the derivative and image height have the law of those of the reverse flow at time one. Write these as $D_1$ and $Y_1$, and let $R$ be the ratio diffusion of <a href="/tag/O0VQ/">O0VQ</a>. The height clock at physical time one is the stopping time $S=\log(Y_1/y)$. Since $Y_1^2\leq y^2+4$, this clock is bounded by $\frac12\log(1+4/y^2)$. Optional stopping in the true martingale of <a href="/tag/AXSH/">AXSH</a> therefore gives</p>
<div class="math-display">$$\mathbb E\!\left[(yD_1)^a(1+R_S^2)^bY_1^{\lambda-a}\right]
=\left(1+\frac{x^2}{y^2}\right)^b y^\lambda.$$</div>
<p>Here $a,b\geq0$. On $\{Y_1\geq h\}$ we have $h\leq Y_1\leq\sqrt5$, so $(1+R_S^2)^bY_1^{\lambda-a}\geq C_{h,a,\lambda}^{-1}$. Restricting the expectation to this event proves the assertion.</p>

## Summable grids in bounded windows {#section-grid-sums}

<p>For $n\geq-2$, set $y_n=2^{-n}$ and $z_{j,n}=j y_n+i y_n$. Define</p>
<div class="math-display">$$J_{p,h,L}(F)=\sum_{n\geq-2}\ \sum_{|j y_n|\leq L}
\mathbf1_{\{\operatorname{Im}F(z_{j,n})\geq h\}}
\bigl(y_n|F'(z_{j,n})|\bigr)^p.$$</div>
<p>The window $L$ bounds the real coordinate before applying $F$; the cutoff $h$ bounds the height after applying it. Put</p>
<div class="math-display">$$\delta(\kappa)=
\begin{cases}1+\kappa/8,&0&lt;\kappa\leq4,\\
1+2/\kappa,&\kappa\geq4.
\end{cases}$$</div>

<a id="tag-AVHR" data-assertion="proposition" data-title="Localized inverse-map grid sums have finite expectation above the hull-boundary exponent"></a>
<p>If $\kappa\ne4$, then for every $p&gt;\delta(\kappa)$, $h&gt;0$ and finite $L&gt;0$,</p>
<div class="math-display">$$\mathbb E[J_{p,h,L}(F)]&lt;\infty.$$</div>
<p><em>Proof.</em> It suffices to take $h\leq1$. Choose $b$ strictly between $\min\{1/2,2/\kappa\}$ and $\max\{1/2,2/\kappa\}$, sufficiently close to the smaller endpoint that $\delta(\kappa)&lt;a&lt;p$. Indeed, $a$ equals $\delta(\kappa)$ at that endpoint and increases immediately to its right. This choice lies in the range of EG6U and gives</p>
<div class="math-display">$$\lambda-2b-1=(2b-1)(1-\kappa b/2)&gt;0.$$</div>
<p>At a grid height $y\leq1$, there are at most $C_L/y$ points in the window, and $1+x^2/y^2\leq(1+L^2)y^{-2}$. EG6U consequently bounds the expected sum of the $a$th powers at that height by $C_{h,L}y^{\lambda-2b-1}$. Summing the geometric series gives a finite expectation.</p>
<p>Schwarz–Pick gives $y|F'(x+iy)|\leq\operatorname{Im}F(x+iy)$, while the reverse-flow height estimate gives $\operatorname{Im}F(x+iy)\leq\sqrt{y^2+4}$. Thus the derivative scale is at most $\sqrt5$ at the fine grid heights, and its $p$th power is at most $5^{(p-a)/2}$ times its $a$th power. The two remaining heights, two and four, have finitely many points in the window and derivative scale at most $\sqrt{20}$. Their contribution is finite as well.</p>
<p>In particular, on one probability-one event these sums are finite for every integer $L\geq1$, every positive rational $h$ and every rational $p&gt;\delta(\kappa)$. Only these countably many choices will be needed.</p>

## From the grid to the boundary {#section-radial-covering}

<p>We use a deterministic consequence of Hölder continuity. Let $g_1:D\to\mathbb H$ be the time-one map of a continuous chordal Loewner driver, $K=\overline{\mathbb H\setminus D}$, and $F(z)=g_1^{-1}(z+U_1)$. The hull is bounded and has height at most two. Reverse flow gives $\operatorname{Im}F(x+iy)\geq y$. The hydrodynamic normalization implies $F(w)=w+U_1+O(1/w)$ near infinity.</p>

<a id="tag-2SVA" data-assertion="proposition" data-title="A finite localized derivative grid sum controls the covering number of a Hölder Loewner hull boundary"></a>
<p>Suppose $F$ extends locally Hölder continuously to $\overline{\mathbb H}$. Fix $h&gt;0$ and put $E=\partial K\cap\{\operatorname{Im}z\geq2h\}$. There is a finite integer $L$ such that, for every $p&gt;0$ with $J_{p,h,L+2}(F)&lt;\infty$,</p>
<div class="math-display">$$N(\varepsilon,E)\leq C_{F,h,p}\,J_{p,h,L+2}(F)
\left(\frac{\log(1/\varepsilon)}{\varepsilon}\right)^p$$</div>
<p>for all sufficiently small $\varepsilon&gt;0$. Here $N$ is the least number of open disks of radius $\varepsilon$ covering the set.</p>
<p><em>Proof.</em> The assertion is immediate when $E$ is empty. Otherwise every $z_0\in E$ has a real preimage $x$ under the continuous extension of $F$. To see this, approach $z_0$ from $D$. The preimages remain bounded by the normalization at infinity; a convergent subsequence cannot have its limit in $\mathbb H$, since $z_0\in\partial D$. Boundary continuity gives the required real preimage. The same normalization bounds all such preimages by one finite integer $L$.</p>
<p>On $[-L,L]+i[0,3]$, choose a Hölder exponent $\theta&gt;0$ and a constant $C\geq1$ such that</p>
<div class="math-display">$$|F(x+it)-F(x)|\leq C t^\theta.$$</div>
<p>For $F(x)=z_0$, consider the radial image $\beta(t)=F(x+it)$. It exits $B(z_0,\varepsilon)$ before time three when $\varepsilon&lt;1$, because $\operatorname{Im}\beta(3)\geq3$ whereas $\operatorname{Im}z_0\leq2$. Let $t_e$ be its first exit time and put $t_0=(\varepsilon/(4C))^{1/\theta}$. The Hölder bound keeps $\beta([0,t_0])$ within distance $\varepsilon/4$ of $z_0$. Hence $t_0&lt;t_e$ and</p>
<div class="math-display">$$\frac{3\varepsilon}{4}
\leq\int_{t_0}^{t_e}|F'(x+it)|\,dt
=\int_{t_0}^{t_e}t|F'(x+it)|\,d\log t.$$</div>
<p>Since $\log(3/t_0)\leq C_F\log(1/\varepsilon)$ for small $\varepsilon$, some $t\in[t_0,t_e]$ satisfies</p>
<div class="math-display">$$\frac{c_F\varepsilon}{\log(1/\varepsilon)}
\leq t|F'(x+it)|\leq2\varepsilon.$$</div>
<p>The upper bound holds throughout this interval: the conformal radius of $D$ at $F(x+it)$ is $2t|F'(x+it)|$, so Koebe's quarter theorem gives $t|F'(x+it)|\leq2\operatorname{dist}(F(x+it),\partial D)\leq2\varepsilon$.</p>
<p>Choose a grid height $y_n\in[t/2,t]$ and $j$ with $|j y_n-x|\leq y_n/2$. The points $w=z_{j,n}$ and $x+it$ are at uniformly bounded hyperbolic distance in $\mathbb H$. Koebe distortion, integrated along their joining segment, gives absolute constants for which</p>
<div class="math-display">$$\frac{c_F\varepsilon}{\log(1/\varepsilon)}
\leq y_n|F'(w)|\leq C_1\varepsilon,
\qquad |F(w)-z_0|\leq C_2\varepsilon.$$</div>
<p>Here $n\geq-2$ and $|\operatorname{Re}w|\leq L+2$. For sufficiently small $\varepsilon$, depending also on $h$, the second bound gives $\operatorname{Im}F(w)\geq h$.</p>
<p>Take a maximal $\varepsilon$-separated subset of the compact set $E$ and assign one such grid point to each of its points. The $\varepsilon$-disks centered at the separated points cover $E$. Each grid point receives at most an absolute number of assignments, by planar packing in $B(F(w),C_2\varepsilon)$. Every assigned point contributes at least $(c_F\varepsilon/\log(1/\varepsilon))^p$ to $J_{p,h,L+2}(F)$. Summing proves the bound.</p>

## The boundary exponent and zero area {#section-boundary-dimension}

<a id="tag-K8Y5" data-assertion="theorem" data-title="At each fixed time SLE hull boundaries have covering exponent at most delta and zero planar area for every positive kappa"></a>
<p>Fix $\kappa&gt;0$ and a deterministic $T&gt;0$. Almost surely, for every $h&gt;0$ and $\alpha&gt;\delta(\kappa)$,</p>
<div class="math-display">$$\lim_{\varepsilon\downarrow0}\varepsilon^\alpha
N\bigl(\varepsilon,\partial K_T\cap\{\operatorname{Im}z\geq h\}\bigr)=0.
$$</div>
<p>Consequently, almost surely</p>
<div class="math-display">$$\dim_{\mathrm H}\partial K_T\leq\delta(\kappa),
\qquad \operatorname{area}(\partial K_T)=0.$$</div>
<p>The theorem includes $\kappa=8$ without assuming the existence of a generating trace there. It does not assert simultaneous covering bounds at all times.</p>
<p><em>Proof.</em> Scaling reduces the proof to $T=1$. Suppose first that $\kappa\ne4$. Intersect the event in AVHR with the local Hölder event of <a href="/tag/OLNV/">OLNV</a>. For any $h&gt;0$ and $\alpha&gt;\delta(\kappa)$, choose positive rational $h_0&lt;h/2$ and rational $p\in(\delta(\kappa),\alpha)$. Apply 2SVA with $h_0$ and the finite integer window selected there. Its bound gives</p>
<div class="math-display">$$\varepsilon^\alpha N\bigl(\varepsilon,\partial K_1\cap\{\operatorname{Im}z\geq h\}\bigr)
\leq C J_{p,h_0,L+2}(F)\,
\varepsilon^{\alpha-p}\log^p(1/\varepsilon)\longrightarrow0.$$</div>
<p>All required sums were made finite on one countable intersection, so this proves the asserted quantifiers over $h$ and $\alpha$.</p>
<p>At $\kappa=4$, use the simple trace supplied by <a href="/tag/MN2A/">MN2A</a> and <a href="/tag/CKFH/">CKFH</a>. For a bounded open rectangle $A$ with closure in $\mathbb H$, the upper bound of <a href="/tag/1424/">1424</a> implies, for every $r&gt;3/2$,</p>
<div class="math-display">$$\mathbb E[N(2^{-n},\Gamma\cap A)]\leq C_{A,r}2^{nr}$$</div>
<p>for all large $n$. Choose $3/2&lt;r&lt;q&lt;\alpha$. Markov's inequality gives</p>
<div class="math-display">$$\sum_n\mathbb P\bigl(N(2^{-n},\Gamma\cap A)&gt;2^{nq}\bigr)
\leq C_{A,r}\sum_n2^{-n(q-r)}&lt;\infty.$$</div>
<p>Borel–Cantelli yields the required limit along dyadic scales, and monotonicity of $N$ gives it at every scale. Take a countable exhaustion by rectangles with rational endpoints and rational exponents greater than $3/2$. The time-one hull is the compact simple trace $\gamma[0,1]$ and has height at most two. Its part above any positive height lies in one of these rectangles and in $\Gamma$. This proves the covering assertion at four, with the same simultaneous quantifiers over heights and exponents.</p>
<p>For each positive height, these covers imply Hausdorff dimension at most $\delta(\kappa)$. The boundary is contained in the union of the real line and the strips with heights $1/m$, $m\geq1$. Countable stability of Hausdorff dimension gives the full boundary bound. Finally $\delta(\kappa)\leq3/2&lt;2$, so its planar area vanishes.</p>
<p>This supplies the upper-covering conclusion of Rohde–Schramm Theorem 8.6 and the boundary upper bound of Corollary 8.7. The bounded-window proof avoids a global expected Whitney sum: it does not establish Theorem 8.3 or Corollary 8.5, whose lower estimates require further work. The zero-area conclusion also supplies the deterministic-time input used from Corollary 5.3.</p>

## Space filling above eight {#section-space-filling-update}

<a id="tag-BQ8X" data-assertion="corollary" data-title="Ordinary SLE above kappa eight is transient and covers every compact subset of the closed half-plane in finite time"></a>
<p>For $\kappa&gt;8$, ordinary chordal SLE has a continuous generating trace $\gamma$ for which, almost surely,</p>
<div class="math-display">$$\operatorname{dist}(0,D_t)&gt;0\quad(t&gt;0),
\qquad \lim_{t\to\infty}|\gamma(t)|=\infty,
\qquad \gamma[0,\infty)=\overline{\mathbb H}.$$</div>
<p>On the same event, every compact $C\subset\overline{\mathbb H}$ lies in $\gamma[0,T]$ for some finite $T$.</p>
<p><em>Proof.</em> MN2A supplies the continuous generating trace and the unrestricted inverse-map tip limit simultaneously at all times. K8Y5 supplies zero boundary area at each deterministic time. These are precisely the two inputs of <a href="/tag/ZS6G/">ZS6G</a> and <a href="/tag/R2A0/">R2A0</a>, which prove immediate origin engulfment, transience and finite-time compact coverage. Their area argument integrates at deterministic times and does not require an all-times version of K8Y5.</p>
<p>At $\kappa=8$, K8Y5 still supplies the boundary-area input. The remaining input for the same argument is the separate Lawler–Schramm–Werner trace-construction theorem; it has not been proved in these articles.</p>
