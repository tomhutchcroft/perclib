---
{
  "id": "triangle-susceptibility",
  "title": "Susceptibility from a small open triangle",
  "subtitle": "Probability derivatives, finite maxima and critical limits",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Finite-volume bounds give a globally Lipschitz reciprocal. A small neighbouring open triangle gives the matching upper bound; triangle finiteness alone is kept distinct.",
  "context": [
    "Independent nearest-neighbour bond percolation on $\\mathbb Z^d$, unless a walk or a spread-out model is specified.",
    "All integrals on the torus use normalized Lebesgue measure.",
    "Statements about an infrared bound retain that bound as a hypothesis."
  ],
  "related": [
    "integrated-susceptibility",
    "sharpness-bond-parameter",
    "infrared-diagrams"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [],
  "prototypeUses": []
}
---

## The reciprocal across the transition {#section-reciprocal}

<p>Write $\chi(p)=\sum_x\mathbb P_p(0\leftrightarrow x)$ and use $1/\infty=0$. The parameter here is the bond probability itself.</p>
<a id="tag-8ZGG" data-assertion="theorem" data-title="The reciprocal susceptibility is globally Lipschitz in the bond probability"></a>
<p>For nearest-neighbour percolation on $\mathbb Z^d$, $d\ge1$,</p>
<div class="math-display">$$0\le\chi(s)^{-1}-\chi(t)^{-1}\le2d(t-s)\qquad(0\le s<t\le1).$$</div>
<p>In particular,</p>
<div class="math-display">$$\chi(p)\ge\frac1{2d(p_c-p)}\qquad(0\le p<p_c).$$</div>
<p><em>Proof.</em> In a finite induced subgraph $F$, put $f_w(p)=\sum_{x\in F}\mathbb P_p(w\leftrightarrow_F x)$ and $m_F=\max_{w\in F}f_w$. Each $f_w$ is a polynomial. The finite Russo formula and BK give</p>
<div class="math-display">$$0\le f_w'(p)\le\sum_{\substack{u,v\in F\\u\sim v}}\tau_F(w,u)\sum_{x\in F}\tau_F(v,x)\le2d\,m_F(p)^2.$$</div>
<p>Here an oriented pivotal event is read with its bond deleted: it has disjoint path witnesses from $w$ to $u$ and from $v$ to $x$. BK applies in that deleted product law, and its connection probabilities are at most the full finite-volume ones. Thus this is a bound for state-independent pivotality; no closed-bond factor is lost in changing parameters.</p>
<p>A finite maximum of these polynomials is Lipschitz on $[0,1]$. At each interior $p$, let $I(p)$ be its active set of maximizers. Inactive indices remain below the maximum in a sufficiently small neighbourhood. The first-order expansions of the active functions consequently give</p>
<div class="math-display">$$(m_F)'_+(p)=\max_{w\in I(p)}f_w'(p),\qquad
(m_F)'_-(p)=\min_{w\in I(p)}f_w'(p).$$</div>
<p>In particular $0\le m_F'\le2d m_F^2$ almost everywhere. Since $m_F\ge1$, its reciprocal is absolutely continuous and has derivative in $[-2d,0]$ almost everywhere. Integration proves the asserted reciprocal inequality for $m_F$.</p>
<p>Exhaust the lattice by boxes containing zero. Transitivity of the infinite law and inclusion of the finite cluster give $f_0(p)\le m_F(p)\le\chi(p)$, while finite path witnesses and monotone convergence give $f_0(p)\uparrow\chi(p)$. Hence $m_F(p)\to\chi(p)$, including when the limit is infinite. Pass to the limit at both endpoints of the reciprocal inequality.</p>
<p>When $p_c<1$, the reciprocal is zero for every $p>p_c$, so continuity makes it zero at $p_c$ too. If $p_c=1$, the full lattice at $p=1$ has infinite susceptibility directly. The lower bound follows by taking $t=p_c$. Subcritical finiteness is supplied separately by <a href="/tag/JQLC/">sharpness</a>.</p>
<p>The one-sided formula also states precisely what is needed in Exercise 4.2. A finite maximum need not have an ordinary derivative at a tie: $\max\{p,1-p\}$ has a corner at $1/2$. The preceding source argument already invokes almost-everywhere differentiability; the integral proof above needs no stronger interpretation.</p>

## The small-triangle estimate {#section-small-triangle}

<p>For $p\le p_c$, set</p>
<div class="math-display">$$\Delta_p(x)=\sum_{u,v}\tau_p(0,u)\tau_p(u,v)\tau_p(v,x).$$</div>
<a id="tag-0Y4K" data-assertion="theorem" data-title="A small neighbouring open triangle gives matching susceptibility bounds"></a>
<p>For $d\ge2$, suppose $\delta=\max_{e\sim0}\Delta_{p_c}(e)<1$. Then, for $0\le p<p_c$,</p>
<div class="math-display">$$\frac1{2d(p_c-p)}\le\chi(p)
\le\frac1{2d(1-\delta)\log\!\bigl((1-p)/(1-p_c)\bigr)}
\le\frac1{2d(1-\delta)(p_c-p)}.$$</div>
<p>Thus $\chi(p)\asymp(p_c-p)^{-1}$.</p>
<p><em>Proof.</em> Set $b=-\log(1-p)$, so that unit edge weights give the intensity law $p=1-e^{-b}$. The <a href="/tag/4960/">weighted open-triangle inequality</a>, with row sum $2d$, yields</p>
<div class="math-display">$$\frac{d\chi}{db}\ge2d(1-\delta)\chi^2$$</div>
<p>almost everywhere below $b_c=-\log(1-p_c)$. All its regularity and finiteness hypotheses hold by sharpness and the <a href="/tag/MXGM/">finite-volume regularity argument</a>. Monotonicity bounds every subcritical neighbouring triangle by $\delta$. The change of variables gives $\chi'(p)\ge2d(1-\delta)\chi(p)^2/(1-p)$ almost everywhere. Integrate the reciprocal from $p$ to $t<p_c$, discard the nonnegative reciprocal at $t$, and let $t\uparrow p_c$. This proves the first upper bound; $\int_p^{p_c}(1-u)^{-1}\,du\ge p_c-p$ proves the second. The lower bound is 8ZGG. Endpoint $p=0$ follows by continuity.</p>
<p>The hypothesis concerns neighbouring endpoints, not just large separations. Finite $\Delta_{p_c}(0)$ and <a href="/tag/96A2/">decay of open triangles</a> do not themselves establish $\delta<1$. The regularization argument needed for the full finite-triangle susceptibility theorem is not supplied here; the manuscript also leaves it to its references.</p>

## Critical nonpercolation and one-sided exponents {#section-critical}

<a id="tag-5W46" data-assertion="corollary" data-title="Triangle nonpercolation and the one-sided mean-field exponent bounds"></a>
<p>For nearest-neighbour percolation with $d\ge2$, finite $\Delta_{p_c}(0)$ implies $\theta(p_c)=0$. Independently of that triangle assumption, any positive exponents defined by</p>
<div class="math-display">$$\chi(p_c-u)=u^{-g+o(1)},\qquad
\theta(p_c+u)=u^{b+o(1)},\qquad
M(p_c,h)=h^{1/\delta+o(1)}$$</div>
<p>satisfy $g\ge1$, $b\le1$ and $\delta\ge2$, respectively. Each conclusion only assumes existence of its own displayed exponent.</p>
<p><em>Proof.</em> Taking $u=0$ in one of the sums defining the triangle shows $\sum_x\tau_{p_c}(0,x)^2<\infty$, hence $\tau_{p_c}(0,x)\to0$. By <a href="/tag/Y6SG/">uniqueness</a>, two vertices in infinite clusters are connected almost surely. Harris therefore gives $\tau_{p_c}(0,x)\ge\theta(p_c)^2$, proving critical nonpercolation.</p>
<p>For the exponent bounds, 8ZGG gives $\chi(p_c-u)\ge c/u$, and <a href="/tag/JQLC/">JQLC</a> gives $\theta(p_c+u)\ge cu$. Critical susceptibility is infinite. If $\theta(p_c)=0$, the finite-cluster mean is therefore infinite; if $\theta(p_c)>0$, magnetization already has a positive limit. In either case <a href="/tag/ZDVK/">ZDVK</a>, with the percolation inequality supplied by <a href="/tag/G192/">G192</a>, gives $M(p_c,h)\ge c\sqrt h$. Divide the logarithms of these inequalities by the negative logarithm of their small parameter to obtain the stated restrictions.</p>
<p>The critical susceptibility lower bound and these one-sided exponent estimates use no triangle assumption. Under the finite triangle condition the matching bounds hold as well: this is the <a href="/tag/2ZI0/">mean-field theorem under the triangle condition</a>, proved on $\mathbb Z^d$ in the article on <a href="/articles/triangle-condition/">the triangle condition</a>, and, with the magnetization, the <a href="#tag-I23O">lattice mean-field theorem</a> below, which is deduced from its transitive-graph form.</p>

<p>The <a href="/tag/YT0O/">explicit bootstrap consequence</a> supplies the small neighbouring triangle for every $d\ge10^{11}$, with $\delta\le189/d$, and gives a numerical susceptibility comparison there. The general finite-triangle regularization remains separate.</p>


## Finite triangles through the boundary inequality {#section-finite-triangle}

<p>The small-neighbouring-triangle argument above is only one route to the susceptibility bound. The corrected boundary inequality gives the finite-triangle conclusion directly. In particular, the earlier caveat about regularization concerns the classical endpoint-separation proof, not an additional hypothesis needed for the result below.</p>

<a id="tag-ADWR" data-assertion="theorem" data-title="A finite critical triangle gives mean-field susceptibility and critical tails without a smallness assumption"></a>
<p>Consider independent bonds on a countable vertex set with probabilities $1-e^{-\beta J(u,v)}$. Suppose the symmetric nonnegative weights are invariant under a transitive action with the <a href="/tag/N0HM/">mass-transport property</a> and are normalized by $\sum_{v\ne o}J(o,v)=1$. Write</p>
<div class="math-display">$$b=\sup\{\beta\ge0:\chi(\beta)<\infty\},\qquad
D=T_b^3(o,o).$$</div>
<p>Assume $b<\infty$ and $D<\infty$. Then $b\ge1$, $D\ge1$, and for $0<\beta<b$,</p>
<div class="math-display">$$\frac1{b-\beta}\le\chi(\beta)
\le 2D^2+\frac{3\beta bD^2}{b-\beta}.$$</div>
<p>Moreover, with $N=|K_o|$ and $M(b,h)=\mathbb E_b[1-e^{-hN}]$,</p>
<div class="math-display">$$\mathbb P_b(N\ge n)\asymp n^{-1/2},\qquad
M(b,h)\asymp\sqrt h\quad(h\downarrow0),\qquad
\theta(b)=0,\qquad \theta(b+\varepsilon)=O(\varepsilon)\quad(\varepsilon\downarrow0).$$</div>
<p>The comparison constants may depend on the model. No smallness assumption on $D-1$ or on any off-diagonal triangle is imposed.</p>
<p><em>Proof.</em> The path expansion gives $\chi(\beta)\le(1-\beta)^{-1}$ for $\beta<1$, so $b\ge1$. By <a href="/tag/5LNL/">right-openness of finite susceptibility</a>, susceptibility is finite below $b$ and infinite at $b$. The <a href="/tag/MXGM/">reciprocal lower bound</a> gives the first inequality. Monotonicity gives $1\le\Delta(\beta)=T_\beta^3(o,o)\le D$ below $b$.</p>
<p>The <a href="/tag/4KBG/">corrected boundary argument</a> proves, almost everywhere,</p>
<div class="math-display">$$\chi'(\beta)\ge
\frac{(\chi(\beta)-\Delta(\beta))_+^2}{3\beta^2\Delta(\beta)^2}
\ge\frac{(\chi(\beta)-D)_+^2}{3\beta^2D^2}.$$</div>
<p>For the second comparison, divide the numerator by its diagram value: $(\chi/t-1)_+^2$ is nonincreasing in $t>0$. Susceptibility is locally Lipschitz by MXGM, so <a href="/tag/6PGV/">the integrated positive-part inequality</a> applies with the constant diagram bound $D$. Since</p>
<div class="math-display">$$\int_\beta^b\frac{ds}{3s^2D^2}=\frac{b-\beta}{3\beta bD^2},$$</div>
<p>its conclusion is precisely the asserted upper bound. Thus $\chi(\beta)\asymp(b-\beta)^{-1}$. The endpoint hypotheses of <a href="/tag/UPMK/">the susceptibility–tail equivalence</a> have all been checked, so it gives the two-sided critical tail and $\theta(b)=0$. The <a href="/tag/3C2F/">tail–field equivalence</a> gives the magnetization estimate. Finally, <a href="/tag/QS3L/">entropy comparison across the endpoint</a>, with logarithmic exponent zero, gives the density upper bound.</p>
<p>This proof uses the squared positive-part numerator, whose derivation is supplied in the wiki. It does not use the stronger source numerator $\chi(\chi-\Delta)$, which fails at small intensity. Identifying the susceptibility endpoint $b$ with an infinite-cluster threshold, or supplying a density lower bound above it, requires the corresponding sharpness theorem; the lattice specialization follows.</p>

## The finite-triangle mean-field theorem on the lattice {#section-finite-triangle-lattice}

<p><em>Main article: <a href="/articles/triangle-condition/">The triangle condition</a>.</em> The susceptibility, critical-tail and order-parameter estimates below are the <a href="/tag/2ZI0/">mean-field theorem under the triangle condition</a>, which that article proves directly on $\mathbb Z^d$: Russo's formula, the boundary of the root cluster and a Fourier comparison of diagrams give $\chi'\ge\chi^2/(24d\nabla_{p_c}^2)$ near $p_c$, and the entropy comparison of cluster tails converts the resulting susceptibility bound into the tail and density bounds. This section obtains the same estimates, together with the magnetization, by specialising the transitive-graph theorem of the previous section.</p>
<a id="tag-I23O" data-assertion="corollary" data-title="The finite triangle condition gives the classical lattice mean-field laws"></a>
<p>For nearest-neighbour bond percolation on $\mathbb Z^d$, $d\ge2$, suppose $D=\Delta_{p_c}(0)<\infty$. Then</p>
<div class="math-display">$$\chi(p)\asymp(p_c-p)^{-1},\qquad
\theta(p)\asymp p-p_c\quad(p\downarrow p_c),\qquad
\mathbb P_{p_c}(|C_0|\ge n)\asymp n^{-1/2},\qquad
M(p_c,h)\asymp\sqrt h\quad(h\downarrow0).$$</div>
<p>The susceptibility comparison is as $p\uparrow p_c$. These are two-sided order estimates, with constants depending on the fixed dimension and its critical triangle; no limiting amplitude is asserted. In particular, the susceptibility, density and critical-field exponents exist in the logarithmic sense and equal $1$, $1$ and $2$, respectively.</p>
<p><em>Proof.</em> Put $q=2d$, assign weight $1/q$ to each nearest-neighbour edge, and set</p>
<div class="math-display">$$\beta=-q\log(1-p),\qquad b=-q\log(1-p_c).$$</div>
<p>The normalized intensity model is exactly the bond model at probability $p$. The <a href="/tag/NUJY/">nontrivial lattice transition</a> gives $0<p_c<1$, and <a href="/tag/JQLC/">sharpness</a> gives finite susceptibility for $p<p_c$. By <a href="/tag/8ZGG/">the reciprocal endpoint argument</a>, susceptibility is infinite at $p_c$. Thus $b$ is its finite intensity threshold, and translations have the mass-transport property. Apply ADWR. The change of variables has derivative $q/(1-p)$, bounded above and below by positive constants on a neighbourhood of $p_c$. It therefore transfers the susceptibility and density upper bounds to the probability parameter. The tail and field statements concern the same critical law and require no conversion. Finally, JQLC supplies $\theta(p)\ge(p-p_c)/p$ for $p>p_c$, giving the density lower bound.</p>
<p>For an explicit subcritical comparison, ADWR and 8ZGG give, for $0<p<p_c$,</p>
<div class="math-display">$$\frac1{q(p_c-p)}\le\chi(p)
\le 2D^2+\frac{3\beta bD^2}{b-\beta}.$$</div>
<p>The two proofs of the lattice estimates share the lower bound from the reciprocal Lipschitz bound and differ in the rest. The <a href="/articles/triangle-condition/">triangle-condition article</a> integrates $\chi'\ge\chi^2/(24d\nabla_{p_c}^2)$ in the bond parameter, which gives the upper constant $24d\nabla_{p_c}^2$, and applies the <a href="/tag/JL1S/">entropy comparison of cluster tails</a> directly for the tail and the density. The proof above integrates the positive-part inequality of the boundary argument in the intensity, which gives the constant above, and obtains the tail from the susceptibility–tail equivalence and the density from entropy comparison across the endpoint. Neither proves that the critical triangle is finite in any dimension. The explicit high-dimensional results above retain their stronger uniform constants. <a href="/tag/7T8L/">The moment and cutoff extension</a> below uses the same finite-triangle hypothesis.</p>

<p>The finite-triangle susceptibility bound also controls <a href="/tag/Z78U/">intrinsic volume in susceptibility-biased cylinder limits</a>: short-path thinning gives a linear independent-law ball mean, and the multipoint diagram then gives exponential upper tails on the radius-squared scale. This requires neither a small triangle nor uniqueness of the IIC limit.</p>

<p>Combining the critical tail with the uniform intrinsic-arm bound and <a href="/tag/KGPE/">a stopped exploration under susceptibility bias</a> gives <a href="/tag/RG3Z/">quadratic intrinsic volume</a> and <a href="/tag/POD2/">linear intrinsic resistance</a> in every susceptibility-biased cylinder limit. This completes the matching lower-volume estimate left separate above without adding a small-triangle or spatial two-point assumption to that construction.</p>
