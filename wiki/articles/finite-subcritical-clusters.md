---
{
  "id": "finite-subcritical-clusters",
  "title": "Finite graphs below the critical window",
  "subtitle": "The integrated triangle error and subcritical component sizes",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Keeping the susceptibility-dependent triangle error gives sharp subcritical susceptibility and a positive-denominator bound for the reference parameter. Root tails then bound the largest component between its susceptibility-square scale and a logarithmic upper scale.",
  "context": [
    "Independent bond percolation on finite simple graphs; transitivity is assumed for the triangle estimates and the component lower bound.",
    "The finite reference parameter satisfies $H=\\chi(p_c)$, with $1<H<N$.",
    "The displacement below the reference parameter is $\\varepsilon=m(p_c-p)$."
  ],
  "related": [
    "finite-graph-criticality",
    "finite-triangle-window",
    "finite-window-susceptibility",
    "finite-supercritical-clusters",
    "cluster-partitions"
  ],
  "sourceIds": [
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "sharpened finite triangle bound",
    "subcritical largest component",
    "positive critical parameter denominator",
    "finite susceptibility asymptotic"
  ],
  "prototypeUses": []
}
---

## Integrating the triangle error {#section-susceptibility}

<p>Let $G$ be a finite connected simple vertex-transitive graph of degree $m$ and order $N\ge2$. Write $T_p(x,y)=\mathbb P_p(x\leftrightarrow y)$ and $\chi(p)=\mathbb E_p|C_o|$. Fix $p_c\in(0,1)$, and set $H=\chi(p_c)$ and $h=H^{-1}$. Suppose that, for constants $K_1,K_2\ge0$,</p>
<div class="math-display">$$T_p^3(x,y)\le\mathbf1_{\{x=y\}}+\frac{K_1}{m}+\frac{K_2\chi(p)^3}{N}\qquad(0\le p\le p_c,\ x,y\in V).$$</div>
<p>Put</p>
<div class="math-display">$$\kappa=\frac{K_1}{m},\qquad \nu=\frac{K_2H^3}{N},\qquad a=\kappa+\nu<1,\qquad c=1-a.$$</div>
<p>The constant triangle bound gives $\chi(p)\le[h+c\varepsilon]^{-1}$, where $\varepsilon=m(p_c-p)$. Substituting this back into the triangle error makes that error decrease as one moves below $p_c$.</p>

<a id="tag-IWRH" data-assertion="theorem" data-title="Integrating the susceptibility-dependent finite triangle error"></a>
<p>For every $0\le p\le p_c$,</p>
<div class="math-display">$$\frac1{\chi(p)}\ge h+(1-\kappa)\varepsilon-\frac{K_2}{2cN}\left[h^{-2}-(h+c\varepsilon)^{-2}\right].$$</div>
<p>In particular, with $\bar a(\varepsilon)=\kappa+\nu h/(h+c\varepsilon)$,</p>
<div class="math-display">$$\frac1{h+\varepsilon}\le\chi(p)\le\frac1{h+[1-\bar a(\varepsilon)]\varepsilon},\qquad 0\le\bar a(\varepsilon)\le a<1.$$</div>
<p><em>Proof.</em> Let $y(u)=1/\chi(p_c-u/m)$ for $0\le u\le mp_c$. The differential argument in <a href="/tag/F5Y5/">F5Y5</a>, using the triangle bound at the current parameter, gives</p>
<div class="math-display">$$1-\kappa-\frac{K_2}{N(h+cu)^3}\le y'(u)\le1.$$</div>
<p>Indeed $\chi(p_c-u/m)\le(h+cu)^{-1}$ by the constant triangle bound, and the lower differential coefficient is nonnegative since $\kappa+K_2\chi^3/N\le a<1$. Integrating from zero to $\varepsilon$ proves the first assertion and $y(\varepsilon)\le h+\varepsilon$. The integral error satisfies the identity and bound</p>
<div class="math-display">$$\frac{K_2}{2cN}\left[h^{-2}-(h+c\varepsilon)^{-2}\right]=\frac{\nu\varepsilon h(2h+c\varepsilon)}{2(h+c\varepsilon)^2}\le\frac{\nu\varepsilon h}{h+c\varepsilon}.$$</div>
<p>Thus $y(\varepsilon)\ge h+[1-\bar a(\varepsilon)]\varepsilon>0$, and taking reciprocals gives the susceptibility bounds. These formulas also hold at $\varepsilon=0$.</p>

## A positive denominator for the reference parameter {#section-threshold}

<a id="tag-AJQL" data-assertion="theorem" data-title="A sharpened finite reference-parameter bound with a positive denominator"></a>
<p>Under the same hypotheses, define</p>
<div class="math-display">$$D_*=1-\kappa-\frac{\nu h}{c+ah}.$$</div>
<p>Then $D_*\ge c>0$ and</p>
<div class="math-display">$$1-h\le mp_c\le\frac{1-h}{D_*}.$$</div>
<p>The weaker denominator $D_0=1-\kappa-\nu h/c$ also gives $mp_c\le(1-h)/D_0$ whenever $D_0>0$.</p>
<p><em>Proof.</em> Write $r=mp_c$. At $p=0$, where $\chi=1$, the susceptibility bounds give $r\ge1-h$ and</p>
<div class="math-display">$$[1-\bar a(r)]r\le1-h.$$</div>
<p>Since $h+cr\ge h+c(1-h)=c+ah$, we have $1-\bar a(r)\ge D_*$. Moreover $0<h<1$ and $c+ah=h+c(1-h)\ge h$, so $D_*\ge1-\kappa-\nu=c$. Division by $D_*$ is therefore legitimate. Finally $c+ah\ge c$ gives $D_*\ge D_0$, proving the last assertion when its denominator is positive.</p>
<p>The positivity qualification on $D_0$ is absent from (1.30) of the checked preprint. Keeping $c+ah$ gives a bound throughout its stated range $a<1$. This is a <a href="/errata/borgs-chayes-finite-window/#sharp-threshold-denominator">provisional statement correction</a>; the subcritical susceptibility estimate itself is unchanged.</p>

<a id="tag-UQEG" data-assertion="proposition" data-title="The weakened threshold denominator can be negative under the stated triangle hypothesis"></a>
<p>On the single-edge complete graph $K_2$, take $p_c=1/10$, $K_1=0$ and $K_2=1$. The strong triangle bound holds for all $0\le p\le p_c$, and $1<H<N$, but</p>
<div class="math-display">$$a=\frac{1331}{2000}<1,\qquad D_0=-\frac{541}{669}<0.$$</div>
<p>Consequently the unqualified upper bound $mp_c\le(1-h)/D_0$ is false.</p>
<p><em>Proof.</em> Here $m=1$, $N=2$ and $\chi(p)=1+p$. The <a href="/tag/R2Y7/">complete-graph triangle formula</a> gives $T_p^3(x,y)\le\mathbf1_{\{x=y\}}+\chi(p)^3/2$, so the triangle hypothesis holds on the whole interval. Now $H=11/10$, $h=10/11$, $\nu=1331/2000$ and $c=669/2000$. Hence $\nu h/c=1210/669$ and $(1-h)/D_0=-669/5951$, whereas $mp_c=1/10>0$. The source's susceptibility normalization is satisfied by $\lambda=H/2^{1/3}$.</p>

## The sharp susceptibility scale {#section-asymptotic}

<a id="tag-UF7P" data-assertion="corollary" data-title="Asymptotically sharp susceptibility below a strong-triangle finite window"></a>
<p>Consider a sequence of the graphs above with $N\to\infty$, $m\to\infty$, $H=\lambda N^{1/3}$, and fixed $\lambda>0$ and $K_1,K_2\ge0$. Suppose $K_2\lambda^3<1$ and the strong triangle bound holds. Then</p>
<div class="math-display">$$mp_c=1+O(m^{-1}+N^{-1/3}).$$</div>
<p>If $p=p_c-\varepsilon/m\in[0,p_c]$ and $\varepsilon/h\to\infty$, then</p>
<div class="math-display">$$\varepsilon\chi(p)\longrightarrow1.$$</div>
<p>The constants may depend on $K_1,K_2,\lambda$.</p>
<p><em>Proof.</em> Now $\nu=K_2\lambda^3<1$ is fixed, $\kappa\to0$, and $c=1-\nu-\kappa$ is bounded below by a positive constant for all sufficiently large graphs. The reference-parameter bounds give, with $r=mp_c$,</p>
<div class="math-display">$$1-r\le h,\qquad r-1\le\frac{\kappa+\nu h/(c+ah)-h}{D_*}\le\frac\kappa c+\frac{\nu h}{c^2}.$$</div>
<p>This proves the first assertion. For the second, $\bar a(\varepsilon)=\kappa+\nu/(1+c\varepsilon/h)\to0$. Multiplying the susceptibility bounds by $\varepsilon$ gives</p>
<div class="math-display">$$\frac1{h/\varepsilon+1}\le\varepsilon\chi(p)\le\frac1{h/\varepsilon+1-\bar a(\varepsilon)},$$</div>
<p>and both endpoints tend to one. The uniform positive gap below $a=1$ is what makes this limit valid.</p>

## Expected size of the largest component {#section-upper}

<p>The next bound needs no triangle hypothesis. Let the graph be any finite nonempty simple graph with arbitrary independent bond probabilities, and put $M=\max_x\mathbb E|C_x|$ and $L_1=\max_x|C_x|$.</p>
<a id="tag-WM3D" data-assertion="theorem" data-title="A logarithmic expectation upper bound from finite susceptibility"></a>
<p>If $R=N/M^3\ge e^6$, then</p>
<div class="math-display">$$\mathbb EL_1\le2M^2\log R.$$</div>
<p><em>Proof.</em> Put $A=\log R\ge6$ and take the real cutoff $k=2(A-1)M^2$. With $Z_k=\sum_x\mathbf1_{\{|C_x|\ge k\}}$, we have $L_1\le k+Z_k$. Since $k\ge M^2$, the <a href="/tag/4A0G/">optimized root tail</a> gives</p>
<div class="math-display">$$\mathbb EL_1\le k+N\sqrt{e/k}\,e^{-k/(2M^2)}=M^2\left[2(A-1)+\frac{e^{3/2}}{\sqrt{2(A-1)}}\right]\le2AM^2.$$</div>
<p>For the last inequality use $A-1\ge5$ and $e^3<27<40$. A noninteger cutoff causes no problem: either the largest component has fewer than $k$ vertices, or all its vertices are counted by $Z_k$.</p>

## A component of susceptibility-square size {#section-lower}

<p>For the lower bound return to a finite connected simple transitive graph. Here only the constant triangle hypothesis is needed:</p>
<div class="math-display">$$0<p_c<1,\qquad H=\chi(p_c)\ge100,\qquad T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+a_0,\qquad a_0\le1/100.$$</div>
<a id="tag-DAN9" data-assertion="theorem" data-title="A susceptibility-square component lower bound with all cutoff cases included"></a>
<p>For $0\le p\le p_c$, write $\chi=\chi(p)$. For every $\omega\ge1$,</p>
<div class="math-display">$$\mathbb P_p\!\left(L_1\ge\frac{\chi^2}{80000\omega}\right)\ge\frac1{1+25\chi^3/(\omega N)}.$$</div>
<p>In particular,</p>
<div class="math-display">$$\mathbb E_pL_1\ge\frac{\chi^2}{80000(1+25\chi^3/N)}.$$</div>
<p><em>Proof.</em> Write $s=\chi^2/(80000\omega)$. If $s\le1$, the probability is one. Otherwise let $k=\lceil s\rceil\le2s\le\chi^2/40000$. The <a href="/tag/EPK3/">second-moment component bound</a> applies and yields</p>
<div class="math-display">$$\mathbb P_p(L_1\ge s)=\mathbb P_p(L_1\ge k)\ge\frac1{1+10^6k\chi/N}\ge\frac1{1+25\chi^3/(\omega N)}.$$</div>
<p>The expectation bound follows by taking $\omega=1$ and multiplying this probability by the cutoff.</p>

## Leaving the finite window on the lower side {#section-below-window}

<a id="tag-L5E1" data-assertion="corollary" data-title="Susceptibility and largest-component scales below a finite triangle window"></a>
<p>Consider a sequence satisfying the constant triangle hypotheses of the preceding result, with $N\to\infty$ and $H=\lambda N^{1/3}$ for a fixed $\lambda>0$. Let</p>
<div class="math-display">$$p=p_c-\varepsilon/m\in[0,p_c],\qquad \varepsilon N^{1/3}\longrightarrow\infty.$$</div>
<p>Then $\chi(p)\asymp\varepsilon^{-1}$ and $R=N/\chi(p)^3\to\infty$. For every sufficiently large member of the sequence,</p>
<div class="math-display">$$\frac{\chi(p)^2}{80000(1+25/R)}\le\mathbb E_pL_1\le2\chi(p)^2\log R,$$</div>
<div class="math-display">$$\mathbb P_p\!\left(\frac{\chi(p)^2}{80000}\le L_1\le2\chi(p)^2\log R\right)\ge1-\frac{25}{R+25}-\frac{\sqrt e}{(2\log R)^{3/2}}.$$</div>
<p>In particular, $L_1/N^{2/3}\to0$ in probability and in mean. If the strong triangle assumptions and fixed-constant regime of the sharp susceptibility corollary also hold, then $\chi(p)\sim\varepsilon^{-1}$.</p>
<p><em>Proof.</em> Since $h=\lambda^{-1}N^{-1/3}=o(\varepsilon)$, <a href="/tag/F5Y5/">F5Y5</a> gives</p>
<div class="math-display">$$\frac1{h+\varepsilon}\le\chi(p)\le\frac1{h+(1-a_0)\varepsilon},$$</div>
<p>with $1-a_0\ge99/100$. Hence $\chi\asymp\varepsilon^{-1}$ and $\chi/N^{1/3}\to0$, so $R\to\infty$. The expectation bounds above apply once $R\ge e^6$. Combine the lower probability estimate at $\omega=1$ with the <a href="/tag/3RIO/">largest-component exponential upper tail</a> to obtain the displayed probability. Finally</p>
<div class="math-display">$$\frac{\mathbb E_pL_1}{N^{2/3}}\le\frac{2\log R}{R^{2/3}}\longrightarrow0.$$</div>
<p>Markov's inequality gives convergence in probability, and the sharp susceptibility corollary gives the final assertion. These bounds leave a logarithmic gap between the lower and upper component scales. They do not assert the matching logarithmic lower bound known for the random graph.</p>


## Tree components in the complete graph {#section-tree-component-counts}

<p>We now specialize to the Erdős–Rényi graph $G(N,p)$: independent bond percolation on $K_N$. A tree component has no occupied edges beyond those of its spanning tree. Let $X_j$ count tree components with exactly $j$ vertices, and put $q=1-p$.</p>

<a id="tag-P1F1" data-assertion="proposition" data-title="Exact tree-component counts have variance at most their mean below a complete-graph threshold"></a>
<p>For $N\ge2$, $0<p<1$ and $1\le j\le N$,</p>
<div class="math-display">$$a_j:=\mathbb EX_j
=\binom Nj j^{j-2}p^{j-1}q^{d_j},\qquad
d_j=j(N-j)+\binom j2-j+1.$$</div>
<p>If $0<p\le1/(N+1)$ and $J\subseteq\{1,\ldots,N\}$, then for $X_J=\sum_{j\in J}X_j$,</p>
<div class="math-display">$$\operatorname{Var}X_J\le\mathbb EX_J.$$</div>
<p>In particular, when $J$ is nonempty, $\mathbb P(X_J=0)\le1/\mathbb EX_J$.</p>
<p><em>Proof.</em> Choose the $j$ vertices and one of their $j^{j-2}$ labelled trees, as counted by Prüfer codes. Its $j-1$ edges must be open, every edge from these vertices to the complement must be closed, and so must the remaining internal edges. Distinct trees give disjoint configurations on the chosen vertex set. This proves the expectation formula, including $j=1$.</p>
<p>Two distinct components have disjoint vertex sets. For $j+k\le N$, counting ordered pairs gives</p>
<div class="math-display">$$\mathbb E\bigl[X_jX_k-\mathbf1_{\{j=k\}}X_j\bigr]
=a_ja_k\frac{\binom{N-j}{k}}{\binom Nk}\,q^{-jk}.$$</div>
<p>The factor $q^{-jk}$ corrects the double counting of closed edges between the two sets. When $j+k>N$, the left-hand side is zero. In the remaining case,</p>
<div class="math-display">$$\frac{\binom{N-j}{k}}{\binom Nk}
=\prod_{i=0}^{k-1}\left(1-\frac{j}{N-i}\right)
\le e^{-jk/N}.$$</div>
<p>Since $-\log q\le p/(1-p)\le1/N$ under the stated restriction, the pair expectation is at most $a_ja_k$. Summing over $j,k\in J$ gives $\mathbb E[X_J(X_J-1)]\le(\mathbb EX_J)^2$, and hence the variance bound. Chebyshev proves the last assertion. This is a bound on component counts after summing over their locations; it does not assert independence of component events.</p>

## Many trees near the logarithmic scale {#section-logarithmic-tree-lower}

<p>Let $N\to\infty$, take $p=(1-\varepsilon)/N$, and assume</p>
<div class="math-display">$$\varepsilon\longrightarrow0,\qquad
R=N\varepsilon^3\longrightarrow\infty.
\qquad I=-\varepsilon-\log(1-\varepsilon)\sim\frac{\varepsilon^2}{2}.$$</div>
<p>Here $\varepsilon>0$ is defined by this complete-graph parametrization. For fixed $0<\delta<1$, set</p>
<div class="math-display">$$k=\left\lceil\frac{(1-\delta)\log R}{I}\right\rceil,\qquad
w=\lfloor I^{-1}\rfloor,\qquad J=\{k,k+1,\ldots,k+w\}.$$</div>

<a id="tag-XF00" data-assertion="theorem" data-title="Barely subcritical Erdős–Rényi graphs contain many tree components just below the logarithmic scale"></a>
<p>For all sufficiently large $N$, the set $J$ is contained in $\{1,\ldots,N\}$ and</p>
<div class="math-display">$$\mathbb EX_J\asymp_\delta
\frac{R^\delta}{(\log R)^{5/2}}\longrightarrow\infty,
\qquad \frac{X_J}{\mathbb EX_J}\longrightarrow1
\quad\text{in probability}.$$</div>
<p>In particular, for every fixed positive integer $r$, the probability of at least $r$ distinct tree components of size at least $k$ tends to one.</p>
<p><em>Proof.</em> Write $c=1-\varepsilon$. Stirling's formula and the exact expectation in P1F1 give, uniformly for $j\to\infty$ with $j\le N/2$ and $c\in[1/2,1)$,</p>
<div class="math-display">$$\log a_j
=\log\frac{N}{c\sqrt{2\pi}}-\frac52\log j-Ij
-\frac{\varepsilon j^2}{2N}
+O\!\left(\frac1j+\frac jN+\frac{j^3}{N^2}\right).$$</div>
<p>The cancellation in the quadratic term is needed near the window. Indeed, the falling-factorial contribution and the closed-edge contribution are respectively</p>
<div class="math-display">$$\sum_{i=0}^{j-1}\log(1-i/N)
=-\frac{j(j-1)}{2N}+O(j^3/N^2),$$</div>
<div class="math-display">$$d_j\log(1-c/N)
=-cj+\frac{cj^2}{2N}+O(j/N).$$</div>
<p>Their $j^2/N$ terms leave $-\varepsilon j^2/(2N)$; no assumption that $j^2/N\to0$ is made.</p>
<p>For $j\in J$ we have $j\asymp_\delta\varepsilon^{-2}\log R$, $w/k\to0$, and</p>
<div class="math-display">$$\frac jN=O_\delta\!\left(\frac{\varepsilon\log R}{R}\right),\qquad
\frac{\varepsilon j^2}{N}=O_\delta\!\left(\frac{(\log R)^2}{R}\right),\qquad
\frac{j^3}{N^2}=O_\delta\!\left(\frac{(\log R)^3}{R^2}\right).$$</div>
<p>All three vanish uniformly on the interval. Thus $k+w\le N/2$ eventually and</p>
<div class="math-display">$$a_j=(1+o(1))\frac{N}{c\sqrt{2\pi}}j^{-5/2}e^{-Ij}
\qquad(j\in J),$$</div>
<p>with a uniform error. On $J$, $j^{-5/2}\asymp_\delta k^{-5/2}$ and $e^{-Ij}\asymp R^{-(1-\delta)}$, while $w+1\asymp I^{-1}$. Consequently</p>
<div class="math-display">$$\mathbb EX_J\asymp_\delta
NI^{3/2}(\log R)^{-5/2}R^{-(1-\delta)}
\asymp_\delta\frac{R^\delta}{(\log R)^{5/2}}.$$</div>
<p>The summation over an interval of width $I^{-1}$ matters: the expected number at a single size need not diverge in the full regime considered here. Finally $N\varepsilon\to\infty$, so $p\le1/(N+1)$ eventually. P1F1 and Chebyshev give relative concentration, and hence arbitrarily many components in the interval with probability tending to one.</p>

## The largest subcritical components in Erdős–Rényi graphs {#section-er-logarithmic-law}

<p>Order all component sizes as $L_1\ge L_2\ge\cdots$, and order the tree-component sizes as $T_1\ge T_2\ge\cdots$, padding either list with zeros if necessary. Keep the preceding assumptions and put</p>
<div class="math-display">$$b_N=2\varepsilon^{-2}\log(N\varepsilon^3).$$</div>

<a id="tag-X0R0" data-assertion="theorem" data-title="Every fixed-rank barely subcritical Erdős–Rényi component has the sharp logarithmic leading size in probability and mean"></a>
<p>For every fixed positive integer $r$,</p>
<div class="math-display">$$\frac{L_r}{b_N}\longrightarrow1,\qquad
\frac{T_r}{b_N}\longrightarrow1
\quad\text{in probability},$$</div>
<div class="math-display">$$\mathbb E\left|\frac{L_r}{b_N}-1\right|\longrightarrow0,
\qquad
\mathbb E\left|\frac{T_r}{b_N}-1\right|\longrightarrow0.$$</div>
<p>In particular, $\mathbb EL_r\sim\mathbb ET_r\sim2\varepsilon^{-2}\log(N\varepsilon^3)$.</p>
<p><em>Proof.</em> XF00 gives $T_r\ge k$ with probability tending to one, and $k/b_N\to1-\delta$. For the upper bound, the path-counting estimate MIQ7 gives</p>
<div class="math-display">$$M=\mathbb E|C_o|
\le\frac1{1-(N-1)p}\le\varepsilon^{-1}.$$</div>
<p>With $t=(1+\delta)b_N$, the largest-component tail 3RIO therefore yields, for all sufficiently large $N$,</p>
<div class="math-display">$$\mathbb P(L_1\ge t)
\le\sqrt e\,Nt^{-3/2}e^{-\varepsilon^2t/2}
\le C_\delta\frac{R^{-\delta}}{(\log R)^{3/2}}
\longrightarrow0.$$</div>
<p>The required cutoff condition $t\ge M^2$ holds since $\log R\to\infty$. Since $T_r\le L_r\le L_1$, letting $\delta\downarrow0$ proves both probability limits.</p>
<p>To pass to means, use WM3D. For large $N$, $N/M^3\ge R\ge e^6$. The function $x\mapsto x^2\log(N/x^3)$ is increasing for $1\le x\le\varepsilon^{-1}$, since its derivative is $x[2\log(N/x^3)-3]>0$. Hence</p>
<div class="math-display">$$\mathbb EL_1\le2M^2\log(N/M^3)\le b_N.$$</div>
<p>Each nonnegative normalized variable $Y_N=L_r/b_N$ or $T_r/b_N$ thus has $\mathbb EY_N\le1$ eventually. Its convergence in probability to one implies $\liminf\mathbb EY_N\ge1$ and $\mathbb E(1-Y_N)_+\to0$. The identity</p>
<div class="math-display">$$\mathbb E|Y_N-1|=\mathbb EY_N-1+2\mathbb E(1-Y_N)_+$$</div>
<p>proves the claimed mean absolute convergence.</p>
<p>This supplies the matching logarithmic lower bound for the complete graph, including every fixed rank. The argument uses its exact tree enumeration; the logarithmic lower bound for a general graph under only the finite triangle hypotheses remains separate. No critical-window joint limit, second-order fluctuation law or assertion that the largest component itself is a tree is needed.</p>


## Components with more than one cycle {#section-bicyclic-bound}

<p>A connected graph with $v$ vertices and $e$ edges has cycle rank $e-v+1$. The next bound excludes components of cycle rank at least two throughout the barely subcritical regime.</p>

<a id="tag-EMO3" data-assertion="proposition" data-title="A subcritical complete graph contains a component with two independent cycles with probability at most three over N epsilon cubed"></a>
<p>For $N\ge2$, $0<\varepsilon<1$ and $p=(1-\varepsilon)/N$,</p>
<div class="math-display">$$\mathbb P\bigl(\text{some component of }G(N,p)\text{ has cycle rank at least }2\bigr)
\le \min\left\{1,\frac{3}{N\varepsilon^3}\right\}.$$</div>
<p><em>Proof.</em> Such a component contains a spanning tree together with two further edges. Delete leaves from this subgraph. The remaining connected graph has minimum degree two and satisfies $\sum_v(\deg v-2)=2$. Suppressing degree-two vertices therefore leaves either one vertex of degree four or two vertices of degree three. Accordingly, the original subgraph contains two cycles meeting at one vertex, two disjoint cycles joined by a path, or three internally disjoint paths with the same two endpoints.</p>
<p>Write $c=1-\varepsilon$. For each of the last two forms, specify three positive lengths; for the first, specify the two cycle lengths. A valid simple graph of any of these forms with $e$ edges has $e-1$ vertices. There are at most $N^{e-1}$ injective assignments of its vertices to $K_N$, and each assignment has all its edges open with probability $p^e$. This gives an expected number at most $N^{-1}c^e$. Only simple templates are counted here: cycle lengths are at least three, and the three-path form has at most one path of length one. Extending the resulting upper sums to all positive lengths gives</p>
<div class="math-display">$$\mathbb P(\text{such a component exists})
\le\frac1N\left[2\left(\sum_{l\ge1}c^l\right)^3+
\left(\sum_{l\ge1}c^l\right)^2\right]
\le\frac3{N\varepsilon^3}.$$</div>
<p>The argument only requires the displayed subgraphs to be present; no condition on the other edges is imposed.</p>

## Poisson counts at the largest tree sizes {#section-tree-extremes}

<p>Return to $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$, and retain $c=1-\varepsilon$ and $I=-\varepsilon-\log(1-\varepsilon)$. Define</p>
<div class="math-display">$$B_N=\log\frac{NI^{3/2}}{c\sqrt{2\pi}}
=\log R-\log(4\sqrt\pi)+o(1),
\qquad s_N(j)=Ij-B_N+\frac52\log B_N.$$</div>
<p>These expressions are used for sufficiently large $N$, when $B_N>0$. For $x\in\mathbb R$, let $Z_N^{\mathrm{tree}}(x)$ count tree components $C$ for which $s_N(|C|)>x$.</p>

<a id="tag-VGZ9" data-assertion="theorem" data-title="Barely subcritical complete-graph tree counts at the centered extreme scale converge to a Poisson law"></a>
<p>For every fixed $x\in\mathbb R$,</p>
<div class="math-display">$$Z_N^{\mathrm{tree}}(x)\ \xrightarrow{\ d\ }\ \operatorname{Poisson}(e^{-x}).$$</div>
<p><em>Proof.</em> Put</p>
<div class="math-display">$$k=\left\lfloor\frac{B_N-\tfrac52\log B_N+x}{I}\right\rfloor+1,
\qquad m=\left\lfloor\frac{2B_N}{I}\right\rfloor,
\qquad Z=\sum_{j=k}^m X_j.$$</div>
<p>For large $N$ these are positive cutoffs with $k\le m=o(N)$. The expansion proved in <a href="/tag/XF00/">XF00</a> is uniform over $k\le j\le m$, since $j=O(\varepsilon^{-2}\log R)$ and its three finite-population errors tend to zero there. Hence</p>
<div class="math-display">$$a_j=(1+o(1))\frac{N}{c\sqrt{2\pi}}j^{-5/2}e^{-Ij}
\qquad(k\le j\le m).$$</div>
<p>As $I\to0$ and $Ik\to\infty$, comparison with a decreasing integral gives</p>
<div class="math-display">$$\sum_{j\ge k}j^{-5/2}e^{-Ij}
\sim I^{3/2}(Ik)^{-5/2}e^{-Ik}.$$</div>
<p>Indeed the integral becomes $I^{3/2}\int_{Ik}^{\infty}t^{-5/2}e^{-t}\,dt$, whose ratio to the right-hand side tends to one; the endpoint error is smaller by a factor of order $I$. The part beyond $m$ contributes $O(e^{-B_N}B_N^{-5/2})$ after multiplication by $N/(c\sqrt{2\pi})$. Since $Ik=B_N-\tfrac52\log B_N+x+O(I)$ and $Ik/B_N\to1$, it follows that</p>
<div class="math-display">$$\mathbb EZ\sim e^{B_N}(Ik)^{-5/2}e^{-Ik}\longrightarrow e^{-x}.$$</div>
<p>We next count ordered tuples of distinct tree components. Fix $\ell\ge1$ and sizes $j_1,\ldots,j_\ell\in\{k,\ldots,m\}$, and write $K=\sum_a j_a$ and $S=\sum_{a<b}j_aj_b$. With $(n)_j=n(n-1)\cdots(n-j+1)$, the exact expectation of the number of such tuples is</p>
<div class="math-display">$$\left(\prod_{a=1}^{\ell}a_{j_a}\right)
\frac{(N)_K}{\prod_{a=1}^{\ell}(N)_{j_a}}\,q^{-S}.$$</div>
<p>The falling-factorial ratio enforces disjoint vertex sets, and $q^{-S}$ counts their shared closed edges once. For each fixed $\ell$, eventually $K\le N/2$, and expansion of these two factors yields</p>
<div class="math-display">$$\log\left(\frac{(N)_K}{\prod_a(N)_{j_a}}q^{-S}\right)
=-\frac{\varepsilon S}{N}+O(K^3/N^2)=o(1)$$</div>
<p>uniformly over the chosen sizes. Here the separate quadratic contributions are $-S/N$ and $cS/N$; the errors are bounded using $\varepsilon K^2/N=O_\ell((\log R)^2/R)$ and $K^3/N^2=O_\ell((\log R)^3/R^2)$. Summing over the sizes gives</p>
<div class="math-display">$$\mathbb E(Z)_\ell=(1+o(1))(\mathbb EZ)^\ell\longrightarrow e^{-\ell x}.$$</div>
<p>For completeness, these factorial moments determine the limiting probabilities without a tail assumption. For every fixed integer $r\ge0$ and $h\ge0$, the alternating binomial sums give</p>
<div class="math-display">$$\sum_{j=0}^{2h+1}\frac{(-1)^j\mathbb E(Z)_{r+j}}{r!j!}
\le\mathbb P(Z=r)\le
\sum_{j=0}^{2h}\frac{(-1)^j\mathbb E(Z)_{r+j}}{r!j!}.$$</div>
<p>These inequalities follow pointwise by multiplying the partial sums of $(1-1)^{Z-r}$ by $\binom Zr$, with both sides zero when $Z<r$. First let $N\to\infty$, then $h\to\infty$. The two bounds converge to $e^{-e^{-x}}e^{-rx}/r!$, the Poisson probabilities, whose sum is one. Finally $m/b_N\to2$, so <a href="/tag/X0R0/">X0R0</a> gives $\mathbb P(L_1>m)\to0$. With this probability removed, $Z$ is exactly $Z_N^{\mathrm{tree}}(x)$. This transfers the distributional limit; no assertion about uncapped factorial moments is needed.</p>

## The fluctuation law for every fixed rank {#section-er-extreme-law}

<p>Let $Z_N(x)$ count all components with $s_N(|C|)>x$, and keep the ordering and zero-padding conventions for $L_r$ and $T_r$ above.</p>

<a id="tag-CJ8R" data-assertion="theorem" data-title="Barely subcritical complete-graph component counts and fixed-rank extreme sizes have Poisson and Gumbel order-statistic limits"></a>
<p>Under $\varepsilon\to0$ and $N\varepsilon^3\to\infty$, for each fixed real $x$,</p>
<div class="math-display">$$\mathbb P\bigl(Z_N(x)=Z_N^{\mathrm{tree}}(x)\bigr)\longrightarrow1,
\qquad Z_N(x)\xrightarrow{\ d\ }\operatorname{Poisson}(e^{-x}).$$</div>
<p>Consequently, for each fixed positive integer $r$,</p>
<div class="math-display">$$\lim_{N\to\infty}\mathbb P\!\left(IL_r-B_N+\frac52\log B_N\le x\right)
=e^{-e^{-x}}\sum_{j=0}^{r-1}\frac{e^{-jx}}{j!},$$</div>
<p>and the same limit holds with $T_r$ in place of $L_r$. In particular the centered largest size has the standard Gumbel distribution in the limit.</p>
<p><em>Proof.</em> By EMO3, the probability of any component of cycle rank at least two is at most $3/R\to0$. It remains to exclude unicyclic components at the cutoffs $k,m$ used in VGZ9.</p>
<p>Let $u_j$ be the number of connected unicyclic simple graphs on a fixed set of $j\ge3$ labelled vertices. Choose the cycle, of length $l$, and attach a forest rooted at its vertices. This gives</p>
<div class="math-display">$$u_j=\frac12\sum_{l=3}^j(j)_l j^{j-l-1}
=\frac12j^{j-1}\sum_{l=3}^j\frac{(j)_l}{j^l}
\le Cj^{j-1/2}.$$</div>
<p>The rooted-forest count used here is $l j^{j-l-1}$. To see it when $j>l$, orient the forest toward its prescribed roots, successively remove the least nonroot leaf, and record its parent. The resulting sequence has length $j-l$, its last entry is a root, and its earlier entries are arbitrary labels. Conversely, at each step remove the least remaining nonroot label absent from the remaining sequence and attach it to the next entry. Such a label exists because the last entry is a root. This decodes every sequence into a forest. When $j=l$ there is just the empty forest, also counted by the formula. Choosing the cycle contributes $\binom jl(l-1)!/2$, proving the identity. For the bound, use $(j)_l/j^l\le\exp[-l(l-1)/(2j)]$ and sum the resulting Gaussian bound to obtain $C\sqrt j$.</p>
<p>If $U_j$ counts unicyclic components of size $j$, its expectation differs from $a_j$ by the graph-count ratio and by replacing one required closed internal edge with an open edge. Thus</p>
<div class="math-display">$$\mathbb EU_j
=a_j\frac{u_j}{j^{j-2}}\frac p q
\le C\frac{j^{3/2}}N a_j.$$</div>
<p>On $k\le j\le m$, the uniform estimate in VGZ9 therefore gives</p>
<div class="math-display">$$\sum_{j=k}^m\mathbb EU_j
\le C\sum_{j\ge k}j^{-1}e^{-Ij}
\le C\frac{e^{-Ik}}{k(1-e^{-I})}
=O_x\!\left(\frac{(\log R)^{3/2}}R\right)\longrightarrow0.$$</div>
<p>Here $Ik=B_N-\tfrac52\log B_N+x+O(I)$, $B_N\sim\log R$ and $e^{B_N}\asymp R$. Markov's inequality excludes unicyclic components in the interval. Components larger than $m$ have probability tending to zero by X0R0. Together with the cycle-rank bound this proves that the two counts agree with probability tending to one. VGZ9 then gives their common Poisson limit.</p>
<p>For large $N$, the cutoff $k$ is positive. The event $s_N(L_r)\le x$ is therefore exactly $\{Z_N(x)\le r-1\}$, including the zero-padding case. The Poisson probabilities give the displayed formula, and the same argument applies to tree components.</p>
<p>The exact rate $I$ is retained in the normalization. Since $I=\varepsilon^2/2+\varepsilon^3/3+O(\varepsilon^4)$, replacing it by $\varepsilon^2/2$ can change the centered variable by order $\varepsilon\log R$, which need not tend to zero under the stated assumptions. The result concerns each fixed rank and fixed threshold in the barely subcritical regime; no joint critical-window law or convergence of centered means is asserted.</p>


## A component tail with the exact exponential rate {#section-poisson-component-tail}

<p>The fluctuation theorem can be strengthened to convergence of centered moments. For this purpose the exponential rate in the upper bound must be retained exactly, even for components much larger than the typical maximum.</p>

<a id="tag-RN5K" data-assertion="proposition" data-title="Poisson exploration gives a finite complete-graph component tail with the exact subcritical rate"></a>
<p>Let $N\ge2$, $0<c<1$, $p=c/N$, and $I=c-1-\log c>0$. For each vertex $v$, the size $|C(v)|$ is stochastically dominated by the total progeny $T$ of a Galton–Watson process with Poisson mean $c$ offspring. For every integer $k\ge1$,</p>
<div class="math-display">$$\mathbb P(|C(v)|\ge k)
\le\frac{k^{-3/2}e^{-Ik}}{c\sqrt{2\pi}(1-e^{-I})},
\qquad
\mathbb P(L_1\ge k)
\le\min\left\{1,\frac{N k^{-5/2}e^{-Ik}}{c\sqrt{2\pi}(1-e^{-I})}\right\}.$$</div>
<p><em>Proof.</em> Explore the component by processing a queue of discovered vertices. Each processed vertex has at most $N-1$ undiscovered neighbours. As in <a href="/tag/0K60/">0K60</a>, its fresh bonds may be coupled to a new row of $N-1$ independent Bernoulli variables with parameter $p$. The component queue is dominated by the queue using every entry of each row.</p>
<p>A Bernoulli variable with parameter $p$ can be realized as $\mathbf1_{\{P>0\}}$, where $P$ is Poisson with mean $-\log(1-p)$, and is then at most $P$. Summing the row gives Poisson mean $(N-1)[-\log(1-c/N)]$, which is at most $c$, because</p>
<div class="math-display">$$(N-1)[-\log(1-c/N)]
\le\frac{(N-1)c}{N-c}\le c.$$</div>
<p>Add an independent Poisson variable for the missing mean in each row. The resulting independent Poisson-$c$ offspring dominate the component exploration. The use of $N-1$ entries, rather than $N$, is what permits the exact mean $c$.</p>
<p>Since $c<1$, the dominating process dies out almost surely. <a href="/tag/RL1L/">Dwass's formula</a> and the Poisson sum law give, for $j\ge1$,</p>
<div class="math-display">$$\mathbb P(T=j)=\frac{e^{-cj}(cj)^{j-1}}{j!}
\le\frac{1}{c\sqrt{2\pi}}j^{-3/2}e^{-Ij},$$</div>
<p>where the inequality is the lower Stirling bound $j!\ge\sqrt{2\pi j}(j/e)^j$. Sum the geometric upper bound from $j=k$ onward to obtain the root tail. If $L_1\ge k$, at least $k$ vertices lie in components of size at least $k$. Taking the expectation of their number gives $\mathbb P(L_1\ge k)\le(N/k)\mathbb P(|C(v)|\ge k)$, proving the second estimate. For $k>N$ the left sides vanish.</p>

## Uniform tails for the centered sizes {#section-centered-component-tails}

<p>Keep $p=(1-\varepsilon)/N$, $\varepsilon\to0$ and $R=N\varepsilon^3\to\infty$, and write</p>
<div class="math-display">$$I=-\varepsilon-\log(1-\varepsilon),\qquad
B=\log\frac{NI^{3/2}}{(1-\varepsilon)\sqrt{2\pi}},\qquad
D=B-\frac52\log B,
\qquad Y_{N,r}=IL_r-D,\quad Y^{\mathrm{tree}}_{N,r}=IT_r-D.$$</div>

<a id="tag-XHEC" data-assertion="theorem" data-title="Centered fixed-rank barely subcritical component sizes have uniform exponential tails on both sides"></a>
<p>For each fixed positive integer $r$, there is a constant $C_r<\infty$ such that, for all sufficiently large $N$ and every $t\ge0$,</p>
<div class="math-display">$$\mathbb P(Y_{N,r}>t)+\mathbb P(Y_{N,r}<-t)\le C_re^{-t},
\qquad
\mathbb P(Y^{\mathrm{tree}}_{N,r}>t)+\mathbb P(Y^{\mathrm{tree}}_{N,r}<-t)\le C_re^{-t}.$$</div>
<p>Consequently, for every $0<a<1$, the expectations $\mathbb E e^{a|Y_{N,r}|}$ and $\mathbb E e^{a|Y^{\mathrm{tree}}_{N,r}|}$ are bounded uniformly over sufficiently large $N$.</p>
<p><em>Proof.</em> For the upper tail take $k=\lfloor(D+t)/I\rfloor+1$. Eventually $D\ge B/2>0$ and $I/(1-e^{-I})\le2$. RN5K gives</p>
<div class="math-display">$$\mathbb P(IL_1-D>t)
\le\frac{I}{1-e^{-I}}e^B(Ik)^{-5/2}e^{-Ik}
\le2\left(\frac B{D+t}\right)^{5/2}e^{-t}
\le2^{7/2}e^{-t}.$$</div>
<p>This applies to every $t\ge0$; when $k>N$ the event is empty. Since $T_r\le L_r\le L_1$, it bounds both upper tails.</p>
<p>For the lower tail, first let $0\le t\le D-2$ and put</p>
<div class="math-display">$$u=D-t\ge2,\qquad
k=\lfloor u/I\rfloor+1,\qquad
w=\lfloor I^{-1}\rfloor,\qquad
Z=\sum_{j=k}^{k+w}X_j.$$</div>
<p>The expansion in <a href="/tag/XF00/">XF00</a> is uniform over all these bands. Their sizes satisfy $j\ge2/I\to\infty$ and $j\le(B+2)/I=O(\varepsilon^{-2}\log R)$; the errors $1/j$, $j/N$, $\varepsilon j^2/N$ and $j^3/N^2$ therefore vanish uniformly. For all sufficiently large $N$, it follows that</p>
<div class="math-display">$$\begin{aligned}
\mu:=\mathbb EZ
&\ge c_0 N I^{3/2}(u+2)^{-5/2}e^{-u}\\
&\ge c_1 e^t\left(\frac B{u+2}\right)^{5/2}
\ge c_1e^t,
\end{aligned}$$</div>
<p>with fixed positive constants. Indeed $w+1\ge I^{-1}$, each $Ij\le u+2$ eventually, and $u+2\le D+2\le B$. These bands stay below $N/2$. Also $p\le1/(N+1)$ eventually, so <a href="/tag/P1F1/">P1F1</a> gives $\operatorname{Var}Z\le\mu$. If $Z\ge r$, then $T_r\ge k$ and $IT_r-D>-t$. Hence, whenever $\mu\ge2r$,</p>
<div class="math-display">$$\mathbb P(Y^{\mathrm{tree}}_{N,r}<-t)
\le\mathbb P(Z<r)
\le\frac{\mu}{(\mu-r)^2}
\le\frac4\mu\le C e^{-t}.$$</div>
<p>Increasing the constant depending on $r$ covers the bounded range of $t$ where $c_1e^t<2r$. If $D-2<t\le D$, monotonicity bounds the probability by its value at $D-2$, and $e^{-(D-2)}\le e^2e^{-t}$. For $t>D$ the event is empty since $T_r\ge0$, including when the list is padded with zeros. This proves the lower tail for trees and, by $L_r\ge T_r$, for all components. Finally, for either centered variable $Y$,</p>
<div class="math-display">$$\mathbb E e^{a|Y|}
=1+a\int_0^\infty e^{at}\mathbb P(|Y|>t)\,dt
\le1+\frac{aC_r}{1-a}.$$</div>

## Centered moments and the expectation correction {#section-centered-component-moments}

<p>Let $S_r$ have the gamma density $s^{r-1}e^{-s}/\Gamma(r)$ on $(0,\infty)$, and put $G_r=-\log S_r$. Its distribution function is the fixed-rank limit in <a href="/tag/CJ8R/">CJ8R</a>.</p>

<a id="tag-OL4S" data-assertion="theorem" data-title="Centered barely subcritical fixed-rank sizes converge in all polynomial moments and have an explicit second-order expectation"></a>
<p>For each fixed positive integer $r$ and every real $q>0$,</p>
<div class="math-display">$$\mathbb E|Y_{N,r}|^q\longrightarrow\mathbb E|G_r|^q,
\qquad
\mathbb E|Y^{\mathrm{tree}}_{N,r}|^q\longrightarrow\mathbb E|G_r|^q.$$</div>
<p>All signed integer moments converge as well. For every $-1<\alpha<1$,</p>
<div class="math-display">$$\mathbb E e^{\alpha Y_{N,r}}\longrightarrow\frac{\Gamma(r-\alpha)}{\Gamma(r)},
\qquad
\mathbb E e^{\alpha Y^{\mathrm{tree}}_{N,r}}\longrightarrow\frac{\Gamma(r-\alpha)}{\Gamma(r)}.$$</div>
<p>In particular, writing $H_0=0$, $H_{r-1}=\sum_{j=1}^{r-1}1/j$ and letting $\gamma$ denote Euler's constant,</p>
<div class="math-display">$$\mathbb EL_r
=\frac{B-\tfrac52\log B+\gamma-H_{r-1}+o(1)}I,
\qquad
\mathbb ET_r
=\frac{B-\tfrac52\log B+\gamma-H_{r-1}+o(1)}I.$$</div>
<p><em>Proof.</em> CJ8R gives convergence in distribution to $G_r$. The uniform exponential bound in XHEC makes every fixed power of the absolute centered size uniformly integrable: for any $0<a<1$, $\sup_{z>M}z^q e^{-az}\to0$ as $M\to\infty$. Truncation therefore proves the absolute and signed moment limits.</p>
<p>For $|\alpha|<1$, choose $a$ with $|\alpha|<a<1$. On $|Y|>M$,</p>
<div class="math-display">$$e^{\alpha Y}\le e^{|\alpha||Y|}
\le e^{-(a-|\alpha|)M}e^{a|Y|}.$$</div>
<p>Thus these exponential functions are uniformly integrable too. Their limiting expectation is</p>
<div class="math-display">$$\mathbb E e^{\alpha G_r}
=\frac1{\Gamma(r)}\int_0^\infty s^{r-1-\alpha}e^{-s}\,ds
=\frac{\Gamma(r-\alpha)}{\Gamma(r)}.$$</div>
<p>The gamma integral is finite because $\alpha<1\le r$. For the mean, $\mathbb E\log S_1=-\gamma$ and integration by parts gives $\mathbb E\log S_{r+1}-\mathbb E\log S_r=1/r$. Hence $\mathbb EG_r=\gamma-H_{r-1}$. Taking expectations in $Y_{N,r}=IL_r-D$ and its tree analogue proves the two expansions.</p>
<p>The $o(1)$ is inside the numerator, so the error in the unscaled expectation is $o(I^{-1})$. All formulas retain the exact rate $I$. These conclusions concern centered sizes in the barely subcritical complete graph; they do not assert a joint critical-window limit.</p>


## Joint counts and ordered extreme sizes {#section-joint-er-extremes}

<p>Keep $p=(1-\varepsilon)/N$, $\varepsilon\to0$ and $N\varepsilon^3\to\infty$. Write $I=-\varepsilon-\log(1-\varepsilon)$, $B=\log[NI^{3/2}/((1-\varepsilon)\sqrt{2\pi})]$, $D=B-\tfrac52\log B$ and $s_N(k)=Ik-D$. The factorial-moment argument also determines several size intervals at once.</p>

<a id="tag-7W39" data-assertion="theorem" data-title="Joint subcritical extreme counts converge to independent Poisson variables and ordered sizes to logarithms of exponential arrival times"></a>
<p>Fix $x_1<\cdots<x_m$. Let $Z_{N,j}$ count components whose centered size lies in $(x_j,x_{j+1}]$ for $j<m$, and let $Z_{N,m}$ count those with centered size greater than $x_m$. Then</p>
<div class="math-display">$$(Z_{N,1},\ldots,Z_{N,m})\ \xrightarrow{\ d\ }\ (P_1,\ldots,P_m),$$</div>
<p>where the $P_j$ are independent Poisson variables with means $e^{-x_j}-e^{-x_{j+1}}$ for $j<m$ and $e^{-x_m}$ for $j=m$. The same limit holds for tree-component counts, and the two count vectors agree with probability tending to one. For every fixed $K\ge1$,</p>
<div class="math-display">$$(s_N(L_1),\ldots,s_N(L_K))\ \xrightarrow{\ d\ }\ (G_1,\ldots,G_K),\qquad G_j=-\log(E_1+\cdots+E_j),$$</div>
<p>where $E_1,E_2,\ldots$ are independent exponential variables of mean one. With probability tending to one, the first $K$ components are trees, so their tree-rank vector has the same limit.</p>
<p><em>Proof.</em> First cap all component sizes at $M=\lfloor2B/I\rfloor$ and count only trees. The first-moment calculation in <a href="/tag/VGZ9/">VGZ9</a>, subtracted at successive thresholds, gives limiting means $\lambda_j=e^{-x_j}-e^{-x_{j+1}}$ and $\lambda_m=e^{-x_m}$. Its ordered-tuple formula applies uniformly to any fixed total number of components in these intervals. Summing that formula with the prescribed interval for each component gives every mixed factorial moment:</p>
<div class="math-display">$$\mathbb E\prod_{j=1}^m(Z_{N,j}^{\mathrm{tree},\le M})_{\ell_j}\longrightarrow\prod_{j=1}^m\lambda_j^{\ell_j}\qquad(\ell_1,\ldots,\ell_m\ge0).$$</div>
<p>Here $(z)_\ell=z(z-1)\cdots(z-\ell+1)$, with $(z)_0=1$. Disjoint intervals ensure that all selected components are distinct. The uniform tuple error remains $o(1)$ because the total number $\sum_j\ell_j$ is fixed and all sizes are $O(\varepsilon^{-2}\log(N\varepsilon^3))$.</p>
<p>To identify the joint law directly, fix $z_j\in[0,1]$ and independently retain each counted component in interval $j$ with probability $1-z_j$. Let $H_N$ be the total retained count. The multinomial expansion of its factorial moments gives</p>
<div class="math-display">$$\mathbb E(H_N)_\ell\longrightarrow\left(\sum_j(1-z_j)\lambda_j\right)^\ell.$$</div>
<p>The alternating bounds for the zero-count probability used in VGZ9 therefore imply</p>
<div class="math-display">$$\mathbb E\prod_j z_j^{Z_{N,j}^{\mathrm{tree},\le M}}=\mathbb P(H_N=0)\longrightarrow\exp\left[-\sum_j(1-z_j)\lambda_j\right].$$</div>
<p>Bounded first moments give tightness of the capped vectors. Each subsequential limit has the displayed probability generating function, which uniquely determines the independent Poisson law by its power-series coefficients. This proves joint convergence. By <a href="/tag/X0R0/">X0R0</a>, the probability of any component larger than $M$ tends to zero. By <a href="/tag/CJ8R/">CJ8R</a>, all components above the smallest threshold are trees with probability tending to one. Removing the cap and adding the other components thus preserve the limit.</p>
<p>The limiting counts are those of the points $-\log(E_1+\cdots+E_j)$: the exponential arrival times form a rate-one Poisson process on $(0,\infty)$, and the change of variable $y=e^{-x}$ gives intensity $e^{-x}\,dx$. For any fixed thresholds $a_1,\ldots,a_K$, the event $s_N(L_j)\le a_j$ for every $j$ is the event that the count above $a_j$ is at most $j-1$ for every $j$. For large $N$ the corresponding size cutoffs are positive, so this remains true with zero padding. Express these tail counts through the intervals cut out by the distinct $a_j$ and apply the joint count limit. The resulting vector distribution has continuous marginals, proving the ordered-size limit. Finally, for a fixed low threshold $x$, absence of cyclic components above $x$ and $s_N(L_K)>x$ ensure that the first $K$ components are trees. Take the limit in $N$ and then let $x\to-\infty$. $\square$</p>
