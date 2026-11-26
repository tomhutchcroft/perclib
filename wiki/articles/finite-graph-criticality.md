---
{
  "id": "finite-graph-criticality",
  "title": "Critical parameters on finite graphs",
  "subtitle": "Susceptibility normalization, triangle mass and exponential component bounds",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A susceptibility level defines a finite-graph parameter. Its constant Fourier mode explains the volume term in the triangle bound; optimized tree-graph tails give explicit largest-component estimates and a one-sided comparison with an infinite-graph critical point.",
  "context": [
    "Independent bond percolation on a finite connected graph with $N\\ge2$ vertices, except where an infinite covering graph is explicitly introduced.",
    "For a transitive graph, $\\chi(p)=\\mathbb E_p|C(v)|$ is independent of the root.",
    "The parameter defined by a finite susceptibility level is a normalization; the scaling-window theorems require further hypotheses."
  ],
  "related": [
    "critical-random-graph-clusters",
    "quotient-cluster-bounds",
    "connection-kernels",
    "exponential-moments",
    "triangle-susceptibility"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "finite triangle condition",
    "Borgs Chayes critical parameter",
    "finite susceptibility threshold",
    "optimized cluster tail"
  ],
  "prototypeUses": []
}
---

## Choosing a susceptibility level {#section-parameter}

<a id="tag-6JZB" data-assertion="proposition" data-title="Every intermediate susceptibility level defines a unique parameter on a finite connected graph"></a>
<p>For each vertex $v$ of a finite connected graph on $N\ge2$ vertices, the function $p\mapsto\chi_v(p)=\mathbb E_p|C(v)|$ is a polynomial, continuous and strictly increasing on $[0,1]$, with endpoint values $1$ and $N$. Thus each $c\in[1,N]$ has a unique solution of $\chi_v(p)=c$; no solution exists outside this interval.</p>
<p>On a transitive graph, write $p_\lambda$ for this solution at $c=\lambda N^{1/3}$. It belongs to $(0,1)$ exactly when $1<\lambda N^{1/3}<N$.</p>
<p><em>Proof.</em> Sum $|C(v)|$ over the finitely many configurations, weighted by their product probabilities, to obtain a polynomial. The common-uniform coupling makes it nondecreasing. To see strictness for $0\le p<q<1$, choose a bond incident to $v$. There is positive probability that its uniform variable lies in $(p,q]$ and every other bond's uniform variable exceeds $q$. On this event the component has size one at $p$ and size two at $q$. Hence $\chi_v(q)>\chi_v(p)$. For $q=1$, insert an intermediate parameter between $p$ and one. The endpoint values follow from connectedness. Continuity and strict monotonicity prove existence and uniqueness.</p>
<p>A fixed positive $\lambda$ satisfies the strict range for all sufficiently large $N$. No infinite cluster appears at $p_\lambda$: the graph is finite. Whether this normalization locates its critical window is a further assertion.</p>

## The constant mode of the triangle {#section-triangle}

<p>Let $T_{xy}=\mathbb P_p(x\leftrightarrow y)$ and $\Delta_p(x,y)=(T^3)_{xy}$. The finite triangle condition is a uniform bound of the form $\Delta_p(x,y)\le\mathbf1_{\{x=y\}}+a_0$, with small $a_0$; finiteness of a sum on a finite graph supplies no such smallness.</p>
<a id="tag-R2Y7" data-assertion="proposition" data-title="The constant mode controls the finite triangle, with an exact complete-graph formula"></a>
<p>On a finite transitive graph with $N$ vertices and susceptibility $\chi$,</p>
<div class="math-display">$$\sum_y\Delta_p(x,y)=\chi^3,\qquad
\Delta_p(x,x)\ge\frac{\chi^3}{N}.$$</div>
<p>Consequently, a bound $\Delta_p(x,y)\le\mathbf1_{\{x=y\}}+a_0$ for every $x,y$ requires $a_0\ge(\chi^3-1)/N$.</p>
<p>For the complete graph, put $a=(\chi-1)/(N-1)$. Then</p>
<div class="math-display">$$\Delta_p(x,y)=(1-a)^3\mathbf1_{\{x=y\}}
+\frac{\chi^3-(1-a)^3}{N}
\le\mathbf1_{\{x=y\}}+\frac{\chi^3}{N}.$$</div>
<p>In particular, at a defined $p_\lambda$, the complete graph satisfies the finite triangle bound with $a_0=\lambda^3$.</p>
<p><em>Proof.</em> Every row of $T$ sums to $\chi$, so $T^3\mathbf1=\chi^3\mathbf1$. The <a href="/tag/70KD/">connection kernel is positive semidefinite</a>; hence its eigenvalues are nonnegative, and one is $\chi$. Transitivity makes every diagonal entry of $T^3$ equal. Thus $N\Delta_p(x,x)=\operatorname{tr}(T^3)\ge\chi^3$. Summing the assumed triangle bound over $y$ gives its necessary condition on $a_0$.</p>
<p>On the complete graph, symmetry gives $T_{xx}=1$ and $T_{xy}=a$ for $x\ne y$, with $0\le a\le1$. Let $P=N^{-1}\mathbf1\mathbf1^{\mathsf T}$ be the projection onto constants. Then</p>
<div class="math-display">$$T=(1-a)(I-P)+\chi P,\qquad
T^3=(1-a)^3(I-P)+\chi^3P.$$</div>
<p>Taking entries proves the formula; $0\le1-a\le1$ gives the bound. The volume term $\lambda^3$ is therefore present even in this maximally symmetric example.</p>

## Optimizing the weighted exponential bound {#section-optimized-tail}

<a id="tag-4A0G" data-assertion="theorem" data-title="Optimized exponential cluster tails retain the inverse-square-root prefactor"></a>
<p>For independent bond percolation on a nonempty countable vertex set, suppose $M=\sup_v\mathbb E|C(v)|<\infty$, and write $\chi_o=\mathbb E|C(o)|$. For every real $k\ge M^2$,</p>
<div class="math-display">$$\mathbb P(|C(o)|\ge k)
\le\frac{\chi_o}{M}\sqrt{\frac ek}\exp\left(-\frac{k}{2M^2}\right).$$</div>
<p>For a transitive model, $M=\chi_o=\chi$, so the prefactor is simply $\sqrt{e/k}$.</p>
<p><em>Proof.</em> For $0\le t<(2M^2)^{-1}$, the <a href="/tag/XLWI/">weighted exponential estimate</a> gives</p>
<div class="math-display">$$\mathbb P(|C(o)|\ge k)
\le\frac{\mathbb E[|C(o)|e^{t|C(o)|}]}{ke^{tk}}
\le\frac{\chi_o e^{-tk}}{k\sqrt{1-2tM^2}}.$$</div>
<p>The logarithm of the final expression has derivative $-k+M^2/(1-2tM^2)$, vanishing at</p>
<div class="math-display">$$t_* = \frac1{2M^2}-\frac1{2k}.$$</div>
<p>Our assumption gives $0\le t_*<(2M^2)^{-1}$. Substituting $1-2t_*M^2=M^2/k$ proves the result. At $k=M^2$, the minimizing parameter is zero, which is allowed.</p>
<p>The domain of $t$ is essential. The bound is not a real-valued expression for arbitrary $t\ge0$; see the <a href="/errata/heydenreich-hofstad/#finite-weighted-mgf-domain">provisional source correction</a>. Its moment input is the existing <a href="/tag/Y84V/">tree-graph theorem</a>, not an extra finiteness assumption on higher moments.</p>

## Largest components below the volume scale {#section-largest}

<a id="tag-3RIO" data-assertion="corollary" data-title="Uniform susceptibility gives explicit finite-graph largest-component tails"></a>
<p>For independent bonds on a finite graph with $N$ vertices, put $M=\max_v\mathbb E|C(v)|$ and $L_1=\max_v|C(v)|$. Then, for every real $k\ge M^2$,</p>
<div class="math-display">$$\mathbb P(L_1\ge k)\le\sqrt e\,N k^{-3/2}e^{-k/(2M^2)}.$$</div>
<p>If $R=N/M^3\ge\sqrt e$, this gives</p>
<div class="math-display">$$\mathbb P\bigl(L_1\ge2M^2\log R\bigr)
\le\frac{\sqrt e}{(2\log R)^{3/2}}.$$</div>
<p>If instead one knows $M\le K N^{1/3}$ for some $K>0$, then, for all $A>0$,</p>
<div class="math-display">$$\mathbb P(L_1\ge AN^{2/3})
\le \sqrt e\max(1,K^3)\,A^{-3/2}e^{-A/(2K^2)}.$$</div>
<p><em>Proof.</em> The deterministic count of vertices in components of size at least $k$ gives</p>
<div class="math-display">$$\mathbb P(L_1\ge k)
\le\frac1k\sum_v\mathbb P(|C(v)|\ge k).$$</div>
<p>This holds for real $k>0$ too: a component whose integer size exceeds that threshold contributes at least $k$ vertices. Apply the preceding bound at each vertex and use $\chi_v/M\le1$ to prove the first estimate. When $R\ge\sqrt e$, the choice $k=2M^2\log R$ satisfies $k\ge M^2$; substitution gives the second.</p>
<p>For the last estimate, take $k=AN^{2/3}$. If $A\ge K^2$, the first bound applies and its exponent is at most $-A/(2K^2)$. For $0<A<K^2$, the function $A^{3/2}e^{A/(2K^2)}$ is increasing and bounded by $K^3e^{1/2}$, so the stated right-hand side is at least one. This covers the remaining range.</p>
<p>Thus a susceptibility upper bound throughout a finite critical window implies the exponential largest-component upper tail there. It does not supply that susceptibility bound or the matching lower tail by itself. The <a href="/articles/quotient-cluster-bounds/#section-torus">torus argument</a> obtains the required susceptibility bound from lattice tails and rooted damping.</p>

## Comparing finite and infinite critical parameters {#section-parameter-comparison}

<a id="tag-FUZK" data-assertion="proposition" data-title="A quotient coupling gives a one-sided finite-volume critical-parameter comparison"></a>
<p>Let the finite connected transitive graph $H$, with $N\ge2$ vertices, admit a neighbour-lifting surjection from a countable locally finite graph $G$. Fix a lift $o$ of a vertex of $H$. Suppose $p_*\in(0,1]$, $K>0$, and</p>
<div class="math-display">$$\mathbb E_p^G|C_G(o)|\le\frac K{p_*-p}\qquad(0\le p<p_*).$$</div>
<p>If $1<\lambda N^{1/3}<N$, then the susceptibility-defined parameter of $H$ satisfies</p>
<div class="math-display">$$p_\lambda(H)\ge p_*-\frac K{\lambda N^{1/3}}.$$</div>
<p><em>Proof.</em> Put $b=p_*-K/(\lambda N^{1/3})$. If $b\le0$ the claim is immediate. Otherwise $0<b<p_*$, and <a href="/tag/VUI1/">cluster domination</a>, followed by the tail-sum identity, gives</p>
<div class="math-display">$$\chi_H(b)\le\mathbb E_b^G|C_G(o)|
\le\lambda N^{1/3}=\chi_H(p_\lambda(H)).$$</div>
<p>Strict monotonicity of $\chi_H$ gives $b\le p_\lambda(H)$.</p>
<p>For sufficiently high-dimensional nearest-neighbour tori, <a href="/tag/0Y4K/">the lattice susceptibility bound</a> and the <a href="/tag/F7N7/">small critical triangle</a> allow $K=2/(2d)$ and $p_*=p_c(\mathbb Z^d)$. The row-sum lower bound gives $2dp_*\ge1$. Consequently, with $V=n^d$ and the susceptibility level in its valid range,</p>
<div class="math-display">$$p_\lambda(\mathbb T_{n,d})
\ge p_c(\mathbb Z^d)\left(1-\frac2\lambda V^{-1/3}\right).$$</div>
<p>This proves the one-sided comparison in Exercise 13.9. The other side requires a lower comparison of the torus susceptibility with the lattice susceptibility, and is not a consequence of domination.</p>

## What the finite triangle programme still requires {#section-scope}

<p>The existing <a href="/tag/L82Q/">three-point tree-graph bound</a> supplies the second moment used in this chapter, and <a href="/tag/Y84V/">Y84V</a> supplies every higher moment in Exercise 13.7. In the displayed three-arm event, all three arms must meet at the branch vertex; the following probability estimate in the source already has that form. The <a href="/errata/heydenreich-hofstad/#finite-tree-arm-origin">provisional notation correction</a> records the mismatch.</p>
<p>The <a href="/coverage/sources/heydenreich-hofstad-2017-random-graphs/">Section 13.3 map</a> distinguishes these deductions from the general finite-triangle differential theory, the lower critical-window root tail, the two-sided location of the lattice critical point, and supercritical giant-component results. Historical open problems in the manuscript are recorded as historical statements, not certified as currently open.</p>
