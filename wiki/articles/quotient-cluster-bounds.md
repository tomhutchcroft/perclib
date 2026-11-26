---
{
  "id": "quotient-cluster-bounds",
  "title": "Clusters on quotient graphs",
  "subtitle": "Lifting exploration and transferring finite-volume upper bounds",
  "kind": "theorem",
  "category": "Methods and inequalities",
  "summary": "A neighbour-lifting map lets a quotient cluster be explored inside a larger graph without reusing bond variables. Root-cluster tails then bound the largest finite component and its moments, including the critical high-dimensional torus.",
  "context": [
    "Graphs are simple, countable and locally finite unless stated otherwise.",
    "Independent bond percolation has the same parameter $p\\in[0,1]$ on both graphs.",
    "A quotient graph has one edge between distinct orbits whenever adjacent representatives exist; loops and multiplicities are discarded."
  ],
  "related": [
    "critical-random-graph-clusters",
    "finite-random-graphs",
    "stopped-exploration",
    "green-free-triangle"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "quotient percolation",
    "torus cluster comparison",
    "Benjamini Schramm coupling"
  ],
  "prototypeUses": []
}
---

## Lifting a stopped exploration {#section-lifting}

<a id="tag-VUI1" data-assertion="theorem" data-title="Neighbour lifting gives stochastic domination of a quotient cluster"></a>
<p>Let $G,H$ be simple countable locally finite graphs, and let $f:V(G)\to V(H)$ be a surjection such that</p>
<div class="math-display">$$b\sim_H f(x)\quad\Longrightarrow\quad
\text{there is }y\sim_Gx\text{ with }f(y)=b.$$</div>
<p>Fix $x\in V(G)$ and write $C_G(x),C_H(f(x))$ for the respective open clusters. Then, for every integer $k\ge1$ and every $p\in[0,1]$,</p>
<div class="math-display">$$\mathbb P_p^H\bigl(|C_H(f(x))|\ge k\bigr)
\le\mathbb P_p^G\bigl(|C_G(x)|\ge k\bigr).$$</div>
<p>In particular, the comparison holds for the orbit map of any group of automorphisms of $G$, with $H$ its simple quotient. Cluster sizes may be infinite.</p>
<p><em>Proof.</em> Fix $k$. Explore the component in $H$, maintaining a queue of discovered vertices. Process each vertex's finitely many neighbours in a fixed order, querying a bond only when its other endpoint has not yet been discovered and the bond has not been queried before. Stop when the queue is empty or $k$ vertices have been discovered. This procedure makes only finitely many queries: before the second stopping condition it processes fewer than $k$ vertices, each with finite degree.</p>
<p>Alongside every discovered vertex $a\in H$, keep one representative $\widetilde a\in G$ with $f(\widetilde a)=a$, starting with $\widetilde{f(x)}=x$. If the next query is $\{a,b\}$ with $a$ discovered and $b$ undiscovered, choose a neighbour $y$ of $\widetilde a$ satisfying $f(y)=b$. Reveal the $G$-bond $\{\widetilde a,y\}$ and give the queried $H$-bond the same state. On an open outcome, discover $b$ and set $\widetilde b=y$.</p>
<p>The lifted bond is fresh. If it had been used earlier, the images of its endpoints would give the same unordered $H$-bond, which the exploration never queries twice. The choice of lift depends only on previous answers and the fixed graph data. Thus every new answer is Bernoulli with parameter $p$, independent of the past. Deferred decisions give the required product-percolation law on $H$; after stopping, fill all unqueried bonds independently. The configuration on $G$ was an independent product configuration from the outset.</p>
<p>Distinct discovered vertices have distinct representatives, since their images under $f$ differ. Every representative is connected to $x$ by the lifted discovery edges. Hence discovering $k$ vertices in $H$ produces $k$ distinct vertices in $C_G(x)$. If the queue empties first, all bonds from the discovered set to its complement have been tested and found closed, so the whole $H$-cluster has been found. This proves the tail comparison for this $k$, and therefore stochastic domination.</p>
<p>For the orbit map, let $b$ be an orbit adjacent to the orbit of $x$. Choose adjacent representatives $u,v$ of these two orbits. An automorphism taking $u$ to $x$ takes $v$ to a neighbour of $x$ in $b$, proving the lifting property. Each quotient vertex has finitely many neighbours because every one has a representative adjacent to any fixed lift.</p>
<p>The construction does not project a whole percolation configuration to the quotient by declaring an edge open whenever any of its lifts is open. That operation generally changes its marginal probability. Only one fresh lift supplies each queried edge.</p>

## Root tails control the largest component {#section-finite-tail}

<a id="tag-JZ89" data-assertion="theorem" data-title="A uniform power tail at each root bounds the largest finite component and its moments"></a>
<p>Let a random graph on $N\ge1$ vertices satisfy, for some $\alpha>0$ and $C\ge1$,</p>
<div class="math-display">$$\mathbb P(|C(v)|\ge k)\le Ck^{-\alpha}
\qquad\text{for every vertex }v\text{ and integer }k\ge1.$$</div>
<p>No independence or transitivity assumption is needed. With $L_1=\max_v|C(v)|$,</p>
<div class="math-display">$$\mathbb P\bigl(L_1\ge A N^{1/(1+\alpha)}\bigr)
\le C A^{-(1+\alpha)}\qquad(A\ge1),$$</div>
<p>and, for $0<q<1+\alpha$,</p>
<div class="math-display">$$\mathbb E L_1^q
\le\left(1+\frac{qC}{1+\alpha-q}\right)N^{q/(1+\alpha)}.$$</div>
<p><em>Proof.</em> Let $Z_{\ge k}$ count vertices in components of size at least $k$. The deterministic implication $L_1\ge k\Rightarrow Z_{\ge k}\ge k$ gives</p>
<div class="math-display">$$\mathbb P(L_1\ge k)\le\frac{\mathbb E Z_{\ge k}}k
=\frac1k\sum_v\mathbb P(|C(v)|\ge k)
\le CNk^{-(1+\alpha)}.$$</div>
<p>Take $k=\lceil A N^{1/(1+\alpha)}\rceil$; if $k>N$, the event is empty. For the moment bound, put $a=N^{1/(1+\alpha)}$. Integer rounding gives $\mathbb P(L_1>t)\le CNt^{-(1+\alpha)}$ for $t\ge a$. Layer cake and the bound one on the remaining interval yield</p>
<div class="math-display">$$\begin{aligned}
\mathbb E L_1^q
&=q\int_0^\infty t^{q-1}\mathbb P(L_1>t)\,dt\\
&\le a^q+qCN\int_a^\infty t^{q-2-\alpha}\,dt
=\left(1+\frac{qC}{1+\alpha-q}\right)a^q.
\end{aligned}$$</div>
<p>The restriction on $q$ is precisely the convergence condition for this last integral. A lower root-tail bound alone would not give a matching lower bound on $L_1$; controlling dependence among large components is a separate matter.</p>

## Critical tori {#section-torus}

<p>Let $\mathbb T_{n,d}=(\mathbb Z/n\mathbb Z)^d$ have its nearest-neighbour simple graph, with $n\ge3$, and write $V=n^d$. Reduction modulo $n$ has the neighbour-lifting property from $\mathbb Z^d$, so the torus root cluster is stochastically dominated by the lattice root cluster at the same parameter.</p>
<a id="tag-SUMF" data-assertion="corollary" data-title="Critical high-dimensional tori have a two-thirds largest-component upper scale"></a>
<p>There are absolute $d_0,C>0$ such that, for every $d\ge d_0$, $n\ge3$ and $A\ge1$, independent bond percolation on $\mathbb T_{n,d}$ at $p=p_c(\mathbb Z^d)$ satisfies</p>
<div class="math-display">$$\mathbb P_p(L_1\ge AV^{2/3})\le C A^{-3/2}.$$</div>
<p>For every $0<q<3/2$, the same models satisfy</p>
<div class="math-display">$$\mathbb E_p L_1^q\le\left(1+\frac{qC}{3/2-q}\right)V^{2q/3}.$$</div>
<p>In particular, $\mathbb E_pL_1\le(1+2C)V^{2/3}$.</p>
<p>There are also absolute $c,C_1,C_2>0$ such that</p>
<div class="math-display">$$\mathbb P_p(L_1\ge AV^{2/3})\le C_1A^{-3/2}e^{-cA},\qquad
\sup_v\mathbb E_p|C(v)|\le C_2V^{1/3}.$$</div>
<p>Consequently, for every $q>0$ there is a constant $C_q$, independent of $d,n$, such that $\mathbb E_pL_1^q\le C_qV^{2q/3}$.</p>
<p><em>Proof.</em> The <a href="/tag/74SS/">dimension-uniform critical cluster-tail bound</a> on the lattice gives $\mathbb P_{p_c}(|C_{\mathbb Z^d}(0)|\ge k)\le Ck^{-1/2}$. Translation invariance makes the bound uniform in the choice of root. Apply the lifting comparison at every torus vertex and then the preceding theorem with $\alpha=1/2$.</p>
<p>For the exponential improvement, put $a=V^{2/3}$ and $M=\min\{m\ge1:\mathbb P_p(L_1\ge m)\le e^{-1}\}$. The first tail bound gives</p>
<div class="math-display">$$M\le Ba,\qquad B=(eC)^{2/3}+1.$$</div>
<p>For an integer $k\ge M$, the <a href="/tag/12NL/">proved rooted damping bound</a> and the transferred root tail give, with $t=k/M$,</p>
<div class="math-display">$$\begin{aligned}
\mathbb P_p(L_1\ge k)
&\le\frac Vk\sup_v\mathbb P_p(|C(v)|\ge k)\\
&\le eC\frac Vk M^{-1/2}e^{-k/(9M)}
=eC V k^{-3/2}t^{1/2}e^{-t/9}
\le C' V k^{-3/2}e^{-t/18}.
\end{aligned}$$</div>
<p>The last constant is finite because $t^{1/2}e^{-t/18}$ is bounded for $t\ge1$. With $k=\lceil Aa\rceil$, one has $t\ge A/B$, giving the claimed exponential factor with $c=1/(18B)$. If $k<M$, then $A<B$, so the original power bound gives the same conclusion after enlarging $C_1$. This also covers empty events with $k>V$.</p>
<p>Layer cake now bounds every positive moment: one may take</p>
<div class="math-display">$$C_q=1+qC_1\int_1^\infty u^{q-5/2}e^{-cu}\,du<\infty.$$</div>
<p>Finally, apply <a href="/tag/WRHL/">finite-set hyperscaling</a> to the entire torus, with $\delta=2$. Its global root-tail hypothesis comes from lifting and 74SS; its rooted damping hypothesis is exactly 12NL. The conclusion $V^{-1}\sum_w\mathbb P_p(v\leftrightarrow w)\le C_2V^{-2/3}$ is the stated susceptibility bound.</p>
<p>The parameter here is the infinite-lattice critical point; no critical parameter has been defined by a phase transition on the finite torus. The <a href="/coverage/sources/heydenreich-hofstad-2017-random-graphs/">source map</a> keeps matching lower bounds and lower bounds for the other ordered components separate. Quotient domination and rooted damping do not supply them.</p>
