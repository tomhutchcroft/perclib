---
{
  "id": "sharpness-exercises",
  "title": "Infinite pivotal sets and zero-field limits",
  "subtitle": "Uniqueness, half-space connections and exact field asymptotics",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "A boundary-counting proof gives nearest-neighbour uniqueness. Two opposite half-space connections then provide a vertex with two disjoint infinite rays, which forces every rooted pivotal set to be finite. Positive-field inequalities also yield an integrated density bound directly, while the tail transform distinguishes exact field asymptotics from logarithmic exponents.",
  "context": [
    "The geometric assertions concern independent nearest-neighbour bond percolation on the integer lattice, in dimension d at least one.",
    "A backbone vertex here means a vertex with two edge-disjoint infinite simple open rays. It is not the two-point backbone count used elsewhere in the wiki.",
    "The finiteness of pivotal sets assumes positive half-space percolation at the parameter under consideration. That assumption is not proved here.",
    "The field asymptotics concern an arbitrary positive integer-valued cluster volume with the specified tail; no percolation exponent hypothesis is inferred for a model."
  ],
  "related": ["sharpness-bond-parameter", "infinite-cluster-uniqueness", "infinite-cluster-zero-one", "forest-connections", "ghost-fields"],
  "sourceIds": ["heydenreich-hofstad"],
  "aliases": ["finite pivotal set", "half-space backbone", "encounter boxes", "magnetization Abelian asymptotics"],
  "prototypeUses": []
}
---

## Encounter boxes and uniqueness {#section-uniqueness}

<a id="tag-Y6SG" data-assertion="theorem" data-title="Uniqueness of the infinite cluster for nearest-neighbour lattice percolation"></a>
<p>For every $p\in[0,1]$, nearest-neighbour bond percolation on $\mathbb Z^d$ has at most one infinite cluster almost surely.</p>
<p><em>Proof.</em> The endpoints are immediate: every vertex is isolated at $p=0$, and the full lattice is connected at $p=1$. Suppose $0<p<1$. The <a href="/tag/6GNC/">cluster-number trichotomy</a> leaves only the possibility of infinitely many infinite clusters to exclude.</p>
<p>Call a finite box $B$ an encounter box if its vertices are connected by open edges inside $B$, and deleting $B$ from their open cluster leaves at least three infinite components. If infinitely many infinite clusters exist, some fixed box $B=\Lambda_m$ meets at least three of them with positive probability. Removing $B$ leaves an infinite component of each such cluster adjacent to $B$: there are only finitely many boundary edges, so these finitely many components could not all be finite.</p>
<p>There are finitely many choices of three boundary edges. Thus some fixed triple has positive probability that its three exterior endpoints belong to distinct infinite components of the graph outside $B$. This event reads only edges with both endpoints outside $B$. Independently force every internal edge of $B$ open, those three boundary edges open, and all other boundary edges closed. The prescribed finite assignment has strictly positive probability because $0<p<1$. In the resulting configuration, $B$ is an encounter box. Write $\eta>0$ for its probability.</p>
<p>Consider the disjoint translates $B_z=(2m+3)z+B$, $z\in\mathbb Z^d$. We claim that in every configuration, the number of encounter boxes among those contained in $\Lambda_{N-1}$ is at most $|\partial\Lambda_N|$. Contract each such encounter box to one vertex in the open graph restricted to $\Lambda_N$, retaining the vertices of $\partial\Lambda_N$ as terminals.</p>
<p>Contraction of a different encounter box cannot join two components separated by deletion of the first: the other box is disjoint from the first and internally connected. For each contracted encounter vertex $v$, at least three components of its infinite cluster after deleting $v$ contain paths to $\partial\Lambda_N$. Stop one path in each component on its first visit to that boundary. They show that the finite contracted graph minus $v$ has at least three distinct components containing terminals, all joined through $v$ before its deletion.</p>
<p>In every component of the finite contracted graph that meets the boundary, take a spanning tree and prune leaves that are not terminals until none remain. Every encounter vertex survives and has degree at least three, because the three separated terminal sets must still be joined. All leaves are terminals. The <a href="/tag/4K33/">finite-forest degree bound</a> therefore bounds the number of encounter vertices by the number of boundary vertices, proving the claim.</p>
<p>By translation invariance, the expected number of encounter boxes contained in $\Lambda_{N-1}$ is $\eta$ times the number of grid boxes there, which grows proportionally to $N^d$. The deterministic bound is $|\partial\Lambda_N|=O(N^{d-1})$. This contradiction excludes infinitely many infinite clusters.</p>
<p>The proof uses finite degree, finite-range boundaries and both opening and closing of finite edge sets. It supplies the nearest-neighbour case needed below; it does not prove the full long-range uniqueness target <a href="/tag/T9KC/">T9KC</a>.</p>

## Two rays control all pivotal edges {#section-pivotals}

<p>Let</p>
<div class="math-display">$$\theta_{\mathrm{half}}(p)=\mathbb P_p\bigl(0\leftrightarrow\infty\text{ in }\{x:x_1\ge0\}\bigr).$$</div>

<a id="tag-5E0D" data-assertion="proposition" data-title="Positive half-space percolation implies finite rooted pivotal sets"></a>
<p>If $p>0$ and $\theta_{\mathrm{half}}(p)>0$, then almost surely every vertex has only finitely many pivotal bonds for its connection to infinity.</p>
<p><em>Proof.</em> Open the two bonds from $0$ to $e_1$ and $-e_1$. Independently require infinite connections from these endpoints inside the disjoint half-spaces $\{x_1\ge1\}$ and $\{x_1\le-1\}$. The four requirements read disjoint coordinate sets, so their intersection has probability</p>
<div class="math-display">$$p^2\theta_{\mathrm{half}}(p)^2>0.$$</div>
<p>Local finiteness supplies an infinite simple ray in each infinite component, by choosing successively a neighbour with infinitely many possible continuations. Thus on this event $0$ has two edge-disjoint infinite rays.</p>
<p>The event that some vertex has two such rays is measurable and translation invariant. For a fixed vertex, two rays exist exactly when there are two edge-disjoint paths to the boundary of every box centred there. The reverse implication follows by a diagonal subsequence of pairs of paths: finite degree leaves finitely many choices for each pair of initial segments. Each box event is a finite-coordinate event. A countable union over vertices therefore proves measurability. <a href="/tag/WUAF/">Translation ergodicity</a> now makes existence of some backbone vertex almost sure.</p>
<p>By Y6SG there is only one infinite cluster. Every vertex $x$ in it is joined by a finite open path $P$ to a backbone vertex $v$. Deleting any edge outside $P$ leaves $P$ intact and leaves at least one of the two edge-disjoint rays from $v$ intact. Hence a pivotal edge for $x\leftrightarrow\infty$ must lie on $P$. If instead the cluster of $x$ is finite, opening one edge can make it infinite only if that edge belongs to the finite boundary of the cluster. In both cases the pivotal set is finite. The uniqueness and backbone events used in the argument hold simultaneously for all roots.</p>
<p>This proves the half-space implication in Exercise 3.7 of the manuscript. It does not prove positivity of the half-space probability throughout the supercritical interval, nor claim to reproduce the original Chayes–Chayes argument cited there.</p>

## An integrated inequality at zero field {#section-zero-field}

<a id="tag-9PPO" data-assertion="proposition" data-title="The positive-field inequality gives an integrated supercritical density bound"></a>
<p>For $p_c<a<b<1$,</p>
<div class="math-display">$$b\theta(b)-a\theta(a)\ge b-a.$$</div>
<p>Consequently, for $p_c<b<1$,</p>
<div class="math-display">$$\theta(b)\ge\frac{b-p_c}{b},$$</div>
<p>and at every differentiability point $p\in(p_c,1)$ of the monotone function $\theta$,</p>
<div class="math-display">$$\theta(p)\le\theta(p)^2+p\theta(p)\theta'(p).$$</div>
<p>The last statement therefore holds almost everywhere. No assertion of differentiability at every parameter is needed.</p>
<p><em>Proof.</em> Start with the finite-torus inequalities proved in <a href="/tag/G192/">G192</a>. Dividing the second one by $M_R>0$ and integrating in $p$ gives, for every positive field $\gamma$,</p>
<div class="math-display">$$bM_R(b,\gamma)-aM_R(a,\gamma)
\ge b-a-\int_a^b\frac{\gamma(M_R)_\gamma(p,\gamma)}{M_R(p,\gamma)}\,dp.$$</div>
<p>The local uniform convergence of $M_R$ and its field derivative, and $M_R\ge\gamma$, permit passage to the infinite lattice at this fixed field. This obtains the same inequality for $M$ at every $\gamma>0$, without choosing a parameter section of an almost-everywhere two-variable inequality.</p>
<p>Let $T$ be the root-cluster volume. For $0<\gamma\le1/2$,</p>
<div class="math-display">$$\gamma M_\gamma(p,\gamma)=
\mathbb E_p[\gamma T(1-\gamma)^{T-1};T<\infty]\longrightarrow0.$$</div>
<p>For each finite $T$ the integrand tends to zero, while</p>
<div class="math-display">$$\gamma t(1-\gamma)^{t-1}\le e^{\gamma}\gamma t e^{-\gamma t}\le e^{1/2}/e\qquad(t\ge1).$$</div>
<p>Dominated convergence gives the limit at each $p$. Moreover $M(p,\gamma)\ge\theta(p)\ge\theta(a)>0$, so the same bound divided by $\theta(a)$ dominates the integrand of the parameter integral. A second dominated-convergence step makes that integral tend to zero. The positive-field limit of $M$ is $\theta$, proving the integrated inequality.</p>
<p>Drop $a\theta(a)\ge0$ and let $a\downarrow p_c$ to obtain the density bound. At a differentiability point $p$, apply the integrated inequality with $a=p$, $b=p+h$, divide by $h$, and let $h\downarrow0$. This gives $\theta(p)+p\theta'(p)\ge1$. Multiply by the positive number $\theta(p)$ to obtain the stated form.</p>
<p>This supplies the integrated and almost-everywhere versions of Exercises 3.6 and 3.8, using positive-field approximation rather than infinite-volume Russo differentiation. The finite-pivotal assertion above is a separate geometric result. The <a href="/tag/JQLC/">finite-set proof</a> already gives the sharper density bound with the additional factor $1/(1-p_c)$.</p>

## What a power tail implies for the field {#section-tail-asymptotics}

<a id="tag-FZQQ" data-assertion="proposition" data-title="Exact Abelian field asymptotics and the borderline logarithm"></a>
<p>Let $T\in\{1,2,\ldots,\infty\}$ satisfy $\mathbb P(T\ge n)\sim A n^{-\alpha}$, with $A>0$ and $\alpha>0$, where $\sim$ means ratio tending to one. For $m(\gamma)=\mathbb E[1-(1-\gamma)^T]$,</p>
<div class="math-display">$$m(\gamma)\sim
\begin{cases}
A\Gamma(1-\alpha)\gamma^\alpha,&0<\alpha<1,\\
A\gamma\log(1/\gamma),&\alpha=1,\\
\gamma\,\mathbb ET,&\alpha>1,
\end{cases}\qquad\gamma\downarrow0.$$</div>
<p>The tail assumption implies $\mathbb P(T=\infty)=0$, and the mean in the last line is finite. Under the weaker assumption $\mathbb P(T\ge n)=n^{-\alpha+o(1)}$, the conclusion is</p>
<div class="math-display">$$m(\gamma)=\gamma^{\min\{\alpha,1\}+o(1)}.$$</div>
<p><em>Proof.</em> Put $h=-\log(1-\gamma)$ and $F(n)=\mathbb P(T\ge n)$. The <a href="/tag/0NVH/">discrete tail identity</a> gives</p>
<div class="math-display">$$m(\gamma)=(e^h-1)\sum_{n\ge1}e^{-hn}F(n),\qquad h\sim\gamma.$$</div>
<p>For $0<\alpha<1$,</p>
<div class="math-display">$$h^{1-\alpha}\sum_{n\ge1}n^{-\alpha}e^{-hn}
=h\sum_{n\ge1}(hn)^{-\alpha}e^{-hn}
\longrightarrow\int_0^\infty x^{-\alpha}e^{-x}\,dx=\Gamma(1-\alpha).$$</div>
<p>To justify the improper Riemann sum, restrict first to $[\varepsilon,R]$. The omitted part below $\varepsilon$ is bounded by a constant times $\varepsilon^{1-\alpha}$, by summing $n^{-\alpha}$; the part above $R$ is bounded by an exponentially decaying integral. Then send $\varepsilon\downarrow0$ and $R\to\infty$. Squeezing $F(n)$ between $(A-\delta)n^{-\alpha}$ and $(A+\delta)n^{-\alpha}$ for large $n$ proves the first line, since finitely many initial terms contribute only $O(h)=o(h^\alpha)$.</p>
<p>For $\alpha=1$, use the exact identity</p>
<div class="math-display">$$\sum_{n\ge1}\frac{e^{-hn}}n=-\log(1-e^{-h})\sim\log(1/h).$$</div>
<p>The same squeeze works, with the finite initial contribution negligible compared with $h\log(1/h)$. For $\alpha>1$, the tail is summable and</p>
<div class="math-display">$$\frac{m(\gamma)}\gamma=\sum_{n\ge1}(1-\gamma)^{n-1}F(n)\uparrow\sum_{n\ge1}F(n)=\mathbb ET.$$</div>
<p>Finally, a logarithmic tail exponent gives the eventual bounds $n^{-\alpha-\delta}\le F(n)\le n^{-\alpha+\delta}$. If $\alpha<1$, apply the preceding power-sum estimates with small $\delta$ on both sides and then let $\delta\downarrow0$. If $\alpha>1$, choose $\delta<\alpha-1$ to obtain a finite mean and linear field behaviour. At $\alpha=1$, use $m(\gamma)\ge\gamma$ and the upper estimate of order $\gamma^{1-\delta}$ for every $\delta>0$. These bounds give the asserted logarithmic exponent.</p>
<p>The manuscript allows several meanings of its asymptotic notation. For Exercise 3.3, taking $\alpha=1/\delta$ with $\delta>1$ gives the expected field exponent; an exact tail equivalent also determines the Gamma factor. At $\delta=1$, the exact equivalent has a logarithm although the logarithmic exponent is still one. The <a href="/tag/3C2F/">two-sided comparison theorem</a> supplies a converse only for $0<\alpha<1$. These distinctions clarify scope; they are not recorded as a new source erratum.</p>

<p>The <a href="/coverage/sources/heydenreich-hofstad-2017-sharpness/">updated Chapter 3 map</a> identifies which exercises these arguments cover. The cited Chayes–Chayes chapter has been identified bibliographically but its full text has not yet been checked. No new compiled Lean association is asserted.</p>
