---
{
  "id": "mass-transport",
  "title": "Mass transport on countable groups",
  "subtitle": "Changing the root of an invariant sum",
  "kind": "method",
  "category": "Methods",
  "summary": "Diagonal invariance equates total outgoing and incoming mass on a group. For invariant random clusters this gives averaging identities on finite clusters and rules out equivariant choices of a single vertex in an infinite cluster.",
  "context": ["A countable group $\\Gamma$, with identity $o$, acts on its vertices by left multiplication.", "All transported quantities are nonnegative, so sums and expectations may be infinite.", "Random transports are measurable and equivariant, and their underlying probability law is invariant."],
  "related": ["product-symmetries", "connectivity", "susceptibility", "triangle-condition"],
  "sourceIds": ["hutchcroft-book", "perclib-train5-mass-transport"],
  "aliases": ["mass transport", "Cayley graph", "diagonal invariance", "unimodularity", "cluster averaging", "invariant representative"],
  "prototypeUses": []
}
---

## Changing the pinned vertex {#section-identity}

<a id="tag-IHJ3" data-assertion="proposition" data-title="Mass-transport identity for a countable group"></a><p>Suppose $F:\Gamma\times\Gamma\to[0,\infty]$ is diagonally invariant:</p><div class="math-display">$$F(gx,gy)=F(x,y)\qquad(g,x,y\in\Gamma).$$</div><p>Then</p><div class="math-display">$$\sum_{x\in\Gamma}F(o,x)=\sum_{x\in\Gamma}F(x,o).$$</div><p><em>Proof.</em> Translating by $x^{-1}$ gives $F(x,o)=F(o,x^{-1})$. Inversion is a bijection of the group, so reindexing the nonnegative sum proves the identity. No commutativity or summability is needed.</p><p>This is the mass-transport principle on a Cayley graph, independent of the choice of generating set. It also applies when an invariant weighted graph has every group element as a vertex and infinitely many possible neighbours. On a general transitive graph there is no group-inversion argument on the vertex set; an appropriate unimodularity assumption is needed. Transitivity alone is not being used as a substitute for that assumption.</p>

## Random transports {#section-random}

<a id="tag-K5ZX" data-assertion="theorem" data-title="Expected incoming and outgoing mass under an invariant law"></a><p>Let $\Gamma$ act measurably on a probability space $(\Omega,\mu)$, preserving $\mu$. For each $x,y\in\Gamma$, let $t(\cdot,x,y):\Omega\to[0,\infty]$ be measurable, and suppose</p><div class="math-display">$$t(g\omega,gx,gy)=t(\omega,x,y)\qquad(g,x,y\in\Gamma,\ \omega\in\Omega).$$</div><p>Then</p><div class="math-display">$$\mathbb E_\mu\sum_y t(\omega,o,y)=\mathbb E_\mu\sum_x t(\omega,x,o).$$</div><p><em>Proof.</em> Invariance of the law makes $F(x,y)=\mathbb E_\mu t(\omega,x,y)$ diagonally invariant. Apply the preceding identity to $F$, then use Tonelli on both sides. The equality holds in $[0,\infty]$ and requires no finite expectation.</p><p>For independent bonds, a left-invariant profile on distinct unordered pairs gives an invariant law of the simple open graph, by <a href="/tag/6VY0/">transport under vertex relabelling</a>. Graph observables can therefore use this theorem with the random graph as $\Omega$. Arbitrary diagonal coordinate parameters are harmless for this purpose: loops are discarded. If the transport also reads diagonal coordinates, invariance of the entire configuration law must instead be checked.</p>

## Averaging inside finite clusters {#section-finite}

<p>Suppose the random simple graph on $\Gamma$ has an invariant law. Any auxiliary marks used below must be included in the probability space, and the joint graph-and-mark law must be invariant. Write $K_x$ for the cluster of $x$.</p>

<a id="tag-4SZ9" data-assertion="proposition" data-title="Finite-cluster averaging under an invariant law"></a><p>Let $f(\omega,x)\in[0,\infty]$ be measurable and equivariant: $f(g\omega,gx)=f(\omega,x)$. Define two random variables to be zero when $K_o$ is infinite, and on the event that it is finite define them respectively as $f(\omega,o)$ and $|K_o|^{-1}\sum_{x\in K_o}f(\omega,x)$. These variables have the same expectation:</p><div class="math-display">$$\mathbb E\!\left[f(\omega,o);\ |K_o|&lt;\infty\right]=\mathbb E\!\left[\frac1{|K_o|}\sum_{x\in K_o}f(\omega,x);\ |K_o|&lt;\infty\right].$$</div><p>In particular, if a measurable equivariant rule selects exactly one vertex in each finite cluster, then</p><div class="math-display">$$\mathbb P(o\text{ is selected})=\mathbb E\!\left[\frac1{|K_o|};\ |K_o|&lt;\infty\right],$$</div><p>where the selection rule selects no vertices from infinite clusters.</p><p><em>Proof.</em> A vertex $x$ in a finite cluster sends mass $f(\omega,x)/|K_x|$ to each member of that cluster; every other transport value is zero. This is measurable and equivariant. Its outgoing mass at $o$ is the first variable, and its incoming mass is the second, since $K_x=K_o$ for $x\in K_o$. Apply expected mass transport. For the selection formula, use the indicator that $x$ is the selected vertex of its finite cluster. Its sum over such a cluster is one.</p><p>The finite-cluster restriction prevents undefined expressions such as infinity divided by infinity. No choice of a uniform vertex from an infinite cluster is implicit in this formula. Nor is a representative chosen using an arbitrary fixed ordering automatically equivariant; the selection hypothesis concerns the rule and its joint law.</p>

## Why an infinite cluster has no invariant representative {#section-infinite}

<a id="tag-O0TO" data-assertion="proposition" data-title="No equivariant single representative in infinite clusters"></a><p>Under an invariant random-graph-and-mark law on a countable group, let $R(\omega)\subseteq\Gamma$ be a measurable equivariant set that contains at most one vertex of each infinite cluster. Then almost surely $R$ contains no vertex of any infinite cluster. Consequently, if infinite clusters occur with positive probability, there is no such rule selecting exactly one vertex from each of them.</p><p><em>Proof.</em> Each vertex in an infinite cluster that meets $R$ sends one unit of mass to the unique selected vertex of that cluster. Other vertices send nothing. The outgoing mass at any vertex is at most one. The incoming mass at $o$ is infinite if $o\in R$ lies in an infinite cluster, and zero otherwise. Expected mass transport forces the probability of the first event to be zero. The same holds at every vertex by invariance, and a countable union shows that there is almost surely no selected vertex in an infinite cluster anywhere.</p><p>There is no contradiction with selecting one vertex from each finite cluster: its incoming mass is then finite, and the preceding averaging formula gives the selection density. There is also no claim about non-equivariant rules, such as choosing the least element in an externally fixed enumeration.</p>

<p>The deterministic identity is used to move the pinned vertex in percolation diagrams. This article proves the countable-group case and two general cluster applications. A broader unimodular-graph formulation and independent-cluster coupling and diagram estimates require additional arguments; they are not consequences of invariance alone.</p>


## Measure-preserving families {#section-measure-families}

<p>The deterministic reindexing argument in <a href="/tag/IHJ3/">IHJ3</a> also works on an arbitrary group: define a nonnegative sum as the supremum of its finite subsums, and inversion preserves that collection of subsums. Countability enters the following random version when exchanging the integral and the vertex sums.</p>

<a id="tag-X5NY" data-assertion="theorem" data-title="Mass transport for an arbitrary measure and a measure-preserving family"></a>
<p>Let $\Gamma$ be a countable group with identity $o$, let $(\Omega,\mathcal F,\mu)$ be a measure space, and for each $g\in\Gamma$ let $T_g:\Omega\to\Omega$ be measurable with $(T_g)_*\mu=\mu$. Suppose $t:\Omega\times\Gamma\times\Gamma\to[0,\infty]$ is measurable in $\omega$ for each pair $x,y$ and satisfies</p>
<div class="math-display">$$t(T_g\omega,gx,gy)=t(\omega,x,y)\qquad(\omega\in\Omega,\ g,x,y\in\Gamma).$$</div>
<p>Then</p>
<div class="math-display">$$\int\sum_y t(\omega,o,y)\,d\mu(\omega)
=\int\sum_x t(\omega,x,o)\,d\mu(\omega).$$</div>
<p>The measure need not be finite or s-finite. No identity or composition law for the maps $T_g$ is required beyond the displayed covariance and preservation assumptions.</p>
<p><em>Proof.</em> Set $F(x,y)=\int t(\omega,x,y)\,d\mu(\omega)$. Preservation of $\mu$ and the assumed covariance give</p>
<div class="math-display">$$F(gx,gy)=\int t(T_g\omega,gx,gy)\,d\mu(\omega)=F(x,y).$$</div>
<p>Reindex the deterministic nonnegative sums by inversion, as above. Countable additivity of the nonnegative integral then gives</p>
<div class="math-display">$$\int\sum_y t(\omega,o,y)\,d\mu
=\sum_y F(o,y)=\sum_x F(x,o)
=\int\sum_x t(\omega,x,o)\,d\mu.$$</div>
<p>Measurability of each summand justifies these countable interchanges; no subtraction of infinities occurs. An ordinary measure-preserving group action is a special case. The additive notation gives the same result, with $o=0$ and reindexing by $x\mapsto-x$.</p>
<p>For the full bond configuration law, a sufficient hypothesis is $q_{\{gx,gy\}}=q_{\{x,y\}}$ for every $g,x,y$, including $x=y$. Left multiplication induces a bijection of unordered pairs, with inverse induced by $g^{-1}$; its image map on configurations is measurable and preserves the product law by the relabelling identity. Apply the theorem to that map. The stronger requirement on diagonal coordinates is needed when a transport can read those coordinates. For a transport determined by the simple open graph, the off-diagonal version already explained under <a href="#section-random">random transports</a> suffices.</p>
<p>On $\mathbb Z$, sending one unit from $x$ to $x+1$ gives outgoing and incoming mass one. If this transport is deterministic on a measure space of total mass two, both integrals equal two; probability normalization is not needed. Infinite values are also allowed. The <a href="/coverage/sources/perclib-caed44f-probability/">new-source inventory</a> records both multiplicative statements and their generated additive versions, without treating the finite-cluster applications above as exports of that module.</p>
