---
{
  "id": "forest-connections",
  "title": "Percolation on a forest",
  "subtitle": "Exact path weights, the ray and the integer line",
  "kind": "model",
  "category": "Models",
  "summary": "Unique paths turn connection probabilities into finite products and susceptibility into an exact sum of path weights. The ray gives formulas at every parameter, including both endpoints. The integer line has critical bond probability one but infinite critical intensity for a finite nearest-neighbour rate.",
  "context": [
    "Independent bond percolation on a countable vertex set $V$, with probabilities $q_e\\in[0,1]$.",
    "A deterministic simple graph $G$ contains the open graph almost surely and is acyclic.",
    "Diagonal bond probabilities are unrestricted and do not affect the open graph."
  ],
  "related": [
    "connectivity",
    "susceptibility",
    "subcritical-bound",
    "binary-tree-percolation"
  ],
  "sourceIds": ["perclib-forest-interface", "perclib-line", "perclib-forest-branching", "perclib-boundary-forest-associations"],
  "aliases": [
    "forest",
    "acyclic",
    "unique path",
    "ray",
    "geometric susceptibility",
    "integer line",
    "nearest-neighbour percolation",
    "infinite critical intensity"
  ],
  "prototypeUses": []
}
---

## The supporting forest {#section-support}

<a id="tag-XHFN" data-assertion="proposition" data-title="Almost-sure containment in the positive-probability support"></a><p>Let $G_q$ have edge $\{u,v\}$ precisely when $u\neq v$ and $q_{uv}&gt;0$. Almost surely, every open edge lies in $G_q$. Consequently, if $G_q$ is acyclic, it can serve as the deterministic forest $G$ in this article.</p><p><em>Proof.</em> Each edge of probability zero is closed almost surely. There are only countably many unordered pairs, so almost surely they are all closed simultaneously. Diagonal pairs are discarded when forming the graph. The same countable-null-union argument also shows that the entire configuration lies in the set of positive-probability coordinates almost surely, including its diagonal coordinates.</p>

## Exact connection probabilities {#section-path}

<a id="tag-8KVE" data-assertion="theorem" data-title="Unique-path formula and forest susceptibility"></a><p>If $x$ and $y$ lie in the same component of $G$, let $P_G(x,y)$ denote their unique simple path. Then</p><div class="math-display">$$\tau(x,y)=\prod_{e\in P_G(x,y)}q_e.$$</div><p>If they lie in different components, $\tau(x,y)=0$. In particular,</p><div class="math-display">$$\chi(x)=\sum_{y\text{ in the component of }x}\prod_{e\in P_G(x,y)}q_e,$$</div><p>as an extended nonnegative sum. The path from $x$ to itself is empty, so its product is one and the root always contributes one to $\chi(x)$.</p><p><em>Proof.</em> Work on the probability-one event that the open graph is contained in $G$. Opening every edge of $P_G(x,y)$ connects its endpoints. Conversely, any open connection contains a simple path, and acyclicity forces that path to be $P_G(x,y)$. Thus the connection event agrees almost surely with the finite cylinder specifying that all its path edges are open. Independence gives the product. Disconnected host components cannot be joined by an open path. Finally, summing the connection probabilities gives $\mathbb E|K(x)|$, by summing the indicators of membership in the root cluster.</p>

<p>The path equivalence in the proof is deterministic and holds on an arbitrary vertex set: if the open graph lies in an acyclic host, a connection between the endpoints of a specified host path occurs exactly when all edges of that path are open. Countability is used for the probabilistic support and measurability arguments, not for uniqueness of the path. On the ray, the path from $m$ to $n$ with $m\leq n$ is the sequence $m,m+1,\ldots,n$; it has length $n-m$ and every vertex on it is at most $n$.</p>

<p>Almost-sure containment is essential: an additional positive-probability edge can provide a route avoiding the displayed path. Nor should the forest formula be replaced by a sum over walks, which repeat edges and count the same connection many times.</p>

## The nearest-neighbour ray {#section-ray}

<a id="tag-TGL4" data-assertion="proposition" data-title="Exact two-point function and endpoint susceptibility on the ray"></a><p>On $\mathbb N$, give each bond $\{n,n+1\}$ probability $t\in[0,1]$ and every other non-loop bond probability zero. Then, for all $m,n\in\mathbb N$,</p><div class="math-display">$$\tau(m,n)=t^{|m-n|},\qquad \chi(0)=\sum_{n=0}^{\infty}t^n=\begin{cases}(1-t)^{-1},&amp;0\leq t&lt;1,\\\infty,&amp;t=1.\end{cases}$$</div><p>Here $t^0=1$, including at $t=0$. The endpoint susceptibility is finite exactly when $t&lt;1$.</p><p><em>Proof.</em> The ray is an almost-sure host. Its unique path between $m$ and $n$ has $|m-n|$ edges, so the path formula gives the two-point function. At the endpoint there is one vertex at every distance, and the susceptibility is the geometric series above. At $t=1$ every summand is one.</p>

<p>The <a href="#/binary-tree-percolation">rooted binary tree</a> shows how the same path calculation changes when the number of vertices at distance $n$ grows exponentially. On the ray it is one; on that tree it is $2^n$, so the corresponding susceptibility series is $\sum_n(2t)^n$.</p>


## The integer line {#section-integer-line}

<a id="tag-BP7B" data-assertion="theorem" data-title="Exact connection, susceptibility and percolation laws on the integer line"></a>
<p>On $\mathbb Z$, give each nearest-neighbour pair probability $p\in[0,1]$, every other non-diagonal pair probability zero, and diagonal pairs arbitrary probabilities. Then</p>
<div class="math-display">$$\tau_p(a,b)=p^{|b-a|},\qquad
\chi_p(a)=\begin{cases}\dfrac{1+p}{1-p},&amp;0\leq p&lt;1,\\[4pt]\infty,&amp;p=1.\end{cases}$$</div>
<p>For $p&lt;1$, almost surely every cluster is finite. At $p=1$, almost surely every root cluster is all of $\mathbb Z$. Thus both root and global percolation probabilities are zero for $p&lt;1$ and one at $p=1$.</p>
<p><em>Proof.</em> The nearest-neighbour line is an almost-sure host by <a href="/tag/XHFN/">positive-probability support</a>. For $a\leq b$, its unique path is $a,a+1,\ldots,b$, of length $b-a$; symmetry covers the other order. The <a href="/tag/8KVE/">forest product formula</a> gives $p^{|b-a|}$, including the empty path and the convention $0^0=1$.</p>
<p>There are two vertices at every positive distance from the root, so</p>
<div class="math-display">$$\chi_p(a)=1+2\sum_{n\geq1}p^n.$$</div>
<p>For $p&lt;1$ this is $(1+p)/(1-p)$. Finite expected cluster size excludes an infinite cluster at each root, and the countable union over roots excludes one anywhere. At $p=1$, all nearest-neighbour bonds are simultaneously open almost surely, by a countable intersection of probability-one events. The entire line is then connected and its susceptibility is infinite.</p>
<p>The <a href="/tag/R3I9/">prescribed-cluster formula</a> also gives, for $0\leq p&lt;1$ and $n\geq1$,</p>
<div class="math-display">$$\mathbb P_p(|K(0)|=n)=n(1-p)^2p^{n-1}.$$</div>
<p>Indeed, a finite root cluster is an interval. There are exactly $n$ intervals of size $n$ containing zero, and each requires its $n-1$ internal bonds open and its two boundary bonds closed. Their cluster events are disjoint. This distributional formula is an additional deduction, not an exported theorem of the line module. It includes the deterministic singleton at $p=0$; at $p=1$ all finite-size probabilities vanish.</p>

## Infinite critical intensity {#section-line-intensity}

<a id="tag-FH1B" data-assertion="corollary" data-title="The unit-rate nearest-neighbour line has infinite root and global critical intensities"></a>
<p>Give each nearest-neighbour pair on $\mathbb Z$ intensity weight one and every other non-diagonal pair weight zero. For finite $\beta\geq0$, use opening probabilities $q_\beta(e)=1-e^{-\beta J_e}$. Then</p>
<div class="math-display">$$\chi_\beta(a)=2e^\beta-1&lt;\infty,\qquad
\mathbb P_\beta(\exists x:\ |K(x)|=\infty)=0.$$</div>
<p>Both the root and global critical intensities are $\infty$, with the convention that the infimum of an empty set of percolating finite intensities is $\infty$. Diagonal weights are unrestricted.</p>
<p><em>Proof.</em> Every finite intensity gives the nearest-neighbour probability $p=1-e^{-\beta}&lt;1$. Substitute this into the preceding susceptibility formula and use simultaneous finiteness of the clusters. No finite parameter belongs to either percolating set, so both threshold infima are infinite.</p>
<p>The critical bond probability is one, while no finite intensity reaches that endpoint. The infinite threshold is therefore not a claim about a probability law at $\beta=\infty$. With finite constant nearest-neighbour weight $\lambda&gt;0$, the same substitution gives $\chi_\beta=2e^{\lambda\beta}-1$ and infinite critical intensities. In particular, the normalized weight $\lambda=1/2$ recovers the line calculation already used in <a href="/tag/MTYL/">the provisional triangle-inequality erratum</a>; that assertion and its source diagnosis are unchanged.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-line/">15-contract inventory</a> records the path, support, endpoint and intensity statements. The finite-cluster size law, explicit exponential susceptibility and general positive-rate specialization are additional deductions from these statements and the prescribed-cluster formula. The older forest and ray records are retained, and all new correspondences await independent review and compiled association.</p>


## Branch vertices and leaves {#section-branch-count}

<p>The following calculation concerns an arbitrary finite forest $T$, with no probability law. Let $c$ be its number of components, $i$ its number of isolated vertices, $L$ its set of degree-one vertices and $B$ its set of vertices of degree at least three.</p>
<a id="tag-4K33" data-assertion="proposition" data-title="Finite-forest degree excess and the bound on branch vertices"></a>
<p>Then</p>
<div class="math-display">$$\sum_{v\in V(T)}(\deg_T(v)-2)=-2c,\qquad
|B|\leq|L|-2(c-i)\leq|L|.$$</div>
<p>In particular, a tree with at least two vertices satisfies $|B|+2\leq|L|$. If a set $A$ of at least two vertices contains every leaf of a finite tree, then $|B|\leq|A|-2$. All subtraction in the degree identity is ordinary signed subtraction.</p>
<p><em>Proof.</em> A finite forest with $n$ vertices and $c$ components has $n-c$ edges. The degree sum is twice the edge count, which proves the first identity. Separate vertices according to degree to obtain</p>
<div class="math-display">$$-2i-|L|+\sum_{v\in B}(\deg_T(v)-2)=-2c,$$</div>
<p>and hence $\sum_{v\in B}(\deg_T(v)-2)=|L|-2(c-i)$. Each summand on the left is at least one. Also $c-i$ is the number of non-singleton components, so it is nonnegative. This gives both inequalities. A nontrivial tree has $c=1$ and $i=0$; replacing its leaf set by the larger set $A$ gives the last bound.</p>
<p>An isolated vertex is not a leaf: it has degree zero and contributes $-2$ to the signed identity. Thus the empty forest has $c=i=0$ and both sides zero, while the singleton tree has $c=i=1$ and no branch vertices or leaves. These cases satisfy the forest inequality but not the nontrivial-tree inequality with its additional two. A path with at least two vertices has two leaves and no branch vertices. A star with $k\geq3$ leaves has one branch vertex of degree $k$, whose excess $k-2$ gives equality in the displayed excess formula.</p>
<p>The source proves the tree identity, preserves vertex degrees when passing to a component, and sums over components. The underlying grouping formula is simply $\sum_v f(v)=\sum_C\sum_{v\in C}f(v)$; it applies to functions into any additive commutative monoid. Its exported forest bound is $|B|\leq|L|$. The stronger correction $2(c-i)$ above is an immediate consequence of the exported signed identity. The <a href="/coverage/sources/perclib-22d8485-forests/">eight-contract inventory</a> also records the tree bound with a prescribed leaf-containing set.</p>

## Scope of the forest probability formulas {#section-forest-source}

<p>The deterministic path equivalence behind <a href="/tag/8KVE/">8KVE</a> holds on arbitrary vertex sets: if the open graph lies in an acyclic host, connection is equivalent to opening its unique simple path. The source's probabilistic path-product and susceptibility formulas assume countable vertices. Countability makes the connection events measurable and makes all zero-probability coordinates closed simultaneously. The separate zero-probability conclusion for vertices disconnected in an almost-sure host requires no countability; it follows directly from the almost-sure containment hypothesis.</p>
<p>The acyclic host may contain bonds with probability zero. Thus the exact product formula includes a zero factor, as well as the empty path with product one. On the ray, the whole nearest-neighbour graph remains an almost-sure host even at parameter zero; it need not equal the positive-probability support. At parameter one the endpoint susceptibility is the divergent geometric sum. Arbitrary diagonal probabilities remain allowed throughout these forest formulas.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-forests/">four-module inventory</a> reconciles these fourteen forest contracts with the host and diagonal-erasure results. The earlier forest, host and diagonal source records remain pinned to their original revision: all three files are byte-identical there and at the newly inspected revision.</p>
