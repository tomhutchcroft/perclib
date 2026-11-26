---
{
  "id": "connection-paths",
  "title": "Connection bounds from specified paths",
  "subtitle": "Distinct bond coordinates and independent alternatives",
  "kind": "method",
  "category": "General theory",
  "summary": "A specified open walk gives a product lower bound for connection. Edge-disjoint alternatives combine by multiplying their failure probabilities; a finite parallel family of two-edge routes gives an exact formula. Pivotal pairs for a realized connection lie on every open path and are bounded in number by the open-graph distance.",
  "context": [
    "Independent unordered pair coordinates with probabilities $q_e\\in[0,1]$; loops do not contribute to graph paths.",
    "Prescribed walks and the family of alternatives are finite and deterministic.",
    "The lower bounds hold on arbitrary vertex sets as outer-measure inequalities. On countable vertices connection events are measurable."
  ],
  "related": [
    "connectivity",
    "forest-connections",
    "finite-transcripts",
    "closed-separators",
    "product-model"
  ],
  "sourceIds": [
    "perclib-path-lower-bounds",
    "perclib-connection-pivotal"
  ],
  "aliases": [
    "path lower bound",
    "parallel paths",
    "edge-disjoint paths",
    "series parallel",
    "connection reliability"
  ],
  "prototypeUses": [
    "connectivity"
  ]
}
---

## A specified walk {#section-walk}

<p>Let $P$ be a finite walk from $x$ to $y$ with successive vertices distinct, and let $E(P)$ be the set of distinct unordered bonds it traverses. Define</p>
<div class="math-display">$$w(P)=\prod_{e\in E(P)}q_e.$$</div>
<p>A walk may revisit vertices or bonds. Each bond is a single random coordinate, so its probability appears only once in this product. Let $\tau^*(x,y)$ denote the product outer measure of the connection event. On a countable vertex set this is the ordinary two-point probability $\tau(x,y)$, by <a href="/tag/7QJG/">connection measurability</a>.</p>

<a id="tag-9IPM" data-assertion="proposition" data-title="A specified finite walk gives a connection lower bound"></a>
<p>On any vertex set,</p>
<div class="math-display">$$\mathbb P(E(P)\text{ is open})=w(P)\leq\tau^*(x,y).$$</div>
<p><em>Proof.</em> The all-open event is a measurable finite cylinder. Independence gives its product probability. On this event the walk connects $x$ to $y$, so monotonicity of outer measure gives the inequality. Neither step requires measurability of the larger connection event.</p>
<p>The length-zero walk has no bonds and weight one, recovering reflexive connection. If a walk uses just one bond, traversed several times, its all-open event still has probability $q_e$, not a power of $q_e$. For a simple path of length $m$ with constant edge probability $p$, the weight is $p^m$. On a <a href="/articles/forest-connections/#section-path">forest</a> the unique path gives equality; in a general graph other routes can make the connection probability larger.</p>

## Independent alternatives {#section-alternatives}

<a id="tag-8V8H" data-assertion="theorem" data-title="Connection lower bound from finitely many edge-disjoint walks"></a>
<p>Let $P_1,\ldots,P_k$ be finite walks from $x$ to $y$ whose bond sets $E(P_i)$ are pairwise disjoint. Then</p>
<div class="math-display">$$1-\prod_{i=1}^k\bigl(1-w(P_i)\bigr)\leq\tau^*(x,y).$$</div>
<p>The walks may share vertices. The disjointness required here is between their bond coordinates.</p>
<p><em>Proof.</em> Put $A_i=\{E(P_i)\text{ is open}\}$. Each $A_i$ is measurable and determined by its bond set. The <a href="/tag/DYU8/">independence of disjoint coordinate blocks</a> therefore applies to their complements and gives</p>
<div class="math-display">$$\mathbb P\Bigl(\bigcup_{i=1}^k A_i\Bigr)=1-\mathbb P\Bigl(\bigcap_{i=1}^k A_i^c\Bigr)=1-\prod_{i=1}^k\bigl(1-\mathbb P(A_i)\bigr).$$</div>
<p>Substitute $\mathbb P(A_i)=w(P_i)$ and use the inclusion of this union in the connection event. The complement identity holds more generally for a finite family of measurable events determined by pairwise disjoint deterministic coordinate sets, even when those sets are infinite.</p>
<p>For an empty family the lower bound is zero. A length-zero member makes the bound one, as it should when $x=y$. For a single member it recovers the specified-walk bound. Shared bonds cannot generally be allowed: if two routes both require the same bond of probability $p\in(0,1)$ and all their other bonds are certain, both route events have probability $p$ but their union also has probability $p$, less than $1-(1-p)^2$.</p>
<p>This argument concerns fixed routes chosen before the configuration is sampled. Exploring routes and then conditioning on the resulting random bond sets does not automatically preserve the product law.</p>

## An exact parallel family {#section-exact-parallel}

<a id="tag-YPNG" data-assertion="proposition" data-title="Exact connection through a finite family of two-edge routes"></a>
<p>On the finite vertex set $\{x,y,z_1,\ldots,z_k\}$, with all vertices distinct, suppose the only pairs of distinct vertices with positive opening probability are $\{x,z_i\}$ and $\{z_i,y\}$. Write their respective probabilities as $a_i,b_i\in[0,1]$. Then</p>
<div class="math-display">$$\tau(x,y)=1-\prod_{i=1}^k(1-a_i b_i).$$</div>
<p>In particular, if all these probabilities equal $t$, then $\tau(x,y)=1-(1-t^2)^k$. Diagonal probabilities are arbitrary.</p>
<p><em>Proof.</em> Almost surely every open non-loop bond belongs to the specified finite host. The two-edge routes have disjoint bond sets, so the preceding product is the probability that at least one route is open. It remains to show that a connection cannot occur without such a route.</p>
<p>Suppose no route is open and put $S=\{x\}\cup\{z_i:\{x,z_i\}\text{ is open}\}$. Every open neighbour of $x$ belongs to $S$. For a middle vertex in $S$, its bond to $y$ is closed, and its only other possible neighbour is $x$. Thus $S$ is closed under open adjacency. Induction along a finite walk shows that every vertex reachable from $x$ belongs to $S$. Since $y\notin S$, there is no connection. This proves the event equivalence and hence the formula.</p>
<p>When $k=0$ the endpoints are isolated and the formula is zero. For $k=1$ it is the two-bond product; for $k\geq1$ and $t=1$ it is one. With two middle vertices and $t=1/2$, it gives $7/16$.</p>
<p>The <a href="/sources/perclib-path-lower-bounds/">pinned source module</a> proves the walk lower bounds on arbitrary vertices and the homogeneous finite example. The heterogeneous probabilities and unrestricted diagonal parameters in the last proposition are elementary extensions. The source's elementary closed-set reachability lemma is the induction used in its proof. No new compiled tag association or reviewed correspondence follows from this exposition.</p>


## Pairs pivotal for a connection {#section-pivotal-pairs}

<p>The following statements are deterministic and require no countability or local finiteness. For an unordered pair $e$, put $\omega^{-e}=\omega\setminus\{e\}$. The pair is pivotal for $x\leftrightarrow y$ when adding it makes the connection hold and deleting it makes the connection fail.</p>

<a id="tag-61PY" data-assertion="theorem" data-title="Connection pivotality joins the two deleted-configuration clusters and is bounded by open distance"></a>
<p>For $e=\{a,b\}$ with $a\ne b$, pivotality is equivalent to</p>
<div class="math-display">$$x\not\leftrightarrow y\text{ in }\omega^{-e},\qquad
\bigl(x\leftrightarrow a,\ y\leftrightarrow b\bigr)\ \text{or}\ \bigl(x\leftrightarrow b,\ y\leftrightarrow a\bigr)\text{ in }\omega^{-e}.$$</div>
<p>Diagonal pairs are never pivotal. If $x\leftrightarrow y$ already holds in $\omega$, every pivotal pair is open and lies on every open walk between the endpoints. In particular,</p>
<div class="math-display">$$\#\{e:e\text{ is pivotal for }x\leftrightarrow y\text{ in }\omega\}
\leq d_\omega(x,y),$$</div>
<p>where $d_\omega$ is distance in the open graph and the displayed bound is asserted on the connection event.</p>
<p><em>Proof.</em> Take a simple path from $x$ to $y$ after adding $e$. If it avoids $e$, it is already a path in $\omega^{-e}$. Otherwise it uses $e$ once, in one of its two orientations; the prefix and suffix lie in $\omega^{-e}$ and give the corresponding pair of endpoint connections. Conversely, either pair of endpoint connections can be concatenated with $e$ to join $x$ to $y$. Requiring the deleted connection to fail gives the characterization. A loop changes no adjacency and cannot create a connection.</p>
<p>Now suppose the connection is realized. If any open walk avoided a pivotal pair, that walk would survive its deletion, a contradiction. Thus every pivotal pair belongs to every such walk, and in particular is open. Choose a shortest open path: its distinct pairs contain all the pivotal pairs, proving the bound. For $x=y$, the length-zero path shows that the pivotal set is empty.</p>
<p>The distance in this bound cannot be replaced by the distance in a larger host graph: a closed shortcut may make the host distance one while every edge of a long open path is pivotal. Nor is the connection hypothesis dispensable. If $x$ and $y$ lie in two infinite connected open components with all cross pairs closed, every pair joining those components is pivotal, so the state-independent pivotal set can be infinite before connection occurs.</p>
<p>For an internal connection in a vertex domain $S$, a pair with an endpoint outside $S$ is never pivotal. For an internal non-diagonal pair, the same characterization holds with all four endpoint connections taken inside $S$. Indeed, restriction commutes with inserting or deleting an internal pair; a noninternal pair leaves the induced graph unchanged. The path-count bound likewise uses distance in the induced open graph on the event of an internal connection. No boundary pair or diagonal coordinate contributes merely because it belongs to the ambient product space.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-pivotal-russo/">pivotal and Russo inventory</a> separates these deterministic path facts from the probability and differentiation identities.</p>
