---
{
  "id": "global-connectivity",
  "title": "Global connectivity and local finiteness",
  "subtitle": "Whole-graph events and finite-radius neighbourhoods",
  "kind": "concept",
  "category": "Foundations",
  "summary": "Pointwise finite probability rows give finite intrinsic balls. Whole-graph connection events admit spanning, Harris and isolation bounds, with empty and singleton cases kept explicit.",
  "context": [
    "A simple graph obtained from open unordered pair coordinates; diagonal coordinates do not create edges.",
    "Deterministic graph statements allow arbitrary vertex sets. Countability is specified for measurable and simultaneous almost-sure conclusions.",
    "Probability bounds use the Bernoulli product law; finite products are distinguished from countable events."
  ],
  "related": [
    "connectivity",
    "open-degree-laws",
    "intrinsic-geometry",
    "closed-separators",
    "harris-inequality"
  ],
  "sourceIds": [
    "perclib-local-finiteness",
    "perclib-global-connectivity"
  ],
  "aliases": [
    "global connectivity",
    "preconnected graph",
    "local finiteness",
    "finite intrinsic balls",
    "spanning certificate",
    "isolated vertex"
  ],
  "prototypeUses": [
    "connectivity"
  ]
}
---

## Local finiteness and intrinsic balls {#section-local-finiteness}

<a id="tag-7R5Q" data-assertion="proposition" data-title="Finite neighbour sets give finite intrinsic balls"></a>
<p>Let $G$ be a simple graph on an arbitrary vertex set, and suppose every neighbour set $N_G(v)$ is finite. For every vertex $v$ and integer $r\geq0$, the set of vertices reachable from $v$ by a walk of length at most $r$ is finite. Equivalently, the closed intrinsic ball</p>
<div class="math-display">$$B_G(v,r)=\{w:d_G(v,w)\leq r\}$$</div>
<p>is finite, where $d_G$ is the <a href="/tag/8W1Q/">extended graph distance</a>, equal to infinity between disconnected vertices. The open ball $\{w:d_G(v,w)&lt;r\}$ is finite as well; at $r=0$ it is empty, whereas the closed ball is $\{v\}$.</p>
<p>Consequently, for Bernoulli bonds on countable $V$, the conditions</p>
<div class="math-display">$$\sum_{w\ne v}q_{vw}&lt;\infty\qquad\text{for every }v\in V$$</div>
<p>give one probability-one event on which every open neighbour set and every finite-radius intrinsic ball is finite. The row sums need not be uniformly bounded or less than one. Diagonal probabilities are unrestricted.</p>
<p><em>Proof.</em> The deterministic assertion follows by induction from</p>
<div class="math-display">$$B_G(v,0)=\{v\},\qquad
B_G(v,r+1)=\{v\}\cup\bigcup_{w\in N_G(v)}B_G(w,r).$$</div>
<p>The right side is a finite union of finite sets. For the random graph, the <a href="/tag/SZLN/">expected degree identity</a> gives $\mathbb E\deg_\omega(v)=\sum_{w\ne v}q_{vw}&lt;\infty$, hence finite degree almost surely at each vertex. Intersect these probability-one events over countably many vertices and apply the deterministic assertion on their intersection.</p>
<p>Local finiteness does not imply finite clusters: all-open nearest-neighbour percolation on $\mathbb Z$ has degree two and an infinite cluster. It also does not make the possible long-range host locally finite. A finite random cluster can still have infinitely many potentially open boundary coordinates, as explained in the <a href="/tag/NBY2/">closed-certificate distinction</a>.</p>

## Events concerning the whole graph {#section-global-events}

<a id="tag-POEO" data-assertion="proposition" data-title="Global connection and cluster-finiteness events"></a>
<p>For any vertex set, write</p>
<div class="math-display">$$\mathcal C=\{\omega:x\leftrightarrow y\text{ for every }x,y\in V\},\qquad
\mathcal C^+=\mathcal C\cap\{\omega:V\ne\varnothing\}.$$</div>
<p>Thus $\mathcal C$ is the all-pairs connection event, while $\mathcal C^+$ also requires a nonempty graph. Both are increasing. On countable $V$ they are measurable, as are</p>
<div class="math-display">$$\mathcal F=\{\omega:|K(x)|&lt;\infty\text{ for every }x\in V\},\qquad
\mathcal F_n=\{\omega:|K(x)|\leq n\text{ for every }x\in V\},$$</div>
<p>for $n\in\mathbb N\cup\{\infty\}$. The events $\mathcal F$ and $\mathcal F_n$ are decreasing. Here $\mathcal F$ permits different finite sizes for different clusters; it does not require a common finite bound.</p>
<p><em>Proof.</em> The event $\mathcal C$ is $\bigcap_{x\in V}\bigcap_{y\in V}\{x\leftrightarrow y\}$. On countable vertices this is a countable intersection of <a href="/tag/7QJG/">measurable connection events</a>. Nonemptiness of $V$ is deterministic, so adding it preserves measurability. The <a href="/tag/5SII/">measurability of cluster volume</a> likewise gives the two cluster-size events by countable intersection. Adding open bonds preserves connections and enlarges every cluster, proving the stated monotonicities without countability.</p>
<p>When $V$ is empty, $\mathcal C$, $\mathcal F$ and every $\mathcal F_n$ are the whole configuration space, but $\mathcal C^+$ is empty. On a singleton, both connection events are certain, independently of the diagonal coordinate. For nonempty $V$, $\mathcal F_0$ is empty; $\mathcal F_\infty$ is always the whole space and does not assert cluster finiteness.</p>

## Bounds for global connection {#section-global-bounds}

<a id="tag-JSS9" data-assertion="proposition" data-title="Spanning, Harris and isolation bounds for global connection"></a>
<p>Under the Bernoulli law, a finite set $T$ of pair coordinates whose associated simple graph connects every pair of vertices gives</p>
<div class="math-display">$$\mathbb P_q(\mathcal C)\geq\prod_{e\in T}q_e.$$</div>
<p>On a finite vertex set, a chosen root $x$ also gives</p>
<div class="math-display">$$\mathbb P_q(\mathcal C)\geq\prod_{y\in V\setminus\{x\}}\tau_q(x,y).$$</div>
<p>On a countable vertex set with at least two vertices, every root $x$ gives the upper bound</p>
<div class="math-display">$$\mathbb P_q(\mathcal C)\leq1-\mathbb P_q(x\text{ is isolated}).$$</div>
<p>For finite $V$ this becomes</p>
<div class="math-display">$$\mathbb P_q(\mathcal C)\leq1-\prod_{y\ne x}(1-q_{xy}).$$</div>
<p><em>Proof.</em> Opening all pairs of $T$ connects every pair of vertices. The corresponding finite cylinder has probability $\prod_{e\in T}q_e$, proving the first inequality. Its hypothesis already forces $V$ to be finite: if a root exists, every other vertex is an endpoint of an edge of $T$; the empty case is immediate. Thus no ambient countability assumption is needed for this bound. Diagonal pairs may remain in $T$, but they add no connections and can only weaken the lower bound.</p>
<p>For a fixed root, connection to every other vertex is equivalent to $\mathcal C$: concatenate a path to the root with a path from it. In finite volume the connection events are measurable and increasing, so iterating <a href="/tag/X5SS/">Harris's inequality</a> gives the second lower bound. On a singleton the empty product is one, as it should be.</p>
<p>If another vertex exists, a path from $x$ to that vertex must start with an open edge incident to $x$. Hence global connection excludes isolation. Isolation is the countable intersection of the events that each non-diagonal incident pair is closed, so it is measurable. Taking complements proves the upper bound, and the <a href="/tag/UNJ6/">isolation product</a> gives its finite form. The size assumption is necessary: a singleton graph is connected and its vertex is isolated.</p>
<p>The pinned <a href="/sources/perclib-local-finiteness/">local-finiteness</a> and <a href="/sources/perclib-global-connectivity/">global-connectivity</a> modules supply these source contracts. Their graph-ball convention is the strict inequality in extended distance, covered by the open-ball conclusion above. The finite-neighbour argument and the global event identities are deterministic; countability enters their measurable and simultaneous almost-sure consequences.</p>
