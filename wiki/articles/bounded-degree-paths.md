---
{
  "id": "bounded-degree-paths",
  "title": "The bounded-degree path criterion",
  "subtitle": "Exclude immediate backtracking before summing paths",
  "kind": "theorem",
  "category": "General theory",
  "summary": "Counting simple paths improves the uniform-degree small-parameter criterion from Delta p below one to (Delta minus one) p below one. The same count bounds susceptibility and includes degrees zero and one.",
  "context": ["A countable simple host graph $G$, with at most $\\Delta$ neighbours at each vertex, where $\\Delta\\in\\mathbb N$.", "Independent bond probabilities $q_e\\leq p\\in[0,1]$ on host edges, and zero on other non-loop pairs.", "Diagonal coordinates are unrestricted; paths and clusters belong to the simple open graph."],
  "related": ["subcritical-bound", "connectivity", "forest-connections", "susceptibility", "binary-tree-percolation"],
  "sourceIds": ["perclib-bounded-degree", "hutchcroft-book", "perclib-self-avoiding-chi", "perclib-self-avoiding-decay", "perclib-tree-counting", "perclib-boundary-forest-associations"],
  "aliases": ["self-avoiding path", "maximum degree", "nonbacktracking", "path criterion"],
  "prototypeUses": []
}
---

## Count simple paths {#section-count}

<a id="tag-8WML" data-assertion="theorem" data-title="Bounded-degree simple-path count and opening probability"></a>
<p>Put $b=\max\{\Delta-1,0\}$. For every root $x$ and integer $n\geq1$, the number of oriented vertex-simple host paths of length $n$ starting at $x$ is at most $\Delta b^{n-1}$. Consequently,</p>
<div class="math-display">$$\mathbb P_q(\text{there is a simple open path of length }n\text{ from }x)\leq\Delta b^{n-1}p^n=\Delta p\,(bp)^{n-1}.$$</div>
<p>As usual an empty product is one, so the formula includes $n=1$, $b=0$ and $p=0$.</p>
<p><em>Proof.</em> There are at most $\Delta$ choices for the first step. After that, a simple path cannot return immediately to its preceding vertex, leaving at most $\Delta-1$ choices. Avoiding all other previously visited vertices only decreases this number. If $\Delta=0$ there is no first step, and if $\Delta=1$ there is no second step. This proves the count in every case. Each simple path has distinct edges, so independence makes its opening probability the product of its edge probabilities, at most $p^n$. A union bound over the finitely many paths finishes the proof.</p>
<p>The count uses nonbacktracking as an upper bound on simple paths. It does not treat repeated traversals of an edge as independent trials, and it does not require that the host be a tree.</p>

<p>The deterministic path count needs no countability of the vertex set. It constructs a finite family of continuation lists, and the list after the root determines both a path and its endpoint. The fixed-length open-host-path event is consequently a finite union of cylinder events even in an uncountable ambient graph. Its probability bound needs only the edge-probability upper bound on the host; off-host probabilities play no role until one uses host paths to control the full open cluster.</p>

<p>There is also a direct route from these path estimates to nonpercolation. In any locally finite graph, the set of vertices reachable from a fixed root by walks of length at most $n$ is finite: at radius zero it is a singleton, and each further radius is contained in that singleton together with the finitely many corresponding smaller balls around its neighbours. An infinite cluster in a subgraph of this host therefore reaches outside that finite set. Take a simple path to such a vertex and truncate it to obtain a simple open path of any prescribed finite length. Under the host-containment event, the probability of an infinite cluster is thus bounded by $\Delta p\,(bp)^{n-1}$ for every $n\geq1$, which tends to zero if $bp&lt;1$. Local finiteness matters for the deterministic implication: an infinite star has an infinite cluster when all its edges are open, but no simple path of length three.</p>

## Sum over lengths {#section-susceptibility}

<a id="tag-YP44" data-assertion="corollary" data-title="Susceptibility and nonpercolation under the bounded-degree criterion"></a>
<p>Under the same assumptions, if $r=bp&lt;1$, then for every root $x$,</p>
<div class="math-display">$$\chi_q(x)\leq1+\frac{\Delta p}{1-r}.$$</div>
<p>With probability one, all open clusters are finite. For $\Delta\geq1$ the criterion is $(\Delta-1)p&lt;1$. For $\Delta=0$ it holds at every $p$ and gives $\chi_q(x)=1$; for $\Delta=1$ it gives $\chi_q(x)\leq1+p$ even at $p=1$.</p>
<p><em>Proof.</em> Almost surely every open non-loop edge belongs to the host: there are only countably many zero-probability off-host coordinates. On that event a connection from $x$ to another vertex has a simple host path as a witness. Sum the path union bound over endpoints and lengths. Every oriented path from $x$ has exactly one endpoint, so</p>
<div class="math-display">$$\chi_q(x)=\sum_y\mathbb P_q(x\leftrightarrow y)\leq1+\sum_{n\geq1}\Delta p\,r^{n-1}=1+\frac{\Delta p}{1-r}.$$</div>
<p>The root contributes the initial one. All sums are nonnegative, so their rearrangement needs no prior finiteness assumption. Finite expected extended cluster volume excludes an infinite cluster at a fixed root. Countability of the vertex set makes this conclusion simultaneous over all roots.</p>
<p>For $\Delta\geq2$, a homogeneous $\Delta$-regular tree attains the susceptibility bound when $r&lt;1$: it has exactly $\Delta(\Delta-1)^{n-1}$ vertices at distance $n\geq1$, each reached along its unique path with probability $p^n$. When $r\geq1$, the same series diverges. Infinite susceptibility alone does not imply an infinite cluster, so this calculation makes no assertion about percolation at the boundary $r=1$.</p>

## Comparison with a row bound {#section-comparison}

<p>The uniform row estimate gives $\sum_yq_{xy}\leq\Delta p$, so its direct geometric criterion requires $\Delta p&lt;1$. The path count improves this to $(\Delta-1)p&lt;1$ when $\Delta\geq1$ by removing the immediate reversal at each later step. The <a href="/tag/53Z9/">row-sum theorem</a> is more flexible: it also treats infinitely many possible neighbours when their probabilities have a summable uniform row. A degree bound is a different hypothesis.</p>
<p>For nearest-neighbour bonds on $\mathbb Z^d$, $d\geq1$, the neighbours of a vertex are its $2d$ distinct translates by the positive and negative coordinate vectors. Thus the criterion gives no infinite cluster when $(2d-1)p&lt;1$. The inspected library's lattice corollary takes the degree estimate as an explicit input; the elementary count just given supplies the mathematical reason for that input.</p>

<p>This proves the lower-bound mechanism for non-triviality. A planar upper-bound argument is separate and is not covered here.</p>


## Retaining the distance restriction {#section-distance-tail}

<a id="tag-UOHI" data-assertion="theorem" data-title="Bounded-degree two-point decay from a lower bound on path length"></a>
<p>Keep the standing host and profile assumptions, and put $b=\max\{\Delta-1,0\}$ and $r=bp$. Let $x\ne y$, and suppose every host walk from $x$ to $y$ has length at least the integer $D\geq0$. Then</p>
<div class="math-display">$$\tau_q(x,y)\leq\sum_{n\geq\max\{D,1\}}\Delta p\,r^{n-1}.$$</div>
<p>The series is an extended nonnegative sum. If $r&lt;1$, it equals</p>
<div class="math-display">$$\frac{\Delta p\,r^{\max\{D,1\}-1}}{1-r}.$$</div>
<p><em>Proof.</em> On the probability-one host-containment event, any connection has a simple open host path. Since $x\ne y$, its length is positive, and the assumed lower bound makes it at least $D$. The <a href="/tag/8WML/">path count and cylinder bound</a> give total probability at most $\Delta p\,r^{n-1}$ for paths of each length $n\geq1$. Summing over the allowed lengths proves the inequality; for $r&lt;1$ the sum is geometric.</p>
<p>The same indexing explains why susceptibility has the initial one in <a href="/tag/YP44/">YP44</a>. When summing over all endpoints, each simple path is counted once at its own endpoint; one does not sum the unrestricted path-existence bound separately for every endpoint. The source implements this endpoint bookkeeping before rearranging the nonnegative series, and does not assume its finiteness in advance.</p>
<p>The formula includes $D=0$, for which the first permitted path length remains one. It also includes $p=0$ and degrees zero and one, with $0^0=1$. At degree zero there are no positive-length paths. At degree one there are no paths of length two, so the bound is at most $p$ for $D\leq1$ and zero for $D\geq2$, even at $p=1$. If $x$ and $y$ are in different host components, their connection probability is zero by host containment.</p>
<p>For nearest-neighbour bonds on $\mathbb Z^d$, take $\Delta=2d$ and $D=\|y-x\|_1$. Every step changes one coordinate by one, so a walk has length at least this norm. For $d\geq1$, $x\ne y$ and $(2d-1)p&lt;1$, the bound becomes</p>
<div class="math-display">$$\tau_q(x,y)\leq\frac{2dp\,[(2d-1)p]^{\|y-x\|_1-1}}{1-(2d-1)p}.$$</div>
<p>The profile may be inhomogeneous; only its edgewise upper bound by $p$ is used. The source's lattice specialization still takes local finiteness and the degree bound as hypotheses. The separate <a href="/tag/8QCR/">lattice geometry result</a> supplies them mathematically. The <a href="/coverage/sources/perclib-22d8485-path-decay/">path-decay inventory</a> records the arbitrary length-bound theorem, its host-distance specialization and the full susceptibility series. None identifies the actual critical parameter with this sufficient bound.</p>


## A cluster-volume tail from closed walks {#section-volume-tail}

<a id="tag-TEYS" data-assertion="theorem" data-title="A closed-walk encoding bounds the cluster-volume tail"></a>
<p>Under the standing countable-host and profile assumptions, put $r=\Delta^2p$. For every root $x$ and integer $n\geq0$,</p>
<div class="math-display">$$\mathbb P_q(|K_x|\geq n+1)\leq r^n.$$</div>
<p>In particular, if $r&lt;1$, then $\chi_q(x)\leq(1-r)^{-1}$. The volume bound uses a stronger small-parameter condition than the earlier simple-path susceptibility estimate, but gives an exponential tail for the whole cluster.</p>
<p><em>Proof.</em> Work on the probability-one event that every open non-loop edge belongs to the host. If $|K_x|\geq n+1$, grow an open tree from $x$ by adding one new vertex at a time until it has $n$ edges. At each stage before the last, a path to a cluster vertex outside the current tree has an edge leaving it; adjoining that edge and its outside endpoint preserves the tree. Traversing each tree edge outwards and back gives a closed open host walk from $x$ of length $2n$, visiting $n+1$ vertices.</p>
<p>There are at most $\Delta^{2n}$ host walks of this length starting at $x$, since each step has at most $\Delta$ choices. A walk visiting $n+1$ vertices uses at least $n$ distinct edges: each vertex first visited after $x$ is reached along an edge not previously traversed. For a fixed walk, independence applies to its distinct edges, so its opening probability is at most $p^m\leq p^n$, where $m\geq n$ is their number. The union bound over the eligible closed walks gives $\Delta^{2n}p^n=r^n$. Summing the positive-index volume tails gives the susceptibility bound.</p>
<p>The case $n=0$ is the length-zero walk and gives $1\leq1$, with $0^0=1$. If $p=0$ or $\Delta=0$, every cluster is a singleton almost surely. For other parameters the tail inequality still holds, but when $r\geq1$ it gives no decay. On nearest-neighbour $\mathbb Z^d$, $d\geq1$, it gives the explicit volume tail $(4d^2p)^n$ for $|K_x|\geq n+1$.</p>
<p>A further consequence is an exponential-moment bound. If $r&lt;1$ and $t\geq0$ satisfy $re^t&lt;1$, then the cluster is finite almost surely and</p>
<div class="math-display">$$\mathbb E_q e^{t(|K_x|-1)}\leq\frac{1-r}{1-re^t}.$$</div>
<p>For the finite nonnegative integer $N=|K_x|-1$, the identity $e^{tN}=1+(e^t-1)\sum_{j=1}^N e^{t(j-1)}$ and nonnegative summation give the bound, using $\mathbb P(N\geq j)\leq r^j$. It includes $t=0$ and $r=0$. The <a href="/sources/perclib-tree-counting/">source module</a> exports the tail and susceptibility inequalities; this exponential-moment formula is a deduction proved here. Its walk construction uses repeated two-step detours, and its cylinder calculation likewise counts each distinct edge once.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-core-models/">source inventory</a> records all eight contracts and separates these volume estimates from the stronger simple-path susceptibility criterion.</p>
