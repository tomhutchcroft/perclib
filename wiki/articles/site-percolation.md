---
{
  "id": "site-percolation",
  "title": "Site percolation",
  "subtitle": "Open vertices, association, and self-avoiding-path bounds",
  "kind": "model",
  "category": "Models",
  "summary": "Site percolation retains vertices independently. Its self-connection probability is the root's open probability, and its cluster is empty when the root is closed. Counting open simple paths gives the degree criterion and the elementary lattice threshold bound.",
  "context": [
    "A fixed simple graph $G=(V,E)$ and a set $\\omega\\subseteq V$ of open vertices.",
    "Under $\\mathbb P_w$, vertex $v$ is open independently with probability $w_v\\in[0,1]$.",
    "Countability is used for the general measurable-event and Harris statements. The locally finite path bounds below hold at each fixed root without global countability."
  ],
  "related": [
    "product-model",
    "connectivity",
    "harris-inequality",
    "criticality",
    "bounded-degree-paths"
  ],
  "sourceIds": [
    "perclib-site-interface",
    "perclib-site-harris",
    "perclib-site-self-avoiding"
  ],
  "aliases": [
    "site model",
    "open vertices",
    "site cluster",
    "site critical probability",
    "site path bound",
    "site degree criterion"
  ],
  "prototypeUses": []
}
---

## Open-vertex connections {#section-definition}

<a id="tag-8FLS" data-assertion="definition" data-title="Site connections and the closed-root convention"></a><p>Write $x\leftrightarrow_{\mathrm s}y$ if there is a finite path in $G$ from $x$ to $y$ whose every vertex is open, including both endpoints. Define $K_{\mathrm s}(x)=\{y:x\leftrightarrow_{\mathrm s}y\}$. The length-zero path is allowed only when $x$ is open. Thus $K_{\mathrm s}(x)=\varnothing$ when $x$ is closed, while an open $x$ belongs to its own cluster.</p><p>Equivalently, retain a graph edge precisely when both endpoints are open, and require the starting vertex to be open before using reachability in that graph. The extra requirement matters: ordinary graph reachability makes every isolated vertex reachable from itself, including a closed vertex. Site clusters partition the open vertices; they do not give a partition of all vertices into nonempty clusters.</p>

<p>These definitions work on any vertex set. Reversing or concatenating open paths proves symmetry and transitivity of site connection. Consequently, connected open roots have the same cluster. If $\omega\subseteq\eta$, every edge retained by $\omega$ is retained by $\eta$, and every site cluster can only grow. Connection to a fixed set $A\subseteq V$ means connection to at least one of its vertices, so this event is increasing as well. An infinite site cluster stays infinite after vertices are opened.</p>

## Basic probabilities {#section-probabilities}

<a id="tag-9R9K" data-assertion="proposition" data-title="Self-connection and adjacent-site connection probabilities"></a><p>Let $\tau_{\mathrm s}(x,y)=\mathbb P_w(x\leftrightarrow_{\mathrm s}y)$. Then</p><div class="math-display">$$\tau_{\mathrm s}(x,x)=w_x,\qquad \tau_{\mathrm s}(x,y)\leq w_xw_y\quad(x\neq y).$$</div><p>If $\{x,y\}$ is an edge of $G$, equality holds in the second formula.</p><p><em>Proof.</em> Self-connection is exactly the event that $x$ is open. A connection between distinct endpoints requires both to be open, whose joint probability is $w_xw_y$ by independence. For adjacent vertices, their common openness also suffices, using the one-edge path.</p><p>In particular, these probabilities differ from bond percolation even on a two-vertex graph. At a homogeneous parameter $p$, the site connection probability is $p^2$, while the bond connection probability is $p$. The bond root also has self-connection probability one.</p>

## Measurability and association {#section-association}

<a id="tag-3YMY" data-assertion="proposition" data-title="Site connection and infinite-cluster events are measurable and increasing"></a><p>On a countable vertex set, each event $\{x\leftrightarrow_{\mathrm s}y\}$ and $\{|K_{\mathrm s}(x)|=\infty\}$ is measurable and increasing in the open-vertex configuration. For any increasing finite exhaustion $F_n\uparrow V$,</p><div class="math-display">$$\{|K_{\mathrm s}(x)|=\infty\}=\bigcap_n\bigcup_{y\notin F_n}\{x\leftrightarrow_{\mathrm s}y\}.$$</div><p><em>Proof.</em> A connection is a countable union of cylinder events, one for each finite path, requiring its vertices to be open. A cluster is infinite precisely when it is not contained in any member of the exhaustion, giving the displayed countable intersection of countable unions. Opening more vertices preserves every open path and can only enlarge the cluster.</p>

<p>The finite-witness description itself needs no countability: a connection is the union over finite vertex lists starting at $x$ and ending at $y$ of the event that the list is an open walk and its starting vertex is open. For any fixed list, its open-walk event is a finite intersection of vertex cylinders, hence measurable in any ambient vertex set. Similarly, a cluster is infinite exactly when it connects to the complement of every finite subset of $V$. Countability is used to turn these unions and intersections into measurable events; it is not needed for the underlying set identities.</p>

<a id="tag-AR5B" data-assertion="proposition" data-title="Site Harris bounds and transfer of an infinite cluster"></a><p>For any two site-connection events, or any two rooted infinite-site-cluster events, their joint probability is at least the product of their probabilities. In particular, writing $\theta_{\mathrm s}(x)=\mathbb P_w(|K_{\mathrm s}(x)|=\infty)$,</p><div class="math-display">$$\tau_{\mathrm s}(x,y)\tau_{\mathrm s}(y,z)\leq\tau_{\mathrm s}(x,z),\qquad \tau_{\mathrm s}(x,y)\theta_{\mathrm s}(x)\leq\theta_{\mathrm s}(y).$$</div><p><em>Proof.</em> Apply the <a href="/tag/X5SS/">Harris inequality</a> to the measurable increasing events just described, now with vertices as the independent coordinates. Two successive site connections imply the connection between their outer endpoints. A connection from $x$ to $y$ also makes their open clusters equal, so an infinite cluster at $x$ is then infinite at $y$. These event containments give the two bounds.</p>

## The lattice threshold convention {#section-threshold}

<a id="tag-8EIH" data-assertion="definition" data-title="Site critical probability on the nearest-neighbour lattice"></a><p>For homogeneous site percolation on the nearest-neighbour graph of $\mathbb Z^d$, $d\geq0$, let</p><div class="math-display">$$\theta_{\mathrm s}(p)=\mathbb P_p(|K_{\mathrm s}(0)|=\infty),\qquad p_{\mathrm c}^{\mathrm s}=\inf\bigl(\{p\in[0,1]:\theta_{\mathrm s}(p)&gt;0\}\cup\{1\}\bigr).$$</div><p>The extra element $1$ makes the set nonempty and places this real-valued threshold in $[0,1]$, even if no parameter percolates. For $d=0$, the graph is a singleton, so $\theta_{\mathrm s}(p)=0$ for every $p$ and this convention gives $p_{\mathrm c}^{\mathrm s}=1$.</p><p>This definition alone says nothing about $\theta_{\mathrm s}(p_{\mathrm c}^{\mathrm s})$. It is also distinct from an extended-valued bond-intensity threshold, which may be infinite.</p>

## Ordered profiles and the threshold {#section-monotonicity}

<a id="tag-M28D" data-assertion="proposition" data-title="Site profile comparison and the two sides of the capped threshold"></a>
<p>On a countable vertex set, let $w_v\leq w'_v$ for every vertex. For every measurable event $A$ increasing in the set of open vertices,</p>
<div class="math-display">$$\mathbb P_w(A)\leq\mathbb P_{w'}(A).$$</div>
<p>In particular, the homogeneous infinite-cluster probability at any root of a fixed graph is nondecreasing in $p$. For the nearest-neighbour lattice threshold defined above and $p\in[0,1]$,</p>
<div class="math-display">$$p&lt;p_{\mathrm c}^{\mathrm s}\ \Longrightarrow\ \theta_{\mathrm s}(p)=0,
\qquad p&gt;p_{\mathrm c}^{\mathrm s}\ \Longrightarrow\ \theta_{\mathrm s}(p)&gt;0.$$</div>
<p><em>Proof.</em> The <a href="/tag/6B9V/">ordered-profile coupling</a>, applied to vertex coordinates, makes the $w$-configuration a subset of the $w'$-configuration almost surely. Increasingness gives the probability comparison. Apply it to the measurable infinite-cluster event for monotonicity.</p>
<p>If $p&lt;p_{\mathrm c}^{\mathrm s}$ and $\theta_{\mathrm s}(p)&gt;0$, then $p$ belongs to the set defining the infimum, a contradiction. Conversely, if $p&gt;p_{\mathrm c}^{\mathrm s}$, the defining set has an element $r&lt;p$. This element cannot be supplied solely by the adjoined endpoint $1$, since $p\leq1$. Hence $\theta_{\mathrm s}(r)&gt;0$, and monotonicity gives $\theta_{\mathrm s}(p)\geq\theta_{\mathrm s}(r)&gt;0$.</p>
<p>No conclusion at $p=p_{\mathrm c}^{\mathrm s}$ follows. On the singleton lattice ($d=0$), the threshold is one and the above-threshold implication has no parameter in $[0,1]$ to which it applies. At the zero profile, every connection probability is zero, including self-connection. On a two-vertex edge at $p=1/2$, the supermultiplicative inequality can be strict: $\tau_{\mathrm s}(x,y)\tau_{\mathrm s}(y,x)=1/16&lt;1/2=\tau_{\mathrm s}(x,x)$.</p>


## Counting open vertex paths {#section-path-counting}

<p>Let $G$ be a simple graph of maximum degree at most $\Delta\in\mathbb N$, and write $b=\max\{\Delta-1,0\}$. Its vertex set may be uncountable. For a fixed root $x$, let $\mathcal P_n(x)$ be the set of simple paths of $n$ edges starting at $x$, and let $E_n(x)$ be the event that at least one of these paths has all its vertices open. The length-zero event is $E_0(x)=\{x\text{ is open}\}$.</p>

<a id="tag-5U4L" data-assertion="theorem" data-title="Site path bounds retain the open-root factor"></a>
<p>If $0\leq w_v\leq p\leq1$ for every vertex, then for every $n\geq1$,</p>
<div class="math-display">$$\mathbb P_w(E_n(x))\leq\sum_{\gamma\in\mathcal P_n(x)}\prod_{v\in\gamma}w_v
\leq w_x\Delta b^{n-1}p^n
\leq\Delta b^{n-1}p^{n+1}.$$</div>
<p>In particular, the source's length-$(n+1)$ form is $\mathbb P_w(E_{n+1}(x))\leq\Delta p^2(bp)^n$ for $n\geq0$. Powers with exponent zero equal one, including $0^0$.</p>
<p><em>Proof.</em> There are at most $\Delta$ choices for the first step and at most $b$ for each subsequent step, since a simple path cannot return immediately along its last edge. This gives $|\mathcal P_n(x)|\leq\Delta b^{n-1}$, as in the <a href="/tag/8WML/">simple-path count</a>. For each such path its $n+1$ vertices are distinct, so independence gives the opening probability $\prod_{v\in\gamma}w_v\leq w_xp^n$. The union bound over the finitely many paths proves the assertion. When $\Delta=0$ there are no positive-length paths; the same formula still holds.</p>
<p>The factor $w_x$ is retained here as an additional refinement of the source's uniform estimate. At length zero the probability is exactly $w_x$, as required by the closed-root convention. The analogous homogeneous bond path requires $n$ open edges and has probability $p^n$; the site path requires $n+1$ open vertices and has probability $p^{n+1}$. No independence between different candidate paths is used.</p>

## Excluding an infinite site cluster {#section-degree-criterion}

<a id="tag-3HEP" data-assertion="theorem" data-title="The site degree criterion holds at each root without global countability"></a>
<p>Under the preceding hypotheses, if $bp&lt;1$, then</p>
<div class="math-display">$$\mathbb P_w\bigl(|K_{\mathrm s}(x)|=\infty\bigr)=0\qquad\text{for every fixed }x.$$</div>
<p>If $V$ is countable, almost surely every site cluster is finite. In real arithmetic the sufficient condition can equivalently be written $(\Delta-1)p&lt;1$, including $\Delta=0$.</p>
<p><em>Proof.</em> Every finite-radius host ball about $x$ is finite. If $K_{\mathrm s}(x)$ is infinite, choose a vertex of this cluster outside the radius-$n$ ball, take a simple open path to it, and retain its first $n+1$ edges. Thus the infinite-cluster event is contained in $E_{n+1}(x)$ for every $n\geq0$. By 5U4L its probability is at most $\Delta p^2(bp)^n$, which tends to zero.</p>
<p>There is no measurability difficulty from an uncountable ambient vertex set. Each $E_n(x)$ is a finite union of vertex cylinders, and</p>
<div class="math-display">$$\{|K_{\mathrm s}(x)|=\infty\}=\bigcap_{n\geq0}E_n(x).$$</div>
<p>The forward inclusion follows from finite host balls; the reverse inclusion follows because a simple path of $n$ edges contains $n+1$ distinct cluster vertices. Finally, for countable $V$, take the union of the null infinite-cluster events over all roots.</p>
<p>When $\Delta=0$ or $1$, every host component has at most two vertices, and the criterion permits $p=1$. For $\Delta\geq2$ it requires a strict inequality. The proof supplies no conclusion at $bp=1$, nor does its final countable union justify a simultaneous assertion over an arbitrary uncountable family of roots. Local finiteness is essential to the finite-path argument: an infinite star has an infinite cluster when all vertices are open but has no simple path of length three.</p>

## The elementary lattice bound {#section-lattice-lower-bound}

<a id="tag-MIUX" data-assertion="corollary" data-title="The site critical probability is at least one over two d minus one"></a>
<p>For nearest-neighbour site percolation on $\mathbb Z^d$, $d\geq1$,</p>
<div class="math-display">$$p&lt;\frac1{2d-1}\ \Longrightarrow\ \theta_{\mathrm s}(p)=0,
\qquad p_{\mathrm c}^{\mathrm s}\geq\frac1{2d-1}.$$</div>
<p><em>Proof.</em> Each neighbour of a lattice vertex is obtained by adding or subtracting one in a single coordinate, so the degree is at most $2d$. Apply 3HEP. Every percolating parameter is therefore at least $(2d-1)^{-1}$; the extra element $1$ in the capped threshold definition has the same lower bound. Taking the infimum gives the result.</p>
<p>For $d=1$ this and $p_{\mathrm c}^{\mathrm s}\leq1$ give $p_{\mathrm c}^{\mathrm s}=1$. Moreover $\theta_{\mathrm s}(1)=1$: almost surely every vertex of the countable line is open. This last endpoint observation is an additional deduction, and shows why the strict degree criterion cannot be replaced by a non-strict one. The zero-dimensional singleton also has capped threshold one, but its infinite-cluster probability is zero even there. For $d=2$ the bound is $1/3$, and in particular $\theta_{\mathrm s}(1/4)=0$. These elementary bounds make no claim about critical percolation in higher dimensions.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-site/">site source inventory</a> separates 41 named public theorem contracts in the foundational, Harris and self-avoiding-path modules. It also records the definitions, private lattice-degree lemmas and endpoint examples outside that theorem count. The existing source records are preserved; the new path correspondences remain pending independent review and compiled association.</p>
