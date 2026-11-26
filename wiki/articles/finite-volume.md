---
{
  "id": "finite-volume",
  "title": "Finite-volume approximation",
  "subtitle": "Finite path witnesses and the order of limits",
  "kind": "method",
  "category": "Methods",
  "summary": "Increasing finite-edge restrictions recover connections, cluster-volume tails and susceptibility. Infinite-cluster probabilities require a different limit, and restricting a graph differs from restricting an observation window. Induced-domain exhaustions also recover susceptibility and give an ordered double-limit formula for escape.",
  "context": [
    "A countable vertex set $V$ and a fixed root $x$.",
    "An open configuration $\\omega$ of unordered bonds; diagonal pairs are discarded by the simple open graph.",
    "Any probability law on the configuration product sigma-algebra; independence is not required for the limit statements."
  ],
  "related": [
    "connectivity",
    "susceptibility",
    "harris-inequality",
    "disjoint-occurrence",
    "russo-formula"
  ],
  "sourceIds": ["perclib-window-tails", "perclib-local-connectivity", "perclib-cluster-moments", "perclib-domain-independence", "perclib-induced-exhaustions", "perclib-finite-volume-associations", "perclib-finite-volume-train9"],
  "aliases": [
    "finite volume",
    "exhaustion",
    "truncation",
    "local connectivity",
    "cluster tails",
    "monotone convergence"
  ],
  "prototypeUses": []
}
---

## Restricting edges {#section-restriction}

<a id="tag-U32Y" data-assertion="definition" data-title="Finite-edge restrictions and their root clusters"></a><p>Let $E_1\subseteq E_2\subseteq\cdots$ be finite sets whose union contains every unordered pair of distinct vertices. Set $\omega_n=\omega\cap E_n$, and let $K_n(x)$ be the root cluster in this restricted configuration, still on the vertex set $V$. Write $K(x)$ for the full cluster. Each $K_n(x)$ is finite and contains $x$, even when no incident edge is retained.</p><p>A finite vertex domain $\Lambda$ gives a special restriction: retain only pairs with both endpoints in $\Lambda$. When $x\in\Lambda$, its restricted cluster lies in $K(x)\cap\Lambda$, but equality need not hold. In the three-vertex path $x-z-y$, with both edges open and $\Lambda=\{x,y\}$, the restricted root cluster is $\{x\}$ while $K(x)\cap\Lambda=\{x,y\}$. The full connection uses a path leaving the observation window.</p>

## Internal connections in a countable domain {#section-local-domain}

<a id="tag-7BMQ" data-assertion="proposition" data-title="Measurable restriction and local connections without ambient countability"></a>
<p>Here the ambient vertex set $V$ may be arbitrary. For $S\subseteq V$, restrict a configuration to unordered pairs with both endpoints in $S$, viewing the result $R_S\omega$ as a configuration on $S$. This restriction is measurable and its simple open graph is the graph induced by $G_\omega$ on $S$. If $S$ is countable, then for $x,y\in S$ the internal connection event</p>
<div class="math-display">$$\{\omega:x\leftrightarrow_S y\}$$</div>
<p>is measurable on the ambient bond configuration space, without any countability assumption on $V$. If $S$ is finite, it is a cylinder event on the finitely many internal pairs. Under a Bernoulli product law, $R_S\omega$ has the product law with the restricted pair profile, for any $S$.</p>
<p>Internal connections depend only on internal pairs, are preserved by adding open coordinates or enlarging the vertex domain, and imply unrestricted connections. Every unrestricted connection has an internal witness in some finite vertex set containing its endpoints, regardless of the cardinality of $V$.</p>
<p>More generally, if $S_n$ is an increasing sequence of vertex sets with union $V$, the events that $x,y\in S_n$ and $x\leftrightarrow_{S_n}y$ increase to $\{x\leftrightarrow y\}$. The sets $S_n$ need not be finite. If they are countable, all these events and their union are measurable, and their probabilities increase to the full connection probability under any probability law on the ambient configuration space.</p>
<p><em>Proof.</em> Each coordinate of $R_S$ is the corresponding ambient coordinate, proving measurability. An internal adjacency holds exactly when its endpoints are distinct and their ambient pair is open; this identifies the induced simple graph. When $S$ is countable, pull back its measurable connection event under $R_S$. In the finite case, only finitely many pairs are read. For the pushforward law, any finite list of distinct internal pairs corresponds to distinct ambient pairs, so its cylinder probabilities are those of the restricted product profile. Cylinder uniqueness gives the claim.</p>
<p>Agreement on internal pairs gives the same induced graph. Adding open edges or enlarging the domain preserves an internal path, and forgetting the domain restriction makes it an ambient path. Conversely, take the finite set of vertices visited by one ambient connecting path. Its induced open graph contains that path. For $x=y$, the singleton domain and length-zero path suffice. In an increasing domain exhaustion, the finite vertex set of a connecting path lies in one common domain, giving the event union. Countable domains make each local event measurable, and continuity from below gives the probability limit.</p>
<p>Thus an uncountable ambient model still has well-defined measurable connection events inside every prescribed countable domain. This does not establish measurability of unrestricted connection in that ambient model: its representation as a union over all finite vertex domains can be uncountable. The countable exhaustion arguments below avoid that difficulty.</p>

## Observing finitely many vertices {#section-window-tails}

<a id="tag-FD69" data-assertion="proposition" data-title="Finite-window tail representation and its finite open witnesses"></a>
<p>For this deterministic statement, let $V$ be any vertex set, let $x\in V$, let $\Lambda\subseteq V$ be finite and let $k\geq0$ be an integer. The root need not belong to $\Lambda$. Then</p>
<div class="math-display">$$\{|K(x)\cap\Lambda|\geq k\}=\bigcup_{\substack{S\subseteq\Lambda\\|S|=k}}\ \bigcap_{y\in S}\{x\leftrightarrow y\}.$$</div>
<p>The event is increasing, and every occurrence has a finite open-edge witness. At $k=0$ it is the whole configuration space, including when $\Lambda$ is empty; at $k&gt;|\Lambda|$ it is empty. If $V$ is countable, it is measurable.</p>
<p><em>Proof.</em> The intersection has at least $k$ vertices exactly when it contains a subset $S$ of size $k$. Every vertex of $S$ then connects to $x$, which proves the event identity. Select a finite open path to each vertex of $S$ and take the union of their edge sets. Retaining just these finitely many open edges preserves the selected connections and hence the volume threshold. Increasingness follows because adding edges preserves connections. At threshold zero use the empty subset and the empty intersection; above $|\Lambda|$ there is no admissible subset. For countable $V$, connection events are measurable and the displayed union and intersections are finite.</p>
<p>This is a finite union of connection events, not necessarily a finite-coordinate event. For example, take vertices $x,y,z_1,z_2,\ldots$ and edges $\{x,z_n\},\{z_n,y\}$ for every $n$, with $\Lambda=\{x,y\}$ and $k=2$. Given any finite coordinate set $F$, choose $n$ such that neither edge through $z_n$ lies in $F$. The all-closed configuration and the configuration opening just those two edges agree on $F$, but only the latter satisfies the tail event. Thus no fixed finite coordinate set determines it, although each occurrence has a finite witness.</p>
<p>The paths may leave $\Lambda$: the observed volume is a full-cluster intersection, not the cluster in the induced graph on $\Lambda$. This is why a finite observation window does not by itself justify a finite-product derivative formula. The finite-edge restrictions below provide the relevant approximations instead.</p>

## Finite witnesses {#section-witnesses}

<a id="tag-F0I9" data-assertion="proposition" data-title="Finite witnesses for simultaneous connections and cluster tails"></a><p>If a finite set $S$ lies in $K(x)$, there is a finite set of open edges $F\subseteq\omega$ for which every vertex of $S$ is connected to $x$ using only $F$. Consequently, for finite $\Lambda\subseteq V$ and an integer $k\geq0$, the event $|K(x)\cap\Lambda|\geq k$ has a finite open-edge witness whenever it occurs.</p><p><em>Proof.</em> Choose one finite open path from $x$ to each vertex of $S$ and take the union of their edge sets. For the tail event, choose $k$ distinct vertices in $K(x)\cap\Lambda$ and apply the first assertion. When $k=0$, the empty set is a witness. When $k&gt;|\Lambda|$, the event is empty.</p><p>These are certificates for connectivity in the full graph. They need not stay inside $\Lambda$. The events are increasing and measurable: finite open certificates form a countable collection on a countable vertex set, as in the <a href="/tag/5CN6/">finite-witness measurability criterion</a>.</p>

## Limits of clusters and probabilities {#section-limits}

<a id="tag-SFLE" data-assertion="proposition" data-title="Finite restrictions recover clusters, tails and susceptibility"></a><p>For every configuration, $K_n(x)\subseteq K_{n+1}(x)$ and $\bigcup_n K_n(x)=K(x)$. Thus, for every finite $\Lambda$ and integer $k\geq0$,</p><div class="math-display">$$\mathbb P(|K_n(x)\cap\Lambda|\geq k)\uparrow\mathbb P(|K(x)\cap\Lambda|\geq k),$$</div><p>and the full cluster sizes satisfy</p><div class="math-display">$$\mathbb P(|K_n(x)|\geq k)\uparrow\mathbb P(|K(x)|\geq k),\qquad \mathbb E|K_n(x)|\uparrow\mathbb E|K(x)|.$$</div><p>The last limit is in $[0,\infty]$ and requires no finite-susceptibility assumption.</p><p><em>Proof.</em> Adding edges preserves every connection. Conversely, a vertex in $K(x)$ is reached by a finite path; all its edges belong to a common $E_n$ because the exhaustion is increasing. This proves the cluster identity. If a volume threshold holds, select the required finite set of vertices and a common finite path witness. Its edges likewise lie in some $E_n$, so the corresponding indicators increase to the full-event indicator. Continuity from below gives the probability limits. The cardinalities themselves increase to $|K(x)|$, including when this is infinite, so monotone convergence gives the expectation limit.</p><p>Taking a one-vertex observation window also gives convergence of each connection probability. For a Bernoulli product law, $\omega_n$ has the profile obtained by keeping the original edge probabilities on $E_n$ and setting them to zero elsewhere. It is not the original law conditioned on an infinite collection of closed exterior edges.</p>

## Infinite clusters and noncommuting limits {#section-infinite}

<a id="tag-B12T" data-assertion="proposition" data-title="Escape characterization and order of cluster-volume limits"></a><p>Let $\Lambda_1\subseteq\Lambda_2\subseteq\cdots$ be finite vertex sets exhausting $V$. Then</p><div class="math-display">$$\{|K(x)|=\infty\}=\bigcap_m\{K(x)\not\subseteq\Lambda_m\},$$</div><p>and therefore</p><div class="math-display">$$\mathbb P(|K(x)|=\infty)=\lim_m\mathbb P(K(x)\not\subseteq\Lambda_m)=\lim_{k\to\infty}\lim_{n\to\infty}\mathbb P(|K_n(x)|\geq k).$$</div><p>In the reverse order, $\lim_{n\to\infty}\lim_{k\to\infty}\mathbb P(|K_n(x)|\geq k)=0$.</p><p><em>Proof.</em> An infinite cluster cannot fit in a finite set. A finite cluster is contained in one member of an increasing exhaustion, by taking the largest of the finitely many indices needed for its vertices. The escape events decrease, so continuity from above gives the first probability limit. For the double limit, first use finite-volume convergence at fixed $k$, then let $k$ tend to infinity in the decreasing events $\{|K(x)|\geq k\}$. Reversing the order gives zero because each restricted cluster is finite.</p><p>For deterministic all-open percolation on an infinite path, the two iterated limits are one and zero respectively. Finite-volume probability convergence does not permit arbitrary interchange of limits, and it supplies no interchange with differentiation in a model parameter. Those steps need their own estimates, as in the <a href="#/russo-formula">infinite-volume caveat for Russo's formula</a>.</p>

## Mixed moments of cluster intersections {#section-moments}

<a id="tag-6HJ9" data-assertion="proposition" data-title="Exact mixed-moment expansions by joint connections"></a>
<p>For finite vertex sets $F,D$ and roots $u,v$, put $X_F(u)=|K(u)\cap F|$. Pointwise, on any vertex set,</p>
<div class="math-display">$$X_F(u)=\sum_{a\in F}\mathbf1_{\{u\leftrightarrow a\}},\qquad
X_F(u)X_D(v)=\sum_{a\in F}\sum_{b\in D}\mathbf1_{\{u\leftrightarrow a,\ v\leftrightarrow b\}}.$$</div>
<p>If $V$ is countable, then under any probability law on its configuration sigma-algebra,</p>
<div class="math-display">$$\mathbb E[X_F(u)X_D(v)]
=\sum_{a\in F}\sum_{b\in D}\mathbb P(u\leftrightarrow a,\ v\leftrightarrow b),$$</div>
<p>and</p>
<div class="math-display">$$\mathbb E[|K(u)|\,|K(v)|]
=\sum_{a\in V}\sum_{b\in V}\mathbb P(u\leftrightarrow a,\ v\leftrightarrow b)\in[0,\infty].$$</div>
<p>Taking $u=v$ and $F=D$ gives the finite-window second moment; taking $u=v$ in the full sum gives $\mathbb E|K(u)|^2$. The roots need not lie in the observation windows, and an empty window gives zero. The sums include $a=b$: they are ordinary moments, not factorial moments.</p>
<p><em>Proof.</em> Expand each volume into connection indicators and multiply. The product of two indicators is the indicator of the intersection, giving the pointwise identities. The corresponding identity for full volumes follows by summing over all pairs of vertices, with infinite values allowed. On countable vertices every summand is measurable. Integrating the finite expansion, or applying Tonelli to the full nonnegative sum, proves the formulas.</p>
<p>These are exact identities for full clusters, whose connecting paths may leave $F$ and $D$. They neither restrict the graph to the windows nor factor the joint connection probability. Product independence is unnecessary for the identities; bounds such as the <a href="/articles/tree-graph/">tree-graph inequality</a> require additional arguments. In the fully open countably infinite graph both sides of the full second-moment identity are infinite.</p>

## Cofinal observation windows {#section-cofinal-moments}

<a id="tag-NEM5" data-assertion="proposition" data-title="Cofinal finite windows recover the full second moment as a supremum"></a>
<p>Let $V$ be countable and let $(F_i)_{i\in I}$ be finite vertex sets satisfying</p>
<div class="math-display">$$\text{for every finite }S\subseteq V\text{ there is }i\in I\text{ with }S\subseteq F_i.$$</div>
<p>Then, for every root $u$ and every probability law on configurations,</p>
<div class="math-display">$$\mathbb E|K(u)|^2=\sup_{i\in I}\mathbb E|K(u)\cap F_i|^2.$$</div>
<p>No finite-moment assumption or ordering of $I$ is required. For an increasing sequence exhausting $V$, the supremum is its increasing limit.</p>
<p><em>Proof.</em> Write $p(a,b)=\mathbb P(u\leftrightarrow a,\ u\leftrightarrow b)$. Each sum over $F_i\times F_i$ is bounded by the full nonnegative sum. Conversely, for any finite $T\subseteq V\times V$, cofinality places both coordinate projections of $T$ inside some $F_i$. Hence</p>
<div class="math-display">$$\sum_{(a,b)\in T}p(a,b)\leq\sum_{a,b\in F_i}p(a,b)
=\mathbb E|K(u)\cap F_i|^2.$$</div>
<p>The full sum is the supremum of its finite subsums, so the reverse inequality follows. This proof does not interchange expectation with an arbitrary supremum.</p>
<p>Merely having $\bigcup_iF_i=V$ is insufficient: on a fully open two-vertex graph, the two singleton windows each give second moment one, while the full second moment is four. Even a cofinal sequence need not have a limit when it is not increasing: alternating between the whole two-vertex set and one singleton gives moments alternating between four and one. Its supremum is still four.</p>

## Independent internal domains {#section-domain-independence}

<a id="tag-RDX7" data-assertion="corollary" data-title="Mutual independence of measurable events internal to disjoint domains"></a>
<p>Here let $V$ be arbitrary and use the Bernoulli product law $\mathbb P_q$. For $S\subseteq V$, let $I(S)$ be the unordered pair coordinates with both endpoints in $S$, including its diagonal coordinates. Suppose $S_1,\ldots,S_m$ are pairwise disjoint and each $A_j$ is a measurable event determined by the coordinates in $I(S_j)$. Then</p>
<div class="math-display">$$\mathbb P_q\!\left(\bigcap_{j=1}^m A_j\right)=\prod_{j=1}^m\mathbb P_q(A_j).$$</div>
<p>This includes the empty family. For countable domains, internal connection events are measurable and satisfy these hypotheses, without ambient countability. Thus if $x,y\in S$, $u,v\in T$ and $S\cap T=\varnothing$, with $S,T$ countable, then</p>
<div class="math-display">$$\mathbb P_q(x\leftrightarrow_S y,\ u\leftrightarrow_T v)
=\mathbb P_q(x\leftrightarrow_S y)\mathbb P_q(u\leftrightarrow_T v).$$</div>
<p><em>Proof.</em> Every unordered pair has an endpoint, so it cannot be internal to two disjoint vertex sets. The blocks $I(S_j)$ are therefore disjoint. A measurable event determined by one block is a measurable event of its restriction: extend a block configuration by closing all other coordinates and take the preimage of the event under this measurable extension. Coordinate determination makes the original event the pullback of that preimage. The <a href="/tag/QH7Q/">independence of disjoint coordinate blocks</a> now gives the finite product formula. This uses a measurable map, not conditioning on an infinite collection of closed coordinates. Internal connections depend only on their internal pairs, and their measurability on countable domains was proved <a href="/tag/7BMQ/">above</a>.</p>
<p>Full-cluster intersections with disjoint windows need not be independent. On four vertices take $S=\{a,b\}$ and $T=\{c,d\}$, open $\{a,c\}$ and $\{b,d\}$ deterministically, and open $\{a,b\}$ with probability $p\in(0,1)$; all other non-diagonal pairs are closed. If $B$ is the indicator of that random edge, then</p>
<div class="math-display">$$|K(a)\cap S|=|K(c)\cap T|=1+B,$$</div>
<p>so their covariance is $p(1-p)&gt;0$. The connection from $c$ to $d$ uses edges outside $T$. This is why the product formula concerns internal events, rather than arbitrary observations of full clusters in disjoint sets.</p>
<p>The pinned <a href="/sources/perclib-cluster-moments/">moment</a> and <a href="/sources/perclib-domain-independence/">domain-independence</a> modules supply the corresponding source contracts. The moment arguments above also explain why their Bernoulli-law identities extend to any configuration law. The two cofinality examples and the dependent-window example clarify scope; they assert no error in those modules or in a published source.</p>


## Exhausting by induced domains {#section-domain-limits}

<p>For a vertex domain $S\subseteq V$, write $K^S(x)$ for the vertices reached from $x$ by an open path entirely inside $S$, and set $K^S(x)=\varnothing$ when $x\notin S$. This convention concerns the induced graph on $S$. It differs from retaining the ambient vertex set and closing all pairs outside $S$: in that graph an exterior root would still have its singleton cluster.</p>

<a id="tag-6QN7" data-assertion="theorem" data-title="Increasing induced domains recover clusters, susceptibility and escape"></a>
<p>Let $S_n\uparrow V$ be an increasing sequence of domains, not necessarily finite. For every configuration and root $x$,</p>
<div class="math-display">$$K^{S_n}(x)\uparrow K(x),\qquad |K(x)|=\sup_n|K^{S_n}(x)|,$$</div>
<p>where all infinite sizes are denoted by $\infty$. If $V$ is countable, then under the bond product law,</p>
<div class="math-display">$$\chi_q(x)=\sup_n\mathbb E_q|K^{S_n}(x)|,$$</div>
<p>and for every fixed $F\subseteq V$,</p>
<div class="math-display">$$\mathbb P_q(K(x)\not\subseteq F)
=\sup_n\mathbb P_q(K^{S_n}(x)\not\subseteq F).$$</div>
<p>No finiteness of susceptibility or local finiteness of the graph is assumed. The domains need not contain $x$ initially; their internal cluster is then empty.</p>
<p><em>Proof.</em> Enlarging the domain preserves internal paths. Conversely, every vertex of $K(x)$ is joined to $x$ by a finite open path, and the vertices of that path all lie in some common $S_n$. This proves the union identity. Every finite subset of the increasing union is contained in one term, proving the equality of extended sizes even when the full cluster is infinite.</p>
<p>On countable vertices, internal connection events are measurable by <a href="/tag/7BMQ/">7BMQ</a>, and the internal volume is the countable sum of their indicators. The volumes increase pointwise, so monotone convergence gives the susceptibility formula. An escape from $F$ has a single endpoint outside $F$ and a finite connecting path. That path eventually lies inside a domain, so the internal escape events increase to the full escape event. Continuity from below gives the probability formula.</p>
<p>Now let $F_m\uparrow V$ be a second exhaustion, this time by finite vertex sets. By <a href="/tag/B12T/">the escape characterization of an infinite cluster</a>,</p>
<div class="math-display">$$\mathbb P_q(|K(x)|=\infty)
=\inf_m\sup_n\mathbb P_q\bigl(K^{S_n}(x)\not\subseteq F_m\bigr).$$</div>
<p>The first exhaustion makes a path available; the second asks that its endpoint leave every finite set. These are separate indices. If every $S_n$ is finite, reversing their order gives zero, because each fixed internal cluster is eventually contained in $F_m$. On the deterministic all-open ray, take $x=0$ and $S_n=F_n=\{0,\ldots,n\}$. The displayed escape probability is $\mathbf1_{\{n&gt;m\}}$, so the two orders give one and zero. If $S_n$ can be infinite, no such zero value for the reversed order is asserted.</p>
<p>For example, on $\mathbb N$ with root $5$ and domains $S_n=\{0,\ldots,n\}$, the first five internal clusters are empty and the later ones contain the root. With $S_n=V$ for every $n$, the cluster identity is constant and imposes no finiteness on $V$. The finite-witness proof therefore does not conceal a bounded interaction range or degree assumption.</p>
<p>The source also states the connection and escape limits for arbitrary ambient $V$. In that generality they are identities of outer measures, unless event measurability has been established separately. For a probability measure $\mu$ and increasing subsets $A_n$, one has $\mu^*(\bigcup_n A_n)=\sup_n\mu^*(A_n)$: choose measurable $B_n\supseteq A_n$ with $\mu(B_n)\leq\mu^*(A_n)+2^{-n}$, and put $C_n=\bigcap_{k\geq n}B_k$. The $C_n$ increase, contain $A_n$, and have measure at most $\sup_k\mu^*(A_k)$. Their measurable union covers $\bigcup_n A_n$, giving the required upper bound; monotonicity gives the reverse bound. Applying this to the deterministic increasing connection or escape events gives the source's outer-measure limits without asserting that an unrestricted connection event on uncountable vertices is measurable.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-domains/">33-contract domain inventory</a> reconciles these limits with local connectivity and the existing <a href="/tag/ROY9/">first-exit bound</a>. The latter is a separate finite-domain estimate with the actual bond probabilities as weights; its independence step uses an internal event and a boundary coordinate. Neither result permits exchanging the two limits or differentiating their limit without further estimates.</p>

## Scope of the tagged finite-witness statements {#section-witness-associations}

<p>The source statements attached to <a href="/tag/FD69/">FD69</a> and <a href="/tag/F0I9/">F0I9</a> retain arbitrary ambient vertex sets. Their finite certificates are sets of open bonds chosen for the particular configuration. Countability enters only the measurable-event clauses. The root need not lie in the observation window, the empty window is allowed, and threshold zero has the empty certificate.</p>
<p>These clauses do not make a finite-window event depend on one fixed finite set of coordinates. The selected paths can leave the window and can use different bonds in different configurations, as in the example above. The <a href="/coverage/sources/perclib-22d8485-associations/">two source contracts</a> therefore support the finite-witness arguments without replacing the distinct finite-edge approximations used for differentiation.</p>


## Exhaustion hypotheses in the expanded source {#section-train9-source}

<p>The <a href="/coverage/sources/perclib-f51f639-reconciliation/">expanded finite-volume source</a> now bundles the full statements of <a href="/tag/7BMQ/">local-domain restriction</a>, <a href="/tag/U32Y/">finite-edge restriction</a>, <a href="/tag/SFLE/">monotone exhaustion</a> and <a href="/tag/B12T/">the two orders of limits</a>. In the edge exhaustion, only non-diagonal pairs need eventually be retained: loops never change a cluster. No bounded-degree, finite-range or finite-susceptibility assumption enters.</p>
<p>For a finite edge set $E$, every restricted cluster lies in the root together with the endpoints of $E$. It is therefore finite even when the ambient vertex set is infinite. This gives the zero limit when the volume threshold tends to infinity first. In the other order, every finite collection of paths is eventually available, so each fixed volume-tail event increases to its unrestricted counterpart. Sending the threshold to infinity afterwards gives the infinite-cluster probability. The source proves the monotone expectation limit for arbitrary measures, allowing an infinite answer; its bundled two-order assertion uses a probability measure for continuity from above.</p>
<p>Countability serves measurability, not the deterministic finite-path argument. In the local-domain statement it is required only for the domains whose events are to be measurable; a countable domain may lie in an uncountable ambient set. The source's product-law clause is the law of a measurable restriction map, so it does not require a positive-probability event on which all exterior coordinates are closed.</p>
