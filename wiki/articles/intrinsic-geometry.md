---
{
  "id": "intrinsic-geometry",
  "title": "Intrinsic balls and cluster-volume tails",
  "subtitle": "Thinning short paths and separating volume from radius",
  "kind": "method",
  "category": "Methods",
  "summary": "A chosen shortest open path compares intrinsic-ball volume with susceptibility at a smaller intensity. An intrinsic-volume bound and a separate one-arm bound together control cluster-volume tails.",
  "context": ["A countable simple graph, with graph distance measured using open edges.", "The thinning comparison uses independent bonds with probabilities $1-e^{-\\beta J_e}$ and finite nonnegative weights.", "The intrinsic one-arm event is not increasing in the edge configuration."],
  "related": ["connectivity", "stopped-exploration", "integrated-lower-tails", "susceptibility"],
  "sourceIds": ["hutchcroft-book", "perclib-intrinsic-balls", "perclib-intrinsic-growth", "hutchcroft-lrp-3"],
  "aliases": ["intrinsic distance", "intrinsic ball", "chemical distance", "intrinsic one-arm", "short-path thinning"],
  "prototypeUses": []
}
---

## Distance inside the open cluster {#section-distance}

<a id="tag-8W1Q" data-assertion="definition" data-title="Intrinsic balls, spheres and one-arm probabilities"></a>
<p>For an edge configuration $\omega$, let $d_\omega(x,y)$ be the smallest number of edges in an open path from $x$ to $y$, with value infinity if there is no such path. For an integer $r\geq0$, define</p>
<div class="math-display">$$B_\omega(x,r)=\{y:d_\omega(x,y)\leq r\},\qquad S_\omega(x,r)=\{y:d_\omega(x,y)=r\}.$$</div>
<p>For a bond law $\mathbb P$ and fixed root $o$, the intrinsic one-arm probability is $Q_r=\mathbb P(S_\omega(o,r)\ne\varnothing)$. In a parameterized independent-bond model on a graph $G$, also define</p>
<div class="math-display">$$Q_r^*(\beta)=\sup_{H\subseteq G}\mathbb P_\beta^H(S_\omega^H(o,r)\ne\varnothing),$$</div>
<p>where $H$ ranges over deterministic subgraphs containing $o$, and the bond law retains the same edge probabilities on $H$.</p>
<p>The ball event $\{x\in B_\omega(o,r)\}$ is increasing, but a sphere need not survive the addition of edges. On the open path $o-u-v$, the sphere of radius two contains $v$; adding the edge $o-v$ makes that sphere empty. Thus an argument about $Q_r$ cannot use stochastic domination as if the arm event were increasing. The supremum over subgraphs supplies a bound for each deleted graph, but an exploration argument must still justify the conditional law on the graph where it restarts.</p>

## Thinning a chosen path {#section-thinning}

<a id="tag-PI11" data-assertion="theorem" data-title="Intrinsic-ball comparison with lower-intensity susceptibility"></a>
<p>Let the edges be independent with probabilities $q_e(t)=1-e^{-tJ_e}$, where each $J_e$ is finite and nonnegative. For $0&lt;\alpha\leq\beta$, every integer $r\geq0$ and every vertex $x$,</p>
<div class="math-display">$$\mathbb P_\beta(x\in B_\omega(o,r))\leq\left(\frac\beta\alpha\right)^r\mathbb P_\alpha(o\leftrightarrow x).$$</div>
<p>Consequently, with possibly infinite expectations,</p>
<div class="math-display">$$\mathbb E_\beta|B_\omega(o,r)|\leq\left(\frac\beta\alpha\right)^r\chi_o(\alpha).$$</div>
<p>If $b&gt;0$ and $\chi_o(b-\varepsilon)\leq C/\varepsilon$ for all sufficiently small $\varepsilon&gt;0$, then for all sufficiently large integers $r$,</p>
<div class="math-display">$$\mathbb E_b|B_\omega(o,r)|\leq\frac{eC}{b}(r+1).$$</div>
<p><em>Proof.</em> Concavity of $t\mapsto1-e^{-tJ_e}$, and its value zero at the origin, give $q_e(\alpha)/q_e(\beta)\geq\alpha/\beta$ whenever $J_e&gt;0$. Sample the configuration at $\beta$. Independently for every edge, retain an open edge with probability $q_e(\alpha)/q_e(\beta)$; edges of zero weight are closed at both parameters. The retained edges are independent with probabilities $q_e(\alpha)$.</p>
<p>On $\{x\in B_\omega(o,r)\}$, choose a shortest open path from $o$ to $x$ using a fixed enumeration to break ties. There are countably many finite paths, so this choice is measurable. A shortest path is simple and has length $\ell\leq r$. Conditional on the entire parameter-$\beta$ configuration, all its edges survive the independent thinning with probability at least $(\alpha/\beta)^\ell\geq(\alpha/\beta)^r$. Survival implies a retained connection from $o$ to $x$. Average this conditional estimate and rearrange. The empty path covers $x=o$, including $r=0$.</p>
<p>Sum over $x$ using Tonelli. For the final assertion take $\beta=b$ and $\alpha=b-b/(r+1)$. For large $r$, the susceptibility hypothesis applies and</p>
<div class="math-display">$$\left(\frac b\alpha\right)^r=\left(1+\frac1r\right)^r\leq e,\qquad \chi_o(\alpha)\leq\frac{C(r+1)}b.$$</div>
<p>This proof uses neither transitivity nor a bound on the vertex degrees. It controls expected intrinsic volume, not the intrinsic arm probability.</p>

## From radius and volume to a cluster tail {#section-tail}

<a id="tag-J1V5" data-assertion="proposition" data-title="Square-root cluster tail from intrinsic volume and arm bounds"></a>
<p>Under any probability law on the countable graph, suppose constants $A,B&lt;\infty$ satisfy</p>
<div class="math-display">$$Q_r\leq\frac A r,\qquad \mathbb E|B_\omega(o,r)|\leq Br\qquad(r\geq1).$$</div>
<p>Then for every integer $n\geq1$,</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq(A+2B)n^{-1/2}.$$</div>
<p><em>Proof.</em> If $S_\omega(o,r)$ is empty, no vertex of the root cluster can have distance greater than $r$: a shortest path to such a vertex would have a vertex at distance exactly $r$. Thus in this case $K_o=B_\omega(o,r)$. For every $r\geq1$, a union bound and Markov's inequality give</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq Q_r+\mathbb P(|B_\omega(o,r)|\geq n)\leq\frac A r+\frac{Br}n.$$</div>
<p>Take $r=\lceil\sqrt n\rceil$. Then $1/r\leq n^{-1/2}$ and $r/n\leq2n^{-1/2}$. This proves the claim without any independence or monotonicity assumption on the law.</p>
<p>The arm bound is a separate hypothesis. A linear expected-ball bound alone does not give the conclusion by this argument. A bound on $Q_r^*$ is sufficient, since the original graph is among the subgraphs in its defining supremum.</p>


## Infinite susceptibility forces linear intrinsic volume {#section-lower-volume}

<a id="tag-R5XZ" data-assertion="theorem" data-title="Intrinsic sphere and ball lower bounds at infinite susceptibility"></a>
<p>Let independent bonds on a countable simple graph have probabilities $q(u,v)$ preserved by a transitive group of vertex permutations. Assume</p>
<div class="math-display">$$D=\sum_{v\ne o}q(o,v)&lt;\infty,\qquad \chi_o=\mathbb E|K_o|=\infty.$$</div>
<p>Then, for every integer $r\geq0$,</p>
<div class="math-display">$$\mathbb E|S_\omega(o,r)|\geq1,\qquad r+1\leq\mathbb E|B_\omega(o,r)|\leq\sum_{j=0}^r D^j,$$</div>
<p>where $D^0=1$. In an invariant transitive intensity model with finite weight row $M$, the summability hypothesis holds at every finite intensity $\beta$, since $D\leq\beta M$.</p>
<p><em>Proof.</em> Every vertex at distance at most $r$ has a simple open path of length at most $r$ from the root. A union bound and independence give an upper bound by the sum of the corresponding path weights. Enlarge the sum to all walks and sum their successive endpoints using the row bound $D$. The total weight of walks of length $j$ is at most $D^j$, proving the upper estimate. In particular every finite-radius ball is finite almost surely and has finite mean.</p>
<p>Write $a_m=\mathbb E|S_\omega(o,m)|$ and $b_m=\mathbb E|B_\omega(o,m)|$. For integers $m,n\geq1$ we claim</p>
<div class="math-display">$$b_{m+n}\leq b_m+a_m b_n.$$</div>
<p>To see this, condition on all intrinsic layers through distance $m$. Put $A=B_\omega(o,m-1)$ and $S=S_\omega(o,m)$. The event specifying these layers depends only on edges with at least one endpoint in $A$: it determines reachability at distances below $m$ and the neighbours of the last interior layer. It places no restriction on edges with both endpoints outside $A$. Conditional on any layer configuration of positive probability, those outside edges therefore retain their independent product law.</p>
<p>This conditional statement is valid on the countable graph: the layers are finite almost surely, so there are countably many possible layer configurations. For each fixed choice, the defining event is measurable using only the incident edges of its fixed interior set. Independence of the two coordinate families applies even if that incident set is infinite.</p>
<p>For a vertex at distance between $m+1$ and $m+n$, choose a shortest path from $o$. Its vertex at step $m$ lies in $S$, and its remaining segment never returns to $A$, since every prefix of a shortest path is shortest. Hence, pointwise,</p>
<div class="math-display">$$B_\omega(o,m+n)\subseteq B_\omega(o,m)\ \cup\!\bigcup_{x\in S}B^{G\setminus A}_\omega(x,n).$$</div>
<p>Conditional on the layers, each ball in the union has expected size at most $b_n$: extend the independent law on $G\setminus A$ to the full graph, use monotonicity of the radius-$n$ ball, and then transitivity. Taking expectations proves the claimed renewal inequality. This comparison concerns balls, whose membership events are increasing; it makes no monotonicity assertion about spheres.</p>
<p>If $a_m&lt;1$ for some $m\geq1$, iteration gives</p>
<div class="math-display">$$b_{km}\leq b_m\sum_{j=0}^{k-1}a_m^j\leq\frac{b_m}{1-a_m}\qquad(k\geq1).$$</div>
<p>Every root-cluster vertex has finite intrinsic distance, so monotone convergence as $k\to\infty$ would give $\chi_o&lt;\infty$, a contradiction. Thus $a_m\geq1$ for every $m\geq1$, and $a_0=1$. Summing the disjoint spheres gives $b_r\geq r+1$.</p>
<p>The theorem uses infinite susceptibility rather than the name of a critical parameter. Combined with the preceding thinning comparison and a mean-field susceptibility upper bound below a finite endpoint $b$, it gives $\mathbb E_b|B_\omega(o,r)|\asymp r$ whenever $\chi(b)=\infty$. It still supplies no intrinsic one-arm bound.</p>


## The intrinsic one-arm bootstrap {#section-bootstrap}

<a id="tag-KEO7" data-assertion="theorem" data-title="Intrinsic one-arm bootstrap from an endpoint volume-tail bound"></a>
<p>Consider an invariant transitive independent-bond intensity model on a nonempty countable graph, with finite weight row $M$. Let $0\leq a&lt;b&lt;\infty$, with $b&gt;0$, and suppose $\chi(\beta)&lt;\infty$ for $a&lt;\beta&lt;b$. If for some $\delta&gt;1$ and $C&lt;\infty$,</p>
<div class="math-display">$$\mathbb P_b(|K_o|\geq n)\leq Cn^{-1/\delta}\qquad(n\geq1),$$</div>
<p>then there is $A_0&lt;\infty$ such that</p>
<div class="math-display">$$Q_r^*(b)\leq A_0r^{-1/(\delta-1)}\qquad(r\geq1).$$</div>
<p>In particular, a square-root endpoint volume tail gives an intrinsic one-arm upper bound of order $r^{-1}$. The conclusion is uniform over deterministic subgraphs; it does not assume their intrinsic spheres are increasing events.</p>
<p><em>Proof.</em> Put $\theta=1/(\delta-1)$. We first prove, for $a&lt;\beta&lt;b$ and integers $r,n\geq1$,</p>
<div class="math-display">$$Q_{3r}^*(\beta)\leq Cn^{-1/\delta}+\frac nr\bigl(Q_r^*(\beta)\bigr)^2.$$</div>
<p>Fix a deterministic subgraph $H$ containing $o$ and explore its intrinsic layers. Stop at the first level $j\in\{r,\ldots,2r-1\}$ with $0&lt;|S^H_\omega(o,j)|\leq n/r$, if one exists. If the cluster reaches level $3r$ but has fewer than $n$ vertices, such a level exists: all $r$ middle layers are nonempty, and their total size is less than $n$.</p>
<p>At the stopping level let $A=B^H_\omega(o,j-1)$ and $S=S^H_\omega(o,j)$. As in the renewal proof, conditional on the explored layers, the edges in $H\setminus A$ retain their product law. The stopping rule depends only on those layers, so the same assertion holds at the random stopping level. If the original cluster reaches level $3r$, a shortest path to that level passes through some $x\in S$ and continues in $H\setminus A$. Its endpoint has distance at least $3r-j\geq r$ from $x$ in that remaining graph: a shorter remaining path would contradict its distance $3r$ from $o$. Thus some $x\in S$ has an intrinsic arm of length $r$ in $H\setminus A$.</p>
<p>Transitivity moves each such root $x$ to $o$ while preserving the full model, so its conditional arm probability is at most $Q_r^*(\beta)$. A union bound gives at most $(n/r)Q_r^*(\beta)$ conditional probability of continuation. The stopping event itself implies that the cluster reaches level $r$, and hence has probability at most $Q_r^*(\beta)$. The alternative large-cluster event has probability at most $Cn^{-1/\delta}$: cluster volume is increasing under the coupling from $H$ at $\beta$ to the full graph at $b$. Taking the supremum over $H$ proves the recursion.</p>
<p>For a fixed $\beta\in(a,b)$, set</p>
<div class="math-display">$$A=\max\left\{1,\sup_{r\geq1}r^\theta Q_r^*(\beta)\right\}.$$</div>
<p>This is finite. Indeed, an arm of length $r$ in any subgraph entails at least $r+1$ vertices in its cluster, which is contained in the full cluster under the natural coupling. Finite transitive susceptibility supplies the <a href="/tag/Y84V/">tree-graph moments</a> and hence an <a href="/tag/SNB3/">exponential volume tail</a> at this fixed parameter. Its constants may depend on $\beta$; only finiteness of $A$ is used at this stage.</p>
<p>Write $q=2/(\delta+1)&lt;1$ and, for each $r$, put $t=r^{\delta\theta}A^{-2\delta/(\delta+1)}$. If $t\geq1$, choose the integer $n=\lceil t\rceil\leq2t$ in the recursion. Since $(\delta-1)\theta=1$, both resulting terms have the same scale, giving</p>
<div class="math-display">$$Q_{3r}^*(\beta)\leq(C+2)A^q r^{-\theta}.$$</div>
<p>If $t&lt;1$, then $r^\theta&lt;A^q$, and the same estimate follows from $Q_{3r}^*(\beta)\leq1$. For every $R\geq3$, choose $r=\lfloor R/3\rfloor$. Intrinsic arm events are decreasing in their radius, so $Q_R^*\leq Q_{3r}^*$, and $R/r\leq5$. For $R=1,2$ use $Q_R^*\leq1$. Consequently</p>
<div class="math-display">$$A\leq K A^q,\qquad K=\max\{1,2^\theta,5^\theta(C+2)\}.$$</div>
<p>Since $1\leq A&lt;\infty$, division gives $A\leq K^{1/(1-q)}$, uniformly in $\beta\in(a,b)$.</p>
<p>It remains to pass to $b$; monotonicity of sphere events is not available. Fix $H$ and $r$ and use the increasing uniform coupling as $\beta\uparrow b$. The radius-$r$ ball at $b$ is almost surely finite by the finite-row path bound. Choose a shortest path at $b$ to each vertex in that ball. Only finitely many open edges are used, and each is eventually open at every sufficiently large lower parameter. The radius-$r$ and radius-$(r-1)$ balls therefore eventually agree with their endpoint values. Their difference, the sphere, also agrees. Bounded convergence gives convergence of the arm probability for this fixed $H,r$. The uniform subcritical bound passes to this limit, and then taking the supremum over $H$ proves the theorem.</p>
<p>This supplies the Kozma–Nachmias bootstrap under explicit finite-susceptibility and summability hypotheses. The proof handles integer cutoff choices and the endpoint limit separately. It uses monotonicity in the radius, but never monotonicity of intrinsic spheres under edge addition.</p>

## Source scope {#section-source}

<p>These are the definitions, thinning comparison and radius-volume implication. The renewal argument also supplies the expected-ball lower bound under explicit summability and infinite-susceptibility hypotheses. The one-arm bootstrap is supplied under its separate endpoint-tail and finite-susceptibility hypotheses. A linear expected-ball estimate alone is not used to deduce an arm estimate, and intrinsic distance is not identified with distance in a Euclidean embedding.</p>

## Source scope of the intrinsic-ball estimates {#section-balls-source}

<p>The source derives measurability of ball events from the recursion</p>
<div class="math-display">$$d_\omega(o,y)\leq r+1\quad\Longleftrightarrow\quad
y=o\ \text{ or }\ \exists z:\ z\sim_\omega y,\ d_\omega(o,z)\leq r.$$</div>
<p>On countable vertices this is a countable union of intersections of measurable events. Summing the resulting indicators gives the extended ball volume and its expectation under any measure. No local-finiteness assumption is needed; a finite-radius ball may be infinite.</p>
<p>For <a href="/tag/PI11/">PI11</a>, the source constructs the retention profile $s_e=q_e(\alpha)/q_e(\beta)$ when the denominator is positive and sets $s_e=1$ otherwise. Thus $q_e(\beta)s_e=q_e(\alpha)$ and $s_e\geq\alpha/\beta$ in both cases. Fixing the original configuration, any open walk of length at most $r$ supplies a finite set $F$ of distinct bonds with $|F|\leq r$. Its chance of surviving the independent thinning is at least $(\alpha/\beta)^{|F|}\geq(\alpha/\beta)^r$. This bounds a section of the thinned connection event pointwise. Product integration then proves the comparison without needing a measurable choice of a path as a separate construction.</p>
<p>The pointwise and volume comparisons include $r=0$, equal positive intensities and infinite susceptibility. The lower intensity must be positive. In the eventual linear bound the source permits an extended constant $C$, but only finite $C$ yields a finite estimate. Choosing $\varepsilon=b/(r+1)$ for sufficiently large $r$ ensures both that the susceptibility hypothesis applies and that $b-\varepsilon&gt;0$.</p>
<p>The source form of <a href="/tag/J1V5/">J1V5</a> allows any measure, with extended nonnegative constants $A,B$. Its proof takes $r=\lfloor\sqrt n\rfloor+1$, which still lies between $\sqrt n$ and $2\sqrt n$ for $n\geq1$. An empty sphere excludes more distant vertices <em>of the root cluster</em>; vertices in other components have infinite distance and are irrelevant. The union bound and Markov step therefore need neither finite balls nor independent edges. Finite constants give the useful square-root tail.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-geometry/">thirteen-contract inventory</a> includes a two-vertex thinning witness at radii zero and one and a singleton radius-volume witness. It does not prove the separate sphere hypothesis, the lower intrinsic-volume theorem or the one-arm bootstrap. In particular, it does not treat intrinsic spheres as increasing events.</p>


## The path-counting upper bound in the source {#section-growth-source}

<p>The <a href="/coverage/sources/perclib-f51f639-endpoints/">intrinsic-growth source</a> proves the upper bound in <a href="/tag/R5XZ/">R5XZ</a> under a uniform bound $D$ on the off-diagonal opening-probability rows. Every vertex at intrinsic distance at most $r$ is the endpoint of a simple open path of length at most $r$. The probability that such a path is open is the product of its edge probabilities. Summing over paths and then enlarging to all walks gives $\mathbb E|B_\omega(o,r)|\leq\sum_{j=0}^rD^j$.</p>
<p>The empty path gives the term one at radius zero. All sums are nonnegative, so the source permits $D=\infty$; a finite bound is needed only to obtain a finite numerical estimate. A transitive profile makes the row sum independent of the root. Infinite susceptibility is not a hypothesis for this upper bound, and the file does not prove the lower sphere bound or an intrinsic one-arm estimate.</p>


## Moments of chemical distance {#section-distance-moments}

<a id="tag-SBMG" data-assertion="proposition" data-title="Susceptibility bounds all rooted chemical-distance moments"></a>
<p>Let an independent bond law on a countable simple graph be invariant under a transitive group. Suppose $\chi=\mathbb E|K_o|&lt;\infty$. For every integer $q\geq1$,</p>
<div class="math-display">$$D_q:=\mathbb E\sum_{x\in K_o}d_\omega(o,x)^q\leq q!\,\chi^{q+1}.$$</div>
<p>Distances are summed only over connected vertices; the root contributes zero. In particular $D_1\leq\chi^2$ and $D_2\leq2\chi^3$.</p>
<p><em>Proof.</em> If $o$ and $x$ are connected at distance $\ell$, take a shortest open path, with vertices $v_0=o,\ldots,v_\ell=x$. Every weakly ordered choice of $q$ indices $0\leq i_1\leq\cdots\leq i_q\leq\ell$ splits this path into $q+1$ edge-disjoint connections through $v_{i_1},\ldots,v_{i_q}$. Repeated indices give empty segments, which are valid witnesses. The resulting vertex tuples are distinct, and their number is $\binom{\ell+q}{q}\geq\ell^q/q!$. Thus, pointwise,</p>
<div class="math-display">$$d_\omega(o,x)^q\mathbf1_{\{x\in K_o\}}
\leq q!\sum_{z_1,\ldots,z_q}\mathbf1_{\{o\leftrightarrow z_1\}\circ\{z_1\leftrightarrow z_2\}\circ\cdots\circ\{z_q\leftrightarrow x\}},$$</div>
<p>with the left side defined as zero off the connection event. Apply the iterated BK inequality to these increasing connection events and sum over all marks and $x$. Every row sum of the two-point function is $\chi$, so the resulting chain sums to $\chi^{q+1}$. Tonelli justifies the sums; finite-edge approximation gives the same BK bound on the countable graph.</p>
<p>The split paths provide a lower bound on the number of disjoint witnesses. No assertion that every such witness comes from a geodesic is needed. This proves Lemma III.2.4(1), equation (III.2.8) and the higher-moment estimate used in (III.6.39) of Part III.</p>

## The derivative carried by open pivotal edges {#section-open-pivotal-rate}

<a id="tag-NMYK" data-assertion="theorem" data-title="Open-pivotal susceptibility rate and its chemical-distance bound"></a>
<p>Consider a transitive independent-bond intensity model on a countable simple graph, with symmetric nonnegative weights and</p>
<div class="math-display">$$0&lt;M=\sum_{v\ne o}J(o,v)&lt;\infty,\qquad p_e(\beta)=1-e^{-\beta J_e}.$$</div>
<p>Fix $\beta&gt;0$ with $\chi(\beta)&lt;\infty$. An open edge is pivotal for $o\leftrightarrow x$ if deleting it disconnects those vertices. Set</p>
<div class="math-display">$$c_\beta(e)=\frac{J_e}{e^{\beta J_e}-1}\quad(J_e&gt;0),\qquad
G(\beta)=\mathbb E_\beta\sum_{x\in K_o}\ \sum_{e\text{ open pivotal for }o\leftrightarrow x}c_\beta(e).$$</div>
<p>Edges of weight zero never contribute. Then</p>
<div class="math-display">$$0\leq G(\beta)\leq M\chi(\beta)^2,\qquad
G(\beta)\leq\left(\sup_{e:J_e&gt;0}c_\beta(e)\right)D_1(\beta)\leq\beta^{-1}D_1(\beta).$$</div>
<p>On any open interval $I\subset(0,\infty)$ where susceptibility is finite, $\chi$ is continuously differentiable and $\chi'=G$ throughout $I$.</p>
<p><em>Proof.</em> Pivotality is independent of the state of the edge. Multiplying its open probability by $c_\beta(e)$ gives $J_e$ times its closed probability. In a closed-pivotal configuration, one endpoint of the edge belongs to the root cluster and the other to the cluster of $x$. Therefore</p>
<div class="math-display">$$G(\beta)=\sum_{u\ne v}\sum_x J(u,v)\,
\mathbb P_\beta(o\leftrightarrow u,\ v\leftrightarrow x,\ o\not\leftrightarrow v).$$</div>
<p>The orientation is determined by the root cluster, so there is no factor of two. BK bounds each event by $\tau_\beta(o,u)\tau_\beta(v,x)$; summing gives $M\chi^2$. Also every open pivotal lies on every open path from $o$ to $x$, hence on a shortest one. Its number is at most $d_\omega(o,x)$. Finally $e^{\beta J_e}-1\geq\beta J_e$, which proves the distance bound.</p>
<p>For the derivative assertion, exhaust the graph by finite vertex sets containing $o$. Finite-volume Russo gives the corresponding oriented sum. For each fixed triple $(u,v,x)$ its event converges to the full-volume event: connections have finite path witnesses, and any full disconnection persists in every restriction. The summable BK bound above gives convergence of the entire sum. On a compact intensity interval $[s,t]\subset I$, the derivative sums are bounded by $M\chi(t)^2$. Integrating before passing to the limit gives</p>
<div class="math-display">$$\chi(t)-\chi(s)=\int_s^t G(\beta)\,d\beta.$$</div>
<p>To see that $G$ is continuous, fix $\beta\in I$ and choose $\beta_+\in I$ with $\beta_+&gt;\beta$. In the uniform coupling, the four clusters rooted at a fixed $o,u,v,x$ at intensity $\beta_+$ are finite almost surely. For parameters near $\beta$, the relevant connections are decided by the finitely many edges within their union. Each of these edge states is locally constant at $\beta$ almost surely. Bounded convergence proves continuity of the event probability. The summable majorant $J(u,v)\tau_{\beta_+}(o,u)\tau_{\beta_+}(v,x)$ then proves continuity of $G$. The integral identity now gives $\chi'=G$ at every point of $I$.</p>
<p>This is the open-pivotal form of the derivative in Lemma III.2.4(3). The argument for the derivative precedes any use of a countable Russo sum. It needs no group structure beyond transitivity and makes no identification of chemical distance with the number of pivotal edges.</p>

## Long paths force a large derivative {#section-distance-derivative-lower}

<a id="tag-OCMG" data-assertion="theorem" data-title="A chemical-distance lower bound forces a susceptibility-rate lower bound"></a>
<p>In the model of NMYK, at a positive intensity with finite susceptibility, for every $\varepsilon&gt;0$,</p>
<div class="math-display">$$D_1\geq\varepsilon\chi^2
\quad\Longrightarrow\quad
G(\beta)\geq\frac{M}{\exp(64\beta M\varepsilon^{-3})-1}\,\chi^2.$$</div>
<p>Thus, when susceptibility is finite on a neighborhood of $\beta$, the same bound holds for $\chi'(\beta)$. This is the constant in Part III, Lemma III.2.5.</p>
<p><em>Proof.</em> Use the probability law on configurations with a marked cluster vertex given by</p>
<div class="math-display">$$\widehat{\mathbb E}F(\omega,X)=\frac1\chi\mathbb E\sum_{x\in K_o}F(\omega,x).$$</div>
<p>Equivalently, first bias by cluster volume and then choose $X$ uniformly from that cluster. By SBMG, the marked distance $L=d_\omega(o,X)$ satisfies $\widehat{\mathbb E}L\geq\varepsilon\chi$ and $\widehat{\mathbb E}L^2\leq2\chi^2$. Paley–Zygmund therefore gives $\widehat{\mathbb P}(L\geq\varepsilon\chi/2)\geq\varepsilon^2/8$.</p>
<p>For a vertex $x$, let</p>
<div class="math-display">$$W(x)=\sum_{(u,v):u\ne v}J(u,v)\,
\mathbf1_{\{o\leftrightarrow u\text{ off }\{u,v\}\}\circ\{v\leftrightarrow x\text{ off }\{u,v\}\}}.$$</div>
<p>Both orientations are included. BK and transitivity give $\mathbb E\sum_x W(x)\leq M\chi^2$, and hence $\widehat{\mathbb E}W(X)\leq M\chi$. Markov's inequality leaves an event of marked probability at least $\varepsilon^2/16$ on which</p>
<div class="math-display">$$L\geq\varepsilon\chi/2,\qquad W(X)\leq16M\varepsilon^{-2}\chi.$$</div>
<p>We turn this weight bound into many opportunities for a pivotal edge. Fix $k\geq1$. Write $A=B_\omega(o,k-1)$ and $F=S_\omega(o,k-1)$. For $x\notin A$, let $C$ be its cluster in the graph with $A$ deleted, and let $\mathcal E_k(x)$ be the edges from $F$ to $C$. Put $W_k(x)=\sum_{e\in\mathcal E_k(x)}J_e$; set it to zero when $x\in A$. Every edge counted here has disjoint paths from $o$ to its endpoint in $F$, inside $A$, and from its endpoint in $C$ to $x$, outside $A$. These paths avoid that edge. An oriented edge has its tail in at most one intrinsic sphere, so</p>
<div class="math-display">$$\sum_{k\geq1}W_k(x)\leq W(x).$$</div>
<p>Let $R=\lceil\varepsilon\chi/2\rceil$ and $H=64M\varepsilon^{-3}$. On the marked event above, $L\geq R$ and $\sum_{k=1}^R W_k(X)\leq HR/2$. At least $R/2$ of those levels have $W_k(X)\leq H$. Removing the size bias yields</p>
<div class="math-display">$$\sum_{k=1}^R\mathbb E\#\{x\in K_o:d_\omega(o,x)\geq k,\ W_k(x)\leq H\}
\geq\frac{\varepsilon^2R\chi}{32}.$$</div>
<p>Now reveal the intrinsic layers through $k-1$ by inspecting only edges incident to $B_\omega(o,k-2)$, with this interior empty when $k=1$. Then reveal $C$ using edges with both endpoints outside $A$. The edges from $F$ to $C$ have not been queried and retain their independent laws. All edges from the earlier layers to $C$ are already known to be closed. This distinction between the interior and the last layer is essential.</p>
<p>The conditioning is legitimate on the countable graph. Finite susceptibility and transitivity make every cluster finite almost surely. There are only countably many possible finite layer lists and finite exterior clusters. For each fixed outcome of positive probability, its defining event depends on coordinates disjoint from the edges between its fixed $F$ and $C$. Independence applies even when specifying the outcome required infinitely many closed-edge observations.</p>
<p>Let $P_k(x)=c_\beta(e)$ if exactly one edge $e$ of $\mathcal E_k(x)$ is open, and let $P_k(x)=0$ otherwise, including $x\in A$. When $x\notin A$, connection to the root occurs exactly when at least one edge of $\mathcal E_k(x)$ is open. Conditional on the exploration, therefore,</p>
<div class="math-display">$$\mathbb P(x\in K_o\mid\mathcal F_k(x))=1-e^{-\beta W_k(x)},\qquad
\mathbb E[P_k(x)\mid\mathcal F_k(x)]=W_k(x)e^{-\beta W_k(x)}.$$</div>
<p>For the second identity, the probability that $e$ is the unique open candidate is $(e^{\beta J_e}-1)e^{-\beta W_k(x)}$; multiplication by $c_\beta(e)$ leaves $J_e e^{-\beta W_k(x)}$. If $W_k(x)=0$, both conditional expressions are zero.</p>
<p>A unique open candidate is pivotal for $o\leftrightarrow x$: the component $C$ has no other open edge to $A$, and no open edge to the rest of the exterior. The same pivotal cannot be counted at two different levels, because its endpoint closer to $o$ has a fixed intrinsic distance. Consequently $G\geq\sum_k\sum_x\mathbb E P_k(x)$. The function $w/(e^{\beta w}-1)$ is decreasing for $w&gt;0$, so the conditional identities give</p>
<div class="math-display">$$\begin{aligned}
G&\geq\frac{H}{e^{\beta H}-1}\sum_{k=1}^R
\mathbb E\#\{x\in K_o:d_\omega(o,x)\geq k,\ W_k(x)\leq H\}\\
&\geq\frac{H}{e^{\beta H}-1}\frac{\varepsilon^2R\chi}{32}
\geq\frac{M}{e^{64\beta M\varepsilon^{-3}}-1}\chi^2.
\end{aligned}$$</div>
<p>In the last step $R\geq\varepsilon\chi/2$. Every sum is nonnegative, and $G\leq M\chi^2$ supplies finiteness. This completes the proof without a reverse-BK hypothesis or a monotonicity claim for intrinsic spheres.</p>

## Negligible distance moments {#section-negligible-distances}

<a id="tag-T9LZ" data-assertion="corollary" data-title="A negligible pivotal rate makes every normalized distance moment negligible"></a>
<p>Consider a sequence of models and parameters satisfying NMYK, with $0&lt;M_j\leq M_0&lt;\infty$ and $0&lt;\beta_j\leq b_1&lt;\infty$. If $G_j/\chi_j^2\to0$, then, for every integer $q\geq1$,</p>
<div class="math-display">$$\frac{D_{q,j}}{\chi_j^{q+1}}\longrightarrow0.$$</div>
<p>In particular, the conclusion follows from $\mathbb E_j|K_o|^2=o(\chi_j^3)$ when the intensities are bounded below by a positive constant and the score bound $G_j^2\leq(M_j/\beta_j)\chi_j\mathbb E_j|K_o|^2$ is available.</p>
<p><em>Proof.</em> If $D_{1,j}/\chi_j^2$ failed to tend to zero, some $\varepsilon&gt;0$ would give a subsequence to which OCMG applies. On that subsequence,</p>
<div class="math-display">$$\frac{G_j}{\chi_j^2}\geq
\frac{M_j}{e^{64\beta_jM_j\varepsilon^{-3}}-1}
\geq\frac{M_0}{e^{64b_1M_0\varepsilon^{-3}}-1}&gt;0,$$</div>
<p>a contradiction. Under the marked probability law used above, put $Y_j=d_\omega(o,X)/\chi_j$. Then $\widehat{\mathbb E}_jY_j\to0$, while SBMG bounds $\widehat{\mathbb E}_jY_j^m\leq m!$ for every positive integer $m$. For $q\geq2$, Cauchy–Schwarz gives</p>
<div class="math-display">$$\widehat{\mathbb E}_jY_j^q\leq
\bigl(\widehat{\mathbb E}_jY_j\bigr)^{1/2}
\bigl(\widehat{\mathbb E}_jY_j^{2q-1}\bigr)^{1/2}\longrightarrow0.$$</div>
<p>This is precisely the claimed normalization. The final assertion follows by dividing the score inequality by $\chi_j^4$.</p>
<p>This supplies the intrinsic-distance implication used in Part III, equation (III.6.39). The <a href="/articles/stopped-exploration/#section-score">exploration-score estimate</a> supplies the stated derivative bound under its own moment and parameter hypotheses. Critical-dimensional suppression of the second moment remains a model input; spatially weighted geodesic estimates and the later diagram bounds are separate arguments.</p>

## Choosing paths consistently under restriction {#section-consistent-geodesics}

<a id="tag-BN7Z" data-assertion="proposition" data-title="Translation-equivariant geodesics can be chosen consistently under subgraph restriction"></a>
<p>For connected vertices $u,v$ of a graph $H$ on a subset of $\mathbb Z^d$, one can choose a shortest path $\gamma_H(u,v)$ measurably and translation-equivariantly so that</p>
<div class="math-display">$$H'\subseteq H,\quad\gamma_H(u,v)\subseteq H'
\quad\Longrightarrow\quad\gamma_{H'}(u,v)=\gamma_H(u,v).$$</div>
<p>Here containment of a path includes its edges. Its vertex set includes both endpoints, and the path from a vertex to itself consists of that one vertex.</p>
<p><em>Proof.</em> Fix a well-order of $\mathbb Z^d\setminus\{0\}$. Among paths of the shortest possible length, choose the one whose sequence of successive displacements is lexicographically least. A finite lexicographic product of well-orders is well-ordered, so a least path exists even when the graph has infinite degree. Translating a path leaves this sequence unchanged. A subgraph containing the chosen path cannot have a shorter path or a lexicographically earlier path of the same length, since either would already be present in $H$.</p>
<p>For fixed endpoints, there are countably many finite paths. The event that a particular path is chosen is the event that all its edges are open and no earlier candidate is open, with candidates ordered first by length and then lexicographically. It is therefore measurable. This construction supplies more than equivariance: an arbitrary equivariant choice need not survive restriction when several shortest paths are available.</p>

## An averaged path bound off a forbidden set {#section-restricted-cluster-comparison}

<a id="tag-XFCJ" data-assertion="theorem" data-title="Restricted-cluster comparison for downward-closed classes and consistent geodesics"></a>
<p>Let a translation-invariant independent bond law on $\mathbb Z^d$ satisfy $\chi=\mathbb E|K_0|&lt;\infty$ and $m_2=\mathbb E|K_0|^2&lt;\infty$. Let $B$ be a finite, nonempty, symmetric set of vertices. Define</p>
<div class="math-display">$$\mu(x)=\frac{\mathbb E[|K_0|\mathbf1_{\{x\in K_0\}}]}{m_2},\qquad
L_\mu(P)=\sum_x\mu(x)|V(P)\cap(x+B)|.$$</div>
<p>Then $\mu$ is a probability measure. It is the law of a uniform vertex of the root cluster after biasing that cluster by its squared size. Use the paths from BN7Z. For a deterministic set $W$, let $K_0^W$ be the root cluster after deleting $W$, and set it to the empty graph if $0\in W$. Suppose $\mathscr A$ is a class of finite vertex sets containing the root which is downward closed among such sets: $0\in S'\subseteq S\in\mathscr A$ implies $S'\in\mathscr A$. Put</p>
<div class="math-display">$$Z_{W,\ell}=\sum_{z\in K_0^W}
\mathbf1_{\{V(K_0^W)\in\mathscr A,\ L_\mu(\gamma_{K_0^W}(0,z))\leq\ell\}}.$$</div>
<p>For every $\ell&gt;0$ and every $W$,</p>
<div class="math-display">$$\mathbb E\left[Z_{W,\ell}\sum_{y\in B}\mathbf1_{\{0\nleftrightarrow y\}}|K_y|\right]
\geq\bigl(|B|\chi-\ell m_2\bigr)\mathbb E Z_{W,\ell}.$$</div>
<p>The same measure $\mu$ works for all $W,\ell,\mathscr A$ satisfying these conditions. In particular, classes defined by upper bounds on nonnegative weighted cluster volumes are allowed.</p>
<p><em>Proof.</em> Tonelli gives $\sum_x\mu(x)=m_2^{-1}\mathbb E[|K_0|\sum_x\mathbf1_{\{x\in K_0\}}]=1$. We first prove a slightly more general comparison. Let $0\leq F(H,z)\leq1$ have the following restriction property: if a connected rooted subgraph $H'$ of $H$ contains $\gamma_H(0,z)$, then $F(H',z)\geq F(H,z)$.</p>
<p>Sample a full configuration with root cluster $K$, and an independent full configuration whose off-$W$ root cluster is $\widetilde H$. Both clusters are finite almost surely. For each $y\in B$, form a configuration $\eta_y$ by preserving every edge state incident to $V(K)$ and using the translated second configuration on all edges with both endpoints outside $V(K)$. Conditional on the entire finite open cluster graph $K$, the original exterior edges have their unchanged product law: the conditioning fixes internal states and the closed boundary, but involves no exterior coordinate. The replacement exterior has precisely that law and is independent of $K$. Thus each $\eta_y$ has the original product law, and its root cluster is exactly $K$.</p>
<p>If $y\notin K$, its off-$(W+y)$ cluster $H_y$ in $\eta_y$ is the component of $y$ in the graph $(y+\widetilde H)\setminus V(K)$. If $K$ misses the translated path $y+\gamma_{\widetilde H}(0,z)$, that path is retained, and the restriction property gives</p>
<div class="math-display">$$F(H_y-y,z)\geq F(\widetilde H,z),\qquad y+z\in H_y.$$</div>
<p>For each fixed path $P$, symmetry of $B$ gives the deterministic counting bound</p>
<div class="math-display">$$\sum_{y\in B}\mathbf1_{\{K\cap(y+V(P))=\varnothing\}}
\geq |B|-\sum_{y\in B}|K\cap(y+V(P))|
=|B|-\sum_{x\in K}|V(P)\cap(x+B)|.$$</div>
<p>Multiply by $|K|F(\widetilde H,z)$, sum over $z$, and average. Independence of $K$ and $\widetilde H$ and the definition of $\mu$ yield</p>
<div class="math-display">$$\begin{aligned}
&\mathbb E\left[|K|\sum_{y\in B}\mathbf1_{\{y\notin K\}}
\sum_{w\in H_y}F(H_y-y,w-y)\right]\\
&\quad\geq |B|\chi\,\mathbb E\sum_{z\in K_0^W}F(K_0^W,z)
-m_2\,\mathbb E\sum_{z\in K_0^W}F(K_0^W,z)L_\mu(\gamma_{K_0^W}(0,z)).
\end{aligned}$$</div>
<p>Each $\eta_y$ has the original law. Translate its summand by $-y$ and then replace $-y$ by $y$ in the sum over the symmetric set $B$. The left side becomes</p>
<div class="math-display">$$\mathbb E\left[\sum_{y\in B}|K_y|\mathbf1_{\{0\nleftrightarrow y\}}
\sum_{z\in K_0^W}F(K_0^W,z)\right].$$</div>
<p>Now take $F$ to be the indicator defining $Z_{W,\ell}$. Downward closure preserves membership in $\mathscr A$, and BN7Z preserves the selected path whenever it survives, so $F$ has the required restriction property. Its weighted path length is at most $\ell$ on its support. Substitution proves the result. The expectations are finite: the left side is bounded using $|B|$ applications of Cauchy–Schwarz and $m_2$, and the unsimplified error is bounded by $m_2\mathbb E|K_0^W|^2\leq m_2^2$.</p>
<p>This is a corrected version of the comparison needed in Lemma III.4.2. The classes later used in its gluing argument impose upper bounds on cluster intersections and their nonnegative averages; they are downward closed. The <a href="/errata/hutchcroft-lrp-3/#restricted-cluster-heredity">provisional erratum</a> distinguishes this repair from the source's arbitrary-class statement.</p>

## Why an arbitrary cluster class is insufficient {#section-restricted-cluster-counterexample}

<a id="tag-OTH1" data-assertion="proposition" data-title="The arbitrary-class restricted-cluster inequality fails on radial lattice percolation"></a>
<p>The conclusion of XFCJ with no downward-closure assumption is false, even for a normalized power-law soft cutoff on $\mathbb Z^d$. This failure does not involve reverse BK.</p>
<p><em>Proof.</em> Fix any integer $d\geq1$, let $\alpha=d/3$, use $\|x\|=2\|x\|_\infty$, and take $j(t)=t^{-d-\alpha}/(d+\alpha)$. Its norm unit ball has volume one and $|j'(t)|=t^{-d-\alpha-1}$. At cutoff radius $r=3$, the observation ball is</p>
<div class="math-display">$$B=\{-1,0,1\}^d,\qquad |B|=3^d.$$</div>
<p>Every nearest-neighbour lattice edge has strictly positive cutoff weight. Let $M=\sum_{z\ne0}J(0,z)&lt;\infty$ and choose $0&lt;\beta\leq1/(4M)$. The <a href="/tag/53Z9/">row-sum bound</a> and the tree-graph inequality give</p>
<div class="math-display">$$\chi\leq4/3,\qquad \frac{m_2}{\chi}\leq\chi^2\leq16/9&lt;|B|.$$</div>
<p>Delete $W=\mathbb Z^d\setminus B$ and take the class $\mathscr A=\{B\}$. The event $V(K_0^W)=B$ has positive probability: it contains the event that a fixed nearest-neighbour spanning tree of this finite box is open. Whenever it occurs, every $y\in B$ is connected to the root in the full configuration. Hence the left side of the claimed arbitrary-class inequality is zero.</p>
<p>For any proposed probability measure $\mu$, set $\ell=1$. The root's zero-edge path has just one vertex, so $L_\mu(\gamma_H(0,0))\leq1$. Thus $Z_{W,1}\geq1$ on $\{V(K_0^W)=B\}$ and $\mathbb E Z_{W,1}&gt;0$. But $|B|\chi-m_2&gt;0$, so the claimed right side is strictly positive. This contradiction applies to every choice of $\mu$.</p>
<p>Deleting vertices can take a cluster out of the singleton class $\{B\}$ even when a selected path survives. That is exactly the unsupported replacement of $F(H',z)$ by $F(H,z)$ in the source proof. Downward closure and consistent path selection repair that step for its intended applications, without claiming the stronger arbitrary-class statement.</p>

## From averaged cluster volume to short averaged paths {#section-reimer-path-conversion}

<a id="tag-X86B" data-assertion="proposition" data-title="Finite Reimer implies the averaged geodesic truncation bound on a countable graph"></a>
<p>Assume the finite-product Reimer inequality for arbitrary events: if $A,C$ are events in a finite Bernoulli product, and $A\mathbin\square C$ requires disjoint coordinate certificates recording both open and closed states, then $\mathbb P(A\mathbin\square C)\leq\mathbb P(A)\mathbb P(C)$. This is a separate literature input here; the wiki's increasing-event BK proof does not prove it.</p>
<p>In the finite-susceptibility invariant model of XFCJ, let $\nu$ be any probability measure on $\mathbb Z^d$, let $B$ be finite, and define</p>
<div class="math-display">$$V_\nu(H)=\sum_x\nu(x)|V(H)\cap(x+B)|,\qquad
L_\nu(P)=\sum_x\nu(x)|V(P)\cap(x+B)|.$$</div>
<p>For every deterministic $W$, every class $\mathscr A$ of finite cluster graphs, and $m,\ell&gt;0$,</p>
<div class="math-display">$$\begin{aligned}
&\mathbb E\sum_{z\in K_0^W}\mathbf1_{\{K_0^W\in\mathscr A,\ L_\nu(\gamma_{K_0^W}(0,z))\leq\ell\}}\\
&\quad\geq\mathbb E\bigl[|K_0^W|;K_0^W\in\mathscr A,\ V_\nu(K_0^W)\leq m\bigr]
-\frac\chi\ell\mathbb E\min(|K_0|,m).
\end{aligned}$$</div>
<p>No downward closure of $\mathscr A$ is needed in this assertion: its constraint is discarded when estimating the error.</p>
<p><em>Proof.</em> Work first in a finite edge restriction. Subtract from the displayed cluster-volume term the vertices whose selected path has $L_\nu&gt;\ell$, and omit $\mathscr A$ from this error. Markov's inequality bounds the error by</p>
<div class="math-display">$$\frac1\ell\sum_x\nu(x)\sum_{w\in x+B}\sum_z
\mathbb P\bigl(w\in\gamma_{K_0^W}(0,z),\ V_\nu(K_0^W)\leq m\bigr).$$</div>
<p>On the event in a summand, split the simple path at $w$. Its prefix, together with every closed edge in the finite restriction, certifies</p>
<div class="math-display">$$A_w=\{w\in K_0^W,\ V_\nu(K_0^W)\leq m\}.$$</div>
<p>Indeed, configurations agreeing with those certificates retain the prefix and can only remove edges from the current open graph; they cannot increase its nonnegative weighted cluster volume. The path suffix certifies $w\leftrightarrow z$ and uses none of those coordinates. Reimer therefore bounds the summand by $\mathbb P(A_w)\mathbb P(w\leftrightarrow z)$. Sum over $z$, using the full-model upper bound $\chi$ for the restricted susceptibility at any root. The error is at most</p>
<div class="math-display">$$\frac\chi\ell\mathbb E[V_\nu(K_0^W);V_\nu(K_0^W)\leq m]
\leq\frac\chi\ell\mathbb E\min(|K_0|,m),$$</div>
<p>since $V_\nu(K_0^W)\leq|K_0^W|\leq|K_0|$.</p>
<p>Finally exhaust the countable edge set by finite sets. The full root cluster is finite almost surely, and all its finitely many internal open edges eventually belong to the restriction. The restricted root cluster graph, its off-$W$ component, and the selected paths therefore eventually equal their full-model counterparts. Dominated convergence applies to the vertex counts, bounded by $|K_0|$, while the capped term converges by bounded convergence. This passes the finite inequality to the countable model without using an infinite closed-edge certificate in the finite Reimer theorem.</p>
<p>This proves the implication used in Lemma III.4.3, including its countable passage. The finite nonmonotone Reimer inequality remains an explicitly identified input, also needed in the separate chemical-distance comparison III.2.4(2).</p>


## Growth after a finite cluster history {#section-conditional-cluster-growth}

<a id="tag-WKM2" data-assertion="proposition" data-title="Unrevealed exponential clocks bound cluster growth with a decreasing volume test"></a>
<p>On the unordered edges of $\mathbb Z^d$, let $E_e$ be independent exponential variables of mean one. Open an edge of displacement $z$ at parameter $t$ when $E_e\leq k_t(z)$, where $k_t(z)=k_t(-z)\geq0$ is nondecreasing in $t$ and has finite off-diagonal row sum. Suppose the full susceptibility $\chi(t)$ is finite at the parameters considered. Fix a deterministic deleted set $W$, a root $y$, and finitely many parameters $s_1&lt;\cdots&lt;s_m=s&lt;t$. Let $H_i=V(K_y^{s_i,W})$, let $\mathcal F=\sigma(H_1,\ldots,H_m)$, and write $H=H_m$. Clusters are empty when their root is deleted.</p>
<p>Let $\Phi$ be a deterministic function on finite vertex sets, with $0\leq\Phi\leq1$ and $\Phi(A')\geq\Phi(A)$ whenever $A'\subseteq A$. Then, almost surely,</p>
<div class="math-display">$$\begin{aligned}
\mathbb E[|K_y^{t,W}|\Phi(V(K_y^{t,W}))\mid\mathcal F]
\leq |H|+\sum_{a\in H}\sum_{b\notin W\cup H}
\bigl(k_t(b-a)-k_s(b-a)\bigr)
\mathbb E_t[|K_b^{W\cup H}|\Phi(V(K_b^{W\cup H}))].
\end{aligned}$$</div>
<p>On the right, $H$ is its realized value and $\mathbb E_t$ denotes a fresh product configuration off the displayed deleted set. In particular, if $\rho_s\geq\sum_{z\ne0}(k_t(z)-k_s(z))$, then</p>
<div class="math-display">$$\mathbb E[|K_y^{t,W}|\mid\mathcal F]\leq |H|(1+\rho_s\chi(t)).$$</div>
<p><em>Proof.</em> Each history consists of finitely many finite vertex sets. Conditional on a possible history, its final exterior contains no revealed edge coordinate: both endpoints of an exterior edge lie outside every $H_i$. The history constrains each edge from $H$ to $\mathbb Z^d\setminus(W\cup H)$ only to be closed at parameter $s$. Earlier closure constraints are implied by this one. The exterior clocks therefore retain their product law, independently of the boundary residual clocks. By exponential memorylessness, a boundary edge opens by $t$ with conditional probability</p>
<div class="math-display">$$1-\exp\bigl(-(k_t-k_s)(b-a)\bigr)\leq(k_t-k_s)(b-a).$$</div>
<p>This factorization can be checked on each history atom: the final boundary is specified by the coordinate conditions $E_e&gt;k_s(e)$, and all remaining history information concerns internal edges. The finite row sum makes the total boundary rate finite. Thus the countable boundary creates no conditioning on a null event for a possible finite history.</p>
<p>For a vertex newly reached at $t$, take a simple open path from $y$ and its last edge exiting $H$. The remaining path stays in the exterior, so the vertex belongs to the exterior component attached to that boundary edge. Whenever the edge is open, its entire exterior component is a subset of $K_y^{t,W}$. Since $\Phi$ decreases under enlargement, that component's contribution with the test on the full cluster is bounded by its contribution with its own test. The old vertices contribute at most $|H|$. Sum these bounds over the boundary edges, use their independence from the exterior components, and apply the displayed conditional probability bound. Tonelli justifies the nonnegative countable sums. All expectations are finite, since each exterior susceptibility is at most $\chi(t)$ and the increment row is finite. Taking $\Phi=1$ proves the last assertion.</p>
<p>This estimate permits a decreasing upper-volume constraint without invoking increasing-event BK on that constraint. It will also be used after conditioning on another finite cluster: its exterior is again a product process on a deterministic deleted domain once the conditioning is fixed.</p>


## Keeping two root components separate {#section-suppressed-merger-likelihood}

<a id="tag-7IVI" data-assertion="theorem" data-title="Suppressing root mergers gives an exact integrated-hazard identity"></a>
<p>Let $G$ be a finite graph with distinct roots $u,v$. Independently on each edge $e$, place an inhomogeneous Poisson process of marks with nonnegative locally integrable rate $a_e(t)$. An edge is open once it has received a mark. Starting with singleton components, form a second process by accepting each proposed component merger except a merger between the component containing $u$ and the component containing $v$. Those mergers are suppressed. Write $A_t,B_t$ for these two permanently disjoint components.</p>
<p>For any nonnegative measurable functional $F$ of the two component histories through $T$,</p>
<div class="math-display">$$\mathbb E\left[F((K_u^t,K_v^t)_{0\leq t\leq T});u\nleftrightarrow_T v\right]
=\mathbb E\left[F((A_t,B_t)_{0\leq t\leq T})
\exp\left(-\int_0^T\sum_{\substack{e=\{a,b\}\in E(G)\\a\in A_t,\ b\in B_t}}a_e(t)\,dt\right)\right].$$</div>
<p>Moreover, with $\chi_u(T)=\mathbb E|K_u^T|$ and $\chi_v(T)=\mathbb E|K_v^T|$ in the original product law,</p>
<div class="math-display">$$\mathbb E[|A_T||B_T|]\leq\chi_u(T)\chi_v(T).$$</div>
<p><em>Proof.</em> Track the full partition, retaining a label on the two root components. In the suppressed process, a transition merges any two different components unless both carry root labels. Its rate is the sum of the rates of the edges between them. The original process, stopped with zero weight at the first root merger, has exactly the same allowed transitions. Its additional killing rate in a state with root components $A,B$ is</p>
<div class="math-display">$$h_t(A,B)=\sum_{\substack{e=\{a,b\}\in E(G)\\a\in A,\ b\in B}}a_e(t).$$</div>
<p>Fix an allowed finite sequence of partition states and jump times. In both processes its likelihood has the same product of transition rates. The waiting factor for the process killed at a root merger has the additional multiplier $\exp(-\int_0^T h_t(A_t,B_t)\,dt)$. There are at most $|V(G)|-2$ accepted mergers, and the total mark intensity on a bounded time interval is finite. Summing and integrating over the possible histories proves the identity, first for indicator functionals and then for all nonnegative $F$ by monotone convergence. The two processes coincide up to the first suppressed merger, so on the event of no original root connection their root histories agree. Values at the finitely many jump times do not affect the integral.</p>
<p>Every suppressed component is connected by accepted edges, hence by edges open in the original terminal configuration. For positive integers $m,n$, the event $|A_T|\geq m$, $|B_T|\geq n$ therefore supplies two vertex-disjoint finite rooted trees, and consequently disjoint open-edge witnesses for $|K_u^T|\geq m$ and $|K_v^T|\geq n$. The <a href="/tag/BNY8/">finite BK inequality</a> bounds this event by the product of those two probabilities. Summing over $m,n$ proves the moment bound.</p>
<p>The identity is a comparison of finite process laws. It does not assume independence of merging attempts selected from a random component history. Its integrated rate remains valid when the same edge contributes during several disjoint time intervals.</p>


## The first merger of two root components {#section-first-connection-identity}

<a id="tag-88ZH" data-assertion="proposition" data-title="The first connection has the crossing-edge compensator"></a>
<p>Let $G$ be a finite simple graph with distinct roots $u,v$. Give each edge an independent Poisson process with deterministic nonnegative locally integrable rate $a_e(t)$, and open the edge at its first mark. Put $R=\inf\{t:u\leftrightarrow_t v\}$, with $R=\infty$ if the roots never connect. For every $T&lt;\infty$ and every nonnegative measurable function $g(t,C)$ of a time and a vertex set,</p>
<div class="math-display">$$\mathbb E[\mathbf1_{\{R\leq T\}}g(R,K_u^R)]
=\int_0^T\mathbb E\left[\mathbf1_{\{u\nleftrightarrow_t v\}}
 g(t,K_u^t\cup K_v^t)
 \sum_{\substack{a\in K_u^t,\ b\in K_v^t\\\{a,b\}\in E(G)}}a_{\{a,b\}}(t)\right]dt.$$</div>
<p>The payoff on the left is defined to be zero when $R&gt;T$.</p>
<p><em>Proof.</em> Before the roots connect, a mark joins them precisely when its edge runs between their two components. That merger changes the root component to their union, and it happens at most once. In the partition process, the rate of this transition from a state with root components $A,B$ is $\sum_{a\in A,b\in B}a_{\{a,b\}}(t)$.</p>
<p>For completeness, fix a sequence of partition states before this transition. Its jump-time density is the product of the transition rates and the exponential waiting factors. Appending a root merger at time $t$ multiplies this density by the displayed crossing rate and by $dt$; its payoff is $g(t,A\cup B)$. Sum over the finitely many possible partition sequences and integrate their earlier jump times. The result is the integral on the right with the components just before $t$. There are at most $|V(G)|-1$ mergers. Since the edge intensities are absolutely continuous in time, each deterministic $t$ is almost surely not a jump time, so the pre-jump components may be replaced by $K_u^t,K_v^t$ in the integral. Truncation and monotone convergence cover unbounded $g$.</p>
<p>Each unordered crossing edge appears once, with its endpoint in $K_u^t$ written first. There is no factor two. Unlike the <a href="/tag/7IVI/">suppressed-merger identity</a>, this formula records the first merger itself.</p>

## Weighted growth after the first connection {#section-first-connection-growth}

<a id="tag-DTOX" data-assertion="theorem" data-title="The stopped root history leaves a fresh exterior for weighted growth"></a>
<p>In the finite model of <a href="/tag/88ZH/">88ZH</a>, write $k_t(e)=\int_0^t a_e(s)\,ds$ and fix a deterministic nonnegative vertex weight $w$. Let</p>
<div class="math-display">$$\mathcal G=\sigma\left(R\wedge T,(K_u^{s\wedge R\wedge T})_{0\leq s\leq T}\right).$$</div>
<p>This records the stopped root-component history, not the partition of the whole graph. On $\{R\leq T\}$ set $H=K_u^R$. If $K_b^{T,H}$ denotes a fresh terminal component in the graph with $H$ deleted, then almost surely on this event,</p>
<div class="math-display">$$\mathbb E\left[\sum_{z\in K_u^T}w(z)\,\middle|\,\mathcal G\right]
\leq\sum_{a\in H}w(a)
+\sum_{\substack{a\in H,\ b\notin H\\\{a,b\}\in E(G)}}
\bigl(k_T(\{a,b\})-k_R(\{a,b\})\bigr)
\mathbb E_T\left[\sum_{z\in K_b^{T,H}}w(z)\right].$$</div>
<p>On the right, $H$ and $R$ have their realized values, and $\mathbb E_T$ is an independent product law on the remaining edges.</p>
<p><em>Proof.</em> Realize the opening process by independent mean-one exponential clocks $E_e$, opening $e$ when $E_e\leq k_t(e)$. We first justify its law conditional on $\mathcal G$. Fix a possible value $H$ of the component at the first connection. In the graph induced by $H$, the first connection time, the root history up to that time, and the condition that the root then fills $H$ depend only on internal clocks. This internal history is also the history in the full graph, with final component exactly $H$, if and only if every boundary clock satisfies $E_e&gt;k_R(e)$. These final closure conditions imply all the earlier boundary closure conditions. No edge with both endpoints outside $H$ occurs in this description.</p>
<p>Fixing the internal clocks first therefore leaves the exterior clocks independent with their original law. Conditional on the boundary inequalities, the variables $E_e-k_R(e)$ on the boundary are independent mean-one exponentials, independently of the exterior. Disintegrating over the internal clocks preserves this description: their influence on the boundary residual law is only through the recorded time $R$. This proves the factorization even though $R$ has no atoms; no conditioning on a positive-probability event of the form $\{R=s\}$ is being assumed.</p>
<p>Every vertex of $K_u^T\setminus H$ can be reached by a simple terminal open path. After its last exit from $H$, that path stays outside $H$. Hence the vertex belongs to an exterior component attached to a boundary edge that was closed at $R$ and is open at $T$. Bound the weight of the union of these components by the sum of their weights. The old vertices contribute $\sum_{a\in H}w(a)$. Conditional independence now bounds the contribution of a boundary edge by</p>
<div class="math-display">$$\left(1-e^{-(k_T(e)-k_R(e))}\right)
\mathbb E_T\sum_{z\in K_b^{T,H}}w(z)
\leq (k_T(e)-k_R(e))\mathbb E_T\sum_{z\in K_b^{T,H}}w(z).$$</div>
<p>Summing proves the assertion. The argument uses only the stopped root history. Revealing the full exterior configuration before stopping would not leave the fresh product law used here.</p>
<p>The deterministic-time history estimate <a href="/tag/WKM2/">WKM2</a> allows a decreasing test on the final volume. The present result instead permits arbitrary nonnegative spatial weights and proves the conditional law at the first-connection time.</p>


## Spatial weights along critical geodesics {#section-critical-weighted-geodesics}

<a id="tag-V7V5" data-assertion="theorem" data-title="Spatially weighted geodesic moments are negligible at the critical dimension"></a>
<p>Assume the normalized radial model and hypotheses of <a href="/tag/7GBI/">7GBI</a>: $d=3\alpha$, $0&lt;\alpha&lt;2$, $\chi_r\sim(\alpha/\beta_c)r^\alpha$, and $\widetilde M_0(r)=o(r^{2\alpha})$. Choose the geodesics of <a href="/tag/BN7Z/">BN7Z</a>. For $a\in K_0$ write $\gamma_a=\gamma_{K_0}(0,a)$ and</p>
<div class="math-display">$$L_a=|V(\gamma_a)|=d_\omega(0,a)+1.$$</div>
<p>For every pair of integers $p,q\geq0$,</p>
<div class="math-display">$$\mathbb E_r\sum_{a\in K_0}L_a^q\sum_{b\in V(\gamma_a)}\|b\|^p
=o\bigl(r^{(q+2)\alpha+p}\bigr)\qquad(r\to\infty).$$</div>
<p>Norm powers of degree zero are one, including at the origin. The estimate also holds with $d_\omega(0,a)^q$ in place of $L_a^q$. Both endpoints are included in every path; in particular $L_0=1$.</p>
<p><em>Proof.</em> First we verify the pivotal-rate input to <a href="/tag/T9LZ/">T9LZ</a> at the fixed intensity $\beta_c$. The cutoff kernel is $J_r(z)=(J(z)-j(r))_+$. If $J_* =\sup_{z\ne0}J(z)$, then, for each sufficiently large finite $r$,</p>
<div class="math-display">$$J_r\leq(1-j(r)/J_*)J.$$</div>
<p>Choose $\beta_+&gt;\beta_c$ so close to $\beta_c$ that $\beta_+(1-j(r)/J_*)&lt;\beta_c$. The comparison used in <a href="/tag/DR1W/">DR1W</a> now gives finite cutoff susceptibility and all cluster-volume moments on an open intensity interval containing $\beta_c$. The cutoff weight row is at most the full, finite weight row $M$.</p>
<p>By <a href="/tag/NMYK/">NMYK</a> the intensity derivative is the continuous pivotal rate $G_r$. The integrated <a href="/tag/UTUF/">score inequality</a> gives</p>
<div class="math-display">$$G_r(\beta_c)^2\leq\frac M{\beta_c}\chi_rm_2(r).$$</div>
<p>Here the inequality holds at $\beta_c$, not just at almost every intensity. Indeed the nearby moments are continuous: in the uniform coupling they are dominated by the finite cluster at $\beta_+$, whose second moment is integrable, and each edge in that finite cluster has almost surely no threshold at the chosen intensity. Divide the integrated score inequality by the interval length and let that length tend to zero.</p>
<p>Now <a href="/tag/5J3U/">5J3U</a> gives $m_2=o(\chi_r^3)$, so $G_r(\beta_c)=o(\chi_r^2)$. T9LZ yields, for each integer $k\geq1$,</p>
<div class="math-display">$$\mathbb E_r\sum_{a\in K_0}L_a^k=o(\chi_r^{k+1})=o(r^{(k+1)\alpha}).$$</div>
<p>Adding one to the distance costs at most $2^{k-1}\chi_r$ in addition to the distance-moment term, and $\chi_r\to\infty$.</p>
<p>For each marked target $a$, choose $Z_a$ uniformly from the $L_a$ vertices of $\gamma_a$, conditionally on the configuration. These auxiliary choices need not be independent. Splitting the path at $b$ gives edge-disjoint connections from $0$ to $b$ and from $b$ to $a$, with empty witnesses allowed at the endpoints. Thus BK and <a href="/tag/YU52/">YU52</a> imply, for every integer $s\geq0$,</p>
<div class="math-display">$$\begin{aligned}
\mathbb E_r\sum_{a\in K_0}L_a\|Z_a\|^s
&=\sum_{a,b}\|b\|^s\mathbb P_r(b\in V(\gamma_a))\\
&\leq\sum_{a,b}\|b\|^s\tau_r(0,b)\tau_r(b,a)
=\chi_r\mathbb E_r\sum_{b\in K_0}\|b\|^s
=O_s(r^{2\alpha+s}).
\end{aligned}$$</div>
<p>Off the event $a\in K_0$, the path event has probability zero. All sums are nonnegative. Cauchy–Schwarz for the measure that sums over the marked target and averages over the configuration and auxiliary vertex gives</p>
<div class="math-display">$$\begin{aligned}
\mathbb E_r\sum_{a\in K_0}L_a^q\sum_{b\in V(\gamma_a)}\|b\|^p
&=\mathbb E_r\sum_{a\in K_0}L_a^{q+1}\|Z_a\|^p\\
&\leq\left(\mathbb E_r\sum_{a\in K_0}L_a^{2q+1}\right)^{1/2}
\left(\mathbb E_r\sum_{a\in K_0}L_a\|Z_a\|^{2p}\right)^{1/2}\\
&=o(r^{(q+2)\alpha+p}).
\end{aligned}$$</div>
<p>The case $q=0$ uses the first distance moment, so no zero-moment negligibility is needed. This proves the critical case of Lemma III.6.18 with its target variable bound and an explicit vertex-count convention. The source prints a free $x$ where the summed target is $a$; the <a href="/errata/hutchcroft-lrp-3/">errata record</a> treats this as a provisional index correction. The probabilistic hypotheses retain the conditional finite-Reimer dependency of the hydrodynamic results.</p>

## Two independent clusters hitting one path {#section-critical-double-path-hit}

<a id="tag-SE64" data-assertion="theorem" data-title="The weighted double-hit geodesic diagram is negligible at criticality"></a>
<p>Under the hypotheses of V7V5, suppress the cutoff subscript and put</p>
<div class="math-display">$$A(b)=\mathbb E[|K_0|\mathbf1_{\{b\in K_0\}}],\qquad
C(x,c,z)=\mathbb E[|K_x|\mathbf1_{\{c,z\in K_x\}}],\qquad
H(y,a;b,c)=\mathbb P(b,c\in V(\gamma_{K_y}(y,a))).$$</div>
<p>The last event is empty if $a\notin K_y$. For integers $p,q\geq0$, with $s=p+q$, the following sum over all six vertices in $\mathbb Z^d$ is finite and satisfies</p>
<div class="math-display">$$\mathcal R_{p,q}(r):=
\sum_{x,y,a,b,c,z} A(b)C(x,c,z)H(y,a;b,c)\|y\|^p\|z\|^q
=o\bigl(V_r^3r^{11\alpha+s}\bigr).$$</div>
<p>Since $|B_r|\asymp r^{3\alpha}$ and $\chi_r\asymp r^\alpha$, this is also $o(|B_r|V_r^3r^s\chi_r^8)$. In particular it bounds the corresponding weighted sum, over $x,y$ and targets $a$, of the event that two independent clusters rooted at $0$ and $x$ both meet a selected path from $y$ to $a$ in a third independent configuration. Restricting $x$ to $B_r$ only decreases the sum.</p>
<p><em>Proof.</em> Write $X=|K_0|$, $m_k=\mathbb E X^k$, and</p>
<div class="math-display">$$U_{k,s}=\mathbb E\left[X^{k-1}\sum_{v\in K_0}\|v\|^s\right],\qquad
P_2=\mathbb E\sum_{a\in K_0}L_a^2,\qquad
P_s=\mathbb E\sum_{a\in K_0}L_a\sum_{b\in V(\gamma_a)}\|b\|^s.$$</div>
<p>With the volume premise supplied by <a href="/tag/RM79/">RM79</a>, the mixed-moment bound <a href="/tag/AR3F/">AR3F</a> gives</p>
<div class="math-display">$$U_{2,s}=O(V_rr^{3\alpha+s}),\qquad
U_{3,s}=O(V_r^2r^{5\alpha+s}).$$</div>
<p>In particular $U_{k,0}=m_k$. V7V5 gives $P_2=o(r^{3\alpha})$ and $P_s=o(r^{3\alpha+s})$.</p>
<p>The relations $y=b+(y-b)$ and $z=(z-c)+(c-y)+y$ imply</p>
<div class="math-display">$$\|y\|^p\|z\|^q\leq C_{p,q}
\bigl(\|b\|^s+\|y-b\|^s+\|y-c\|^s+\|z-c\|^s\bigr).$$</div>
<p>For $s=0$ this simply bounds one by four. The sums obtained by replacing the weight in $\mathcal R_{p,q}$ by the four terms on the right are, in that order, exactly</p>
<div class="math-display">$$U_{2,s}m_3P_2,\qquad m_2m_3P_s,\qquad
m_2m_3P_s,\qquad m_2U_{3,s}P_2.$$</div>
<p>Here are the summation identities behind these equalities. Tonelli and equality of connected clusters give, for fixed $c$,</p>
<div class="math-display">$$\sum_{x,z}C(x,c,z)=m_3,\qquad
\sum_{x,z}C(x,c,z)\|z-c\|^s=U_{3,s},\qquad
\sum_bA(b)=m_2.$$</div>
<p>For example, on $c\in K_x$, one has $K_x=K_c$; summing $x\in K_c$ supplies one cluster-size factor and summing $z\in K_c$ supplies the other. Also, for fixed $b$, translation equivariance of the selected path gives</p>
<div class="math-display">$$\sum_{y,a,c}H(y,a;b,c)=P_2,\qquad
\sum_{y,a,c}H(y,a;b,c)\|y-b\|^s=P_s.$$</div>
<p>To check these formulas, translate by $-y$, then let $b-y$ range over the vertices of the path from $0$ to $a-y$; the sum over $c-y$ counts its $L_{a-y}$ vertices. Weighting by $\|y-c\|^s$ gives the same result after exchanging the two path marks. These changes of variables require no reflection covariance of the chosen geodesic.</p>
<p>Each of the four expressions is $o(V_r^3r^{11\alpha+s})$ by the displayed moment bounds. This also proves finiteness. Finally, whenever both independent clusters meet the third path, choose intersection vertices $b,c$ and apply the union bound. Independence gives the product $A(b)C(x,c,z)H(y,a;b,c)$ after expanding the spatial sum over $z$. This proves the event bound without applying BK to the event that a particular geodesic is selected.</p>
<p>This supplies the independent-cluster diagram used for the redundancy error in Lemma III.6.15, including all four spatial-weight placements. Applying it to a coupled cut event still requires proving that the coupled cluster is contained in its independent comparison cluster and that both cuts force path intersections. The full triple-interaction approximation is not asserted here.</p>


## Retaining the interception point {#section-interception-diagram}

<a id="tag-ZGVN" data-assertion="proposition" data-title="The printed interception diagram diverges after the root-to-path link is dropped"></a>
<p>Let a translation-invariant independent-bond law on $\mathbb Z^d$, $d\geq1$, have finite $\chi=\mathbb E|K_0|$ and $m_2=\mathbb E|K_0|^2$. Suppose that some edge $\{0,v\}$, $v\ne0$, has positive opening probability. With inclusive selected geodesics, the degree-zero diagram printed in the proof of Lemma III.6.17 is</p>
<div class="math-display">$$\sum_{x,y,a,b,c}
\mathbb E[|K_0|\mathbf1_{\{c\in K_0\}}]
\mathbb E[|K_x|^2\mathbf1_{\{b\in K_x\}}]
\mathbb P(a\in K_y,\ b\in V(\gamma_{K_y}(y,a))).$$</div>
<p>This sum is infinite.</p>
<p><em>Proof.</em> Keep only $c=0$, $b=a=x$, and $y=x-v$. For each $x$, the first two factors are $\chi$ and $m_2$. The last factor is $\tau(0,v)&gt;0$, since the terminal vertex belongs to every path to it. Thus restricting $x$ to any finite set $F$ already gives $|F|\chi m_2\tau(0,v)$. Let $F$ increase to the lattice. This argument uses nonzero-length connections and is unchanged if the initial path vertex is omitted.</p>
<p>In particular this applies to every sufficiently large finite radial cutoff at positive intensity. The display occurs in both the versioned HTML and PDF. It remains an upper bound by infinity, but cannot give the finite little-o estimate claimed immediately afterward. The <a href="/errata/hutchcroft-lrp-3/">provisional erratum</a> concerns this proof step, not a counterexample to Lemma III.6.17 or the final theorem.</p>

<a id="tag-IEOH" data-assertion="theorem" data-title="The interception diagram is negligible when the root-cluster mark is retained on the second path"></a>
<p>Under the critical hypotheses of <a href="/tag/V7V5/">V7V5</a>, define</p>
<div class="math-display">$$D(x,b,c,z)=\mathbb E_r\left[|K_x|\mathbf1_{\{z\in K_x,\ c\in V(\gamma_{K_x}(x,b))\}}\right],\qquad
H_1(y,a;b)=\mathbb P_r(b\in V(\gamma_{K_y}(y,a))).$$</div>
<p>A path event is empty when its endpoints are disconnected. With $A(c)=\mathbb E_r[|K_0|\mathbf1_{\{c\in K_0\}}]$, for every pair of integers $p,q\geq0$, $s=p+q$,</p>
<div class="math-display">$$\mathcal I_{p,q}(r):=
\sum_{x,y,a,b,c,z}A(c)D(x,b,c,z)H_1(y,a;b)\|y\|^p\|z\|^q
=o(V_r^3r^{11\alpha+s}).$$</div>
<p>All sums are finite. This is an independent-configuration diagram: the mark $c$ joins the root-cluster factor to the selected path from $x$ to $b$, and $b$ lies on the third configuration's selected path from $y$ to $a$.</p>
<p><em>Proof.</em> In one configuration rooted at zero write $X=|K_0|$, $W_s=\sum_{z\in K_0}\|z\|^s$, and use $L_b$, $P_2$, $P_s$, $U_{k,s}$ as in SE64. Put</p>
<div class="math-display">$$\begin{aligned}
G_s&=\mathbb E_r\sum_{a\in K_0}\sum_{b\in V(\gamma_a)}\|b\|^s,\\
F_0&=\mathbb E_r\left[X^2\sum_{b\in K_0}L_b\right],\\
F_{b,s}&=\mathbb E_r\left[X^2\sum_{b\in K_0}\sum_{c\in V(\gamma_b)}\|b-c\|^s\right],\\
F_{z,s}&=\mathbb E_r\left[X\sum_{b\in K_0}\sum_{c\in V(\gamma_b)}\sum_{z\in K_0}\|z-c\|^s\right].
\end{aligned}$$</div>
<p>V7V5 gives $G_s=o(r^{2\alpha+s})$, $P_2=o(r^{3\alpha})$, and $P_{2s}=o(r^{3\alpha+2s})$. AR3F and RM79 give</p>
<div class="math-display">$$m_5=O(V_r^4r^{9\alpha}),\quad
U_{5,2s}=O(V_r^4r^{9\alpha+2s}),\quad
\mathbb E_r[X^3W_s^2]=O(V_r^4r^{9\alpha+2s}).$$</div>
<p>The last two bounds have five marked cluster vertices; their total spatial degree is $2s$. Cauchy–Schwarz over the configuration and the marked target yields</p>
<div class="math-display">$$F_0\leq\sqrt{m_5P_2}=o(V_r^2r^{6\alpha}),\qquad
\mathbb E_r\left[X^2\sum_{b\in K_0}L_b\|b\|^s\right]
\leq\sqrt{U_{5,2s}P_2}=o(V_r^2r^{6\alpha+s}).$$</div>
<p>For the other path weight, choose a uniform vertex $Z_b$ of $\gamma_b$ as in V7V5. Applying Cauchy–Schwarz to $X^2$ and $L_b\|Z_b\|^s$ gives</p>
<div class="math-display">$$\mathbb E_r\left[X^2\sum_{b\in K_0}\sum_{c\in V(\gamma_b)}\|c\|^s\right]
\leq\sqrt{m_5P_{2s}}=o(V_r^2r^{6\alpha+s}).$$</div>
<p>Since $\|b-c\|^s\leq C_s(\|b\|^s+\|c\|^s)$, these bounds imply $F_{b,s}=o(V_r^2r^{6\alpha+s})$. For $F_{z,s}$ split $\|z-c\|^s$ in the same way. Its $c$ term has just been bounded, and its $z$ term is at most</p>
<div class="math-display">$$\mathbb E_r\left[XW_s\sum_{b\in K_0}L_b\right]
\leq\sqrt{\mathbb E_r[X^3W_s^2]P_2}
=o(V_r^2r^{6\alpha+s}).$$</div>
<p>Thus $F_{z,s}$ has the same bound. These estimates include $s=0$.</p>
<p>Finally use $y=c+(b-c)+(y-b)$ and $z=c+(z-c)$ to bound the original weight by a constant times</p>
<div class="math-display">$$\|c\|^s+\|y-b\|^s+\|b-c\|^s+\|z-c\|^s.$$</div>
<p>Translation equivariance, first for the path rooted at $y$ and then for the path rooted at $x$, makes the four sums exactly</p>
<div class="math-display">$$U_{2,s}F_0G_0,\qquad m_2F_0G_s,\qquad
m_2F_{b,s}G_0,\qquad m_2F_{z,s}G_0.$$</div>
<p>For example, at fixed $b$, summing $y,a$ with weight $\|y-b\|^s$ gives $G_s$. At fixed $c$, translate the second path by $-x$; the sum over $x$ becomes the sum over its marked vertex $c-x$. Summing $z$ supplies the second factor of $X$ in $F_0$ or $F_{b,s}$, whereas retaining its weight gives $F_{z,s}$. The remaining sum over $c$ is $m_2$ or $U_{2,s}$. Tonelli justifies these operations. Substitution of the preceding bounds and $U_{2,s}=O(V_rr^{3\alpha+s})$ proves the assertion.</p>
<p>This supplies a finite negligible diagram with the missing geometric relation retained. It does not yet justify replacing the source's coupled interception event by this diagram. In particular, survival of a connection after deleting a set does not say that its original selected geodesic survives. A path selected in the restricted graph depends on that deletion; its law cannot simply be replaced by an independent unrestricted path. That reduction remains an explicit obligation.</p>


## The redundancy term in the cluster coupling {#section-coupled-redundancy}

<a id="tag-KF1W" data-assertion="theorem" data-title="Two coupled cuts have a negligible critical redundancy term"></a>
<p>Assume the hypotheses of <a href="/tag/SE64/">SE64</a>. For each $x,y$, take the independent copies and sets $A,B,C$ of <a href="/tag/DR5Q/">DR5Q</a>, so $A$ is the first root cluster, $C$ is the independent $x$-cluster and $B$ is its restriction off $A$. Let $W_q(S)=\sum_{z\in S}\|z\|^q$. For all integers $p,q\geq0$,</p>
<div class="math-display">$$\begin{aligned}
&\sum_{x\in B_r}\sum_{y,a}\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|\,|B|W_q(B)
\mathbf1_{\mathcal D_A(y,a)\cap\mathcal D_C(y,a)}\right]\\
&\qquad\leq\mathcal R_{p,q}(r)
=o\bigl(|B_r|V_r^3r^{p+q}\chi_r^8\bigr),
\end{aligned}$$</div>
<p>where $\mathcal R_{p,q}$ is the finite double-hit diagram in SE64. Zero powers are one.</p>
<p><em>Proof.</em> If both cuts occur, $a$ belongs to the third independent cluster $H=K_y(\omega_y)$, and every $y$–$a$ path in that configuration meets both $A$ and $C$. In particular its selected geodesic contains some $b\in A$ and some $c\in C$, allowing the two marks to coincide. These intersections also hold when a cut deletes an endpoint, since geodesics include their endpoints.</p>
<p>On $x\notin A$, DR5Q identifies the coupled $x$-cluster with $B\subseteq C$. Thus $|B|W_q(B)\leq|C|W_q(C)$. Drop the restriction on $x$, expand the latter spatial sum over $z\in C$, and take the union bound over the path marks $b,c$. Independence of $\omega_0,\omega_x,\omega_y$ gives</p>
<div class="math-display">$$\sum_{x,y,a,b,c,z}
\mathbb E_r[|K_0|\mathbf1_{\{b\in K_0\}}]
\mathbb E_r[|K_x|\mathbf1_{\{c,z\in K_x\}}]
\mathbb P_r(b,c\in V(\gamma_{K_y}(y,a)))\|y\|^p\|z\|^q,$$</div>
<p>which is precisely $\mathcal R_{p,q}$. Its finiteness and the required estimate were proved in SE64. No BK inequality is applied to the event that a particular geodesic was selected.</p>
<p>This supplies the coupling-to-diagram step left open after SE64 and proves Lemma III.6.15 at $d=3\alpha$, $\alpha&lt;2$, under the stated hydrodynamic hypotheses. The path is selected in the original independent third configuration. No claim is made here about the distribution of a path selected after deletion; that distinction remains relevant to the separate interception problem.</p>


## Cluster powers in the double-hit estimate {#section-powered-double-hit}

<a id="tag-DVHL" data-assertion="theorem" data-title="The critical double-hit gain survives arbitrary cluster powers"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>. For nonnegative integers $i,j,t$, define</p>
<div class="math-display">$$A_i(b)=\mathbb E_r[|K_0|^i\mathbf1_{\{b\in K_0\}}],\qquad
C_j(x,c,z)=\mathbb E_r[|K_x|^j\mathbf1_{\{c,z\in K_x\}}],$$</div>
<div class="math-display">$$H_t(y,a;b,c)=\mathbb E_r[|K_y|^t\mathbf1_{\{b,c\in V(\gamma_{K_y}(y,a))\}}].$$</div>
<p>The path event is empty when $a\notin K_y$. For nonnegative integers $p,q$, set $s=p+q$ and $n=i+j+t+1$. Then</p>
<div class="math-display">$$\begin{aligned}
\mathcal R^{i,j,t}_{p,q}(r)
&:=\sum_{x,y,a,b,c,z}A_i(b)C_j(x,c,z)H_t(y,a;b,c)\|y\|^p\|z\|^q\\
&=o\bigl(V_r^n r^{(2n+5)\alpha+s}\bigr)
=o\bigl(|B_r|V_r^n r^s\chi_r^{2n+2}\bigr).
\end{aligned}$$</div>
<p>All sums are finite, and zero powers are one. With the independent clusters and deletion cuts of <a href="/tag/DR5Q/">DR5Q</a>, the same bound holds for</p>
<div class="math-display">$$\sum_{x\in B_r}\sum_{y,a}\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|^i|B|^jW_q(B)|H|^t
\mathbf1_{\mathcal D_A(y,a)\cap\mathcal D_C(y,a)}\right],
\qquad W_q(S)=\sum_{z\in S}\|z\|^q.$$</div>
<p><em>Proof.</em> Use $X=|K_0|$, $m_k=\mathbb E_rX^k$, and $U_{k,s}=\mathbb E_r[X^{k-1}W_s(K_0)]$. The volume bound <a href="/tag/RM79/">RM79</a> and mixed moments <a href="/tag/AR3F/">AR3F</a> give, for every $k\geq1$,</p>
<div class="math-display">$$m_k=O(V_r^{k-1}r^{(2k-1)\alpha}),\qquad
U_{k,s}=O(V_r^{k-1}r^{(2k-1)\alpha+s}).$$</div>
<p>Write $L_a=|V(\gamma_{K_0}(0,a))|$ for the inclusive path length. The path factors now needed are</p>
<div class="math-display">$$T_t=\mathbb E_r\sum_{a\in K_0}X^tL_a^2,\qquad
S_{t,s}=\mathbb E_r\sum_{a\in K_0}X^tL_a\sum_{b\in V(\gamma_a)}\|b\|^s.$$</div>
<p>Cauchy–Schwarz under the measure which sums over the target $a$ gives</p>
<div class="math-display">$$T_t^2\leq m_{2t+1}\,\mathbb E_r\sum_{a\in K_0}L_a^4,
\qquad
S_{t,s}^2\leq m_{2t+1}\,\mathbb E_r\sum_{a\in K_0}L_a^3
\sum_{b\in V(\gamma_a)}\|b\|^{2s}.$$</div>
<p>For the second inequality, first use $(\sum_b\|b\|^s)^2\leq L_a\sum_b\|b\|^{2s}$. By <a href="/tag/V7V5/">V7V5</a>, the two path expectations on the right are $o(r^{5\alpha})$ and $o(r^{5\alpha+2s})$. Thus</p>
<div class="math-display">$$T_t=o(V_r^t r^{(2t+3)\alpha}),\qquad
S_{t,s}=o(V_r^t r^{(2t+3)\alpha+s}).$$</div>
<p>The four-weight inequality of <a href="/tag/SE64/">SE64</a> reduces the diagram to a constant times the sum of</p>
<div class="math-display">$$U_{i+1,s}m_{j+2}T_t,\qquad
m_{i+1}m_{j+2}S_{t,s},\qquad
m_{i+1}m_{j+2}S_{t,s},\qquad
m_{i+1}U_{j+2,s}T_t.$$</div>
<p>These are exact summation identities for weights on $b$, $y-b$, $y-c$, and $z-c$, respectively. Summing the first root mark gives $m_{i+1}$; summing the root and spatial mark in the second cluster gives $m_{j+2}$. Translating the selected third path to root zero gives $T_t$ or $S_{t,s}$, with its cluster-size factor unchanged. The same reasoning applies at $i=0$, $j=0$ or $t=0$: all moment indices stay at least one. Substitution proves the stated order and finiteness.</p>
<p>For the coupled bound, both cuts force the original third-copy geodesic to meet $A$ and $C$. Replace $|B|^jW_q(B)$ by $|C|^jW_q(C)$, use a union bound over the two intersection marks, and apply independence of the three copies. This is precisely the displayed diagram. The additional factor $|H|^t$ has been retained throughout.</p>
<p>This result controls redundancy when both cuts affect the same marked target, with arbitrary extra third-cluster marks supplied through $|H|^t$. A loss of a cluster power is a loss of target tuples; two cuts can affect different coordinates of such a tuple. That further contribution is not identified with this single-path event.</p>


## Redundancy for target tuples {#section-tuple-redundancy}

<a id="tag-6IJQ" data-assertion="theorem" data-title="The critical redundancy error is negligible for every target-tuple power"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>, and use the independent copies and sets $A,B,C,H$ from DR5Q. For a tuple $\boldsymbol a=(a_1,\ldots,a_m)\in H^m$, write</p>
<div class="math-display">$$\mathcal D_S^{[m]}(\boldsymbol a)
=\{a_k\notin H_S\text{ for at least one }k\},\qquad
H_S=K_y(\omega_y|_{S^c}).$$</div>
<p>Let $i,j,p,q\geq0$ and $m\geq1$ be integers, and set $n=i+j+m$, $s=p+q$. Then</p>
<div class="math-display">$$\begin{aligned}
&\sum_{x\in B_r}\sum_y\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|^i|B|^jW_q(B)
\sum_{\boldsymbol a\in H^m}
\mathbf1_{\mathcal D_A^{[m]}(\boldsymbol a)\cap\mathcal D_C^{[m]}(\boldsymbol a)}\right]\\
&\qquad=o\bigl(|B_r|V_r^n r^s\chi_r^{2n+2}\bigr).
\end{aligned}$$</div>
<p><em>Proof.</em> Each cut removes some coordinate of the tuple. If both cuts remove the same coordinate, summing over its position and all other coordinates bounds the contribution by</p>
<div class="math-display">$$m|H|^{m-1}\sum_a\mathbf1_{\mathcal D_A(y,a)\cap\mathcal D_C(y,a)}.$$</div>
<p>Its weighted expectation has the required order by <a href="/tag/DVHL/">DVHL</a> with $t=m-1$. For $m\geq2$, the contribution from different coordinates is at most</p>
<div class="math-display">$$m(m-1)|H|^{m-2}\sum_{a,d}
\mathbf1_{\mathcal D_A(y,a)}\mathbf1_{\mathcal D_C(y,d)}.$$</div>
<p>The two target values may coincide; the distinction is between their positions in the tuple. Each cut forces its own original third-copy geodesic to hit the corresponding independent cluster. After replacing $B$ by $C$ in the nonnegative weight, the union bound gives a two-path diagram whose third factor is</p>
<div class="math-display">$$H_t^{(2)}(y,a,d;b,c)
=\mathbb E_r[|K_y|^t\mathbf1_{\{b\in V(\gamma(y,a)),\ c\in V(\gamma(y,d))\}}],
\qquad t=m-2.$$</div>
<p>To estimate it, root the third cluster at zero and put</p>
<div class="math-display">$$Z=\sum_{a\in K_0}L_a,\qquad
Y_s=\sum_{a\in K_0}\sum_{b\in V(\gamma_a)}\|b\|^s,
\qquad Q_t=\mathbb E_r[X^tZ^2],\quad Q_{t,s}=\mathbb E_r[X^tZY_s].$$</div>
<p>With $T_t,S_{t,s}$ as in DVHL, Cauchy–Schwarz first over targets and then over configurations gives</p>
<div class="math-display">$$Q_t\leq T_{t+1},\qquad
Q_{t,s}\leq\sqrt{T_{t+1}S_{t+1,2s}}.$$</div>
<p>Indeed $Z^2\leq X\sum_aL_a^2$ and $Y_s^2\leq X\sum_a(\sum_{b\in\gamma_a}\|b\|^s)^2\leq X\sum_aL_a\sum_{b\in\gamma_a}\|b\|^{2s}$. Hence</p>
<div class="math-display">$$Q_t=o(V_r^{t+1}r^{(2t+5)\alpha}),\qquad
Q_{t,s}=o(V_r^{t+1}r^{(2t+5)\alpha+s}).$$</div>
<p>The four spatial-weight sums in the two-path diagram are</p>
<div class="math-display">$$U_{i+1,s}m_{j+2}Q_t,\qquad
m_{i+1}m_{j+2}Q_{t,s},\qquad
m_{i+1}m_{j+2}Q_{t,s},\qquad
m_{i+1}U_{j+2,s}Q_t.$$</div>
<p>Translation turns the sum over the two targets and their path marks into $Z^2$ or $ZY_s$; the remaining cluster summations are those of DVHL. The two middle expressions agree by exchanging the target paths. Substituting the moment bounds from DVHL gives $o(V_r^{i+j+t+2}r^{(2i+2j+2t+9)\alpha+s})$. Since $t=m-2$, this is the asserted scale. It also proves finiteness of the different-coordinate contribution. When $m=1$ there is no such term, so the first bound already completes the proof.</p>
<p>Thus the redundancy part of the source's triple-interaction expansion is controlled for all cluster powers, including $(p_1,p_2,p_3)=(0,1,2)$ after JG0C's change of root. The joint-cut estimate with an extra third-cluster power, interception and final decoupling are not supplied by this result.</p>



## A path with cluster and spatial marks {#section-marked-single-path}

<a id="tag-PGVH" data-assertion="theorem" data-title="A single critical geodesic remains negligible with cluster and spatial marks"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>, and choose the translation-equivariant geodesics of BN7Z in the original cutoff configuration. Write $X=|K_0|$, $L_u=|V(\gamma(0,u))|$, and $W_s=\sum_{v\in K_0}\|v\|^s$, with zero powers equal to one. For integers $k,s\geq0$, define</p>
<div class="math-display">$$\begin{aligned}
R_k&=\mathbb E_r\sum_{u\in K_0}X^kL_u,\\
P_{k,s}&=\mathbb E_r\sum_{u\in K_0}X^k\sum_{b\in V(\gamma(0,u))}\|b\|^s,\\
E_{k,s}&=\mathbb E_r\sum_{u\in K_0}X^kL_u\|u\|^s.
\end{aligned}$$</div>
<p>For $k\geq1$ also define</p>
<div class="math-display">$$C_{k,s}=\mathbb E_r\left[X^{k-1}W_s\sum_{u\in K_0}L_u\right].$$</div>
<p>Then, for fixed $k,s$,</p>
<div class="math-display">$$R_k=o(V_r^k r^{(2k+2)\alpha}),\qquad
P_{k,s},\ E_{k,s}=o(V_r^k r^{(2k+2)\alpha+s}),$$</div>
<p>and $C_{k,s}$ has the same bound when $k\geq1$. In particular $P_{k,0}=E_{k,0}=R_k$ and $C_{k,0}=R_k$ where defined.</p>
<p><em>Proof.</em> Put $m_l=\mathbb E_rX^l$ and $U_{l,s}=\mathbb E_r[X^{l-1}W_s]$. Cauchy–Schwarz under the measure which sums over $u\in K_0$ gives</p>
<div class="math-display">$$\begin{aligned}
P_{k,s}^2&\leq m_{2k+1}\,\mathbb E_r\sum_{u\in K_0}L_u\sum_{b\in V(\gamma(0,u))}\|b\|^{2s},\\
E_{k,s}^2&\leq U_{2k+1,2s}\,\mathbb E_r\sum_{u\in K_0}L_u^2,\\
C_{k,s}^2&\leq\mathbb E_r[X^{2k-1}W_s^2]\,\mathbb E_r\sum_{u\in K_0}L_u^2\qquad(k\geq1).
\end{aligned}$$</div>
<p>For the first line, use $(\sum_b\|b\|^s)^2\leq L_u\sum_b\|b\|^{2s}$. The path factors are $o(r^{3\alpha+2s})$ and $o(r^{3\alpha})$ by <a href="/tag/V7V5/">V7V5</a>. The remaining factors, by <a href="/tag/AR3F/">AR3F</a> and <a href="/tag/RM79/">RM79</a>, are respectively</p>
<div class="math-display">$$O(V_r^{2k}r^{(4k+1)\alpha}),\qquad
O(V_r^{2k}r^{(4k+1)\alpha+2s}),\qquad
O(V_r^{2k}r^{(4k+1)\alpha+2s}).$$</div>
<p>In the last expression there are $2k+1$ cluster marks: $2k-1$ unweighted marks and the two factors $W_s$. Taking square roots proves the assertions, with $R_k$ obtained by setting $s=0$. The case $k=0$ uses $m_1$ or $U_{1,2s}$ and has no negative cluster power.</p>
<p>The three versions distinguish a spatial mark on the path, its target, or the rest of the cluster. Translation to an intersection vertex $b$ introduces differences such as $u-b$ and $z-b$; the triangle inequality bounds their powers by the corresponding target or cluster moment together with $P_{k,s}$. No geodesic is selected after a random deletion.</p>


## Interception through a surviving path {#section-interception-repair}

<p>The missing reduction after IEOH is supplied by FIXER's proof repair. The third configuration contributes two disjoint connections, not a geodesic selected before deletion. IEOH remains a separate estimate; the argument below does not use it. The <a href="/errata/hutchcroft-lrp-3/#interception-diagram-missing-link">source erratum</a> remains provisional.</p>

<a id="tag-LK8Z" data-assertion="proposition" data-title="An intercepted surviving path supplies two disjoint connections and a second-configuration path mark"></a>
<p>Let $G_2,G_3$ be simple graphs on the same vertex set, let $A$ be a set of vertices, and let $x\notin A$. Write $C=K_x(G_2)$ and $B=K_x(G_2[A^c])$. Suppose that $y$ and $a$ are connected in $G_3[(A\cup B)^c]$, but not in $G_3[C^c]$. Then there is $b\in C\setminus B$ such that $G_3$ contains edge-disjoint connections from $y$ to $b$ and from $b$ to $a$, and every $G_2$ path from $x$ to $b$ meets $A$. In particular, any preselected $G_2$ geodesic $\gamma(x,b)$ has a vertex $c\in A$.</p>
<p><em>Proof.</em> Choose a finite simple $y$–$a$ path $P$ in $G_3[(A\cup B)^c]$. Since no such connection survives deletion of $C$, the path meets $C$ at some $b$. It avoids $B$, so $b\in C\setminus B$. An $x$–$b$ path in $G_2$ avoiding $A$ would place $b$ in $B$, a contradiction. The two portions of $P$ separated at $b$ have disjoint edges and give the claimed witnesses. A portion may have length zero; this also covers $b=y$, $b=a$, and $y=a$.</p>
<p>The path $P$ may depend on all exposed sets. Only its existence is used. After taking a union over deterministic $b,c$, the events that $c\in A$, that $c\in\gamma(x,b)$ in the second configuration, and that the two connections occur disjointly in the third configuration depend on separate configurations. This is the independence needed below.</p>

## The marked moment bound {#section-interception-moments}

<a id="tag-O10I" data-assertion="theorem" data-title="A quantitative interception bound from fifth spatial moments and squared geodesic lengths"></a>
<p>For each $r\geq1$, let $\mathbb P_r$ be a translation-invariant independent-bond law on $\mathbb Z^d$ with finite susceptibility $\chi_r$. Choose translation-covariant geodesics, counted by vertices including both endpoints. For the cluster $K$ at zero, put</p>
<div class="math-display">$$N=|K|,\qquad V_r=\frac{\mathbb E_rN^2}{\chi_r^3},\qquad
S_t=\sum_{z\in K}\|z\|^t,\qquad L_b=1+d_{\mathrm{chem}}(0,b),\qquad
C_2(r)=\mathbb E_r\sum_{b\in K}L_b^2.$$</div>
<p>Degree-zero powers are one, so $S_0=N$. Fix integers $p,q\geq0$ and set $s=p+q$. Assume, uniformly for sufficiently large $r$,</p>
<div class="math-display">$$\mathbb E_rS_s\leq C_s r^s\chi_r,\qquad
\mathbb E_rN^5\leq C_0V_r^4\chi_r^9,\qquad
F_s(r):=\mathbb E_r[N^4S_{2s}]\leq C_s r^{2s}V_r^4\chi_r^9.$$</div>
<p>Take three independent configurations. Let $A$ be the first root cluster, $C$ the second cluster rooted at $x$, and $B$ its restriction off $A$; a deleted root has empty cluster. Let $I_{x,y,a}$ be the event that $x\notin A$ and the third configuration connects $y$ to $a$ off $A\cup B$, but not off $C$. With $W_q(B)=\sum_{z\in B}\|z\|^q$, define</p>
<div class="math-display">$$\mathcal J_{p,q}(r)=\sum_{x\in B_r}\sum_{y,a}\|y\|^p\,
\mathbf E_r\!\left[|A|\,|B|W_q(B)\mathbf1_{I_{x,y,a}}\right],\qquad
B_r=\{x:\|x\|\leq r\}.$$</div>
<p>Then, with $\varepsilon_r=C_2(r)/\chi_r^3$,</p>
<div class="math-display">$$\mathcal J_{p,q}(r)\leq C_{p,q}r^{p+q}V_r^3\chi_r^{11}\sqrt{\varepsilon_r}.$$</div>
<p>All terms are finite. The constant depends on the stated moment constants, the degrees and the norm, but not on $r$.</p>
<p><em>Proof.</em> Write $\chi=\chi_r$, $V=V_r$ and $\tau(u)=\mathbb P_r(0\leftrightarrow u)$. By LK8Z, the event $I_{x,y,a}$ is contained in the union over $b,c$ of</p>
<div class="math-display">$$\{c\in A\}\cap\{b\in C,\ c\in\gamma(x,b)\}
\cap\bigl(\{y\leftrightarrow b\}\circ\{b\leftrightarrow a\}\bigr)_3.$$</div>
<p>Replace $B$ by $C$ in the nonnegative weight and apply independence and BK. This bounds $\mathcal J_{p,q}$ by</p>
<div class="math-display">$$\sum_{x\in B_r}\sum_{y,a,b,c}
\mathbb E_r[N\mathbf1_{\{c\in K\}}]
\mathbb E_r\!\left[|K_x|\mathbf1_{\{b\in K_x,\ c\in\gamma(x,b)\}}
\sum_{z\in K_x}\|z\|^q\right]
\tau(y-b)\tau(a-b)\|y\|^p.$$</div>
<p>The mark $c\in\gamma(x,b)$ must be retained. Before enlarging the $x$ sum, use $\|x\|\leq r$ to obtain</p>
<div class="math-display">$$\|y\|^p\|z\|^q\leq C_{p,q}
\bigl(r^s+\|y-b\|^s+\|b-x\|^s+\|z-x\|^s\bigr).$$</div>
<p>This follows by bounding both norms by a sum of $r$ and their displayed displacements, and then bounding the degree-$s$ power of that sum. Now drop $x\in B_r$ in each nonnegative term. Set</p>
<div class="math-display">$$\begin{aligned}
H_0&=\mathbb E_r\left[N^2\sum_{b\in K}L_b\right],\\
H_s^{(b)}&=\mathbb E_r\left[N^2\sum_{b\in K}L_b\|b\|^s\right],\\
H_s^{(z)}&=\mathbb E_r\left[NS_s\sum_{b\in K}L_b\right].
\end{aligned}$$</div>
<p>For fixed $c$ and a nonnegative function $f$, translation covariance gives</p>
<div class="math-display">$$\sum_{x,b}\mathbb E_r\!\left[|K_x|^2
\mathbf1_{\{b\in K_x,\ c\in\gamma(x,b)\}}f(b-x)\right]
=\mathbb E_r\left[N^2\sum_{b\in K}L_b f(b)\right].$$</div>
<p>Indeed, after translation by $-x$, put $v=b-x$ and $w=c-x$. Summing over $x$ sums $w$ over the vertices of $\gamma(0,v)$, giving $L_v$. No reversal symmetry of the path choice is required. Replacing $|K_x|^2$ by $|K_x|\sum_{z\in K_x}\|z-x\|^s$ gives $H_s^{(z)}$ in the same way. The $c$ sum in the first factor is $\mathbb E_rN^2$, while the two connection sums are $\chi^2$, or $\chi\mathbb E_rS_s$ when $y-b$ carries the weight. The diagram is therefore at most</p>
<div class="math-display">$$C_{p,q}\mathbb E_rN^2\left[
\chi^2\bigl(r^sH_0+H_s^{(b)}+H_s^{(z)}\bigr)
+\chi(\mathbb E_rS_s)H_0\right].$$</div>
<p>Apply Cauchy–Schwarz on configurations with one counted vertex $b\in K$. It gives</p>
<div class="math-display">$$H_0\leq\sqrt{(\mathbb E_rN^5)C_2},\qquad
H_s^{(b)}\leq\sqrt{F_sC_2},\qquad
H_s^{(z)}\leq\sqrt{\mathbb E_r[N^3S_s^2]C_2}\leq\sqrt{F_sC_2}.$$</div>
<p>For the last inequality use $S_s^2\leq NS_{2s}$. In the first inequality the counted target supplies the fifth power of $N$; in the second it supplies the sum defining $S_{2s}$. Thus $H_0\leq C V^2\chi^6\sqrt{\varepsilon_r}$ and both weighted terms are at most $C_s r^sV^2\chi^6\sqrt{\varepsilon_r}$. Since $\mathbb E_rN^2=V\chi^3$, substitution proves the bound. All rearrangements used Tonelli; these estimates also prove finiteness.</p>

## The source interception estimate {#section-source-interception}

<a id="tag-R6CI" data-assertion="corollary" data-title="The source interception error is negligible above and at the upper critical dimension"></a>
<p>In the normalized radial-cutoff model <a href="/tag/C0OR/">C0OR</a> of Critical LRP I–III, assume $d\geq3\alpha$ and $0&lt;\alpha&lt;2$. Use its critical intensity, cutoff clusters and three-copy coupling. For every pair of integers $p,q\geq0$, the interception term of Lemma III.6.17 satisfies</p>
<div class="math-display">$$\mathcal J_{p,q}(r)=o\!\left(|B_r|V_r^3r^{p+q}\chi_r^8\right).$$</div>
<p><em>Proof.</em> The source inputs are <a href="https://arxiv.org/html/2508.18807v1">Part I, Proposition I.4.20 and Lemma I.5.27</a>, and <a href="https://arxiv.org/html/2508.18809v1">Part III, Theorem III.1.11, Lemmas III.2.2 and III.2.5, and (III.6.10)</a>. Their use is specified here so that the repair does not presuppose the final logarithmic asymptotics. At $d&gt;3\alpha$, Case 1 of (HD+) applies; at $d=3\alpha&lt;6$, Theorem III.1.11 supplies the hydrodynamic hypothesis in Case 4. The spatial scale in I.5.27 is $r$. Taking five marked vertices, four constant monomials and one coordinate of degree $2s$, then summing over coordinates, gives</p>
<div class="math-display">$$\mathbb E_r[N^4S_{2s}]=O_s\!\left(r^{2s}(V_r\chi_r^2)^4\chi_r\right).$$</div>
<p>The zero-degree case is the fifth-moment bound in I.4.20. Taking one marked vertex and absolute coordinate monomials gives $\mathbb E_rS_s=O_s(r^s\chi_r)$, also for odd integer $s$. Thus all moment hypotheses of O10I hold.</p>
<p>For every finite-susceptibility product law, $C_2\leq2\chi_r^3$. A path with $L$ vertices has $L(L+1)/2$ weakly ordered pairs. Each pair splits it into three edge-disjoint connections, whose BK products sum to $\chi_r^3$. Coincident marks contribute empty witnesses.</p>
<p>At $d=3\alpha&lt;6$, the chemical-distance consequence of III.2.2 and III.2.5, together with $V_r\to0$ from III.6.10, gives $\mathbb E_r\sum_b d_{\mathrm{chem}}(0,b)=o(\chi_r^2)$. Three ordered marks and BK give $\mathbb E_r\sum_b d_{\mathrm{chem}}(0,b)^3=O(\chi_r^4)$. Cauchy–Schwarz on the same counted-target measure yields</p>
<div class="math-display">$$\mathbb E_r\sum_b d_{\mathrm{chem}}(0,b)^2=o(\chi_r^3).$$</div>
<p>Adding the lower-order linear and constant terms gives $C_2=o(\chi_r^3)$. This is the $q=2$ consequence of (III.6.39); it precedes interception and does not use the final asymptotic for $V_r$.</p>
<p>Finally $\chi_r\asymp r^\alpha$ and $|B_r|\asymp r^d$. Dividing the bound in O10I by the asserted scale gives $O(r^{3\alpha-d}\sqrt{\varepsilon_r})$. It tends to zero by the power of $r$ above the critical dimension, and by $\varepsilon_r\to0$ at equality. Since deletion of $A\cup B$ includes deletion of $A$, the source event reduces exactly to $I_{x,y,a}$; hence this is its stated interception estimate.</p>
<p>This completes the written interception repair, using the named earlier source results. The dropped-link diagram in ZGVN is still divergent and its erratum is not withdrawn. No source-author confirmation or compiled proof is asserted. The full coupling-law construction and the remaining assembly of the triple-interaction argument retain their own formalisation obligations. The deficit conclusions ENWJ and RDLW keep their explicit hypotheses.</p>

<p>The <a href="/tag/0HRJ/">short-path multipoint argument</a> retains the bounded path lengths when adding one unrestricted cluster mark. Under susceptibility bias it gives every intrinsic-ball moment, and <a href="/tag/Z78U/">the finite-triangle consequence</a> gives exponential upper tails on the radius-squared scale for the resulting cylinder limits. These IIC bounds use different laws from the independent critical law considered above.</p>

<p>The <a href="/tag/KGPE/">stopped-boundary comparison</a> now supplies <a href="/tag/RG3Z/">the matching quadratic lower volume</a> in the susceptibility-biased cylinder limits under finite triangle, and in the ratio-controlled distant-point limits. The uniform subgraph arm bound also gives <a href="/tag/POD2/">linear intrinsic resistance growth</a>. These results establish almost-sure volume exponent two and resistance exponent one for each such limit; the random-walk implications remain separate.</p>

<p>The <a href="/tag/NNW7/">deterministic random-walk implication</a> turns volume exponent two and resistance exponent one into mean exit-time exponent three and spectral dimension four thirds. <a href="/tag/IXCJ/">Its application to the incipient limits</a> distinguishes degree volume, fixed-cluster walk probabilities and ordinary versus lazy time.</p>

<p>The <a href="/tag/LCUN/">nearby-vertex hitting comparison</a> yields a lower tail for exit times and a bound on the degree mass missed in a smaller ball. The resulting <a href="/tag/HJKG/">IIC pathwise exponents</a> concern exit time, maximum distance and range separately; the bounded cluster degree is used when passing from degree mass to the number of visited vertices.</p>

<p>The <a href="/tag/G85Z/">annealed walk bounds</a> now give two-sided mean exit times of order $r^3$ and averaged even-time return probabilities of order $n^{-2/3}$ for the same incipient limits. The proof controls rare environments using the lower-volume tail and gives a lower bound of order $n^{1/3}$ on mean intrinsic displacement; it does not infer expectations from almost-sure logarithmic exponents.</p>

<p>The <a href="/tag/YWT9/">quantitative walk estimates</a> give tightness of intrinsic displacement and maximum distance on the $n^{1/3}$ scale, and exit time on the $r^3$ scale, under the joint cluster-and-walk law. Explicit polynomial tails also give positive and negative fractional moments in the stated ranges; they do not supply the missing upper mean-displacement bound.</p>

<p>The <a href="/tag/PSNV/">quantitative range theorem</a> now gives tightness of the number of visited vertices on the $n^{2/3}$ scale, with inverse and positive fractional moments for $-3/23&lt;p&lt;3/94$. The proof combines a bound on the volume missed before exit with the exponential intrinsic-volume tail. It distinguishes these joint-law bounds from the earlier almost-sure logarithmic exponent.</p>


## The finite Reimer premise {#section-finite-reimer-proof-link}

<p>The <a href="/articles/countable-reimer/#section-finite-reimer-proof">complete finite Reimer proof</a> now supplies the combinatorial premise used in X86B at the level of the written argument. Its <a href="/articles/countable-reimer/#section-full-reimer-completed-proof">countable extension</a> permits infinite certificates, with the stated distinction between outer and ordinary probability. The hypotheses and tagged statements above are retained; source corrections remain provisional and formal status still requires Lean evidence.</p>



## Weighted path moments with a decreasing test {#section-decreasing-path-moments}

<p>The full-edge Reimer inequality lets us keep a decreasing constraint when marking a path. Repeated marks give all moments, and summing them gives an exponential truncation error. The path need only be simple; it need not be a geodesic.</p>
<p>Let independent bonds on a countable simple graph have two-point function $\tau$. For every $z\in K_o$, choose a finite simple open path $\gamma_z$ from $o$ to $z$, measurably in the configuration. An enumeration of finite paths supplies such a choice. Given nonnegative vertex weights $a_v,b_v$, put</p>
<div class="math-display">$$
V_a(K_o)=\sum_{v\in K_o}a_v,\qquad
L_a(\gamma_z)=\sum_{v\in V(\gamma_z)}a_v.
$$</div>
<p>Both endpoints are included. Let $\Phi:\{0,1\}^{E}\to[0,1]$ be Borel and decreasing. Every sum below is a sum of nonnegative terms, with a term of weight $\Phi=0$ interpreted as zero.</p>

<a id="tag-9KEP" data-assertion="theorem" data-title="Decreasing tests preserve weighted path moments and exponential tails"></a>
<p>Suppose finite positive constants $M,N$ satisfy</p>
<div class="math-display">$$
\sup_u\sum_v\tau(u,v)a_v\le M,\qquad
\sup_u\sum_v\tau(u,v)b_v\le N,
$$</div>
<p>and let $R=\mathbb E[\Phi V_a(K_o)]&lt;\infty$. For every integer $k\ge1$ and every $0&lt;t&lt;M^{-1}$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E\!\left[\Phi\sum_{z\in K_o}b_zL_a(\gamma_z)^k\right]
&\le k!\,N M^{k-1}R,\\
\mathbb E\!\left[\Phi\sum_{z\in K_o}b_z\bigl(e^{tL_a(\gamma_z)}-1\bigr)\right]
&\le \frac{Nt}{1-tM}\,R.
\end{aligned}
$$</div>
<p>Consequently, for every $\ell&gt;0$,</p>
<div class="math-display">$$
\mathbb E\!\left[\Phi\sum_{z\in K_o}b_z
\mathbf1_{\{L_a(\gamma_z)&gt;\ell\}}\right]
\le NR\min\left\{\frac1\ell,
\frac1{M(e^{\ell/(2M)}-1)}\right\}.
$$</div>
<p>No transitivity or finite unweighted susceptibility is required. In particular, for $h&gt;0$ and $\Phi=e^{-hV_a(K_o)}$, with value zero when $V_a(K_o)=\infty$, one may replace $R$ by $1/(eh)$.</p>

<p><em>Proof.</em> Begin with $\Phi=\mathbf1_D$, where $D$ is decreasing and Borel. Write the vertices of a selected path as $v_0=o,\ldots,v_j=z$. Expanding its weighted length and sorting the indices gives</p>
<div class="math-display">$$
\left(\sum_{i=0}^j a_{v_i}\right)^k
\le k!\!\sum_{0\le i_1\le\cdots\le i_k\le j}
\prod_{r=1}^k a_{v_{i_r}}.
$$</div>
<p>The coefficient of a sorted tuple in the expansion is $k!$ divided by the factorials of its multiplicities, so it is at most $k!$. Since the path is simple, distinct sorted index tuples give distinct ordered vertex tuples.</p>
<p>Fix one such tuple $w_1,\ldots,w_k$. On $D$, the prefix from $o$ to $w_1$, together with <em>all</em> closed edges of the configuration, certifies $D\cap\{o\leftrightarrow w_1\}$. A configuration agreeing with these coordinates retains that prefix and can only remove other open edges, so it remains in $D$. The remaining consecutive segments certify the connections from $w_1$ through $w_k$ to $z$. All these certificates are pairwise disjoint. Repeated marks and endpoint marks give empty segments, which are valid connection certificates.</p>
<p>Apply the <a href="/tag/UFCR/">simultaneous full-certificate inequality</a>, whose finite premise is supplied by <a href="/tag/7GDN/">7GDN</a>. The first event is order-convex Borel and the others are open connection events, so the stated measurability result applies. Alternatively its outer bound already suffices to bound the Borel event that the selected path contains the prescribed ordered marks. We obtain</p>
<div class="math-display">$$
\begin{aligned}
&\mathbb E\!\left[\mathbf1_D\sum_{z\in K_o}b_zL_a(\gamma_z)^k\right]\\
&\quad\le k!\sum_{w_1,\ldots,w_k,z}
\mathbb P(D,\ o\leftrightarrow w_1)
\left(\prod_{r=1}^k a_{w_r}\right)b_z
\left(\prod_{r=1}^{k-1}\tau(w_r,w_{r+1})\right)\tau(w_k,z).
\end{aligned}
$$</div>
<p>Sum first over $z$, then backwards over $w_k,\ldots,w_2$. The two row bounds give $NM^{k-1}$. The remaining sum is $\mathbb E[\mathbf1_D V_a(K_o)]$. Tonelli justifies every sum, including when a cluster is infinite.</p>
<p>For general $\Phi$, apply this result to the decreasing Borel sets $D_s=\{\Phi&gt;s\}$ and integrate over $0&lt;s&lt;1$. The identity $\Phi=\int_0^1\mathbf1_{D_s}\,ds$ and Tonelli give the moment bound. Now expand $e^{tL}-1=\sum_{k\ge1}t^kL^k/k!$ and sum the geometric series. The first moment gives the first tail bound; the exponential estimate with $t=1/(2M)$ gives the second. Finally $x e^{-hx}\le1/(eh)$ for $x\ge0$, with value zero at infinity, proves the soft-volume assertion. $\square$</p>

## Exponential truncation for averaged paths {#section-exponential-averaged-paths}

<a id="tag-FV16" data-assertion="corollary" data-title="The averaged geodesic truncation error decays exponentially beyond the weighted susceptibility scale"></a>
<p>In the invariant finite-susceptibility model and notation of <a href="/tag/X86B/">X86B</a>, suppose the finite observation set $B$ is nonempty and put $\eta=\min\{\chi,|B|\}$. For any deterministic deleted set $W$, any class $\mathscr A$ of finite cluster graphs, and $m,\ell&gt;0$,</p>
<div class="math-display">$$
\begin{aligned}
&\mathbb E\sum_{z\in K_0^W}
\mathbf1_{\{K_0^W\in\mathscr A,\ L_\nu(\gamma_{K_0^W}(0,z))\le\ell\}}\\
&\quad\ge
\mathbb E\bigl[|K_0^W|;\ K_0^W\in\mathscr A,\ V_\nu(K_0^W)\le m\bigr]\\
&\qquad-
\chi\min\left\{\frac1\ell,
\frac1{\eta(e^{\ell/(2\eta)}-1)}\right\}
\mathbb E\min(|K_0|,m).
\end{aligned}
$$</div>
<p>The class $\mathscr A$ need not be downward closed. This strengthens the truncation error in X86B while retaining its model hypotheses.</p>

<p><em>Proof.</em> Work directly in the product law on the graph with $W$ deleted. If the root is deleted, both cluster counts vanish. Otherwise set</p>
<div class="math-display">$$
a_v=\sum_x\nu(x)\mathbf1_{\{v\in x+B\}},\qquad b_v=1.
$$</div>
<p>Then $0\le a_v\le1$, $\sum_v a_v=|B|$ on the full lattice, and the two weighted quantities in 9KEP are exactly $V_\nu$ and $L_\nu$. Every restricted susceptibility is at most $\chi$. The $a$-weighted row is at most both $\chi$ and $|B|$, so $M=\eta$ and $N=\chi$ are admissible. Take $D=\{V_\nu(K_0^W)\le m\}$. This is closed and decreasing: each connection indicator is lower semicontinuous, and the weighted volume is their nonnegative sum. Moreover,</p>
<div class="math-display">$$
\mathbb E[V_\nu(K_0^W);\ V_\nu(K_0^W)\le m]
\le \mathbb E\min(|K_0|,m).
$$</div>
<p>Subtract the long-path vertices from the cluster-volume term and discard $\mathscr A$ only from that error. The tail bound in 9KEP gives the displayed estimate. Infinite closed-edge certificates are allowed throughout, so no finite-restriction stabilization is needed. $\square$</p>
<p>This is a further deduction from the written Reimer proof and the existing averaged-path argument. It changes no earlier tagged statement and records no additional source error. Independent mathematical review and Lean formalisation remain separate.</p>



## Walk observables at intrinsic exit {#section-stopped-walk-moments-link}

<p>The <a href="/articles/iic-random-walk/#section-iic-stopped-moments">stopped-walk estimates</a> use the exponential intrinsic-volume tail to give every positive moment of exit time and range at exit. The exit-time upper tail has an exponential bound in the square root of the normalized time; the stopped range has an exponential upper tail and a lower-tail power $1/7$. These conclusions retain the existing finite-triangle incipient-limit hypotheses and distinguish stopping at a sphere from observing the walk at a fixed time.</p>


## Returning from exit times to fixed times {#section-inverse-walk-link}

<p>The <a href="/articles/iic-random-walk/#section-iic-inverse-moments">inverse-moment estimates</a> use the slow-exit tail in two ways: every inverse moment of the intrinsic maximum has the expected scale, and the inverse-range interval at a fixed time extends to $p&gt;-1/7$. The latter comes with an explicit logarithmic loss in its lower-tail bound. The maximum is kept distinct from the final position, whose returns prevent such an extension to all negative orders.</p>
