---
{
  "id": "cluster-partitions",
  "title": "Cluster partitions and root averages",
  "subtitle": "Counting components once or once per vertex",
  "kind": "method",
  "category": "Foundations",
  "summary": "Clusters partition the vertices. Grouping root sums by components explains squared cluster sizes, size-biased sampling, and deterministic comparisons with the largest cluster in a window. Reciprocal cluster sizes count each component once, and opening a bond merges at most two components.",
  "context": [
    "A fixed open configuration on a vertex set $V$; no probability law is needed for the partition identities.",
    "$K(x)$ is the cluster containing $x$, including $x$ itself.",
    "Finite sets are explicitly required for finite sums and uniform sampling.",
    "The final covariance estimates assume independent bonds and a finite observation window; full clusters may be infinite."
  ],
  "related": [
    "connectivity",
    "susceptibility",
    "universal-tightness",
    "finite-random-graphs"
  ],
  "sourceIds": [
    "perclib-bond-interface",
    "perclib-susceptibility-interface",
    "perclib-cluster-partition",
    "perclib-cluster-count",
    "perclib-window-partition",
    "perclib-finite-volume-associations",
    "perclib-volume-tails",
    "hutchcroft-hierarchical-volumes-2022"
  ],
  "aliases": [
    "cluster partition",
    "connected components",
    "root average",
    "component moments",
    "size biased sampling",
    "component count",
    "reciprocal cluster size"
  ],
  "prototypeUses": []
}
---

## Open pairs and the simple graph {#section-open-pairs}

<a id="tag-Q0D1" data-assertion="proposition" data-title="Open-graph monotonicity and the singleton-cluster convention"></a>
<p>Let $V$ be any vertex set and let $\omega$ be a set of unordered pairs, with repeated pairs allowed as coordinates. The associated simple graph joins $x$ and $y$ exactly when $x\ne y$ and $\{x,y\}\in\omega$. If $\omega\subseteq\omega'$, then every connection in $\omega$ is a connection in $\omega'$, and</p>
<div class="math-display">$$K_\omega(x)\subseteq K_{\omega'}(x).$$</div>
<p>Every cluster contains its root and therefore has extended volume at least one. If no pair of distinct vertices is open, then $K_\omega(x)=\{x\}$ for every $x$, whatever the diagonal coordinates. Conversely, one open pair of distinct vertices connects its endpoints. These statements require neither countability nor a probability law.</p>
<p><em>Proof.</em> Inclusion of configurations preserves every adjacency and hence every finite open path. The length-zero path puts $x$ in its own cluster. With no open pair of distinct vertices, no path of positive length can take even its first step, so the only reachable vertex is $x$. An open pair with distinct endpoints supplies a path of length one.</p>
<p>In particular, on two distinct vertices the all-closed configuration disconnects them and the configuration containing their pair connects them. The empty configuration has singleton clusters, not empty clusters. For a probability law on a countable vertex set, reflexivity and symmetry of connection give $\tau(x,x)=1$, $\tau(x,y)=\tau(y,x)$ and $0\leq\tau(x,y)\leq1$. Full configuration laws can still distinguish diagonal parameters; only the simple graph ignores them.</p>

## Components as classes {#section-partition}

<a id="tag-0N0J" data-assertion="proposition" data-title="Root clusters form a partition"></a><p>For any vertices $x,y$,</p><div class="math-display">$$K(x)=K(y)\quad\Longleftrightarrow\quad x\leftrightarrow y.$$</div><p>Any two root clusters are therefore either equal or disjoint, and the distinct clusters partition $V$. No countability, local finiteness or independence hypothesis is required.</p><p><em>Proof.</em> Connectivity by finite paths is an equivalence relation: the empty path gives reflexivity, reversing a path gives symmetry, and concatenation gives transitivity. Its equivalence class at $x$ is exactly $K(x)$. Equivalence classes are equal precisely when their representatives are equivalent, and otherwise are disjoint.</p>

## Grouping a sum by components {#section-sums}

<a id="tag-TUD2" data-assertion="theorem" data-title="Finite root sums equal size-weighted component sums"></a><p>Suppose $V$ is finite, and let $\mathcal C$ be its set of distinct open components. For every function $f:\mathbb N\to\mathbb R$,</p><div class="math-display">$$\sum_{x\in V}f(|K(x)|)=\sum_{C\in\mathcal C}|C|f(|C|).$$</div><p>In particular,</p><div class="math-display">$$\sum_{x\in V}|K(x)|=\sum_{C\in\mathcal C}|C|^2.$$</div><p>The same identities apply to the graph induced on a finite vertex domain, with its internal components and internal clusters.</p><p><em>Proof.</em> Partition the sum on the left according to the component containing $x$. On a component $C$, every summand equals $f(|C|)$, and there are $|C|$ such summands. Taking $f(n)=n$ gives the squared-size formula. Apply the same argument to the induced graph for the domain version. If $V$ is empty, both sums are empty and equal zero.</p>

## Choosing a root {#section-sampling}

<p>The <a href="/tag/CY0D/">uniform-root component formula</a> gives the following sampling interpretation. Fix a configuration on a finite nonempty $V$, and choose a vertex $U$ uniformly from $V$. For each distinct component $C$,</p><div class="math-display">$$\mathbb P(K(U)=C\mid\omega)=\frac{|C|}{|V|},\qquad \mathbb E[|K(U)|\mid\omega]=\frac1{|V|}\sum_{C\in\mathcal C}|C|^2.$$</div><p>If instead a component is chosen uniformly from $\mathcal C$, its mean size is $|V|/|\mathcal C|$. The uniform-root component law is the size bias of this uniform-component law.</p><p><em>Proof.</em> Exactly the vertices of $C$ select $C$, giving the first probability. Summing its product with $|C|$ gives the expectation. Under uniform-component sampling, the mean size is $\sum_C|C|/|\mathcal C|=|V|/|\mathcal C|$. Biasing its mass $1/|\mathcal C|$ by $|C|$ and normalizing by this mean gives $|C|/|V|$.</p><p>For a random configuration and an independent uniform root, taking another expectation gives the existing <a href="/tag/XCGS/">averaged susceptibility identity</a></p><div class="math-display">$$\frac1{|V|}\sum_{x\in V}\mathbb E|K(x)|=\frac1{|V|}\mathbb E\!\left[\sum_{C\in\mathcal C}|C|^2\right].$$</div><p>No transitivity is needed for this averaged identity. Replacing the average over roots by one fixed root requires additional symmetry.</p>

## Observing clusters in a window {#section-window}

<a id="tag-RU6O" data-assertion="proposition" data-title="Window intersection moments and the largest observed cluster"></a><p>Let $\Lambda\subseteq V$ be finite and nonempty, with $V$ otherwise arbitrary. Form the finite partition</p><div class="math-display">$$\mathcal C_\Lambda=\{C\cap\Lambda:C\text{ is a full open component and }C\cap\Lambda\neq\varnothing\},$$</div><p>and let $M_\Lambda=\max_{D\in\mathcal C_\Lambda}|D|$. Then</p><div class="math-display">$$\sum_{x\in\Lambda}|K(x)\cap\Lambda|=\sum_{D\in\mathcal C_\Lambda}|D|^2,\qquad M_\Lambda^2\leq\sum_{x\in\Lambda}|K(x)\cap\Lambda|\leq M_\Lambda|\Lambda|.$$</div><p><em>Proof.</em> Intersecting the full component partition with $\Lambda$ and discarding empty intersections gives a partition of $\Lambda$. Grouping the root sum by these classes proves the identity. One class has size $M_\Lambda$, so its square gives the lower bound. For the upper bound, use $|D|^2\leq M_\Lambda|D|$ and $\sum_D|D|=|\Lambda|$.</p><p>These classes need not be the components of the induced graph on $\Lambda$: two observed vertices may be joined by an excursion outside the window. For an open path $x-z-y$ with $\Lambda=\{x,y\}$ and $z\notin\Lambda$, the full-cluster intersection is one class of size two, whereas the induced graph has two singleton components. The corresponding squared-size sums are four and two. This is the observation-window convention used by <a href="#/universal-tightness">maximum-cluster tightness</a>.</p>

## The cluster as a measurable random set {#section-random-set}

<a id="tag-GUHT" data-assertion="proposition" data-title="Cluster-set measurability and the extended connection-indicator sum"></a>
<p>On a countable vertex set, the map $\omega\mapsto K_\omega(x)$ is measurable from the bond configuration space to $2^V$, with the product sigma-algebra on each. Its extended volume $|K_\omega(x)|\in\mathbb N\cup\{\infty\}$ is measurable as well. The deterministic identity</p>
<div class="math-display">$$|K_\omega(x)|=\sum_{y\in V}\mathbf1_{\{x\leftrightarrow y\}}(\omega)$$</div>
<p>holds on an arbitrary vertex set, interpreting the nonnegative sum as the supremum of its finite subsums and every infinite cardinality as $\infty$.</p>
<p><em>Proof.</em> Membership at $y$ is a generating coordinate event of $2^V$, and its inverse image under the cluster map is the connection event $\{x\leftrightarrow y\}$. On a countable vertex set this is measurable by the finite-path argument, proving measurability of the random set.</p>
<p>For the identity, a finite cluster contributes exactly one for each of its vertices. An infinite cluster contains finite subsets of arbitrarily large size, so the supremum of finite subsums is infinite. When $V$ is countable, enumerate it by increasing finite sets. The corresponding indicator sums are measurable and increase to the extended volume. Equivalently, each volume threshold is a countable union of measurable finite-sum thresholds, proving measurability as an extended integer-valued variable.</p>
<p>Integrating the nonnegative sum gives the <a href="/tag/8DSI/">susceptibility identity</a> by Tonelli, including infinite values. This step requires measurable connection events; the arbitrary-set deterministic identity alone supplies no such measurability. The empty configuration contributes the root term one.</p>

<p>The measurability argument also separates finite witnesses from countability. For any finite vertex list, the event that consecutive vertices form an open walk is a finite intersection of coordinate cylinders (or the empty event if two consecutive vertices coincide), so it is measurable for arbitrary $V$. Connection is the union over lists with the specified endpoints. An infinite cluster is equivalently one that connects to the complement of every finite subset of $V$. These are set identities without countability; countability makes the relevant unions and intersections countable and hence measurable. Neither graph definitions nor deterministic root-cluster identities require measurable connection events.</p>


## Counting each component once {#section-component-count}

<p>On a finite vertex set $V$, let $\kappa(\omega)$ be the number of distinct open components. Every component is nonempty, so $0\leq\kappa(\omega)\leq|V|$, with $\kappa(\omega)\geq1$ when $V$ is nonempty.</p>

<a id="tag-ZAIH" data-assertion="proposition" data-title="Reciprocal cluster sizes count components and give their expected number"></a>
<p>For every configuration on finite $V$,</p>
<div class="math-display">$$\kappa(\omega)=\sum_{x\in V}\frac1{|K_\omega(x)|}.$$</div>
<p>Consequently, under any probability law on these configurations,</p>
<div class="math-display">$$\mathbb E\kappa=\sum_{x\in V}\mathbb E\!\left[\frac1{|K(x)|}\right].$$</div>
<p><em>Proof.</em> Apply the <a href="/tag/TUD2/">component grouping identity</a> with $f(n)=1/n$ for positive $n$ and any value at zero. Each component $C$ contributes $|C|/|C|=1$. The expectation identity follows by linearity of a finite sum. The configuration space is finite with its full sigma-algebra, so every real-valued function on it is measurable and bounded, hence integrable under any probability law.</p>
<p>The empty graph has no components, and both sums are zero. For a nonempty graph, no reciprocal has zero denominator because each cluster contains its root. If $U$ is an independent uniform vertex, the same formula reads $\mathbb E\kappa=|V|\mathbb E[1/|K(U)|]$. This is an average of reciprocals, not the reciprocal of the average cluster size. No transitivity or independence of bond states is needed.</p>
<p>The choice $f(n)=n$ in the same grouping identity gives the earlier <a href="/tag/XCGS/">sum of susceptibilities</a> as the expected sum of squared component sizes. The reciprocal and first-power choices count components with different weights; neither supplies a distributional assumption.</p>

## Opening one bond {#section-component-insertion}

<p>Consider inserting the pair $\{a,b\}$ into a fixed configuration, on an arbitrary vertex set. A connection created by this insertion has a finite simple path that uses the new pair once. Removing that pair leaves old paths to its two endpoints. Hence a new connection from $u$ to $v$ either existed already, or joins a vertex in $K_\omega(a)$ to one in $K_\omega(b)$. The two endpoint components are the only components that can merge.</p>

<a id="tag-NW8B" data-assertion="proposition" data-title="Opening a pair merges at most two components and larger profiles decrease expected component counts"></a>
<p>For finite $V$, opening a pair decreases $\kappa$ by at most one. More precisely,</p>
<div class="math-display">$$\kappa(\omega\cup\{\{a,b\}\})=\kappa(\omega)-\mathbf1_{\{a\not\leftrightarrow b\text{ in }\omega\}}.$$</div>
<p>Thus $\omega\subseteq\omega'$ implies $\kappa(\omega')\leq\kappa(\omega)$. For Bernoulli product profiles $q\leq q'$ on the same finite vertex set,</p>
<div class="math-display">$$\mathbb E_{q'}\kappa\leq\mathbb E_q\kappa.$$</div>
<p><em>Proof.</em> If the endpoint components are distinct, the new bond joins them into one component and leaves every other component unchanged. If they coincide, the partition is unchanged. This proves the exact formula, including a loop or an already open pair. Adding the finitely many pairs of $\omega'\setminus\omega$ gives the configuration inequality.</p>
<p>Use the <a href="/tag/6B9V/">ordered product coupling</a> with independent uniform variables $U_e$, and declare $e$ open at profile $q$ when $U_e\leq q_e$. The configuration at $q$ is contained in that at $q'$ almost surely. Apply the deterministic inequality and take expectations; $\kappa\leq|V|$ ensures integrability.</p>
<p>The source exports the at-most-one decrease, and the exact formula is the stronger informal consequence of its path argument. The source's profile comparison assumes domination on every pair. For the graph observable $\kappa$, domination only off the diagonal also suffices: replace both diagonal profiles by zero, which leaves the open graphs unchanged, and apply the preceding comparison. This last reduction is an additional consequence of <a href="/tag/LNKT/">diagonal erasure</a>.</p>
<p>All these counts concern components in the specified graph. On a finite domain they count components of its induced graph; counting full ambient clusters that meet the domain is a different operation, as in the earlier window example. The <a href="/coverage/sources/perclib-5d6efa8-cluster-counts/">19-contract inventory</a> connects the partition and count modules to these arguments, preserving the finite-vertex restrictions and distinguishing the additional deductions. Existing source records remain pending independent review and compiled association.</p>

## Window sums in the source {#section-window-source}

<p>The source implements <a href="/tag/RU6O/">RU6O</a> by taking the distinct traces $D_x=K(x)\cap\Lambda$ for $x\in\Lambda$. For $a\in\Lambda$, the equality $D_a=D_x$ holds exactly when $a\in K(x)$. Thus the fibre of the map $a\mapsto D_a$ over a trace $D$ has exactly $|D|$ elements. Grouping the root sum by this finite map gives $\sum_{x\in\Lambda}|D_x|=\sum_D|D|^2$ directly, without choosing or enumerating the full clusters.</p>
<p>The source also includes the empty window: all sums and the maximum are zero. For a nonempty window, write $Z=\max_x|D_x|$ for the realized maximum. Then $Z^2\leq\sum_x|D_x|\leq Z|\Lambda|$. This $Z$ is a random variable, distinct from its deterministic tightness quantile. All these identities hold pointwise on arbitrary vertex sets.</p>
<p>On countable vertices, measurability of finite-window tail events makes every $|D_x|$ measurable. Finite summation under the independent bond law then gives</p>
<div class="math-display">$$\sum_{x\in\Lambda}\mathbb E|K(x)\cap\Lambda|
=\mathbb E\sum_{D\in\mathcal C_\Lambda}|D|^2.$$</div>
<p>Both sides are bounded by $|\Lambda|^2$, irrespective of full-cluster susceptibility. The <a href="/coverage/sources/perclib-22d8485-geometry/">seven-contract inventory</a> records this expected identity and the singleton and empty-configuration witnesses. Every trace uses connectivity in the full graph, so paths outside the observation window remain part of the observable.</p>

## Scope of the tagged partition statements {#section-partition-associations}

<p>The source bundles <a href="/tag/Q0D1/">Q0D1</a>, <a href="/tag/0N0J/">0N0J</a>, <a href="/tag/TUD2/">TUD2</a> and <a href="/tag/GUHT/">GUHT</a> without imposing countability on their deterministic clauses. In particular, the partition identity and the nonnegative indicator sum hold on arbitrary vertex sets. Countability is supplied separately for measurability of the cluster and its extended volume. The two-point normalization and symmetry identities in Q0D1 also hold without countability, with the source's outer-measure convention; interpreting general connection events as measurable events still requires justification.</p>
<p>The finite-sum statement applies either to a finite ambient vertex set or to a finite induced domain. In its second form, the ambient set may be arbitrary, but the summands are internal cluster sizes. They are not full-cluster traces in an observation window. The empty finite vertex set is included. The <a href="/coverage/sources/perclib-22d8485-associations/">association inventory</a> records the four source statements and their separate hypotheses.</p>


## Full-volume tails and the root contribution {#section-volume-tails}

<p>On a countable vertex set, let $N=|K_x|\in\mathbb N\cup\{\infty\}$. Its measurability makes every tail $\{N\geq n\}$ measurable, even at the extended threshold $n=\infty$. The finite-threshold events decrease to $\{N=\infty\}$, so continuity from above gives</p>
<div class="math-display">$$\mathbb P_q(N=\infty)=\inf_{n\geq0}\mathbb P_q(N\geq n).$$</div>
<p>The pointwise identity $N=\sum_{n\geq0}\mathbf1_{\{N\geq n+1\}}$ holds also at $N=\infty$. Tonelli therefore proves the <a href="/tag/CSY8/">tail-sum identity</a> with infinite values allowed. The sum starts at the positive threshold one: its first term is one because the cluster contains its root.</p>
<p>For each integer $n\geq1$, integration of $n\mathbf1_{\{N\geq n\}}\leq N$ gives $n\mathbb P_q(N\geq n)\leq\chi_q(x)$. If susceptibility is finite, the tail infimum is zero, proving <a href="/tag/INZI/">almost-sure finiteness</a>. Conversely, positive probability of $N=\infty$ makes every positive-integer tail at least that positive number, so their sum diverges. Neither argument makes infinite susceptibility sufficient for percolation; the <a href="/tag/SA9P/">bounded-degree example</a> shows that distinction within percolation itself. At $n=0$, the source's undivided inequality is simply $0\leq\chi_q(x)$.</p>
<p>Every open neighbour of $x$ belongs to its cluster, and $x$ is a further vertex. Thus $1+D_x\leq N$ pointwise. The <a href="/tag/SZLN/">degree expectation identity</a> gives</p>
<div class="math-display">$$1+\sum_{y\ne x}q_{xy}\leq\chi_q(x),$$</div>
<p>again in extended nonnegative arithmetic. The source also derives this by summing $q_{xy}\leq\tau_q(x,y)$ for $y\ne x$ and retaining $\tau_q(x,x)=1$. An open pair connects its distinct endpoints, which proves the individual measure inequality on arbitrary vertex types. That set inclusion alone does not establish measurability of an unrestricted connection event on an uncountable type. Diagonal probabilities belong in neither row sum.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-volume-quantile/">volume-source inventory</a> keeps these full-volume statements separate from finite-window witnesses and their exhaustion limits. It retains the one-vertex susceptibility-one case and the all-open countably infinite example, where both the connection sum and susceptibility are infinite.</p>



## Covariance comes from a common cluster {#section-cluster-covariance}

<a id="tag-25Z4" data-assertion="theorem" data-title="Distinct-cluster comparison and a diagonal covariance bound"></a>
<p>Consider independent bond percolation on a countable graph and a finite nonempty observation set $\Lambda$. Let $\mathscr C$ be the partition of $\Lambda$ by full clusters. For nonnegative increasing functions $F,G:[1,|\Lambda|]\to[0,\infty)$, put</p>
<div class="math-display">$$T_F=\sum_{A\in\mathscr C}|A|F(|A|),\qquad
T_G=\sum_{A\in\mathscr C}|A|G(|A|).$$</div>
<p>Then</p>
<div class="math-display">$$\mathbb E\sum_{\substack{A,B\in\mathscr C\\A\ne B}}|A||B|F(|A|)G(|B|)
\leq\mathbb E T_F\,\mathbb E T_G,$$</div>
<div class="math-display">$$0\leq\operatorname{Cov}(T_F,T_G)
\leq\mathbb E\sum_{A\in\mathscr C}|A|^2F(|A|)G(|A|).$$</div>
<p>The pair sum is ordered. In particular, with $S_p=\sum_A|A|^p$,</p>
<div class="math-display">$$0\leq\operatorname{Cov}(S_p,S_q)\leq\mathbb E S_{p+q}\qquad(p,q\geq1).$$</div>
<p><em>Proof.</em> First work on a finite graph. Write $a_x=|K(x)\cap\Lambda|$ for $x\in\Lambda$. The ordered distinct-cluster sum equals</p>
<div class="math-display">$$\sum_{x,y\in\Lambda}F(a_x)G(a_y)\mathbf1_{\{y\notin K(x)\}}.$$</div>
<p>Condition on the complete vertex set $K(x)=C$. This event is determined by edges inside $C$ and between $C$ and its complement: it requires internal connection to $x$ and closed boundary edges. Edges with both endpoints outside $C$ retain their independent product law. If $y\notin C$, its conditional cluster is therefore the cluster in the induced graph on $C^c$. Coupling with an independent full configuration by adding the omitted vertices and edges shows</p>
<div class="math-display">$$\mathbb E[G(a_y)\mid K(x)=C]\leq\mathbb E G(a_y)\qquad(y\notin C).$$</div>
<p>Only conditioning events of positive probability are used. Multiplying by the nonnegative $F(|C\cap\Lambda|)$, summing over $C$ and dropping the remaining indicator gives</p>
<div class="math-display">$$\mathbb E[F(a_x)G(a_y)\mathbf1_{\{y\notin K(x)\}}]
\leq\mathbb E F(a_x)\,\mathbb E G(a_y).$$</div>
<p>Summing over $x,y$ proves the distinct-cluster comparison. Both $T_F=\sum_{x\in\Lambda}F(a_x)$ and $T_G$ are increasing functions of the bonds, so Harris gives nonnegative covariance. Separating the diagonal $A=B$ from $T_FT_G$ and applying the comparison to the other terms gives the upper bound. Taking $F(a)=a^{p-1}$ and $G(a)=a^{q-1}$ yields the power-sum assertion.</p>
<p>On a countable graph, exhaust the edges by finite sets while keeping $\Lambda$. The partition of the finite window eventually agrees with its full partition, by finite connection witnesses. All observables above are bounded by constants depending only on $|\Lambda|,F,G$, so bounded convergence passes the inequalities to the limit. Neither local finiteness nor finite full-cluster sizes are required.</p>
<p>This proves and extends the finite-block estimates in Lemmas 4.6–4.7 of the <a href="/coverage/sources/hierarchical-volumes-2211.05686v1/">hierarchical-volume paper</a>. The upper comparison comes from the conditional product law outside an explored cluster; it does not assert independence between two clusters in the original configuration.</p>



## Counting large clusters in a finite window {#section-large-cluster-counts}

<p>Let independent bond percolation be given on a countable graph, and fix a finite observation set $\Lambda\subseteq V$. Partition $\Lambda$ by the full open clusters, writing $\mathscr C_\Lambda$ for the resulting nonempty blocks. These are intersections with full clusters, not components of the graph induced by $\Lambda$; a path joining two observed vertices may leave the window. Full clusters may be infinite.</p>
<p>For an integer $m\ge1$, put</p>
<div class="math-display">$$
N_m=\#\{A\in\mathscr C_\Lambda:|A|\ge m\},\qquad
\lambda_m=\frac1m\sum_{x\in\Lambda}\mathbb P(|K_x\cap\Lambda|\ge m).
$$</div>
<p>Write $(n)_r=n(n-1)\cdots(n-r+1)$ for $r\ge1$, with $(n)_0=1$.</p>

<a id="tag-SPLO" data-assertion="theorem" data-title="Factorial moments and upper tails for the number and ordered sizes of large observed clusters"></a>
<p>For every integer $r\ge0$ and every $t\ge0$,</p>
<div class="math-display">$$
\mathbb E(N_m)_r\le\lambda_m^r,\qquad
\mathbb E(1+t)^{N_m}\le e^{\lambda_m t},
$$</div>
<p>where the zeroth powers equal one. In particular, for integers $r\ge1$,</p>
<div class="math-display">$$
\mathbb P(N_m\ge r)\le\min\left\{1,\frac{\lambda_m^r}{r!}\right\}.
$$</div>
<p>When $\lambda_m&gt;0$ and $r\ge\lambda_m$, the exponential bound also gives</p>
<div class="math-display">$$
\mathbb P(N_m\ge r)\le e^{-\lambda_m}\left(\frac{e\lambda_m}{r}\right)^r.
$$</div>
<p>If $\lambda_m=0$, then $N_m=0$ almost surely. Let $M_r(\Lambda)$ denote the $r$th largest block size, padded with zeros when there are fewer than $r$ blocks. If $\mathbb P(|K_x\cap\Lambda|\ge m)\le f(m)$ for every $x\in\Lambda$, then</p>
<div class="math-display">$$
\mathbb P(M_r(\Lambda)\ge m)
\le\min\left\{1,\frac{(|\Lambda|f(m)/m)^r}{r!}\right\}
\le\min\left\{1,\left(\frac{e|\Lambda|f(m)}{rm}\right)^r\right\}.
$$</div>

<p><em>Proof.</em> Count ordered $r$-tuples of observed roots that lie in distinct blocks of size at least $m$. Grouping the tuples by their blocks gives the pointwise identity</p>
<div class="math-display">$$
\sum_{(x_1,\ldots,x_r)\in\Lambda^r}
\mathbf1_{\{K_{x_i}\text{ pairwise distinct}\}}
\prod_{i=1}^r\mathbf1_{\{|K_{x_i}\cap\Lambda|\ge m\}}
=\sum_{\substack{A_1,\ldots,A_r\in\mathscr C_\Lambda\ \text{distinct}\\|A_i|\ge m\ \text{for all }i}}
\prod_{i=1}^r|A_i|
\ge m^r(N_m)_r.
$$</div>
<p>Each volume-threshold functional is increasing in the full cluster and has a Borel evaluation. Apply the <a href="/tag/39JJ/">distinct-cluster product bound</a> to every root tuple and sum. The resulting sum of products of marginal probabilities factors, giving</p>
<div class="math-display">$$
m^r\mathbb E(N_m)_r
\le\left(\sum_{x\in\Lambda}\mathbb P(|K_x\cap\Lambda|\ge m)\right)^r.
$$</div>
<p>This proves the factorial-moment bound, including the empty window; $r=0$ is immediate. Since $N_m\le\lfloor|\Lambda|/m\rfloor$, the binomial expansion is finite. Thus</p>
<div class="math-display">$$
\mathbb E(1+t)^{N_m}
=\sum_{r\ge0}\frac{t^r}{r!}\mathbb E(N_m)_r
\le\sum_{r\ge0}\frac{(\lambda_m t)^r}{r!}
=e^{\lambda_m t}.
$$</div>
<p>On $N_m\ge r$, one has $(N_m)_r\ge r!$, which proves the first tail bound. Applying Markov to $(1+t)^{N_m}$ and taking $t=r/\lambda_m-1\ge0$ proves the exponential bound. The first moment handles $\lambda_m=0$. Finally, $\{M_r(\Lambda)\ge m\}=\{N_m\ge r\}$, and $r!\ge(r/e)^r$, giving the ordered-size estimates. $\square$</p>

<p>A uniform full-cluster tail bound $\mathbb P(|K_x|\ge m)\le A m^{-\alpha}$, with $A,\alpha&gt;0$, is a sufficient input, since $|K_x\cap\Lambda|\le|K_x|$. It gives</p>
<div class="math-display">$$
\mathbb P(M_r(\Lambda)\ge m)
\le\min\left\{1,\left(\frac{eA|\Lambda|}{r\,m^{1+\alpha}}\right)^r\right\}.
$$</div>
<p>For the mean-field tail exponent $\alpha=1/2$, this is an upper bound at the volume scale $(|\Lambda|/r)^{2/3}$. The one-cluster tail estimate is an input; the counting argument supplies neither that estimate nor a matching lower bound.</p>
<p>The generating-function comparison is not stochastic domination by a Poisson variable. With a one-vertex window and $m=1$, both $N_m$ and $\lambda_m$ equal one, whereas a Poisson variable of mean one is zero with positive probability. No independence of the cluster-count indicators is asserted. These are new deductions from the written countable Reimer argument and the partition identity, with independent review and Lean formalisation pending.</p>


## Ordered discovery and convex comparison {#section-window-convex-comparison}

<p>Continue with independent bonds on a countable graph and a finite window $\Lambda=\{v_1,\ldots,v_n\}$. Fix a real $p\ge1$. For the partition $\mathscr C_\Lambda$ by full clusters, write $S_p=\sum_{A\in\mathscr C_\Lambda}|A|^p$. Assign each block to its first vertex in the chosen order:</p>
<div class="math-display">$$
Z_i=|K(v_i)\cap\Lambda|^p
\mathbf1_{\{K(v_i)\cap\{v_1,\ldots,v_{i-1}\}=\varnothing\}},
\qquad U_i=\sum_{j\le i}Z_j.
$$</div>
<p>Thus $U_n=S_p$, and $\sum_i Z_i^k=S_{kp}$ for every positive integer $k$. Each $Z_i$ takes values in $\{0,1,2^p,\ldots,n^p\}$.</p>

<a id="tag-WR5S" data-assertion="theorem" data-title="Finite-window power sums are bounded in convex order by independent ordered-discovery contributions"></a>
<p>Let $Z_1^*,\ldots,Z_n^*$ be independent variables with the respective marginal laws of $Z_1,\ldots,Z_n$. For every real-valued convex function $\varphi$ on $\mathbb R$,</p>
<div class="math-display">$$
\mathbb E\varphi(S_p)\le
\mathbb E\varphi\!\left(\sum_{i=1}^n Z_i^*\right).
$$</div>
<p>In particular, for every real $t$,</p>
<div class="math-display">$$
\log\mathbb E e^{t(S_p-\mathbb ES_p)}
\le \mathbb E\sum_{A\in\mathscr C_\Lambda}
       \bigl(e^{t|A|^p}-1-t|A|^p\bigr).
$$</div>
<p>These statements include the empty window, when all sums are zero. They require neither finite full clusters nor finite susceptibility. The independent variables depend on the order of the window; the displayed exponential bound does not.</p>

<p><em>Proof.</em> First suppose only finitely many edges can be open. For $r&gt;0$, the event $Z_i\ge r$ is the disjoint union of events $K(v_i)=C$ for which $C$ avoids the earlier window vertices and $|C\cap\Lambda|^p\ge r$. Conditional on any such event of positive probability, the edges outside $C$ retain their independent laws. Moreover, $U_{i-1}$ is computed entirely from clusters in $C^c$.</p>
<p>Couple this exterior graph to an independent full graph by restoring the removed vertices and bonds. Restoring the vertices as isolated vertices leaves $U_{i-1}$ unchanged, since none is an earlier window vertex. Adding bonds can only increase $U_{i-1}$: merging a counted block with an uncounted block increases its observed size, and merging two counted blocks replaces $a^p+b^p$ by $(a+b)^p\ge a^p+b^p$. Hence, for every real $u$,</p>
<div class="math-display">$$
\mathbb P(U_{i-1}\ge u\mid K(v_i)=C)
\le \mathbb P(U_{i-1}\ge u).
$$</div>
<p>Summing over the possible $C$ gives</p>
<div class="math-display">$$
\mathbb P(U_{i-1}\ge u,Z_i\ge r)
\le \mathbb P(U_{i-1}\ge u)\mathbb P(Z_i\ge r).
\tag{1}
$$</div>
<p>For $r\le0$ this is equality. On a countable graph, exhaust the edge set by finite sets and set all remaining bonds to closed. For each configuration the resulting partition of $\Lambda$ eventually equals its full partition: every connected pair in the finite window has a finite open path, and finitely many such paths suffice for all pairs. Thus all the $Z_i$ and $U_i$ eventually agree with their full-graph values. Bounded convergence passes (1) to the limit, including thresholds at atoms of their laws.</p>
<p>For completeness, the finite-valued comparison used in the <a href="/tag/I2YU/">fourth-moment argument</a> follows directly from (1). If $X,Y$ have ordered supports $x_0&lt;\cdots&lt;x_a$ and $y_0&lt;\cdots&lt;y_b$, the expansion of $\varphi(X+Y)$ by successive differences has two marginal terms and mixed terms with coefficients</p>
<div class="math-display">$$
\varphi(x_j+y_k)-\varphi(x_{j-1}+y_k)
-\varphi(x_j+y_{k-1})+\varphi(x_{j-1}+y_{k-1})\ge0.
$$</div>
<p>The inequality is convexity: the increment across an interval of fixed length increases when the interval is translated to the right. The corresponding mixed term is multiplied by $\mathbf1_{\{X\ge x_j,Y\ge y_k\}}$. The joint-tail bound therefore gives $\mathbb E\varphi(X+Y)\le\mathbb E\varphi(X+Y^*)$ when $Y^*$ is independent of $X$ with the law of $Y$.</p>
<p>Apply this with $X=U_{i-1}$ and $Y=Z_i$. Induction on $i$, using the convex function $x\mapsto\mathbb E\varphi(x+Z_i^*)$, replaces the remaining earlier sum by its independent counterpart. This proves the first assertion. All variables have finite support, so every expectation exists.</p>
<p>Take $\varphi(x)=e^{tx}$, which is convex for either sign of $t$. Independence and $\log a\le a-1$ for $a&gt;0$ give</p>
<div class="math-display">$$
\log\mathbb E e^{tS_p}
\le\sum_i\log\mathbb E e^{tZ_i}
\le\sum_i\mathbb E(e^{tZ_i}-1)
=\mathbb E\sum_{A\in\mathscr C_\Lambda}(e^{t|A|^p}-1).
$$</div>
<p>Subtract $t\mathbb ES_p=t\sum_i\mathbb EZ_i$ to obtain the centered bound. $\square$</p>

<p>For $t\ge0$, this extends the <a href="/tag/1NYQ/">finite-graph exponential product estimate</a> to observation windows. The proof also covers $t&lt;0$; this does not follow by substituting a negative parameter in the earlier expansion with nonnegative cluster weights. The comparison concerns finitely many bounded discovery variables even when the ambient graph is infinite. It makes no claim about the general unbounded-variable convex-comparison theorem.</p>

## Concentration of observed power sums {#section-window-concentration}

<a id="tag-SARI" data-assertion="corollary" data-title="Gaussian lower tails and Bennett upper tails for finite-window cluster power sums"></a>
<p>In the preceding setting put $\mu=\mathbb ES_p$ and $v=\mathbb ES_{2p}$. Suppose $v&gt;0$, and choose a deterministic $b&gt;0$ such that $|A|^p\le b$ for every observed block almost surely; $b=n^p$ always works for a nonempty window. For every $u\ge0$,</p>
<div class="math-display">$$
\mathbb P(S_p\le\mu-u)\le\exp\!\left(-\frac{u^2}{2v}\right),
$$</div>
<div class="math-display">$$
\mathbb P(S_p\ge\mu+u)
\le\exp\!\left[-\frac{v}{b^2}
 h\!\left(\frac{bu}{v}\right)\right],
\qquad h(s)=(1+s)\log(1+s)-s.
$$</div>
<p>The simpler Bernstein bound also holds:</p>
<div class="math-display">$$
\mathbb P(S_p\ge\mu+u)
\le\exp\!\left[-\frac{u^2}{2(v+bu/3)}\right].
$$</div>
<p>Here $v$ is a moment bound, not an assertion that $\operatorname{Var}(S_p)=v$. If $v=0$, the window is empty and $S_p=0$ deterministically; both deviation events have probability zero for $u&gt;0$.</p>

<p><em>Proof.</em> For $t,y\ge0$, $e^{-ty}-1+ty\le t^2y^2/2$. The exponential bound in <a href="/tag/WR5S/">WR5S</a> therefore gives</p>
<div class="math-display">$$
\log\mathbb E e^{-t(S_p-\mu)}\le vt^2/2.
$$</div>
<p>Exponential Markov with $t=u/v$ proves the lower-tail estimate. For $0\le y\le b$, expansion in nonnegative powers gives</p>
<div class="math-display">$$
e^{ty}-1-ty
\le\frac{y^2}{b^2}(e^{tb}-1-tb),
\qquad
\log\mathbb E e^{t(S_p-\mu)}
\le\frac{v}{b^2}(e^{tb}-1-tb).
$$</div>
<p>Exponential Markov with $t=b^{-1}\log(1+bu/v)$ gives the Bennett bound. For $0\le t&lt;3/b$, the factorial inequality $j!\ge2\,3^{j-2}$ for $j\ge2$ also gives</p>
<div class="math-display">$$
\log\mathbb E e^{t(S_p-\mu)}
\le\frac{vt^2}{2(1-bt/3)}.
$$</div>
<p>Take $t=u/(v+bu/3)$ to obtain the Bernstein bound. The case $u=0$ in all three estimates is the trivial probability bound one. $\square$</p>

<p>For the observed squared mass, the lower-tail estimate reads</p>
<div class="math-display">$$
\mathbb P\bigl(S_2\le(1-\varepsilon)\mathbb ES_2\bigr)
\le\exp\!\left[-\frac{\varepsilon^2(\mathbb ES_2)^2}
                         {2\mathbb ES_4}\right]
\qquad(\varepsilon\ge0).
$$</div>
<p>Thus $\mathbb ES_4=o((\mathbb ES_2)^2)$ along a sequence of nonempty finite windows gives an exponential bound in the ratio $(\mathbb ES_2)^2/\mathbb ES_4$ for each fixed relative lower deviation. No largest-cluster estimate is needed for this conclusion. The upper bound still requires control of the jump sizes: $b$ must be deterministic and cannot be replaced by the random largest block. One may instead estimate the full exponential cluster sum in WR5S. These are additional written deductions, with independent mathematical review and Lean formalisation pending.</p>
