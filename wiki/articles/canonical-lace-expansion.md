---
{
  "id": "canonical-lace-expansion",
  "title": "The canonical lace expansion",
  "subtitle": "Independent bond models, exact identities and refined diagram bounds",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Double connections and cutting pivotal bonds give the canonical coefficients. Deleted-bond diagrams bound every order; explicit contraction gives summability for the lace and Fourier identities.",
  "context": [
    "The initial definitions use independent bond percolation on a countable vertex set V, with arbitrary edge probabilities q and with loops ignored.",
    "The two-point function is τ(x,y)=P(x↔y), including τ(x,x)=1. All diagram sums are nonnegative and may be infinite.",
    "The lattice expansion below specializes explicitly to nearest-neighbour percolation on ℤᵈ; its parameter p is the probability of each nearest-neighbour bond."
  ],
  "related": [
    "lace-expansion",
    "lace-coefficient-diagrams",
    "weighted-lace-coefficients",
    "disjoint-occurrence",
    "bk-inequality",
    "triangle-condition",
    "connection-kernels",
    "branching-random-walk",
    "backbone-connections"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "lace expansion",
    "double connectivity",
    "doubly connected",
    "first pivotal bond",
    "cutting bond",
    "lace coefficient",
    "irreducible two-point function",
    "infrared bound"
  ],
  "prototypeUses": [
    "connectivity",
    "bk-inequality",
    "triangle-condition"
  ]
}
---

<p>The lace expansion expresses connectivity through an alternating series of irreducible connections. The <a href="/articles/lace-expansion/">cutting-bond expansion</a> gives the nearest-neighbour presentation of Heydenreich–van der Hofstad. Here the coefficient construction and exact identities are developed for arbitrary countable independent bond models, with each finiteness or summability hypothesis stated explicitly.</p>
<p>The all-order bounds refine the <a href="/articles/lace-coefficient-diagrams/">lattice coefficient diagrams</a> by retaining bond deletion, the initial diagonal and the excluded joining diagonal, and by separating the terminal norm from the interior transfer. An explicit contraction criterion supplies coefficient summability; the Fourier quotient additionally requires the stated translation and integrability hypotheses.</p>

## Double connections and the diagonal {#section-double-connections}

<a id="tag-ZUND" data-assertion="definition" data-title="Double connection"></a><p>Write $x\Longleftrightarrow y$ when the connection event $\{x\leftrightarrow y\}$ occurs disjointly with itself. Thus there are two disjoint finite sets of open bonds, each sufficient to connect $x$ to $y$. Equivalently, for distinct vertices there are two bond-disjoint open paths. The convention at $x=y$ is that the event always occurs: the two empty witnesses suffice.</p>
<p>A double connection survives deletion of any single bond. This is the obstruction to a pivotal bond: in a connected configuration, an open bond is pivotal for $x\leftrightarrow y$ exactly when deleting it destroys that connection. Paths may share vertices; disjointness here concerns bonds.</p>

<a id="tag-DLF1" data-assertion="proposition" data-title="Double connection is connection without a pivotal pair"></a><p>For any vertex set and configuration,</p>
<div class="math-display">$$x\Longleftrightarrow y\quad\Longleftrightarrow\quad x\leftrightarrow y\ \text{ and no pair is pivotal for }x\leftrightarrow y.$$</div>
<p>Here a pair $e$ is pivotal if opening $e$ gives a connection and deleting $e$ destroys it. On a realised connection, the right side therefore says that deleting any one pair preserves connection. The connection hypothesis is essential. No finiteness or countability of the vertex set is required.</p>
<p><em>Proof.</em> One of two disjoint witnesses avoids any specified pair. Conversely, choose a finite simple connecting path. If deletion of each edge preserves the connection, that edge's endpoints have a route avoiding the edge, obtained by combining an avoiding connection with the original path's prefix and suffix. Each step of the path is consequently a double connection. Double connections are transitive: two pairs of disjoint paths can be joined by cutting at their first contacts and routing to those contacts along opposite sides. Repeatedly joining the finitely many steps gives two disjoint witnesses between the original endpoints.</p>

<a id="tag-U8OS" data-assertion="definition" data-title="Zeroth lace coefficient"></a><p>The zeroth coefficient is</p>
<div class="math-display">$$\pi^{(0)}(x,y)=\mathbf1_{\{x\ne y\}}\,\mathbb P(x\Longleftrightarrow y).$$</div>
<p>In real-valued notation this is $\mathbb P(x\Longleftrightarrow y)-\mathbf1_{\{x=y\}}$. In particular $\pi^{(0)}(x,x)=0$. The subtraction removes the deterministic empty connection; it does not remove genuine double connections between distinct vertices.</p>

<a id="tag-X30S" data-assertion="proposition" data-title="BK bound for the zeroth lace coefficient"></a><p>For every pair of vertices,</p>
<div class="math-display">$$0\leq\pi^{(0)}(x,y)\leq\mathbf1_{\{x\ne y\}}\,\tau(x,y)^2.$$</div>
<p><em>Proof.</em> For $x\ne y$, apply the <a href="#/bk-inequality">BK inequality</a> to the disjoint occurrence of the increasing connection event with itself. Both sides vanish on the diagonal. The product comes from BK, not from independence of the two connection events.</p>

<a id="tag-S9QJ" data-assertion="proposition" data-title="Single-bond deletion sharpens the double-connection bound"></a><p>Fix any bond $e$ and write $\tau^{\setminus e}(x,y)$ for the probability that $x$ connects to $y$ after deleting $e$. Then</p>
<div class="math-display">$$\mathbb P(x\Longleftrightarrow y)\leq\tau(x,y)\tau^{\setminus e}(x,y),\qquad \pi^{(0)}(x,y)\leq\mathbf1_{\{x\ne y\}}\tau(x,y)\tau^{\setminus e}(x,y).$$</div>
<p><em>Proof.</em> At least one of two disjoint connection witnesses avoids $e$. It witnesses the deleted-bond connection and is disjoint from the other witness for ordinary connection. Both events are increasing, so BK applies. Since $\tau^{\setminus e}\le\tau$, this retains at least as much information as the square bound.</p>

## Combining diagonal and distinct-vertex contributions {#section-diagram-bound}

<p>Fix a root $o$, and write</p>
<div class="math-display">$$B_o^\circ=\sum_{x\ne o}\tau(o,x)^2,\qquad \nabla_o=\sum_{x,y}\tau(o,x)\tau(x,y)\tau(y,o).$$</div>
<a id="tag-RCHH" data-assertion="proposition" data-title="Factor-four triangle bound for the zeroth lace coefficient"></a><p>The zeroth coefficient satisfies</p>
<div class="math-display">$$1+4\sum_x\pi^{(0)}(o,x)\leq\nabla_o.$$</div>
<p>Consequently a finite rooted triangle implies summability of the real-valued zeroth coefficient, with</p>
<div class="math-display">$$\sum_x\pi^{(0)}(o,x)\leq\frac{\nabla_o-1}{4}.$$</div>
<p><em>Proof.</em> Write $M_o=\sum_x\pi^{(0)}(o,x)$. Separate the triangle sum into $(x,y)=(o,o)$, $x=o\ne y$, $y=o\ne x$, $x=y\ne o$, and pairs of distinct non-root vertices. Symmetry and $\tau(x,x)=1$ give the exact identity</p>
<div class="math-display">$$\nabla_o=1+3B_o^\circ+\sum_{\substack{x\ne o,\ y\ne o\\x\ne y}}\tau(o,x)\tau(x,y)\tau(y,o).$$</div>
<p>The square bound gives $M_o\le B_o^\circ$. For a distinct vertex $x$, two bond-disjoint paths from $o$ to $x$ cannot both consist of the single bond $\{o,x\}$, because the model has no parallel bonds. One path therefore has an interior vertex $u\notin\{o,x\}$. Split it at $u$ and keep the other path. These three bond-disjoint witnesses imply</p>
<div class="math-display">$$\{o\Longleftrightarrow x\}\subseteq\bigcup_{u\notin\{o,x\}}\bigl(\{o\leftrightarrow u\}\circ\{u\leftrightarrow x\}\circ\{o\leftrightarrow x\}\bigr).$$</div>
<p>The union bound and iterated BK give $\pi^{(0)}(o,x)\le\sum_{u\notin\{o,x\}}\tau(o,u)\tau(u,x)\tau(x,o)$. After summing over $x$, the distinct-vertex part of the triangle is at least $M_o$. Together the two estimates give $\nabla_o\ge1+3M_o+M_o$.</p>
<p>The intermediate bound $1+3B_o^\circ\le\nabla_o$ holds for every nonnegative symmetric kernel with diagonal one, and its factor $3$ is best possible: a two-vertex bond model with opening probability $p&gt;0$ has $B_o^\circ=p^2$ and $\nabla_o=1+3p^2$. Improving the coefficient estimate to factor $4$ uses the extra path geometry through a distinct third vertex.</p>
<p>The factor $4$ in the coefficient bound is also best possible over independent bond models. On the complete graph with three vertices and every bond open with probability one, both other vertices are doubly connected to the root, so $M_o=2$. Every two-point function equals one, hence $\nabla_o=9=1+4M_o$.</p>

## Cutting a connection at its first pivotal bond {#section-cutting}

<a id="tag-UINB" data-assertion="definition" data-title="Connection through a vertex set"></a><p>In the general countable bond model, write $x\overset A\longleftrightarrow y$ when $x$ connects to $y$ but no open path connects them entirely inside $A^c$. Equivalently, the connection event occurs and its restriction to the graph induced on $A^c$ does not. Write $\tau^{\setminus A}(x,y)$ for the probability of that restricted connection, taking it to be zero if either endpoint lies in $A$.</p>
<p>On the diagonal, $\{x\overset A\longleftrightarrow x\}$ is the whole sample space if $x\in A$ and is empty otherwise. If either endpoint lies in $A$, going through $A$ is just ordinary connection. Enlarging $A$ enlarges the through-set event; the empty set gives the empty event. By contrast, this event need not increase when more bonds open: a path $x$–$a$–$y$ goes through $\{a\}$, but opening the direct bond $\{x,y\}$ creates an avoiding path and destroys the through-set event.</p>

<a id="tag-ZTE7" data-assertion="proposition" data-title="Exact decomposition into avoiding and through-set connections"></a><p>For every vertex set $A$,</p>
<div class="math-display">$$\tau(x,y)=\tau^{\setminus A}(x,y)+\mathbb P(x\overset A\longleftrightarrow y).$$</div>
<p><em>Proof.</em> Connections avoiding $A$ form a measurable subset of all connections. Its set difference is the through-set event. The two pieces are disjoint, so their probabilities add exactly.</p>

<a id="tag-84FZ" data-assertion="proposition" data-title="Through-set connection bound with constant one"></a><p>The through-set probability satisfies</p>
<div class="math-display">$$\mathbb P(x\overset A\longleftrightarrow y)\leq\sum_{a\in A}\tau(x,a)\tau(a,y).$$</div>
<p><em>Proof.</em> Choose a simple open connecting path. It meets $A$, and splitting at a vertex $a\in A$ gives two bond-disjoint connection witnesses, with an empty witness allowed at an endpoint. Thus the through-set event is contained in $\bigcup_{a\in A}(\{x\leftrightarrow a\}\circ\{a\leftrightarrow y\})$. Apply the union bound and BK to these increasing connection events. No monotonicity of the through-set event is used. The constant is best possible: for $A=\{x\}$ both sides equal $\tau(x,y)$, which can be positive.</p>

## The exact cutting-bond partition {#section-cutting-partition}

<a id="tag-FWTN" data-assertion="definition" data-title="No-earlier-cutting and occupied directed cutting events"></a><p>Fix vertices $x,y,u,v$ and a vertex set $A$. For a configuration $\omega$, put $\omega^- = \omega\setminus\{\{u,v\}\}$ and $\omega^+ = \omega\cup\{\{u,v\}\}$. Write $D_{x,y}(u,v)$ for the directed pivotal event: $x$ connects to $y$ in $\omega^+$, does not connect to $y$ in $\omega^-$, and the deleted configuration $\omega^-$ connects $x$ to $u$ and $v$ to $y$. The underlying bond need not be open; its orientation is determined after deletion.</p>
<p>Define $E'(x,y;A)$ to be $\{x\overset A\longleftrightarrow y\}$ with no directed pivotal pair $(u,v)$ satisfying $x\overset A\longleftrightarrow u$. The occupied cutting event is</p>
<div class="math-display">$$C_A(x,y;u,v)=E'(x,u;A)\cap D_{x,y}(u,v)\cap\{\{u,v\}\text{ is open}\}.$$</div>
<p>The occupation condition is essential. It turns a pair which could connect the two components into a bond on the realised connection. Pairs with $u=v$ contribute the empty event, and opposite orientations cannot both be pivotal in the displayed direction.</p>

<a id="tag-VXRP" data-assertion="proposition" data-title="Disjoint cutting-bond partition of a through-set connection"></a><p>For every configuration,</p>
<div class="math-display">$$\{x\overset A\longleftrightarrow y\}=E'(x,y;A)\mathbin{\dot\cup}\mathop{\dot\bigcup}_{(u,v)\in V\times V}C_A(x,y;u,v).$$</div>
<p>All the displayed events are pairwise disjoint. This set identity requires no finiteness or countability of $V$, and no assumption that clusters are finite.</p>
<p><em>Proof.</em> If a through-set connection is outside $E'$, choose an eligible directed pivotal pair whose initial endpoint has least graph distance from $x$. If an eligible pivotal appeared before that endpoint, it would also be pivotal for the full connection and would have strictly smaller initial-endpoint distance. Thus the chosen prefix is in $E'$ and gives a cutting event. Conversely, continuing a through-set prefix across an occupied pivotal bond gives a through-set connection. Distinct pivotal bonds on a realised connection occur in an order: one is pivotal for the prefix ending at the initial endpoint of the other. Two cutting bonds would therefore contradict the later one's $E'$ condition. Reverse orientations are excluded by the two separated components. This also excludes overlap with the no-eligible-pivotal event.</p>

<a id="tag-HU0W" data-assertion="proposition" data-title="Exact probability sum over directed cutting bonds"></a><p>On a countable vertex set with arbitrary independent bond probabilities,</p>
<div class="math-display">$$\mathbb P(x\overset A\longleftrightarrow y)=\mathbb P(E'(x,y;A))+\sum_{u\in V}\sum_{v\in V}\mathbb P(C_A(x,y;u,v)).$$</div>
<p>All these events are measurable, so countable additivity applies to the disjoint partition. Each configuration with a cutting bond appears exactly once. There is no factor $2$ for the two orientations and no loss from a union bound.</p>
<p>This generalizes the cutting-bond partition of Heydenreich–van der Hofstad, Lemma 6.5, equations (6.2.21)–(6.2.22), to arbitrary countable inhomogeneous bond models. It does not assume $\theta=0$. Rewriting each cutting-event probability as an expectation involving a restricted two-point function is a separate conditional factorisation step; the partition alone is not the finite lace-expansion identity below.</p>

## The initial first-pivotal identity {#section-first-pivotal}

<p>For the full vertex set, going through $V$ is ordinary connection. Every pivotal pair on a realised connection has a unique orientation from the source component to the target component. The characterization by absence of pivotal pairs therefore gives</p>
<div class="math-display">$$E'(x,y;V)=\{x\Longleftrightarrow y\}.$$</div>
<p>Thus $C_V(x,y;u,v)$ is the event that $(u,v)$ is the first occupied pivotal bond, with $x$ doubly connected to its initial endpoint $u$. The disjoint cutting partition becomes a partition of ordinary connection into double connection and its unique first-pivotal event.</p>

<a id="tag-CM8M" data-assertion="proposition" data-title="Exact initial two-point decomposition at the first pivotal bond"></a><p>For arbitrary independent bond probabilities on a countable vertex set,</p>
<div class="math-display">$$\tau(x,y)=\mathbf1_{\{x=y\}}+\pi^{(0)}(x,y)+\sum_{u\in V}\sum_{v\in V}\mathbb P(C_V(x,y;u,v)).$$</div>
<p><em>Proof.</em> Set $A=V$ in the exact cutting probability sum, use $E'(x,y;V)=\{x\Longleftrightarrow y\}$, and split the double-connection probability into its deterministic diagonal and zeroth coefficient. The identity holds without a finite-cluster or subcriticality assumption. Each directed pair again has coefficient one. This is the initial probability partition; extracting an edge weight and a restricted continuation from its summands still requires the cutting-bond factorisation.</p>

## Factorisation across a cutting bond {#section-cutting-factorisation}

<a id="tag-ONAY" data-assertion="proposition" data-title="Cutting-bond factorisation on two independent configurations"></a><p>Fix $x,y,u,v\in V$ and $A\subseteq V$ in the countable independent bond model. Assume that the cluster of $x$ after deleting $\{u,v\}$ is finite almost surely. Let $\omega_0,\omega_1$ be independent configurations with law $\mathbb P_q$, and put $C_0=\widetilde C_0^{(u,v)}(x)$. Then</p>
<div class="math-display">$$\mathbb P_q(C_A(x,y;u,v))=q(\{u,v\})\,(\mathbb P_q\otimes\mathbb P_q)\!\left(E'_0(x,u;A)\cap\{v\leftrightarrow y\text{ in }C_0^c\text{ in }\omega_1\}\right).$$</div>
<p>The exterior event requires both $v$ and $y$ to lie in $C_0^c$ and a connection in the graph induced there. In particular, when $v=y$ it records membership in $C_0^c$, not an unconditional diagonal connection. The event $E'_0$ uses the original first configuration $\omega_0$; only the cluster $C_0$ is computed with $\{u,v\}$ deleted. No global subcriticality assumption is imposed: the stated almost-sure finiteness concerns this deleted cluster at this root.</p>
<p><em>Proof.</em> Split according to the finite value of $C_0$. On the exterior event, $v$ lies outside the deleted source component, so removing the separating pair does not change the prefix event $E'(x,u;A)$. The deleted-cluster slice and this prefix event are determined by bonds touching $C_0$, except the cutting pair. The exterior connection uses bonds with both endpoints outside $C_0$. These two coordinate sets and the cutting coordinate are disjoint, so independence factors their probabilities, with the exact factor $q(\{u,v\})$. Sum over the countably many finite vertex sets and realize the exterior factor in the independent configuration $\omega_1$. Almost-sure finiteness makes these slices exhaustive up to a null set.</p>
<p>This is the inhomogeneous form of the cutting-bond lemma, Heydenreich–van der Hofstad, Lemma 6.4 and equation (6.2.13), used after the cutting partition in equation (6.2.23). There is no multiplicative estimate or loss in the identity. Iterating it through the random sets in all coefficient layers, and deriving the signed remainder formula, are further steps.</p>

<p>For the lattice formulas below take nearest-neighbour bond percolation on $\mathbb Z^d$, $d\ge2$, with parameter $p\in[0,1]$. Put $\tau(x)=\mathbb P_p(0\leftrightarrow x)$ and</p>
<div class="math-display">$$J(z)=p\mathbf1_{\{|z|_1=1\}}=2dpD(z),\qquad D(z)=\frac1{2d}\mathbf1_{\{|z|_1=1\}},\qquad (f*g)(x)=\sum_y f(y)g(x-y).$$</div>
<p>Thus $J$ is an edge-probability kernel and has mass $2dp$. A convention in which the parameter itself is the mass of $J$ changes every occurrence of $2dp$.</p>
<p>For an oriented bond $b=(u,v)$ let $\widetilde C^b(a)$ be the cluster of $a$ after declaring the underlying unordered bond closed. A connection which is not double has a unique first pivotal bond, oriented from $a$ towards $x$ as above. Before it, $a$ is doubly connected to the initial endpoint.</p>
<p>The first-pivotal partition leads to an expectation involving the two-point function restricted to the complement of $\widetilde C^b(a)$. The restriction matters: the continuation from $v$ must avoid the already exposed cluster. Replacing it by the unrestricted two-point function introduces an error, which is expanded again at a cutting bond.</p>
<p>In the coefficient construction, the set $A$ in $E'(a,x;A)$ is supplied by an earlier, independent configuration.</p>

## Coefficients and the finite expansion {#section-finite-expansion}

<a id="tag-NLIV" data-assertion="definition" data-title="Positive higher lace coefficients"></a><p>The coefficient construction applies to an arbitrary countable vertex set $V$ and inhomogeneous bond profile $q$. Put $w_q(u,v)=q(\{u,v\})$ for $u\ne v$ and $w_q(u,u)=0$. For order $k\ge1$, take $k+1$ independent configurations $\omega_0,\ldots,\omega_k$, each with law $\mathbb P_q$, and sum over all directed pairs $b_i=(u_i,v_i)\in V\times V$, $0\le i&lt;k$. Set $v_{-1}=x$, $u_k=y$, and $C_i=\widetilde C_i^{b_i}(v_{i-1})$, the cluster in layer $i$ with bond $b_i$ deleted. Define</p>
<div class="math-display">$$\pi_q^{(k)}(x,y)=\sum_{b_0,\ldots,b_{k-1}}\left(\prod_{i=0}^{k-1}w_q(u_i,v_i)\right)\mathbb E_q\!\left[\mathbf1_{\{x\Longleftrightarrow u_0\}_0}\prod_{i=1}^{k}\mathbf1_{E'_i(v_{i-1},u_i;C_{i-1})}\right].$$</div>
<p>A subscript $i$ evaluates the event or cluster in $\omega_i$. Thus the first deleted cluster is rooted at $x$, each later deleted cluster at the preceding bond's target, and the last $E'$ event ends at $y$. Repeated directed pairs in different layers are allowed. Diagonal pairs have zero weight, so arbitrary loop probabilities have no effect. These are nonnegative, possibly infinite sums; no finiteness or signed convergence is part of the definition. Order zero is $\pi_q^{(0)}(x,y)$ from the zeroth-coefficient definition.</p>
<p>For nearest-neighbour percolation, $w_q(u,v)=J(v-u)$ vanishes away from nearest-neighbour pairs. Specializing the initial vertex to $0$, the final vertex to $x$, and writing $\pi^{(n)}(x)=\pi_q^{(n)}(0,x)$ gives the lattice formula</p>
<div class="math-display">$$\pi^{(n)}(x)=\sum_{b_0,\ldots,b_{n-1}}\left(\prod_{i=0}^{n-1}J(v_i-u_i)\right)\mathbb E\!\left[\mathbf1_{\{0\Longleftrightarrow u_0\}_0}\prod_{i=1}^{n}\mathbf1_{E'_i(v_{i-1},u_i;C_{i-1})}\right].$$</div>
<p>Here $n\ge1$, $v_{-1}=0$, and $u_n=x$. The full initial double-connection indicator, including its certain diagonal $u_0=0$, remains in every positive order; only order zero removes the diagonal. In the finite lattice expansion below, the signed partial sum is $\Pi_N=\sum_{n=0}^N(-1)^n\pi^{(n)}$.</p>

<p>In the general countable model, define the nonnegative remainder $r_q^{(n)}(x,y)$ using the construction of $\pi_q^{(n+1)}(x,y)$, replacing only its last $E'$ event by $\{v_n\overset{C_n}\longleftrightarrow y\}_{n+1}$. It uses $n+1$ directed pairs and $n+2$ independent layers, retaining the first double connection and the preceding $n$ events $E'$. Like the coefficients, these remainder magnitudes take values in $[0,\infty]$.</p>

<a id="tag-YLI6" data-assertion="proposition" data-title="Exact nonnegative initial lace expansion"></a><p>Fix $x$ in a countable independent bond model. Assume that, for every pair $u,v$, the cluster of $x$ after deleting $\{u,v\}$ is finite almost surely. Then, for every $y$,</p>
<div class="math-display">$$\begin{aligned}\tau_q(x,y)+r_q^{(0)}(x,y)
&=\mathbf1_{\{x=y\}}+\pi_q^{(0)}(x,y)+\sum_v w_q(x,v)\tau_q(v,y)\\
&\quad+\sum_{u,v}\pi_q^{(0)}(x,u)w_q(u,v)\tau_q(v,y).
\end{aligned}$$</div>
<p>This is an equality of extended nonnegative quantities and requires no summability assumption. <em>Proof.</em> Apply the cutting-bond factorisation to each term of the first-pivotal identity. In the independent continuation layer, unrestricted connection splits into connection avoiding the deleted cluster and connection through it. Adding the latter contribution to the left gives the unrestricted continuation on the right. Countable nonnegative summation and the identity $\mathbb P_q(x\Longleftrightarrow u)=\mathbf1_{\{x=u\}}+\pi_q^{(0)}(x,u)$ give the formula. This is the nonnegative version of the source's initial step (6.2.20); signed subtraction additionally requires finite quantities.</p>

<a id="tag-G1IE" data-assertion="proposition" data-title="Exact nonnegative lace recurrence at every order"></a><p>Assume that, for every root $a$ and pair $u,v$, the cluster of $a$ after deleting $\{u,v\}$ is finite almost surely. For every $n\ge0$ and $x,y\in V$,</p>
<div class="math-display">$$r_q^{(n)}(x,y)+r_q^{(n+1)}(x,y)=\pi_q^{(n+1)}(x,y)+\sum_{u,v}\pi_q^{(n+1)}(x,u)w_q(u,v)\tau_q(v,y).$$</div>
<p>The identity holds in $[0,\infty]$, without assuming finite coefficient or remainder sums. <em>Proof.</em> Condition on the preceding independent layers and apply the cutting partition and factorisation to the last through-set event. Split unrestricted continuation into its avoiding and through-set parts. The no-earlier-cut contribution gives the next coefficient; the new through-set term gives the next remainder. Integrate over the preceding layers and sum their nonnegative bond weights. This is the additive form of the iteration in (6.2.24) and (6.2.27)–(6.2.28); it uses no cancellation of infinite sums.</p>

<a id="tag-XMUG" data-assertion="theorem" data-title="Finite signed expansion under explicit mass and continuation bounds"></a><p>In the countable bond model, retain the preceding almost-sure finiteness hypothesis at every root and deleted pair. Fix $N\ge0$ and endpoints $x,y$. Assume</p>
<div class="math-display">$$M_n(x):=\sum_u\pi_q^{(n)}(x,u)&lt;\infty\quad(0\le n\le N),\qquad \sum_v w_q(u,v)\tau_q(v,y)\le C&lt;\infty\quad\text{for every }u.$$</div>
<p>The continuation bound concerns this fixed endpoint $y$; uniformity over all target endpoints is not required. All coefficients and remainders used below are then finite. Regard them as real numbers and put</p>
<div class="math-display">$$\Pi_{q,N}(x,z)=\sum_{n=0}^{N}(-1)^n\pi_q^{(n)}(x,z),\qquad R_{q,N}(x,y)=(-1)^{N+1}r_q^{(N)}(x,y).$$</div>
<p>The finite signed identity is</p>
<div class="math-display">$$\begin{aligned}\tau_q(x,y)&=\mathbf1_{\{x=y\}}+\Pi_{q,N}(x,y)+\sum_v w_q(x,v)\tau_q(v,y)\\
&\quad+\sum_{u,v}\Pi_{q,N}(x,u)w_q(u,v)\tau_q(v,y)+R_{q,N}(x,y).
\end{aligned}$$</div>
<p><em>Proof.</em> Each nonnegative coefficient continuation is at most $C M_n(x)$. The remainder bounds give $r_q^{(0)}(x,y)\le C(1+M_0(x))$ and $r_q^{(n)}(x,y)\le C M_n(x)$ for $n\ge1$. Thus the initial identity and recurrence may be read as real equalities. Alternating the recurrence telescopes to the displayed formula. Absolute summability permits interchanging the finite alternating sum with the spatial continuation sums. No limit in $N$ is taken.</p>

<a id="tag-VYRB" data-assertion="theorem" data-title="Finite inclusion-exclusion lace expansion and remainder sign"></a><p>Proposition 6.1 of the source states that, if $\theta(p)=\mathbb P_p(|C(0)|=\infty)=0$, then for every $N\ge0$ the real-valued finite expansion is</p>
<div class="math-display">$$\tau=\delta_0+\Pi_N+(\delta_0+\Pi_N)*J*\tau+R_N.$$</div>
<p>Here $R_N=(-1)^{N+1}r_N$ with $r_N\ge0$. More explicitly, sum over $b_0,\ldots,b_N$, retain the first double-connection indicator and the $E'$ indicators with $1\le i\le N$, and replace the final $E'$ indicator of the coefficient construction by the event $\{v_N\overset{C_N}\longleftrightarrow x\}_{N+1}$:</p>
<div class="math-display">$$r_N(x)=\sum_{b_0,\ldots,b_N}\left(\prod_{i=0}^{N}J(v_i-u_i)\right)\mathbb E\!\left[\mathbf1_{\{0\Longleftrightarrow u_0\}_0}\left(\prod_{i=1}^{N}\mathbf1_{E'_i(v_{i-1},u_i;C_{i-1})}\right)\mathbf1_{\{v_N\overset{C_N}\longleftrightarrow x\}_{N+1}}\right].$$</div>
<p>The product over $i$ is empty when $N=0$. Thus the zeroth remainder is nonpositive and the first remainder is nonnegative. In particular, deleting the remainder gives an upper bound at even $N$ and a lower bound at odd $N$.</p>
<p>The source is <a href="https://rhofstad.win.tue.nl/survey-high-d-percolation.pdf">Heydenreich–van der Hofstad, author manuscript of 17 March 2017</a>, Proposition 6.1 and equations (6.2.7), (6.2.25), (6.2.27)–(6.2.28). The cutting-bond lemma supplies conditional factorisation after the cluster is exposed; the cutting-bond partition and repeated subtraction produce the identity. A finite number of expansion steps does not assert convergence as $N\to\infty$.</p>
<p>The <a href="/tag/XMUG/">general-kernel finite signed expansion</a> realizes this formula under explicit mass and continuation bounds; it does not identify those hypotheses with the source's stated $\theta(p)=0$ assumption. Almost-sure finiteness of the exposed cluster and summability are distinct requirements. The later diagram estimates (7.2.11) and (7.5.3), on pages 73 and 82, bound each coefficient's $\ell^1$ mass by triangle diagrams. Finiteness of those diagrams suffices at each fixed order; their geometric smallness is needed to sum over expansion orders, as discussed after Proposition 7.4 on page 83.</p>

## A first-coefficient diagram retaining bond deletion {#section-first-diagram}

<p>Work again in the countable bond model and write $D_e(r,s)=\mathbb P_q(r\leftrightarrow s\text{ after deleting }e)$. For a directed pair $b=(u,v)$, put $e=\{u,v\}$ and define the diagram factors</p>
<div class="math-display">$$L_b(x,a)=\begin{cases}
D_e(x,a),&x=u,\\
\displaystyle\min\!\left\{\tau_q(x,u)D_e(x,u),\ \sum_z\tau_q(x,u)D_e(x,z)\tau_q(z,u)D_e(z,a)\right\},&x\ne u,
\end{cases}$$</div>
<div class="math-display">$$R_b(a,y)=\begin{cases}\tau_q(v,y)D_e(v,y),&a=v,\\\tau_q(v,a)\tau_q(a,y),&a\ne v.\end{cases}$$</div>
<a id="tag-LCX2" data-assertion="proposition" data-title="First lace coefficient with deleted-arm and endpoint gains"></a><p>With no finite-cluster or summability assumption,</p>
<div class="math-display">$$\pi_q^{(1)}(x,y)\le\sum_{u,v}w_q(u,v)\sum_a L_{(u,v)}(x,a)R_{(u,v)}(a,y).$$</div>
<p><em>Proof.</em> Choose a contact $a$ with the first deleted cluster. In the first layer, the event is a double connection from $x$ to $u$ together with a deleted-bond connection from $x$ to $a$. The case $x=u$ is exact. Otherwise a first-contact decomposition gives four disjoint connection witnesses, retaining deletion on both $x$–$z$ and $z$–$a$ arms. Iterated BK gives the sum in $L_b$; the separate deletion-sensitive double-connection bound gives its other entry, so their minimum is valid. In the second layer, contact at $a=v$ makes $E'$ a double connection, giving the deletion-sensitive factor in $R_b$. Other contacts give two disjoint connection witnesses. Independence between layers and nonnegative summation finish the bound.</p>
<p>The prefactor one is attained. On two vertices $\{0,1\}$ with sole bond probability $p$, at $x=y=0$ both $\pi_q^{(1)}(0,0)$ and the displayed diagram equal $p^2$. Deleting the bond isolates the root, so only $(u,v,a)=(0,1,0)$ contributes. This refinement and its equality witness follow from the direct arguments above.</p>

## All-order diagrams with deletion and diagonal gains {#section-all-order-diagrams}

<p>Continue with arbitrary independent bond probabilities on a countable vertex set. Suppress the subscript $q$ on $\tau$, and retain $D_e$ and $w_q$ from above. A diagram state is an ordered pair $\xi=(a,b)$, recording a branch vertex and an outgoing bond's initial endpoint. The initial row is</p>
<div class="math-display">$$A_x(a,b)=\begin{cases}\mathbf1_{\{a=x\}},&b=x,\\\tau(x,a)\tau(x,b)\tau(a,b),&b\ne x.\end{cases}$$</div>
<p>The first case handles the certain initial diagonal exactly. The connector retains the deleted outgoing bond:</p>
<div class="math-display">$$C_{\mathrm d}\bigl((a,b),(z,t)\bigr)=\sum_v w_q(b,v)D_{\{b,v\}}(a,z)\tau(v,t).$$</div>
<p>The two interior geometries are</p>
<div class="math-display">$$\begin{aligned}
B_1\bigl((z,t),(w,u)\bigr)&=\tau(z,t)\tau(z,u)\tau(t,w)\tau(w,u),\\
B_2\bigl((z,t),(w,u)\bigr)&=\mathbf1_{\{t=w\}}\tau(z,u)\sum_{r\ne w}\tau(w,r)\tau(r,z)\tau(r,u).
\end{aligned}$$</div>
<p>The exclusion $r\ne w$ in $B_2$ removes the zero-length joining arm already covered by the first geometry. Define the transfer kernel $K$ and the separate terminal factor $L$ by</p>
<div class="math-display">$$\begin{aligned}
K(\xi,\eta)&=\sum_{z,t}C_{\mathrm d}\bigl(\xi,(z,t)\bigr)\bigl(B_1+B_2\bigr)\bigl((z,t),\eta\bigr),\\
L(\xi,y)&=\sum_{z,t}C_{\mathrm d}\bigl(\xi,(z,t)\bigr)\tau(z,t)\tau(z,y)\tau(t,y).
\end{aligned}$$</div>
<p>Let $A_x^{(0)}=A_x$, $A_x^{(n+1)}(\eta)=\sum_\xi A_x^{(n)}(\xi)K(\xi,\eta)$ and $\mathcal D_n(x,y)=\sum_\xi A_x^{(n)}(\xi)L(\xi,y)$. All these sums take values in $[0,\infty]$.</p>

<a id="tag-3W0M" data-assertion="theorem" data-title="All-order coefficient bound by deleted-bond diagrams"></a><p>For every $n\ge0$ and every pair of endpoints,</p>
<div class="math-display">$$\pi_q^{(n+1)}(x,y)\le\mathcal D_n(x,y).$$</div>
<p>No finite-cluster or summability assumption is required. <em>Proof.</em> Mark a vertex of the last deleted cluster in a coefficient prefix. Finite open-path witnesses and first-contact decompositions give two possible interior geometries with six disjoint connection arms. Keep the deleted connection in the outgoing layer, apply iterated BK within each layer, and use independence between layers. Nonnegative sum rearrangements contract these arms into $C_{\mathrm d}(B_1+B_2)$, giving one application of $K$ for each interior step. The final three arms contract into $L$. The initial diagonal is handled by $A_x$, completing the induction.</p>

<p>For a fixed root, define the initial mass and the uniform transfer and terminal row norms by</p>
<div class="math-display">$$\alpha_x=\sum_\xi A_x(\xi),\qquad \rho=\sup_\xi\sum_\eta K(\xi,\eta),\qquad \kappa=\sup_\xi\sum_y L(\xi,y).$$</div>
<p>Any uniform upper bounds for $\rho$ and $\kappa$ may be substituted in the following estimates.</p>

<a id="tag-0HQZ" data-assertion="proposition" data-title="Geometric coefficient mass bound with separate terminal norm"></a><p>For every $n\ge0$,</p>
<div class="math-display">$$M_{n+1}(x)=\sum_y\pi_q^{(n+1)}(x,y)\le\alpha_x\rho^n\kappa.$$</div>
<p><em>Proof.</em> Each application of $K$ multiplies the row mass by at most $\rho$. The final factor costs $\kappa$, so no additional interior transfer is needed at the terminal layer. Apply the coefficient comparison and sum nonnegative terms.</p>

<a id="tag-5KBX" data-assertion="theorem" data-title="Coefficient summability from diagram contraction"></a><p>If $\alpha_x&lt;\infty$, $\kappa&lt;\infty$ and $\rho&lt;1$, then</p>
<div class="math-display">$$\sum_{n\ge0}M_n(x)&lt;\infty.$$</div>
<p><em>Proof.</em> The zeroth coefficient satisfies $\pi_q^{(0)}(x,y)\le A_x(x,y)$, so $M_0(x)\le\alpha_x$. Summing the positive-order geometric bounds gives the quantitative estimate</p>
<div class="math-display">$$\sum_{n\ge0}M_n(x)\le M_0(x)+\frac{\alpha_x\kappa}{1-\rho}.$$</div>
<p>This establishes summability of the actual canonical coefficients from the displayed diagram criterion, without an assumed coefficient comparison or a finite-cluster hypothesis.</p>
<p>For each fixed order, the weaker conditions $\alpha_x,\rho,\kappa&lt;\infty$ already make the coefficient row finite; $\rho&lt;1$ is needed only for summing all orders. Combined with almost-sure finite deleted clusters at every cutting root and the fixed-endpoint continuation bound, finite diagram norms justify the <a href="/tag/XMUG/">finite signed expansion</a>. The source's $\theta(p)=0$ statement and its finiteness caveat above remain separate. The <a href="/tag/1741/">infinite equation</a> additionally uses a finite continuation bound uniform in both endpoints and almost-sure finite deleted clusters.</p>

## A sharper transfer norm under translations {#section-transfer-norm}

<p>Now let the vertex set be a countable additive abelian group and assume $q(\{a+g,b+g\})=q(\{a,b\})$. Put</p>
<div class="math-display">$$\Delta=\sum_{u,w}\tau(0,u)\tau(u,w)\tau(w,0),\qquad T(b,t)=\sum_v w_q(b,v)\tau(v,t),$$</div>
<div class="math-display">$$\begin{aligned}
M_{\mathrm d}(\xi)&=\sum_{z,t}C_{\mathrm d}\bigl(\xi,(z,t)\bigr)\tau(z,t),\qquad M_{\mathrm d}=\sup_\xi M_{\mathrm d}(\xi),\\
M^\circ&=\sup_{a,b}\sum_{z,t}\tau(a,z)T(b,t)\mathbf1_{\{z\ne t\}}\tau(z,t).
\end{aligned}$$</div>
<a id="tag-MERJ" data-assertion="proposition" data-title="Transfer bound retaining deleted and off-diagonal masses"></a><p>The transfer rows satisfy</p>
<div class="math-display">$$\sum_\eta K(\xi,\eta)\le\Delta\bigl(M_{\mathrm d}(\xi)+M^\circ\bigr),\qquad \rho\le\Delta\bigl(M_{\mathrm d}+M^\circ\bigr).$$</div>
<p>The inequality holds for nonnegative extended sums. <em>Proof.</em> In the first geometry, the <a href="/tag/UZ7J/">open triangle is bounded by the diagonal triangle</a> $\Delta$; the remaining connector mass is exactly $M_{\mathrm d}(\xi)$. For the second geometry, translations move its triangle to the origin. The excluded joining diagonal leaves the off-diagonal factor in $M^\circ$. Tonelli's theorem then separates the triangle and the remaining mass.</p>
<p>To compare with a coarser estimate, let $M=\sup_{a,b}\sum_{z,t}\tau(a,z)T(b,t)\tau(z,t)$. Dropping deletion gives $M_{\mathrm d}\le M$, and filling in the joining diagonal gives $M^\circ\le M$. Thus the displayed bound retains both improvements in the chain $\rho\le\Delta(M_{\mathrm d}+M^\circ)\le\Delta(M+M^\circ)\le2\Delta M$. The initial diagonal, deleted connector, excluded joining diagonal and separate terminal norm are refinements of the diagrammatic framework in Heydenreich–van der Hofstad, Sections 7.3–7.5; these refined formulas are not asserted to occur verbatim there.</p>
<p>A nonzero finite model realizes the contraction criterion. On two vertices with sole bond probability $1/4$ and arbitrary loop probabilities, direct finite sums give</p>
<div class="math-display">$$\alpha_x=\frac98,\qquad \rho=\frac{1365}{4096}&lt;1,\qquad \kappa=\frac{35}{128},\qquad \pi_q^{(1)}(0,0)=\frac1{16}&gt;0.$$</div>
<p>The transfer row is $195/1024$ at a diagonal pair state and $1365/4096$ at an off-diagonal state. The corresponding terminal masses are $25/256$ and $35/128$, so the displayed uniform constants are exact maxima. The diagram criterion therefore gives finite total coefficient mass at either root.</p>

## Removing the remainder {#section-convergence}

<a id="tag-LVRG" data-assertion="proposition" data-title="Positive-order remainder bound with coefficient one"></a><p>For arbitrary independent bond probabilities on a countable vertex set and every $n\ge1$,</p>
<div class="math-display">$$r_q^{(n)}(x,y)\le\sum_{u,v}\pi_q^{(n)}(x,u)w_q(u,v)\tau_q(v,y).$$</div>
<p>No finite-cluster or summability hypothesis is required; the inequality holds in $[0,\infty]$. <em>Proof.</em> In the final independent layer, bound connection through the preceding deleted cluster by ordinary connection. Integrating this layer and summing over the last directed pair leaves exactly the order-$n$ coefficient. The multiplicative constant is one. At order zero the prefix is the full double-connection probability, so the corresponding bound uses $\mathbf1_{\{x=u\}}+\pi_q^{(0)}(x,u)$. This is the general-model version of the positive-order estimate (6.3.2).</p>

<a id="tag-4PAZ" data-assertion="proposition" data-title="Optimality of the constant-one remainder bound"></a><p>Any nonnegative universal prefactor $K$ in the preceding remainder bound must satisfy $K\ge1$. Two-vertex models already force this at order one. With sole bond probability $p$,</p>
<div class="math-display">$$\pi_q^{(1)}(0,0)=p^2,\qquad \pi_q^{(1)}(0,1)=0,\qquad r_q^{(1)}(0,0)=\sum_{u,v}\pi_q^{(1)}(0,u)w_q(u,v)\tau_q(v,0)=p^4.$$</div>
<p><em>Proof.</em> The repeated directed pair $(0,1),(0,1)$ contributes two bond weights and one cross-connection in each of the final two independent layers, giving $p^4$. The upper-bound convolution also equals $p^4$. Taking $p=1$ makes both sides one and forces $K\ge1$. Repeated pairs across independent layers are allowed by the coefficient and remainder definitions. This sharpness witness is a direct computation, not an additional assumption on the source expansion.</p>

<a id="tag-6UGP" data-assertion="proposition" data-title="Uniform vanishing of nonnegative remainders"></a><p>Fix the root $x$ and put $M_n(x)=\sum_u\pi_q^{(n)}(x,u)$. Suppose</p>
<div class="math-display">$$\sum_{n\ge1}M_n(x)&lt;\infty,\qquad \sum_v w_q(u,v)\tau_q(v,y)\le C&lt;\infty\quad\text{for all }u,y.$$</div>
<p>Then</p>
<div class="math-display">$$\sup_y r_q^{(n)}(x,y)\le C M_n(x)\quad(n\ge1),\qquad \lim_{n\to\infty}\sup_y r_q^{(n)}(x,y)=0.$$</div>
<p><em>Proof.</em> Apply the preceding bound and retain the supplied continuation constant $C$. Summability implies $M_n(x)\to0$, so the displayed bound proves uniform convergence. One can take $C=\sup_{u,y}\sum_v w_q(u,v)\tau_q(v,y)$ whenever it is finite. Only the positive coefficient masses are needed; the initial remainder does not affect the limit. No finite-cluster assumption or signed expansion identity enters this conclusion. Obtaining the full lace equation additionally requires the finite signed identities and passage to the limit in their other terms.</p>

<a id="tag-1741" data-assertion="proposition" data-title="The canonical infinite lace equation under summability"></a><p>In the countable bond model, assume that every root's cluster after deletion of any fixed pair is finite almost surely. Fix $x$ and suppose</p>
<div class="math-display">$$\sum_{n\ge0}\sum_u\pi_q^{(n)}(x,u)&lt;\infty,\qquad \sum_v w_q(u,v)\tau_q(v,z)\le C&lt;\infty\quad\text{for all }u,z.$$</div>
<p>The canonical signed row</p>
<div class="math-display">$$\Pi_q(x,z)=\sum_{n\ge0}(-1)^n\pi_q^{(n)}(x,z)$$</div>
<p>is absolutely summable in $z$. Its partial sums satisfy $\Pi_{q,N}(x,z)\to\Pi_q(x,z)$, and the signed remainders satisfy $R_{q,N}(x,z)\to0$. For every endpoint $y$, the resulting real-valued identity is</p>
<div class="math-display">$$\begin{aligned}\tau_q(x,y)&=\mathbf1_{\{x=y\}}+\Pi_q(x,y)+\sum_v w_q(x,v)\tau_q(v,y)\\
&\quad+\sum_{u,v}\Pi_q(x,u)w_q(u,v)\tau_q(v,y).
\end{aligned}$$</div>
<p><em>Proof.</em> Total nonnegative coefficient mass gives absolute summability of the signed series over order and endpoint. The total absolute continuation contribution is at most $C\sum_{n\ge0}M_n(x)$, so its sums can also be interchanged and its partial sums converge. The positive-order remainder estimate gives $|R_{q,N}(x,y)|\le C M_N(x)$ for $N\ge1$, uniformly in $y$, and hence vanishing of the remainder. Take limits in the finite signed expansion. The coefficient row mass at $x$ suffices; the finite-cluster assumption is imposed at every cutting root.</p>
<p>For nearest-neighbour percolation on $\mathbb Z^d$, write $\Pi(z)=\Pi_q(0,z)$. The identity becomes</p>
<div class="math-display">$$\tau=\delta_0+\Pi+(\delta_0+\Pi)*J*\tau.$$</div>
<p>The model-dependent continuation constant $C_p=\|J*\tau\|_\infty\le2dp$ retains the two-point information. In particular, $\|R_N\|_\infty\le C_p\|\pi^{(N)}\|_1$ for $N\ge1$. If additionally $\chi(p)&lt;\infty$, nonnegative summation gives $\|R_N\|_1\le2dp\,\|\pi^{(N)}\|_1\chi(p)$. Finite susceptibility is not needed for the pointwise infinite equation above. Summability of all coefficient masses remains an explicit hypothesis, supplied in particular by the <a href="/tag/5KBX/">diagram contraction criterion</a>; the zeroth bound alone does not establish it.</p>

## Fourier analysis and the bootstrap {#section-fourier}

<a id="tag-PI55" data-assertion="proposition" data-title="Canonical Fourier quotient on a countable abelian group"></a><p>Let $G$ be a countable additive abelian group, and assume the bond profile is translation invariant: $q(\{a+t,b+t\})=q(\{a,b\})$. Put $J(z)=w_q(0,z)$, $\tau(z)=\tau_q(0,z)$ and $\Pi(z)=\Pi_q(0,z)$. Suppose</p>
<div class="math-display">$$\sum_z J(z)&lt;\infty,\qquad \chi_q(0)=\sum_z\tau(z)&lt;\infty,\qquad \sum_{n\ge0}\sum_z\pi_q^{(n)}(0,z)&lt;\infty.$$</div>
<p>For any unitary additive character $\psi:G\to\{w\in\mathbb C:|w|=1\}$, with $\psi(a+b)=\psi(a)\psi(b)$ and $\psi(0)=1$, define $\widehat f(\psi)=\sum_z f(z)\psi(z)$. Then</p>
<div class="math-display">$$1-(1+\widehat\Pi(\psi))\widehat J(\psi)\ne0,\qquad \widehat\tau(\psi)=\frac{1+\widehat\Pi(\psi)}{1-(1+\widehat\Pi(\psi))\widehat J(\psi)}.$$</div>
<p><em>Proof.</em> Translation invariance transports finite susceptibility to every root, making its cluster and every deleted cluster finite almost surely. Finite step mass bounds the continuation uniformly, so the canonical infinite expansion applies. The three rooted kernels are absolutely summable. Grouping absolutely convergent sums and using the character identity turns convolution into multiplication, giving $\widehat\tau=1+\widehat\Pi+(1+\widehat\Pi)\widehat J\widehat\tau$. If its denominator vanished, this equality would force $1+\widehat\Pi=0$, making that same denominator one. The convolution equation and denominator nonvanishing are conclusions of the stated percolation hypotheses.</p>
<p>For nearest-neighbour percolation on $\mathbb Z^d$, take $\psi_k(z)=e^{ik\cdot z}$, $k\in[-\pi,\pi]^d$, and use $J=2dpD$. This gives</p>
<div class="math-display">$$\widehat\tau(k)=\frac{1+\widehat\Pi(k)}{1-2dp\widehat D(k)(1+\widehat\Pi(k))}.$$</div>
<p>At criticality, finite susceptibility and an ordinary absolutely convergent transform of $\tau$ are generally unavailable. Critical formulas require an additional limiting or Fourier-integrability argument; substituting $p=p_c$ into this statement is not justified by the displayed algebra.</p>
<p>To obtain the high-dimensional infrared bound, one still needs quantitative estimates on every coefficient and on its Fourier variation, uniform up to criticality. Such estimates depend on the two-point function they are meant to control. The bootstrap in Chapters 7–8 closes this dependence by improving a preliminary bound and excluding an intermediate range. The exact expansion, its analytic convergence, and verification of the <a href="#/triangle-condition">triangle condition</a> are separate mathematical steps. A normalized kernel constructed from $J*(\delta_0+\Pi)$ may have negative entries, so it cannot automatically be treated as a random-walk transition probability.</p>
