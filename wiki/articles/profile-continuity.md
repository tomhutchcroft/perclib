---
{
  "id": "profile-continuity",
  "title": "Continuity in the percolation profile",
  "subtitle": "Finite coordinates, coupling bounds, and an infinite-volume caveat",
  "kind": "method",
  "category": "Methods",
  "summary": "Finite-cylinder expectations vary continuously with the coordinate probabilities. Finite open witnesses give lower semicontinuity in countable products, but full connection probabilities need not be continuous. Summable profile changes control all measurable event probabilities in total variation.",
  "context": [
    "Independent Bernoulli coordinates indexed by $I$, with profile $q\\in[0,1]^I$.",
    "Profiles carry the product topology: convergence means convergence at each fixed coordinate.",
    "The finite-coordinate statements require no countability of $I$."
  ],
  "related": [
    "product-model",
    "russo-formula",
    "connectivity",
    "harris-inequality"
  ],
  "sourceIds": ["perclib-finite-cylinders", "perclib-finite-expectations", "perclib-finite-continuity", "perclib-monotone-coupling", "perclib-product-law", "perclib-profile-total-variation", "perclib-susceptibility-continuity", "perclib-profile-regularity", "perclib-theta-semicontinuity", "hutchcroft-book"],
  "aliases": [
    "profile continuity",
    "cylinder continuity",
    "lower semicontinuity",
    "finite expectation",
    "coupling estimate"
  ],
  "prototypeUses": []
}
---

## The canonical configuration law {#section-product-law}

<p>The <a href="/tag/8NWX/">product law</a> can be written either on binary coordinate functions or on their open sets. The maps $\omega\mapsto\mathbf1_\omega$ and $b\mapsto\{i:b_i=1\}$ are inverse measurable maps, since each coordinate is unchanged. Transporting the product of the one-coordinate laws $q_i\delta_1+(1-q_i)\delta_0$ through this identification gives the same probability measure $\mathbb P_q$ on subsets of $I$. Its total mass is one for every index set.</p>
<p>For a deterministic subset $U\subseteq I$, sample independent probability-$p$ coordinates on $U$ and extend their open set to $I$ with all coordinates outside $U$ closed. The resulting law has profile $q_i=p$ on $U$ and $q_i=0$ outside it: the two laws agree on every finite cylinder and hence on the product sigma-algebra. Taking $U=I$ gives the homogeneous product law. This construction is valid for arbitrary $I$ and $U$; it is a measurable pushforward statement, not an assumption that an uncountable intersection of coordinate events is measurable.</p>

## Restricting the product law {#section-restriction}

<a id="tag-ZNMQ" data-assertion="theorem" data-title="Finite restrictions and weighted expectations on arbitrary coordinate sets"></a>
<p>For any index set $I$, finite $F\subseteq I$, and profile $q\in[0,1]^I$, restriction $\rho_F(\omega)=\omega\cap F$ is measurable and carries $\mathbb P_q$ to the Bernoulli product law with profile $q|_F$. Consequently, for every $\eta\subseteq F$,</p>
<div class="math-display">$$\mathbb P_q(\omega\cap F=\eta)=w_q(\eta),\qquad w_q(\eta)=\prod_{i\in\eta}q_i\prod_{i\in F\setminus\eta}(1-q_i).$$</div>
<p>For every real function $f$ on the subsets of $F$ and every family $\mathcal A\subseteq 2^F$,</p>
<div class="math-display">$$\mathbb E_q[f(\omega\cap F)]=\sum_{\eta\subseteq F}f(\eta)w_q(\eta),\qquad \mathbb P_q(\omega\cap F\in\mathcal A)=\sum_{\eta\in\mathcal A}w_q(\eta).$$</div>
<p>In particular, for disjoint finite $A,B\subseteq I$,</p>
<div class="math-display">$$\mathbb P_q(A\subseteq\omega,\ B\cap\omega=\varnothing)=\prod_{i\in A}q_i\prod_{i\in B}(1-q_i).$$</div>
<p><em>Proof.</em> Each coordinate of the restriction is an original coordinate, so restriction is measurable. The event $\omega\cap F=\eta$ prescribes finitely many independent open and closed coordinates and has the displayed product probability. These events partition the entire space, identifying the restriction law and giving the expectation and event formulas by finite summation. The observable is bounded because its domain is finite, hence integrable. Take $F=A\cup B$ and $\eta=A$ for the mixed cylinder formula.</p>
<p>No countability of $I$ is used. The all-open case $B=\varnothing$ gives $\mathbb P_q(A\subseteq\omega)=\prod_{i\in A}q_i$, including the singleton marginal. If $F=\varnothing$, its only configuration has weight one and the expectation is $f(\varnothing)$. On two coordinates with probabilities $a,b$, the configuration with only the first open has mass $a(1-b)$. At $(a,b)=(1,0)$ the whole law is concentrated on that configuration. These endpoint cases use the same formula, without division by a coordinate probability.</p>

## Finite observations {#section-finite}

<a id="tag-RA0Z" data-assertion="theorem" data-title="Finite-cylinder expectations are continuous in the ambient profile"></a><p>Let $F\subseteq I$ be finite and let $f:\{0,1\}^F\to\mathbb R$. Then</p><div class="math-display">$$q\longmapsto\mathbb E_q[f(\omega|_F)]$$</div><p>is continuous on $[0,1]^I$, including profiles with zero or one coordinates. In particular, pointwise convergence of profiles implies convergence of every fixed finite-cylinder probability. For bond percolation, connection probabilities inside a fixed finite vertex domain have this property.</p><p><em>Proof.</em> Restriction to $F$ has the independent Bernoulli law with profile $q|_F$. Its expectation is the <a href="/tag/7WIO/">finite configuration polynomial</a></p><div class="math-display">$$\sum_{\eta\subseteq F} f(\eta)\prod_{i\in\eta}q_i\prod_{i\in F\setminus\eta}(1-q_i).$$</div><p>It is continuous in its finitely many arguments, and restriction $q\mapsto q|_F$ is continuous for the product topology. A connection inside a finite vertex domain uses only its finitely many internal pairs, so it is a cylinder event. An empty coordinate block gives a constant expectation.</p>

## A quantitative comparison {#section-coupling}

<a id="tag-RGN6" data-assertion="proposition" data-title="Finite-block profile perturbation bound"></a><p>For the same $F$ and $f$, put $\operatorname{osc}(f)=\max f-\min f$. For any two profiles $q,r$,</p><div class="math-display">$$\left|\mathbb E_q f(\omega|_F)-\mathbb E_r f(\omega|_F)\right|\leq\operatorname{osc}(f)\min\!\left\{1,\sum_{i\in F}|q_i-r_i|\right\}.$$</div><p>For an event depending only on $F$, its probability difference is therefore at most $\min\{1,\sum_{i\in F}|q_i-r_i|\}$.</p><p><em>Proof.</em> Use independent uniform variables $U_i$, $i\in F$, and set $X_i=\mathbf1_{\{U_i\leq q_i\}}$ and $Y_i=\mathbf1_{\{U_i\leq r_i\}}$. Coordinate $i$ disagrees with probability $|q_i-r_i|$. A union bound gives $\mathbb P(X\neq Y)\leq\min\{1,\sum_i|q_i-r_i|\}$. Since $|f(X)-f(Y)|\leq\operatorname{osc}(f)\mathbf1_{\{X\neq Y\}}$, taking expectations proves the bound. No coordinatewise ordering of $q$ and $r$ is required.</p>

## Ordered profiles {#section-order}

<a id="tag-6B9V" data-assertion="theorem" data-title="Ordered product coupling and comparison of nonnegative observables"></a>
<p>Suppose $I$ is countable and $p_i\leq q_i$ for every $i\in I$. There is a probability law $\gamma$ on $2^I\times2^I$ whose marginals are $\mathbb P_p$ and $\mathbb P_q$ and for which $\omega\subseteq\omega'$ almost surely. Hence every increasing measurable event $A$ and every increasing measurable $H:2^I\to[0,\infty]$ satisfy</p>
<div class="math-display">$$\mathbb P_p(A)\leq\mathbb P_q(A),\qquad \mathbb E_p[H]\leq\mathbb E_q[H].$$</div>
<p>The expectations are extended nonnegative integrals; neither is assumed finite. For a countable vertex set, the same construction couples bond configurations on all unordered pairs, including diagonal coordinates, provided the profiles are ordered on all those pairs.</p>
<p><em>Proof.</em> Independently at each coordinate $i$, choose the pair of bits $(X_i,Y_i)$ with probabilities</p>
<div class="math-display">$$\mathbb P((X_i,Y_i)=(1,1))=p_i,\quad \mathbb P((X_i,Y_i)=(0,1))=q_i-p_i,\quad \mathbb P((X_i,Y_i)=(0,0))=1-q_i.$$</div>
<p>These numbers are nonnegative and sum to one. The remaining pair $(1,0)$ is never chosen. The map from the product of these three-state spaces to the two open-coordinate sets is measurable, since its coordinates are measurable. Its pushforward has the required marginals: each first bit has parameter $p_i$, each second bit has parameter $q_i$, and finite families of either kind remain independent. Cylinder uniqueness identifies both product laws.</p>
<p>Every configuration in the three-state construction satisfies $X_i\leq Y_i$ for all $i$. On the target pair space, the event $\omega\subseteq\omega'$ is measurable because it is the countable intersection of the events excluding an open first bit and a closed second bit. Thus it has $\gamma$-probability one. Increasingness gives $\mathbf1_A(\omega)\leq\mathbf1_A(\omega')$ and $H(\omega)\leq H(\omega')$ on this event. Integrate and use the marginal identities. Monotonicity of the nonnegative integral applies even when an expectation is infinite.</p>
<p>The construction includes $p_i=0$, $q_i=1$, empty coordinate sets and equal profiles. If $p=q$, the middle state has zero probability at each coordinate, so countability gives $\omega=\omega'$ almost surely. At the extreme profiles $p\equiv0$, $q\equiv1$, the pair is the empty and full configuration. No division by $p_i$ or $1-q_i$ occurs.</p>
<p>This comparison concerns ordered profiles. The finite-block perturbation bound above also compares profiles that are not ordered. Neither result asserts continuity for a general infinite-volume event.</p>

## Finite witnesses in infinite volume {#section-witnesses}

<a id="tag-ARYU" data-assertion="proposition" data-title="Finite open witnesses give lower semicontinuous probabilities"></a><p>Suppose $I$ is countable and an event $A$ has a representation</p><div class="math-display">$$A=\bigcup_{F\in\mathcal W}\{\omega:F\subseteq\omega\},$$</div><p>where every $F\in\mathcal W$ is finite. Then $A$ is measurable and $q\mapsto\mathbb P_q(A)$ is lower semicontinuous in the product topology. Thus, whenever $q^{(n)}\to q$ coordinatewise,</p><div class="math-display">$$\mathbb P_q(A)\leq\liminf_{n\to\infty}\mathbb P_{q^{(n)}}(A).$$</div><p>This applies to connection events on any countable graph.</p><p><em>Proof.</em> There are countably many finite subsets of $I$. Enumerate the witness family and let $A_m$ be the union of its first $m$ cylinder events (with the empty-family case immediate). Then $A_m\uparrow A$, each $A_m$ depends on finitely many coordinates, and</p><div class="math-display">$$\mathbb P_q(A)=\sup_m\mathbb P_q(A_m).$$</div><p>Every function in this supremum is continuous by the finite-cylinder result, so their supremum is lower semicontinuous. A connection has a finite open path witness, giving the stated application.</p>

<p>Continuity can fail even for a connection between two fixed vertices. Take the graph with vertices $x,y,v_1,v_2,\ldots$ and edges $\{x,v_n\},\{v_n,y\}$ for every $n$. In profile $q^{(n)}$, give the two edges through $v_n$ probability one and every other edge probability zero. Each fixed edge probability tends to zero, but $\mathbb P_{q^{(n)}}(x\leftrightarrow y)=1$ for all $n$, whereas the all-zero limiting profile gives probability zero. This agrees with lower semicontinuity and rules out an unrestricted continuity claim.</p><p>Nor does this argument apply directly to the event of an infinite cluster: no finite open set certifies that event. Continuity of an infinite-cluster probability, including behavior at criticality, needs additional information.</p>


## Summable changes of the entire profile {#section-total-variation}

<a id="tag-W90W" data-assertion="theorem" data-title="Summable profile perturbations control every measurable event"></a>
<p>Let $I$ be countable and let $q,r\in[0,1]^I$. Set $d_1(q,r)=\sum_{i\in I}|q_i-r_i|\in[0,\infty]$. With total variation normalized as a supremum over measurable events,</p>
<div class="math-display">$$\|\mathbb P_q-\mathbb P_r\|_{\mathrm{TV}}
\equiv\sup_{A\text{ measurable}}|\mathbb P_q(A)-\mathbb P_r(A)|
\leq\min\{1,d_1(q,r)\}.$$</div>
<p>More generally, for every bounded measurable $f:2^I\to\mathbb R$,</p>
<div class="math-display">$$|\mathbb E_q f-\mathbb E_r f|\leq\operatorname{osc}(f)\min\{1,d_1(q,r)\},
\qquad\operatorname{osc}(f)=\sup f-\inf f.$$</div>
<p><em>Proof.</em> Couple the configurations using independent uniform variables $(U_i)_{i\in I}$, putting $X_i=\mathbf1_{\{U_i\leq q_i\}}$ and $Y_i=\mathbf1_{\{U_i\leq r_i\}}$. The two marginal laws are the required product laws, and coordinate $i$ disagrees with probability $|q_i-r_i|$. Since $I$ is countable, the disagreement event is measurable and the union bound gives</p>
<div class="math-display">$$\mathbb P(X\ne Y)\leq\min\left\{1,\sum_i|q_i-r_i|\right\}.$$</div>
<p>Now $|f(X)-f(Y)|\leq\operatorname{osc}(f)\mathbf1_{\{X\ne Y\}}$. Taking expectations proves the observable bound, and applying it to event indicators gives the total-variation bound.</p>
<p>The source obtains its event inequalities from the <a href="/tag/6B9V/">ordered coupling</a>: compare each profile with $s_i=\min\{q_i,r_i\}$ and add the two discrepancy bounds, using $(q_i-s_i)+(r_i-s_i)=|q_i-r_i|$. Its extended inequalities allow $d_1=\infty$; a real absolute-difference bound requires a finite sum. The displayed normalization caps the bound by one, and the bounded-observable form is an additional deduction. Neither monotonicity of $A$ nor coordinatewise comparability of $q$ and $r$ is required.</p>
<p>For bond percolation on countable vertices, this applies to connection and rooted infinite-cluster events. In particular, convergence $d_1(q^{(n)},q)\to0$ gives convergence of every such probability, uniformly over all measurable events. For graph observables, one may first <a href="/tag/LNKT/">erase diagonal coordinates</a>, so only the differences on distinct-vertex pairs need be summed. This refinement is a consequence of diagonal invariance; the source's displayed sum includes all unordered pairs.</p>
<p>The topology matters. Pointwise convergence of profiles controls finite cylinders, but does not imply $d_1$ convergence: in the earlier moving-path example, the sum of differences from the zero profile remains two. Likewise, changing a homogeneous probability by any nonzero amount on infinitely many coordinates gives $d_1=\infty$. The estimate therefore supplies no continuity assertion across a homogeneous critical parameter. For equal profiles the discrepancy is zero; on a single coordinate the total-variation distance is exactly the difference of its opening probabilities. Endpoints zero and one and the empty index set require no exception.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-profile/">30-contract profile inventory</a> distinguishes finite weighted expectations and product-topology continuity from ordered comparison and the stronger summable-perturbation estimate.</p>

## Approaching an intensity from below {#section-left-intensity}

<p>For a countable bond model with finite nonnegative pair intensities, put $q_\beta(e)=1-e^{-\beta J_e}$. The lower-semicontinuity argument above applies to each $\tau_\beta(o,y)$, since $q_\beta$ is coordinatewise continuous. Nonnegative sums preserve lower semicontinuity, so $\beta\mapsto\chi_\beta(o)=\sum_y\tau_\beta(o,y)$ is lower semicontinuous as a function into $[0,\infty]$. It is also nondecreasing. At every finite $b&gt;0$, these two properties give</p>
<div class="math-display">$$\chi_b(o)\leq\liminf_{\beta\uparrow b}\chi_\beta(o)
\leq\limsup_{\beta\uparrow b}\chi_\beta(o)\leq\chi_b(o).$$</div>
<p>Thus the left limit equals $\chi_b(o)$, including when that value is infinite. Equivalently, take an increasing finite edge exhaustion $E_n$. Each truncated susceptibility is continuous, and finite-path approximation gives $\chi_\beta(o)=\sup_n\chi_{E_n,\beta}(o)$. Interchanging the two suprema yields</p>
<div class="math-display">$$\sup_{0\leq\beta&lt;b}\chi_\beta(o)
=\sup_n\sup_{0\leq\beta&lt;b}\chi_{E_n,\beta}(o)
=\sup_n\chi_{E_n,b}(o)=\chi_b(o).$$</div>
<p>No bound on intensity rows or susceptibility is used. In particular, this supplies the left-limit step in <a href="/tag/RDF0/">RDF0</a> once divergence at a finite critical intensity has been established by a separate argument. It gives neither continuity from above nor continuity of the infinite-cluster probability. At $b=0$ there are no smaller nonnegative intensities: the source's formal left-limit statement there is vacuous, rather than a right-continuity assertion.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-susceptibility/">susceptibility-source inventory</a> records the extended-valued limit and the separate finite-row hypotheses needed for boundary-flux convergence.</p>


## Infinite clusters on a locally finite host {#section-host-continuity}

<p>Let $V$ be countable and let $G$ be a fixed locally finite simple graph on $V$. Write $\mathcal P_G$ for the profiles with $q_{xy}=0$ whenever $x\ne y$ and $\{x,y\}$ is not an edge of $G$. Diagonal probabilities are unrestricted. Give $\mathcal P_G$ the subspace topology inherited from the product topology, and put $\theta_x(q)=\mathbb P_q(|K_x|=\infty)$.</p>
<a id="tag-Y5HD" data-assertion="theorem" data-title="The infinite-cluster probability is upper semicontinuous on a fixed locally finite host"></a>
<p>For every $x\in V$, $\theta_x$ is upper semicontinuous on $\mathcal P_G$. In particular, if $q^{(n)}\to q$ coordinatewise and all these profiles belong to $\mathcal P_G$, then</p>
<div class="math-display">$$\limsup_{n\to\infty}\theta_x(q^{(n)})\leq\theta_x(q).$$</div>
<p>Along a nondecreasing, coordinatewise continuous family $t\mapsto q_t\in\mathcal P_G$ on a real interval, $t\mapsto\theta_x(q_t)$ is right-continuous within that interval.</p>
<p><em>Proof.</em> Choose an increasing finite exhaustion $F_n$ of $V$ containing $x$, and let $E_n$ be the event that $x$ is connected to a vertex outside $F_n$. These events decrease to $\{|K_x|=\infty\}$, so</p>
<div class="math-display">$$\theta_x(q)=\inf_n\mathbb P_q(E_n).$$</div>
<p>Let $B_n$ be the set of host edges with at least one endpoint in $F_n$. It is finite by local finiteness. For $q\in\mathcal P_G$, every open non-diagonal pair lies in $G$ simultaneously almost surely: there are countably many off-host pairs, each with opening probability zero. On this event, a path escaping $F_n$ can be stopped at its first exit; every edge of the stopped path lies in $B_n$. Thus escape is determined by the configuration restricted to $B_n$. Its probability on $\mathcal P_G$ agrees with a finite-cylinder probability, which is continuous by <a href="/tag/RA0Z/">RA0Z</a>. The infimum of these continuous functions is upper semicontinuous.</p>
<p>The rooted infinite-cluster event is increasing, so <a href="/tag/6B9V/">ordered coupling</a> makes $\theta_x(q_t)$ nondecreasing. Approaching $t$ from above, monotonicity bounds the lower limit by $\theta_x(q_t)$, while upper semicontinuity bounds the upper limit by the same value. This proves right continuity.</p>
<p>No uniform degree bound is needed. The same fixed locally finite host must support the whole family; local finiteness of each realized open graph is a different condition. Without the support restriction the conclusion fails even for translation-invariant profiles on $\mathbb Z$: give a pair probability one when its endpoints are at distance at least $n$ and zero otherwise. These profiles converge pointwise to zero, but at every $n$ each vertex has infinitely many open neighbours, so $\theta_0=1$ throughout and equals zero at the limit.</p>
<p>The opposite one-sided statement holds for $\tau_q(x,y)$ without a locally finite host. Its <a href="/tag/ARYU/">lower semicontinuity</a> and monotonicity give left continuity along every nondecreasing coordinatewise continuous family. The source expresses both one-sided conclusions as continuity within the lower or upper order interval on an arbitrary topological preordered parameter space. The same proof applies: the order restriction supplies one bound and semicontinuity supplies the other. On a real interval this is the usual one-sided assertion, with a missing side at an endpoint vacuous.</p>
<p>The source also obtains monotonicity of extended susceptibility and of global infinite-cluster existence directly from ordered coupling. Those observables are increasing and measurable; neither susceptibility finiteness nor spatial invariance is required. The <a href="/coverage/sources/perclib-22d8485-profile-energy/">source inventory</a> separates these order statements from the finite-cylinder and host-continuity arguments. None proves left continuity of $\theta$, absence of an infinite cluster at criticality, or full continuity of an arbitrary infinite-volume event.</p>



## Summable intensities on an infinite-degree host {#section-summable-theta}

<a id="tag-0OQL" data-assertion="theorem" data-title="Summable intensity rows give right continuity of the percolation probability"></a>
<p>Let $V$ be countable, fix $o\in V$, and let $J_{xy}=J_{yx}\geq0$ be finite for distinct vertices, with $\sum_{y\ne x}J_{xy}&lt;\infty$ for every $x$. Open pairs independently with probabilities $1-e^{-\beta J_{xy}}$, for $0\leq\beta&lt;\infty$. Then $\theta_o(\beta)=\mathbb P_\beta(|K_o|=\infty)$ is upper semicontinuous and right-continuous. At every $b$ with $\theta_o(b)=0$, the law of the entire rooted vertex cluster is continuous in total variation as $\beta\to b$ within $[0,\infty)$.</p>
<p><em>Proof.</em> For finite $S\ni o$, put</p>
<div class="math-display">$$B(S)=\sum_{x\in S}\sum_{y\notin S}J_{xy},\qquad
h_S(\beta)=\mathbb P_\beta(\text{the open graph induced on }S\text{ is connected}).$$</div>
<p>The boundary sum is finite. The internal event uses finitely many edges, so $h_S$ is a finite polynomial in their opening and closing probabilities, and is continuous. Independence gives the exact identity</p>
<div class="math-display">$$a_S(\beta):=\mathbb P_\beta(K_o=S)=e^{-\beta B(S)}h_S(\beta).$$</div>
<p>Indeed, the internal graph must be connected and all boundary bonds closed. The latter probability is obtained by decreasing finite-edge intersections and equals the exponential of the boundary sum. Thus $a_S$ is continuous, including at zero. There are only countably many finite sets containing $o$, and</p>
<div class="math-display">$$1-\theta_o(\beta)=\sum_{\substack{S\ni o\text{ finite}}}a_S(\beta).$$</div>
<p>A sum of nonnegative continuous functions is lower semicontinuous. Its complement is upper semicontinuous. Ordered coupling makes $\theta_o$ nondecreasing, so for $\beta\downarrow b$ its upper and lower limits both equal $\theta_o(b)$.</p>
<p>If $\theta_o(b)=0$, choose finitely many sets $S_1,\ldots,S_m$ whose cluster probabilities at $b$ sum to at least $1-\varepsilon$. For every measurable event $D$ of the vertex cluster, separate these atoms from their complement. Uniformly in $D$,</p>
<div class="math-display">$$\bigl|\mathbb P_\beta(K_o\in D)-\mathbb P_b(K_o\in D)\bigr|
\leq\sum_{i=1}^m|a_{S_i}(\beta)-a_{S_i}(b)|
+\mathbb P_\beta(K_o\notin\{S_1,\ldots,S_m\})
+\mathbb P_b(K_o\notin\{S_1,\ldots,S_m\}).$$</div>
<p>The upper limit is at most $2\varepsilon$, proving total-variation convergence. The cluster is viewed as a random subset of $V$ with its product sigma algebra; each finite cluster is a measurable atom.</p>
<p>Local finiteness of the host and a uniform row bound are unnecessary here. Summability at each vertex supplies continuity of every finite-cluster probability. This is different from coordinatewise convergence of arbitrary profiles, which need not control boundary products. Total-variation continuity at a nonpercolating parameter controls bounded cluster observables; it does not bound susceptibility or any other unbounded moment.</p>
