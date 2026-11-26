---
{
  "id": "product-symmetries",
  "title": "Relabelling product percolation",
  "subtitle": "Coordinate transformations, vertex maps and component laws",
  "kind": "method",
  "category": "Foundations",
  "summary": "Coordinate maps and deterministic changes transport a Bernoulli product law by changing its profile. Independent intersections multiply opening probabilities, while independent unions multiply their complements. Vertex injections compare cluster observables, while bijections and closed components give exact identities.",
  "context": [
    "Arbitrary coordinate sets $I,K$ and a bijection $e:I\\to K$.",
    "Product sigma-algebras and profiles $q:I\\to[0,1]$.",
    "For bond applications, vertex relabelling induces relabelling of unordered pairs.",
    "Vertex-bijection transport allows arbitrary vertex sets; embedding comparisons assume a countable source, and disjoint-union probabilities assume countable parts."
  ],
  "related": [
    "product-model",
    "connectivity",
    "susceptibility",
    "finite-random-graphs"
  ],
  "sourceIds": ["mathlib", "perclib-diagonal", "perclib-reindexing", "perclib-host-support", "perclib-product-characterization", "perclib-superposition", "perclib-deterministic-modification", "perclib-injective-pullback", "perclib-bond-transport", "perclib-bond-embedding", "perclib-disjoint-union", "perclib-symmetry-associations", "perclib-product-associations"],
  "aliases": [
    "reindexing",
    "permutation",
    "symmetry",
    "invariant law",
    "relabelling",
    "all-open characterization",
    "injective pullback",
    "independent thinning",
    "superposition",
    "deterministic deletion",
    "vertex embedding",
    "transport of clusters",
    "disjoint union",
    "closed vertex part"
  ],
  "prototypeUses": []
}
---

## Transporting the law {#section-transport}

<p>Identify a configuration with its set of open coordinates. A bijection $e:I\to K$ induces $R_e(\omega)=e[\omega]$. The value at $k$ after relabelling is the old value at $e^{-1}(k)$, so the transported profile must be $q\circ e^{-1}$.</p>

<a id="tag-6RZ8" data-assertion="proposition" data-title="Product-law transport under coordinate bijections"></a><p>The map $R_e$ is a measurable bijection with measurable inverse, and</p><div class="math-display">$$(R_e)_*\mathbb P_q=\mathbb P_{q\circ e^{-1}}.$$</div><p>Equivalently, for every measurable event $A$ on $K$,</p><div class="math-display">$$\mathbb P_q(R_e^{-1}(A))=\mathbb P_{q\circ e^{-1}}(A).$$</div><p><em>Proof.</em> The inverse image under $R_e$ of the event that $k$ is open is the event that $e^{-1}(k)$ is open. Coordinate events generate the product sigma-algebra, so $R_e$ is measurable; applying the same argument to $e^{-1}$ gives its measurable inverse. A finite cylinder on $K$ pulls back to the corresponding cylinder on distinct coordinates of $I$. Its probability is the product of the Bernoulli weights with parameters $q(e^{-1}(k))$. Thus the pushforward and the stated product law agree on the cylinder pi-system. Uniqueness of probability measures on its generated sigma-algebra proves the identity.</p><p>No countability assumption is needed. Parameters zero and one cause no exception, since the cylinder argument uses no division.</p>

## When relabelling is a symmetry {#section-invariance}

<a id="tag-VEUZ" data-assertion="corollary" data-title="Profile-preserving permutations preserve the product law"></a><p>If $e:I\to I$ is a bijection satisfying $q(e(i))=q(i)$ for every $i$, then $(R_e)_*\mathbb P_q=\mathbb P_q$. Hence $\mathbb P_q(R_e^{-1}(A))=\mathbb P_q(A)$ for every measurable event $A$.</p><p><em>Proof.</em> Apply the profile equality at $e^{-1}(i)$ to obtain $q(e^{-1}(i))=q(i)$, and use the transport identity.</p><p>A homogeneous profile is preserved by every permutation of its coordinates. For an inhomogeneous profile, a permutation generally changes the law. In particular, if two coordinates have different opening probabilities, exchanging them exchanges those marginal probabilities. The combinatorial symmetry of an index set alone is not a symmetry of its probability law.</p>

## Unordered pairs and diagonal coordinates {#section-bonds}

<a id="tag-6VY0" data-assertion="corollary" data-title="Transport of a bond profile by vertex relabelling"></a><p>Let $f:V\to W$ be a bijection and let $f_2$ be its induced bijection of unordered pairs, including repeated pairs: $f_2(\{x,y\})=\{f(x),f(y)\}$. If bonds have profile $q$, relabelling their open set by $f_2$ gives product profile</p><div class="math-display">$$q'(\{u,v\})=q(\{f^{-1}(u),f^{-1}(v)\}).$$</div><p>This is the coordinate-transport proposition applied to $f_2$.</p><p>The simple open graph discards repeated pairs $\{x,x\}$, but the underlying product configuration retains those coordinates. To claim invariance of the <em>entire product law</em> under a vertex permutation, profile preservation is required on all coordinates, including repeated pairs. Arbitrary diagonal values are allowed; they need not be zero. Statements about only the simple open graph may ignore the diagonal, but that is a distinct claim.</p><p>For example, on two vertices with unequal diagonal opening probabilities, swapping the vertices changes the full product law. Its only non-loop edge is fixed by the swap, so the simple open graph nevertheless has the same law. This separates invariance of graph observables from invariance of all coordinate events.</p>

## Erasing loops {#section-erasure}

<a id="tag-LNKT" data-assertion="theorem" data-title="Loop erasure transports the product law and preserves insensitive observables"></a>
<p>Let $V$ be any vertex set, let $D=\{\{v,v\}:v\in V\}$ be the diagonal coordinates, and put $E(\omega)=\omega\setminus D$. For a profile $p$ on unordered pairs, define $p^\circ(e)=0$ on $D$ and $p^\circ(e)=p(e)$ elsewhere. Then $E$ is measurable and</p>
<div class="math-display">$$E_*\mathbb P_p=\mathbb P_{p^\circ}.$$</div>
<p>If profiles $p,q$ agree off $D$, and $F$ is a measurable map to any measurable space satisfying $F(E(\omega))=F(\omega)$ for every configuration, then</p>
<div class="math-display">$$F_*\mathbb P_p=F_*\mathbb P_q.$$</div>
<p>In particular, every measurable event unchanged by loop erasure has the same probability under these two profiles. Countability of $V$ is not required.</p>
<p><em>Proof.</em> Each output coordinate of $E$ is either constantly closed or equal to its input coordinate. This proves measurability, and the probabilities of finite output cylinders are exactly those of the product profile $p^\circ$. Cylinder uniqueness gives the first identity. Since $p^\circ=q^\circ$, composition of pushforwards gives</p>
<div class="math-display">$$F_*\mathbb P_p=(F\circ E)_*\mathbb P_p=F_*\mathbb P_{p^\circ}=F_*\mathbb P_{q^\circ}=(F\circ E)_*\mathbb P_q=F_*\mathbb P_q.$$</div>
<p>Apply this to an event's indicator for the last claim. The argument includes diagonal probabilities zero and one; it does not condition on a possibly null event that all loops are closed.</p>

<a id="tag-EYCQ" data-assertion="corollary" data-title="Diagonal parameters do not affect connection probabilities or cluster-volume laws"></a>
<p>Suppose $V$ is countable and $p,q$ agree on every pair of distinct vertices. Let $K_x$ be the cluster of $x$ in the simple open graph, with the length-zero path allowed. Then for all $x,y\in V$,</p>
<div class="math-display">$$\mathbb P_p(x\leftrightarrow y)=\mathbb P_q(x\leftrightarrow y),\qquad \mathcal L_p(|K_x|)=\mathcal L_q(|K_x|),\qquad \chi_p(x)=\chi_q(x).$$</div>
<p>The volume law takes values in $\mathbb N\cup\{\infty\}$, and susceptibility is an extended nonnegative expectation. Thus all cluster-volume tail probabilities and all nonnegative moments agree, whether finite or infinite.</p>
<p><em>Proof.</em> Deleting repeated pairs leaves the simple open graph unchanged, hence leaves connectivity and each root cluster unchanged. On a countable vertex set, connectivity is a countable union of finite-path cylinder events. Also $|K_x|=\sum_{y\in V}\mathbf1_{\{x\leftrightarrow y\}}$ is measurable as a monotone limit of finite sums. Apply the preceding theorem to these observables, and integrate any nonnegative function of the volume against the common law. No finiteness assumption on susceptibility enters.</p>
<p>These conclusions concern graph observables. The event that a specified loop is open still has probability equal to that loop's parameter, and can distinguish $\mathbb P_p$ from $\mathbb P_q$.</p>

<p>On two vertices, replacing both loop parameters by zero or by one leaves the susceptibility unchanged for every off-diagonal probability. The equality also reaches genuinely infinite values: on a countably infinite vertex set with every off-diagonal probability one, every such pair is open simultaneously almost surely, so the graph is complete and each susceptibility is infinite. Choosing zero instead of one on the diagonal changes none of this.</p>

## Host support and diagonal coordinates {#section-host}

<a id="tag-H48I" data-assertion="proposition" data-title="Host containment for configurations and for their simple graphs"></a>
<p>Let $V$ be countable, let $G$ be a simple graph on $V$, and let $\mathbb P_q$ be the product law on all unordered pairs, including diagonal pairs. Then</p>
<div class="math-display">$$\mathbb P_q(\omega\subseteq E(G))=1\quad\Longleftrightarrow\quad q(e)=0\text{ for every }e\notin E(G).$$</div>
<p>In contrast, writing $G_\omega$ for the simple open graph,</p>
<div class="math-display">$$\mathbb P_q(G_\omega\subseteq G)=1\quad\Longleftrightarrow\quad q(\{x,y\})=0\text{ whenever }x\ne y\text{ and }\{x,y\}\notin E(G).$$</div>
<p>The first condition forces every diagonal probability to be zero, since a simple host has no loops. The second places no restriction on diagonal probabilities. No degree bound on $G$ is assumed.</p>
<p><em>Proof.</em> An outside coordinate $e$ is open with probability $q(e)$. If all these probabilities vanish, the union of the outside-open events is a countable union of null events, since the unordered-pair set of a countable vertex set is countable. Its complement is exactly configuration containment. Conversely, any outside-open event is contained in the failure of configuration containment, so almost-sure containment forces its marginal to be zero.</p>
<p>For graph containment the same argument uses only non-diagonal pairs outside the host. An open such pair is an edge of the simple open graph and violates containment, while diagonal coordinates never contribute an edge. These countable unions also establish measurability of both containment events.</p>
<p>For example, on a nonempty countable vertex set, give every diagonal probability one and every other probability zero. The simple open graph is empty almost surely and lies in every host, but the configuration does not lie in the edge set of any simple host. On the other hand, arbitrary probabilities on host edges, including one, are allowed in both criteria once the required outside probabilities vanish.</p>
<p>The library's host interface assumes the stronger all-pair support condition and obtains both containments together. The graph-only criterion and the converse directions above make the distinction explicit; they are additional expository consequences of the coordinate marginals.</p>

## Identifying a product law {#section-characterization}

<p>For a finite coordinate set $F\subseteq I$, put $U_F=\{\omega:F\subseteq\omega\}$. These are measurable cylinder events. They form a pi-system because $U_F\cap U_G=U_{F\cup G}$, and they generate the product sigma-algebra because the singleton events $U_{\{i\}}$ generate it.</p>

<a id="tag-NGWR" data-assertion="theorem" data-title="Finite all-open probabilities determine the product law"></a>
<p>Let $\mu$ be a probability measure on the configuration space $\{0,1\}^I$. If</p>
<div class="math-display">$$\mu(U_F)=\prod_{i\in F}q_i\qquad\text{for every finite }F\subseteq I,$$</div>
<p>then $\mu=\mathbb P_q$. More generally, two probability measures agreeing on every $U_F$ agree everywhere on the product sigma-algebra. Thus a measurable map $T:\{0,1\}^I\to\{0,1\}^J$ satisfies $T_*\mathbb P_q=\mathbb P_r$ if and only if</p>
<div class="math-display">$$\mathbb P_q\bigl(T^{-1}U_F\bigr)=\prod_{j\in F}r_j\qquad\text{for every finite }F\subseteq J.$$</div>
<p><em>Proof.</em> The pi-system contains the whole space, obtained from $F=\varnothing$. Uniqueness of finite measures on a generating pi-system proves the first two assertions. For the last, $T_*\mathbb P_q$ is a probability measure and its value on $U_F$ is the probability of the indicated inverse image. Apply the first assertion; the reverse implication follows from the same pushforward identity.</p>
<p>The test includes every finite $F$, not just singletons. For example, on two coordinates, the law giving probability one half each to the all-open and all-closed configurations has both marginals equal to one half, but the all-open probability is one half rather than one quarter. It is not their product law. There is no countability restriction on $I$ or $J$, and deterministic probabilities zero or one cause no exception. On the empty coordinate set the configuration space has one point and the empty-set test records total mass one.</p>

## Sampling distinct coordinates {#section-pullback}

<a id="tag-YMHY" data-assertion="theorem" data-title="Injective coordinate sampling preserves the product structure"></a>
<p>Let $g:J\to I$ be injective. The pullback $R_g(\omega)=g^{-1}\omega$ is measurable and</p>
<div class="math-display">$$(R_g)_*\mathbb P_q=\mathbb P_{q\circ g}.$$</div>
<p>Consequently $\mathbb P_q(R_g^{-1}A)=\mathbb P_{q\circ g}(A)$ for every measurable event $A$ on $J$. Surjectivity is not required. More generally, if independent coordinates $X_i$ take values in a common measurable space $X$ with probability laws $\mu_i$, then $(X_{g(j)})_{j\in J}$ has product law $\bigotimes_{j\in J}\mu_{g(j)}$.</p>
<p><em>Proof.</em> Each output coordinate reads one input coordinate, giving measurability. The inverse image of the all-open event for a finite $F\subseteq J$ is the all-open event for $g(F)$. Injectivity makes those input coordinates distinct, so its probability is</p>
<div class="math-display">$$\prod_{i\in g(F)}q_i=\prod_{j\in F}q_{g(j)}.$$</div>
<p>The characterization just proved identifies the law. In the general measurable-space version, use finite cylinders of the form $X_{g(j)}\in A_j$ with measurable $A_j$. Distinct input coordinates give probability $\prod_{j\in F}\mu_{g(j)}(A_j)$, and cylinder uniqueness again identifies the product law.</p>
<p>Taking $g$ to be the inclusion $S\hookrightarrow I$ gives restriction to any deterministic subset $S$, finite or infinite. This produces a configuration <em>on $S$</em>, with the restricted profile. For the map $n\mapsto2n$ on the natural numbers, it gives the law of the even coordinates. Taking $g$ to be the inverse of a bijection recovers <a href="/tag/6RZ8/">the earlier relabelling formula</a>.</p>
<p>Injectivity cannot be discarded. If two output coordinates both read one input bit of probability $p\in(0,1)$, their joint open probability is $p$, whereas the product of their marginals is $p^2$. Each marginal is correct, but the outputs are dependent.</p>

## Deterministic opening and closing {#section-modification}

<p>Fix any deterministic $E\subseteq I$. Define $M_E(\omega)=\omega\cap E$, $O_E(\omega)=\omega\cup E$, and $D_E(\omega)=\omega\setminus E$. These maps all take values in configurations on the original coordinate set $I$.</p>

<a id="tag-6J1Y" data-assertion="theorem" data-title="Deterministic modifications replace exactly the specified marginals"></a>
<p>The three maps are measurable and have product pushforward laws with profiles</p>
<div class="math-display">$$\begin{aligned}
q_i^{M_E}&=\begin{cases}q_i&i\in E,\\0&i\notin E,\end{cases}&
q_i^{O_E}&=\begin{cases}1&i\in E,\\q_i&i\notin E,\end{cases}&
q_i^{D_E}&=\begin{cases}0&i\in E,\\q_i&i\notin E.\end{cases}
\end{aligned}$$</div>
<p>For every measurable increasing event $A$,</p>
<div class="math-display">$$\mathbb P_{q^{M_E}}(A)\leq\mathbb P_q(A)\leq\mathbb P_{q^{O_E}}(A),\qquad \mathbb P_{q^{D_E}}(A)\leq\mathbb P_q(A).$$</div>
<p>No finiteness or countability assumption on either $I$ or $E$ is required.</p>
<p><em>Proof.</em> Every output bit is either its original bit or a fixed constant. Hence the maps are measurable. A finite output all-open event is impossible if one of its coordinates is fixed closed; otherwise it requires precisely the original bits among those output coordinates to be open. Independence gives the product of the displayed marginals. Apply the characterization. The event inequalities follow from</p>
<div class="math-display">$$D_E(\omega)\subseteq\omega,\qquad M_E(\omega)\subseteq\omega\subseteq O_E(\omega).$$</div>
<p>These inclusions also give the inverse-image inequalities for the product outer measure of any increasing set, even before measurability is known. The displayed comparison of probabilities under the modified profiles uses measurability to apply the pushforward formula.</p>
<p>Closing outside $E$ and restricting to $E$ carry the same retained bits, but their target spaces differ: the first fixes the other coordinates to zero in $I$, whereas the second removes them from the coordinate space. The empty and full choices of $E$ give the identity map or a constant configuration as appropriate. This is modification, not conditioning on an event that the specified coordinates already have their imposed values.</p>
<p>For bond configurations on any vertex set, take $E$ to be the edge set of a deterministic simple host $G$. The masked law sets all non-host coordinates, including loops, to zero. On countable vertices the connection event is measurable and increasing, so</p>
<div class="math-display">$$\tau_{q^{M_E}}(x,y)\leq\tau_q(x,y).$$</div>
<p>Diagonal erasure itself leaves the graph observables unchanged, as proved earlier. Host masking can additionally delete genuine bonds and need not preserve connection probabilities.</p>
<p>The modifying set must be fixed for this formula. On two independent fair coordinates, choosing $E(\omega)=I$ when coordinate 1 is open and $E(\omega)=\varnothing$ otherwise makes the retained indicators $X_1$ and $X_1X_2$. Their joint mean is $1/4$, while the product of their means is $1/8$. A configuration-dependent choice can therefore destroy the product structure.</p>

## Independent thinning and superposition {#section-superposition}

<a id="tag-KDNA" data-assertion="theorem" data-title="Independent intersections multiply open probabilities and unions multiply closed probabilities"></a>
<p>Let $\omega,\eta$ be independent configurations with product laws $\mathbb P_p,\mathbb P_r$ on the same arbitrary coordinate set $I$. Then</p>
<div class="math-display">$$\omega\cap\eta\ \sim\ \mathbb P_{pr},\qquad
\omega\cup\eta\ \sim\ \mathbb P_{1-(1-p)(1-r)},$$</div>
<p>with products taken coordinatewise. These identities include probabilities zero and one and the empty coordinate set.</p>
<p><em>Proof.</em> For a finite $F\subseteq I$, the event $F\subseteq\omega\cap\eta$ is the intersection of $F\subseteq\omega$ and $F\subseteq\eta$, events on the two independent layers. Thus</p>
<div class="math-display">$$\mathbb P(F\subseteq\omega\cap\eta)=\left(\prod_{i\in F}p_i\right)\left(\prod_{i\in F}r_i\right)=\prod_{i\in F}p_i r_i.$$</div>
<p>The intersection map is measurable, and the all-open characterization gives its law. For the union, use $I\setminus(\omega\cup\eta)=(I\setminus\omega)\cap(I\setminus\eta)$. The two complements remain independent and have profiles $1-p,1-r$ by <a href="/tag/CW1V/">complement duality</a>. Apply the intersection law and complement once more.</p>
<p>Induction gives, for a finite independent family with profiles $p^{(1)},\ldots,p^{(m)}$, intersection profile $\prod_{k=1}^m p^{(k)}$ and union profile $1-\prod_{k=1}^m(1-p^{(k)})$. For no layers, the intersection is the full configuration and the union is empty. Exponential closed probabilities turn the union identity into <a href="/tag/TWLQ/">additivity of intensity</a>.</p>
<p>Independence of the layers is essential. Taking $\eta=\omega$ with a nondegenerate homogeneous profile leaves both the intersection and the union equal to $\omega$; neither has the profile predicted by the independent formulas. Independent random thinning is permitted here because the entire joint input law is specified, unlike an adaptive choice of retained coordinates.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-product-transforms/">source-contract inventory</a> records the 23 named theorems behind these arguments. The complement identity reuses its existing assertion. The finite-family extension and the examples are expository deductions; no compiled association or reviewed correspondence is supplied by these law calculations.</p>

## Transporting clusters and their observables {#section-cluster-transport}

<p>Write $\theta_q(x)=\mathbb P_q(|K_x|=\infty)$ for the rooted infinite-cluster probability. Let $\sigma:V\to W$ be a bijection and let $T_\sigma$ be its induced map on bond configurations. Thus $\{\sigma x,\sigma y\}$ belongs to $T_\sigma\omega$ exactly when $\{x,y\}$ belongs to $\omega$, including repeated pairs.</p>

<a id="tag-ZE95" data-assertion="theorem" data-title="Vertex bijections transport connections, clusters and their laws exactly"></a>
<p>For every configuration,</p>
<div class="math-display">$$x\leftrightarrow y\text{ in }\omega\quad\Longleftrightarrow\quad\sigma x\leftrightarrow\sigma y\text{ in }T_\sigma\omega,\qquad
K_{\sigma x}(T_\sigma\omega)=\sigma(K_x(\omega)).$$</div>
<p>Cluster volumes and infinitude are preserved. For any $F\subseteq V$, the cluster of $x$ leaves $F$ exactly when the transported cluster leaves $\sigma(F)$. If $(T_\sigma)_*\mathbb P_q=\mathbb P_{q'}$, then</p>
<div class="math-display">$$\tau_{q'}(\sigma x,\sigma y)=\tau_q(x,y),\qquad
\theta_{q'}(\sigma x)=\theta_q(x),\qquad
\chi_{q'}(\sigma x)=\chi_q(x).$$</div>
<p>On countable vertex sets these have their usual probability and extended-expectation meanings. On arbitrary vertex sets, the same identities hold with product outer measure for possibly nonmeasurable events and the nonnegative lower integral for susceptibility. They do not assert measurability of those graph observables.</p>
<p><em>Proof.</em> Distinct vertices remain distinct under $\sigma$, so the coordinate identity gives an isomorphism of the simple open graphs. Map a finite path by $\sigma$ and use $\sigma^{-1}$ for the converse. This proves the connection and cluster identities; the bijection preserves finite cardinalities and infinite sets. It also sends $V\setminus F$ onto $W\setminus\sigma(F)$, proving the escape identity. The identity bijection changes no configuration, and applying $\sigma^{-1}$ after $\sigma$ recovers it.</p>
<p>The coordinate maps make $T_\sigma$ a measurable bijection with measurable inverse, as in <a href="/tag/6VY0/">bond-profile transport</a>. Such a map carries measurable supersets of an arbitrary set bijectively to measurable supersets of its image. Taking the infimum of their measures gives</p>
<div class="math-display">$$((T_\sigma)_*\mu)(A)=\mu(T_\sigma^{-1}A)$$</div>
<p>even when $A$ is not measurable, with both sides interpreted as outer measures. Likewise, composition with $T_\sigma$ and its inverse gives a bijection between the measurable nonnegative simple functions below $f$ and those below $f\circ T_\sigma$. Taking their integral suprema gives the lower-integral identity</p>
<div class="math-display">$$\int^- f\,d((T_\sigma)_*\mu)=\int^- f(T_\sigma\omega)\,d\mu(\omega)$$</div>
<p>for every nonnegative extended-valued $f$. Apply these identities to the connection and infinitude events and to cluster volume, using the deterministic equalities already proved.</p>
<p>The transported-profile formula supplies the law hypothesis. In particular, a law-preserving vertex permutation preserves these observables; a transitive group of such permutations makes root susceptibility and root percolation probability independent of the root. This is equality of values under an actual symmetry, stronger than the <a href="/tag/C3OO/">positive-path comparison</a> available without symmetry.</p>

## Comparison under an injective vertex map {#section-vertex-embedding}

<p>For an injection $f:V\to W$, write $f_2\{x,y\}=\{f(x),f(y)\}$. Pulling back a configuration gives $P_f(\omega)=f_2^{-1}\omega$. Each output coordinate reads one input coordinate, so this map is measurable; injectivity and <a href="/tag/YMHY/">coordinate sampling</a> give</p>
<div class="math-display">$$(P_f)_*\mathbb P_{q'}=\mathbb P_r,\qquad r(e)=q'(f_2(e)).$$</div>
<p>These assertions require no countability. Every connection in the pullback maps to a connection in the full graph, and</p>
<div class="math-display">$$f(K_x(P_f\omega))\subseteq K_{f(x)}(\omega).$$</div>

<a id="tag-1H8U" data-assertion="theorem" data-title="Off-diagonal profile domination under an injection compares cluster observables"></a>
<p>Suppose $V$ is countable, $W$ is arbitrary, and</p>
<div class="math-display">$$q(\{x,y\})\leq q'(\{f(x),f(y)\})\qquad(x\ne y).$$</div>
<p>Then</p>
<div class="math-display">$$\tau_q(x,y)\leq\tau_{q'}(f(x),f(y)),\qquad
\theta_q(x)\leq\theta_{q'}(f(x)),\qquad
\chi_q(x)\leq\chi_{q'}(f(x)).$$</div>
<p>If $W$ is not countable, the target quantities retain the outer-measure and lower-integral conventions just described. No comparison of diagonal probabilities, summability or finiteness of susceptibility is assumed.</p>
<p><em>Proof.</em> Replace $q$ on the diagonal by zero, obtaining $q^\circ$. This leaves all its graph observables unchanged by <a href="/tag/EYCQ/">diagonal insensitivity</a>, and now $q^\circ\leq r$ on every coordinate. Monotone coupling on $V$ therefore increases connection events, root infinitude and cluster volume when the profile changes from $q^\circ$ to $r$.</p>
<p>Under the pullback law, a path from $x$ to $y$ maps to a path from $f(x)$ to $f(y)$. Its image cluster is a subset of the latter root cluster; because $f$ is injective, this inclusion preserves the lower bound on volume and carries an infinite cluster to an infinite cluster. Taking measures gives the two event inequalities, and integrating the volume inequality gives the susceptibility inequality. Countability of $V$ supplies measurability of the source events and volume, so the pullback change of measure is justified. The final comparisons use only monotonicity of outer measure and of the lower integral on the target side.</p>
<p>Equality of the profiles on pairs in the image does not force equality of full-cluster observables. The larger graph may connect two image vertices through a path leaving the image, as in the <a href="/tag/U32Y/">finite-domain example</a>. An inclusion of a finite box into the lattice is a typical application of the inequality. An arbitrary vertex identification is different: without injectivity, distinct bond coordinates can be identified and cluster cardinalities need not be preserved.</p>

## A part with no open boundary {#section-closed-part}

<a id="tag-7CR8" data-assertion="proposition" data-title="A closed vertex part has exactly the clusters of its induced restriction"></a>
<p>Let $f:V\to W$ be injective, with image $S$, and fix a configuration $\omega$ on $W$. If no open pair joins $S$ to $W\setminus S$, then</p>
<div class="math-display">$$K_{f(x)}(\omega)=f(K_x(P_f\omega))\qquad(x\in V).$$</div>
<p>No probability or countability assumption is needed.</p>
<p><em>Proof.</em> The image of a pullback path is always a path in the full graph, giving one inclusion. A full path starting in $S$ cannot leave it: its first exit would cross an open pair from $S$ to its complement. Each vertex of the path therefore has a unique preimage under $f$, and the path pulls back to one in $P_f\omega$. This gives the reverse inclusion.</p>
<p>The hypothesis concerns the actual configuration. Probability-zero cross edges imply their simultaneous absence only after a suitable measurability and countability argument; that step is separate in the product-law application below.</p>

## Independent laws on a disjoint union {#section-disjoint-union}

<p>Let $W=V_1\sqcup V_2$, with inclusions $\iota_1,\iota_2$, and restrict a product configuration by $\omega_j=P_{\iota_j}\omega$. The two restrictions have the product profiles $q_j(e)=q((\iota_j)_2(e))$. Their determining sets of pair coordinates are disjoint, even when cross pairs may be open. Thus <a href="/tag/RDX7/">independence of internal observations</a> gives, for measurable events $A_j$ of the restricted configurations,</p>
<div class="math-display">$$\mathbb P_q(\omega_1\in A_1,\omega_2\in A_2)=\mathbb P_{q_1}(A_1)\mathbb P_{q_2}(A_2).$$</div>
<p>This restriction identity holds for arbitrary $V_1,V_2$ and does not require the absence of cross edges.</p>

<a id="tag-WD2J" data-assertion="theorem" data-title="Zero cross probabilities identify full percolation observables with their disjoint components"></a>
<p>Suppose now that $V_1,V_2$ are countable and every cross pair has probability zero. Almost surely, each full cluster lies in one side and</p>
<div class="math-display">$$K_{\iota_j(x)}(\omega)=\iota_j(K_x(\omega_j)),\qquad j=1,2.$$</div>
<p>Consequently, for each side,</p>
<div class="math-display">$$\tau_q(\iota_j(x),\iota_j(y))=\tau_{q_j}(x,y),\qquad
\theta_q(\iota_j(x))=\theta_{q_j}(x),\qquad
\chi_q(\iota_j(x))=\chi_{q_j}(x),$$</div>
<p>while $\tau_q(\iota_1(x),\iota_2(y))=0$. If $\Theta_j$ is the probability that some cluster in side $j$ is infinite, then the global probability is</p>
<div class="math-display">$$\Theta=1-(1-\Theta_1)(1-\Theta_2).$$</div>
<p><em>Proof.</em> There are countably many cross pairs, and each is open on a null event. Their union is null. Outside it, both sides have no open boundary, so the preceding deterministic proposition gives the cluster identities. The restriction laws then give the within-side probabilities and susceptibilities, including infinite expectations. No path can join the sides, giving the cross two-point value zero.</p>
<p>The event that no full cluster is infinite is, almost surely, the intersection of the corresponding events for the two restrictions. These events are measurable because their vertex sets are countable. They are independent by the restriction identity, so their intersection has probability $(1-\Theta_1)(1-\Theta_2)$. Take its complement.</p>
<p>The empty-side case has $\Theta_j=0$ and causes no exception; a singleton side has cluster volume one regardless of its loop probability. No diagonal restriction is imposed. The formulas for either side follow from the same argument, although the source exports the susceptibility and within-side two-point identities only for the first inclusion. Independence of restrictions alone would not identify them with full clusters when cross edges are present.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-bond-transport/">46-contract inventory</a> distinguishes arbitrary-vertex transport, the countable-source embedding comparison and the countable disjoint-union formulas. Coordinate pullback and internal independence reuse their earlier assertions. All new source correspondences remain pending independent review and compiled association.</p>

## Scope of the tagged diagonal statements {#section-diagonal-associations}

<p>The source statement for <a href="/tag/LNKT/">LNKT</a> includes erasure, its pushforward law, equality in law of every measurable erasure-insensitive observable, and equality of probabilities for every measurable erasure-insensitive event. It allows an arbitrary vertex set and an arbitrary measurable target space. This last generality concerns the target sigma-algebra, without any standard Borel assumption.</p>
<p>The <a href="/tag/EYCQ/">EYCQ</a> specialization uses countable vertices to obtain measurable connection events and extended cluster volume. Its equality of volume laws gives equality on every measurable set of extended integers and equality of the integrals of every measurable nonnegative function of volume. Infinite values are included. The <a href="/coverage/sources/perclib-22d8485-associations/">two source contracts</a> preserve this separation between the general erasure argument and the measurability needed for cluster observables.</p>
