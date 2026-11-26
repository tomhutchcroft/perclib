---
{
  "id": "boundary-laws",
  "title": "Boundary wiring and first exit",
  "subtitle": "Independent boundaries, finite cluster laws and first exit",
  "kind": "method",
  "category": "Methods",
  "summary": "Exterior bonds induce independent marks on a domain. Internal connections and boundary edges give a first-exit bound, with the original bond probabilities as weights. A prescribed finite cluster factors into internal connectivity and a closed boundary, leaving exterior coordinates independent.",
  "context": [
    "Independent bond percolation on a countable vertex set $V$, with probabilities $q_{uv}\\in[0,1]$.",
    "A fixed domain $S\\subseteq V$; it is finite only where explicitly required.",
    "Loops are discarded by the open graph; diagonal probabilities are unrestricted."
  ],
  "related": [
    "product-model",
    "connectivity",
    "finite-transcripts",
    "sharpness"
  ],
  "sourceIds": ["hutchcroft-book", "perclib-boundary-wiring", "perclib-first-exit", "dct-sharpness", "perclib-cluster-law", "perclib-boundary-contraction", "perclib-wiring-collapse", "perclib-boundary-forest-associations"],
  "aliases": [
    "boundary wiring",
    "ghost boundary",
    "first exit",
    "escape",
    "boundary functional",
    "finite cluster law",
    "prescribed cluster",
    "domain Markov property"
  ],
  "prototypeUses": []
}
---

## Collapsing the exterior {#section-boundary}

<a id="tag-XN06" data-assertion="definition" data-title="Boundary indicators and internal connections"></a><p>For $u\in S$, let $B_u$ be the indicator that at least one bond from $u$ to $V\setminus S$ is open. Replacing these exterior bonds by a single edge from $u$ to an auxiliary vertex gives the <em>wired boundary</em> description. Write $x\leftrightarrow_S y$ when there is an open path from $x$ to $y$ all of whose vertices lie in $S$, and set $\tau_S(x,y)=\mathbb P(x\leftrightarrow_S y)$ for $x,y\in S$.</p><p>The indicator $B_u$ records an open boundary bond, not a connection to infinity. Identifying the exterior can connect interior vertices whose actual exterior endpoints are disconnected. For example, the two open edges $a-u$ and $b-v$, with $a,b\in S$ and distinct exterior vertices $u,v$ and no other open edges, connect $a$ and $b$ after wiring, but not in the original graph.</p>

<a id="tag-AGF6" data-assertion="proposition" data-title="Independent boundary marks and their marginals"></a><p>The family consisting of all $B_u$, $u\in S$, and all internal bond indicators is mutually independent. Moreover,</p><div class="math-display">$$\mathbb P(B_u=0)=\prod_{v\notin S}(1-q_{uv}).$$</div><p>The product means the limit of finite products over an increasing exhaustion of $V\setminus S$. It is one when the exterior is empty, and zero if any exterior bond has probability one.</p><p><em>Proof.</em> The exterior edges incident to distinct vertices of $S$ form disjoint coordinate blocks, all disjoint from the internal coordinates. Each $B_u$ is a measurable function of its block: its defining event is a countable union of one-edge events. Independence of product-coordinate blocks therefore gives the joint independence. For the marginal, exhaust the exterior by finite sets. The events that all corresponding bonds are closed decrease to $\{B_u=0\}$, and their probabilities are the finite products displayed above.</p>

## Exponential intensities {#section-intensity}

<a id="tag-ZANA" data-assertion="proposition" data-title="Total exterior intensity determines a boundary mark"></a><p>Fix $u\in S$. Suppose $\beta\geq0$, $J_{uv}\geq0$,</p><div class="math-display">$$\sum_{v\notin S}J_{uv}<\infty,\qquad q_{uv}=1-e^{-\beta J_{uv}}\quad(v\notin S).$$</div><p>Then</p><div class="math-display">$$\mathbb P(B_u=0)=\exp\!\left(-\beta\sum_{v\notin S}J_{uv}\right).$$</div><p><em>Proof.</em> For a finite exterior set $F$, the product of closed-bond probabilities is $\exp(-\beta\sum_{v\in F}J_{uv})$. Exhaust the exterior and use summability and continuity of the exponential. In particular, at $\beta=0$ every boundary mark is closed. The stated summability hypothesis avoids any convention involving $0\cdot\infty$.</p>

## A first-exit bound {#section-exit}

<a id="tag-ROY9" data-assertion="theorem" data-title="Boundary functional bounds escape and percolation"></a><p>Let $S$ be finite and contain $x$. Define</p><div class="math-display">$$\Phi_q(x,S)=\sum_{u\in S}\sum_{v\notin S}\tau_S(x,u)q_{uv}.$$</div><p>With extended nonnegative sums,</p><div class="math-display">$$\mathbb P(|K(x)|=\infty)\leq\mathbb P(K(x)\not\subseteq S)\leq\Phi_q(x,S).$$</div><p>For $S=\{x\}$ this becomes the off-diagonal row-sum bound $\mathbb P(K(x)\neq\{x\})\leq\sum_{v\neq x}q_{xv}$. If all boundary probabilities vanish, the escape probability is zero.</p><p><em>Proof.</em> A path from $x$ to the exterior has a first exiting edge $\{u,v\}$, with $u\in S$ and $v\notin S$. Its initial segment witnesses $x\leftrightarrow_S u$. That event depends only on internal edges and is independent of the exiting edge, so the probability that both occur is $\tau_S(x,u)q_{uv}$. Taking the union bound over boundary pairs proves the escape inequality. An infinite cluster cannot be contained in finite $S$, which gives the first inequality. For a singleton, the internal connection is reflexive and has probability one.</p>

<p>The weights here are $q_{uv}$, not $\beta J_{uv}$. For an exponential-intensity profile, $q_{uv}\leq\beta J_{uv}$ gives a further upper bound, usually weaker. Nor does $\Phi_q(x,S)&lt;1$ by itself prove the sharpness theorem: iteration or differential inequalities require additional arguments.</p>

## Equality on the ray {#section-ray-equality}

<a id="tag-6J9C" data-assertion="proposition" data-title="The first-exit boundary bound is exact for initial ray segments"></a>
<p>On $\mathbb N$, let every consecutive pair have probability $t\in[0,1]$, every other non-diagonal pair have probability zero, and diagonal probabilities be arbitrary. For $S_n=\{0,1,\ldots,n\}$,</p>
<div class="math-display">$$\mathbb P(K(0)\not\subseteq S_n)=\Phi_q(0,S_n)=t^{n+1}.$$</div>
<p><em>Proof.</em> Almost surely the open graph lies in the nearest-neighbour ray. It exits $S_n$ from zero exactly when every edge from $0$ to $n+1$ is open. Independence gives $t^{n+1}$. In the boundary sum, the only boundary pair whose probability can be nonzero is $\{n,n+1\}$, and the internal connection from zero to $n$ has probability $t^n$ by the unique-path formula. Thus the sum is $t^n t=t^{n+1}$. At $n=0$ the internal path is empty and has weight one; this includes $t=0$ without changing the convention $t^0=1$. At $t=1$ both sides are one.</p>
<p>The first-exit mechanism itself is more general than a finite domain. On any vertex set, a finite path from $x\in S$ to the exterior has a first exiting edge whose prefix stays in $S$. For any countable $S$ inside an arbitrary ambient vertex set, the internal-connection event is measurable and independent of a specified boundary-edge coordinate: its coordinates are all internal, while the boundary edge is not. The finite-domain bound above then uses the countable ambient union over possible exit pairs. The ray identity shows that this bound can be attained; it is not just a comparison with unspecified constants.</p>

## Keeping the connection after the exit {#section-restricted-exit}

<a id="tag-USAC" data-assertion="theorem" data-title="Restricted-domain first-exit inequality with the remaining connection retained"></a>
<p>Let $V$ be countable, with independent bond probabilities $q_{xy}\in[0,1]$. Let $u\in S\subseteq A\subseteq V$ and $B\subseteq A\setminus S$. The sets need not be finite. Then</p>
<div class="math-display">$$\mathbb P(u\leftrightarrow_A B)\leq\sum_{x\in S}\sum_{y\in A\setminus S}\tau_S(u,x)q_{xy}\mathbb P(y\leftrightarrow_A B).$$</div>
<p>The right side is an extended nonnegative sum. Connections to a set mean connections to at least one of its vertices.</p>
<p><em>Proof.</em> On the event on the left, choose a simple open path in $A$ from $u$ to $B$. Split it at its first edge $\{x,y\}$ leaving $S$. Its prefix, that edge, and its suffix are disjoint finite open witnesses for $u\leftrightarrow_S x$, the opening of $\{x,y\}$, and $y\leftrightarrow_A B$. Apply <a href="/tag/JRCI/">countable BK</a> twice and take the union bound over the possible exit pairs.</p>
<p>The suffix may return to $S$; it is only required to avoid the edges already used by this particular simple path. The prefix may have length zero when $x=u$, and the suffix may have length zero when $y\in B$. Empty witnesses cause no exception. Countability makes the union and all connection events measurable; no moment or transitivity assumption enters.</p>
<p>This is the product-law version of <a href="https://arxiv.org/pdf/1502.03050v3#page=6">Lemma 1.5 of arXiv:1502.03050v3</a>. Unlike the elementary escape bound, it retains the cost of reaching the target after the first exit. That refinement is what the finite-size iteration below uses.</p>

## A finite-size susceptibility criterion {#section-finite-size}

<a id="tag-YLZV" data-assertion="theorem" data-title="Uniform local boundary contraction implies finite susceptibility"></a>
<p>For each vertex $x$, choose a finite set $S_x$ containing $x$. Suppose there are constants $B&lt;\infty$ and $0\leq a&lt;1$ such that, for every $x$,</p>
<div class="math-display">$$\sum_{u\in S_x}\tau_{S_x}(x,u)\leq B,\qquad \Phi_q(x,S_x)\leq a.$$</div>
<p>Then $\chi_q(x)\leq B/(1-a)$ for every $x$, and almost surely every cluster is finite. In particular, a uniform size bound $|S_x|\leq N$ permits $B=N$.</p>
<p><em>Proof.</em> First retain only a finite set $F$ of possible non-loop edges. Write $\tau_F$ and $\chi_F$ for this truncated model, and set $M_F=\sup_x\chi_F(x)$. This supremum is finite: vertices outside the finite endpoint set of $F$ are isolated, and every other cluster is contained in that endpoint set.</p>
<p>A simple open path from $x$ to $y$ either stays in $S_x$ or has a first exit $\{u,v\}$, with $u\in S_x$ and $v\notin S_x$. In the latter case its prefix, exit edge and suffix are pairwise edge-disjoint witnesses. Applying finite BK twice, and then enlarging the internal connection and edge probabilities to their untruncated values, gives</p>
<div class="math-display">$$\tau_F(x,y)\leq\mathbf1_{\{y\in S_x\}}\tau_{S_x}(x,y)+\sum_{u\in S_x}\sum_{v\notin S_x}\tau_{S_x}(x,u)q_{uv}\tau_F(v,y).$$</div>
<p>The internal term is read as zero when $y\notin S_x$. The suffix may return to $S_x$; only edge-disjointness from the chosen prefix and exit edge is used. All events before enlarging probabilities depend on the finite coordinate set $F$, so <a href="/articles/bk-inequality/">finite BK</a> applies directly.</p>
<p>Sum over $y$ and use nonnegativity to interchange sums. The assumptions give</p>
<div class="math-display">$$\chi_F(x)\leq B+\Phi_q(x,S_x)M_F\leq B+aM_F.$$</div>
<p>Taking the supremum over $x$ and rearranging the finite quantity $M_F$ yields $M_F\leq B/(1-a)$. Exhaust all possible edges by increasing finite sets. Every finite open path eventually lies in a truncation, so root cluster volumes increase to their full values. Monotone convergence gives the same bound for $\chi_q(x)$. Finite expectation excludes an infinite cluster at each root, and countability excludes one anywhere.</p>
<p>If a group of vertex permutations acts transitively and preserves $q$, one finite set $S\ni o$ with $\Phi_q(o,S)&lt;1$ suffices. Transport $S$ to each root, preserving both its internal mean and its boundary functional. The bound becomes</p>
<div class="math-display">$$\chi_q(o)\leq\frac{\sum_{u\in S}\tau_S(o,u)}{1-\Phi_q(o,S)}\leq\frac{|S|}{1-\Phi_q(o,S)}.$$</div>
<p>Uniform local contraction is essential in the nontransitive statement. A small escape probability at one root alone gives no comparable control on the clusters reached after exiting its neighbourhood.</p>

## Boundary flux at the critical intensity {#section-critical-flux}

<a id="tag-R84Z" data-assertion="theorem" data-title="Critical boundary flux from a continuous finite-size criterion"></a>
<p>Let finite nonnegative weights $J_{uv}$ on a countable vertex set be invariant under a transitive group of permutations, with finite off-diagonal row sums. Use probabilities $q_\beta(u,v)=1-e^{-\beta J_{uv}}$. Define</p>
<div class="math-display">$$\beta_c=\inf\{\beta\geq0:\mathbb P_\beta(\text{there is an infinite cluster})&gt;0\},\qquad\inf\varnothing=\infty.$$</div>
<p>If $\beta_c&lt;\infty$, then for every finite $S$ containing a fixed root $o$,</p>
<div class="math-display">$$1\leq\Phi_{q_{\beta_c}}(o,S)\leq\beta_c\sum_{u\in S}\tau_{S,\beta_c}(o,u)\sum_{v\notin S}J_{uv}.$$</div>
<p><em>Proof.</em> For fixed finite $S$, the function $\beta\mapsto\Phi_{q_\beta}(o,S)$ is continuous. Indeed, internal connection probabilities are polynomials in finitely many edge probabilities and hence continuous. Each exterior sum $\sum_{v\notin S}(1-e^{-\beta J_{uv}})$ is continuous by dominated convergence: on $0\leq\beta\leq b$ its summands are bounded by the summable sequence $bJ_{uv}$. The boundary functional is a finite sum of products of these continuous functions. It is also nondecreasing by the monotone coupling.</p>
<p>If $\Phi_{q_{\beta_0}}(o,S)&lt;1$ at a finite $\beta_0$, continuity gives $\varepsilon&gt;0$ with $\Phi_{q_{\beta_0+\varepsilon}}(o,S)&lt;1$. The finite-size criterion and transitivity give finite susceptibility at every root at $\beta_0+\varepsilon$. Monotonicity then excludes percolation at every smaller intensity, so $\beta_c\geq\beta_0+\varepsilon&gt;\beta_0$. Applying this implication at $\beta_0=\beta_c$ rules out a boundary functional below one. The second inequality follows termwise from $1-e^{-t}\leq t$.</p>
<p>This establishes a necessary critical boundary-flux inequality. It does not prove that every intensity below $\beta_c$ admits a contracting finite set, or the supercritical lower bound needed to identify a finite-size threshold with $\beta_c$. Those further parts are established in the <a href="/articles/finite-size-sharpness/">threshold-identification argument</a>.</p>


## The law of a prescribed finite cluster {#section-finite-cluster-law}

<p>Fix a finite set $C\subseteq V$ containing $x$. Let $I_C$ be the event that every vertex of $C$ is connected to $x$ inside the induced graph on $C$, and let $D_C$ be the event that every pair from $C$ to $V\setminus C$ is closed. Each boundary pair is indexed once, with its endpoint in $C$ first.</p>

<a id="tag-R3I9" data-assertion="theorem" data-title="A prescribed finite cluster factors into internal connectivity and a closed boundary"></a>
<p>For every configuration,</p>
<div class="math-display">$$\{K(x)=C\}=I_C\cap D_C.$$</div>
<p>This identity holds on arbitrary vertex sets. On countable $V$, the three events are measurable and</p>
<div class="math-display">$$\mathbb P_q(K(x)=C)=\mathbb P_q(I_C)\mathbb P_q(D_C)
=\mathbb P_q(I_C)\prod_{\substack{u\in C\\v\notin C}}(1-q_{uv}).$$</div>
<p>The product is the limit along any increasing finite exhaustion of the boundary pairs; it may be zero.</p>
<p><em>Proof.</em> If $K(x)=C$, any open path from $x$ to a vertex of $C$ stays in $C$, since every vertex on the path is connected to $x$. An open boundary pair would then connect $x$ to a vertex outside $C$. This gives $I_C$ and $D_C$. Conversely, internal connectivity puts $C$ in the root cluster, while a first-exit argument and the closed boundary prevent the cluster from leaving $C$.</p>
<p>The internal event depends on finitely many pair coordinates, so is a measurable cylinder even when the ambient vertex set is uncountable. On countable $V$, the boundary event is a countable intersection of closed-coordinate events. The internal and boundary blocks are disjoint, so <a href="/tag/DYU8/">block independence</a> factors their probabilities. The <a href="/tag/QH7Q/">countable closed-product formula</a> gives the last expression. Loops belong to no boundary and do not affect internal connectivity.</p>
<p>For $C=\{x\}$ the internal event is certain, recovering the probability that $x$ is isolated. If $C=V$ is finite, the boundary product is empty and equals one. If $x\notin C$, the cluster-equality event is empty. No positivity assumption on the displayed probability is made.</p>

## The law outside a known finite cluster {#section-cluster-exterior}

<a id="tag-E7R2" data-assertion="theorem" data-title="A fixed finite-cluster event is independent of the configuration strictly outside it"></a>
<p>Let $V$ be countable, let $C$ be finite with $x\in C$, and let $B$ be a measurable event determined by pairs with both endpoints in $V\setminus C$. Then</p>
<div class="math-display">$$\mathbb P_q(K(x)=C,\ B)=\mathbb P_q(K(x)=C)\mathbb P_q(B).$$</div>
<p>If $\mathbb P_q(K(x)=C)&gt;0$, the conditional law of the configuration on $V\setminus C$ is therefore the original product law restricted to pairs in that set. In particular, for $y,z\notin C$,</p>
<div class="math-display">$$\mathbb P_q(y\leftrightarrow_{V\setminus C}z\mid K(x)=C)
=\tau_{q,V\setminus C}(y,z).$$</div>
<p><em>Proof.</em> The preceding decomposition shows that $\{K(x)=C\}$ is determined by the internal and boundary pairs, all of which meet $C$. Changing pairs strictly outside $C$ cannot change this event. It is therefore independent of $B$ by block independence. Dividing by its positive probability gives the conditional formula. Applying the factorization to every measurable event of the exterior restriction identifies its conditional product law.</p>
<p>The factorization remains valid when $\{K(x)=C\}$ has probability zero; a conditional probability obtained by division does not. Boundary pairs are forced closed by the conditioning, and the internal configuration is constrained to connect $C$. Neither belongs to the unchanged exterior product law.</p>
<p>On $\{K(x)=C\}$, a path between two exterior vertices cannot enter $C$, since the boundary is closed. Thus the conditional full-graph connection probability also equals $\tau_{q,V\setminus C}(y,z)$. It need not equal the unconditioned full-graph value $\tau_q(y,z)$: without the conditioning, paths may pass through $C$. The domain in this formula is part of the conclusion.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-cluster-law/">eight-contract inventory</a> records the deterministic identity, measurability, factorization and exterior-connection consequence. The product expression and positive-probability conditional interpretation are deductions from the recorded factorization and earlier product laws. No independence of an adaptively chosen random exterior is assumed without first fixing the cluster event.</p>

## Last exit from the exposed cluster {#section-contraction-source}

<p>The source proves <a href="/tag/USAC/">USAC</a> by an exploration argument, providing an alternative to the BK proof above. First suppose $S$ is finite and expose the cluster $K$ of $u$ inside $S$. If an open path in $A$ reaches a target not in $K$, take its last edge $\{x,y\}$ leaving $K$. Its remainder stays in $A\setminus K$. Moreover, $y\notin S$: an open edge from $K$ to another vertex of $S$ would put that vertex in the internal cluster.</p>
<p>For a fixed possible $K$, the event specifying this cluster reads only pairs inside $S$ that meet $K$. The exit pair has its second endpoint outside $S$, and the remaining connection reads pairs with both endpoints in $A\setminus K$. These three coordinate sets are disjoint. Their probabilities therefore factor. Enlarge the remaining connection to one in $A$, then sum over possible clusters containing $x$. The cluster events are disjoint and their union is $\{u\leftrightarrow_S x\}$, giving the factor $\tau_S(u,x)$. A union bound over exit pairs gives the desired inequality.</p>
<p>This finite-domain argument also applies to a target lying in $S$ if it is not joined to $u$ inside $S$. That form is needed for susceptibility: a path may leave and re-enter $S$ before reaching its endpoint. For infinite $S$, restrict a connecting path to its finite vertex support $F$, apply the finite argument with $S\cap F$ and $A\cap F$, and enlarge the internal connections back to $S$. A term whose exit endpoint lies outside $F$ has zero remaining-connection probability. Thus an endpoint in $S\setminus F$ contributes nothing, and the surviving exit endpoints lie outside $S$. The directed union over finite supports recovers every connection. All sums are nonnegative and may be infinite.</p>
<p>For <a href="/tag/YLZV/">YLZV</a>, the source truncates by finite vertex domains rather than finite edge sets. In a finite $\Lambda$, let $\chi_\Lambda(x)$ be the expected internal cluster size, read as zero for $x\notin\Lambda$, and put $M_\Lambda=\sup_x\chi_\Lambda(x)\leq|\Lambda|$. At $x\in\Lambda$, apply the preceding decomposition with $S_x\cap\Lambda$. Its internal contribution is at most $B$. An exit endpoint still in $\Lambda$ must lie outside $S_x$; an endpoint outside $\Lambda$ has no remaining connection. Enlarging internal probabilities to those in $S_x$ consequently gives</p>
<div class="math-display">$$\chi_\Lambda(x)\leq B+\Phi_q(x,S_x)M_\Lambda\leq B+aM_\Lambda.$$</div>
<p>This uses the remaining-connection factor: it does not assert that the full boundary functional of $S_x\cap\Lambda$ is bounded by that of $S_x$. Taking the supremum and rearranging is legitimate because $M_\Lambda$ is finite. Exhaustion then gives $\chi(x)\leq B/(1-a)$. The exported inequality allows $B=\infty$ as well, but almost-sure finiteness needs $B&lt;\infty$. Countability makes the finite-cluster conclusion simultaneous at every root. No transitivity, finite range or separate row-sum bound is required. Singleton domains recover the off-diagonal row-sum criterion, including $a=0$.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-wiring/">source inventory</a> records the fifteen contraction contracts and their full hypotheses. The restricted-exit export even permits $S$ not contained in $A$; the article uses the usual nested-domain formulation.</p>

## What the collapse preserves {#section-collapse-source}

<p>Wiring a domain $\Lambda$ replaces each family $\{\{u,v\}:v\notin\Lambda\}$, for $u\in\Lambda$, by one ghost bond. Different ghost bonds use disjoint original pairs, and every proper internal bond forms a singleton coordinate block. In the intensity model, a summable block with total intensity $j$ is entirely closed with probability $e^{-\beta j}$. Its replacement is therefore open with probability $1-e^{-\beta j}$. Identifying vertices also creates diagonal pairs; the collapse discards them. This leaves a product law with the original internal intensities and ghost intensity $\sum_{v\notin\Lambda}J_{uv}$ at $u$.</p>
<p>Every original open path maps to a path after collapse, allowing repeated consecutive vertices to be omitted. Conversely, follow a collapsed path starting at an interior vertex $u$. Before its first visit to the ghost, every internal edge is an original edge, and the edge reaching the ghost has an open representative from its interior endpoint to the exterior. Hence the original cluster of $u$ exits $\Lambda$ exactly when the collapsed cluster reaches the ghost. If that cluster avoids the ghost, connections from $u$ to other interior vertices agree in the two configurations. Without this avoidance hypothesis, wiring may join different exterior components, as the example at the start of the article shows.</p>
<p>The deterministic path statements need neither countability nor summability. Countability makes the collapse measurable; summability makes each aggregated intensity finite. For ghost wiring only the exterior rows at vertices of $\Lambda$ are needed. The derivative application assumes summable rows everywhere, a stronger convenient hypothesis. No positive-intensity assumption is imposed, and the law includes $\beta=0$, an empty exterior and arbitrary original diagonal intensities.</p>


## The boundary and forest associations {#section-boundary-associations}

<p>The <a href="/coverage/sources/perclib-f51f639-boundary-martingales/">Train 9 association source</a> packages the existing boundary, forest and walk estimates under thirteen assertion tags. It retains the distinctions needed in applying them: a bound on simple host paths needs no assumption about off-host bonds, whereas a bound on the entire cluster requires those bonds to be closed. The forest formulas include the root's empty path and permit infinite susceptibility. The ray formulas include probability one, where susceptibility is infinite.</p>
<p>For boundary laws, the marks and internal coordinates are jointly independent because their bond-coordinate sets are disjoint. Their closed-mark probabilities are limits of finite products along every increasing exhaustion of the exterior. A mark records an edge to that exterior; it does not record an original connection between two interior vertices. Collapsing the whole exterior may create such a connection even when the original clusters were disjoint. The source's internal-connection statement instead concerns the induced graph and its restricted probability profile.</p>
