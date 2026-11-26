---
{
  "id": "hierarchical-block-coalescent",
  "title": "Exact block layers of hierarchical percolation",
  "subtitle": "Each hierarchical block adds an independent complete-graph layer, inside which the clusters merge as a multiplicative coalescent.",
  "kind": "model",
  "category": "Critical phenomena",
  "summary": "For the exact radial kernel on the hierarchical lattice, percolation is the union of independent complete-graph layers, one for each block. Inside a block the cluster partition is a finite multiplicative coalescent started from the clusters of its children, which gives exact moment recursions across scales.",
  "context": [
    "The hierarchical lattice $\\mathbb H_L^d$, for integers $L\\geq2$ and $d\\geq1$, has blocks of level $n$ with $Q^n$ vertices, $Q=L^d$; $h(x,y)$ is the least level of a block containing distinct $x,y$, and $\\|x-y\\|=L^{h(x,y)}$.",
    "$s=d+\\alpha$ with $\\alpha>0$, the intensity is $\\beta\\geq0$, and the layer of a level-$n$ block runs for time $t_n=\\beta L^{-sn}$.",
    "$X_{n,t}$ is the cluster partition of an $n$-block at time $t\\in[0,t_n]$ of its layer, and $S_p(n,t)=S_p(X_{n,t})$ are its mass power sums. Clusters are those of the truncated block law, which uses only the layers of blocks inside the block, not intersections of full clusters with the block."
  ],
  "related": [
    "multiplicative-coalescent",
    "hierarchical-lattice",
    "hierarchical-runaway",
    "hierarchical-two-point",
    "universal-tightness",
    "cutoff-hydrodynamics"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "hutchcroft-hierarchical-volumes-2022"
  ],
  "aliases": [
    "exact block layers",
    "block coalescent",
    "hierarchical block coalescent",
    "exact radial hierarchical model",
    "periodic block kernel"
  ],
  "prototypeUses": []
}
---

<p>On the <a href="/articles/hierarchical-lattice/">hierarchical lattice</a>, long-range percolation with the exact radial kernel $J_\infty(x,y)=\frac{L^s}{L^s-1}\|x-y\|^{-s}$, $s=d+\alpha$, has an exact multiscale structure. It is the union of independent layers, one for each finite block, and in the layer of a block every pair of its points is joined independently with the same probability. The layer of a block of level $n$ has intensity $t_n=\beta L^{-sn}$, so the clusters inside a block are obtained from the clusters of its children by running a <a href="/articles/multiplicative-coalescent/">finite multiplicative coalescent</a> for time $t_n$.</p>

<p>This structure, due to Hutchcroft (2022), turns the moments of block clusters into an exact recursion. Within a level, the expected power sums $\mathbb E S_p$ of the cluster sizes obey the coalescent moment equations. Between levels, the power sums of a block start as the sums of those of its $Q=L^d$ independent children, and the expected $q$th power of the size of the root cluster is $Q^{-n}\mathbb E S_{q+1}$. The universal <a href="/tag/25TW/">moment comparisons for finite percolation</a> bound the expected power sums by the mean of $S_2$ and the typical size of the largest cluster, and reduce the mean equation to $\mu'=\mu^2$ up to an explicit error.</p>

<p>These recursions are the basis of the analysis of critical cluster volumes in the exact model at $\beta=\beta_c$ and $0&lt;\alpha&lt;d$, in the three regimes $d&gt;3\alpha$, $d=3\alpha$ and $d&lt;3\alpha$, summarised in <a href="/articles/hierarchical-runaway/">the hierarchical runaway observable</a>.</p>

## Definitions and setting {#section-definitions}

<p>Fix integers $L\geq2$, $d\geq1$, an exponent $\alpha&gt;0$ and an intensity $\beta\geq0$. Write $s=d+\alpha$, $Q=L^d$, and let $h(x,y)$ be the least level of a block containing distinct vertices $x,y$ of the <a href="/articles/hierarchical-lattice/">hierarchical lattice</a> $\mathbb H_L^d$. Thus $\|x-y\|=L^{h(x,y)}$: two vertices first share a block of level $j$ exactly when their distance is $L^j$. A block of level $n$, or $n$-block, has $Q^n$ vertices and is the disjoint union of its $Q$ children, the $(n-1)$-blocks it contains. $B_n$ denotes the $n$-block containing the root $o$. The constructions below work for every $\alpha&gt;0$; the critical-volume theorems that use them assume $0&lt;\alpha&lt;d$.</p>
<p><em>Layers and the truncated block law.</em> Each finite block $B$ carries a layer, independent <a href="/articles/product-model/">bond percolation</a> on the complete graph on $B$ with edge probability $1-e^{-t_n}$ when $B$ is an $n$-block, where $t_n=\beta L^{-sn}$. The layer of $B$ contains every pair of points of $B$, including pairs in the same child, and the layers of different blocks are independent; the <a href="/tag/VI3Y/">layer decomposition</a> realises them by exponential clocks and shows that the union $\omega$ of all layers is percolation with the exact radial kernel. Let $\eta_B$ be the union of the layers of the blocks contained in $B$. The cluster $K_{\eta_B}(o)$ of $o$ in $\eta_B$ uses only the layers inside $B$; this is the <strong>truncated block law</strong>, and the identities on this page concern it. If $\omega[B]$ is the graph induced by $\omega$ on $B$, then</p>
<div class="math-display">$$K_{\eta_B}(o)\subseteq K_{\omega[B]}(o)\subseteq K_\omega(o)\cap B,$$</div>
<p>and the last set may contain vertices reached by paths leaving $B$.</p>
<p><em>The double index.</em> A state of the block process is indexed by a level $n\geq0$ and a time $t\in[0,t_n]$ within that level. For a hierarchical $n$-block, start from the terminal partitions of its $Q$ children and run the parent clocks for $0\leq t\leq t_n$. Call the resulting partition $X_{n,t}$; it is a <a href="/articles/multiplicative-coalescent/">finite multiplicative coalescent</a> started from the union of the children's terminal partitions. The blocks of this coalescent, the elements of its partition, are the clusters of the layer graph; elsewhere on this page "block" means a hierarchical block. Its terminal state, at $t=t_n$, is the component partition of $\eta_{B_n}$ by the <a href="/tag/VI3Y/">layer decomposition</a>. At an intermediate time its edges are independent, with open probabilities</p>
<div class="math-display">$$1-\exp\!\left[-t-\beta\sum_{m=h(x,y)}^{n-1}L^{-sm}\right].$$</div>
<p>The sum in the exponent is empty for endpoints in different children. Since the edges are independent, the <a href="/articles/harris-inequality/">Harris inequality</a> and the <a href="/articles/bk-inequality/">BK inequality</a> apply at each intermediate time. Passing from level $n$ to level $n+1$, called gluing, assembles $X_{n+1,0}$ from the terminal partitions $X_{n,t_n}$ of $Q$ independent children.</p>
<p><em>Notation.</em> The following symbols are fixed on this page.</p>
<ul><li>$S_p(n,t)=S_p(X_{n,t})=\sum_{A\in X_{n,t}}|A|^p$, the mass power sums; $\mu_n(t)=\mathbb E S_2(n,t)$.</li><li>$K_{n,t}(o)$, the cluster of $o$ in $X_{n,t}$; at $t=t_n$ it is $K_{\eta_{B_n}}(o)$.</li><li>$Z_{n,t}$, the largest cluster size in $X_{n,t}$, and $M_n=\min\{m\geq1:\mathbb P(Z_{n,t_n}\geq m)\leq e^{-1}\}$, the terminal <a href="/articles/universal-tightness/">integer quantile</a> of the largest cluster.</li><li>$\epsilon_n(t)=\bigl(\mathbb E S_4(n,t)-\operatorname{Var}S_2(n,t)\bigr)/\mu_n(t)^2$, the relative error in the mean equation $\mu_n'=(1-\epsilon_n)\mu_n^2$ of the <a href="/tag/X2A4/">moment-control theorem</a>.</li></ul>
<p><em>The hydrodynamic condition.</em> The exact derivative of $\mu_n(t)$ is $\mathbb E S_2(n,t)^2-\mathbb E S_4(n,t)$, by the <a href="/tag/22H8/">coalescent moment equations</a>. If $S_2(n,t)$ is concentrated around its mean and $\mathbb E S_4(n,t)$ is small compared with $\mu_n(t)^2$, then $\mu_n'\approx\mu_n^2$, the equation satisfied by the second moment of <a href="/articles/multiplicative-coalescent/#section-coalescent-moments">Smoluchowski's coagulation equation</a> with multiplicative kernel. The block process satisfies the <strong>hydrodynamic condition</strong> if $M_n=o(L^{(d+\alpha)n/2})$. At criticality $\mu_n(t)$ is of order $L^{(d+\alpha)n}$ (<a href="/tag/2VXH/">critical truncated-block means</a>), so the condition says that the square of a typical largest cluster is negligible compared with $\mathbb E S_2$: no single cluster carries a positive fraction of $S_2$, which is what makes $S_2$ concentrate. Together with a lower bound $\mu_n(t)\geq c_0L^{(d+\alpha)n}$ the condition makes the approximation valid uniformly in $t$, by the <a href="/tag/X2A4/">moment-control theorem</a>. The same name is used for cutoff families of long-range models in <a href="/articles/cutoff-hydrodynamics/">cutoff hydrodynamics</a>.</p>

## Exact block layers {#section-exact-block-layers}

<a id="tag-VI3Y" data-assertion="proposition" data-title="Independent complete-block layers and the hierarchical cluster law"></a>
<p>For every finite hierarchical block $B$ and every unordered pair $\{x,y\}\subset B$, take independent rate-one exponential variables $T_{B,\{x,y\}}$. The layer of an $n$-block $B$ contains the edges with $T_{B,\{x,y\}}\leq t_n$, where $t_n=\beta L^{-sn}$. Let $\eta_B$ be the union of the layers of all blocks contained in $B$, and let $\omega$ be the union of all layers. Then $\omega$ is independent bond percolation with probabilities $1-e^{-\beta J_\infty(x,y)}$, where</p>
<div class="math-display">$$J_\infty(x,y)=\sum_{m=h(x,y)}^\infty L^{-sm}
=\frac{L^s}{L^s-1}\|x-y\|^{-s}.$$</div>
<p>For an $n$-block $B$, the law of $\eta_B$ is instead given by the truncated weights</p>
<div class="math-display">$$J_n(x,y)=\sum_{m=h(x,y)}^n L^{-sm}
=J_\infty(x,y)-\frac{L^{-sn}}{L^s-1}\qquad(x,y\in B,\ x\ne y).$$</div>
<p>In this coupling the induced graph $\omega[B]$ is $\eta_B$ together with an independent complete-graph layer whose edge probability is $1-\exp[-\beta L^{-sn}/(L^s-1)]$. If $B_n$ is the $n$-block containing $o$, then the clusters of $o$ in $\eta_{B_n}$ increase to its cluster in $\omega$.</p>
<p><em>Idea of the proof.</em> A pair of vertices has one independent copy in each block containing both, that is, in its common blocks of levels $m\geq h(x,y)$. The edge is absent exactly when no copy is open, which has probability $\exp(-\beta\sum_mL^{-sm})$, and the geometric series gives the two kernels. Different pairs use disjoint sets of clocks, so their edges are independent.</p>
:::details Proof
<p>The blocks containing a fixed pair are its unique common blocks at levels $m\geq h(x,y)$. The probability that all their copies of the edge are absent is the product of their exponential survival probabilities. The geometric series gives $J_\infty$ and $J_n$. Different physical pairs use disjoint collections of independent variables, even when they lie in the same block. Their open indicators are therefore independent.</p>
<p>For endpoints in $B$, the remaining copies lie in the strict ancestors of $B$. Their total weight is $\sum_{m=n+1}^\infty L^{-sm}=L^{-sn}/(L^s-1)$, independently of the endpoints. These variables are independent of those defining $\eta_B$.</p>
<p>Finally every open edge of $\omega$ occurs in at least one finite-level layer. A finite open path uses only finitely many such layers, all eventually contained in some $B_n$. This proves the increasing-cluster assertion. The full law has finite intensity row sum, since the number of vertices at distance $L^m$ is $Q^m-Q^{m-1}$ and $\sum_m L^{-\alpha m}&lt;\infty$.</p>
:::

## Passing between scales and rooted moments {#section-coalescent-gluing}

<a id="tag-54V4" data-assertion="proposition" data-title="Independent-child gluing and the rooted cluster identity"></a>
<p>For the exact model of VI3Y, let $S_p(n,t)=S_p(X_{n,t})$. At level zero all these variables equal one. For $n\geq1$ the initial variables satisfy</p>
<div class="math-display">$$S_p(n,0)=\sum_{\ell=1}^{Q}S_p^{(\ell)}(n-1,t_{n-1}),$$</div>
<p>where the child vectors, including all their coordinates $p$, are independent and identically distributed. Hence, for every finitely supported sequence $m=(m_p)_{p\geq2}$ of nonnegative integers,</p>
<div class="math-display">$$\mathbb E\prod_{p\geq2}S_p(n,0)^{m_p}
=\sum_{m^{(1)}+\cdots+m^{(Q)}=m}
\left[\prod_{p\geq2}\binom{m_p}{m_p^{(1)},\ldots,m_p^{(Q)}}\right]
\prod_{\ell=1}^Q\mathbb E\prod_{p\geq2}S_p(n-1,t_{n-1})^{m_p^{(\ell)}}.$$</div>
<p>For example, if $Y_p=S_p(n-1,t_{n-1})$, then</p>
<div class="math-display">$$\mathbb E S_p(n,0)=Q\mathbb E Y_p,\qquad
\mathbb E[S_p(n,0)S_q(n,0)]
=Q\mathbb E(Y_pY_q)+Q(Q-1)\mathbb E Y_p\,\mathbb E Y_q.$$</div>
<p>Write $K_{n,t}(o)$ for the cluster of $o$ in the intermediate block graph. For every integer $q\geq0$ and every $0\leq t\leq t_n$,</p>
<div class="math-display">$$\mathbb E|K_{n,t}(o)|^q=Q^{-n}\mathbb E S_{q+1}(n,t).$$</div>
<p><em>Idea of the proof.</em> The children of a block are independent and identically distributed, and at the start of the parent layer none of their clusters have merged, so the power sums of the children add; the multinomial theorem then gives the mixed moments. For the rooted identity, summing $|K(x)|^q$ over the vertices $x$ counts a component of size $a$ exactly $a$ times, and translation invariance makes every vertex of the block a typical root.</p>
:::details Proof
<p>All coordinates defining different child interiors are independent, and their translated laws agree. At time zero their components have not yet been joined, so the sums of their powers add. Apply the multinomial theorem to each $p$ and then use independence between children. The terms with both factors in one child and in two distinct children give the stated two-factor example.</p>
<p>For any deterministic partition of $B_n$, summing $|K(x)|^q$ over vertices counts each component of size $a$ exactly $a$ times, giving $\sum_x|K(x)|^q=S_{q+1}$. Translations of $B_n$, viewed as a finite subgroup, preserve hierarchical distances, the block decomposition and all clock laws. Every root therefore has the same cluster-size law at time $t$. Take expectations and divide the deterministic identity by $|B_n|=Q^n$.</p>
:::
<p>Together with the <a href="/tag/22H8/">coalescent moment equations</a>, the gluing identity gives exact equations and initial values for all mixed moments at every scale. For the variance $V_n(t)=\operatorname{Var}(S_2(n,t))$ and the covariance $C_n(t)=\operatorname{Cov}(S_2(n,t),S_3(n,t))$, which satisfy the <a href="/tag/C1BP/">exact variance and covariance equations</a> within a level, independent children additionally give the exact gluing identities $V_{n+1}(0)=QV_n(t_n)$ and $C_{n+1}(0)=QC_n(t_n)$.</p>

## Uniform moment control {#section-coalescent-concentration}

<a id="tag-X2A4" data-assertion="theorem" data-title="Block moment comparisons, concentration and the mean-equation error"></a>
<p>Use the exact block process of <a href="/tag/VI3Y/">VI3Y</a> and <a href="/tag/Z960/">Z960</a>, at any fixed $\beta\geq0$. Let $Z_{n,t}$ be its largest cluster, let $S_p(n,t)$ be its mass power sums, and define the terminal integer quantile</p>
<div class="math-display">$$M_n=\min\{m\geq1:\mathbb P(Z_{n,t_n}\geq m)\leq e^{-1}\}.$$</div>
<p>For every fixed list of indices $p_i\geq1$, the mixed-moment comparisons of <a href="/tag/25TW/">25TW</a> hold uniformly in $n$ and $0\leq t\leq t_n$. For fixed $p,q\geq1$ one also has</p>
<div class="math-display">$$\mathbb E S_{p+q}(n,t)\leq\mathbb E[S_p(n,t)Z_{n,t}^{q}]
\leq C_{p,q}M_n^q\mathbb E S_p(n,t).$$</div>
<p>For $n\geq1$,</p>
<div class="math-display">$$\mathbb E S_p(n,t)\geq\mathbb E Z_{n,t}^p\geq\frac{M_{n-1}^p}{2^p e}.$$</div>
<p>At $n=0$ all power sums and the maximum are identically one; no negative-index quantile is needed.</p>
<p>Put $\mu_n(t)=\mathbb E S_2(n,t)$. There is a universal finite constant $C$ such that</p>
<div class="math-display">$$\frac{\operatorname{Var}(S_2(n,t))}{\mu_n(t)^2}\leq C\frac{M_n^2}{\mu_n(t)},\qquad
\mu_n'(t)=(1-\epsilon_n(t))\mu_n(t)^2,$$</div>
<div class="math-display">$$\epsilon_n(t)=\frac{\mathbb E S_4(n,t)-\operatorname{Var}(S_2(n,t))}{\mu_n(t)^2},\qquad
0\leq\epsilon_n(t)\leq\min\!\left\{1,C\frac{M_n^2}{\mu_n(t)}\right\}.$$</div>
<p>If $\sup_{0\leq t\leq t_n}M_n^2/\mu_n(t)\to0$, then $S_2(n,t)/\mu_n(t)\to1$ in $L^r$ for every fixed $1\leq r&lt;\infty$, uniformly over $0\leq t\leq t_n$, and $\sup_t\epsilon_n(t)\to0$. A sufficient pair of hypotheses is</p>
<div class="math-display">$$\inf_{0\leq t\leq t_n}\mu_n(t)\geq c_0 L^{(d+\alpha)n}\quad\text{for all sufficiently large }n,\qquad
M_n=o\!\left(L^{(d+\alpha)n/2}\right),\qquad c_0&gt;0.$$</div>
<p>This last implication keeps the mean lower bound and the hydrodynamic condition as separate inputs.</p>
<p><em>Idea of the proof.</em> At every time of the layer the block configuration is independent bond percolation on a finite graph, so the universal <a href="/tag/25TW/">power-sum moment comparisons</a> apply with the whole block as window, and the current maximum is dominated by the terminal one. The lower bound holds because a parent's maximum is at least the terminal maximum of any child. The variance bound is the <a href="/tag/25Z4/">distinct-cluster covariance bound</a>, and the error in the mean equation is the exact derivative of $\mu_n$ minus $\mu_n^2$.</p>
:::details Proof
<p>At every intermediate time the graph has independent bonds, as described in Definitions and setting. Apply the <a href="/tag/25TW/">power-sum moment comparisons</a> with the whole block as the window. The current maximum is bounded by its terminal maximum in the clock coupling, so its integer quantile is at most $M_n$. This gives the uniform upper comparisons. The parent maximum is at least the terminal maximum of any one child. Minimality of the child's integer quantile gives $\mathbb P(Z_{n-1,t_{n-1}}\geq M_{n-1}-1)&gt;e^{-1}$, and $M_{n-1}\geq2$. This proves the lower comparison.</p>
<p>The <a href="/tag/25Z4/">distinct-cluster covariance bound</a> and the upper comparison with $p=q=2$ give</p>
<div class="math-display">$$\operatorname{Var}(S_2(n,t))\leq\mathbb E S_4(n,t)\leq C M_n^2\mu_n(t).$$</div>
<p>The exact derivative given by the <a href="/tag/22H8/">moment equations</a> is $\mu_n'=\mathbb E S_2^2-\mathbb E S_4$. Subtracting and adding $\mu_n^2$ gives the stated error. The covariance bound makes it nonnegative; nonnegativity of the variance gives its upper bound by $\mathbb E S_4/\mu_n^2$. Finally $S_2^2-S_4\geq0$ pointwise, so $\mu_n'\geq0$ and $\epsilon_n\leq1$. At $t=0$ and $t=t_n$ the derivatives are one-sided.</p>
<p>The displayed ratio bound proves uniform $L^2$ convergence under its stated hypothesis. For every fixed larger exponent the normalized power sums have uniformly bounded higher moments by the power-sum moment comparisons. Splitting according to whether $|S_2/\mu_n-1|$ exceeds a threshold and applying Hölder upgrades the convergence to any fixed finite $L^r$; exponents at most two follow directly from $L^2$. All these bounds are uniform in the intermediate time. The sufficient pair of hypotheses makes $M_n^2/\mu_n(t)$ tend to zero uniformly.</p>
:::

## Examples and non-examples {#section-examples}

<p><em>The first level.</em> The children of a $1$-block are single vertices, so $X_{1,0}$ is the partition into singletons and $X_{1,t}$ is the component partition of the <a href="/articles/finite-random-graphs/">Erdős–Rényi graph</a> on $Q$ vertices with edge probability $1-e^{-t}$, for $0\leq t\leq t_1=\beta L^{-s}$. In particular $S_p(1,0)=Q$ for every $p$.</p>
<p><em>The mean recursion.</em> Taking $p=2$ in the <a href="/tag/54V4/">gluing identity</a> and $q=1$ in the rooted identity gives</p>
<div class="math-display">$$\mu_n(0)=Q\mu_{n-1}(t_{n-1}),\qquad \mu_n(t_n)=Q^n\,\mathbb E|K_{\eta_{B_n}}(o)|.$$</div>
<p>Within a level $\mu_n$ is nondecreasing, and the mean equation of the <a href="/tag/X2A4/">moment-control theorem</a> reads $(1/\mu_n)'=-(1-\epsilon_n)$. When $\epsilon_n$ is small, the reciprocal of the mean therefore decreases by approximately $t_n$ across level $n$ and is multiplied by $Q^{-1}$ at gluing. Heuristically, if $1/\mu_n(0)\approx aL^{-sn}$ at every scale, these two steps give $aL^{-s(n+1)}=Q^{-1}(a-\beta)L^{-sn}$, so $a=\beta/(1-q)$ with $q=L^{-\alpha}$, that is $\mu_n(0)\approx\frac{1-q}{\beta}L^{(d+\alpha)n}$. A smaller $a$ drives the reciprocal to zero after finitely many levels, and a larger one leaves the mean of lower order. At $\beta=\beta_c$ the <a href="/tag/W2VN/">reciprocal-mean theorem</a> makes this exact: $\mu_n(t)=L^{sn}/\bigl(\beta_c(A-t/t_n-R_n(t))\bigr)$ with $A=(1-q)^{-1}$ and a nonnegative remainder $R_n(t)$.</p>
<p><em>Non-example: the full law restricted to a block.</em> The partition of an $n$-block $B$ into the sets $K_\omega(x)\cap B$ is not the terminal state of the block process. Its restrictions to the children of $B$ depend on the layers of the common ancestors and on paths through other children, so they are not independent, and paths through vertices outside $B$ join clusters of different children before the layer of $B$ acts. The gluing identity, which uses independent children whose clusters have not yet merged, does not apply to it. The critical analysis passes from the truncated law to full clusters by a separate argument (<a href="/articles/hierarchical-runaway/#section-critical-ghost-absorption">absorbing connections beyond the truncated block</a>).</p>

## Consequences and applications {#section-consequences}

<p>At $\beta=\beta_c$ and $0&lt;\alpha&lt;d$ the recursion governs the critical exact model, whose analysis is summarised in <a href="/articles/hierarchical-runaway/">the hierarchical runaway observable</a>. The <a href="/tag/2VXH/">critical truncated-block means</a> are of order $L^{\alpha n}$ for every such $\alpha$. Above the critical dimension, $d&gt;3\alpha$, the <a href="/tag/6WO3/">hydrodynamic condition holds</a> and the rooted moments have <a href="/tag/FY23/">explicit equivalents</a>. Below it, $d&lt;3\alpha$, <a href="/tag/I7HB/">hydrodynamics fails</a> and the critical cluster volume has <a href="/tag/ZDDE/">tail of order</a> $x^{-(d-\alpha)/(d+\alpha)}$. At $d=3\alpha$ the <a href="/tag/UL8V/">hydrodynamic condition holds</a> and the volume tail is of order <a href="/tag/FMVJ/">$m^{-1/2}(\log m)^{1/4}$</a>.</p>

## Variants and generalisations {#section-periodic-block-kernel}

<p><em>General radial kernels.</em> The layer decomposition needs only a radial kernel that decreases with the level. If $J(x,y)=j(h(x,y))$ with $j$ nonincreasing and $j(m)\to0$, write $j(h)=\sum_{m\geq h}w_m$ with $w_m=j(m)-j(m+1)\geq0$. Percolation with edge probabilities $1-e^{-\beta J(x,y)}$ is then the union of independent complete-graph layers in which the layer of an $n$-block has intensity $\beta w_n$, and the gluing and rooted identities and the moment comparisons hold with $\beta w_n$ in place of $t_n$. The exact kernel $J_\infty$ is the case of geometric layer times $t_n=\beta L^{-sn}$, which make the recursion the same at every scale up to scaling; the amplitude of the mean recursion above and the constant of the periodic kernel below use this. A union of complete-graph block layers has a kernel of the form $\sum_{B\ni x,y}w_B$, a sum over the blocks containing both points, so a kernel that is only comparable to $\|x-y\|^{-s}$ is in general not of this form.</p>
<p><em>Periodic boundary conditions.</em> Periodic percolation on $B_n$ is independent bond percolation on $B_n$ in which distinct $x,y$ are joined with probability $1-\exp(-\beta J_n^{\mathrm{per}}(x,y))$, where $J_n^{\mathrm{per}}$ is the exact kernel summed over the fibres of the coordinate projection defined below.</p>

<a id="tag-YY9S" data-assertion="proposition" data-title="Periodizing the hierarchical kernel adds an explicit final coalescent time"></a>
<p>Write the hierarchical group as $\mathbb H=\bigoplus_{j\geq1}(\mathbb Z/L\mathbb Z)^d$. Let $B_n$ be the subgroup supported on coordinates $1,\ldots,n$, let $T_n$ be the subgroup supported on coordinates greater than $n$, and let $\pi_n:\mathbb H\to B_n$ be the coordinate projection. Thus $\mathbb H/T_n\cong B_n$. For distinct $x,y\in B_n$, define</p>
<div class="math-display">$$J_n^{\mathrm{per}}(x,y)=\sum_{z:\pi_nz=y}J_\infty(x,z),\qquad
J_n^{\mathrm{free}}(x,y)=\sum_{j=h(x,y)}^nL^{-(d+\alpha)j}.$$</div>
<p>With $s=d+\alpha$ and $q=L^{-\alpha}$, the sum converges and</p>
<div class="math-display">$$J_n^{\mathrm{per}}(x,y)=J_n^{\mathrm{free}}(x,y)
+\frac{q}{1-q}L^{-sn}.\tag{9}$$</div>
<p>At any intensity $\beta\geq0$, periodic percolation on $B_n$ therefore has the cluster law obtained by running the last coalescent stage to time $\beta L^{-sn}/(1-q)$, leaving the earlier stages unchanged.</p>
<p><em>Idea of the proof.</em> The fibre of the projection over $y$ consists of $y$ itself and, for each $k\geq1$, of $(Q-1)Q^{k-1}$ further points at distance $L^{n+k}$ from $x$. Summing the kernel over the fibre adds a constant independent of $x$ and $y$, which is an independent complete-graph layer, that is, extra coalescent time.</p>
:::details Proof
<p>Put $Q=L^d$ and $r=L^{-s}$, so that $Qr=q&lt;1$. In the fibre $\pi_nz=y$, the point $z=y$ contributes $J_n^{\mathrm{free}}(x,y)+r^{n+1}/(1-r)$. For each $k\geq1$, there are $(Q-1)Q^{k-1}$ other points whose highest nonzero tail coordinate is $n+k$. Each has distance $L^{n+k}$ from $x$, and hence weight $r^{n+k}/(1-r)$. Summing the geometric series gives</p>
<div class="math-display">$$\begin{aligned}
J_n^{\mathrm{per}}-J_n^{\mathrm{free}}
&amp;=\frac{r^n}{1-r}\left[r+(Q-1)\sum_{k\geq1}Q^{k-1}r^k\right]\\
&amp;=\frac{r^n}{1-r}\left[r+\frac{(Q-1)r}{1-Qr}\right]
=r^n\frac{q}{1-q}.
\end{aligned}$$</div>
<p>This proves convergence and (9). The extra constant kernel is an independent layer with edge probability $1-\exp[-\beta r^nq/(1-q)]$. Between current components of sizes $a,b$, its absent-edge probability is $\exp[-\beta r^nqab/(1-q)]$. It is therefore an additional coalescent time $\beta r^nq/(1-q)$ after the usual final time $\beta r^n$, proving the distributional assertion.</p>
:::
<p>The periodic block is the quotient $\mathbb H/T_n$ by the tail subgroup. Its final coalescent time is $At_n$, where $A=(1-q)^{-1}$, so asymptotics for periodic blocks require control of the coalescent beyond the interval $[0,t_n]$ used for the truncated block law.</p>

## History and attribution {#section-history}

<p>The decomposition of exact radial hierarchical percolation into independent complete-graph block layers, the description of each layer as a <a href="/articles/multiplicative-coalescent/">multiplicative coalescent</a> and the resulting moment recursion across scales are due to Hutchcroft (2022, section 1.1 and section 2, equations (2.2)–(2.7)), who used them to determine the critical cluster volumes in all three regimes. The uniform moment control combines the universal power-sum comparisons with the exact mean equation, as in his Corollary 3.7, Proposition 4.5 and Lemma 4.8, and the periodic kernel is from his section 7.1. Material on this page is also credited to T. Hutchcroft, book in preparation.</p>

## References {#section-references}

<ul><li>T. Hutchcroft, <a href="https://arxiv.org/abs/2211.05686v1">Critical cluster volumes in hierarchical percolation</a>, arXiv:2211.05686 (2022).</li><li>T. Hutchcroft, book in preparation.</li></ul>
