---
{
  "id": "multiplicative-coalescent",
  "title": "The finite multiplicative coalescent",
  "subtitle": "Blocks of a partition merge at a rate equal to the product of their sizes.",
  "kind": "model",
  "category": "Methods",
  "summary": "Independent edge clocks on a finite set give a Markov chain on partitions in which two blocks merge at rate the product of their sizes. Its generator gives exact equations for the expected power sums of the block sizes, and these moments determine the law of the block sizes.",
  "context": [
    "$\\Omega$ is a finite set of $N$ points, and the states of the process are partitions of $\\Omega$.",
    "$S_p(P)=\\sum_{A\\in P}|A|^p$ is the $p$th mass power sum of a partition $P$; $S_1=N$."
  ],
  "related": [
    "hierarchical-block-coalescent",
    "finite-random-graphs",
    "critical-random-graph-clusters",
    "finite-triangle-window",
    "hierarchical-runaway"
  ],
  "sourceIds": [
    "hutchcroft-hierarchical-volumes-2022",
    "aldous-critical-random-graphs"
  ],
  "aliases": [
    "multiplicative coalescent",
    "edge-clock coalescent",
    "coalescent moment equations",
    "mass power sums"
  ],
  "prototypeUses": []
}
---

<p>The <strong>finite multiplicative coalescent</strong> is the Markov process on partitions of a finite set in which any two blocks, of sizes $a$ and $b$, merge at rate $ab$. It is obtained by giving each pair of points an independent exponential clock and joining blocks along the pairs whose clocks have rung. Started from singletons, its state at time $t$ is the partition into components of the <a href="/articles/finite-random-graphs/">Erdős–Rényi random graph</a> with edge probability $1-e^{-t}$.</p>

<p>The generator acts simply on the power sums $S_p=\sum_A|A|^p$ of the block sizes. These carry the cluster-size information a probabilist needs: $S_2=\sum_{v\in\Omega}|K_v|$, where $K_v$ is the block containing $v$, so $\mathbb ES_2/N$ is the expected size of the block of a uniformly chosen point, the susceptibility of the random graph. For example $\frac{d}{dt}\mathbb E S_2=\mathbb E(S_2^2-S_4)$, and every mixed moment of $S_2,S_3,\ldots$ satisfies an explicit equation of the same kind. On a set of $N$ points the expectations of the products of $S_2,\ldots,S_N$ determine the law of the multiset of block sizes.</p>

<p>The process is the Marcus–Lushnikov stochastic coalescent (Marcus 1968; Lushnikov 1978) with multiplicative kernel, the finite-particle counterpart of Smoluchowski's coagulation equation, and started from singletons it is the classical edge-clock construction of the Erdős–Rényi random graph process. In <a href="/articles/hierarchical-block-coalescent/">exact hierarchical percolation</a> each block layer runs such a coalescent for a finite time, started from the clusters of the smaller blocks, and Hutchcroft (2022) used its moment identities as the starting point of his analysis of critical cluster volumes. The coalescent with infinitely many square-summable masses, introduced by Aldous (1997), is treated in <a href="/articles/finite-triangle-window/">the finite triangle window</a>.</p>

## Definitions and setting {#section-definitions}

<p>Let $\Omega$ be a finite set of $N$ points. A partition $P$ of $\Omega$ is a set of disjoint nonempty blocks with union $\Omega$; the size, or mass, of a block $A$ is its cardinality $|A|$. For distinct blocks $A,B\in P$, the partition obtained by merging them is $P^{A,B}=(P\setminus\{A,B\})\cup\{A\cup B\}$. The <strong>mass power sums</strong> of $P$ are $S_p(P)=\sum_{A\in P}|A|^p$ for $p\geq1$. Thus $S_1=N$ for every partition, and $S_2$ is the sum of the squared block sizes.</p>
<p>Let $P_0$ be a random partition of $\Omega$. Attach to each unordered pair of distinct points an independent rate-one exponential clock, independent of $P_0$, and let $X_t$ be the partition obtained from $P_0$ by joining blocks along the pairs whose clocks have rung by time $t$. The process $(X_t)_{t\geq0}$ is the <strong>finite multiplicative coalescent</strong> started from $P_0$. When $P_0$ is the partition into singletons, $X_t$ is the partition into components of independent <a href="/articles/product-model/">bond percolation</a> on the complete graph on $\Omega$ with edge probability $1-e^{-t}$.</p>

## The generator {#section-block-coalescent}

<a id="tag-Z960" data-assertion="proposition" data-title="The finite edge-clock coalescent and its generator"></a>
<p>Let $\Omega$ be a finite set of size $N$, with an initial partition $P_0$. Add independent rate-one edge clocks between its vertices, independently of $P_0$, and at time $t$ take the partition $X_t$ obtained by joining the initial blocks along edges whose clocks have rung. Each unordered pair of current blocks $\{A,B\}$ merges at rate $|A||B|$. For any function $F$ on the finite set of partitions,</p>
<div class="math-display">$$\frac{d}{dt}\mathbb E F(X_t)=\mathbb E[\mathcal L F(X_t)],\qquad
\mathcal L F(P)=\sum_{\{A,B\}\subset P}|A||B|\bigl[F(P^{A,B})-F(P)\bigr],$$</div>
<p>where the sum is over two distinct blocks without ordering, and $P^{A,B}=(P\setminus\{A,B\})\cup\{A\cup B\}$. Expectations are smooth in $t$, including right derivatives at zero, for every initial law independent of the clocks.</p>
<p><em>Idea of the proof.</em> By memorylessness, the $|A||B|$ unrung clocks joining two current blocks $A$ and $B$ ring first at rate $|A||B|$, and clocks inside a block change nothing.</p>
:::details Proof
<p>If $A$ and $B$ are distinct current blocks, none of their $|A||B|$ joining clocks has rung. Conditional on the clock history, their residual times are independent rate-one exponentials by memorylessness. Their minimum has rate $|A||B|$, so the chain leaves $P$ at rate $\lambda(P)=\sum_{\{A,B\}\subset P}|A||B|=\frac12\bigl(N^2-S_2(P)\bigr)$. All other rings either merge another pair or leave the partition unchanged. There are finitely many clocks, so the probability of two or more rings during an interval of length $\varepsilon$ is $O(\varepsilon^2)$, uniformly over states. This gives the generator and the Markov property. The transition matrix is the exponential of a finite matrix, which proves smoothness and the expectation identity, also after averaging over $P_0$.</p>
:::

## Moment equations {#section-coalescent-moments}

<a id="tag-22H8" data-assertion="theorem" data-title="Single and mixed cluster-mass moment equations"></a>
<p>For a partition $P$ of a finite set, put $S_p(P)=\sum_{A\in P}|A|^p$. Then $S_1=N$ is constant. For every integer $p\geq2$, the coalescent of Z960 satisfies</p>
<div class="math-display">$$\frac{d}{dt}\mathbb E S_p(X_t)
=\frac12\sum_{k=1}^{p-1}\binom pk\mathbb E\bigl[S_{k+1}(X_t)S_{p-k+1}(X_t)-S_{p+2}(X_t)\bigr].$$</div>
<p>In particular, writing the arguments $X_t$ implicitly,</p>
<div class="math-display">$$\frac{d}{dt}\mathbb E S_2=\mathbb E(S_2^2-S_4),\qquad
\frac{d}{dt}\mathbb E S_3=3\mathbb E(S_2S_3-S_5).$$</div>
<p>There is an explicit formula for every mixed moment. Let $p_1,\ldots,p_r\geq2$ be integers, with repeated indices permitted, and for $I\subseteq\{1,\ldots,r\}$ put $D_I=\sum_{i\in I}p_i$. Then</p>
<div class="math-display">$$\begin{aligned}
\mathcal L\!\left(\prod_{i=1}^r S_{p_i}\right)
={}&\frac12\sum_{\varnothing\ne I\subseteq\{1,\ldots,r\}}
\left(\prod_{i\notin I}S_{p_i}\right)
\sum_{\substack{1\leq k_i\leq p_i-1\\i\in I}}
\left(\prod_{i\in I}\binom{p_i}{k_i}\right)\\
&\hspace{12mm}\cdot\left[S_{1+\sum_{i\in I}k_i}\,
S_{1+D_I-\sum_{i\in I}k_i}-S_{2+D_I}\right].
\end{aligned}$$</div>
<p>Taking expectations gives the derivative of the mixed moment. If $S_p$ is assigned degree $p$, every term on the right has degree $2+\sum_i p_i$. The empty product has derivative zero.</p>
<p><em>Idea of the proof.</em> Merging blocks of masses $a$ and $b$ changes $S_p$ by $(a+b)^p-a^p-b^p$, a polynomial in $a$ and $b$. Multiplying by the merger rate $ab$ and summing over pairs of distinct blocks, written as a sum over all ordered pairs minus the diagonal, expresses $\mathcal L S_p$ through products of power sums. Products of several power sums are expanded in the same way.</p>
:::details Proof
<p>Merging masses $a,b$ changes $S_p$ by</p>
<div class="math-display">$$\Delta_p(a,b)=(a+b)^p-a^p-b^p
=\sum_{k=1}^{p-1}\binom pk a^k b^{p-k}.$$</div>
<p>Use the ordered-pair form of the generator, including its factor $1/2$. For a single factor, the term indexed by $k$ sums $a^{k+1}b^{p-k+1}$ over distinct blocks. Summing over all ordered pairs and subtracting the diagonal gives $S_{k+1}S_{p-k+1}-S_{p+2}$.</p>
<p>For several labelled factors, expand $\prod_i(S_{p_i}+\Delta_{p_i})-\prod_i S_{p_i}$ according to the nonempty set $I$ of factors from which an increment is chosen. Expand each increment by the binomial theorem and multiply by the merger rate $ab$. The two exponents of $a,b$ are $1+\sum_{i\in I}k_i$ and $1+D_I-\sum_{i\in I}k_i$. Subtracting the diagonal now gives the displayed bracket. The untouched factors supply the remaining degree. All sums are finite, so the expectations may be differentiated term by term.</p>
:::
<p>For a product of two power sums the generator has a merger correction:</p>
<div class="math-display">$$\mathcal L(S_pS_q)=S_p\mathcal L S_q+S_q\mathcal L S_p
+\sum_{\{A,B\}\subset P}|A||B|\Delta_p(|A|,|B|)\Delta_q(|A|,|B|).$$</div>
<p>In particular $\mathcal L(S_2^2)=2S_2(S_2^2-S_4)+2(S_3^2-S_6)$.</p>
<p>The equations for the means are not closed: the derivative of $\mathbb E S_2$ involves $\mathbb E S_2^2$ and $\mathbb E S_4$. If $S_2$ is concentrated and $\mathbb E S_4$ is small compared with $(\mathbb E S_2)^2$, the mean $\mu=\mathbb E S_2$ approximately solves $\mu'=\mu^2$. This is the equation for the second moment $\sum_kk^2n_k$ of a solution of Smoluchowski's coagulation equation with multiplicative kernel,</p>
<div class="math-display">$$\frac{d}{dt}n_k=\frac12\sum_{i+j=k}ij\,n_in_j-kn_k\sum_{j\geq1}jn_j\qquad(k\geq1),$$</div>
<p>where $n_k(t)$ is the density of blocks of mass $k$. Up to the gelation time $1/\mu(0)$ the first moment $\sum_kkn_k$ is conserved and the second moment solves $\mu'=\mu^2$; at that time the second moment blows up, and afterwards mass is lost to the gel. In <a href="/articles/hierarchical-block-coalescent/">exact hierarchical percolation</a> the relative error in the approximation is at most a constant times $M_n^2/\mu_n(t)$, where $M_n$ is a typical size of the largest cluster of a block of level $n$, so the approximation is justified when $\sup_tM_n^2/\mu_n(t)\to0$. This holds under the <a href="/articles/hierarchical-block-coalescent/#section-definitions">hydrodynamic condition</a> together with a lower bound on $\mu_n$ of its critical order, by the <a href="/tag/X2A4/">moment-control theorem</a>.</p>

## Variance and covariance equations {#section-norm-covariance-equations}

<a id="tag-C1BP" data-assertion="theorem" data-title="Exact coalescent equations for the variance of S2 and its covariance with S3"></a>
<p>For a finite multiplicative coalescent, write $f_j=\mathbb ES_j$, $\mu=f_2$, $\nu=f_3$, $V=\operatorname{Var}(S_2)$, $C=\operatorname{Cov}(S_2,S_3)$ and $\Delta_j=S_j-f_j$. Then</p>
<div class="math-display">$$\begin{aligned}
V'&amp;=4\mu V+2\nu^2+2\operatorname{Var}(S_3)+2\mathbb E\Delta_2^3
-2\operatorname{Cov}(S_2,S_4)-2f_6,\\
C'&amp;=5\mu C+3\nu V+6\nu f_4+4\mathbb E(\Delta_3\Delta_2^2)
-3\operatorname{Cov}(S_2,S_5)+5\operatorname{Cov}(S_3,S_4)-6f_7.
\end{aligned}$$</div>
<p><em>Idea of the proof.</em> The merger increments of $S_2$ and $S_3$ give the generator applied to $S_2^2$ and to $S_2S_3$, exactly as for the <a href="/tag/22H8/">moment equations</a>. Subtracting the derivatives of $\mu^2$ and $\mu\nu$ and writing the cubic terms through centred moments gives the two identities.</p>
:::details Proof
<p>A merger of blocks of sizes $a,b$ has rate $ab$ and increments $S_2$ by $2ab$ and $S_3$ by $3ab(a+b)$. Applying the finite generator and writing distinct-pair sums as products minus diagonals gives</p>
<div class="math-display">$$\begin{aligned}
\mathcal L S_2&amp;=S_2^2-S_4,&amp;\mathcal L S_3&amp;=3(S_2S_3-S_5),\\
\mathcal L(S_2^2)&amp;=2(S_2^3-S_2S_4+S_3^2-S_6),\\
\mathcal L(S_2S_3)&amp;=4S_2^2S_3-3S_2S_5+5S_3S_4-6S_7.
\end{aligned}$$</div>
<p>For example the product increment is $3ab(a+b)S_2+2abS_3+6a^2b^2(a+b)$; summation over unordered pairs gives the last formula. Differentiate $V=\mathbb ES_2^2-\mu^2$ and $C=\mathbb E(S_2S_3)-\mu\nu$, then use</p>
<div class="math-display">$$\mathbb ES_2^3=\mu^3+3\mu V+\mathbb E\Delta_2^3,\qquad
\mathbb E(S_2^2S_3)=\mu^2\nu+2\mu C+\nu V+\mathbb E(\Delta_3\Delta_2^2).$$</div>
<p>Collecting the remaining mixed products into covariances proves both identities, for every initial law independent of the clocks.</p>
:::

## Mass moments determine the size law {#section-size-determination}

<a id="tag-W8PB" data-assertion="proposition" data-title="Mixed mass moments determine the finite component-size law"></a>
<p>For a random partition of a fixed $N$-element set with $N\geq1$, the expectations of all products of $S_2,\ldots,S_N$ determine the law of its multiset of component sizes. They need not determine the labelled partition law.</p>
<p><em>Idea of the proof.</em> The power sums $S_p=\sum_a a^pc_a$ are linear in the numbers $c_a$ of blocks of each size $a$, with an invertible Vandermonde-type matrix, so $(S_2,\ldots,S_N)$ determines the size multiset. As there are finitely many multisets, the indicator of each one is a polynomial in $S_2,\ldots,S_N$, and its expectation is the probability of that multiset.</p>
:::details Proof
<p>Let $c_a$ be the number of blocks of size $a$, for $1\leq a\leq N$. Then $S_p=\sum_{a=1}^N a^p c_a$. The matrix $(a^p)_{1\leq p,a\leq N}$ is invertible: factor $a$ from column $a$ to leave the Vandermonde matrix on the distinct points $1,\ldots,N$. Since $S_1=N$ is fixed, the vector $(S_2,\ldots,S_N)$ distinguishes all possible block-size multisets.</p>
<p>There are finitely many such multisets. For a fixed one $\lambda$ and each other one $\mu$, choose $k(\mu)\in\{2,\ldots,N\}$ with $S_{k(\mu)}(\lambda)\ne S_{k(\mu)}(\mu)$. The polynomial</p>
<div class="math-display">$$I_\lambda(S)=\prod_{\mu\ne\lambda}
\frac{S_{k(\mu)}-S_{k(\mu)}(\mu)}
{S_{k(\mu)}(\lambda)-S_{k(\mu)}(\mu)}$$</div>
<p>is one at $\lambda$ and zero at every other possible multiset. Its expectation is therefore the probability of $\lambda$, determined by the mixed moments. For $N=1$ there is only one possible multiset.</p>
:::

## Examples {#section-examples}

<p><em>Two points.</em> If $N=2$ and $P_0$ consists of two singletons, the blocks merge at time $T$, an exponential variable of rate one. Before the merger $S_2=2$ and $S_4=2$; afterwards $S_2=4$ and $S_4=16$. Hence $\mathbb E S_2(X_t)=4-2e^{-t}$, and the <a href="/tag/22H8/">moment equation</a> $\frac{d}{dt}\mathbb E S_2=\mathbb E(S_2^2-S_4)=2\,\mathbb P(T&gt;t)=2e^{-t}$ agrees with it.</p>
<p><em>Erdős–Rényi graphs.</em> Started from singletons, $X_t$ is the component partition of the <a href="/articles/finite-random-graphs/">Erdős–Rényi graph</a> on $N$ vertices with edge probability $1-e^{-t}$. Since $S_2=\sum_{v\in\Omega}|K_v|$, where $K_v$ is the component of $v$, the moment equations give exact differential equations for $N$ times the expected size of the component of a uniformly chosen vertex. In the <a href="/articles/critical-random-graph-clusters/">critical window</a> $1-e^{-t}=(1+\lambda N^{-1/3})/N$, $\mathbb E S_2$ is of order $N^{4/3}$.</p>
<p><em>Labelled partitions are not determined.</em> On $\Omega=\{1,2,3\}$ the partitions $\{\{1,2\},\{3\}\}$ and $\{\{1,3\},\{2\}\}$ have the same power sums $S_p=2^p+1$. The point masses at these two partitions therefore have the same mixed moments, although they are different laws; the moments determine only the law of the size multiset.</p>

## Consequences and applications {#section-consequences}

<p>In <a href="/articles/hierarchical-block-coalescent/">exact block layers of hierarchical percolation</a>, the cluster partition of a block of level $n$ evolves within the level-$n$ layer as a finite multiplicative coalescent started from the terminal cluster partitions of its children. The <a href="/tag/22H8/">moment equations</a>, together with the <a href="/tag/54V4/">gluing of independent children</a> at the start of each layer, give exact equations for all moments at every scale. The critical analysis of block means, maxima and higher moments summarised in <a href="/articles/hierarchical-runaway/">the hierarchical runaway observable</a> is built on them, and the <a href="/tag/C1BP/">variance and covariance equations</a> give the <a href="/tag/LWRN/">leading variance and covariance constants</a> of the power sums under hydrodynamics. By the <a href="/tag/W8PB/">determination of the size law</a>, exact equations for all mixed moments describe the law of the cluster sizes at each scale.</p>

## Variants and generalisations {#section-variants}

<p>The clock construction also defines a Markov process for infinitely many blocks with square-summable masses, the multiplicative coalescent of Aldous. Its <a href="/tag/3G0K/">construction from independent edge clocks</a>, the <a href="/tag/7HLE/">continuity of its transition law</a> in time and initial masses, and the <a href="/tag/GRSC/">convergence of finite coalescents</a> to it in path space are proved in <a href="/articles/finite-triangle-window/">the finite triangle window</a>, where the standard multiplicative coalescent appears as the limit of <a href="/articles/critical-random-graph-clusters/">critical Erdős–Rényi</a> component sizes.</p>

## History and attribution {#section-history}

<p>Finite stochastic coalescents, in which two clusters of masses $a$ and $b$ merge at rate $K(a,b)$, go back to Marcus (1968) and Lushnikov (1978) and are called Marcus–Lushnikov processes. They are the finite-particle counterparts of the coagulation equation of Smoluchowski (1916); Aldous (1999) surveys both from a probabilistic point of view. With the multiplicative kernel $K(a,b)=ab$ and singleton initial state, the edge-clock construction gives the component process of the <a href="/articles/finite-random-graphs/">Erdős–Rényi random graph</a> (Erdős and Rényi 1960) in continuous time. Aldous (1997) introduced the multiplicative coalescent on square-summable mass sequences and identified the standard multiplicative coalescent as the scaling limit of the ranked component sizes of <a href="/articles/critical-random-graph-clusters/">critical Erdős–Rényi graphs</a>.</p>
<p>Hutchcroft (2022) used these identities in the analysis of hierarchical percolation: the finite generator and the single moment equations are in his section 2 (Lemma 2.3), the variance and covariance equations are his Lemma 6.9, and the determination of the size law by the mixed moments is in his discussion after equation (2.4).</p>

## References {#section-references}

<ul><li>D. Aldous, <a href="https://doi.org/10.1214/aop/1024404421">Brownian excursions, critical random graphs and the multiplicative coalescent</a>, Ann. Probab. 25 (1997), 812–854.</li><li>D. Aldous, Deterministic and stochastic models for coalescence (aggregation and coagulation): a review of the mean-field theory for probabilists, Bernoulli 5 (1999), 3–48.</li><li>P. Erdős and A. Rényi, On the evolution of random graphs, Publ. Math. Inst. Hung. Acad. Sci. 5 (1960), 17–61.</li><li>A. A. Lushnikov, Coagulation in finite systems, J. Colloid Interface Sci. 65 (1978), 276–285.</li><li>A. H. Marcus, Stochastic coalescence, Technometrics 10 (1968), 133–143.</li><li>M. von Smoluchowski, Drei Vorträge über Diffusion, Brownsche Molekularbewegung und Koagulation von Kolloidteilchen, Physik. Z. 17 (1916), 557–571 and 585–599.</li><li>T. Hutchcroft, <a href="https://arxiv.org/abs/2211.05686v1">Critical cluster volumes in hierarchical percolation</a>, arXiv:2211.05686 (2022).</li></ul>
