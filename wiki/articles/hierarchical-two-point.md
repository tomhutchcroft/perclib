---
{
  "id": "hierarchical-two-point",
  "title": "Critical two-point function on the hierarchical lattice",
  "subtitle": "At criticality, connection probabilities decay like the distance to the power −(d − α).",
  "kind": "theorem",
  "category": "Hierarchical percolation",
  "summary": "For long-range percolation on the hierarchical lattice with a symmetric kernel comparable to ‖x‖^(−d−α), 0 < α < d, critical connection probabilities averaged over the vertices at distance L^n are of order L^(−(d−α)n) (Hutchcroft, 2021). For radial kernels the bound holds for every pair of vertices.",
  "context": [
    "Integers $d\\ge1$ and $L\\ge2$ define the hierarchical lattice.",
    "The intensity kernel $J$ is nonnegative and symmetric, $J(x)=J(-x)$. It is radial, depending only on the hierarchical distance, only where a statement says so.",
    "Edges are independent, with probabilities $1-\\exp(-\\beta J(x-y))$ at intensity $\\beta\\ge0$."
  ],
  "related": [
    "hierarchical-lattice",
    "hierarchical-runaway",
    "hierarchical-comparison",
    "pointwise-long-range",
    "sharpness",
    "universal-tightness",
    "triangle-condition",
    "cutoff-families"
  ],
  "sourceIds": [
    "hutchcroft-hierarchical-2021",
    "hutchcroft-book"
  ],
  "aliases": [
    "hierarchical two-point function",
    "hierarchical long-range percolation",
    "critical two point"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "criticality",
    "susceptibility"
  ]
}
---

<p>On the <a href="/articles/hierarchical-lattice/">hierarchical lattice</a> $\mathbb H_L^d$, <a data-wanted="long-range-percolation">long-range percolation</a> with a kernel $J(x)$ comparable to $\|x\|^{-d-\alpha}$, $0&lt;\alpha&lt;d$, has a critical <a href="/tag/6WC8/">two-point function</a> of order $\|x-y\|^{-(d-\alpha)}$: at the <a href="/articles/criticality/">critical intensity</a> $\beta_c$, two vertices at distance $r$ are connected with probability between two constant multiples of $r^{-(d-\alpha)}$. The lower bound holds for connections inside the smallest ball containing both vertices. For a general symmetric kernel the estimate holds on average over the vertices at a given distance; for a radial kernel it holds for every pair. The theorem is due to Hutchcroft [@hutchcroft-hierarchical-2021].</p>

<p>The exponent $d-\alpha$ is the mean-field value, and the theorem gives it throughout $0&lt;\alpha&lt;d$. When $3\alpha&lt;d$ the pointwise bound implies the <a href="/articles/triangle-condition/">triangle condition</a> and hence <a href="/articles/critical-exponents/">mean-field behaviour</a>; when $3\alpha&gt;d$ the triangle condition fails, and the tail exponent of the critical cluster volume, if it exists, differs from its mean-field value, yet the two-point exponent is unchanged. On $\mathbb Z^d$ only partial analogues are known: an <a href="/articles/hierarchical-comparison/">averaged upper bound at criticality</a> and <a href="/articles/pointwise-long-range/">pointwise bounds for $\alpha&lt;1$</a>. The hierarchical lattice, whose balls are nested subgroups, is a model on which statements of this kind can be proved also in the regime $3\alpha&gt;d$.</p>

<p>The proof combines the <a href="/articles/hierarchical-runaway/">runaway observable</a>, which uses amplification of large clusters in balls and <a href="/articles/sharpness/">sharpness</a> to fix the critical size of clusters in each ball, with the critical boundary flux, which bounds the expected cluster size in a ball below, and a recursion between sibling balls, which bounds it above; these bounds are then converted into bounds on connection probabilities. In volume form, the critical <a href="/articles/susceptibility/">susceptibility</a> of a ball of radius $L^n$ grows like $L^{\alpha n}$.</p>

## Definitions and setting {#section-model}

<p><em>Main article: <a href="/articles/hierarchical-lattice/">The hierarchical lattice and radial kernels</a>.</em></p>
<a id="tag-XMYD" data-assertion="definition" data-title="Hierarchical lattice"></a><p>The vertex group is</p>
      $$\mathbb H_L^d=\bigoplus_{i\ge1}(\mathbb Z/L\mathbb Z)^d.$$
      <a id="tag-T6SL" data-assertion="definition" data-title="Hierarchical distance and ball volume"></a><p>Vertices are sequences with only finitely many nonzero coordinates. For $x\ne y$, their distance is $L^{\max\{i:x_i\ne y_i\}}$, and the distance from a vertex to itself is zero. A radius-$L^n$ ball contains $L^{dn}$ vertices.</p>
      <a id="tag-JCRB" data-assertion="definition" data-title="Smallest common hierarchical ball and regularized distance"></a><p>For vertices $x,y$, let $\Lambda(x,y)$ be the smallest hierarchical ball containing them, and put $\langle x-y\rangle=\max\{1,\|x-y\|\}$. A radial kernel depends only on this distance.</p>
<p>Here $\|x\|$ is the distance from $x$ to $0$, so that the distance between $x$ and $y$ is $\|x-y\|$. For $n\ge0$ let $\Lambda_n$ be the subgroup of sequences supported on the first $n$ coordinates. The closed ball of radius $L^n$ about $x$ is the coset $x+\Lambda_n$, which is why it has $|\Lambda_n|=L^{dn}$ vertices. The distance satisfies the ultrametric inequality $\|x-z\|\le\max\{\|x-y\|,\|y-z\|\}$, so two balls are disjoint or nested, and $\Lambda(x,y)=x+\Lambda_n$ when $\|x-y\|=L^n$. The shell $\Lambda_n\setminus\Lambda_{n-1}$ of vertices at distance exactly $L^n$ from $0$ has $(1-L^{-d})L^{dn}$ points, by the <a href="/tag/9408/">exact shell counts</a>.</p>
<p>The ball $x+\Lambda_n$ is also called the level-$n$ <em>block</em> of $x$ (written $B_n$ when $x=0$), and a vertex at distance $L^j$ from $0$ has level $j$, so two vertices at distance $L^j$ first share a block at level $j$.</p>
<p><em>The model.</em> Fix integers $d\ge1$ and $L\ge2$ and a kernel $J:\mathbb H_L^d\to[0,\infty)$ that is symmetric, $J(x)=J(-x)$. At intensity $\beta\ge0$, <a data-wanted="long-range-percolation">long-range percolation</a> on $\mathbb H_L^d$ declares each pair $\{x,y\}$ of distinct vertices an open edge, independently, with probability</p>
$$1-e^{-\beta J(x-y)}.$$
<p>This is the <a href="/tag/A65C/">exponential intensity family</a> of <a href="/articles/product-model/">product percolation</a>; $\mathbb P_\beta$ and $\mathbb E_\beta$ denote its law and expectation. The edge probabilities depend only on $x-y$, so translations of $\mathbb H_L^d$ preserve $\mathbb P_\beta$. A radial kernel is symmetric, since $\|-x\|=\|x\|$.</p>
<p><em>Clusters and connections.</em> The <a href="/tag/6WC8/">cluster</a> $K_x$ of $x$ is the set of vertices joined to $x$ by an open path, and $\tau_\beta(x,y)=\mathbb P_\beta(x\leftrightarrow y)$ is the two-point function. For $\Lambda\subseteq\mathbb H_L^d$, $x\xleftrightarrow{\Lambda}y$ (in the statements, "$x\leftrightarrow y$ inside $\Lambda$") is the event that an open path from $x$ to $y$ uses only edges with both endpoints in $\Lambda$; its probability is $\tau^\Lambda_\beta(x,y)$. The <a href="/tag/OG96/">restricted cluster</a> $K^\Lambda_x$ is the set of $y$ with $x\xleftrightarrow{\Lambda}y$. It is contained in $K_x\cap\Lambda$ and can be strictly smaller.</p>
<p><em>The critical intensity.</em> The <a href="/tag/8DAH/">critical intensity</a> is $\beta_c=\inf\{\beta\ge0:\mathbb P_\beta(|K_0|=\infty)&gt;0\}$; by transitivity the root does not matter. When $J$ is summable, <a href="/tag/L0TE/">sharpness for transitive summable intensities</a> shows that the <a href="/articles/susceptibility/">susceptibility</a> $\chi(\beta)=\mathbb E_\beta|K_0|$ is finite for every $\beta&lt;\beta_c$, so $\beta_c$ is also the threshold for finite susceptibility.</p>

## Statement {#section-statement}

<p>Both results concern the model of the <a href="#section-model">setting</a> at its critical intensity. The first, Hutchcroft's main theorem, averages connection probabilities over a shell; the second is its pointwise form for <a href="/articles/hierarchical-lattice/">radial kernels</a>.</p>
<a id="tag-J98J" data-assertion="theorem" data-title="Critical averaged two-point estimate"></a><div class="theorem-statement"><p>Let $0&lt;\alpha&lt;d$, let $J$ be symmetric and integrable, and suppose that there are constants $c,C&gt;0$ such that</p>
      $$c\|x\|^{-d-\alpha}\le J(x)\le C\|x\|^{-d-\alpha}
      \qquad(x\ne0).$$
      <p>For $n\ge0$ let $\Lambda_n=\{x:\|x\|\le L^n\}$ be the hierarchical ball of radius $L^n$ about the origin, so that $|\Lambda_n|=L^{dn}$. Then the <a href="/articles/criticality/">critical intensity</a> satisfies $\beta_c&lt;\infty$, and there are constants $a,A&gt;0$, depending only on $d,L,\alpha,c,C$, such that, for every $n\ge1$,</p>
      $$aL^{-(d-\alpha)n}
      \le \frac1{|\Lambda_n|}\sum_{x\in\Lambda_n\setminus\Lambda_{n-1}}\mathbb P_{\beta_c}\bigl(0\leftrightarrow x\text{ inside }\Lambda_n\bigr)
      \le \frac1{|\Lambda_n|}\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)
      \le AL^{-(d-\alpha)n}.$$</div>
<a id="tag-W498" data-assertion="theorem" data-title="Critical pointwise two-point estimate for radial kernels"></a><div class="theorem-statement"><p>Let $0&lt;\alpha&lt;d$, let $J$ be radial, and suppose that there are constants $c,C&gt;0$ such that</p>
      $$c\|x\|^{-d-\alpha}\le J(x)\le C\|x\|^{-d-\alpha}
      \qquad(x\ne0).$$
      <p>Then the <a href="/articles/criticality/">critical intensity</a> satisfies $0&lt;\beta_c&lt;\infty$, and there are constants $a,A&gt;0$, depending only on $d,L,\alpha,c,C$, such that, for every $x,y\in\mathbb H_L^d$,</p>
      $$a\langle x-y\rangle^{-d+\alpha}
      \le \mathbb P_{\beta_c}\bigl(x\leftrightarrow y\text{ inside }\Lambda(x,y)\bigr)
      \le \mathbb P_{\beta_c}(x\leftrightarrow y)
      \le A\langle x-y\rangle^{-d+\alpha}.$$</div>
<p>In words: the probability that the origin is connected to a vertex at distance $L^n$, averaged over all such vertices, is of order $L^{-(d-\alpha)n}$, and for a radial kernel every such vertex has a connection probability of this order. The lower bounds are for connections inside the smallest common ball, the upper bounds for unrestricted connections, so confining paths to $\Lambda(x,y)$ changes the probability by at most a constant factor. The shell sum in the averaged estimate is divided by $|\Lambda_n|$, not by the size of the shell; since the shell has $(1-L^{-d})|\Lambda_n|$ points, this differs from the shell average only by that factor.</p>
<p>Since $\alpha&gt;0$, the upper envelope is summable; this gives the integrability of $J$ and the bound $\beta_c\ge1/\sum_{x\ne0}J(x)&gt;0$. The lower envelope supplies edges between large clusters in neighbouring balls: it drives the amplification that gives $\beta_c&lt;\infty$, the recursion between sibling balls and the lower bound on connection probabilities. The upper envelope bounds the expected number of edges leaving a ball, which at criticality forces expected cluster sizes in balls to be large, and it controls the sum over long edges in the upper bound. The condition $\alpha&lt;d$ makes amplification possible and makes the sum $\sum_mL^{-(d-\alpha)m}$ over scales converge.</p>

## Examples and non-examples {#section-examples}

<p><em>The power kernel.</em> $J(x)=\|x\|^{-d-\alpha}$ for $x\ne0$ (and any value at $0$) is radial, with $c=C=1$, so both estimates apply for every $0&lt;\alpha&lt;d$. So does the kernel $J(x)=\sum_{m\ge h}L^{-(d+\alpha)m}=\|x\|^{-d-\alpha}/(1-L^{-(d+\alpha)})$, $\|x\|=L^h$, of the <a href="/tag/VI3Y/">independent complete-block layers</a>, with $c=1$ and $C=(1-L^{-(d+\alpha)})^{-1}$.</p>
<p><em>A symmetric kernel that is not radial.</em> Let $J(x)=\bigl(1+\tfrac12\mathbf 1_{\{x_1=0\}}\bigr)\|x\|^{-d-\alpha}$ for $x\ne0$. Since $(-x)_1=0$ exactly when $x_1=0$, it is symmetric, and it lies in the envelope with $c=1$, $C=\tfrac32$. It is not radial: for $n\ge2$ the shell at distance $L^n$ contains vertices with $x_1=0$ and with $x_1\ne0$. The averaged estimate applies; the pointwise estimate as stated does not (see <a href="#section-position">Variants</a>).</p>
<p><em>$\alpha\le0$.</em> The lower envelope then forces $\sum_{x\ne0}J(x)\ge c\sum_{j\ge1}(1-L^{-d})L^{-\alpha j}=\infty$, the divergent case of the <a href="/tag/YW7B/">power-kernel summability criterion</a>. For <a href="/tag/K38T/">nonsummable intensities</a> every vertex has infinitely many open edges almost surely at every $\beta&gt;0$, so $\beta_c=0$; at $\beta=0$ there are no edges, $\mathbb P_0(0\leftrightarrow x)=0$ for $x\ne0$, and the lower bounds of both estimates fail.</p>
<p><em>$\alpha\ge d$.</em> For the power kernel, $\beta_c&lt;\infty$ holds if and only if $\alpha&lt;d$ (Koval, Meester and Trapman; Dawson and Gorostiza). For $\alpha\ge d$ the model never percolates, and the condition $\alpha&lt;d$ in the theorem cannot be dropped.</p>

## Idea of the proof {#section-idea}

<p>Write $R_n(\beta)$ for the typical size of the largest cluster of a ball of radius $L^n$ formed by edges inside the ball (the smallest $m$ with $\mathbb P_\beta(\text{largest such cluster}\ge m)\le e^{-1}$), and $a_n=\mathbb E_{\beta}|K^{\Lambda_n}_0|$ for the expected size of the restricted cluster of the origin.</p>
<p><a href="/tag/7AER/">Block-quantile amplification</a> and <a href="/articles/sharpness/">sharpness</a> show that <a href="/tag/FF30/">$\beta_c$ is finite and $R_n(\beta_c)^2\lesssim L^{(d+\alpha)n}$</a>. Sharpness also gives the critical boundary flux: at $\beta_c$ the expected total intensity $\beta_cJ$ of the edges leaving $\Lambda_n$ from the restricted cluster of the origin is at least $1$, and since each vertex of $\Lambda_n$ sends out intensity of order $L^{-\alpha n}$, this forces $a_n\gtrsim L^{\alpha n}$. Since $a_n\le L^{dn}$, the <a href="/tag/655W/">sibling recursion</a> $a_{n+1}\gtrsim L^{-\alpha n}a_n^2$ forces $a_n\lesssim L^{\alpha n}$. Finally <a href="/tag/7YNX/">block means become pointwise bounds</a>: two vertices at distance $L^n$ lie in different sub-balls of $\Lambda_n$, an edge between their independent sub-ball clusters gives the lower bound, and the <a href="/articles/bk-inequality/">BK inequality</a>, applied according to the smallest ball containing an <a href="/articles/connectivity/">open path</a>, gives the upper bound, with terms summable over scales because $\alpha&lt;d$.</p>

## Proof {#section-proof}

::::details Proof of the averaged estimate
<p><em>Outline.</em> Steps 2 to 5 rest on results of the <a href="/articles/hierarchical-runaway/">runaway observable article</a>, which work as follows. In <a href="/tag/7AER/">block-quantile amplification</a>, if $R_n(\beta)^2$ exceeds a large multiple of $L^{(d+\alpha)n}/\beta$, many of the $L^{d\ell}$ sub-balls of a ball $\ell$ levels higher contain large clusters, with probability at least $1/2$ these are all joined by direct edges, and the excess propagates to every larger scale. Below $\beta_c$ the <a href="/articles/susceptibility/">susceptibility</a> is finite and $R_n$ grows only linearly in $n$, so amplification cannot start; since $R_0=2$, it starts at scale $0$ once $\beta$ is large enough, and therefore $\beta_c&lt;\infty$. In the <a href="/tag/655W/">sibling recursion</a>, the restricted cluster of the origin in $\Lambda_n$ and the restricted cluster of a vertex $w$ of a sibling ball are independent, and they are joined by a direct edge with probability of order $\beta L^{-(d+\alpha)n}$ times the product of their sizes, provided that this product is at most of order $L^{(d+\alpha)n}/\beta$; summing over the $L^{dn}$ vertices $w$ of the sibling ball, whose clusters have expected size $a_n$, gives $a_{n+1}\gtrsim L^{-\alpha n}a_n^2$. <a href="/tag/12NL/">Rooted damping</a> shows that clusters of size at most a constant multiple of $R_n$ carry at least half of each mean, and for them the quantile bound $R_n(\beta_c)^2\lesssim L^{(d+\alpha)n}$ keeps the product of sizes in this range, where the joining probability is comparable to it.</p>
<p>Throughout, $J$ satisfies the hypotheses of the averaged estimate. At level $j$, that is for $\|u-v\|=L^j$, the envelope reads $cL^{-(d+\alpha)j}\le J(u-v)\le CL^{-(d+\alpha)j}$, which is the form used by the results of the <a href="/articles/hierarchical-runaway/">runaway observable article</a>.</p>
<p><em>Step 1 (row sum).</em> There are $(1-L^{-d})L^{dj}$ vertices at distance $L^j$ from the origin, so the upper bound on $J$ gives the finite <a href="/articles/subcritical-bound/">row sum</a></p>
$$B=\sum_{x\ne0}J(x)\le CK,\qquad K=\frac{(1-L^{-d})L^{-\alpha}}{1-L^{-\alpha}}.$$
<p>The same computation shows that for every $u\in\Lambda_n$, since every vertex outside $\Lambda_n$ is at distance at least $L^{n+1}$ from $u$,</p>
$$\sum_{v\notin\Lambda_n}J(u-v)\le CKL^{-\alpha n}.$$
<p><em>Step 2 (finite critical intensity, quantile bound and boundary flux).</em> The kernel is <a href="/articles/displacement-kernels/">translation invariant</a> and symmetric, its row sum is finite, and it satisfies the lower bound of <a href="/tag/7AER/">block-quantile amplification</a>, whose constant $A_0$ depends only on $c,d,L,\alpha$. Hence the <a href="/tag/FF30/">finite critical intensity and boundary-flux theorem</a> gives</p>
$$\frac1{CK}\le\frac1B\le\beta_c\le\frac{A_0}4&lt;\infty,\qquad R_n(\beta_c)^2\le\frac{A_0}{\beta_c}L^{(d+\alpha)n}\quad(n\ge0),$$
<p>in particular the first assertion of the averaged estimate, $\beta_c&lt;\infty$. For every finite $T\ni0$ it also gives $\beta_c\sum_{u\in T}\tau^T_{\beta_c}(0,u)\sum_{v\notin T}J(u-v)\ge1$, in particular for $T=\Lambda_n$. Since $J$ is summable and the model is transitive, <a href="/tag/L0TE/">sharpness</a> gives $\chi(\beta)&lt;\infty$ for every $0&lt;\beta&lt;\beta_c$.</p>
<p><em>Step 3 (rooted damping in each ball).</em> Fix $n$ and regard $\Lambda_n$, with the edges between its vertices, as a finite graph carrying independent <a href="/articles/product-model/">bond percolation</a>; then clusters in this graph are the restricted clusters $K^{\Lambda_n}_x$. Apply the <a href="/tag/12NL/">witness-splitting tail bound</a> with observation set $\Lambda_n$: with $X_x=|K^{\Lambda_n}_x|$, $Z=\max_{x\in\Lambda_n}X_x$ and $M=R_n(\beta_c)$, so that $\mathbb P(Z\ge M)\le e^{-1}$, it gives $\mathbb P(X_x\ge3^kM)\le\mathbb P(X_x\ge M)\,e^{-3^{k-1}}$ for $k\ge1$. For real $\lambda\ge1$ choose $k\ge0$ with $3^k\le\lambda&lt;3^{k+1}$. If $k=0$, then $\mathbb P(X_x\ge\lambda M)\le\mathbb P(X_x\ge M)\le e^{1-\lambda/9}\mathbb P(X_x\ge M)$ because $\lambda&lt;9$. If $k\ge1$, then $3^{k-1}&gt;\lambda/9$ and $\mathbb P(X_x\ge\lambda M)\le\mathbb P(X_x\ge3^kM)\le e^{-\lambda/9}\mathbb P(X_x\ge M)$. In both cases</p>
$$\mathbb P_{\beta_c}(|K^{\Lambda_n}_x|\ge\lambda R_n)\le e^{1-\lambda/9}\,\mathbb P_{\beta_c}(|K^{\Lambda_n}_x|\ge R_n)\qquad(x\in\Lambda_n,\ \lambda\ge1),$$
<p>which is the rooted damping hypothesis of the sibling recursion, at $b=\beta_c$.</p>
<p><em>Step 4 (expected cluster sizes in balls).</em> By Steps 2 and 3, the <a href="/tag/655W/">sibling-block recursion</a> applies with endpoints $0$ and $b=\beta_c$. Its proof chooses a fixed $t\ge1$ with $(t+9)e^{1-t/9}\le\tfrac12$, puts $T=cA_0t^2L^{-(d+\alpha)}$, which does not involve $b$, and gives</p>
$$a_n=\mathbb E_{\beta_c}|K^{\Lambda_n}_0|\le C'L^{\alpha n}\quad(n\ge0),\qquad C'=\frac{4e^TL^{d+2\alpha}}{\beta_cc}.$$
<p><em>Step 5 (pointwise bounds on each shell).</em> The <a href="/tag/7YNX/">conversion from block means to pointwise bounds</a> applies at $b=\beta_c$ with $C_0=C$: its hypotheses are those of Step 4, the upper envelope and the boundary-flux inequalities of Step 2 for $T=\Lambda_n$. For $n\ge1$ and $x\in\Lambda_n\setminus\Lambda_{n-1}$ it gives</p>
$$c_1L^{-(d-\alpha)n}\le\tau^{\Lambda_n}_{\beta_c}(0,x)\le\tau_{\beta_c}(0,x)\le C_1L^{-(d-\alpha)n}.$$
<p>Its proof gives the values $c_1=ce^{-T}L^{-2\alpha}/(4\beta_cD^2)$ and $C_1=\beta_cC(C')^2/(1-L^{-(d-\alpha)})$, where $D=C(1-L^{-d})L^{-\alpha}/(1-L^{-\alpha})=CK$ is the bound on the outgoing row of Step 1.</p>
<p><em>Step 6 (uniformity of the constants).</em> The kernel enters $c_1$ and $C_1$ beyond $c$ and $C$ only through $\beta_c$. Since $\beta_c\le A_0/4$,</p>
$$c_1\ge\frac{ce^{-T}L^{-2\alpha}}{A_0C^2K^2},$$
<p>and since $C_1=16Ce^{2T}L^{2d+4\alpha}/\bigl(\beta_cc^2(1-L^{-(d-\alpha)})\bigr)$ and $1/\beta_c\le CK$,</p>
$$C_1\le\frac{16C^2Ke^{2T}L^{2d+4\alpha}}{c^2(1-L^{-(d-\alpha)})}.$$
<p>The right-hand sides depend only on $d,L,\alpha,c,C$, because $A_0$, $T$ and $K$ do; replace $c_1$ and $C_1$ by them.</p>
<p><em>Step 7 (summing over shells).</em> Summing the lower bound over the $(1-L^{-d})L^{dn}$ points of the shell gives the first inequality with $a=(1-L^{-d})c_1$. The middle inequality holds because a connection inside $\Lambda_n$ is a connection, and the shell is part of the ball. For the last, the origin contributes $1$ and the shell at distance $L^k$ contributes at most $L^{dk}\cdot C_1L^{-(d-\alpha)k}=C_1L^{\alpha k}$, so</p>
$$\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)\le1+C_1\sum_{k=1}^nL^{\alpha k}\le\Bigl(1+\frac{C_1}{1-L^{-\alpha}}\Bigr)L^{\alpha n}.$$
<p>Dividing by $|\Lambda_n|=L^{dn}$ gives the upper bound with $A=1+C_1/(1-L^{-\alpha})$.</p>
::::

::::details Proof of the pointwise estimate
<p>A <a href="/articles/hierarchical-lattice/">radial kernel</a> is symmetric, since $\|-x\|=\|x\|$, and the upper envelope makes it integrable because $\alpha&gt;0$; so the hypotheses of the averaged estimate hold, and Steps 1 to 6 of its proof apply. Positivity of $\beta_c$ is the bound $\beta_c\ge1/(CK)&gt;0$ of Step 2, and $\beta_c&lt;\infty$ by the same step.</p>
<p>Let $x\ne y$ and $\|x-y\|=L^n$ with $n\ge1$, so $\langle x-y\rangle=L^n$. Translation by $-x$ preserves $\mathbb P_{\beta_c}$, maps the pair to $(0,y-x)$ with $y-x\in\Lambda_n\setminus\Lambda_{n-1}$, and maps $\Lambda(x,y)=x+\Lambda_n$ to $\Lambda_n$. Hence</p>
$$\tau^{\Lambda(x,y)}_{\beta_c}(x,y)=\tau^{\Lambda_n}_{\beta_c}(0,y-x),\qquad \tau_{\beta_c}(x,y)=\tau_{\beta_c}(0,y-x),$$
<p>and the shell bounds of Step 5, with the constants of Step 6, give the claim with $a=c_1$ and $A=C_1$. The inner inequality holds because a connection inside $\Lambda(x,y)$ is a connection. If $x=y$, both probabilities equal $1$ and $\langle0\rangle=1$; replacing $a$ by $\min\{c_1,1\}$ and $A$ by $\max\{C_1,1\}$, which still depend only on $d,L,\alpha,c,C$, covers this case.</p>
::::

## Consequences and applications {#section-consequence}

<a id="tag-V4QQ" data-assertion="corollary" data-title="Full-cluster susceptibility in a hierarchical ball"></a><p>The critical estimate immediately determines the <a href="/articles/susceptibility/">finite-region susceptibility</a>, namely the expected mass of the full cluster inside a ball. For $n\ge1$, multiplying the chain of inequalities in <a href="/tag/J98J/">the averaged estimate</a> by $|\Lambda_n|=L^{dn}$ gives both bounds for every symmetric kernel in that theorem; for $n=0$ the sum is $1$. For a radial kernel the pointwise estimate gives the same order shell by shell: the shell at distance $L^k$ contains $L^{dk}-L^{d(k-1)}$ vertices, and multiplying by a connection probability of order $L^{-k(d-\alpha)}$ gives a shell contribution of order $L^{\alpha k}$. Summing the geometric series yields</p>
      $$\mathbb E_{\beta_c}|K_0\cap\Lambda_n|
        =\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)
        \asymp L^{\alpha n}.$$
      <a id="tag-YWTU" data-assertion="corollary" data-title="Restricted-cluster susceptibility in a hierarchical ball"></a><p>The restricted lower estimate, the first inequality of <a href="/tag/J98J/">the averaged estimate</a>, also gives the same order for the cluster formed using only edges inside $\Lambda_n$; the upper bound holds because that cluster is contained in the full cluster. These are distinct observables with matching orders in this theorem.</p>
:::details Proof of the two volume estimates
<p>Let $a,A$ be the constants of the averaged estimate and put $a'=\min\{a,1\}$, $A'=\max\{A,1\}$. For $n=0$, $\Lambda_0=\{0\}$ and both volumes equal $1=L^0$. Let $n\ge1$. Multiplying the averaged estimate by $|\Lambda_n|=L^{dn}$ gives</p>
$$aL^{\alpha n}\le\sum_{x\in\Lambda_n\setminus\Lambda_{n-1}}\mathbb P_{\beta_c}\bigl(0\xleftrightarrow{\Lambda_n}x\bigr)\le\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)\le AL^{\alpha n}.$$
<p>The ball sum in the middle is the <a href="/tag/BX1L/">intersection susceptibility</a> $\mathbb E_{\beta_c}|K_0\cap\Lambda_n|$, so $aL^{\alpha n}\le\mathbb E_{\beta_c}|K_0\cap\Lambda_n|\le AL^{\alpha n}$. For the restricted cluster, $\mathbb E_{\beta_c}|K^{\Lambda_n}_0|=\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\xleftrightarrow{\Lambda_n}x)$ is at least the shell sum on the left, hence at least $aL^{\alpha n}$; and $K^{\Lambda_n}_0\subseteq K_0\cap\Lambda_n$ (<a href="/tag/HQ6X/">restricted clusters lie in full-cluster intersections</a>), so it is at most $AL^{\alpha n}$. With $a',A'$ both estimates hold for all $n\ge0$, with constants depending only on $d,L,\alpha,c,C$.</p>
:::
<p><em>The triangle diagram.</em> For a <a href="/articles/hierarchical-lattice/">radial kernel</a>, the pointwise estimate shows that $f(x)=\tau_{\beta_c}(0,x)$ satisfies $a\langle x\rangle^{-(d-\alpha)}\le f(x)\le A\langle x\rangle^{-(d-\alpha)}$, and $\tau_{\beta_c}(x,y)=f(y-x)$ by translation invariance. The <a href="/tag/MS6M/">triangle diagram across scales</a> then shows that the critical <a href="/tag/67VP/">triangle diagram</a> $\sum_{x,y}\tau_{\beta_c}(0,x)\tau_{\beta_c}(x,y)\tau_{\beta_c}(y,0)$ is finite exactly when $3\alpha&lt;d$. For $3\alpha&lt;d$ the <a href="/tag/7UDJ/">triangle condition</a> therefore holds; Hutchcroft deduces from it <a href="/articles/critical-exponents/">mean-field behaviour</a> of the volume tail, the susceptibility and the percolation probability. For $3\alpha=d$ the diagram restricted to $\Lambda_N$ grows linearly in $N$, logarithmically in the radius $L^N$.</p>
<p><em>The volume exponent.</em> For $3\alpha&gt;d$ the <a href="/tag/7GDE/">volume-exponent obstruction</a> shows that if the tail of the critical cluster volume has an <a href="/tag/U5MC/">exponent</a> $\delta$, $\mathbb P_{\beta_c}(|K_0|\ge n)=n^{-1/\delta+o(1)}$, then $\delta\ge(d+\alpha)/(d-\alpha)$, which exceeds the mean-field value $2$.</p>
<p><em>Tail and density bounds.</em> Together with the critical boundary flux, the pointwise estimate is the input of the <a href="/tag/WPAD/">tail and density upper bounds near the triangle threshold</a>, valid for $0&lt;\alpha&lt;4d/11$.</p>

## Variants and generalisations {#section-position}

<p><em>Pointwise bounds without radial symmetry.</em> The proof of the pointwise estimate given above uses radial symmetry only to deduce that $J$ is symmetric. For every symmetric kernel satisfying the two-sided envelope with $0&lt;\alpha&lt;d$, the same argument (Step 5 of the averaged proof, then translation) gives the conclusion of the pointwise estimate for every pair $x,y$, with constants depending only on $d,L,\alpha,c,C$. The symmetric non-radial kernel of the <a href="#section-examples">examples</a> is covered in this way.</p>
<p><em>Dimension.</em> A bijection between $(\mathbb Z/L\mathbb Z)^d$ and $\mathbb Z/L^d\mathbb Z$ fixing $0$, applied in every coordinate, gives a bijection $\mathbb H_L^d\to\mathbb H_{L^d}^1$ that raises distances to the power $d$, since it preserves the last coordinate in which two vertices differ. Since the edge law depends only on distances when $J$ is <a href="/articles/hierarchical-lattice/">radial</a>, the power kernel $\|x\|^{-d-\alpha}$ on $\mathbb H_L^d$ corresponds to $\|x\|^{-1-\alpha/d}$ on $\mathbb H^1_{L^d}$. Up to this change of parameters the dimension plays no role, and the hierarchical model is closer to long-range percolation on $\mathbb Z$ than on $\mathbb Z^d$.</p>
<p><em>Euclidean long-range percolation.</em> On $\mathbb Z^d$ the corresponding sharp statements are known only in part. For kernels bounded below by $c\|x\|^{-d-\alpha}$, <a href="/tag/MRZO/">hierarchical comparison</a> gives the averaged upper bound $\sum_{\|z\|_\infty\le r}\mathbb P_\beta(0\leftrightarrow z)\le Cr^\alpha/(c\beta)$ for $\beta\le\beta_c$. For two-sided power kernels with $\alpha&lt;1$, the <a href="/tag/TGF9/">critical pointwise upper bound</a> and the <a href="/tag/TQ77/">matching pointwise lower bound</a> give $\tau_{\beta_c}(0,x)\asymp\|x\|^{-d+\alpha}$.</p>

## History and attribution {#section-history}

<p><a href="/articles/hierarchical-lattice/">Hierarchical lattices</a> were introduced by Dyson (1969) to study the Ising model, and have since been used throughout statistical mechanics as models in which the renormalisation group can be carried out exactly; Bauerschmidt, Brydges and Slade (2019) give background. For long-range percolation on $\mathbb H_L^d$ with the power kernel, Koval, Meester and Trapman (2012) and Dawson and Gorostiza (2013) proved independently that $\beta_c&lt;\infty$ if and only if $\alpha&lt;d$, and Koval, Meester and Trapman proved that there is no infinite cluster at $\beta_c$.</p>
<p>The averaged estimate is Theorem 1.1 and the pointwise estimate is Corollary 1.2 of Hutchcroft [@hutchcroft-hierarchical-2021]. There the pointwise form is derived from the averaged one by symmetry: for a radial kernel, any two pairs of vertices at the same distance are exchanged by an isometry that preserves the law (<a href="/articles/hierarchical-lattice/#section-level-isometries">level isometries of the hierarchical lattice</a>), so both connection probabilities from the origin are constant on each shell, and the shell averages bound them pointwise with constants changed by at most $(1-L^{-d})^{-1}$. The proof given in this article follows the structure of Hutchcroft's argument (block quantiles, sharpness, the sibling recursion and a BK decomposition) but derives the pointwise bounds directly from the block means. The triangle consequence for $3\alpha&lt;d$ is Corollary 1.4 and the volume-exponent bound is Corollary 1.5 of the same paper, where the value $\delta=(d+\alpha)/(d-\alpha)$ for $d/3&lt;\alpha&lt;d$ is conjectured. The volume estimates of the consequences restate Theorem 1.1.</p>

## References {#section-references}

<ul>
<li>R. Bauerschmidt, D. C. Brydges and G. Slade, <em>Introduction to a Renormalisation Group Method</em>, Lecture Notes in Mathematics 2242, Springer, 2019.</li>
<li>D. A. Dawson and L. G. Gorostiza, Percolation in an ultrametric space, <em>Electron. J. Probab.</em> 18 (2013), no. 12.</li>
<li>F. J. Dyson, Existence of a phase-transition in a one-dimensional Ising ferromagnet, <em>Comm. Math. Phys.</em> 12 (1969), 91–107.</li>
<li>T. Hutchcroft, The critical two-point function for long-range percolation on the hierarchical lattice, <a href="https://arxiv.org/abs/2103.17013v1">arXiv:2103.17013</a> (2021).</li>
<li>V. Koval, R. Meester and P. Trapman, Long-range percolation on the hierarchical lattice, <em>Electron. J. Probab.</em> 17 (2012), no. 57.</li>
</ul>
