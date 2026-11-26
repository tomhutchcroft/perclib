---
{
  "id": "hierarchical-comparison",
  "title": "Hierarchical comparison for Euclidean long-range percolation",
  "subtitle": "From selected blocks to the full critical two-point function",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "A hierarchy of independent edge layers retains exterior connections while allowing two renormalization arguments. Selecting blocks with controlled connections to their ancestors then gives the sharp averaged critical upper bound.",
  "context": [
    "The kernel on the integer lattice is symmetric, translation invariant and summable off the diagonal.",
    "A positive power-law lower envelope has exponent d + alpha, with 0 < alpha < d.",
    "Restricted clusters may leave the observation block; their edges are selected by independent layers."
  ],
  "related": [
    "finite-set-hyperscaling",
    "hierarchical-two-point",
    "integrated-susceptibility",
    "cutoff-hydrodynamics"
  ],
  "sourceIds": [
    "hutchcroft-hierarchical-upper-2022"
  ],
  "aliases": [
    "sharp averaged two-point bound",
    "ancestrally good blocks",
    "hierarchical decomposition",
    "Euclidean long-range percolation"
  ],
  "prototypeUses": []
}
---

## A hierarchy that retains exterior edges {#section-decomposition}

<p>Let $d\geq1$, $0&lt;\alpha&lt;d$ and $s=d+\alpha$. Throughout this article, $J$ is a symmetric, translation-invariant kernel on distinct vertices of $\mathbb Z^d$, with finite row sum and</p>
<div class="math-display">$$J(x,y)\geq c\|x-y\|_\infty^{-s}\qquad(x\ne y)$$</div>
<p>for some $c&gt;0$. Bonds have probabilities $1-e^{-\beta J(x,y)}$. The <a href="/tag/KXV3/">power-law theorem</a> gives $0&lt;\beta_c&lt;\infty$, and <a href="/tag/DYUM/">sharpness</a> gives finite susceptibility for $\beta&lt;\beta_c$. We first work at such a subcritical intensity. The desired estimate will be uniform as $\beta$ increases to $\beta_c$.</p>

<a id="tag-EKDO" data-assertion="definition" data-title="Translated hierarchical edge layers and good blocks"></a>
<p>Fix an integer $L\geq2$. For digits $\sigma_m\in\{0,\ldots,L-1\}^d$, put</p>
<div class="math-display">$$t_n=\sum_{m=1}^nL^{m-1}\sigma_m,\qquad
\mathcal B_n^\sigma=\{t_n+L^nk+\{0,\ldots,L^n-1\}^d:k\in\mathbb Z^d\}.$$</div>
<p>The congruence $t_{n+1}\equiv t_n\pmod{L^n}$ makes these partitions nested. Each block has $Q=L^d$ children. Their parameter space is the compact product of the digit sets. Translation by $x$ acts by replacing $t_n$ with $t_n+x$ modulo $L^n$, so every translated hierarchy is again represented. For distinct vertices, let $h_\sigma(x,y)$ be their first common block level, allowing infinity, and set</p>
<div class="math-display">$$H_\sigma(x,y)=cL^{-s h_\sigma(x,y)},\qquad R_\sigma(x,y)=J(x,y)-H_\sigma(x,y),\qquad L^{-\infty}=0.$$</div>
<p>A common $n$-block has diameter less than $L^n$, so $H_\sigma\leq J$ and $R_\sigma\geq0$. For each block $B$ at level $n\geq1$, let $\omega_B$ open independently the pairs in different children of $B$, each with probability $1-e^{-c\beta L^{-sn}}$. Independently let $\omega_R$ have intensity kernel $\beta R_\sigma$. Their union has the original bond law: each pair has at most one hierarchical contribution and its intensities add to $\beta J$.</p>
<p>For a block $B$, define $\eta_B$ to be the union of $\omega_R$ and all hierarchical layers except those indexed by strict ancestors of $B$. If $P$ is its parent, then</p>
<div class="math-display">$$\eta_P=\eta_B\cup\omega_P.$$</div>
<p>Siblings have the same restricted configuration, and $\omega_P$ is independent of it. These configurations retain many exterior edges; a cluster of $\eta_B$ is not required to stay in $B$.</p>
<p>Let $K_B(x)$ be the cluster in $\eta_B$ and define</p>
<div class="math-display">$$Z_B=\max_x|K_B(x)\cap B|,\quad
M_B=\min\{m\geq1:\mathbb P(Z_B\geq m)\leq e^{-1}\},\quad
S_B=\sum_{x,y\in B}\mathbb P(x\leftrightarrow y\text{ in }\eta_B).$$</div>
<p>A block is <em>good</em> if at least $\lfloor Q/2\rfloor-1$ of its siblings have expected maximum at least $\mathbb E Z_B$, and at least one sibling $B'$ satisfies $S_{B'}\geq S_B$. It is <em>ancestrally good</em> if it and every strict ancestor are good. These are deterministic properties of the law, not events in the percolation configuration.</p>
<p>The digit weight $L^{m-1}$ makes translation closure explicit. The source's displayed $L^m$ leaves every first-level partition fixed and does not have that property; see the <a href="/errata/hutchcroft-hierarchical-upper-2022/">provisional erratum</a>.</p>

## Choosing a good hierarchy {#section-good-hierarchy}

<a id="tag-F2G0" data-assertion="proposition" data-title="A subcritical model admits an ancestrally good hierarchy through the origin"></a>
<p>For every $0\leq\beta&lt;\beta_c$ there is a hierarchy in which $\{0\}$ is ancestrally good. Every block has at least $Q/2$ good children.</p>
<p><em>Proof.</em> Among $Q$ children, at most $\lfloor Q/2\rfloor-1$ fail the expected-maximum condition, by ordering these expectations; at most one fails the condition on $S$. Ties only increase the number satisfying the conditions. Thus at least $Q-\lfloor Q/2\rfloor\geq Q/2$ are good.</p>
<p>The required inequalities are closed conditions on the hierarchy. To justify this, suppose $\sigma^{(j)}\to\sigma$ in the digit topology. Any fixed finite collection of blocks stabilizes. The restricted intensity of each fixed edge then converges: its first common block either stabilizes, or recedes to infinity and its hierarchical contribution tends to zero. Couple all the restricted models, and the full model, by one independent uniform random variable per edge. Every restricted configuration is contained in the full configuration. The latter has finite clusters almost surely at $\beta&lt;\beta_c$.</p>
<p>For a fixed root, condition on its finite full cluster. Its finitely many internal edge statuses in the restricted configurations eventually agree with their limiting statuses almost surely, since a uniform variable equals any prescribed limiting threshold with probability zero. All edges leaving the full cluster are closed in every restricted configuration. Hence the restricted root cluster eventually agrees with its limit. Apply this simultaneously to the finitely many vertices in a block. Both $Z_B$ and its partition sum are bounded by deterministic powers of $|B|$, so bounded convergence proves continuity of $\mathbb E Z_B$ and $S_B$. The same argument applies to finite sums of connections between a block and a fixed ancestor.</p>
<p>Start with any block at level $N+1$, choose a good child, then a good child of that child, down to a singleton. Translate this singleton to the origin. The resulting hierarchy has good origin blocks at levels $0,\ldots,N$. Compactness gives a subsequential limit as $N\to\infty$; closedness of goodness at every fixed level proves the assertion.</p>
<p>This proves the selection and continuity needed in Proposition 2.2 and Lemma 2.3. The common-uniform coupling also avoids an incorrect equality in the source's mismatch display: at rates $a,b$, its mismatch probability is $|e^{-\beta a}-e^{-\beta b}|$, at most $\beta|a-b|$. The equality and its sufficient replacement are recorded provisionally in the errata.</p>

## Bounding the largest restricted cluster {#section-maximum}

<a id="tag-27T8" data-assertion="theorem" data-title="Ancestrally good blocks have a bounded maximum-cluster scale"></a>
<p>There is $L_0=L_0(d,\alpha)$ such that, for every integer $L\geq L_0$, there is $A=A(d,L,\alpha)$ with</p>
<div class="math-display">$$M_B^2&lt;\frac A{c\beta}L^{sn}$$</div>
<p>whenever $0&lt;\beta&lt;\beta_c$ and $B$ is an ancestrally good block at level $n$.</p>
<p><em>Proof.</em> The <a href="/tag/12NL/">universal intersection bounds</a> give, for every restricted model and block,</p>
<div class="math-display">$$\frac{M_B}{2e}\leq\mathbb E Z_B\leq10M_B,\qquad
\mathbb P(Z_B&lt;\varepsilon M_B)\leq27\varepsilon.$$</div>
<p>The lower mean bound follows from $\mathbb P(Z_B\geq M_B-1)&gt;e^{-1}$ and $M_B\geq2$; the upper bound follows by integrating the exponential upper tail.</p>
<p>Suppose first that $B$ is good, and take $\ell\geq\lfloor Q/2\rfloor$ children of its parent, including $B$, whose expected maxima are at least $\mathbb E Z_B$. Their quantiles are at least $M_B/(20e)\geq M_B/60$. With $t=2^{-14}$, the lower-tail bound therefore gives $\mathbb P(Z_{B_i}&lt;tM_B)\leq1/8$. By Markov's inequality, with probability at least $3/4$ at least $\ell/2$ of these children have $Z_{B_i}\geq tM_B$. No independence between these maxima is needed.</p>
<p>Reveal their common restricted configuration. In each child, choose the intersection attaining its maximum, breaking ties by a fixed ordering of the finite subsets. These chosen sets are disjoint because the children are disjoint, even if some belong to the same full restricted cluster. The unqueried parent layer joins any two chosen sets of size at least $tM_B$ with conditional probability at least</p>
<div class="math-display">$$1-\exp\{-c\beta L^{-s(n+1)}t^2M_B^2\}.$$</div>
<p>A union bound over at most $Q^2$ pairs shows that all the large sets are joined except with probability at most $Q^2e^{-c\beta L^{-s(n+1)}t^2M_B^2}$. Their union then lies in one parent cluster and has at least $t\ell M_B/2$ vertices. Since $d&gt;s/2$, choose $L_0$ so large that $t\lfloor Q/2\rfloor/2\geq L^{s/2}$. Choose $A$ so large that $Q^2e^{-t^2 A L^{-s}}\leq1/4$. Whenever $M_B^2\geq A(c\beta)^{-1}L^{sn}$, we obtain</p>
<div class="math-display">$$\mathbb P(Z_P\geq L^{s/2}M_B)\geq1/2&gt;e^{-1},\qquad M_P\geq L^{s/2}M_B.$$</div>
<p>If an ancestrally good block violated the claimed bound, this implication would iterate along its ancestors $B_m$, giving $M_{B_m}^2\geq A(c\beta)^{-1}L^{sm}$ for every $m\geq n$. On the other hand, domination by the full model and the partition identity give</p>
<div class="math-display">$$L^{dm}\chi_\beta\geq\mathbb E\sum_{x\in B_m}|K_{B_m}(x)\cap B_m|
\geq\mathbb E Z_{B_m}^2\geq\frac{M_{B_m}^2}{4e^2}.$$</div>
<p>Thus $\chi_\beta\geq A(4e^2c\beta)^{-1}L^{\alpha m}$ for every $m$, contradicting its finiteness. This proves the bound. With a good origin hierarchy and $n=0$, where $M_{\{0\}}=2$, it also gives $c\beta_c\leq A/4$ by taking $\beta\uparrow\beta_c$.</p>
<p>The contradiction starts from the level-dependent threshold $L^{sn}$. The source's different exponent in the opening line of the proof of Proposition 2.4 is recorded as a provisional display correction.</p>

## Restricted pair connections {#section-restricted}

<a id="tag-2P4M" data-assertion="theorem" data-title="The restricted pair sum is bounded on ancestrally good blocks"></a>
<p>For $L\geq L_0$ as above there is $A_1=A_1(d,L,\alpha)$ such that, at every $0&lt;\beta&lt;\beta_c$,</p>
<div class="math-display">$$S_B&lt;\frac{A_1}{c\beta}L^{sn}$$</div>
<p>for every ancestrally good level-$n$ block $B$.</p>
<p><em>Proof.</em> We first record the cap estimate supplied by rooted damping. If $X=|K_B(x)\cap B|$ and $M=M_B$, then</p>
<div class="math-display">$$\mathbb E(X-100M)_+\leq9M e^{1-100/9}\mathbb P(X\geq M)\leq\tfrac12\mathbb E X.$$</div>
<p>The first inequality integrates the rooted tail in 12NL; the second uses $M\mathbb P(X\geq M)\leq\mathbb E X$. Consequently, for $0&lt;\lambda\leq1$,</p>
<div class="math-display">$$\mathbb E(X\wedge\lambda M)\geq\frac\lambda{100}\mathbb E(X\wedge100M)\geq\frac\lambda{200}\mathbb E X.$$</div>
<p>Choose a sibling $B'$ with $S_{B'}\geq S_B$, and write $P$ for their parent and $h=c\beta L^{-s(n+1)}$. Condition on their common configuration $\eta_B=\eta_{B'}$. For $x\in B$, let $C(x)=K_B(x)\cap B$, and partition $B'$ into its restricted cluster intersections $D$. Parent edges join $C(x)$ to each $D$ with probability $1-e^{-h|C(x)||D|}$. Since the sets $D$ are disjoint, linearity of expectation gives</p>
<div class="math-display">$$\mathbb E[|K_P(x)\cap P|\mid\eta_B]
\geq(1-e^{-1})h\,(|C(x)|\wedge h^{-1/2})
\sum_D|D|(|D|\wedge h^{-1/2}).$$</div>
<p>This uses $1-e^{-u}\geq(1-e^{-1})u$ for $0\leq u\leq1$ after capping both factors. It is valid even when two intersections were already connected before the parent layer was added.</p>
<p>Both factors on the right are increasing functions of the common independent-bond configuration. For the second, write the sum as $\sum_{y\in B'}(|K_B(y)\cap B'|\wedge h^{-1/2})$. Harris therefore factors a lower bound for its expectation. Summing over $x\in B$ yields</p>
<div class="math-display">$$S_P\geq(1-e^{-1})h
\left[\sum_{x\in B}\mathbb E(|K_B(x)\cap B|\wedge h^{-1/2})\right]
\left[\sum_{y\in B'}\mathbb E(|K_{B'}(y)\cap B'|\wedge h^{-1/2})\right].$$</div>
<p>Pointwise $Z_B,Z_{B'}\leq Z_P$, so $M_B,M_{B'}\leq M_P$. The parent is ancestrally good, hence 27T8 bounds both child quantiles by $\sqrt{A/h}$. Taking $\lambda=\min\{1,A^{-1/2}\}$ in the cap estimate shows that each bracket retains a fixed positive fraction of its uncapped sum. Thus, for $a=a(d,L,\alpha)&gt;0$,</p>
<div class="math-display">$$S_P\geq a c\beta L^{-s(n+1)}S_BS_{B'}\geq a c\beta L^{-s(n+1)}S_B^2.$$</div>
<p>Set $U_B=c\beta L^{-sn}S_B$. This recurrence becomes $U_P\geq aL^{-2s}U_B^2$. If $U_B\geq a^{-1}L^{2s}$ at an ancestrally good block, the same lower bound persists along every ancestor. It would force $\chi_\beta\geq S_{B_m}/|B_m|\geq a^{-1}L^{2s}(c\beta)^{-1}L^{\alpha m}$ for every $m$, a contradiction. Taking $A_1=a^{-1}L^{2s}$ proves the theorem.</p>

<p>The parent layer used here opens only pairs in different children. The source's broader opening sentence in Lemma 2.8 is corrected provisionally in the <a href="/errata/hutchcroft-hierarchical-upper-2022/">errata</a>; all subsequent joining pairs in that proof already lie in different siblings.</p>

## Selecting control at every ancestor {#section-selection}

<a id="tag-F9QT" data-assertion="proposition" data-title="A hierarchy can control all block-to-ancestor pair sums simultaneously"></a>
<p>Fix $0&lt;\beta&lt;\beta_c$, $L\geq L_0$ and $n\geq0$. There is a hierarchy with a level-$n$ block $B_n$ containing the origin such that, writing $B_{n+k}$ for its ancestor,</p>
<div class="math-display">$$T_k(B_n):=\sum_{x\in B_n}\sum_{y\in B_{n+k}}
\mathbb P(x\leftrightarrow y\text{ in }\eta_{B_{n+k}})
\leq\frac{A_1}{c\beta}4^k L^{sn+\alpha k}\qquad(k\geq0).$$</div>
<p><em>Proof.</em> First prescribe only $0\leq k\leq\ell$. Take an ancestrally good block at level $n+\ell$, using F2G0. Let $\mathcal A_k$ be its ancestrally good descendants at level $n+k$, and let $\mathcal B_k$ consist of all their level-$n$ descendants. In particular $\mathcal B_0=\mathcal A_0$, and</p>
<div class="math-display">$$\sum_{D\in\mathcal B_k}T_k(D)=\sum_{C\in\mathcal A_k}S_C,\qquad
|\mathcal B_k|=L^{dk}|\mathcal A_k|,\qquad
|\mathcal B_0|\geq2^{-k}|\mathcal B_k|.$$</div>
<p>The last inequality follows by taking at least half the children at each of $k$ levels. Since $\mathcal B_0\subseteq\mathcal B_k$, the restricted pair bound gives</p>
<div class="math-display">$$\frac1{|\mathcal B_0|}\sum_{D\in\mathcal B_0}T_k(D)
\leq\frac{A_1}{c\beta}2^k L^{sn+\alpha k}.$$</div>
<p>For $k\geq1$, at most a fraction $2^{-k}$ of $\mathcal B_0$ can exceed the proposed bound with $4^k$. Since $\sum_{k=1}^\ell2^{-k}&lt;1$, some $D\in\mathcal B_0$ meets all these bounds. At $k=0$ the estimate holds for every such $D$ by 2P4M.</p>
<p>Translate $D$ so it contains the origin and let $\ell\to\infty$. Compactness of the hierarchy space and the finite-window continuity proved in F2G0 give a limit meeting every fixed-$k$ bound. This selection makes no translation-invariance claim about any individual restricted configuration.</p>

## The full-space two-point bound {#section-full-space}

<a id="tag-MRZO" data-assertion="theorem" data-title="Sharp averaged critical two-point upper bound from a power-law lower envelope"></a>
<p>Under the kernel hypotheses at the start of this article, there is $C=C(d,\alpha)&lt;\infty$ such that</p>
<div class="math-display">$$\sum_{z\in[-r,r]^d\cap\mathbb Z^d}\mathbb P_\beta(0\leftrightarrow z)
\leq\frac{C}{c\beta}r^\alpha\qquad(r\geq1,\ 0&lt;\beta\leq\beta_c).$$</div>
<p>Equivalently, the average over this cube is at most $C'(c\beta)^{-1}r^{-d+\alpha}$.</p>
<p><em>Proof.</em> For any fixed block chain, the configurations $\eta_{B_m}$ increase to the full configuration: every excluded hierarchical layer enters at its finite ancestor level, and the remainder is present from the start. If $x$ first becomes connected to $y$ at level $m&gt;n$, a simple connecting path uses an edge of the new layer $\omega_{B_m}$. Splitting that path at such an edge gives disjoint witnesses for the two endpoint connections and the new open edge. BK on the independent layer coordinates and a union bound give</p>
<div class="math-display">$$\tau_\beta(x,y)\leq\mathbb P(x\leftrightarrow y\text{ in }\eta_{B_n})
+c\beta\sum_{m&gt;n}L^{-sm}\sum_{a,b\in B_m}
\mathbb P(x\leftrightarrow a\text{ in }\eta_{B_m})
\mathbb P(y\leftrightarrow b\text{ in }\eta_{B_m}).$$</div>
<p>Parallel layer coordinates on one physical pair are kept distinct in this application of BK. A simple physical path supplies disjoint layer witnesses after choosing one open coordinate for each of its edges. Finite paths also justify the increasing union in this first-connection decomposition.</p>
<p>Take $L\geq\max\{L_0,4\}$ so large that $16L^{-(d-\alpha)}\leq1/2$. Use F9QT and sum the last inequality over $x,y\in B_n$. It becomes</p>
<div class="math-display">$$\begin{aligned}
\sum_{x,y\in B_n}\tau_\beta(x,y)
&\leq T_0(B_n)+c\beta L^{-sn}\sum_{k\geq1}L^{-sk}T_k(B_n)^2\\
&\leq\frac{L^{sn}}{c\beta}\left[A_1+A_1^2\sum_{k\geq1}16^k L^{-(d-\alpha)k}\right]
\leq\frac{A_1+A_1^2}{c\beta}L^{sn}.
\end{aligned}$$</div>
<p>For $n\geq1$, at least $(L-2)^dL^{d(n-1)}$ vertices $x\in B_n$ have $x+[-L^{n-1},L^{n-1}]^d\cap\mathbb Z^d\subseteq B_n$. Translation invariance of the full law, which is restored in the left side, therefore bounds the cube sum by $C(c\beta)^{-1}L^{\alpha n}$. Choose $n$ so that $r\leq L^{n-1}&lt;Lr$ to obtain the asserted estimate for arbitrary $r\geq1$. All constants depend only on $d,\alpha$ after fixing $L$ in terms of them.</p>
<p>Finally increase $\beta$ to $\beta_c$. Every connection has a finite path witness, so its probability is left-continuous in intensity. The cube contains finitely many vertices; passing to the limit gives the critical estimate. This proves Theorem 1.1 of the 2022 paper. It does not require the finite Gladkov inequality, a triangle condition, or an identification of critical exponents.</p>
<p>The factor $16^k$ comes from squaring the selection bound. It must be kept before summing the geometric series; the source drops it in one intermediate display and restores it in the following line. That local display correction, together with the hierarchy and continuity corrections above, is provisional in the <a href="/errata/hutchcroft-hierarchical-upper-2022/">source errata</a>.</p>

## The radial cutoff input {#section-radial-input}

<p>For the positive radial profile in <a href="/tag/DR1W/">DR1W</a>, norm equivalence and $j(t)\sim a t^{-d-\alpha}$ give the required lower envelope at large distances. There are only finitely many remaining nonzero lattice displacements in a bounded ball, and their intensities are positive; reducing $c$ therefore gives the envelope at every displacement. A ball in the chosen norm is contained in a cube of comparable radius. MRZO consequently gives</p>
<div class="math-display">$$\mathbb E_{\beta_c}|K_o\cap B_r|\leq C_J r^\alpha\qquad(r\geq1).$$</div>
<p>This verifies the sharp window hypothesis in <a href="/tag/KPBJ/">KPBJ</a> and hence in <a href="/tag/N3OC/">the reverse-doubling theorem</a> and <a href="/tag/X8F6/">the model good-scale argument</a>. The latter still uses the cited finite Gladkov theorem through its mixed-window estimate. The all-scale fictitious bounds and the critical-dimensional hydrodynamic theorem remain separate.</p>



## The improved critical volume tail {#section-improved-volume-tail}

<a id="tag-QV5S" data-assertion="theorem" data-title="The full-space average gives the improved critical volume tail"></a>
<p>Under the hypotheses of this article, let $\theta=(d-\alpha)/(2d)$. There is $C=C(d,\alpha)&lt;\infty$ such that</p>
<div class="math-display">$$\mathbb P_\beta(|K_0|\geq n)\leq
\frac{C}{\sqrt{c\beta}}n^{-\theta}
\qquad(0&lt;\beta\leq\beta_c,\ n\geq1).$$</div>
<p>In particular $\mathbb P_{\beta_c}(|K_0|=\infty)=0$. If the critical volume exponent exists in the sense that $\mathbb P_{\beta_c}(|K_0|\geq n)=n^{-1/\delta+o(1)}$, then $\delta\leq2d/(d-\alpha)$. The following weaker normalization is the form in <a href="https://arxiv.org/html/2202.07634v2#S1">Corollary 1.4 of the source</a>:</p>
<div class="math-display">$$\mathbb P_{\beta_c}(|K_0|\geq n)\leq
\frac{C'}{(c\beta_c)^{d/(2d-\alpha)}}n^{-(d-\alpha)/(2d)},\qquad C'=C'(d,\alpha).$$</div>
<p>For a fixed kernel, there are also $a_J,A_J&gt;0$ and an integer $N_J$ such that</p>
<div class="math-display">$$\begin{aligned}
\mathbb P_\beta(|K_0|\geq n)&\leq A_J n^{-\theta}
e^{-a_J(\beta_c-\beta)n^\theta}quad(0\leq\beta&lt;\beta_c,\ n\geq N_J),\\
\chi_\beta&\leq A_J(\beta_c-\beta)^{-(d+\alpha)/(d-\alpha)}
\quad(0\leq\beta&lt;\beta_c).
\end{aligned}$$</div>
<p><em>Proof.</em> The <a href="/tag/MRZO/">full-space estimate</a> supplies $\sum_{x\in Q_r}\tau_\beta(x)\leq C_0(c\beta)^{-1}r^\alpha$ for all $r\geq1$ and $0&lt;\beta&lt;\beta_c$, with $C_0=C_0(d,\alpha)$. Sharpness gives $\chi_\beta&lt;\infty$ throughout this interval. Apply <a href="/tag/GW20/">GW20</a> with $\gamma=\alpha$ and $B=C_0/(c\beta)$. Its exponent is $\theta=(d-\alpha)/(2d)$, and both amplitude terms are constant multiples of $(c\beta)^{-1/2}$. This proves the displayed bound below criticality using only written wiki proofs, including the two-ghost estimate BYEO.</p>
<p>For each fixed integer $n$, the event $|K_0|\geq n$ has a finite witness: the union of paths from zero to $n$ distinct vertices. In the common-uniform coupling, every finite family of edges open at $\beta_c$ is already open sufficiently near $\beta_c$ from below, almost surely. Hence</p>
<div class="math-display">$$\mathbb P_\beta(|K_0|\geq n)\uparrow
\mathbb P_{\beta_c}(|K_0|\geq n)\qquad(\beta\uparrow\beta_c).$$</div>
<p>Taking this limit gives the critical bound without assuming critical nonpercolation. Letting $n\to\infty$ then proves nonpercolation, since $\theta&gt;0$. Taking logarithms of the same estimate gives the claimed inequality for $\delta$ when its defining limit exists.</p>
<p>The passage to the source's prefactor uses the bound $c\beta_c\leq C_3(d,\alpha)$ already established in <a href="/tag/27T8/">27T8</a>. Since $s=d/(2d-\alpha)&gt;1/2$,</p>
<div class="math-display">$$(c\beta_c)^{-1/2}
=(c\beta_c)^{-s}(c\beta_c)^{s-1/2}
\leq C_3^{s-1/2}(c\beta_c)^{-s}.$$</div>
<p>The different prefactor comes from choosing a box with radius comparable to $n^{1/d}$ in GW20 and solving the least-amplitude quadratic directly. It is not a correction to the source statement.</p>
<p>Finally, apply <a href="/tag/I328/">the polynomial endpoint-tail theorem</a> with endpoint $\beta_c$ and the critical bound just proved. Translation invariance supplies the bound at every root, and summability gives the required uniform row bound. That theorem yields the stretched exponential and susceptibility estimates, with exponent $(1-\theta)/\theta=(d+\alpha)/(d-\alpha)$; enlarge $A_J$ to serve both estimates.</p>
<p>This completes the volume-tail deduction in section 3. The averaged spatial estimate does not establish a pointwise two-point bound, a triangle condition, or the predicted equality $\delta=(d+\alpha)/(d-\alpha)$. The proof concerns Euclidean long-range percolation; the three hierarchical-lattice tail regimes are separate results.</p>
