---
{
  "id": "hierarchical-runaway",
  "title": "The hierarchical runaway observable",
  "subtitle": "Amplification across blocks and the finite-susceptibility contradiction",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Independent block clusters and direct connecting edges give a quantitative quantile amplification. Finite susceptibility forbids the resulting exponential growth, and finite-block continuity extends the bound to an endpoint.",
  "context": [
    "The standard hierarchical lattice has level-n blocks of size $L^{dn}$, for integers $L\\geq2$ and $d\\geq1$.",
    "The intensity model is translation-invariant, and weights at hierarchical level j are at least $cL^{-(d+\\alpha)j}$ with $0<\\alpha<d$.",
    "Clusters in this article are restricted to their finite block, not full-cluster intersections with it.",
    "The final sections use a separate exact radial model and distinguish its truncated block layers from the full law restricted to a block."
  ],
  "related": [
    "hierarchical-two-point",
    "hierarchical-block-coalescent",
    "multiplicative-coalescent",
    "finite-random-graphs",
    "exponential-moments",
    "multipoint-trees",
    "universal-tightness"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "hutchcroft-hierarchical-2021",
    "hutchcroft-hierarchical-volumes-2022"
  ],
  "aliases": [
    "runaway observable",
    "hierarchical amplification",
    "block quantile",
    "scaling catastrophe"
  ],
  "prototypeUses": []
}
---

## Amplifying a large block quantile {#section-amplification}

<a id="tag-7AER" data-assertion="theorem" data-title="Quantitative hierarchical block-quantile amplification"></a>
<p>On the standard hierarchical lattice, fix integers $L\geq2$, $d\geq1$, and constants $c&gt;0$, $0&lt;\alpha&lt;d$. Use independent bonds of probabilities $1-e^{-\beta J(u,v)}$, with finite nonnegative translation-invariant weights satisfying</p>
<div class="math-display">$$J(u,v)\geq cL^{-(d+\alpha)j}\quad\text{when }u,v\text{ first share a level-}j\text{ block}.$$</div>
<p>Let $Z_n$ be the largest cluster size using only edges inside a level-$n$ block, and define $R_n(\beta)=\min\{m\geq1:\mathbb P_\beta(Z_n\geq m)\leq e^{-1}\}$. Translation invariance makes this independent of the chosen block. Choose an integer $\ell\geq1$ such that, with $N=L^{d\ell}$,</p>
<div class="math-display">$$e^{-N/(8e)}\leq\frac14,\qquad L^{(d-\alpha)\ell}\geq16e^2,$$</div>
<p>and set</p>
<div class="math-display">$$A=\frac4c L^{(d+\alpha)\ell}\log(2N^2).$$</div>
<p>For every $\beta&gt;0$ and integer $n\geq0$,</p>
<div class="math-display">$$R_n(\beta)^2\geq\frac A\beta L^{(d+\alpha)n}\quad\Longrightarrow\quad R_{n+\ell}(\beta)^2\geq\frac A\beta L^{(d+\alpha)(n+\ell)}.$$</div>
<p>Such $\ell$ exist because $\alpha&lt;d$. This statement needs no critical-parameter or susceptibility assumption.</p>
<p><em>Proof.</em> A level-$(n+\ell)$ block contains $N$ disjoint level-$n$ blocks. Write $R=R_n(\beta)$. Since $2\leq R\leq L^{dn}+1$ and $\mathbb P(Z_n\geq R-1)&gt;e^{-1}$, each small block has probability at least $e^{-1}$ of containing a cluster of size at least $R/2$. Call such a block good, and choose one of its largest clusters by a fixed tie-breaking rule. Goodness depends only on internal edges, so the good-block indicators are independent.</p>
<p>If $G$ is their number, an exponential Markov bound gives</p>
<div class="math-display">$$\mathbb P\left(G&lt;\frac N{2e}\right)\leq e^{-N/(8e)}\leq\frac14.$$</div>
<p>For completeness, with $t=\log2$ the product of the Bernoulli Laplace transforms is at most $\exp[-(N/e)(1-e^{-t})]$. Multiplying by $\exp[tN/(2e)]$ gives an exponent at most $-N/(8e)$, since $(1-\log2)/2&gt;1/8$.</p>
<p>Condition on all small-block interiors. Between selected clusters $C_i,C_j$ in distinct good blocks, every edge has weight at least $cL^{-(d+\alpha)(n+\ell)}$. The probability that no direct edge joins them is therefore at most</p>
<div class="math-display">$$\exp\!\left[-\beta cL^{-(d+\alpha)(n+\ell)}|C_i||C_j|\right]\leq\exp\!\left[-\frac{cA}4L^{-(d+\alpha)\ell}\right]=\frac1{2N^2}.$$</div>
<p>Here the last inequality uses the assumed lower bound on $R^2$ and $|C_i|,|C_j|\geq R/2$. The connecting edges have not been exposed. A union bound over fewer than $N^2/2$ cluster pairs shows that, conditionally, all pairs have a direct connection with probability at least $3/4$.</p>
<p>With probability at least $1/2&gt;e^{-1}$, there are at least $N/(2e)$ good clusters and they all belong to one larger cluster. Its size is at least $NR/(4e)$. The quantile definition gives $R_{n+\ell}\geq NR/(4e)$, also when this threshold is not an integer: apply the probability bound at its ceiling. Hence</p>
<div class="math-display">$$R_{n+\ell}^2\geq\frac{L^{2d\ell}}{16e^2}R_n^2\geq\frac A\beta L^{(d+\alpha)(n+\ell)}\frac{L^{(d-\alpha)\ell}}{16e^2}\geq\frac A\beta L^{(d+\alpha)(n+\ell)}.$$</div>
<p>The argument deliberately asks for every pair of selected clusters to be connected directly. This costs a large fixed $A$, but avoids a separate random-graph giant-component theorem.</p>

## Ruling out runaway growth {#section-bound}

<a id="tag-2XJX" data-assertion="theorem" data-title="Hierarchical block-quantile bound from finite susceptibility and endpoint continuity"></a>
<p>In the preceding model, with the same $\ell,A$, if $\beta&gt;0$ and the full-model susceptibility $\chi(\beta)$ is finite, then</p>
<div class="math-display">$$R_n(\beta)^2&lt;\frac A\beta L^{(d+\alpha)n}\qquad(n\geq0).$$</div>
<p>More generally, if $0\leq a&lt;b&lt;\infty$, $b&gt;0$, and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$, then</p>
<div class="math-display">$$R_n(\beta)^2\leq\frac A b L^{(d+\alpha)n}\qquad(n\geq0,\ 0\leq\beta\leq b).$$</div>
<p><em>Proof.</em> Fix a positive parameter with finite susceptibility $\chi$. Transitivity and the <a href="/tag/Y84V/">tree-graph moments</a> give the <a href="/tag/SNB3/">exponential full-cluster tail</a></p>
<div class="math-display">$$\mathbb P_\beta(|K_x|\geq k)\leq(1+\chi^{-1})e^{-k/(2\chi^2)}.$$</div>
<p>A union bound over the $L^{dn}$ vertices of a level-$n$ block therefore gives</p>
<div class="math-display">$$R_n(\beta)\leq\left\lceil2\chi^2\left(dn\log L+\log(1+\chi^{-1})+1\right)\right\rceil=O_\beta(n+1).$$</div>
<p>If the first asserted bound failed at any scale $n$, amplification would propagate its failure to every $n+k\ell$. It would force $R_{n+k\ell}\geq\sqrt{A/\beta}\,L^{(d+\alpha)(n+k\ell)/2}$, contradicting the linear bound as $k\to\infty$. This proves the strict inequality.</p>
<p>For the endpoint claim fix $n$ and write $m=R_n(b)$. The block has finitely many edges with finite weights, so each probability $\mathbb P_\beta(Z_n\geq k)$ is continuous in $\beta$. Since $\mathbb P_b(Z_n\geq m-1)&gt;e^{-1}$, the same strict inequality holds sufficiently close to $b$ from below. Monotonicity gives $R_n(\beta)\leq R_n(b)$, so in fact $R_n(\beta)=m$ for all sufficiently close lower parameters. Passing to the limit in the first bound yields $R_n(b)^2\leq(A/b)L^{(d+\alpha)n}$. Finally $R_n(\beta)\leq R_n(b)$ for $0\leq\beta\leq b$.</p>
<p>This is the runaway-observable mechanism. Applying it with $b=\beta_c$ still requires a finite positive critical parameter and finite susceptibility below it. Those sharpness inputs are not consequences of block amplification. The subsequent expected-size recursion and restricted-to-unrestricted two-point estimates are also separate steps.</p>

## Identifying a finite critical intensity {#section-critical-intensity}

<a id="tag-FF30" data-assertion="theorem" data-title="Hierarchical critical intensity and boundary flux from amplification and sharpness"></a>
<p>In the model of <a href="/tag/7AER/">the amplification theorem</a>, assume also that the weights are symmetric and have finite common off-diagonal row sum</p>
<div class="math-display">$$B=\sum_{v\ne o}J(o,v)&lt;\infty.$$</div>
<p>The lower bound on the weights gives $B&gt;0$. Let $\beta_c$ be the critical intensity, and retain the constant $A$ from that theorem. Then</p>
<div class="math-display">$$0&lt;\frac1B\leq\beta_c\leq\frac A4&lt;\infty,\qquad R_n(\beta_c)^2\leq\frac A{\beta_c}L^{(d+\alpha)n}\quad(n\geq0).$$</div>
<p>For every finite $T\ni o$, writing $\tau_{T,\beta_c}(o,u)$ for internal connectivity, one also has</p>
<div class="math-display">$$\beta_c\sum_{u\in T}\tau_{T,\beta_c}(o,u)\sum_{v\notin T}J(u,v)\geq1.$$</div>
<p><em>Proof.</em> The row-sum bound gives $\beta_c\geq1/B$. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness argument</a> gives finite susceptibility at every finite $\beta&lt;\beta_c$, including when the extended threshold might initially be infinite. Hence <a href="/tag/2XJX/">the runaway bound</a> applies at every $0&lt;\beta&lt;\beta_c$. A level-zero block consists of one vertex, so $R_0(\beta)=2$. Taking $n=0$ in that bound gives $4&lt;A/\beta$, or $\beta&lt;A/4$. Thus every positive subcritical intensity is less than $A/4$, which rules out an infinite threshold and yields $\beta_c\leq A/4$. The endpoint part of 2XJX now applies with $b=\beta_c$ and gives the quantile estimate.</p>
<p>For the boundary assertion, put</p>
<div class="math-display">$$\Phi_\beta(T)=\sum_{u\in T}\tau_{T,\beta}(o,u)\sum_{v\notin T}(1-e^{-\beta J(u,v)}).$$</div>
<p>The <a href="/articles/finite-size-sharpness/">canonical finite-size characterization</a> and continuity of $\Phi_\beta(T)$ imply $\Phi_{\beta_c}(T)\geq1$: a strict contraction at $\beta_c$ would persist at a larger intensity and force finite susceptibility there. Continuity holds because the internal graph is finite and the exterior probability rows converge locally uniformly, bounded by a constant times the summable intensity rows. Finally $1-e^{-\beta_c J}\leq\beta_c J$ gives the displayed flux bound.</p>
<p>This supplies the finite positive endpoint, subcritical finiteness and boundary-flux assumptions used later in this article. If the matching upper bound on $J$ and the stated rooted damping estimate are also supplied, <a href="/tag/7YNX/">the conditional two-point theorem</a> therefore applies at $b=\beta_c$. Rooted damping is a separate input to this argument, supplied by <a href="/tag/12NL/">the marked-tree splitting proof</a> for independent bonds. Nor does finite critical intensity alone prove absence of an infinite critical cluster.</p>

## The sibling-block expected-size recursion {#section-expected-size}

<a id="tag-655W" data-assertion="theorem" data-title="Restricted hierarchical susceptibility bound from rooted damping"></a>
<p>Retain the model of <a href="/tag/7AER/">the amplification theorem</a> and the endpoint hypotheses of <a href="/tag/2XJX/">the quantile bound</a>: $0\leq a&lt;b&lt;\infty$, $b&gt;0$, and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$. Let $a_n=\mathbb E_b|K_o^{\Lambda_n}|$ be the expected root-cluster size using only edges inside its level-$n$ block. Suppose the following rooted damping estimate holds in each finite block, with its largest-cluster quantile $R_n=R_n(b)$:</p>
<div class="math-display">$$\mathbb P_b(|K_x^{\Lambda_n}|\geq\lambda R_n)\leq e^{1-\lambda/9}\mathbb P_b(|K_x^{\Lambda_n}|\geq R_n)\qquad(x\in\Lambda_n,\ \lambda\geq1).$$</div>
<p>There are constants $k,C'&gt;0$, independent of $n$, such that</p>
<div class="math-display">$$a_{n+1}\geq kL^{-\alpha n}a_n^2,\qquad a_n\leq C'L^{\alpha n}\qquad(n\geq0).$$</div>
<p>Rooted damping is the <a href="/tag/21D4/">universal-tightness input</a>; it is stated here for block-restricted clusters and follows from <a href="/tag/12NL/">the finite-witness proof</a> applied to the block as the whole graph. No lower bound on $a_n$ is asserted.</p>
<p><em>Proof.</em> Choose a fixed real $t\geq1$ with $(t+9)e^{1-t/9}\leq1/2$. If $X$ is a rooted cluster size in a level-$n$ block and $R=R_n$, tail integration and rooted damping give</p>
<div class="math-display">$$\begin{aligned}
\mathbb E[X\mathbf1_{\{X&gt;tR\}}]
&=tR\,\mathbb P(X&gt;tR)+\int_{tR}^\infty\mathbb P(X&gt;s)\,ds\\
&\leq(t+9)R e^{1-t/9}\mathbb P(X\geq R)
\leq\frac12\mathbb E X.
\end{aligned}$$</div>
<p>Thus truncation to $X\leq tR$ retains at least half the mean. This is a relative-mean estimate; a small probability of exceeding $tR$ alone would not suffice.</p>
<p>Choose a sibling level-$n$ block $\Lambda_n'$ inside the parent of $\Lambda_n$. Condition on the two block interiors. Let $X=|K_o^{\Lambda_n}|$, and let $C_i$ be the clusters in $\Lambda_n'$. Every edge between the two blocks has weight at least $cL^{-(d+\alpha)(n+1)}$. With $\lambda_n=bcL^{-(d+\alpha)(n+1)}$, the conditional probability that $K_o^{\Lambda_n}$ has a direct edge to $C_i$ is at least $1-e^{-\lambda_n X|C_i|}$. Therefore</p>
<div class="math-display">$$a_{n+1}\geq\mathbb E\sum_i |C_i|\bigl(1-e^{-\lambda_n X|C_i|}\bigr).$$</div>
<p>The selected sibling clusters are disjoint, so this counts each of their vertices at most once. It does not require the different connecting events to be independent.</p>
<p>Restrict the sum to $X\leq tR_n$ and $|C_i|\leq tR_n$. The quantile bound $R_n^2\leq(A/b)L^{(d+\alpha)n}$ makes $\lambda_n X|C_i|\leq T$, where $T=cAt^2L^{-(d+\alpha)}$ is independent of $n$. Since $1-e^{-u}\geq ue^{-T}$ for $0\leq u\leq T$, independence of the block interiors gives</p>
<div class="math-display">$$a_{n+1}\geq e^{-T}\lambda_n\,\mathbb E[X\mathbf1_{\{X\leq tR_n\}}]\,\mathbb E\sum_i|C_i|^2\mathbf1_{\{|C_i|\leq tR_n\}}.$$</div>
<p>Counting each sibling vertex in its own cluster rewrites the last sum as $\sum_{x\in\Lambda_n'}|K_x^{\Lambda_n'}|\mathbf1_{\{|K_x^{\Lambda_n'}|\leq tR_n\}}$. Translations within a hierarchical block preserve its restricted law, so the truncated-mean bound makes the two factors at least $a_n/2$ and $L^{dn}a_n/2$. Hence the recursion holds with</p>
<div class="math-display">$$k=\frac{bc}{4}e^{-T}L^{-(d+\alpha)}&gt;0.$$</div>
<p>To turn the lower recursion into an upper bound, put $y_n=kL^{-\alpha(n+1)}a_n$. Then $y_{n+1}\geq y_n^2$. If $y_n&gt;1$ at any scale, iteration gives $y_{n+j}\geq y_n^{2^j}$. But the deterministic volume bound $a_{n+j}\leq L^{d(n+j)}$ implies</p>
<div class="math-display">$$y_{n+j}\leq kL^{-\alpha}L^{(d-\alpha)(n+j)},$$</div>
<p>which grows only exponentially in $j$, a contradiction. Thus $y_n\leq1$ for every $n$, and $a_n\leq(L^\alpha/k)L^{\alpha n}$.</p>
<p>This supplies the sibling-block recursion and its deterministic runaway conclusion. The constants need not be sharp. The sharpness boundary-flux lower bound, pointwise conversion and removal of the block restriction remain further steps.</p>

## From block means to the two-point function {#section-two-point}

<a id="tag-7YNX" data-assertion="theorem" data-title="Conditional hierarchical two-point bounds from block means and boundary flux"></a>
<p>Retain all hypotheses of <a href="/tag/655W/">the expected-size theorem</a>, including its general endpoint $b$ and rooted damping, and suppose also that for some $C_0&lt;\infty$,</p>
<div class="math-display">$$J(u,v)\leq C_0L^{-(d+\alpha)j}\quad\text{at hierarchical level }j.$$</div>
<p>Write $\tau_n(o,u)=\mathbb P_b(o\leftrightarrow u\text{ using only edges in }\Lambda_n)$ and $\tau(o,u)=\mathbb P_b(o\leftrightarrow u)$. Assume the boundary-flux inequalities</p>
<div class="math-display">$$b\sum_{u\in\Lambda_n}\tau_n(o,u)\sum_{v\notin\Lambda_n}J(u,v)\geq1\qquad(n\geq0).$$</div>
<p>Then there are constants $c_1,C_1&gt;0$ such that, whenever $x\in\Lambda_n\setminus\Lambda_{n-1}$ and $n\geq1$,</p>
<div class="math-display">$$c_1L^{-(d-\alpha)n}\leq\tau_n(o,x)\leq\tau(o,x)\leq C_1L^{-(d-\alpha)n}.$$</div>
<p>The boundary-flux inequalities and finite susceptibility below $b$ are the sharpness inputs to this conditional statement. The theorem does not establish those inputs or identify $b$ as the critical parameter.</p>
<p><em>Proof.</em> The number of vertices at hierarchical level $j$ from a fixed vertex is $(1-L^{-d})L^{dj}$. For every $u\in\Lambda_n$, all vertices outside $\Lambda_n$ are at levels greater than $n$, so</p>
<div class="math-display">$$\sum_{v\notin\Lambda_n}J(u,v)\leq D L^{-\alpha n},\qquad D=\frac{C_0(1-L^{-d})L^{-\alpha}}{1-L^{-\alpha}}.$$</div>
<p>The flux hypothesis therefore gives $a_n\geq L^{\alpha n}/(bD)$. Together with the preceding theorem this bounds the restricted mean above and below by fixed multiples of $L^{\alpha n}$.</p>
<p>For the pointwise lower bound, the two vertices $o,x$ lie in distinct level-$(n-1)$ blocks inside $\Lambda_n$. Their clusters in these two blocks are independent, with volumes $X,Y$ each having mean $a_{n-1}$. The same truncation used in the sibling recursion retains at least half of each mean below $tR_{n-1}$. On that event, with $\lambda=bcL^{-(d+\alpha)n}$, we have $\lambda XY\leq T=cAt^2L^{-(d+\alpha)}$. A direct edge between the clusters gives</p>
<div class="math-display">$$\tau_n(o,x)\geq e^{-T}\lambda\,\mathbb E[X\mathbf1_{\{X\leq tR_{n-1}\}}]\mathbb E[Y\mathbf1_{\{Y\leq tR_{n-1}\}}]\geq\frac{ce^{-T}L^{-2\alpha}}{4bD^2}L^{-(d-\alpha)n}.$$</div>
<p>This uses the lower block mean explicitly; an averaged estimate and distance symmetry alone would not supply this lower bound.</p>
<p>For the upper bound, let $E_m$ be the event that $o$ connects to $x$ inside $\Lambda_m$. Every finite open path is contained in some such block, and $E_m$ increases with $m$. Thus</p>
<div class="math-display">$$\tau(o,x)=\mathbb P(E_n)+\sum_{m&gt;n}\mathbb P(E_m\setminus E_{m-1}).$$</div>
<p>On $E_n$, any path from $o$ to $x$ crosses between level-$(n-1)$ child blocks. On $E_m\setminus E_{m-1}$, every path inside $\Lambda_m$ must cross between level-$(m-1)$ child blocks. In either case choose a simple witnessing path and orient one such edge $(u,v)$ along it. The two path segments and that edge have pairwise disjoint edge sets. Finite-coordinate BK and a union bound over oriented crossing pairs give, for the corresponding term at level $m$,</p>
<div class="math-display">$$\mathbb P(\text{term at level }m)\leq\sum_{\substack{u,v\in\Lambda_m\\u,v\text{ in different children}}}\tau_m(o,u)\bigl(1-e^{-bJ(u,v)}\bigr)\tau_m(v,x)\leq bC_0L^{-(d+\alpha)m}a_m^2.$$</div>
<p>Translations within $\Lambda_m$ make both connection sums equal to $a_m$, and $1-e^{-bJ}\leq bJ$. With $a_m\leq C'L^{\alpha m}$, this is at most $bC_0(C')^2L^{-(d-\alpha)m}$. Since $\alpha&lt;d$, summing the geometric series gives the upper bound with</p>
<div class="math-display">$$C_1=\frac{bC_0(C')^2}{1-L^{-(d-\alpha)}}.$$</div>
<p>The two path pieces are both estimated in the larger block $\Lambda_m$; neither is assumed to stay in the original scale-$n$ block. Their resulting decay in the excess scale is enough for summability.</p>
<p>This supplies the boundary-flux reduction and restricted-to-unrestricted argument. It completes the two-point proof mechanism conditional on the stated sharpness and rooted-damping inputs. The hierarchical volume-tail benchmarks, including critical-dimensional logarithms, require additional results.</p>

## The triangle diagram across scales {#section-triangle}

<a id="tag-MS6M" data-assertion="theorem" data-title="Hierarchical triangle threshold from two-sided kernel bounds"></a>
<p>On the standard hierarchical lattice with $L\geq2$, $d\geq1$, let $0&lt;\alpha&lt;d$ and let $f$ be a nonnegative function satisfying, for constants $0&lt;c\leq C&lt;\infty$,</p>
<div class="math-display">$$c\langle x\rangle^{-(d-\alpha)}\leq f(x)\leq C\langle x\rangle^{-(d-\alpha)},\qquad \langle x\rangle=\max\{1,\|x\|\}.$$</div>
<p>Define</p>
<div class="math-display">$$\Delta_N=\sum_{x,y\in\Lambda_N}f(x)f(y-x)f(y),\qquad N\geq0.$$</div>
<p>There are positive constants $a,A$, depending only on $c,C,L,d,\alpha$, such that for every integer $n\geq1$,</p>
<div class="math-display">$$aL^{(3\alpha-d)n}\leq\Delta_n-\Delta_{n-1}\leq AL^{(3\alpha-d)n}.$$</div>
<p>Consequently the full triangle sum is finite exactly when $3\alpha&lt;d$. For $3\alpha=d$, $\Delta_N\asymp N+1$; for $3\alpha&gt;d$, $\Delta_N\asymp L^{(3\alpha-d)N}$. These are deterministic kernel statements; neither positive definiteness nor a radial equality for $f$ is required.</p>
<p><em>Proof.</em> Put $s=d-\alpha$ and $F_n=\sum_{z\in\Lambda_n}f(z)$. Shell counting gives</p>
<div class="math-display">$$cL^{\alpha n}\leq F_n\leq C\sum_{j=0}^nL^{\alpha j}\leq\frac{C}{1-L^{-\alpha}}L^{\alpha n}.$$</div>
<p>For the lower bound, use $f(z)\geq cL^{-sn}$ throughout $\Lambda_n$. For the upper bound, a level-$j$ shell has at most $L^{dj}$ vertices; the $j=0$ term accounts for the origin.</p>
<p>The increment contains precisely those pairs $(x,y)$ in $\Lambda_n^2$ for which at least one vertex is outside $\Lambda_{n-1}$. Among the three distances $\|x\|,\|y\|,\|y-x\|$, at least two then equal $L^n$: the ultrametric inequality excludes a unique largest distance. Cover these pairs by the three possible choices of two such distances. The corresponding two factors are at most $C^2L^{-2sn}$. In each case, the sum of the remaining factor over all pairs in $\Lambda_n^2$ is $L^{dn}F_n$. For the factor $f(y-x)$ this follows by setting $z=y-x$ in the finite subgroup $\Lambda_n$; the other two cases are immediate. Overcounting is harmless, so</p>
<div class="math-display">$$\Delta_n-\Delta_{n-1}\leq3C^2L^{-2sn}L^{dn}F_n\leq\frac{3C^3}{1-L^{-\alpha}}L^{(3\alpha-d)n}.$$</div>
<p>For the reverse inequality restrict to $x\in\Lambda_n\setminus\Lambda_{n-1}$ and $y\in\Lambda_{n-1}$. Both $x$ and $y-x$ have norm $L^n$. There are $(1-L^{-d})L^{dn}$ choices of $x$, whence</p>
<div class="math-display">$$\Delta_n-\Delta_{n-1}\geq c^2L^{-2sn}(1-L^{-d})L^{dn}F_{n-1}\geq c^3(1-L^{-d})L^{-\alpha}L^{(3\alpha-d)n}.$$</div>
<p>Summing the increments, starting from $\Delta_0=f(0)^3$, proves all three cases. The full sum is their monotone limit.</p>
<p>Applied to the preceding conditional two-point bounds, this locates the triangle threshold without assuming radial symmetry. At $3\alpha=d$, the linear growth in the number of scales is logarithmic in the block radius $L^N$. This does not by itself prove logarithmic corrections for cluster volumes, susceptibility, or the percolation density; those require additional probabilistic arguments.</p>

## A constraint on the volume-tail exponent {#section-volume-exponent}

<a id="tag-7GDE" data-assertion="corollary" data-title="Hierarchical volume-tail exponent obstruction below the triangle threshold"></a>
<p>In the model of <a href="/tag/7AER/">the amplification theorem</a>, suppose the weights are symmetric and also satisfy $J(u,v)\leq C_0L^{-(d+\alpha)j}$ at level $j$, for some finite $C_0$. Assume $d/3&lt;\alpha&lt;d$. If the critical full-cluster tail has a finite positive logarithmic exponent $\delta$, in the sense that</p>
<div class="math-display">$$\mathbb P_{\beta_c}(|K_o|\geq n)=n^{-1/\delta+o(1)}\qquad(n\to\infty),$$</div>
<p>then</p>
<div class="math-display">$$\delta\geq\frac{d+\alpha}{d-\alpha}.$$</div>
<p><em>Proof.</em> The upper weight bound is summable because $\alpha&gt;0$. Thus <a href="/tag/FF30/">the critical-intensity theorem</a> gives a finite positive $\beta_c$, the critical quantile estimate and boundary flux. The <a href="/tag/12NL/">rooted-tail theorem</a> supplies damping in each finite block. Consequently <a href="/tag/7YNX/">the two-point argument</a> applies at $b=\beta_c$; its boundary-flux calculation gives $\mathbb E_{\beta_c}|K_o^{\Lambda_m}|\geq c_*L^{\alpha m}$ for a fixed $c_*&gt;0$.</p>
<p>If the asserted inequality for $\delta$ failed, we could choose</p>
<div class="math-display">$$\frac{d-\alpha}{d+\alpha}&lt;\theta&lt;\min\{1/\delta,1/2\},$$</div>
<p>since $\alpha&gt;d/3$. The logarithmic tail law gives $\mathbb P_{\beta_c}(|K_o|\geq n)\leq A n^{-\theta}$ for all integers $n\geq1$, after enlarging $A$ for finitely many small values. Translation invariance gives the same bound at every root. Apply <a href="/tag/UVQ6/">finite-window hyperscaling</a> to $\Lambda_m$, and use that an internal cluster is contained in the full-cluster intersection:</p>
<div class="math-display">$$
c_*L^{\alpha m}\leq\mathbb E_{\beta_c}|K_o^{\Lambda_m}|
\leq\sum_{v\in\Lambda_m}\mathbb P_{\beta_c}(o\leftrightarrow v)
\leq C A^{2/(1+\theta)}L^{d(1-\theta)m/(1+\theta)}.
$$</div>
<p>The last exponent is smaller than $\alpha$ by the choice of $\theta$, a contradiction as $m\to\infty$.</p>
<p>This is the volume-exponent obstruction of <a href="https://arxiv.org/pdf/2103.17013v1#page=6">Corollary 1.5</a>, with the underlying probability bound proved separately. It does not establish existence of $\delta$, equality in the bound, or any logarithmic correction. Radial equality of the weights is unnecessary for this argument; the stated translation invariance and two-sided level bounds suffice.</p>

## Boundary scales below an endpoint {#section-boundary-scales}

<p>Fix integers $L\geq2$, $d\geq1$ and a real $0&lt;\alpha&lt;d$. On $\mathbb H_L^d$, let $J$ be a symmetric displacement kernel satisfying</p>
<div class="math-display">$$c_J\|x\|^{-d-\alpha}\leq J(x)\leq C_J\|x\|^{-d-\alpha}\qquad(x\ne0),$$</div>
<p>with $0&lt;c_J\leq C_J&lt;\infty$. Use the independent bond law with probabilities $q_\beta(x,y)=1-e^{-\beta J(y-x)}$. Write $\chi_n(\beta)=\mathbb E_\beta|K_o^{\Lambda_n}|$ for the internal-ball susceptibility, $\chi(\beta)=\mathbb E_\beta|K_o|$ for the full susceptibility, and $\tau_\beta$ for the full connection kernel. Suppose a finite $b&gt;0$ satisfies the two endpoint conditions</p>
<div class="math-display">$$\tau_b(o,x)\leq A\langle x\rangle^{-d+\alpha}\quad(x\in\mathbb H_L^d),\qquad
\varphi_b(\Lambda_n)\geq1\quad(n\geq0),$$</div>
<p>for some finite $A$. Here $\varphi_\beta(\Lambda_n)=\sum_{x\in\Lambda_n,y\notin\Lambda_n}\tau_\beta^{\Lambda_n}(o,x)q_\beta(x,y)$, with the first connection restricted to the ball. These are explicit inputs for the remainder of this section. At $b=\beta_c$ they are supplied by the upper critical two-point estimate and the root-containing finite-set criterion; a pointwise estimate alone does not supply the second condition.</p>

<a id="tag-GPDF" data-assertion="definition" data-title="Hierarchical boundary thresholds and their length scale"></a>
<p>Set</p>
<div class="math-display">$$r_n(\beta)=\sum_{y\notin\Lambda_n}(1-e^{-\beta J(y)}),\qquad
\varphi_\beta(\Lambda_n)=r_n(\beta)\chi_n(\beta).$$</div>
<p>The identity holds because translating by any $x\in\Lambda_n$ permutes its complement. Let $\beta_n\in(0,b)$ be the unique solution of $\varphi_{\beta_n}(\Lambda_n)=1/2$, and put</p>
<div class="math-display">$$b_n=\max_{0\leq k\leq n}\beta_k,\qquad
m(\beta)=\min\{n\geq0:\beta\leq b_n\},\qquad
\xi(\beta)=L^{m(\beta)}.$$</div>
<p>If the set defining $m(\beta)$ is empty, take $m(\beta)=\xi(\beta)=\infty$. The thresholds exist: $r_n$ is continuous on $[0,b]$ by domination by $bJ$, and strictly increasing; $\chi_n$ is continuous and nondecreasing, and is at least one. Thus their product is continuous and strictly increasing, starts at zero and is at least one at $b$.</p>

<a id="tag-6F2J" data-assertion="proposition" data-title="Finite-ball control at the hierarchical boundary thresholds"></a>
<p>Under the preceding assumptions, $\chi(\beta)\leq2\chi_n(\beta)$ whenever $0\leq\beta\leq\beta_n$. There are constants $c_0,C_0&gt;0$, independent of $n$ and $\beta$, such that</p>
<div class="math-display">$$c_0L^{\alpha n}\leq\chi_n(\beta)\leq\chi_n(b)\leq C_0L^{\alpha n}
\qquad(b_n\leq\beta\leq b).$$</div>
<p>If $b_n\leq\beta\leq b_{n+1}$, then also $\chi(\beta)\leq2C_0L^\alpha L^{\alpha n}$.</p>
<p><em>Proof.</em> The first estimate is a first-exit bound in a finite volume, where rearrangement is legitimate. For $N\geq n$, split a simple path in $\Lambda_N$ at its first exit from $\Lambda_n$. The internal path, exit edge and remaining path have disjoint edge witnesses. BK, a union bound and translation invariance within $\Lambda_N$ give</p>
<div class="math-display">$$\chi_N(\beta)\leq\chi_n(\beta)+\varphi_\beta(\Lambda_n)\chi_N(\beta).$$</div>
<p>The boundary sum may include vertices outside $\Lambda_N$; enlarging it only increases the right side. If $\beta\leq\beta_n$, its coefficient is at most $1/2$, so $\chi_N(\beta)\leq2\chi_n(\beta)$. Internal connection events increase to full connection events as $N\to\infty$, since each path is finite. Monotone convergence proves the full susceptibility bound without assuming it finite in advance.</p>
<p>Shell summation of the endpoint upper bound gives $\chi_n(b)\leq C_0L^{\alpha n}$. Also</p>
<div class="math-display">$$r_n(\beta)\leq b\sum_{y\notin\Lambda_n}J(y)\leq D L^{-\alpha n},\qquad
D=\frac{bC_J(1-L^{-d})}{L^\alpha-1}.$$</div>
<p>For $\beta\geq b_n\geq\beta_n$, the boundary coefficient is at least $1/2$, so $\chi_n(\beta)\geq(2D)^{-1}L^{\alpha n}$. Finally, if $\beta\leq b_{n+1}$, some $k\leq n+1$ attains that maximum. The first estimate at $k$ gives $\chi(\beta)\leq2\chi_k(b)\leq2C_0L^{\alpha(n+1)}$.</p>

## The rate of approach to the endpoint {#section-off-critical}

<a id="tag-OVWJ" data-assertion="theorem" data-title="Hierarchical susceptibility and length bounds from endpoint inputs"></a>
<p>Retain the model and both endpoint conditions of <a href="#section-boundary-scales">the boundary-scale section</a>, and assume $\alpha&lt;2d/5$. Then $b_n\uparrow b$, $\xi(\beta)&lt;\infty$ for $0\leq\beta&lt;b$, and</p>
<div class="math-display">$$\chi(\beta)\asymp\xi(\beta)^\alpha\qquad(\beta\uparrow b).$$</div>
<p>With $\varepsilon=b-\beta$, the upper bounds are</p>
<div class="math-display">$$\begin{array}{c|c|c}
\text{range}&\xi(b-\varepsilon)&\chi(b-\varepsilon)\\ \hline
0&lt;\alpha&lt;d/3&O(\varepsilon^{-1/\alpha})&O(\varepsilon^{-1})\\
\alpha=d/3&O(\varepsilon^{-1/\alpha}(\log(1/\varepsilon))^{2/\alpha})
&O(\varepsilon^{-1}(\log(1/\varepsilon))^2)\\
d/3&lt;\alpha&lt;2d/5&O(\varepsilon^{-1/(2d-5\alpha)})
&O(\varepsilon^{-\alpha/(2d-5\alpha)}).
\end{array}$$</div>
<p>All constants are independent of sufficiently small $\varepsilon&gt;0$. If $R=\sum_{x\ne0}J(x)$, then also $\chi(b-\varepsilon)\geq1/(R\varepsilon)$, so $\xi(b-\varepsilon)\geq c\varepsilon^{-1/\alpha}$ near $b$. These conclusions do not presuppose that $b$ has been identified as the critical parameter.</p>
<p><em>Proof.</em> Let $\Delta_n(\beta)$ be the triangle diagram of the internal connection kernel on $\Lambda_n$. The endpoint upper bound and the upper shell estimate in <a href="/tag/MS6M/">MS6M</a> imply, uniformly for $0\leq\beta\leq b$,</p>
<div class="math-display">$$1\leq\Delta_n(\beta)\leq C_1 H_n,\qquad
H_n=\begin{cases}1,&3\alpha&lt;d,\\ n+1,&3\alpha=d,\\
L^{(3\alpha-d)n},&3\alpha&gt;d.\end{cases}$$</div>
<p>Indeed, the internal kernel is bounded by the full endpoint kernel, which is bounded by $A\langle x-y\rangle^{-d+\alpha}$; apply that deterministic estimate to this last function. Since $\alpha&lt;2d/5&lt;d/2$, $H_n=o(L^{\alpha n})$. The preceding lemma therefore gives $\Delta_n(\beta)\leq\chi_n(\beta)/2$ for all sufficiently large $n$, uniformly on $b_n\leq\beta\leq b$.</p>
<p>Each ball is a finite group under translation, so its invariant law has the mass-transport property and finite susceptibility. To use <a href="/tag/4KBG/">the corrected quadratic inequality</a> without a normalization assumption, set $\kappa=\max(1,R)$ and apply it to weights $J/\kappa$ at parameter $t=\kappa\beta$. The chain rule supplies</p>
<div class="math-display">$$\chi_n'(\beta)\geq
\frac{(\chi_n(\beta)-\Delta_n(\beta))_+^2}
{3\kappa\beta^2\Delta_n(\beta)^2}
\geq c_1\frac{L^{2\alpha n}}{H_n^2}
\qquad(b_n\leq\beta\leq b)$$</div>
<p>almost everywhere, for all sufficiently large $n$. The finite internal row sum is positive when $n\geq1$ and at most $R$, as required after scaling. Integrating and using $\chi_n(b)\leq C_0L^{\alpha n}$ yields</p>
<div class="math-display">$$0&lt;b-b_n\leq C_2 H_n^2L^{-\alpha n}.$$
</div>
<p>The right side tends to zero: in the last regime its exponential rate is $2d-5\alpha&gt;0$. Thus $b_n\uparrow b$. Moreover each $b_n&lt;b$, so $m(\beta)\to\infty$ as $\beta\uparrow b$.</p>
<p>For $m=m(\beta)\geq1$, minimality gives $b_{m-1}&lt;\beta\leq b_m$. The preceding lemma at $m-1$, and at a maximizing index $k\leq m$, gives</p>
<div class="math-display">$$c_0L^{\alpha(m-1)}\leq\chi(\beta)\leq2C_0L^{\alpha m}.$$</div>
<p>This proves the comparison with $\xi^\alpha$. Also $\varepsilon&lt;b-b_{m-1}\leq C_2H_{m-1}^2L^{-\alpha(m-1)}$. In the first and third regimes this directly bounds $L^m$ by the stated power of $\varepsilon^{-1}$.</p>
<p>At $3\alpha=d$, it instead gives $\varepsilon\leq C_3m^2e^{-cm}$, where $c=\alpha\log L&gt;0$. Taking logarithms and using $2\log m\leq cm/2$ for large $m$ shows $m=O(\log(1/\varepsilon))$. Returning to the same inequality now gives $L^{\alpha m}\leq C_4\varepsilon^{-1}(\log(1/\varepsilon))^2$, proving the borderline bounds.</p>
<p>Finally $\varphi_b(\Lambda_n)\geq1$ and the bound on $r_n(b)$ force $\chi_n(b)\to\infty$, hence $\chi(b)=\infty$. If $R\varepsilon\chi(b-\varepsilon)&lt;1$, adding an independent intensity-$\varepsilon$ layer would keep susceptibility finite by <a href="/tag/MLLO/">MLLO</a>: its probability row sum is at most $R\varepsilon$. The union has the law at $b$, a contradiction. This proves the lower susceptibility bound and, by the comparison already established, the lower length bound.</p>
<p>The proof uses the squared positive part throughout. Its separation from the triangle diagram is proved before the derivative is bounded below by a multiple of $\chi_n^2/\Delta_n^2$.</p>

## Cluster tails and density {#section-off-critical-tails}

<a id="tag-WPAD" data-assertion="corollary" data-title="Hierarchical tail and density upper bounds near the triangle threshold"></a>
<p>Retain the model and both endpoint conditions of <a href="#section-boundary-scales">the boundary-scale section</a>. If $0&lt;\alpha&lt;4d/11$, the following bounds hold as $N\to\infty$ and $\varepsilon\downarrow0$:</p>
<div class="math-display">$$\begin{array}{c|c|c}
\text{range}&\mathbb P_b(|K_o|\geq N)&\mathbb P_{b+\varepsilon}(|K_o|=\infty)\\ \hline
0&lt;\alpha&lt;d/3&O(N^{-1/2})&O(\varepsilon)\\
\alpha=d/3&O(N^{-1/2}(\log N)^2)&O(\varepsilon(\log(1/\varepsilon))^2)\\
d/3&lt;\alpha&lt;4d/11&
O(N^{-(4d-11\alpha)/(4d-10\alpha)})&
O(\varepsilon^{(4d-11\alpha)/(2d-5\alpha)}).
\end{array}$$</div>
<p>In particular there is no infinite cluster at $b$.</p>
<p><em>Proof.</em> The weight row sum is finite. Apply <a href="/tag/X8T6/">the power-law susceptibility comparison</a> to OVWJ, with $(\gamma,a)=(1,0)$ below the triangle threshold, $(1,2)$ at the threshold, and $(\alpha/(2d-5\alpha),0)$ above it. In the last case $\gamma&lt;2$ is exactly $\alpha&lt;4d/11$, and $2-\gamma=(4d-11\alpha)/(2d-5\alpha)$.</p>
<p>For radial kernels, taking $b=\beta_c$ and using <a href="/tag/W498/">the critical two-point input</a> together with <a href="/tag/FF30/">the critical boundary-flux input</a> supplies the upper bounds in Theorems 1.9 and 4.1 of <a href="https://arxiv.org/html/2106.06400v3#S4">the triangle paper</a>. The arguments here prove the implications from those inputs. They do not improve the logarithmic powers, establish exponent limits or give matching lower tail and density estimates.</p>



## Exact block layers {#section-exact-model}

<p><em>Main article: <a href="/articles/hierarchical-block-coalescent/">Exact block layers of hierarchical percolation</a>.</em></p>
<p>Fix integers $L\geq2$, $d\geq1$, an exponent $\alpha&gt;0$ and an intensity $\beta\geq0$. Write $s=d+\alpha$, $Q=L^d$, and let $h(x,y)$ be the least level of a block containing distinct vertices $x,y$ of $\mathbb H_L^d$. Thus $\|x-y\|=L^{h(x,y)}$. By the <a href="/tag/VI3Y/">layer decomposition</a>, percolation at intensity $\beta$ with the exact radial kernel $J_\infty(x,y)=\frac{L^s}{L^s-1}\|x-y\|^{-s}$ is the union of independent layers, one for each finite block; the layer of an $n$-block is independent percolation on the complete graph on that block with edge probability $1-e^{-t_n}$, where $t_n=\beta L^{-sn}$. The union $\eta_B$ of the layers of the blocks inside $B$ is the truncated block law. Its clusters are contained in the intersections of the full clusters with $B$, which may also contain vertices reached by paths leaving $B$.</p>
<p>Inside an $n$-block, start from the terminal cluster partitions of its $Q$ children and run the parent layer for time $t\in[0,t_n]$. The resulting partition $X_{n,t}$ is a <a href="/articles/multiplicative-coalescent/">finite multiplicative coalescent</a>, and its terminal state is the cluster partition of $\eta_{B_n}$. By <a href="/tag/54V4/">independent-child gluing</a>, its power sums $S_p(n,t)=\sum_{A\in X_{n,t}}|A|^p$ start each level as sums over $Q$ independent children, and the cluster $K_{n,t}(o)$ of the root satisfies $\mathbb E|K_{n,t}(o)|^q=Q^{-n}\mathbb ES_{q+1}(n,t)$. Let $Z_{n,t}$ be the largest cluster size, $Z_n=Z_{n,t_n}$ its terminal value, $M_n$ the integer quantile of $Z_n$ and $\mu_n(t)=\mathbb ES_2(n,t)$. The <a href="/tag/X2A4/">uniform moment control</a> bounds the expected power sums by $\mu_n$ and powers of $M_n$ and gives the mean equation $\mu_n'=(1-\epsilon_n)\mu_n^2$ with $0\leq\epsilon_n\leq\min\{1,CM_n^2/\mu_n\}$.</p>

## The finite multiplicative coalescent {#section-coalescent-summary}

<p><em>Main article: <a href="/articles/multiplicative-coalescent/">The finite multiplicative coalescent</a>.</em></p>
<p>In a finite multiplicative coalescent two blocks of sizes $a$ and $b$ merge at rate $ab$; its <a href="/tag/Z960/">generator</a> $\mathcal L$ is a finite matrix. The <a href="/tag/22H8/">moment equations</a> give exact equations for all mixed moments of the power sums, for example $\frac{d}{dt}\mathbb ES_2=\mathbb E(S_2^2-S_4)$ and $\frac{d}{dt}\mathbb ES_3=3\mathbb E(S_2S_3-S_5)$. On a set of $N$ points the expectations of the products of $S_2,\ldots,S_N$ <a href="/tag/W8PB/">determine the law of the block sizes</a>.</p>

## The periodic block kernel {#section-periodic-kernel-summary}

<p><em>Main article: <a href="/articles/hierarchical-block-coalescent/#section-periodic-block-kernel">Exact block layers of hierarchical percolation</a>.</em></p>
<p>Periodizing the exact kernel on an $n$-block, by summing it over the fibres of the projection of $\mathbb H$ onto $B_n$ that forgets the coordinates above $n$, adds the constant $\frac{q}{1-q}L^{-(d+\alpha)n}$ to the truncated kernel, where $q=L^{-\alpha}$. Periodic percolation on $B_n$ is independent bond percolation on $B_n$ with edge probabilities $1-\exp(-\beta J_n^{\mathrm{per}}(x,y))$ for this periodized kernel $J_n^{\mathrm{per}}$. By the <a href="/tag/YY9S/">periodic-kernel identity</a>, it has the cluster law of the block process with its last coalescent stage run to time $\beta L^{-(d+\alpha)n}/(1-q)$.</p>



## Critical means for the truncated block law {#section-critical-block-means}

<p>For the rest of this article, use the exact kernel and block layers of <a href="/tag/VI3Y/">VI3Y</a>, with $0&lt;\alpha&lt;d$ and $\beta=\beta_c$. Thus $s=d+\alpha$, $Q=L^d$ and $t_n=\beta_cL^{-sn}$. Write $K_n(o)$ for the terminal cluster of $o$ in $\eta_{B_n}$ and $\chi_n=\mathbb E|K_n(o)|$. Retain the terminal maximum $Z_n$, its integer quantile $M_n$, and $\mu_n(t)=\mathbb E S_2(n,t)$ from <a href="/tag/X2A4/">X2A4</a>. Constants in the following estimates may depend on $L,d,\alpha$.</p>

<a id="tag-2VXH" data-assertion="theorem" data-title="Critical truncated-block mean and maximum estimates"></a>
<p>The critical intensity is finite and positive, and there are constants $c,C&gt;0$ such that, for every $n\geq0$,</p>
<div class="math-display">$$cL^{\alpha n}\leq\chi_n\leq CL^{\alpha n},\qquad
M_n\leq CL^{sn/2},\qquad
cL^{sn}\leq\mu_n(t)\leq CL^{sn}\quad(0\leq t\leq t_n).$$</div>
<p>In particular the error and relative variance satisfy</p>
<div class="math-display">$$\epsilon_n(t)+\frac{\operatorname{Var}(S_2(n,t))}{\mu_n(t)^2}
\leq C M_n^2L^{-sn}.$$</div>
<p><em>Proof.</em> The exact kernel is symmetric, summable and bounded above and below by positive multiples of $\|x-y\|^{-s}$. Hence <a href="/tag/FF30/">the critical-intensity and boundary-flux theorem</a> applies. Let $a_n$ be the mean root-cluster size in the induced full graph $\omega[B_n]$, and let $R_n$ be its maximum quantile. That theorem, followed by <a href="/tag/655W/">the expected-size recursion</a> with the <a href="/tag/12NL/">rooted damping bound</a>, gives</p>
<div class="math-display">$$0&lt;\beta_c&lt;\infty,\qquad R_n^2\leq C L^{sn},\qquad a_n\leq C L^{\alpha n}.$$</div>
<p>For $u\in B_n$, shell counting gives the exact exterior weight</p>
<div class="math-display">$$\sum_{v\notin B_n}J_\infty(u,v)=D L^{-\alpha n},\qquad
D=\frac{L^s}{L^s-1}\frac{1-L^{-d}}{L^\alpha-1}.$$</div>
<p>Indeed the shell at level $m&gt;n$ has $(1-L^{-d})L^{dm}$ vertices, each with weight $L^sL^{-sm}/(L^s-1)$. The boundary-flux inequality is therefore $\beta_c D L^{-\alpha n}a_n\geq1$, so</p>
<div class="math-display">$$a_n\geq\frac{L^{\alpha n}}{\beta_c D}.$$</div>
<p>The lower bound must still be transferred to $\eta_{B_n}$, which omits the ancestor layers. By VI3Y, adding an independent uniform layer to $\eta_{B_n}$ gives $\omega[B_n]$. Its probability row sum is</p>
<div class="math-display">$$\delta_n=(L^{dn}-1)\left(1-\exp\left[-\frac{\beta_cL^{-sn}}{L^s-1}\right]\right)
\leq E L^{-\alpha n},\qquad E=\frac{\beta_c}{L^s-1}.$$</div>
<p>Translations within the block preserve the truncated law, so every red susceptibility in this coupling equals $\chi_n$. If $E L^{-\alpha n}\chi_n\geq1/2$, then $\chi_n\geq L^{\alpha n}/(2E)$. Otherwise $\delta_n\chi_n&lt;1/2$, and <a href="/tag/MLLO/">the independent-layer comparison</a> gives $a_n\leq\chi_n/(1-\delta_n\chi_n)\leq2\chi_n$. Thus in both cases</p>
<div class="math-display">$$\chi_n\geq\min\left\{\frac1{2E},\frac1{2\beta_c D}\right\}L^{\alpha n}.$$</div>
<p>The same coupling gives $\chi_n\leq a_n$ and $M_n\leq R_n$, proving the remaining terminal bounds. The <a href="/tag/54V4/">rooted identity and child gluing</a> give $\mu_n(t_n)=L^{dn}\chi_n$ and, for $n\geq1$,</p>
<div class="math-display">$$Q\mu_{n-1}(t_{n-1})=\mu_n(0)\leq\mu_n(t)\leq\mu_n(t_n).$$</div>
<p>These prove the bounds on $\mu_n$ uniformly in time; at $n=0$ it is identically one. Finally apply X2A4 and the lower bound on $\mu_n$ to obtain the error and variance estimate.</p>
<p>This supplies the truncated-law input in Theorem 4.1 and (4.4) of the <a href="/coverage/sources/hierarchical-volumes-2211.05686v1/">hierarchical-volume paper</a>. In particular, the lower mean estimate does not rely on identifying the truncated law with the full law restricted to the block.</p>

## The maximum above the critical dimension {#section-high-dimensional-maximum}

<a id="tag-6WO3" data-assertion="theorem" data-title="A tree-graph maximum bound and high-dimensional hydrodynamics"></a>
<p>In the critical exact model just specified,</p>
<div class="math-display">$$M_n\leq C(n+1)L^{2\alpha n}\qquad(n\geq0).$$</div>
<p>If $d&gt;3\alpha$, then the hydrodynamic condition holds:</p>
<div class="math-display">$$M_nL^{-sn/2}\longrightarrow0.$$</div>
<p>More precisely, with $\gamma=d-3\alpha&gt;0$,</p>
<div class="math-display">$$\sup_{0\leq t\leq t_n}\left(\epsilon_n(t)+\frac{\operatorname{Var}(S_2(n,t))}{\mu_n(t)^2}\right)
\leq C(n+1)^2L^{-\gamma n}.$$</div>
<p>Consequently $S_2(n,t)/\mu_n(t)\to1$ in every fixed finite $L^r$, uniformly in $t$.</p>
<p><em>Proof.</em> In a terminal block every rooted mean equals $\chi_n$. The <a href="/tag/XLWI/">tree-graph exponential bound</a> gives, for every real $m&gt;0$,</p>
<div class="math-display">$$\mathbb P(|K_n(o)|\geq m)\leq\frac{\sqrt2\chi_n}{m}\exp\left[-\frac{m}{4\chi_n^2}\right].$$</div>
<p>A union bound over the $L^{dn}$ possible roots and 2VXH therefore yield</p>
<div class="math-display">$$\mathbb P(Z_n\geq m)\leq\frac{\sqrt2 C L^{sn}}{m}\exp\left[-\frac{m}{4C^2L^{2\alpha n}}\right],$$</div>
<p>where $C\geq1$. Take $m=\lceil B(n+1)L^{2\alpha n}\rceil$. Choosing $B$ so that $B/(4C^2)\geq s\log L+\log(\sqrt2 C)+1$ makes the last bound at most $e^{-1}$ for every $n$, even after discarding $1/m\leq1$. This proves the quantile estimate, including the singleton level after enlarging its constant.</p>
<p>When $d&gt;3\alpha$, it gives</p>
<div class="math-display">$$M_nL^{-sn/2}\leq C(n+1)L^{-(d-3\alpha)n/2}\longrightarrow0.$$</div>
<p>The quantitative error and variance bounds now follow from 2VXH. The fixed-$L^r$ concentration follows from X2A4.</p>
<p>This proves Proposition 4.2 and its concentration consequence for the exact law. At $d=3\alpha$ the displayed maximum bound does not establish hydrodynamics; that case requires a further argument.</p>

## The reciprocal mean and its amplitude {#section-reciprocal-mean}

<a id="tag-W2VN" data-assertion="theorem" data-title="Exact reciprocal-mean series and the critical first-moment amplitude"></a>
<p>Retain the same critical model and put</p>
<div class="math-display">$$q=L^{-\alpha},\qquad A=\frac1{1-q}=\frac{L^\alpha}{L^\alpha-1},\qquad
\overline\epsilon_n=\frac1{t_n}\int_0^{t_n}\epsilon_n(v)\,dv.$$</div>
<p>For every $n\geq0$ and $0\leq t\leq t_n$, define</p>
<div class="math-display">$$R_n(t)=\frac1{t_n}\int_t^{t_n}\epsilon_n(v)\,dv
+\sum_{m=1}^{\infty}q^m\overline\epsilon_{n+m}.$$</div>
<p>This series converges absolutely, $R_n(t)\geq0$, and the following identity has a strictly positive denominator:</p>
<div class="math-display">$$\mu_n(t)=\frac{L^{sn}}{\beta_c\left(A-t/t_n-R_n(t)\right)}.$$</div>
<p>In particular, without a hydrodynamic assumption,</p>
<div class="math-display">$$\mu_n(t)\geq\frac{L^{sn}}{\beta_c(A-t/t_n)},\qquad
\chi_n\geq\frac{L^\alpha-1}{\beta_c}L^{\alpha n}.$$</div>
<p>If $M_n=o(L^{sn/2})$, then</p>
<div class="math-display">$$\mu_n(t)\sim\frac{L^{sn}}{\beta_c(A-t/t_n)}\quad\text{uniformly for }0\leq t\leq t_n,\qquad
\chi_n\sim\frac{L^\alpha-1}{\beta_c}L^{\alpha n}.$$</div>
<p>For $d&gt;3\alpha$, these equivalents hold unconditionally and, uniformly in $t$ for all sufficiently large $n$,</p>
<div class="math-display">$$0\leq\frac{\beta_c(A-t/t_n)\mu_n(t)}{L^{sn}}-1
\leq C(n+1)^2L^{-(d-3\alpha)n}.$$</div>
<p><em>Proof.</em> Since $\mu_n(t)&gt;0$, the mean equation in X2A4 gives $(1/\mu_n)'=-1+\epsilon_n$. Set $U_n=L^{sn}/\mu_n(0)$. Integrating over the level-$n$ time interval and using $\mu_{n+1}(0)=Q\mu_n(t_n)$ gives</p>
<div class="math-display">$$U_n=\beta_c(1-\overline\epsilon_n)+qU_{n+1}.$$</div>
<p>Iterating this equality yields, for every integer $k\geq0$,</p>
<div class="math-display">$$U_n=\beta_c\sum_{m=0}^k q^m(1-\overline\epsilon_{n+m})+q^{k+1}U_{n+k+1}.$$</div>
<p>The lower mean bound in 2VXH makes $U_j$ bounded above uniformly in $j$. Hence the last term tends to zero. Also $0\leq\overline\epsilon_j\leq1$, so the series is dominated by a geometric series. We obtain</p>
<div class="math-display">$$U_n=\beta_c\sum_{m=0}^{\infty}q^m(1-\overline\epsilon_{n+m}).$$</div>
<p>A second integration, now from zero to $t$, gives</p>
<div class="math-display">$$\begin{aligned}
\frac{L^{sn}}{\mu_n(t)}
&amp;=U_n-L^{sn}t+L^{sn}\int_0^t\epsilon_n(v)\,dv\\
&amp;=\beta_c\left(A-\frac{t}{t_n}-\frac1{t_n}\int_t^{t_n}\epsilon_n(v)\,dv
-\sum_{m=1}^{\infty}q^m\overline\epsilon_{n+m}\right).
\end{aligned}$$</div>
<p>This proves the identity and its denominator's positivity. Since $R_n(t)\geq0$ and $A-t/t_n\geq A-1&gt;0$, dropping $R_n(t)$ gives the lower bound. At $t=t_n$, divide by $L^{dn}$ and use $A-1=(L^\alpha-1)^{-1}$ to obtain the bound for $\chi_n$.</p>
<p>Under the hydrodynamic condition, 2VXH gives $e_n:=\sup_{0\leq t\leq t_n}\epsilon_n(t)\to0$. The exact error satisfies</p>
<div class="math-display">$$0\leq R_n(t)\leq\sum_{m=0}^{\infty}q^m e_{n+m}
\leq A\sup_{j\geq n}e_j\longrightarrow0.$$</div>
<p>The baseline denominator is bounded below by $A-1$, uniformly in $t$. Thus the relative error is $R_n(t)/(A-t/t_n-R_n(t))$, which tends to zero uniformly. For $d&gt;3\alpha$, 6WO3 gives $e_j\leq C(j+1)^2L^{-\gamma j}$, where $\gamma=d-3\alpha$. Therefore</p>
<div class="math-display">$$R_n(t)\leq C(n+1)^2L^{-\gamma n}\sum_{m=0}^{\infty}(m+1)^2(qL^{-\gamma})^m
\leq C'(n+1)^2L^{-\gamma n}.$$</div>
<p>Here $n+m+1\leq(n+1)(m+1)$ and the last series converges. Substitution into the relative error proves the quantitative assertion.</p>
<p>This proves Lemma 4.10 and Corollaries 4.11 and 4.13 of the source, including the bound needed to discard the terminal reciprocal in the recursion. At the initial time, the corresponding coefficient of $L^{\alpha n}$ in $L^{-dn}\mu_n(0)$ is $(L^\alpha-1)/(L^\alpha\beta_c)$; at the terminal time it is $(L^\alpha-1)/\beta_c$. The latter is the coefficient for the source's $K_n$. The arXiv statements of Theorems 1.4 and 1.6 print the former coefficient even for $p=1$, in conflict with the exact lower bound above. This is recorded as a <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional first-moment correction</a>. No correction to all higher-moment constants, no journal-version agreement and no proof of hydrodynamics at $d=3\alpha$ is asserted here.</p>



## The second rooted moment {#section-second-moment}

<p>Continue with the critical exact block model of <a href="/tag/2VXH/">2VXH</a>. Write $f_{p,n}(t)=\mathbb E S_p(n,t)$, so that $\mu_n=f_{2,n}$, and put $\nu_n=f_{3,n}$. By the rooted identity, $L^{-dn}\nu_n(t_n)=\mathbb E|K_n(o)|^2$. Set $q=L^{-\alpha}$, $A=(1-q)^{-1}$ and $\phi(u)=1-u/A$ for $0\leq u\leq1$; thus $\phi(1)=q$.</p>

<a id="tag-I7HB" data-assertion="theorem" data-title="Second-moment growth and its high-dimensional amplitude"></a>
<p>If the hydrodynamic condition $M_n=o(L^{(d+\alpha)n/2})$ holds, then, uniformly in $0\leq t\leq t_n$,</p>
<div class="math-display">$$\frac{\nu_n(t)}{\nu_n(0)}\sim\phi(t/t_n)^{-3},\qquad
\nu_n(t)=L^{(d+3\alpha)n+o(n)}.$$</div>
<p>If $d&gt;3\alpha$, there is a constant $B\in(0,\infty)$ such that, with $\gamma=d-3\alpha$,</p>
<div class="math-display">$$\nu_n(t)=B\phi(t/t_n)^{-3}L^{(d+3\alpha)n}
\left(1+O\!\left((n+1)^2L^{-\gamma n}\right)\right)$$</div>
<p>uniformly in $t$. In particular,</p>
<div class="math-display">$$\mathbb E|K_n(o)|^2\sim B L^{3\alpha}L^{3\alpha n}.$$</div>
<p>When $d&lt;3\alpha$, the hydrodynamic condition cannot hold.</p>
<p><em>Proof.</em> The exact equation in <a href="/tag/22H8/">22H8</a> is</p>
<div class="math-display">$$\nu_n'=3\mathbb E(S_2S_3-S_5)=3(1-\epsilon_{3,n})\mu_n\nu_n,\qquad
\epsilon_{3,n}=\frac{f_{5,n}-\operatorname{Cov}(S_2,S_3)}{\mu_n\nu_n}.$$</div>
<p>The <a href="/tag/25Z4/">covariance comparison</a> and <a href="/tag/X2A4/">fixed-index moment bound</a> give</p>
<div class="math-display">$$0\leq\epsilon_{3,n}(t)\leq\frac{f_{5,n}(t)}{\mu_n(t)\nu_n(t)}
\leq C\frac{M_n^2}{\mu_n(t)}.$$</div>
<p>Also $\epsilon_{3,n}\leq1$, since $S_2S_3\geq S_5$ pointwise. The lower mean in 2VXH makes this error uniformly $o(1)$ under hydrodynamics. For $d&gt;3\alpha$, <a href="/tag/6WO3/">6WO3</a> bounds it by $C(n+1)^2L^{-\gamma n}$.</p>
<p>Write the exact mean as</p>
<div class="math-display">$$\mu_n(t)=\frac{1+H_n(t)}{t_n(A-t/t_n)}.$$</div>
<p>By <a href="/tag/W2VN/">the reciprocal-mean theorem</a>, $H_n\geq0$ is uniformly $o(1)$ under hydrodynamics, and is $O((n+1)^2L^{-\gamma n})$ in high dimension. This bound uses the geometric tail of the mean errors, as well as the error in the current block.</p>
<p>Integrating the logarithmic derivative of $\nu_n$ gives the exact relation</p>
<div class="math-display">$$\nu_n(ut_n)=\nu_n(0)\phi(u)^{-3}\exp(D_n(u)),$$</div>
<div class="math-display">$$D_n(u)=3\int_0^u\frac{(1-\epsilon_{3,n}(vt_n))(1+H_n(vt_n))-1}{A-v}\,dv.$$</div>
<p>The integral of $(A-v)^{-1}$ over $[0,1]$ is $\log(A/(A-1))=\alpha\log L$. Hence $\sup_u|D_n(u)|\to0$ under hydrodynamics, and is $O((n+1)^2L^{-\gamma n})$ in high dimension. This proves the time ratio. Let $d_n=D_n(1)$. Child gluing now gives</p>
<div class="math-display">$$\nu_{n+1}(0)=L^{d+3\alpha}e^{d_n}\nu_n(0),\qquad
\nu_n(0)=L^{(d+3\alpha)n}\exp\left(\sum_{j=0}^{n-1}d_j\right),$$</div>
<p>since $\nu_0(0)=1$. If $d_j\to0$, their partial sums are $o(n)$, proving the growth exponent. In high dimension their absolute sum converges, so</p>
<div class="math-display">$$B=\exp\left(\sum_{j=0}^{\infty}d_j\right)\in(0,\infty).$$</div>
<p>The remaining tail is $O((n+1)^2L^{-\gamma n})$: use $n+m+1\leq(n+1)(m+1)$ and sum the resulting geometric series with a quadratic factor. Comparing the finite and infinite exponential products proves the quantitative equivalent. At $u=1$, $\phi(1)^{-3}=L^{3\alpha}$; divide by the block volume to obtain the rooted second moment.</p>
<p>Finally X2A4 and 2VXH always give</p>
<div class="math-display">$$\nu_n(t_n)\leq C M_n\mu_n(t_n)\leq C L^{3(d+\alpha)n/2}.$$</div>
<p>If $d&lt;3\alpha$, then $d+3\alpha&gt;3(d+\alpha)/2$, contradicting the growth exponent that hydrodynamics would imply. This proves failure of that condition, without asserting a pointwise lower bound on $M_n$.</p>
<p>This supplies Proposition 4.14 and Corollary 4.15 of the source. The high-dimensional display in Proposition 4.14 prints $d+\alpha$ where its proof requires $d+3\alpha$; the <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional errata</a> record this local correction.</p>

## Contraction of the higher-moment ratios {#section-higher-moment-ratios}

<a id="tag-ANYT" data-assertion="theorem" data-title="Higher hierarchical moments from a stable ratio equation"></a>
<p>Assume hydrodynamics in the same critical exact model. For every fixed integer $p\geq2$, set $a_p=(2p-5)!!$, with $a_2=(-1)!!=1$. Then</p>
<div class="math-display">$$f_{p,n}(t)\sim a_p\frac{\nu_n(t)^{p-2}}{\mu_n(t)^{p-3}}
=L^{(d+(2p-3)\alpha)n+o(n)}$$</div>
<p>uniformly for $0\leq t\leq t_n$. Constants and convergence rates may depend on $p$.</p>
<p><em>Proof.</em> The cases $p=2,3$ are identities. The coefficient calculation for the induction is</p>
<div class="math-display">$$\frac12\sum_{k=2}^{p-2}\binom pk a_{k+1}a_{p-k+1}=(p-3)a_p\qquad(p\geq4).$$</div>
<p>For completeness, the exponential generating series of $b_j=(2j-3)!!$ is $F(z)=1-\sqrt{1-2z}$. Its identity $F^2=2F-2z$ gives $\sum_{k=1}^{p-1}\binom pk b_k b_{p-k}=2b_p$. Removing the two endpoint terms $2p b_{p-1}$ gives the displayed identity, since $b_p=(2p-3)a_p$ and $b_{p-1}=a_p$.</p>
<p>Fix $p\geq4$ and assume the asserted equivalents for every smaller index. Suppress $n,t$ temporarily. The exact generator and covariance comparison let us write</p>
<div class="math-display">$$f_p'=(p-\eta_p)\mu f_p+T_p,\qquad
T_p=\frac12\sum_{k=2}^{p-2}\binom pk f_{k+1}f_{p-k+1},$$</div>
<div class="math-display">$$\eta_p=\frac{(2^{p-1}-1)f_{p+2}-\frac12\sum_{k=1}^{p-1}\binom pk
\operatorname{Cov}(S_{k+1},S_{p-k+1})}{\mu f_p},\qquad
0\leq\eta_p\leq C_p\frac{M_n^2}{\mu}.$$</div>
<p>Indeed each covariance lies between zero and $f_{p+2}$, and the binomial coefficients with their factor $1/2$ sum to $2^{p-1}-1$. The last bound follows from X2A4. Thus $\eta_p=o(1)$ uniformly in the block time.</p>
<p>Put $F_p=a_p\nu^{p-2}\mu^{-(p-3)}$ and $h_p=f_p/F_p$. The induction hypothesis and the coefficient identity give</p>
<div class="math-display">$$T_p=(p-3)(1+\delta_p)\mu F_p,\qquad \sup_{0\leq t\leq t_n}|\delta_{p,n}(t)|\longrightarrow0.$$</div>
<p>All factors in this sum have indices between three and $p-1$. In each product their powers of $\nu$ add to $p-2$ and their powers of $\mu$ to $-p+4$, which are the powers in $\mu F_p$. No estimate for the unknown $f_p$ is used in this step.</p>
<p>Use the exact logarithmic derivatives $\mu'/\mu=(1-\epsilon_n)\mu$ and $\nu'/\nu=3(1-\epsilon_{3,n})\mu$. If $z_p=h_p-1$ and $g=p-3&gt;0$, direct differentiation gives</p>
<div class="math-display">$$z_p'=\mu\bigl[(-g+b_p)z_p+r_p\bigr],$$</div>
<div class="math-display">$$b_p=-\eta_p-(p-3)\epsilon_n+3(p-2)\epsilon_{3,n},\qquad
r_p=b_p+(p-3)\delta_p.$$</div>
<p>Both $b_p$ and $r_p$ tend uniformly to zero. Also W2VN gives</p>
<div class="math-display">$$\int_0^{t_n}\mu_n(t)\,dt\longrightarrow\alpha\log L&gt;0.$$</div>
<p>The ratio has exact gluing: multiplying both $\mu$ and $\nu$ by $Q$ multiplies $F_p$ by $Q$, just as it multiplies $f_p$. Therefore $z_{p,n+1}(0)=z_{p,n}(t_n)$.</p>
<p>For all sufficiently large $n$, $|b_p|\leq g/2$. Variation of constants gives</p>
<div class="math-display">$$|z_{p,n+1}(0)|\leq\rho_n|z_{p,n}(0)|+e_n,\qquad
\rho_n=\exp\left(\int_0^{t_n}\mu_n(t)(-g+b_{p,n}(t))\,dt\right)
\longrightarrow L^{-(p-3)\alpha}&lt;1,$$</div>
<p>where $e_n\to0$: the integrating factors are at most one, so the forcing contribution is at most $\sup_t|r_{p,n}(t)|\int_0^{t_n}\mu_n(t)\,dt$. Choose $\rho&lt;1$ bounding $\rho_n$ for large $n$ and iterate. The initial contribution vanishes geometrically. The finitely many early forcing terms also vanish; the remaining sum is bounded by $(1-\rho)^{-1}$ times their supremum, which tends to zero. Hence $z_{p,n}(0)\to0$. The same variation-of-constants bound at every intermediate time proves uniform convergence there as well.</p>
<p>This completes the induction. Combining the equivalent with the mean growth in W2VN and the second-moment growth in I7HB gives the exponent $d+(2p-3)\alpha$.</p>
<p>The proof supplies Proposition 4.17 and its coefficient identity, Lemma 4.18. Its contraction is $L^{-(p-3)\alpha}$: the normalizing moment grows between scales by $L^{d+(2p-3)\alpha}$, while the homogeneous term grows by $L^{d+p\alpha}$. The source prints different exponents at this final step; both corrected exponents still give a strict contraction for $p\geq4$. The heuristic recursion preceding its formal proof also needs the factor $1/2$ retained above. These corrections are <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional</a>; the higher-moment conclusion is preserved.</p>

## Concentration of all fixed power sums {#section-all-moment-concentration}

<a id="tag-KPCV" data-assertion="corollary" data-title="Hierarchical power-sum concentration and mixed-moment factorization"></a>
<p>Under the hydrodynamic condition, for every fixed pair of integers $p,q\geq2$,</p>
<div class="math-display">$$\frac{f_{p+q,n}(t)}{f_{p,n}(t)f_{q,n}(t)}\longrightarrow0,\qquad
\frac{\mathbb E[S_p(n,t)S_q(n,t)]}{f_{p,n}(t)f_{q,n}(t)}\longrightarrow1.$$</div>
<p>For every fixed integer $p\geq2$ and every real $1\leq r&lt;\infty$,</p>
<div class="math-display">$$\frac{S_p(n,t)}{f_{p,n}(t)}\longrightarrow1\quad\text{in }L^r.$$</div>
<p>All limits are uniform over $0\leq t\leq t_n$. The same holds for any fixed finite product of normalized power sums, so all its mixed moments factor asymptotically.</p>
<p><em>Proof.</em> ANYT gives</p>
<div class="math-display">$$\frac{f_{p+q}}{f_pf_q}\sim\frac{a_{p+q}}{a_pa_q}\frac{\nu^2}{\mu^3}.$$</div>
<p>By X2A4, $\nu\leq C M_n\mu$; by 2VXH and hydrodynamics, $M_n^2/\mu\to0$ uniformly. This proves the first limit. The covariance comparison gives $0\leq\operatorname{Cov}(S_p,S_q)\leq f_{p+q}$, proving factorization and, with $q=p$, $L^2$ convergence.</p>
<p>For every fixed larger integer $k$, <a href="/tag/25TW/">the norm-moment bounds</a> uniformly bound $\mathbb E(S_p/f_p)^k$. Hölder and truncation therefore upgrade the $L^2$ limit to any fixed finite $L^r$. For a finite product, subtract one by a telescoping expansion and apply Hölder to each term, using sufficiently high fixed moments of the other factors. This also proves uniform convergence in $L^r$ of the product, and its expectation tends to one. Repeated power-sum indices are permitted.</p>
<p>This proves Corollary 4.19 and its fixed-index moment extension. It does not give a uniform statement as the indices grow with the block scale.</p>

## Rooted moments and the volume-biased law {#section-rooted-moment-equivalents}

<a id="tag-FY23" data-assertion="theorem" data-title="Critical rooted moment equivalents and a squared-normal volume-biased limit"></a>
<p>Let $T_n=|K_n(o)|$, $m_{k,n}=\mathbb E T_n^k$ and $\zeta_n=m_{2,n}/m_{1,n}$. Under hydrodynamics, for every fixed integer $k\geq1$,</p>
<div class="math-display">$$m_{k,n}\sim(2k-3)!!\,m_{1,n}\zeta_n^{k-1}.$$</div>
<p>Define a probability law $\widehat{\mathbb P}_n$ by $\widehat{\mathbb E}_n f(T_n)=\mathbb E[T_nf(T_n)]/m_{1,n}$. Then under this volume-biased law,</p>
<div class="math-display">$$T_n/\zeta_n\ \Longrightarrow\ N^2,$$</div>
<p>where $N$ is a standard normal variable.</p>
<p>For $d&gt;3\alpha$, hydrodynamics holds and there is a constant $D\in(0,\infty)$ such that</p>
<div class="math-display">$$m_{k,n}\sim(2k-3)!!\,c_1D^{k-1}L^{(2k-1)\alpha n},\qquad
c_1=\frac{L^\alpha-1}{\beta_c},\qquad D=\frac{B L^{3\alpha}}{c_1}.$$</div>
<p>Here $B$ is the positive amplitude in I7HB. Thus $\zeta_n\sim D L^{2\alpha n}$, and the same volume-biased limit holds with that deterministic scale.</p>
<p><em>Proof.</em> The <a href="/tag/54V4/">rooted identity</a> gives $m_{k,n}=L^{-dn}f_{k+1,n}(t_n)$. Substitute ANYT with $p=k+1$ and cancel the block-volume factors. The cases $k=1,2$ are exact identities. Under volume bias, for each fixed integer $j\geq1$,</p>
<div class="math-display">$$\widehat{\mathbb E}_n(T_n/\zeta_n)^j
=\frac{m_{j+1,n}}{m_{1,n}\zeta_n^j}\longrightarrow(2j-1)!!.$$</div>
<p>The <a href="/tag/0N85/">moment-determination theorem</a> therefore gives the squared-normal limit. Its tightness and uniform-integrability argument applies to the discrete sequence of scales without change.</p>
<p>In high dimension W2VN gives $m_{1,n}\sim c_1L^{\alpha n}$, while I7HB gives $m_{2,n}\sim B L^{3\alpha}L^{3\alpha n}$. Substitute these in the moment ratios. The deterministic scale is asymptotic to $\zeta_n$, so replacing the scale preserves weak convergence.</p>
<p>This completes the high-dimensional moment theorem with the terminal normalization made explicit. Relative to Theorem 1.4 of the arXiv source, the common prefactor is $c_1$ and the remaining moment constant is $D$. It extends the earlier first-moment repair to the full high-dimensional family. At $d=3\alpha$ the ratio and volume-biased conclusions still require hydrodynamics; neither its proof nor the critical second-moment logarithmic amplitude is supplied here.</p>



## The low-dimensional maximum at every scale {#section-low-dimensional-maximum}

<p>In the critical exact model, put $s=d+\alpha$ and $v_n=L^{sn/2}$. The quantity $v_n$ will be the cluster-volume scale; $Q^n=L^{dn}$ is the number of vertices in the block. Retain $\mu_n=\mathbb E S_2(n,\cdot)$, $\nu_n=\mathbb E S_3(n,\cdot)$, $q=L^{-\alpha}$ and $A=(1-q)^{-1}$.</p>

<a id="tag-Q8JZ" data-assertion="theorem" data-title="Low-dimensional maximum and block moments at every scale"></a>
<p>If $d/3&lt;\alpha&lt;d$, there are constants $c,C&gt;0$ such that</p>
<div class="math-display">$$cv_n\leq M_n\leq Cv_n\qquad(n\geq0).$$</div>
<p>For every fixed real $p\geq2$ there are $c_p,C_p&gt;0$ such that, uniformly in $n\geq0$ and $0\leq t\leq t_n$,</p>
<div class="math-display">$$c_pv_n^p\leq\mathbb E S_p(n,t)\leq C_pv_n^p.$$</div>
<p>Consequently, for every fixed real $r\geq1$,</p>
<div class="math-display">$$\mathbb E|K_n(o)|^r\asymp L^{(s(r+1)/2-d)n}.$$</div>
<p><em>Proof.</em> The upper maximum bound is <a href="/tag/2VXH/">2VXH</a>. The exact third-power equation, the covariance bound and <a href="/tag/X2A4/">the fixed-index estimates</a> give, without a hydrodynamic assumption,</p>
<div class="math-display">$$\frac{d}{dt}\log\nu_n(t)=3(1-\epsilon_{3,n}(t))\mu_n(t),\qquad
0\leq\epsilon_{3,n}(t)\leq C M_n^2/v_n^2.$$</div>
<p>Also $\nu_n(0)\leq C v_n^3$. Choose $0&lt;\delta\leq1$ so small that $C\delta^2\leq1/2$ and</p>
<div class="math-display">$$\lambda:=d+3\alpha(1-C\delta^2)&gt;3s/2.$$</div>
<p>Call a scale bad when $M_n\leq\delta v_n$. At each bad scale, <a href="/tag/W2VN/">the sharp lower mean bound</a> and its integral imply</p>
<div class="math-display">$$\nu_{n+1}(0)=Q\nu_n(t_n)\geq L^\lambda\nu_n(0),\qquad
\int_0^{t_n}\frac{dt}{t_n(A-t/t_n)}=\alpha\log L.$$</div>
<p>Scale zero is good, since $M_0=2&gt;\delta$. Consider any consecutive bad scales $a,\ldots,b$ whose preceding scale is good. The child bound in X2A4 gives</p>
<div class="math-display">$$\nu_a(0)\geq\frac{M_{a-1}^3}{8e}&gt;\frac{\delta^3}{8e}L^{3s(a-1)/2}.$$</div>
<p>Iterate across all $b-a+1$ bad scales, then use the unconditional upper bound at $b+1$. Writing $j=b-a+1$, we obtain</p>
<div class="math-display">$$\frac{\delta^3}{8e}L^{3s(a-1)/2}L^{\lambda j}
\leq\nu_{b+1}(0)\leq C L^{3s(b+1)/2},\qquad
L^{(\lambda-3s/2)j}\leq\frac{8eC}{\delta^3}L^{3s/2}.$$</div>
<p>Thus every bad run has length at most a fixed integer $N$, including every finite prefix of a putative infinite run. The clock coupling makes $M_n$ nondecreasing. Every scale $n$ has a good scale $m$ with $\max(0,n-N)\leq m\leq n$, so</p>
<div class="math-display">$$M_n\geq M_m&gt;\delta v_m\geq\delta L^{-sN/2}v_n.$$</div>
<p>This proves the pointwise lower bound.</p>
<p>For $p\geq3$, X2A4 gives $\mathbb E S_p\leq C_pM_n^{p-2}\mu_n\leq C_pv_n^p$. The case $p=2$ is 2VXH. For $2&lt;p&lt;3$, Hölder first over clusters and then over configurations gives</p>
<div class="math-display">$$\mathbb E S_p\leq(\mathbb E S_2)^{3-p}(\mathbb E S_3)^{p-2}\leq C_pv_n^p.$$</div>
<p>The lower moment bound for $n\geq1$ follows from $\mathbb E S_p(n,t)\geq M_{n-1}^p/(2^p e)$ and the maximum bound just proved. At $n=0$ all power sums equal one. Finally the rooted identity gives $\mathbb E|K_n(o)|^r=Q^{-n}\mathbb E S_{r+1}(n,t_n)$, also for real $r\geq1$.</p>
<p>This proves Theorem 5.1 and Corollary 5.2 of the source. The argument uses the previous good scale in the initial child estimate and the growth exponent $d+3\alpha(1-C\delta^2)$; the corresponding source bookkeeping has a <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional repair</a>.</p>

## Capping the rooted contribution {#section-capped-block-moments}

<a id="tag-RHK3" data-assertion="theorem" data-title="Capped block moments and backward propagation of a mean lower bound"></a>
<p>For the critical exact model with any $0&lt;\alpha&lt;d$ and real $m&gt;0$, define</p>
<div class="math-display">$$T_m(P)=\sum_{C\in P}|C|\min(|C|,m),\qquad
\tau_{n,m}(t)=\mathbb E T_m(X_{n,t}).$$</div>
<p>Then</p>
<div class="math-display">$$\tau_{n,m}'\leq\tau_{n,m}^2,\qquad
\tau_{n+1,m}(0)=Q\tau_{n,m}(t_n),\qquad
\tau_{n,m}(t_n)=Q^n\mathbb E\min(|K_n(o)|,m).$$</div>
<p>There is a constant $C$ independent of $n,m,t$ such that</p>
<div class="math-display">$$\nu_n'(t)\geq3\bigl(\tau_{n,m}(t)-Cm v_n\bigr)\nu_n(t).$$</div>
<p>For $0&lt;\varepsilon\leq1$ and $0&lt;\eta&lt;1$, choose an integer $N\geq0$ such that $q^N/\varepsilon\leq\eta/(1-\eta)$. If $\tau_{n,m}(t_n)\geq\varepsilon\mu_n(t_n)$, then for every $0\leq\ell\leq n-N$ and $0\leq t\leq t_\ell$,</p>
<div class="math-display">$$\tau_{\ell,m}(t)\geq\frac{1-\eta}{t_\ell(A-t/t_\ell)}.$$</div>
<p><em>Proof.</em> A merger of masses $a,b$ changes $T_m$ by</p>
<div class="math-display">$$\Delta_m(a,b)=(a+b)\min(a+b,m)-a\min(a,m)-b\min(b,m).$$</div>
<p>This is nonnegative and at most $2\min(a,m)\min(b,m)$. To check the upper bound, suppose $a\leq b$. If $a\geq m$, the increment is zero. If $a&lt;m\leq b$, it is $a(m-a)\leq am$. If $b&lt;m$ and $a+b\leq m$, it equals $2ab$. In the remaining case it is $m(a+b)-a^2-b^2\leq(a+b)^2-a^2-b^2=2ab$.</p>
<p>The finite generator therefore bounds $\tau_{n,m}'$ by the expected ordered distinct-cluster sum of $a\min(a,m)b\min(b,m)$. The <a href="/tag/25Z4/">distinct-cluster comparison</a> bounds this by $\tau_{n,m}^2$. Additivity over children gives gluing. Counting each vertex in its own cluster and using translation invariance gives the rooted identity, with the factor $Q^n$.</p>
<p>For the third-power drift, the exact generator and Harris give</p>
<div class="math-display">$$\begin{aligned}
\nu_n'&amp;=3\mathbb E\sum_{C\ne D}|C|^2|D|^3\\
&amp;\geq3\mathbb E\left[T_mS_3-\sum_C|C|^4\min(|C|,m)\right]\\
&amp;\geq3\tau_{n,m}\nu_n-3m\mathbb E S_4.
\end{aligned}$$</div>
<p>Here $T_m=\sum_x\min(|K(x)|,m)$ and $S_3$ are increasing functions of the bonds. X2A4 and 2VXH give $\mathbb E S_4\leq C M_n\nu_n\leq Cv_n\nu_n$, proving the asserted drift.</p>
<p>Since $\tau_{j,m}&gt;0$, its differential inequality implies $(1/\tau_{j,m})'\geq-1$. Set $U_j=L^{sj}/\tau_{j,m}(0)$. Integration and gluing give $U_j\leq\beta_c+qU_{j+1}$. A finite iteration, followed by integration backwards from the end of level $\ell$, yields for $0\leq\ell\leq n$</p>
<div class="math-display">$$\frac{L^{s\ell}}{\tau_{\ell,m}(t)}
\leq\beta_c\left(\sum_{j=0}^{n-\ell}q^j-\frac{t}{t_\ell}\right)
+q^{n-\ell+1}U_{n+1}.$$</div>
<p>The assumed terminal bound and W2VN give</p>
<div class="math-display">$$q^{n-\ell+1}U_{n+1}
=q^{n-\ell}\frac{L^{sn}}{\tau_{n,m}(t_n)}
\leq\frac{\beta_c(A-1)}{\varepsilon}q^{n-\ell}.$$</div>
<p>Consequently the reciprocal above is at most $\beta_c(A-t/t_\ell)+\beta_c(A-1)q^{n-\ell}/\varepsilon$. If $n-\ell\geq N$, this is at most $\beta_c(A-t/t_\ell)/(1-\eta)$, because $A-t/t_\ell\geq A-1$. Taking reciprocals proves the last assertion.</p>
<p>This proves Lemmas 5.4 and 5.6 and strengthens the parameter separation in Corollary 5.5. The cap may be any positive real number, including values below one. The source's capped-merger maximization, block-volume factor and mixed scale indices have <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional corrections</a>.</p>

## Small clusters carry little susceptibility {#section-mesoscopic-negligibility}

<a id="tag-L3QJ" data-assertion="theorem" data-title="Uniform negligibility of capped critical cluster volumes in low dimension"></a>
<p>Assume $d/3&lt;\alpha&lt;d$. For every $\varepsilon&gt;0$ there is $\delta&gt;0$ such that, for every $n\geq0$,</p>
<div class="math-display">$$\mathbb E\min(|K_n(o)|,\delta v_n)\leq\varepsilon\mathbb E|K_n(o)|.$$</div>
<p>In particular the same bound holds with the left side replaced by $\mathbb E[|K_n(o)|\mathbf1_{\{|K_n(o)|\leq\delta v_n\}}]$.</p>
<p><em>Proof.</em> It suffices to consider $0&lt;\varepsilon\leq1$. Choose</p>
<div class="math-display">$$\frac{d+3\alpha}{2\alpha}&lt;a&lt;3,\qquad
0&lt;\eta&lt;1-a/3,\qquad g=d+a\alpha-3s/2&gt;0.$$</div>
<p>Let $N$ be as in RHK3 for these $\varepsilon,\eta$. Its backward lower bound implies, whenever the terminal capped mean is at least $\varepsilon\mu_n(t_n)$, that</p>
<div class="math-display">$$\tau_{\ell,m}(t)\geq(1-\eta)G_\ell(t),\qquad
G_\ell(t)=\frac1{t_\ell(A-t/t_\ell)}\geq\frac{v_\ell^2}{\beta_c A}\quad(\ell\leq n-N).$$</div>
<p>Choose $b&gt;0$ with $3Cb\beta_c A\leq3(1-\eta)-a$, where $C$ is the drift constant in RHK3. At every such scale with $m\leq bv_\ell$, that drift gives $\nu_\ell'\geq aG_\ell\nu_\ell$. Integration and gluing imply</p>
<div class="math-display">$$\nu_{\ell+1}(0)\geq L^{d+a\alpha}\nu_\ell(0).$$</div>
<p>By Q8JZ, fix $c_3,C_3&gt;0$ such that $c_3v_j^3\leq\nu_j(0)\leq C_3v_j^3$ for every $j\geq0$. Choose an integer $J\geq1$ with $L^{gJ}&gt;C_3/c_3$. Such growth cannot hold over $J$ consecutive scales: iteration would contradict these two bounds.</p>
<p>Now take $\delta\leq bL^{-s(N+J)/2}$ and suppose $n\geq N+J$. If the claimed bound failed with $m=\delta v_n$, RHK3 would give the lower capped mean at every scale up to $n-N$. For $k=n-N-J$ and $k\leq\ell&lt;k+J$, we would also have $m\leq bv_k\leq bv_\ell$. The forbidden $J$ consecutive growth steps would follow.</p>
<p>It remains to choose $\delta$ for the finitely many smaller scales without assuming that the cap is at least one. Let $c_2v_n^2\leq\mu_n(t_n)$ be the uniform lower mean. Since $T_m\leq mQ^n$ pointwise,</p>
<div class="math-display">$$\frac{\tau_{n,\delta v_n}(t_n)}{\mu_n(t_n)}
\leq\frac{\delta}{c_2}L^{(d-\alpha)n/2}
\leq\frac{\delta}{c_2}L^{(d-\alpha)(N+J)/2}\quad(n&lt;N+J).$$</div>
<p>Reduce $\delta$ until this is at most $\varepsilon$. Divide the resulting capped-mean bound by $Q^n$ using RHK3. The indicator version follows pointwise from $x\mathbf1_{\{x\leq m\}}\leq\min(x,m)$.</p>
<p>This supplies Proposition 5.3, in the stronger capped form. The proof uses a fixed window of scales and treats all smaller scales explicitly, so no minimal-scale endpoint or integer rounding of the cap is left implicit.</p>

## The critical volume tail in low dimension {#section-low-dimensional-tail}

<a id="tag-ZDDE" data-assertion="theorem" data-title="Matching low-dimensional critical cluster-volume tails"></a>
<p>Assume $d/3&lt;\alpha&lt;d$ and put $\theta=(d-\alpha)/(d+\alpha)\in(0,1)$. If $T=|K(o)|$ is the full critical cluster volume and $T_n=|K_n(o)|$, there are positive constants $c,C,b$ such that</p>
<div class="math-display">$$c x^{-\theta}\leq\mathbb P(T\geq x)\leq Cx^{-\theta}\qquad(x\geq1),$$</div>
<div class="math-display">$$\mathbb P(T_n\geq x)\geq c x^{-\theta}\quad(1\leq x\leq bv_n),\qquad
\mathbb P(T_n\geq x)\leq Cx^{-\theta}\exp(-cx/v_n)\quad(x\geq1).$$</div>
<p>In particular all full critical clusters are finite almost surely.</p>
<p><em>Proof.</em> First count the vertices in large block clusters. The maximum quantile satisfies $M_n\geq2$ and $\mathbb P(Z_n\geq M_n-1)&gt;e^{-1}$. Hence</p>
<div class="math-display">$$\mathbb P(T_n\geq M_n/2)
=Q^{-n}\mathbb E\#\{x\in B_n:|K_n(x)|\geq M_n/2\}
\geq\frac{M_n}{2eQ^n}.$$</div>
<p>Q8JZ gives constants $b,c&gt;0$, with $b\leq1/2$, such that $\mathbb P(T_n\geq bv_n)\geq cv_n^{-\theta}$, since $Q^n=v_n^{1+\theta}$. For $x\geq1$, choose the least $j$ with $bv_j\geq x$. Then $v_j&lt;L^{s/2}x/b$. The nested-layer coupling gives $T_n\geq T_j$ whenever $j\leq n$, and $T\geq T_j$ always. This proves both lower bounds.</p>
<p>For the upper bound, partition the lattice into level-$n$ blocks and retain all layers within them. Their union is a red product configuration. All higher layers form an independent blue configuration, and red plus blue has the full law by <a href="/tag/VI3Y/">VI3Y</a>. The blue probability row sum is bounded by its intensity row:</p>
<div class="math-display">$$d_n\leq\beta_c\sum_{j&gt;n}(Q^j-1)L^{-sj}
\leq\frac{\beta_c}{L^\alpha-1}L^{-\alpha n}=:D L^{-\alpha n}.$$</div>
<p>Independently mark each vertex green with probability $1-e^{-h}$. Let $g(h)$ be the probability that the full root cluster meets a green vertex. For every cutoff $a&gt;0$,</p>
<div class="math-display">$$g(h)\leq\frac{\chi_n}{a}
+h\mathbb E[T_n\mathbf1_{\{T_n\leq a\}}]
+d_n\mathbb E[T_n\mathbf1_{\{T_n\leq a\}}]g(h),\qquad \chi_n=\mathbb E T_n.$$</div>
<p>Indeed the first term bounds $\mathbb P(T_n&gt;a)$. On $T_n\leq a$, a green mark in the red root cluster has conditional probability at most $hT_n$. If that cluster has no mark but the full cluster does, a finite witnessing path has a last exit from the red cluster. This exit must use a blue edge. Conditional on the red cluster's vertex set, red edges outside it retain their product law, blue edges remain independent, and marks outside remain independent. For each exit endpoint the probability of connection to a mark without entering the revealed cluster is at most $g(h)$, by adding back the omitted vertices and edges. Summing the crossing probabilities gives the last term. The summable blue row justifies this union bound even on the infinite lattice.</p>
<p>Choose $\varepsilon&gt;0$ so small that $D\varepsilon\chi_n L^{-\alpha n}\leq1/2$ uniformly in $n$, using 2VXH. Apply L3QJ to obtain a fixed $\delta&gt;0$, and set $a=\delta v_n$. The last term can be absorbed, giving</p>
<div class="math-display">$$g(h)\leq C\left(L^{-(d-\alpha)n/2}+hL^{\alpha n}\right).$$</div>
<p>For $0&lt;h\leq1$, choose the least $n\geq0$ with $v_n\geq h^{-1}$. Both terms are at most a constant times $h^\theta$, since $v_n&lt;L^{s/2}h^{-1}$. For $h&gt;1$, the same conclusion follows from $g(h)\leq1$. Finally</p>
<div class="math-display">$$\mathbb P(T\geq x)\leq\frac{g(1/x)}{1-e^{-1}}\leq Cx^{-\theta}.$$</div>
<p>Letting $x\to\infty$ excludes an infinite root cluster; transitivity and countability exclude all infinite clusters.</p>
<p>To obtain the exponential cutoff in a block, combine $\mathbb P(T_n\geq x)\leq\mathbb P(T\geq x)$ with <a href="/tag/12NL/">rooted damping</a>:</p>
<div class="math-display">$$\mathbb P(T_n\geq x)\leq e^{1-x/(9M_n)}\mathbb P(T_n\geq M_n)
\leq C M_n^{-\theta}e^{-x/(9M_n)}\qquad(x\geq M_n).$$</div>
<p>The factor $(x/M_n)^\theta$ is absorbed by half the exponential. For $x&lt;M_n$ use the power-law bound and enlarge the constant. Finally $M_n\leq Cv_n$, proving the stated estimate.</p>
<p>Together with Q8JZ, this completes Theorem 1.2 and the finite-block lower bound (5.7). The mesoscopic input has been proved above, rather than assumed in the ghost argument.</p>

## Tightness of the ordered cluster volumes {#section-low-dimensional-vector-tightness}

<a id="tag-THZF" data-assertion="theorem" data-title="The sharp norm threshold for low-dimensional cluster-vector tightness"></a>
<p>Assume $d/3&lt;\alpha&lt;d$. List the terminal block-cluster volumes in decreasing order, padding with zeros, and set</p>
<div class="math-display">$$Y_n=v_n^{-1}(|K_{n,1}|,|K_{n,2}|,\ldots),\qquad
p_* =\frac{2d}{d+\alpha}=1+\theta\in(1,2).$$</div>
<p>For $1\leq p\leq\infty$, the laws of $Y_n$ are tight in $\ell^p_\downarrow\setminus\{0\}$ if and only if $p&gt;p_*$. At the endpoint,</p>
<div class="math-display">$$\mathbb E\|Y_n\|_{p_*}^{p_*}\asymp n+1,\qquad
\|Y_n\|_{p_*}\longrightarrow\infty\quad\text{in probability}.$$</div>
<p><em>Proof.</em> First let $p_*&lt;p\leq2$ and write $r=p-1&gt;\theta$. Counting vertices in their clusters gives</p>
<div class="math-display">$$\mathbb E\|Y_n\|_p^p=Q^nv_n^{-p}\mathbb E T_n^{p-1}.$$</div>
<p>The block-tail bound in ZDDE and tail integration yield $\mathbb E T_n^r\leq C_rv_n^{r-\theta}$. The powers of $v_n$ cancel because $Q^n=v_n^{1+\theta}$, so $\sup_n\mathbb E\|Y_n\|_p^p&lt;\infty$. The same counting and the power-law tail alone give</p>
<div class="math-display">$$\mathbb E\sum_iY_{n,i}^p\mathbf1_{\{Y_{n,i}\leq\delta\}}
=Q^nv_n^{-p}\mathbb E[T_n^{p-1}\mathbf1_{\{T_n\leq\delta v_n\}}]
\leq C_p\delta^{p-1-\theta}.$$</div>
<p>For example, bound the truncated moment by $\mathbb E\min(T_n,\delta v_n)^r=r\int_0^{\delta v_n}x^{r-1}\mathbb P(T_n&gt;x)\,dx$. The estimate $\mathbb P(T_n&gt;x)\leq Cx^{-\theta}$ also holds for $0&lt;x&lt;1$ after enlarging $C$, so this argument covers cutoffs smaller than one.</p>
<p>These estimates give compact sets with uniformly large probability. Fix a probability tolerance. Markov bounds the norm by a common constant with arbitrarily high probability. Choose $\delta_j\downarrow0$ so that, outside events with summable probabilities as small as desired, the $p$th-power mass of entries at most $\delta_j$ is at most $2^{-j}$. On the event $\|Y_n\|_p^p\leq R$, ordering gives $Y_{n,i}^p\leq R/i$. Thus for fixed $N_j&gt;R/\delta_j^p$, the coordinate tail from $N_j$ onwards is at most $2^{-j}$. The closed set with this norm bound and all these tail bounds is compact in $\ell^p$: finite-coordinate truncations approximate it uniformly. A union bound proves tightness. The continuous inclusion into $\ell^q$ for $q&gt;p$, including $q=\infty$, proves the remaining upper cases.</p>
<p>The limits cannot charge zero. Q8JZ and the maximum quantile imply $\mathbb E Z_n\geq M_n/(2e)\geq cv_n$. The lower-tail estimate in <a href="/tag/3109/">norm tightness</a> therefore gives $\mathbb P(Z_n/v_n\leq u)\leq Cu$ (apply its strict-threshold bound at $2u$) for sufficiently small $u&gt;0$. Intersecting the preceding compact sets with $\{\|x\|_\infty\geq u\}$ proves tightness in the space with zero removed.</p>
<p>At $p=p_*$, the same rooted identity reduces the expected norm power to $\mathbb E T_n^\theta$. The lower tail up to $bv_n$ in ZDDE gives a lower bound of order $\log v_n$, and its exponential cutoff gives the matching upper bound after splitting the integral at $v_n$. Enlarging constants handles the finitely many small scales, giving $\mathbb E\|Y_n\|_{p_*}^{p_*}\asymp n+1$.</p>
<p>Divergence of these expectations alone would not prove non-tightness. Apply the moment comparison in 3109 to the cluster norm $W_n=\|Y_n\|_{p_*}$:</p>
<div class="math-display">$$\mathbb E W_n^{p_*}\leq D_{p_*}(\mathbb E W_n)^{p_*},\qquad
\mathbb E W_n\geq c(n+1)^{1/p_*}.$$</div>
<p>Its lower-tail estimate, applied at $2R$, now implies $\mathbb P(W_n\leq R)\leq C R/\mathbb E W_n\to0$ for every fixed $R$. Hence $W_n\to\infty$ in probability. For $1\leq p\leq p_*$, $\|Y_n\|_p\geq W_n$, so tightness fails there as well.</p>
<p>This proves Corollary 1.15. The endpoint proof uses the correct tail-integration power and the norm estimate needed to pass from moment growth to non-tightness; both are documented in the <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional errata</a>. Positivity of every coordinate of a subsequential limit, as opposed to exclusion of the zero vector, requires the further argument of section 5.4.</p>


## Propagating a large maximum to earlier scales {#section-backward-maximum}

<a id="tag-O7W9" data-assertion="theorem" data-title="A large normalized maximum persists over any fixed number of scales"></a>
<p>In the critical exact model, let $0&lt;\alpha&lt;d$ and $v_n=L^{(d+\alpha)n/2}$. For every $\rho&gt;0$ and integer $\ell\geq1$ there is $b=b(\rho,\ell)&gt;0$ such that</p>
<div class="math-display">$$M_n\geq\rho v_n\quad\Longrightarrow\quad M_{n-\ell}\geq b v_{n-\ell}\qquad(n\geq\ell).$$</div>
<p><em>Proof.</em> Write $a_n=\nu_n(t_n)=\mathbb E S_3(n,t_n)$. The exact third-moment equation and the distinct-cluster comparison give $\nu_n'\leq3\mu_n\nu_n$. By <a href="/tag/2VXH/">the mean bound</a>, $\mu_n\leq C v_n^2$, while $t_n=\beta_c/v_n^2$. Integration over a level and <a href="/tag/54V4/">gluing</a> therefore give</p>
<div class="math-display">$$a_n\leq e^{3C\beta_c}\nu_n(0)=Qe^{3C\beta_c}a_{n-1}\qquad(n\geq1).$$</div>
<p>Increase the constant to $D\geq\max\{Qe^{3C\beta_c},L^{3(d+\alpha)/2}\}$. The maximum quantile and <a href="/tag/X2A4/">the moment comparison</a> give, for constants $c,C_1&gt;0$,</p>
<div class="math-display">$$cM_j^3\leq a_j\leq C_1M_jv_j^2\qquad(j\geq0).$$</div>
<p>The lower inequality follows from $S_3\geq Z_j^3$ and $\mathbb P(Z_j\geq M_j/2)&gt;e^{-1}$; the upper one follows from $\mathbb E S_3\leq C_1M_j\mu_j$. Thus</p>
<div class="math-display">$$c\rho^3v_n^3\leq a_n\leq D^\ell a_{n-\ell}\leq C_1D^\ell M_{n-\ell}v_{n-\ell}^2.$$</div>
<p>Take $b=(c/C_1)\rho^3D^{-\ell}L^{3(d+\alpha)\ell/2}$. This proves the assertion, including $n=\ell$, where the earlier block is a singleton.</p>
<p>This supplies Lemma 5.9. Both the logarithmic derivative bound and the upper moment comparison retain the block-volume factor: their scale is $L^{(d+\alpha)n}$, not $L^{\alpha n}$. The source displays are recorded in the <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional errata</a>.</p>

## Connections between selected large clusters {#section-selected-cluster-connections}

<a id="tag-OAE2" data-assertion="theorem" data-title="Separated selected block maxima rarely connect after the higher layers are added"></a>
<p>Retain $0&lt;\alpha&lt;d$. Let $W,W'$ be distinct level-$m$ blocks whose points are at hierarchical distance $L^h$, with $h&gt;m$. In each block choose one largest cluster of its truncated layer configuration, breaking ties by the least vertex in a fixed total ordering of that block. Denote these clusters by $C_W,C_{W'}$. For every $n\geq h$,</p>
<div class="math-display">$$\mathbb P(C_W\xleftrightarrow{\eta_n}C_{W'})\leq C L^{-(d-\alpha)(h-m)}.$$</div>
<p>The constant depends only on the model. The same bound holds with the full critical configuration in place of $\eta_n$. No lower bound on $M_m$ is needed.</p>
<p><em>Proof.</em> We first bound the cost of a path that leaves both selected clusters. Put $s=d+\alpha$, $q=d-\alpha$, and let $h(z)$ be the hierarchical level of $z$, with $h(0)=0$. Define</p>
<div class="math-display">$$k_m(z)=L^{-s\max\{m,h(z)\}},\qquad f_m(z)=L^{-q\max\{m,h(z)\}}.$$</div>
<p>The probability $b_m(x,y)$ that at least one layer above level $m$ opens the pair $\{x,y\}$ satisfies $b_m(x,y)\leq Ck_m(y-x)$ for $x\ne y$. This follows by summing the geometric intensity series. Set $b_m(x,x)=0$. The full two-point function satisfies $\tau(x,y)\leq Cf_0(y-x)$ by <a href="/tag/7YNX/">the two-point bound</a>: its endpoint assumptions follow here from <a href="/tag/FF30/">sharpness and boundary flux</a>, and its rooted-damping input is <a href="/tag/12NL/">12NL</a>.</p>
<p>Shell counting gives</p>
<div class="math-display">$$\sum_z k_m(z)\leq C_\alpha L^{-\alpha m},\qquad
\sum_{z\in B_j}f_0(z)\leq C_\alpha L^{\alpha j},\qquad C_\alpha=(1-L^{-\alpha})^{-1}.$$</div>
<p>It also gives the convolution estimate</p>
<div class="math-display">$$(k_m*f_0)(z)\leq C_0L^{-\alpha m}f_m(z),\qquad
C_0=2C_\alpha+\frac{L^{-d}}{1-L^{-d}}.$$</div>
<p>For $h(z)\leq m$, the sum over $B_m$ is at most $C_\alpha L^{-(d+\alpha)m}L^{\alpha m}$, and the remaining shells contribute at most $\sum_{j&gt;m}L^{-dj}$. For $h=h(z)&gt;m$, split the sum into $u\in B_{h-1}$, $u\in B_h\setminus B_{h-1}$, and $u\notin B_h$. The first part is bounded by $C_\alpha L^{-\alpha m}L^{-qh}$. In the second, $k_m(u)=L^{-sh}$ and $z-u\in B_h$, giving at most $C_\alpha L^{-dh}$. The last part is at most $\sum_{j&gt;h}L^{-dj}$. Since $h\geq m$, both latter bounds have the required size. This proves the estimate for all $z$.</p>
<p>As $f_m\leq f_0$, a second application and Tonelli give</p>
<div class="math-display">$$(k_m*f_0*k_m)(z)\leq C_0^2L^{-2\alpha m}f_m(z).$$</div>
<p>Also $k_m(z)\leq L^{-2\alpha m}f_m(z)$. Thus, for $x\in W$ and $y\in W'$ at distance $L^h$,</p>
<div class="math-display">$$b_m(x,y)+\sum_{u,v}b_m(x,u)\tau(u,v)b_m(v,y)
\leq C L^{-2\alpha m}L^{-qh}.\tag{*}$$</div>
<p>It remains to justify using this bound for clusters chosen from the configuration. Fix nonempty sets $A\subseteq W$ and $B\subseteq W'$. The event $\{C_W=A\}$ is the intersection of an event $F_A$ depending only on lower-layer coordinates with both endpoints in $A$, and a decreasing event $D_A$ on all other lower-layer coordinates in $W$. Here $F_A$ says that $A$ is connected. The event $D_A$ closes every lower-layer edge from $A$ to $W\setminus A$ and requires each component in $W\setminus A$ to rank below $A$. This requirement is decreasing: deleting edges only splits a competitor, and a split can retain its size only by leaving that component unchanged. The least-vertex tie rule is therefore preserved. Define $F_B,D_B$ in the same way. The two blocks use disjoint coordinate sets.</p>
<p>For $x\in A$ and $y\in B$, let $H_{xy}$ be the event that there is an open path from $x$ to $y$ with interior outside $A\cup B$, whose first and last edges come from layers above $m$. A direct higher-layer edge is allowed. This event is increasing and does not use the internal coordinates defining $F_A,F_B$. <a href="/tag/F4CV/">Harris's inequality for opposite monotonicities</a>, applied to the increasing event $H_{xy}$ and the decreasing event $D_A\cap D_B$ on the remaining coordinates, gives</p>
<div class="math-display">$$\mathbb P(C_W=A,C_{W'}=B,H_{xy})
\leq\mathbb P(C_W=A)\mathbb P(C_{W'}=B)\mathbb P(H_{xy}).$$</div>
<p>If $A$ and $B$ connect, a simple path between them has a segment from its last visit to $A$ before its first subsequent visit to $B$. Its interior avoids both sets. Every lower-layer edge leaving either selected cluster is closed, so its first and last edges must use higher layers. For a segment of length at least two, these two edges and the intervening path have disjoint open witnesses. BK therefore bounds $\mathbb P(H_{xy})$ by the left side of (*); the direct-edge term treats a segment of length one. The middle path may have length zero. All these statements use the independent layer coordinates, so a closed lower-layer copy and an open higher-layer copy of the same pair remain distinct coordinates.</p>
<p>Sum first over endpoints, then over the possible sets $A,B$. This yields</p>
<div class="math-display">$$\mathbb P(C_W\leftrightarrow C_{W'})
\leq C L^{-2\alpha m}L^{-qh}\,\mathbb E|C_W|\,\mathbb E|C_{W'}|.$$</div>
<p>The selected clusters have the size of the respective maxima. The maximum tail estimate and <a href="/tag/2VXH/">2VXH</a> give $\mathbb E|C_W|\leq C M_m\leq Cv_m$, and likewise for $W'$. Since $v_m^2L^{-2\alpha m}=L^{qm}$, the claimed bound follows. Finite-volume Harris and BK suffice for $\eta_n$. For the full law, increase the finite set of layer coordinates: connection events have finite witnesses, and the convolution bounds are summable.</p>
<p>The argument selects one cluster in each block and averages its size; it needs no bound for the total mass of all tied maxima. The two factors $L^{-\alpha m}$ charge the first and last higher-layer edges. Without them, the endpoint sum in the source's Proposition 5.8 does not yield decay in the separation of scales. The <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional correction</a> records this distinction.</p>

## Many large clusters throughout a coalescent level {#section-many-large-clusters}

<a id="tag-YUJ9" data-assertion="theorem" data-title="A large maximum quantile forces any fixed number of large clusters at every intermediate time"></a>
<p>For every $0&lt;\alpha&lt;d$, integer $k\geq1$, $\rho&gt;0$ and $0&lt;\varepsilon&lt;1$, there are $b&gt;0$ and $N&lt;\infty$ such that, whenever $n\geq N$ and $M_n\geq\rho v_n$,</p>
<div class="math-display">$$\mathbb P\bigl(|K_{n,k,t}|\geq bv_n\text{ for every }0\leq t\leq t_n\bigr)\geq1-\varepsilon.$$</div>
<p>Here $K_{n,k,t}$ is the $k$th largest component at time $t$, with missing components assigned size zero. The parameters $\rho$ and $\varepsilon$ are independent.</p>
<p><em>Proof.</em> Choose an integer $r\geq1$ with $Q^r\geq k$, and select $k$ distinct level-$(n-r)$ blocks within the level-$n$ block. For an integer $\ell\geq r$, choose a level-$(n-\ell)$ block $W_i$ inside each. Write $m=n-\ell$ and select a largest cluster $C_i$ in each $W_i$ with the tie rule of OAE2. Points in different $W_i$ have distance at least $L^{n-r+1}$. Consequently, by OAE2 and a union bound,</p>
<div class="math-display">$$\mathbb P(C_i\xleftrightarrow{\eta_n}C_j\text{ for some }i&lt;j)
\leq Ck^2L^{-(d-\alpha)(\ell-r)}.$$</div>
<p>Fix $\ell$ large enough that this is at most $\varepsilon/2$. O7W9 now supplies a constant $b_0=b_0(\rho,\ell)&gt;0$ with $M_m\geq b_0v_m$ whenever $M_n\geq\rho v_n$. The universal lower tail for a block maximum gives $\mathbb P(|C_i|&lt;aM_m)\leq C a$. Choose $a&gt;0$ with $Cka\leq\varepsilon/2$. Except on an event of probability at most $\varepsilon/2$, all selected clusters have size at least $ab_0v_m$.</p>
<p>Take $N=\ell$ and $b=ab_0L^{-(d+\alpha)\ell/2}$. Since $\ell\geq r\geq1$, every selected cluster is already present inside a component at time zero of level $n$. If no two selected clusters are connected at the terminal time, they remain in distinct components throughout the level. Those components never lose vertices. On the intersection of the two good events, there are therefore at least $k$ components of size $bv_n$ at every time. This proves the assertion. It does not use monotonicity of the $k$th largest component, which can fail when components merge.</p>
<p>This proves Proposition 5.8 with separate size and probability parameters and with a single event valid over the whole time interval.</p>

## Positive coordinates in every subsequential limit {#section-positive-limit-coordinates}

<a id="tag-ADJZ" data-assertion="corollary" data-title="Every fixed largest-cluster rank has the low-dimensional volume scale and every limiting coordinate is positive"></a>
<p>If $d/3&lt;\alpha&lt;d$, then for each integer $k\geq1$ and $\varepsilon&gt;0$ there are $b&gt;0$ and $N&lt;\infty$ such that</p>
<div class="math-display">$$\mathbb P\bigl(|K_{n,k,t}|\geq bv_n\text{ for all }0\leq t\leq t_n\bigr)\geq1-\varepsilon\qquad(n\geq N).$$</div>
<p>For every $p&gt;2d/(d+\alpha)$, including $p=\infty$, every weak subsequential limit of the terminal vectors $Y_n$ in $\ell^p_\downarrow$ is supported on sequences $y$ with $y_k&gt;0$ for every $k\geq1$.</p>
<p><em>Proof.</em> <a href="/tag/Q8JZ/">The low-dimensional maximum bound</a> gives $M_n\geq\rho v_n$ for a fixed $\rho&gt;0$ and all $n$. Apply YUJ9. An upper bound in probability for any fixed rank follows from the upper tail of the largest cluster, so each fixed rank has scale $v_n$.</p>
<p>Tightness in the stated norm spaces is <a href="/tag/THZF/">THZF</a>. Suppose $Y_{n_j}$ converges weakly to $Y$ there. Fix $k$ and $\varepsilon&gt;0$, and take $b,N$ from the first assertion. Coordinate evaluation is continuous in each of these norm topologies, and $\{y:y_k\geq b\}$ is closed. Portmanteau therefore gives</p>
<div class="math-display">$$\mathbb P(Y_k\geq b)\geq\limsup_{j\to\infty}\mathbb P(Y_{n_j,k}\geq b)\geq1-\varepsilon.$$</div>
<p>Let $\varepsilon\downarrow0$ to obtain $\mathbb P(Y_k&gt;0)=1$, then intersect these probability-one events over all positive integers $k$. This proves positivity of every coordinate, not merely exclusion of the zero vector. It does not identify a unique limiting law.</p>
<p>This completes Theorem 5.7 and the assertion about subsequential limits following Corollary 1.15. The general implication YUJ9 is also available at the critical dimension, where a large normalized maximum will be a temporary hypothesis in the hydrodynamic argument.</p>

## A susceptibility derivative from vanishing ghost intensity {#section-finite-mean-derivative}

<a id="tag-LHKO" data-assertion="theorem" data-title="Finite transitive susceptibility has an OSSS lower derivative bound"></a>
<p>Let $G$ be a nonempty finite graph with finite nonnegative edge weights invariant under a transitive group of vertex permutations. At parameter $\beta&gt;0$, open its edges independently with probabilities $1-e^{-\beta J_e}$. Write $T=|K_o|$, $\chi=\mathbb E_\beta T$ and $p_k=\mathbb P_\beta(T\geq k)$. Then</p>
<div class="math-display">$$p_k'\geq\frac{p_k}{2\beta}\left(\frac{k}{\chi}-1\right),\qquad
\chi'\geq\frac1\beta\left(\frac{\mathbb E_\beta T^2}{4\chi}-\frac\chi2+\frac14\right).$$</div>
<p><em>Proof.</em> Give vertices independent green marks with probability $1-e^{-h}$, and put $M(h)=\mathbb E_\beta(1-e^{-hT})$. Transitivity makes this quantity independent of the root. Apply <a href="/tag/29WG/">finite OSSS</a> with the tree exploring all green clusters and the increasing bond observable $g=\mathbf1_{\{T\geq k\}}$. The <a href="/tag/XZ7B/">edge revealment bound</a> is $2M(h)$; mark covariances vanish because $g$ depends only on bonds. The <a href="/tag/6X74/">ghost covariance estimate</a> therefore gives</p>
<div class="math-display">$$p_k(1-e^{-hk}-M(h))\leq2M(h)\sum_e\operatorname{Cov}_\beta(g,\omega_e).$$</div>
<p>Finite Russo's formula, with zero-weight coordinates omitted, gives</p>
<div class="math-display">$$p_k'=\sum_{e:J_e&gt;0}\frac{J_e}{1-e^{-\beta J_e}}\operatorname{Cov}_\beta(g,\omega_e)
\geq\frac1\beta\sum_e\operatorname{Cov}_\beta(g,\omega_e).$$</div>
<p>Divide the preceding covariance bound by $2\beta M(h)&gt;0$ and let $h\downarrow0$. Since $T$ is bounded, $M(h)/h\to\chi$, proving the first assertion. Sum it over $1\leq k\leq|V|$, using $\sum_k p_k=\chi$ and $\sum_k kp_k=\mathbb E[T(T+1)]/2$. This proves the second assertion, including when its right side is negative.</p>
<p>This supplies the finite-volume input of Lemma 6.3. Its coefficient $1/\beta$ also implies the source's coefficient $\min_{e:J_e&gt;0}J_e/(e^{\beta J_e}-1)$: when the parenthesis is nonnegative use $J_e/(e^{\beta J_e}-1)\leq1/\beta$, and otherwise use $\chi'\geq0$. No interchange of an infinite sum and a Dini derivative is needed here.</p>

## Small capped moments on infinitely many critical scales {#section-critical-capped-scales}

<a id="tag-NHNY" data-assertion="theorem" data-title="Failure of critical hydrodynamics forces arbitrarily small capped susceptibility on infinitely many scales"></a>
<p>In the critical exact hierarchical model, assume $d=3\alpha$. Retain $s=d+\alpha$, $v_n=L^{sn/2}$, $q=L^{-\alpha}$, $A=(1-q)^{-1}$ and</p>
<div class="math-display">$$G_n(t)=\frac1{t_n(A-t/t_n)},\qquad t_n=\beta_c/v_n^2.$$</div>
<p>If $M_n/v_n$ does not tend to zero, then for every $\varepsilon&gt;0$ there is $\delta&gt;0$ such that</p>
<div class="math-display">$$\liminf_{n\to\infty}\inf_{0\leq t\leq t_n}\frac{\tau_{n,\delta v_n}(t)}{G_n(t)}&lt;\varepsilon.$$</div>
<p>Consequently, for every $\varepsilon&gt;0$ there is $\delta&gt;0$ for which the set</p>
<div class="math-display">$$\mathcal A_\varepsilon=\{n\geq1:\mathbb E\min(|K_n(o)|,\delta v_n)&lt;\varepsilon L^{\alpha n}\}$$</div>
<p>is infinite.</p>
<p><em>Proof.</em> Suppose the first conclusion fails. There is then $\varepsilon_0&gt;0$ such that for every fixed $\delta&gt;0$ the displayed lower limit is at least $\varepsilon_0$. Since $\mu_n/G_n$ is bounded above by <a href="/tag/2VXH/">2VXH</a>, every such cap eventually satisfies a terminal lower bound $\tau_{n,\delta v_n}(t_n)\geq c_0\mu_n(t_n)$, where $0&lt;c_0\leq1$ is independent of $\delta$.</p>
<p>Fix $\eta\in(0,1)$, and choose $N$ for the backward estimate <a href="/tag/RHK3/">RHK3</a> with this $c_0$ and $\eta$. For a desired cap $\delta v_n$, apply the terminal lower bound at scale $n+N$ with the fixed coefficient $\delta'=\delta L^{-sN/2}$. This is the same cap, since $\delta'v_{n+N}=\delta v_n$. RHK3 gives $\tau_{n,\delta v_n}(t)\geq(1-\eta)G_n(t)$ for all large $n$ and all $t$. Thus every fixed $\delta&gt;0$ has lower limit at least one. A diagonal choice gives $\delta_n\downarrow0$ so slowly that, uniformly in $t$,</p>
<div class="math-display">$$\tau_{n,m_n}(t)\geq(1-o(1))G_n(t),\qquad m_n=\delta_n v_n=o(v_n).\tag{1}$$</div>
<p>Failure of hydrodynamics gives infinitely many $j$ with $M_j\geq\rho v_j$, for some $\rho&gt;0$. The maximum quantile gives $\nu_j(t_j)\geq cM_j^3$, and gluing gives $\nu_{j+1}(0)=Q\nu_j(t_j)$. Hence for some $a&gt;0$ there are arbitrarily large $n$ with $\nu_n(0)\geq av_n^3$. Only a positive upper limit is needed at this point.</p>
<p>We show that, for all sufficiently large $n$, this last inequality forces a strict increase of $\nu_n(0)/v_n^3$ at the next scale. Indeed, $\nu_n(0)\leq CM_nv_n^2$ implies $M_n\geq\rho_1v_n$, with $\rho_1&gt;0$ depending on $a$. By <a href="/tag/YUJ9/">the many-cluster bound</a>, at every time there is probability at least $1/2$ of two distinct components of size at least $bv_n$, where $b&gt;0$ is fixed. For large $n$, $m_n\leq bv_n/2$. Split the exact third-power drift as</p>
<div class="math-display">$$\nu_n'=3\mathbb E\sum_{C\ne D}|C|\min(|C|,m_n)|D|^3
+3\mathbb E\sum_{C\ne D}|C|\bigl(|C|-\min(|C|,m_n)\bigr)|D|^3.$$</div>
<p>Harris and subtraction of the diagonal bound the first sum below by $\tau_{n,m_n}\nu_n-m_n\mathbb E S_4$, exactly as in RHK3. The event of two large components bounds the second below by $cv_n^5$. The moment bounds give $\mathbb E S_4\leq Cv_n^4$ and $\nu_n\leq Cv_n^3$. Thus (1), $G_n\leq Cv_n^2$ and $m_n/v_n\to0$ imply, for some $\gamma&gt;0$ independent of $n,t$,</p>
<div class="math-display">$$\nu_n'(t)\geq3(1+\gamma)G_n(t)\nu_n(t)$$</div>
<p>whenever $n$ is sufficiently large and $\nu_n(0)\geq av_n^3$. Since</p>
<div class="math-display">$$\int_0^{t_n}G_n(t)\,dt=\log\frac A{A-1}=\alpha\log L,$$</div>
<p>integration and gluing yield</p>
<div class="math-display">$$\nu_{n+1}(0)\geq L^{d+3\alpha(1+\gamma)}\nu_n(0)
=L^{3\alpha\gamma}\frac{v_{n+1}^3}{v_n^3}\nu_n(0).$$</div>
<p>The equality uses $d=3\alpha$. Starting at one arbitrarily large scale with $\nu_n(0)\geq av_n^3$, this implication perpetuates its own premise and makes the normalized moments grow geometrically. It contradicts $\nu_n(0)\leq Cv_n^3$. This proves the first conclusion.</p>
<p>To pass to terminal rooted volumes, apply that conclusion with an arbitrarily small auxiliary tolerance $\zeta$. At infinitely many scales there is $u\in[0,t_n]$ with $\tau_{n,\delta v_n}(u)\leq C\zeta v_n^2$. From $\tau'\leq\tau^2$ we have</p>
<div class="math-display">$$\tau(t_n)\leq\frac{\tau(u)}{1-(t_n-u)\tau(u)}\leq2C\zeta v_n^2$$</div>
<p>provided $\zeta$ is small enough that $C\beta_c\zeta\leq1/2$. Divide by $Q^n$ using the rooted identity in RHK3, then choose $2C\zeta&lt;\varepsilon$. This proves the terminal assertion with normalization $L^{\alpha n}$.</p>
<p>The first assertion also holds with the integer cap $\lceil\delta v_n\rceil$. Increasing a cap by at most one adds at most $Q^n$ to its block moment, and $Q^n/G_n(t)\leq CL^{-\alpha n}\to0$. Apply the real-cap assertion with a smaller tolerance. This proves Lemma 6.2 with a positive cap parameter, the required upper-limit statement and the reciprocal mean profile retained.</p>

## Growth of two clusters conditioned at an earlier scale {#section-conditional-two-cluster-growth}

<a id="tag-837P" data-assertion="proposition" data-title="Distinct rooted cluster volumes have a uniform conditional growth bound"></a>
<p>For any $0&lt;\alpha&lt;d$, let $x\in B_m$, $n\geq m$, and write $T_j(y)=|K_j(y)|$ and $D_j=\{K_j(0)\ne K_j(x)\}$. Conditional on the two sets $K_m(0),K_m(x)$,</p>
<div class="math-display">$$\mathbb E[T_n(0)T_n(x)\mathbf1_{D_n}\mid K_m(0),K_m(x)]
\leq C L^{2\alpha(n-m)}T_m(0)T_m(x)\mathbf1_{D_m}.$$</div>
<p>The constant depends only on the model, not on $m,n,x$ or any cap.</p>
<p><em>Proof.</em> There is nothing to prove if the old clusters coincide. Otherwise fix their disjoint vertex sets $U,V$. The conditioning closes their lower-layer boundaries and requires connectivity inside each set. All remaining lower-layer coordinates outside $U\cup V$, and all higher-layer coordinates, retain their product law. A path from $U$ to $y\notin U\cup V$ on $D_n$ has a segment from its last visit to $U$ to $y$ whose interior avoids $U\cup V$. Its first edge must come from a layer above $m$.</p>
<p>Let $b_m(a,z)$ be the probability that a higher-layer copy of $\{a,z\}$ is open, using only layers up to $n$. The geometric row sum gives $\sum_z b_m(a,z)\leq CL^{-\alpha m}$. After the first edge, the remaining path is bounded by the unconditioned two-point function $\tau_n(z,y)$, whose row sum is $\chi_n\leq CL^{\alpha n}$. For paths growing from both $U$ and $V$, the event $D_n$ supplies disjoint witnesses. Finite BK on the still-random coordinates therefore bounds the double increment by</p>
<div class="math-display">$$\mathbb E[(T_n(0)-|U|)(T_n(x)-|V|)\mathbf1_{D_n}\mid U,V]
\leq |U||V|\bigl(CL^{-\alpha m}\chi_n\bigr)^2.$$</div>
<p>For completeness, expand both increments as sums over their endpoint vertices. For each pair of endpoints choose the two last-exit edges and the two remaining paths. Their witnesses are disjoint because the final clusters are distinct. A union bound and BK give the product of the four probabilities; summing the two first-edge rows and the two path rows gives the displayed expression. Conditioning can only remove boundary coordinates; the remaining paths avoid both old sets, so no conditioned internal connectivity enters this calculation. The same argument with one path bounds each mixed term by $|U||V|CL^{-\alpha m}\chi_n$. Including the base term gives $|U||V|(1+CL^{-\alpha m}\chi_n)^2$, which has the asserted bound since $n\geq m$.</p>
<p>A useful consequence is that if $\mathbb E\min(T_m(o),\delta v_m)\leq\varepsilon L^{\alpha m}$, then</p>
<div class="math-display">$$\mathbb E[T_n(0)T_n(x)\mathbf1_{D_n}\mathbf1_{\{\min(T_m(0),T_m(x))&lt;\delta v_m\}}]
\leq C\varepsilon L^{2\alpha n}.\tag{2}$$</div>
<p>Indeed, after conditioning, bound the earlier product on the small-cluster event by</p>
<div class="math-display">$$T_m(0)\min(T_m(x),\delta v_m)+\min(T_m(0),\delta v_m)T_m(x).$$</div>
<p>Keep the distinct-cluster indicator. Each expectation is at most $\chi_m\mathbb E\min(T_m(o),\delta v_m)$: expand the two nonnegative increasing functions into weighted cluster-size tail indicators, use disjoint witnesses on $D_m$, then apply BK and sum. Finally use $\chi_m\leq CL^{\alpha m}$. In particular the constant in (2) is independent of $\varepsilon$ and $\delta$.</p>

## Repeated opportunities to join two large clusters {#section-suppressed-layer-edges}

<a id="tag-EH4L" data-assertion="proposition" data-title="Uninspected next-layer edges bound the weighted survival of two large clusters"></a>
<p>Retain $0&lt;\alpha&lt;d$, fix distinct $0,x\in B_N$, and fix $\delta&gt;0$. For $n\geq N$ let</p>
<div class="math-display">$$g_n=\#\{m\in\{N,\ldots,n\}:\min(T_m(0),T_m(x))\geq\delta v_m\}.$$</div>
<p>For every real $a\geq0$,</p>
<div class="math-display">$$\mathbb E[T_n(0)T_n(x)\mathbf1_{D_n}\mathbf1_{\{g_n&gt;a\}}]
\leq e^{-\beta_c\delta^2 L^{-s}(a-1)}\chi_n^2.$$</div>
<p><em>Proof.</em> Construct a smaller configuration recursively. Start with $\widetilde\eta_N=\eta_N$. To pass from $m$ to $m+1$, add the independent truncated configurations in the sibling blocks, and add all level-$(m+1)$ coordinates except those with one endpoint in each of the two old root clusters $\widetilde K_m(0),\widetilde K_m(x)$. When the old clusters are distinct, leave these exceptional coordinates uninspected and set them closed in the smaller configuration. If the root clusters have already merged, no further suppression is needed.</p>
<p>Use a transcript recording the revealed coordinates, the suppressed coordinate sets and the smaller configurations through level $n$. Its decisions at each level depend only on already revealed coordinates. Consequently, conditional on a possible transcript, all suppressed coordinates retain their independent original Bernoulli laws. One can see this directly: the event giving that transcript specifies the values of revealed coordinates only; changing any suppressed value leaves every subsequent decision unchanged.</p>
<p>On $D_n$, the smaller root clusters equal the original ones at every level. Inductively, a suppressed open edge between the two old clusters would already join the original roots; hence all suppressed coordinates are closed on $D_n$. Conversely, if the smaller terminal clusters are distinct and every suppressed coordinate is closed, the original and smaller configurations agree and $D_n$ holds. Thus, conditional on the transcript,</p>
<div class="math-display">$$\mathbb P(D_n\mid\text{transcript})
=\mathbf1_{\{\widetilde K_n(0)\ne\widetilde K_n(x)\}}
\exp\left[-\beta_c\sum_{m=N}^{n-1}L^{-s(m+1)}|\widetilde K_m(0)||\widetilde K_m(x)|\right].\tag{3}$$</div>
<p>The sizes in this sum are those before the next layer is added. Define $\widetilde g_n$ by the same finite count as $g_n$, using the smaller clusters. On transcripts with distinct terminal clusters, every qualifying scale $m&lt;n$ contributes at least $\delta^2L^{-s}$ to the sum. Only the last scale can lack a following layer. Therefore, on $\{\widetilde g_n&gt;a\}$, the conditional probability in (3) is at most $e^{-\beta_c\delta^2L^{-s}(a-1)}$ times the distinctness indicator.</p>
<p>On $D_n$ all the volume and count factors can be replaced by their smaller-configuration counterparts before conditioning. It remains to bound</p>
<div class="math-display">$$\mathbb E[|\widetilde K_n(0)||\widetilde K_n(x)|\mathbf1_{\{\widetilde K_n(0)\ne\widetilde K_n(x)\}}]\leq\chi_n^2.$$</div>
<p>For integers $i,j\geq1$, two distinct smaller clusters with sizes at least $i,j$ contain disjoint open tree witnesses for $\{T_n(0)\geq i\}$ and $\{T_n(x)\geq j\}$ in the original product configuration. The smaller configuration is a subconfiguration of the original one, even when the original roots connect. Hence this joint event is contained in the disjoint occurrence of the two size events. BK and summation over $i,j$ give the required bound. No product-law assertion is made about the smaller configuration itself.</p>
<p>This is the weighted survival estimate in the proof of Theorem 6.1. The finite transcript, the count restricted to $m\leq n$, and the factor $L^{-s}$ make the conditioning and scale index explicit.</p>

## Hydrodynamics at the critical dimension {#section-critical-hydrodynamics}

<a id="tag-UL8V" data-assertion="theorem" data-title="The hydrodynamic condition holds at the critical dimension in the exact hierarchical model"></a>
<p>For the critical exact hierarchical model with $d=3\alpha$,</p>
<div class="math-display">$$M_n=o(L^{(d+\alpha)n/2}).$$</div>
<p>Consequently the sharp mean profile, fixed-order moment ratios, concentration and volume-biased limit proved under hydrodynamics earlier in this article hold at $d=3\alpha$ without that additional assumption.</p>
<p><em>Proof.</em> Suppose hydrodynamics fails. By NHNY, for every $\varepsilon&gt;0$ choose $\delta&gt;0$ such that $\mathcal A_\varepsilon$ is infinite. Fix distinct $0,x\in B_N$ and set $a_n=\#(\mathcal A_\varepsilon\cap[N,n])$. Then $a_n\to\infty$. Write $W_n=T_n(0)T_n(x)\mathbf1_{D_n}$ and use the count $g_n$ from EH4L. On $\{g_n\leq a_n/2\}$, at least $a_n/2$ scales in $\mathcal A_\varepsilon\cap[N,n]$ have $\min(T_m(0),T_m(x))&lt;\delta v_m$. Therefore (2) gives, once $a_n&gt;0$,</p>
<div class="math-display">$$\mathbb E[W_n\mathbf1_{\{g_n\leq a_n/2\}}]
\leq\frac2{a_n}\sum_{m\in\mathcal A_\varepsilon\cap[N,n]}
\mathbb E[W_n\mathbf1_{\{\min(T_m(0),T_m(x))&lt;\delta v_m\}}]
\leq C\varepsilon L^{2\alpha n}.$$</div>
<p>EH4L and $\chi_n\leq CL^{\alpha n}$ bound the complementary part by $CL^{2\alpha n}\exp[-\beta_c\delta^2L^{-s}(a_n/2-1)]$. Thus</p>
<div class="math-display">$$\limsup_{n\to\infty}L^{-2\alpha n}\mathbb E W_n\leq C\varepsilon.$$</div>
<p>The constant is independent of $\varepsilon$ and $\delta$. Letting $\varepsilon\downarrow0$ proves $\mathbb E W_n=o(L^{2\alpha n})$ for every fixed $x$.</p>
<p>Now regard the terminal block law as percolation with parameter $\beta$ and weights $J_n(u,v)=\sum_{j=h(u,v)}^nL^{-sj}$. Put $D_n^{\mathrm{sus}}=\left.\frac{d}{d\beta}\mathbb E_\beta T_n(o)\right|_{\beta=\beta_c}$. Finite Russo and translation invariance give the exact identity</p>
<div class="math-display">$$D_n^{\mathrm{sus}}=\sum_{x\in B_n}J_n(0,x)\mathbb E[T_n(0)T_n(x)\mathbf1_{\{K_n(0)\ne K_n(x)\}}].\tag{4}$$</div>
<p>To check the coefficient, a new edge between distinct components $C,D$ increases the sum of squared component sizes by $2|C||D|$ at rate $J_n(C,D)$. Sum over unordered component pairs and divide by $Q^n$. Replacing the unordered sum by the ordered vertex sum cancels the factor two; translation of its first endpoint to the origin gives (4).</p>
<p>Distinct-cluster BK bounds each expectation in (4) by $\chi_n^2\leq CL^{2\alpha n}$. Since $J_n(0,x)\leq J_\infty(0,x)$ and the latter has finite row sum, the pointwise estimate just proved and dominated convergence on the countable vertex set imply</p>
<div class="math-display">$$D_n^{\mathrm{sus}}=o(L^{2\alpha n}).$$</div>
<p>For $x\notin B_n$, extend the summand by zero; for $x=0$ it is already zero. This justifies the moving block in the convergence argument.</p>
<p>On the other hand, failure of hydrodynamics gives infinitely many $n$ with $M_n\geq\rho v_n$. The maximum quantile and rooted identity yield</p>
<div class="math-display">$$\mathbb E T_n(o)^2=Q^{-n}\nu_n(t_n)\geq cQ^{-n}M_n^3\geq c_\rho L^{3\alpha n}.$$</div>
<p>Here again $d=3\alpha$. Applying LHKO at $\beta_c$ and using $\chi_n\asymp L^{\alpha n}$ gives $D_n^{\mathrm{sus}}\geq cL^{2\alpha n}$ on all sufficiently large scales in this infinite set: the subtracted term has only order $L^{\alpha n}$. This contradiction proves hydrodynamics.</p>
<p>The remaining assertions follow by applying <a href="/tag/W2VN/">W2VN</a>, <a href="/tag/ANYT/">ANYT</a>, <a href="/tag/KPCV/">KPCV</a> and <a href="/tag/FY23/">FY23</a> with their hydrodynamic premise now discharged. In particular the last result gives the squared-normal volume-biased limit at the critical dimension. This does not yet determine the logarithmic amplitude of the second rooted moment; the covariance asymptotics in sections 6.2–6.3 of the source are still needed for that calculation.</p>
<p>This completes Theorem 6.1 and its finite-volume ingredients. The sign, normalization and conditioning corrections in section 6.1 are recorded as <a href="/errata/hutchcroft-hierarchical-volumes-2022/">provisional source errata</a>; the theorem's conclusion is unchanged.</p>

## A fourth-moment bound from ordered cluster discovery {#section-cluster-fourth-moment}

<a id="tag-I2YU" data-assertion="theorem" data-title="Finite percolation power sums admit a fourth central moment bound"></a>
<p>For independent bond percolation on any finite graph, let $S_p=\sum_C|C|^p$, where $p\geq1$. Then</p>
<div class="math-display">$$\mathbb E(S_p-\mathbb ES_p)^4\leq\mathbb ES_{4p}+3(\mathbb ES_{2p})^2.$$</div>
<p><em>Proof.</em> Order the vertices as $v_1,\ldots,v_N$. Let $Z_i=|K(v_i)|^p$ if its cluster contains no earlier vertex, and let $Z_i=0$ otherwise. Then $\sum_i Z_i^k=S_{kp}$. Put $U_{i-1}=\sum_{j&lt;i}Z_j$, the sum of the $p$th powers of the sizes of clusters meeting the earlier vertices.</p>
<p>For $r&gt;0$, condition on $K(v_i)=B$, where $B$ avoids the earlier vertices and $|B|^p\geq r$. All bonds outside $B$ retain their product law. The variable $U_{i-1}$ is now computed in the graph with $B$ removed. Adding the removed vertices as isolated vertices does not change it, and subsequently adding edges can only increase it: a merger involving one earlier-root cluster increases its size, while a merger of two replaces $a^p+b^p$ by $(a+b)^p\geq a^p+b^p$. Consequently</p>
<div class="math-display">$$\mathbb P(U_{i-1}\geq u\mid K(v_i)=B)\leq\mathbb P(U_{i-1}\geq u).$$</div>
<p>Sum over these possible sets $B$. This proves</p>
<div class="math-display">$$\mathbb P(Z_i\geq r,U_{i-1}\geq u)\leq\mathbb P(Z_i\geq r)\mathbb P(U_{i-1}\geq u).\tag{5}$$</div>
<p>For $r\leq0$ this is equality. This argument retains the condition that the current cluster avoids earlier vertices; it does not identify the law of $Z_i$ with that of $|K(v_i)|^p$.</p>
<p>We use the following elementary convex comparison. If finite-valued variables $X,Y$ satisfy the joint-tail inequality (5), and $Y^*$ is independent of $X$ with the law of $Y$, then $\mathbb E f(X+Y)\leq\mathbb E f(X+Y^*)$ for convex $f$. Indeed, on the ordered supports $x_0&lt;\cdots&lt;x_a$ and $y_0&lt;\cdots&lt;y_b$, the mixed differences</p>
<div class="math-display">$$f(x_i+y_j)-f(x_{i-1}+y_j)-f(x_i+y_{j-1})+f(x_{i-1}+y_{j-1})$$</div>
<p>are nonnegative. Expand $f(X+Y)$ by summation by parts into its two marginal boundary terms and these mixed differences multiplied by $\mathbf1_{\{X\geq x_i,Y\geq y_j\}}$. The marginal terms are unchanged by independence, and (5) bounds each remaining expectation. Applying this comparison successively, with induction on $i$ and the convex function $x\mapsto\mathbb E f(x+Z_i^*)$, gives</p>
<div class="math-display">$$\mathbb E f\left(\sum_i Z_i\right)\leq\mathbb E f\left(\sum_i Z_i^*\right),$$</div>
<p>where the starred variables are independent copies with their respective marginal laws. This proves the finite-valued form of the convex comparison used here.</p>
<p>Take $f(x)=(x-\mathbb ES_p)^4$. Independence and centering give</p>
<div class="math-display">$$\mathbb E\left(\sum_i(Z_i^*-\mathbb EZ_i^*)\right)^4
=\sum_i\mathbb E(Z_i-\mathbb EZ_i)^4+6\sum_{i&lt;j}\operatorname{Var}(Z_i)\operatorname{Var}(Z_j).$$</div>
<p>For a nonnegative variable $Z$, $\mathbb E(Z-\mathbb EZ)^4\leq\mathbb EZ^4$. To check this when $m=\mathbb EZ&gt;0$, Cauchy–Schwarz gives $\mathbb EZ^3\geq(\mathbb EZ^2)^2/m$. Writing $x=\mathbb EZ^2/m^2\geq1$, the difference between the raw and centered fourth moments is at least $m^4(4x^2-6x+3)\geq0$. The case $m=0$ is immediate. Also $\operatorname{Var}(Z_i)\leq\mathbb EZ_i^2$. The preceding display is therefore at most $\sum_i\mathbb EZ_i^4+3(\sum_i\mathbb EZ_i^2)^2$, as required.</p>
<p>This supplies the fourth-moment estimate needed in section 6.3, with coefficient three. The source's independent fourth-moment expansion has coefficient two instead of six on unordered pairs, and its last BK equality drops the avoidance condition. The corrected bound suffices for all subsequent negligible-error estimates; no assertion that the sharper printed bound is false is needed.</p>

## Exact variance and covariance equations {#section-variance-covariance-summary}

<p><em>Main article: <a href="/articles/multiplicative-coalescent/">The finite multiplicative coalescent</a>.</em></p>
<p>In the block process write $f_{j,n}(t)=\mathbb ES_j(n,t)$, $\nu_n=f_{3,n}$, $V_n(t)=\operatorname{Var}(S_2(n,t))$ and $C_n(t)=\operatorname{Cov}(S_2(n,t),S_3(n,t))$. Within a level, $V_n$ and $C_n$ satisfy the <a href="/tag/C1BP/">exact variance and covariance equations</a> of the finite multiplicative coalescent, in terms of the means and centred mixed moments, and independent children give the gluing identities $V_{n+1}(0)=QV_n(t_n)$ and $C_{n+1}(0)=QC_n(t_n)$.</p>

## The leading norm correlations {#section-leading-norm-correlations}

<a id="tag-LWRN" data-assertion="theorem" data-title="Hydrodynamics fixes the leading variance and covariance constants"></a>
<p>In the critical exact hierarchical model, assume hydrodynamics. Uniformly for $0\leq t\leq t_n$,</p>
<div class="math-display">$$V_n(t)\sim2\frac{\nu_n(t)^2}{\mu_n(t)}\sim\frac23 f_{4,n}(t),\qquad
C_n(t)\sim12\frac{\nu_n(t)^3}{\mu_n(t)^2}\sim\frac45 f_{5,n}(t).$$</div>
<p>Moreover, the exact equations above have the uniform additive approximations</p>
<div class="math-display">$$V_n'=4\mu_n V_n+2\nu_n^2+o(\nu_n^2),\qquad
C_n'=5\mu_n C_n+3\nu_n V_n+6\nu_n f_{4,n}+o(\nu_n f_{4,n}).$$</div>
<p><em>Proof.</em> Suppress $n,t$ and put $r=\nu^2/\mu^3$, which tends uniformly to zero by <a href="/tag/KPCV/">KPCV</a>. The moment equivalents <a href="/tag/ANYT/">ANYT</a> give $f_4\asymp\nu^2/\mu$, $f_6\asymp\nu^4/\mu^3$, and $f_8\asymp\nu^6/\mu^5=o(f_4^2)$. The covariance comparison bounds both $\operatorname{Var}(S_3)$ and $\operatorname{Cov}(S_2,S_4)$ by $f_6=o(\nu^2)$. By I2YU and Cauchy–Schwarz,</p>
<div class="math-display">$$|\mathbb E\Delta_2^3|\leq f_4^{1/2}(f_8+3f_4^2)^{1/2}
=O(\nu^2\sqrt r)=o(\nu^2).$$</div>
<p>Similarly, the two higher covariances in the second exact equation are bounded by $f_7=o(\nu f_4)$, and</p>
<div class="math-display">$$|\mathbb E(\Delta_3\Delta_2^2)|\leq f_6^{1/2}(f_8+3f_4^2)^{1/2}
=O(\nu f_4\sqrt r)=o(\nu f_4).$$</div>
<p>This proves the additive approximations, with uniform errors.</p>
<p>Normalize the variance by $F=2\nu^2/\mu$. The exact mean and third-moment equations give $F'/F=(5+o(1))\mu$. Hence $h=V/F$ satisfies</p>
<div class="math-display">$$h'=\mu\bigl[(-1+o(1))h+1+o(1)\bigr].$$</div>
<p>The ratio glues exactly, since both $V$ and $F$ are multiplied by $Q$ between a terminal level and the next initial level. Also $\int_0^{t_n}\mu_n\to\alpha\log L$. For $z=h-1$, variation of constants thus gives $|z_{n+1}(0)|\leq\rho|z_n(0)|+e_n$ for all sufficiently large $n$, where $\rho&lt;1$ and $e_n\to0$. The limiting contraction factor is $L^{-\alpha}$. Iterating the inequality sends the initial value and the finitely many early errors to zero geometrically; the remaining errors contribute at most $(1-\rho)^{-1}\sup_{j\geq n_0}e_j$. Let $n_0\to\infty$. The same integrating-factor bound at intermediate times proves $h\to1$ uniformly.</p>
<p>Now $3\nu V+6\nu f_4=(24+o(1))\nu^3/\mu$. Put $F_*=12\nu^3/\mu^2$. Then $F_*'/F_*=(7+o(1))\mu$, and $h_*=C/F_*$ satisfies</p>
<div class="math-display">$$h_*'=\mu\bigl[(-2+o(1))h_*+2+o(1)\bigr].$$</div>
<p>This ratio also glues exactly. The same argument, with contraction tending to $L^{-2\alpha}$, gives $h_*\to1$ uniformly. Finally $f_4\sim3\nu^2/\mu$ and $f_5\sim15\nu^3/\mu^2$ give the stated fractions. This proves Propositions 6.5 and 6.10 with all remainder estimates supplied. Hydrodynamics is available in both $d&gt;3\alpha$ and $d=3\alpha$ by 6WO3 and UL8V.</p>
<p>The central limit statement in Remark 6.14 remains a conjecture. For a centered variable divided by its standard deviation, the intended standard-normal $k$th moment is zero for odd $k$ and $(k-1)!!$ for even $k$. The printed $(2k-1)!!$ already gives three instead of one at $k=2$. No Gaussian fluctuation theorem is asserted here.</p>

## The first correction to the mean profile {#section-first-mean-correction}

<a id="tag-5B41" data-assertion="theorem" data-title="The mean correction retains the terminal endpoint of the time integral"></a>
<p>Assume hydrodynamics in the critical exact model. Put $q=L^{-\alpha}$, $A=(1-q)^{-1}$, $u=t/t_n$, $\phi=1-u/A$ and $r_n=\nu_n(0)^2/\mu_n(0)^3$. Write</p>
<div class="math-display">$$\epsilon_{2,n}=\frac{f_{4,n}-V_n}{\mu_n^2},\qquad
\epsilon_{3,n}=\frac{f_{5,n}-C_n}{\mu_n\nu_n},\qquad
H_n(t)=t_n(A-u)\mu_n(t)-1.$$</div>
<p>Uniformly for $0\leq u\leq1$,</p>
<div class="math-display">$$\epsilon_{2,n}(ut_n)=r_n\phi^{-3}(1+o(1)),\qquad
\epsilon_{3,n}(ut_n)=3r_n\phi^{-3}(1+o(1)),$$</div>
<div class="math-display">$$H_n(ut_n)=\frac{r_n}{2\phi}\left[q^{-2}-\phi^{-2}
+\frac{q^{-2}-1}{L^{d-2\alpha}-1}\right]+o(r_n).$$</div>
<p>In particular, at $d=3\alpha$, the bracket becomes $q^{-2}+q^{-1}+1-\phi^{-2}$.</p>
<p><em>Proof.</em> LWRN and ANYT give $\epsilon_{2,n}\sim\nu_n^2/\mu_n^3$ and $\epsilon_{3,n}\sim3\nu_n^2/\mu_n^3$. The time ratios in W2VN and I7HB give $\nu_n(ut_n)^2/\mu_n(ut_n)^3\sim r_n\phi^{-3}$ uniformly. This proves the first two formulas.</p>
<p>For the last, use the exact reciprocal series of W2VN:</p>
<div class="math-display">$$H_n(ut_n)=\frac{R_n(ut_n)}{A-u-R_n(ut_n)},\qquad
R_n(ut_n)=\int_u^1\epsilon_{2,n}(vt_n)\,dv
+\sum_{k\geq1}q^k\int_0^1\epsilon_{2,n+k}(vt_{n+k})\,dv.$$</div>
<p>Gluing and the time ratios give $r_{n+1}/r_n\to\rho=L^{3\alpha-d}$. By I7HB, hydrodynamics is impossible if $d&lt;3\alpha$, so $\rho\leq1$. Choose $b&gt;\rho$ with $qb&lt;1$. For all large $n$ and every $k\geq0$, $r_{n+k}/r_n\leq b^k$. The first two formulas also bound $\sup_t\epsilon_{2,j}(t)\leq Cr_j$ for every sufficiently large $j$. Thus the future-scale series, divided by $r_n$, is dominated by $C(qb)^k$. Dominated convergence justifies replacing each fixed-scale ratio by $\rho^k$ and controls the tail uniformly in $u$.</p>
<p>The time integral is</p>
<div class="math-display">$$\int_u^1(1-v/A)^{-3}\,dv=\frac A2\bigl(q^{-2}-\phi^{-2}\bigr).\tag{6}$$</div>
<p>It vanishes at $u=1$, as it must. Summing the future-scale geometric series gives</p>
<div class="math-display">$$\frac{R_n(ut_n)}{r_n}\longrightarrow\frac A2\left[q^{-2}-\phi^{-2}
+\frac{q^{-2}-1}{L^{d-2\alpha}-1}\right].$$</div>
<p>Since $r_n\to0$ and $A-u=A\phi\geq Aq&gt;0$, expansion of the exact denominator proves the result. For $d=3\alpha$, use $(q^{-2}-1)/(q^{-1}-1)=q^{-1}+1$.</p>
<p>This retains Corollary 6.6 and corrects the integral and profile in Corollary 6.7. It also passes an independent boundary check: exact gluing gives $H_{n+1}(0)=H_n(t_n)$, and the displayed coefficient $h(u)=\lim H_n(ut_n)/r_n$ satisfies $h(1)=\rho h(0)$. At the critical dimension the two endpoint coefficients are equal. The printed profile fails this check. The resulting change to the critical amplitude is kept explicit below and in the provisional errata.</p>

## An exponential recursion with polynomial decay {#section-polynomial-recursion}

<a id="tag-S23T" data-assertion="proposition" data-title="A small multiplicative decrement determines a polynomial amplitude"></a>
<p>Let $a_n&gt;0$, $B&gt;0$ and $\gamma&gt;0$. If</p>
<div class="math-display">$$a_{n+1}=a_n\exp[-(B+o(1))a_n^\gamma],$$</div>
<p>then $a_n\sim(\gamma Bn)^{-1/\gamma}$.</p>
<p><em>Proof.</em> Eventually the coefficient in the exponent lies between $B/2$ and $3B/2$, so $a_n$ decreases to a limit. A positive limit would make the successive ratios bounded away from one, forcing convergence to zero; hence the limit is zero. Set $b_n=a_n^{-\gamma}$. Then</p>
<div class="math-display">$$b_{n+1}-b_n=a_n^{-\gamma}\left(\exp[\gamma(B+o(1))a_n^\gamma]-1\right)\longrightarrow\gamma B.$$</div>
<p>Summation and division by $n$ give $b_n/n\to\gamma B$. Taking the power $-1/\gamma$ proves the assertion.</p>
<p>This proves Lemma 6.4 without an integral comparison. In the source's integral proof, the exponential upper bounds must retain $a_n^\gamma$ rather than $a_n$.</p>

## Critical logarithmic moment amplitudes {#section-critical-logarithmic-amplitudes}

<a id="tag-WQ7B" data-assertion="theorem" data-title="Critical hierarchical rooted moments have explicit logarithmic amplitudes"></a>
<p>In the critical exact hierarchical model with $d=3\alpha$, put</p>
<div class="math-display">$$q=L^{-\alpha},\qquad c_1=\frac{1-q}{\beta_cq},\qquad
D=\frac1{2\sqrt{\beta_cq(1+q+q^2)}}.$$</div>
<p>For every fixed integer $k\geq1$, the terminal rooted moments satisfy</p>
<div class="math-display">$$\mathbb E|K_n(o)|^k\sim(2k-3)!!\,c_1D^{k-1}n^{-(k-1)/2}L^{(2k-1)\alpha n}.$$</div>
<p>Under volume bias,</p>
<div class="math-display">$$\frac{|K_n(o)|}{D n^{-1/2}L^{2\alpha n}}\ \Longrightarrow\ N^2,$$</div>
<p>where $N$ is standard normal. These amplitudes use the exact kernel and the terminal block convention fixed earlier. They differ from the constants printed in arXiv:2211.05686v1; the calculation and source discrepancy are recorded below.</p>
<p><em>Proof.</em> Hydrodynamics holds by UL8V. Set $a_n=L^{-(d+3\alpha)n}\nu_n(0)$ and $c_0=(1-q)/\beta_c$. By W2VN, $\mu_n(0)\sim c_0L^{(d+\alpha)n}$, so at $d=3\alpha$ we have $r_n\sim a_n^2/c_0^3$. The exact third-moment equation is</p>
<div class="math-display">$$\frac{d}{dt}\log\nu_n(t)=3G_n(t)(1-\epsilon_{3,n}(t))(1+H_n(t)),\qquad
G_n(t)=\frac1{t_n(A-t/t_n)}.$$</div>
<p>Use 5B41 with $\phi=1-t/(At_n)$. If $C_q=q^{-2}+q^{-1}+1$, its expansions give, uniformly in time,</p>
<div class="math-display">$$\epsilon_{3,n}-H_n
=r_n\left(\frac72\phi^{-3}-\frac{C_q}{2}\phi^{-1}\right)+o(r_n),\qquad
\epsilon_{3,n}H_n=O(r_n^2)=o(r_n).$$</div>
<p>The leading difference need not be positive at every time. Its integral, which is what the recursion requires, is strictly positive:</p>
<div class="math-display">$$\begin{aligned}
3\int_q^1\left(\frac72\phi^{-4}-\frac{C_q}{2}\phi^{-2}\right)d\phi
&amp;=\frac72(q^{-3}-1)-\frac32C_q(q^{-1}-1)\\
&amp;=2(q^{-3}-1),
\end{aligned}$$</div>
<p>because $C_q(q^{-1}-1)=q^{-3}-1$. Here $G_n(t)dt=-d\phi/\phi$. Integrating the logarithmic equation and using $Q$-gluing therefore gives</p>
<div class="math-display">$$a_{n+1}=a_n\exp[-(B+o(1))a_n^2],\qquad
B=\frac{2(q^{-3}-1)}{c_0^3}&gt;0.$$</div>
<p>S23T now yields</p>
<div class="math-display">$$\nu_n(0)\sim B_0 n^{-1/2}L^{(d+3\alpha)n},\qquad
B_0=\frac{c_0^{3/2}}{2\sqrt{q^{-3}-1}}.$$</div>
<p>The time ratio in I7HB gives $\nu_n(t_n)\sim q^{-3}\nu_n(0)$. Divide by $Q^n$ to obtain the rooted second moment, and combine it with $\mathbb E|K_n(o)|\sim c_1L^{\alpha n}$. Their ratio is</p>
<div class="math-display">$$\zeta_n=\frac{\mathbb E|K_n(o)|^2}{\mathbb E|K_n(o)|}
\sim\frac{q^{-3}B_0}{c_1}n^{-1/2}L^{2\alpha n}
=D n^{-1/2}L^{2\alpha n}.$$</div>
<p>The simplification uses $1-q^3=(1-q)(1+q+q^2)$. Apply the rooted moment ratios and volume-biased limit of FY23 to conclude.</p>
<p>The initial third-power amplitude can equivalently be written</p>
<div class="math-display">$$B_0=\frac{(L^\alpha-1)^{3/2}}{\beta_c^{3/2}\sqrt{4L^{6\alpha}-4L^{3\alpha}}}.$$</div>
<p>The source prints $5L^{6\alpha}-2L^{3\alpha}-3L^{2\alpha}$ under the square root. Formula (6) corrects its time integral before the recurrence is derived. There is also a sign change between the source's expression for $\epsilon_3-H$ and its displayed integral for the decrement. The proof above recomputes the entire decrement and keeps the distinction between initial and terminal moments. These are provisional corrections to the cited version, not a claim about the journal formulas. The powers of $n$ and $L$ are unchanged.</p>


## Small clusters carry little of the critical mean {#section-critical-small-volume}

<a id="tag-9GFG" data-assertion="proposition" data-title="Small critical clusters carry a uniformly small fraction of the susceptibility"></a>
<p>In the critical exact hierarchical model with $d=3\alpha$, set $T_n=|K_n(o)|$, $\chi_n=\mathbb ET_n$ and</p>
<div class="math-display">$$b_n=(n+1)^{-1/2}L^{2\alpha n}\qquad(n\geq0).$$</div>
<p>For every $\varepsilon&gt;0$ there is $\delta&gt;0$ such that</p>
<div class="math-display">$$\mathbb E[T_n\mathbf1_{\{T_n\leq\delta b_n\}}]\leq\varepsilon\chi_n\qquad\text{for every }n\geq0.$$</div>
<p><em>Proof.</em> Under volume bias, <a href="/tag/WQ7B/">WQ7B</a> gives $T_n/b_n\Rightarrow DN^2$, where $D&gt;0$ and $N$ is standard normal. The limiting law has no atom at zero. Choose $a&gt;0$ so that $\mathbb P(DN^2\leq a)&lt;\varepsilon/2$. Weak convergence at the continuity point $a$ gives, for all sufficiently large $n$,</p>
<div class="math-display">$$\frac{\mathbb E[T_n\mathbf1_{\{T_n\leq ab_n\}}]}{\chi_n}&lt;\varepsilon.$$</div>
<p>For the finitely many remaining levels, choose $0&lt;\delta\leq a$ small enough that $\delta b_n&lt;1$. Their truncated expectations vanish because $T_n\geq1$; at later levels, reducing the threshold preserves the bound. This proves the uniform assertion.</p>
<p>This is Lemma 6.15 with a scale defined also at level zero. The replacement of $n^{-1/2}$ by $(n+1)^{-1/2}$ does not affect any large-level equivalent. Only absence of a zero atom in the biased limit is used.</p>

## Absorbing connections beyond the truncated block {#section-critical-ghost-absorption}

<a id="tag-F62A" data-assertion="proposition" data-title="The critical ghost connection probability has a uniform two-scale bound"></a>
<p>Let $T=|K(o)|$ be the full critical cluster volume and, independently of the bonds, mark each vertex green with probability $1-e^{-h}$. Write</p>
<div class="math-display">$$M(h)=\mathbb P_h(o\leftrightarrow\mathcal G)=\mathbb E(1-e^{-hT}),$$</div>
<p>with $e^{-h\infty}=0$. There is a finite constant $C$, depending only on the model, such that for every $h&gt;0$ and $n\geq0$,</p>
<div class="math-display">$$M(h)\leq C\bigl((n+1)^{1/2}L^{-\alpha n}+hL^{\alpha n}\bigr).$$</div>
<p><em>Proof.</em> Let $S=K_n(o)$, the cluster using only layers contained in the level-$n$ block. Its boundary is closed in those layers. Conditional on $S$, all coordinates with both endpoints outside $S$ retain their product law, as do all omitted layer coordinates. This follows by writing $\{K_n(o)=S\}$ as internal connectivity together with the closed truncated boundary. The event imposes no condition on the remaining coordinates.</p>
<p>Suppose $S$ contains no green vertex, but $o$ connects to a green vertex in the full configuration. On a finite open path to such a vertex, take the last edge leaving $S$. It is an omitted layer edge, and the remaining path lies outside $S$. For $x\in S$, the sum of opening probabilities over all omitted copies incident to $x$ is at most</p>
<div class="math-display">$$\sum_{j&gt;n}\beta_cL^{-(d+\alpha)j}(L^{dj}-1)
\leq\beta_c\sum_{j&gt;n}L^{-\alpha j}=c_*L^{-\alpha n},\qquad
c_*=\frac{\beta_cL^{-\alpha}}{1-L^{-\alpha}}.$$</div>
<p>The layer at level $j$ means the unique level-$j$ block containing $x$. The bound therefore counts every omitted coordinate, including higher-layer edges whose two endpoints both lie in the level-$n$ block.</p>
<p>For each candidate edge from $x\in S$ to $y\notin S$, its opening is independent of the event that $y$ reaches a green vertex off $S$. The latter uses only outside coordinates and marks. Its conditional probability is at most the unconditioned value $M(h)$, by restoring the removed vertices and bonds and using transitivity. The condition that $S$ have no green vertex uses separate marks and can be dropped for an upper bound. Summing over candidate edges thus gives</p>
<div class="math-display">$$\mathbb P_h(S\cap\mathcal G=\varnothing, K(o)\cap\mathcal G\ne\varnothing\mid S)
\leq c_*L^{-\alpha n}|S|M(h).\tag{7}$$</div>
<p>The last-exit decomposition can first be made in a finite set of layer coordinates. Every connection to a green vertex has a finite witness, so increasing the finite sets proves (7) for the full law. The displayed row sum justifies the countable union bound. No independence of the random set $S$ from the surrounding configuration is assumed.</p>
<p>For a threshold $a&gt;0$, split according to $T_n&gt;a$, a green vertex in $S$, and the event in (7). Markov's inequality and $1-e^{-hx}\leq hx$ give</p>
<div class="math-display">$$M(h)\leq\frac{\chi_n}{a}
+h\mathbb E[T_n\mathbf1_{\{T_n\leq a\}}]
+c_*L^{-\alpha n}\mathbb E[T_n\mathbf1_{\{T_n\leq a\}}]M(h).$$</div>
<p>By W2VN and the finitely many initial levels, $\chi_n\leq C_\chi L^{\alpha n}$ for all $n$. Choose $\varepsilon&gt;0$ so that $c_*C_\chi\varepsilon\leq1/2$, and use 9GFG to fix $\delta&gt;0$ with the corresponding small-volume bound. Set $a=\delta b_n$. The last coefficient is at most $1/2$, uniformly in $n$. Absorbing it into the left side gives</p>
<div class="math-display">$$M(h)\leq\frac{2C_\chi}{\delta}(n+1)^{1/2}L^{-\alpha n}
+2\varepsilon C_\chi hL^{\alpha n},$$</div>
<p>which proves the assertion. The tolerance is chosen after both the susceptibility constant and the omitted-layer row constant are fixed.</p>

## The critical full-cluster volume tail {#section-critical-volume-tail}

<a id="tag-FMVJ" data-assertion="theorem" data-title="Critical hierarchical cluster volumes have a one-quarter logarithmic tail correction"></a>
<p>In the critical exact hierarchical model with $d=3\alpha$, there are constants $0&lt;c\leq C&lt;\infty$ such that for every real $m\geq1$,</p>
<div class="math-display">$$c\,m^{-1/2}\bigl(\log(2+m)\bigr)^{1/4}
\leq\mathbb P(T\geq m)
\leq C\,m^{-1/2}\bigl(\log(2+m)\bigr)^{1/4}.$$</div>
<p>Consequently, $T&lt;\infty$ almost surely and, for every real $p&gt;0$,</p>
<div class="math-display">$$\mathbb ET^p&lt;\infty\quad\Longleftrightarrow\quad p&lt;\frac12.$$</div>
<p>The ghost probability satisfies $M(h)\asymp h^{1/2}(\log(1/h))^{1/4}$ as $h\downarrow0$.</p>
<p><em>Proof.</em> Apply 9GFG with $\varepsilon=1/2$ and fix its $\delta$. The random variable $Z_n=T_n\mathbf1_{\{T_n&gt;\delta b_n\}}$ has mean at least $\chi_n/2$. Cauchy–Schwarz gives</p>
<div class="math-display">$$\mathbb P(T_n&gt;\delta b_n)\geq\frac{\chi_n^2}{4\mathbb ET_n^2}
\geq c_0(n+1)^{1/2}L^{-\alpha n},\tag{8}$$</div>
<p>where the last bound follows from WQ7B and adjustment of a constant over the finitely many initial levels.</p>
<p>The sequence $b_n$ tends to infinity, is eventually increasing, and has successive ratios tending to $L^{2\alpha}&gt;1$. For every sufficiently large $m$, choose the least sufficiently large $n$ with $\delta b_n\geq m$. Then $\delta b_n\asymp m$, and taking logarithms of $b_n=(n+1)^{-1/2}L^{2\alpha n}$ gives $n+1\asymp\log m$. Since the full cluster contains $K_n(o)$, (8) yields</p>
<div class="math-display">$$\mathbb P(T\geq m)\geq c_0(n+1)^{1/2}L^{-\alpha n}
=c_0(n+1)^{1/4}b_n^{-1/2}
\geq c_2m^{-1/2}(\log m)^{1/4}.$$</div>
<p>This proves the lower tail for large $m$.</p>
<p>For the upper bound, put $x=\log(1/h)$ and take $h$ sufficiently small that $x\geq1$. Choose the integer</p>
<div class="math-display">$$n=\left\lceil\frac{x+\tfrac12\log x}{2\alpha\log L}\right\rceil.$$</div>
<p>Then $n+1\asymp x$ and</p>
<div class="math-display">$$h^{-1/2}x^{1/4}\leq L^{\alpha n}\leq L^\alpha h^{-1/2}x^{1/4}.$$</div>
<p>Both terms in F62A are therefore bounded by a constant times $h^{1/2}x^{1/4}$. With $h=1/m$ and $m$ sufficiently large,</p>
<div class="math-display">$$(1-e^{-1})\mathbb P(T\geq m)\leq M(1/m)
\leq C_2m^{-1/2}(\log m)^{1/4}.$$</div>
<p>This proves the upper tail. The lower tail at one large fixed threshold gives a positive uniform lower bound on the probability over the remaining bounded range of $m$. Enlarging the upper constant and decreasing the lower one extends both inequalities to all $m\geq1$ with $\log(2+m)$.</p>
<p>The upper tail tends to zero, proving almost sure finiteness. For $p&gt;0$, the layer-cake identity gives</p>
<div class="math-display">$$\mathbb ET^p=p\int_0^\infty t^{p-1}\mathbb P(T&gt;t)\,dt.$$</div>
<p>The tail just proved makes the integral at infinity comparable to $\int_2^\infty t^{p-3/2}(\log t)^{1/4}\,dt$. It converges exactly when $p&lt;1/2$, including divergence at equality. Finally, the upper bound on $M(h)$ was already established, and its matching lower bound follows from $M(h)\geq(1-e^{-1})\mathbb P(T\geq1/h)$.</p>
<p>This proves Theorem 1.7, whose original statement correctly uses thresholds at least two. The logarithmic exponent is unaffected by the provisional amplitude correction in WQ7B. In the proof, the logarithmic expression for $M(h)$ is used only for small $h$; it cannot hold for every $h&gt;0$ as written after the optimization in section 6.4. The scale choice above displays the logarithm of the full balancing product without ambiguity.</p>


## A continuous renormalization map {#section-renormalization-map}

<a id="tag-7VHT" data-assertion="theorem" data-title="The hierarchical coalescent recursion defines a continuous map on cluster laws"></a>
<p>Let $E=\ell^2_\downarrow$ be the space of nonnegative decreasing square-summable sequences, with its norm topology. Retain $Q=L^d$, $s=d+\alpha$, and put $r=L^{-s}$ and $\lambda=L^{-s/2}$. For a probability law $\mu$ on $E$, take $Q$ independent sequences with law $\mu$, combine their entries and rank them, run the multiplicative coalescent for time $r$, and multiply all masses by $\lambda$. Denote the resulting law by $\mathcal R\mu$.</p>
<p>The map $\mathcal R:\mathcal P(E)\to\mathcal P(E)$ is well-defined and continuous for weak convergence of probability measures on $E$. For $\mu_\beta=\delta_{(\sqrt\beta,0,\ldots)}$, $\beta\geq0$,</p>
<div class="math-display">$$\mathcal R^n\mu_\beta=\operatorname{Law}(Z_n^\beta),\qquad
Z_n^\beta=\sqrt\beta L^{-sn/2}(|K_{n,1}^\beta|,|K_{n,2}^\beta|,\ldots),$$</div>
<p>where the components use the truncated exact model. If the full sequence $\mathcal R^n\mu$ converges weakly to a law $\nu$, then $\mathcal R\nu=\nu$.</p>
<p><em>Proof.</em> We use <a href="https://doi.org/10.1214/aop/1024404421">Aldous's Proposition 5, p. 818</a>: the multiplicative coalescent is an $E$-valued Markov process, and its transition law $P_t(x,\cdot)$ depends weakly continuously on $x\in E$ for every fixed $t\geq0$. This is an external input; the construction for infinite square-summable initial states is proved in section 4.2 of that paper.</p>
<p>The combination and ranking map $D:E^Q\to E$ is continuous. In fact,</p>
<div class="math-display">$$\|D(x^{(1)},\ldots,x^{(Q)})-D(y^{(1)},\ldots,y^{(Q)})\|_2^2
\leq\sum_{j=1}^Q\|x^{(j)}-y^{(j)}\|_2^2.$$</div>
<p>For finite lists, matching the entries in decreasing order minimizes the sum of squared differences: exchanging an inverted pair changes the cross term by twice the product of two nonnegative differences. Apply this to truncations of the lists. Their decreasing rearrangements increase coordinatewise to the full rearrangement, and their squared norms increase to its squared norm. Thus they converge in $\ell^2$, since for $0\leq a_i\leq b_i$ one has $\sum_i(b_i-a_i)^2\leq\sum_i(b_i^2-a_i^2)$. Passing to the limit proves the inequality.</p>
<p>If $\mu_j\Rightarrow\mu$, their $Q$-fold product laws converge weakly; continuity of $D$ gives convergence of the combined initial laws. For every bounded continuous $f:E\to\mathbb R$, the Feller input says that</p>
<div class="math-display">$$x\longmapsto\int_E f(\lambda y)P_r(x,dy)$$</div>
<p>is bounded and continuous. Integration against those initial laws proves continuity of $\mathcal R$ and also its definition for arbitrary probability laws on $E$.</p>
<p>For the orbit identity, the assertion at $n=0$ is immediate. At the next level the child blocks are independent. Their rescaled component masses are $\sqrt\beta L^{-s(n-1)/2}a$, where $a$ is a physical component size. Running the coalescent for time $r$ gives a merger exponent</p>
<div class="math-display">$$r\bigl(\sqrt\beta L^{-s(n-1)/2}a\bigr)
\bigl(\sqrt\beta L^{-s(n-1)/2}b\bigr)
=\beta L^{-sn}ab.$$</div>
<p>This is exactly the new level's all-pairs layer, including pairs of components inside the same child. Multiplication by $\lambda$ then gives the required normalization at level $n$. Induction proves the identity, also at $\beta=0$. Finally, if an entire orbit converges to $\nu$, continuity gives $\mathcal R^{n+1}\mu\Rightarrow\mathcal R\nu$, while shifting a convergent sequence leaves its limit unchanged. Hence $\mathcal R\nu=\nu$.</p>

## The critical orbit and its topology {#section-critical-orbit-topology}

<a id="tag-NIXH" data-assertion="theorem" data-title="Renormalization detects the critical parameter and distinguishes coordinate decay from norm tightness"></a>
<p>For the exact hierarchical model,</p>
<div class="math-display">$$\mathcal R^n\mu_\beta\Rightarrow\delta_0\text{ in }\mathcal P(E)
\quad\Longleftrightarrow\quad 0\leq\beta&lt;\beta_c.$$</div>
<p>If $d&lt;3\alpha$, the critical laws are tight in $E$, and every subsequential limit is supported on sequences with all coordinates positive. If $d\geq3\alpha$, then</p>
<div class="math-display">$$\|Z_n^{\beta_c}\|_\infty\longrightarrow0,\qquad
\|Z_n^{\beta_c}\|_2^2\longrightarrow L^\alpha-1$$</div>
<p>in probability, and the critical laws are not tight in $E$. More generally, their $\ell^p$ norms tend to infinity in probability for $1\leq p&lt;2$, and tend to zero for $2&lt;p\leq\infty$.</p>
<p><em>Proof.</em> For $\beta&lt;\beta_c$, sharpness gives finite full susceptibility $\chi(\beta)$. The rooted counting identity implies</p>
<div class="math-display">$$\mathbb E\|Z_n^\beta\|_2^2
=\beta L^{-sn}Q^n\mathbb E_\beta|K_n(o)|
\leq\beta\chi(\beta)L^{-\alpha n}\longrightarrow0.$$</div>
<p>Markov's inequality proves norm convergence in probability to zero, and hence the asserted weak convergence.</p>
<p>At criticality put $W_n=\|Z_n^{\beta_c}\|_2^2$. The mean and relative-variance bounds of <a href="/tag/2VXH/">2VXH</a> give $\inf_n\mathbb EW_n&gt;0$ and $\sup_n\mathbb EW_n^2&lt;\infty$. Indeed $W_n=\beta_cL^{-sn}S_2(n,t_n)$, the mean of $S_2$ is comparable to $L^{sn}$, and its variance is at most a fixed multiple of the square of that mean. Cauchy–Schwarz therefore gives fixed $a,b&gt;0$ such that</p>
<div class="math-display">$$\mathbb P(W_n\geq a)\geq b\qquad\text{for every }n.$$</div>
<p>For example use $\mathbb P(W_n\geq\mathbb EW_n/2)\geq(\mathbb EW_n)^2/(4\mathbb EW_n^2)$. Increasing $\beta$ only merges clusters, so both $S_2$ and its prefactor $\beta$ increase in the common monotone coupling. The same lower probability bound holds for every $\beta\geq\beta_c$. Their norm laws cannot converge to zero. This proves the equivalence and, in particular, the source's supremum characterization of $\beta_c$ without requiring a supercritical finite-block giant-component theorem.</p>
<p>When $d&lt;3\alpha$, apply <a href="/tag/THZF/">THZF</a> with $p=2$ and <a href="/tag/ADJZ/">ADJZ</a>, then multiply by the fixed factor $\sqrt{\beta_c}$. This gives tightness and positivity of every limiting coordinate.</p>
<p>When $d\geq3\alpha$, hydrodynamics holds by 6WO3 and UL8V. The universal maximum-tail bound gives $\mathbb E|K_{n,1}|\leq CM_n=o(L^{sn/2})$, so the sup norm tends to zero in probability. By W2VN and KPCV,</p>
<div class="math-display">$$\|Z_n^{\beta_c}\|_2^2
=\beta_cL^{-sn}\mu_n(t_n)\frac{S_2(n,t_n)}{\mu_n(t_n)}
\longrightarrow L^\alpha-1&gt;0.$$</div>
<p>Were these laws tight in $E$, Prokhorov's theorem would supply a weakly convergent subsequence. Each coordinate of its limit would be zero, by continuity of coordinate evaluation and the sup-norm convergence. Its limit law would thus be $\delta_0$. Continuity of the squared norm would then contradict the positive limit just computed. This proves non-tightness.</p>
<p>The remaining norm statements follow from</p>
<div class="math-display">$$\|z\|_2^2\leq\|z\|_\infty^{2-p}\|z\|_p^p\quad(1\leq p&lt;2),\qquad
\|z\|_p^p\leq\|z\|_\infty^{p-2}\|z\|_2^2\quad(2&lt;p&lt;\infty).$$</div>
<p>This gives a precise coordinate and norm interpretation of Remark 7.2. In low dimension, any limit of the entire orbit would be a nonzero fixed point by 7VHT. Tightness alone does not prove convergence of that orbit. Conjecture 7.1 remains a conjecture in the cited source; no present-day status of that problem is asserted here.</p>

## The spin comparison and its normalization {#section-spin-comparison}

<a id="tag-YXL0" data-assertion="proposition" data-title="The spin comparison has a negative gradient sign, an explicit pair convention and a normalization domain"></a>
<p>For a finite graph with symmetric nonnegative weights $J(x,y)$ and zero diagonal, write $r_x=\sum_yJ(x,y)$. With the ordered-pair convention of the source's energy,</p>
<div class="math-display">$$\sum_{x,y}J(x,y)\varphi_x\varphi_y
=\sum_xr_x\varphi_x^2-\frac12\sum_{x,y}J(x,y)(\varphi_x-\varphi_y)^2.\tag{10}$$</div>
<p>In particular the gradient interaction has negative sign. Its single-site factors are $e^{r_xu^2}\mu(du)$; they can vary with $x$ when the row sums vary.</p>
<p>For the hierarchical spin kernel $J(x,y)=L^{-sh(x,y)}$ on distinct vertices, put $Q=L^d$, $r=L^{-s}$, $q=Qr$ and $\lambda=L^{-s/2}$. The corresponding one-step map on single-site laws is</p>
<div class="math-display">$$\int F\,d\mathcal R_{\mathrm{spin}}\mu
=\frac1{Z(\mu)}\int_{\mathbb R^Q}
F\left(\lambda\sum_{i=1}^Qx_i\right)
\exp\left(2r\sum_{i&lt;j}x_ix_j\right)\prod_{i=1}^Q\mu(dx_i),\tag{11}$$</div>
<p>on the domain where $0&lt;Z(\mu)&lt;\infty$. For bounded-support $\mu$, every iterate is defined, and the law of the normalized total spin $L^{-sn/2}\sum_{x\in B_n}\varphi_x$ is $\mathcal R_{\mathrm{spin}}^n\mu$.</p>
<p>For a centered Gaussian input with variance $v&gt;0$, (11) is normalizable exactly when $2r(Q-1)v&lt;1$. In that case its output is centered Gaussian with variance</p>
<div class="math-display">$$\frac{qv}{1-2r(Q-1)v}.$$</div>
<p>It has the nondegenerate Gaussian fixed point</p>
<div class="math-display">$$v_* =\frac{1-q}{2r(Q-1)}.$$</div>
<p><em>Proof.</em> Expanding the squares in (10) and using symmetry proves the identity. The finite-volume partition function is finite, for instance, if $\int e^{r_xu^2}\mu(du)&lt;\infty$ for every vertex: the negative gradient factor is at most one. Bounded support is one sufficient condition.</p>
<p>To derive (11), divide a level-$n$ block into its $Q$ children and let $U_i$ be the unnormalized spin sum in child $i$. Every pair in different children has weight $r^n$. The ordered energy counts both orientations, so its cross-child part is $2r^n\sum_{i&lt;j}U_iU_j$. Set $x_i=r^{(n-1)/2}U_i$. The cross energy becomes $2r\sum_{i&lt;j}x_ix_j$, while the normalized parent spin is $\lambda\sum_i x_i$. Factoring the within-child partition functions proves the recursion. A finite sum and rescaling preserve bounded support, establishing the assertion for every iterate.</p>
<p>For a Gaussian input, the tilted density has precision matrix</p>
<div class="math-display">$$B=(v^{-1}+2r)I-2r\mathbf1\mathbf1^{\mathsf T}.$$</div>
<p>Its eigenvalue in the constant direction is $v^{-1}-2r(Q-1)$; the other eigenvalues are $v^{-1}+2r&gt;0$. Gaussian integration is finite exactly when the former is positive. The variance of $\lambda\sum_i x_i$ is then $\lambda^2Q/[v^{-1}-2r(Q-1)]$, giving the displayed map. Solving its positive fixed-point equation yields $v_*$. Since $2r(Q-1)v_*=1-q&lt;1$, this fixed point is in the normalization domain.</p>
<p>If the energy is instead defined using unordered pairs, the factors $2r$ in (11) and the variance formulas become $r$, and the gradient coefficient in (10) changes accordingly. Either convention is consistent when used throughout. The source's ordered energy, positive gradient display and one-step factor $r$ do not use a common convention. Also its spin map is not defined on all of $\mathcal P(\mathbb R)$: Gaussian inputs with variance at or above the stated threshold already have infinite partition function. These corrections are recorded provisionally. They concern the spin-system comparison and do not enter the percolation proofs.</p>



## The coalescent continuity input {#section-coalescent-input-proof}

<p>The <a href="/tag/3G0K/">edge-clock construction</a> and <a href="/tag/7HLE/">continuity theorem</a> now give a written proof of the square-summable multiplicative-coalescent input used in 7VHT. They allow infinite total mass and prove joint continuity in time and the $\ell^2$ initial state. The argument controls the effect of small components through an explicit <a href="/tag/5HM7/">attachment estimate</a>. This discharges that external input in the exposition; it does not prove convergence of the low-dimensional renormalization orbit or create a compiled Lean correspondence.</p>



## Finite approximations to the coalescent path {#section-coalescent-path-approximation}

<p>The <a href="/tag/GRSC/">finite-approximation theorem</a> now strengthens the linked coalescent input: whenever finite initial mass laws converge weakly in $\ell^2_\downarrow$, their coalescent paths converge on bounded time intervals in the Skorokhod $J_1$ topology. Total initial mass need not be uniformly bounded. This concerns the coalescent evolution from a convergent initial law; it does not establish convergence of the hierarchical renormalization orbit itself.</p>


## Convex comparison for integrable increments {#section-integrable-convex-comparison}

<p>The ordered-discovery proof above uses a finite-valued comparison. The following version allows signed, unbounded increments. Integrability makes the expectation of every affine function finite; a convex expectation may still be $+\infty$. Write $S_0=0$ and $S_i=\sum_{j=1}^i Z_j$.</p>

<a id="tag-3NBK" data-assertion="theorem" data-title="Negative quadrant dependence with preceding sums gives convex comparison for integrable real increments"></a>
<p>Let $Z_1,\ldots,Z_n$ be integrable real random variables such that, for each $2\le i\le n$ and every $u,v\in\mathbb R$,</p>
<div class="math-display">$$
\mathbb P(S_{i-1}\ge u,Z_i\ge v)
\le\mathbb P(S_{i-1}\ge u)\mathbb P(Z_i\ge v).
\tag{1}
$$</div>
<p>Let $Z_1^*,\ldots,Z_n^*$ be independent variables with the same respective marginal laws, and put $S_n^*=\sum_{i=1}^n Z_i^*$. Then, for every real-valued convex $\varphi:\mathbb R\to\mathbb R$,</p>
<div class="math-display">$$
\mathbb E\varphi(S_n)\le\mathbb E\varphi(S_n^*).
$$</div>
<p>Both expectations are well-defined in $(-\infty,\infty]$. In particular, for every $a\in\mathbb R$ and $r\ge1$,</p>
<div class="math-display">$$
\mathbb E(S_n-a)_+\le\mathbb E(S_n^*-a)_+,
\qquad
\mathbb E|S_n-\mathbb ES_n|^r
\le\mathbb E|S_n^*-\mathbb ES_n^*|^r.
$$</div>
<p>The case $n=0$ means two empty sums, and $n=1$ is equality in distribution.</p>

<p><em>Proof.</em> Suppose first that integrable $X,Y$ satisfy the joint-tail bound in (1), and that $Y^*$ has the law of $Y$ independently of $X$. For positive integers $m$, set</p>
<div class="math-display">$$
q_m(x)=\frac1m\left\lfloor m\max\{-m,\min\{x,m\}\}\right\rfloor.
$$</div>
<p>This is an increasing map with finite range. Its upper level sets are upper half-lines, empty sets or the whole line, so $q_m(X),q_m(Y)$ still satisfy the joint-tail bound. For finite-valued variables the <a href="/tag/I2YU/">summation-by-parts argument</a> applies: on ordered supports $x_j,y_k$, the coefficients of the joint upper-tail indicators are</p>
<div class="math-display">$$
\varphi(x_j+y_k)-\varphi(x_{j-1}+y_k)
-\varphi(x_j+y_{k-1})+\varphi(x_{j-1}+y_{k-1})\ge0.
$$</div>
<p>Convexity gives their sign, and the remaining terms depend only on the marginals. Consequently</p>
<div class="math-display">$$
\mathbb E\varphi(q_m(X)+q_m(Y))
\le\mathbb E\varphi(q_m(X)+q_m(Y^*)).
$$</div>
<p>If $\varphi$ is also Lipschitz, this inequality passes to the limit. Indeed,</p>
<div class="math-display">$$
|q_m(x)-x|\le(|x|-m)_++m^{-1},
$$</div>
<p>so each approximation converges in $L^1$ by integrability. We have proved the two-variable comparison for every convex Lipschitz function.</p>
<p>Now fix such a $\varphi$ and proceed by induction on $n$. Apply the two-variable result to $(S_{n-1},Z_n)$, then apply the induction hypothesis to the convex Lipschitz function $x\mapsto\mathbb E\varphi(x+Z_n^*)$. This expectation is finite because $Z_n^*$ is integrable. It follows that</p>
<div class="math-display">$$
\mathbb E\varphi(S_n)
\le\mathbb E\varphi(S_{n-1}+Z_n^*)
\le\mathbb E\varphi(S_{n-1}^*+Z_n^*).
$$</div>
<p>Only the pair $(S_{n-1},Z_n)$ was approximated. We have not assumed that the sequence obtained by truncating all the individual increments still satisfies (1).</p>
<p>To remove the Lipschitz restriction, choose a supporting affine function $\ell_0$ for $\varphi$ at zero and supporting affine functions $\ell_j$ at an enumeration of the rational points. Put $\varphi_m=\max_{0\le j\le m}\ell_j$. Each $\varphi_m$ is convex and Lipschitz, and $\varphi_m\uparrow\varphi$ pointwise. The latter follows from continuity of a finite convex function and boundedness of its supporting slopes on compact intervals: rational contact points can approach any given point.</p>
<p>Since $\varphi_m-\ell_0\ge0$, monotone convergence applies after subtracting $\ell_0$. The two sums have the same finite mean, and hence the same expectation of $\ell_0$. This proves the desired comparison, allowing $+\infty$. A supporting affine lower bound also shows that the negative parts of $\varphi(S_n)$ and $\varphi(S_n^*)$ are integrable. Finally take $\varphi(x)=(x-a)_+$ or $\varphi(x)=|x-\mathbb ES_n|^r$. $\square$</p>

<p>This supplies an explicit integrable form of <a href="https://arxiv.org/html/2211.05686v1">Theorem 6.12 and Remark 6.13</a>. The argument uses only negative quadrant dependence between each increment and its preceding sum. It does not assert full negative association of the sequence or the maximal-process comparisons proved under stronger hypotheses in <a href="https://doi.org/10.1023/A:1007849609234">Shao's comparison theorem</a>. The bounded cluster-discovery variables in I2YU and <a href="/tag/WR5S/">WR5S</a> satisfy the integrability requirement automatically.</p>


<p>Pairwise independence of the increments does not suffice. Give each of $(0,0,0),(0,1,1),(1,0,1),(1,1,0)$ probability $1/4$. The three coordinates are pairwise independent fair Bernoulli variables, but for their sum $S$ and a sum $S^*$ of three independent fair Bernoulli variables,</p>
<div class="math-display">$$\mathbb E(S-1)_+=\frac34&gt;\frac58=\mathbb E(S^*-1)_+.$$</div>
<p>The necessary distinction is visible in (1): $\mathbb P(Z_1+Z_2\ge1,Z_3=1)=1/2$, whereas the product of the two marginal probabilities is $3/8$.</p>

## Absolutely summable sequences {#section-summable-convex-comparison}

<a id="tag-OCZT" data-assertion="corollary" data-title="Convex comparison passes to absolutely integrable countable sums"></a>
<p>Let $(Z_i)_{i\ge1}$ be real random variables satisfying (1) at every finite index, and suppose</p>
<div class="math-display">$$
\sum_{i\ge1}\mathbb E|Z_i|&lt;\infty.
$$</div>
<p>Let $(Z_i^*)_{i\ge1}$ be independent with the same respective marginal laws. Then both series converge absolutely almost surely and in $L^1$. Their sums $S$ and $S^*$ have the same finite mean and satisfy</p>
<div class="math-display">$$
\mathbb E\varphi(S)\le\mathbb E\varphi(S^*)
$$</div>
<p>for every real-valued convex $\varphi$, with the same extended-expectation convention as above. Thus, for every real $t$ and every $r\ge1$,</p>
<div class="math-display">$$
\mathbb E e^{t(S-\mathbb ES)}\le\mathbb E e^{t(S^*-\mathbb ES^*)},
\qquad
\mathbb E|S-\mathbb ES|^r\le\mathbb E|S^*-\mathbb ES^*|^r.
$$</div>
<p><em>Proof.</em> Tonelli gives $\mathbb E\sum_i|Z_i|=\sum_i\mathbb E|Z_i|&lt;\infty$, and the same identity holds for the independent copies. Hence both absolute sums are finite almost surely. The expected absolute remainder after index $n$ is at most $\sum_{i&gt;n}\mathbb E|Z_i|$, which tends to zero. The partial sums therefore converge in $L^1$, and their equal means pass to the limit.</p>
<p>For a convex Lipschitz $\varphi$, apply <a href="/tag/3NBK/">3NBK</a> to the first $n$ increments and use $L^1$ convergence on both sides. For a general finite convex function, use the increasing maxima of supporting affine functions from that proof and subtract their common affine lower bound. Monotone convergence proves the comparison and the two displayed consequences. $\square$</p>

<p>The passage to the limit uses $L^1$ control: almost-sure convergence alone does not justify convergence of first moments or of the hinge expectations. For example, $X_n=n\mathbf1_{\{U\le1/n\}}$ with $U$ uniform on $(0,1)$ converges almost surely to zero but has expectation one for every $n$. This example explains the limit issue; it is not a counterexample to a weaker dependence theorem. No claim is made here for nonintegrable increments or for conditionally convergent series. Independent mathematical review and Lean formalisation remain pending.</p>


## Convex comparison under weak limits {#section-convex-weak-limits}

<p>Write $X\le_{\mathrm{cx}}Y$ when $X,Y$ are integrable real random variables and $\mathbb E\varphi(X)\le\mathbb E\varphi(Y)$ for every real-valued convex function $\varphi$. The expectations may be $+\infty$. Testing the two affine functions $x$ and $-x$ gives equality of means.</p>

<a id="tag-MDB8" data-assertion="theorem" data-title="Uniform integrability preserves convex order under weak limits and a vanishing variance gap identifies the limit law"></a>
<p>Suppose $X_n\le_{\mathrm{cx}}Y_n$, $X_n\Rightarrow X$ and $Y_n\Rightarrow Y$. If $(Y_n)$ is uniformly integrable, then $(X_n)$ is uniformly integrable, $X,Y$ are integrable, their means are equal, and $X\le_{\mathrm{cx}}Y$. Moreover, if $(Y_n^2)$ is uniformly integrable and</p>
<div class="math-display">$$
\mathbb EY_n^2-\mathbb EX_n^2\longrightarrow0,
$$</div>
<p>then $(X_n^2)$ is uniformly integrable and $X,Y$ have the same distribution. The variables in the two sequences need not be defined on a common probability space.</p>

<p><em>Proof.</em> For $q=1$, and also for $q=2$ under the additional hypothesis, the function $x\mapsto(|x|^q-K)_+$ is convex. Consequently</p>
<div class="math-display">$$
\mathbb E(|X_n|^q-K)_+\le\mathbb E(|Y_n|^q-K)_+,
\qquad
\mathbb E\bigl[|X_n|^q\mathbf1_{\{|X_n|^q&gt;2K\}}\bigr]
\le2\mathbb E(|Y_n|^q-K)_+.
$$</div>
<p>The right side tends to zero uniformly in $n$ as $K\to\infty$. This proves the asserted uniform integrability. Weak convergence and truncation on a large bounded interval now give convergence of the means and of the expectations of every convex Lipschitz function. Passing the finite-$n$ comparison to the limit proves it for those functions. The increasing supporting-affine approximants used in <a href="/tag/3NBK/">3NBK</a>, with their common affine lower bound subtracted, extend the comparison to every finite convex function by monotone convergence.</p>
<p>Under the second hypothesis, uniform integrability also gives convergence of the second moments, so $\mathbb EX^2=\mathbb EY^2&lt;\infty$. Put $c_Z(t)=\mathbb E(Z-t)_+$ and $d(t)=c_Y(t)-c_X(t)$. Convex order makes $d$ nonnegative and continuous. Equality of means gives, for $t\ge0$,</p>
<div class="math-display">$$
d(-t)=\mathbb E(-Y-t)_+-\mathbb E(-X-t)_+.
$$</div>
<p>Integrating the positive and negative parts of the square by Tonelli therefore yields</p>
<div class="math-display">$$
\int_{\mathbb R}d(t)\,dt
=\frac12\bigl(\mathbb EY^2-\mathbb EX^2\bigr)=0.
$$</div>
<p>Thus $d$ vanishes everywhere. The right derivative of $c_Z$ is $-\mathbb P(Z&gt;t)$, so equality of these functions identifies the distributions. $\square$</p>

<p>Applied to the partial sums in 3NBK, the first assertion requires only weak convergence of both sums and uniform integrability of the independent sums. In particular, convergence of both sums in $L^1$ suffices; the absolute first-moment summability in <a href="/tag/OCZT/">OCZT</a> is one way to obtain it. This also covers a conditionally convergent series when these limit hypotheses are separately verified. It does not establish convergence of an arbitrary dependent series.</p>
<p>The uniform integrability condition cannot simply be dropped. Let $R$ be a fair sign and, independently, let $B_n$ be Bernoulli with parameter $1/n$. Set $X_n=R$ and $Y_n=nRB_n$. Since $\mathbb E[Y_n\mid R]=R$, conditional Jensen gives $X_n\le_{\mathrm{cx}}Y_n$. But $Y_n\to0$ in probability while $X_n$ has the same nonconstant law for every $n$. All means are zero; the lost first absolute moment is visible in $\mathbb E|Y_n|=1$.</p>

## A sufficient Gaussian fluctuation criterion {#section-gaussian-comparison-criterion}

<p>The preceding result distinguishes a Gaussian upper comparison from a Gaussian limit. For an ordered discovery, dependence can reduce the variance even when the independent comparison satisfies a central limit theorem.</p>

<a id="tag-25Z0" data-assertion="theorem" data-title="Lindeberg control and a negligible variance deficit give a Gaussian limit for ordered negatively dependent sums"></a>
<p>For each $n$, let $Z_{n,1},\ldots,Z_{n,k_n}$ be square-integrable real random variables such that each $Z_{n,i}$ is negatively quadrant dependent with $\sum_{j&lt;i}Z_{n,j}$. Set</p>
<div class="math-display">$$
D_n=\sum_{i=1}^{k_n}(Z_{n,i}-\mathbb EZ_{n,i}),
\qquad
V_n=\sum_{i=1}^{k_n}\operatorname{Var}(Z_{n,i})&gt;0.
$$</div>
<p>Suppose that for every $\varepsilon&gt;0$,</p>
<div class="math-display">$$
\frac1{V_n}\sum_{i=1}^{k_n}
\mathbb E\left[(Z_{n,i}-\mathbb EZ_{n,i})^2
\mathbf1_{\{|Z_{n,i}-\mathbb EZ_{n,i}|&gt;\varepsilon\sqrt{V_n}\}}\right]
\longrightarrow0.
\tag{2}
$$</div>
<p>Then $(D_n/\sqrt{V_n})$ is tight and its squares are uniformly integrable. Every subsequential weak limit $X$ satisfies $X\le_{\mathrm{cx}}G$, where $G$ is standard normal. If, in addition,</p>
<div class="math-display">$$
\frac{\operatorname{Var}(D_n)}{V_n}\longrightarrow1,
\tag{3}
$$</div>
<p>then $D_n/\sqrt{V_n}\Rightarrow G$. The actual variance is positive for all sufficiently large $n$, and the same conclusion holds with the denominator $\sqrt{\operatorname{Var}(D_n)}$. For $0&lt;r\le2$, the corresponding absolute $r$th moments converge to $\mathbb E|G|^r$.</p>

<p><em>Proof.</em> Write $W_{n,i}=(Z_{n,i}-\mathbb EZ_{n,i})/\sqrt{V_n}$ and let $W_{n,i}^*$ be independent copies within each row. Translation and positive rescaling preserve the quadrant condition, so 3NBK gives</p>
<div class="math-display">$$
X_n:=D_n/\sqrt{V_n}\le_{\mathrm{cx}}Y_n:=\sum_iW_{n,i}^*,
\qquad
\mathbb EX_n^2\le\mathbb EY_n^2=1.
$$</div>
<p>The second-moment bound proves tightness of $(X_n)$. We give the independent limit argument explicitly. For fixed real $t$ and $\delta&gt;0$, Taylor's formula on $|W_{n,i}^*|\le\delta$ and the quadratic remainder bound on its complement give</p>
<div class="math-display">$$
\mathbb E e^{itW_{n,i}^*}
=1-\frac{t^2}{2}\mathbb E(W_{n,i}^*)^2+r_{n,i},
\qquad
\sum_i|r_{n,i}|
\le C_t\delta+C_t\sum_i\mathbb E\bigl[(W_{n,i}^*)^2\mathbf1_{\{|W_{n,i}^*|&gt;\delta\}}\bigr].
$$</div>
<p>First let $n\to\infty$ and then $\delta\downarrow0$. Condition (2) makes the remainder sum tend to zero. It also gives</p>
<div class="math-display">$$
\max_i\mathbb E(W_{n,i}^*)^2
\le\delta^2+\sum_i\mathbb E\bigl[(W_{n,i}^*)^2\mathbf1_{\{|W_{n,i}^*|&gt;\delta\}}\bigr],
\qquad
\limsup_{n\to\infty}\max_i\mathbb E(W_{n,i}^*)^2\le\delta^2.
$$</div>
<p>Letting $\delta\downarrow0$ proves that the largest variance vanishes. Thus, writing each characteristic-function factor as $1+a_{n,i}$, we have $\max_i|a_{n,i}|\to0$, $\sum_i a_{n,i}\to-t^2/2$ and $\sum_i|a_{n,i}|^2\to0$; the last assertion uses the boundedness of $\sum_i|a_{n,i}|$. Independence and $\log(1+a)=a+O(|a|^2)$ show that the characteristic function of $Y_n$ tends to $e^{-t^2/2}$. The continuity theorem for characteristic functions gives $Y_n\Rightarrow G$.</p>
<p>The identity $\mathbb EY_n^2=\mathbb EG^2=1$ also gives uniform integrability of $(Y_n^2)$. Indeed, weak convergence applied to $\min\{x^2,K\}$ gives</p>
<div class="math-display">$$
\lim_{n\to\infty}\mathbb E(Y_n^2-K)_+
=1-\mathbb E\min\{G^2,K\}\longrightarrow0
\quad\text{as }K\to\infty;
$$</div>
<p>the finitely many earlier indices can be controlled separately. The tail bound in <a href="/tag/MDB8/">MDB8</a> transfers this uniform integrability to $(X_n^2)$. Apply its first assertion along any weakly convergent subsequence to obtain $X\le_{\mathrm{cx}}G$. If (3) holds, its second assertion identifies every such limit as $G$. Tightness then gives convergence of the whole sequence. Uniform integrability proves convergence of the absolute moments through order two. Finally, (3) permits replacement of $\sqrt{V_n}$ by the actual standard deviation. $\square$</p>

<p>The variance deficit in (3) can be written exactly as</p>
<div class="math-display">$$
V_n-\operatorname{Var}(D_n)
=-2\sum_{i=2}^{k_n}\operatorname{Cov}\left(\sum_{j&lt;i}Z_{n,j},Z_{n,i}\right)\ge0.
$$</div>
<p>Each covariance is nonpositive: apply the two-variable convex comparison to the square of the centered sum. Condition (3) asks that their combined contribution be negligible compared with $V_n$.</p>
<p>For example, independent fair signs $R_1,\ldots,R_n$ arranged as $Z_{n,2j-1}=R_j$, $Z_{n,2j}=-R_j$ satisfy the quadrant condition and (2), with $V_n=2n$, but $D_n=0$. The independent comparison tends to a Gaussian while the dependent sum is identically zero. This shows why the variance condition cannot be inferred from the independent limit.</p>
<p>For cluster power sums, use the ordered-discovery contributions of <a href="/tag/I2YU/">I2YU</a> or <a href="/tag/WR5S/">WR5S</a>. Conditions (2) and (3) are additional estimates to establish in the model; neither is asserted here for the hierarchical critical regime. This is a sufficient route to a distributional central limit theorem, not a resolution of <a href="https://arxiv.org/html/2211.05686v1">Remark 6.14</a>. That remark also asks for moments of every order; the conclusion above controls moments only through order two. Independent mathematical review and Lean formalisation remain pending.</p>


## Independent discovery sums in the hierarchical regime {#section-hierarchical-discovery-comparison}

<p>We can now check the independent comparison in the actual hierarchical model. Use the critical exact block process with $d\ge3\alpha$. Hydrodynamics holds by <a href="/tag/6WO3/">6WO3</a> and <a href="/tag/UL8V/">UL8V</a>. Write $N_n=L^{dn}$, $f_{q,n}(t)=\mathbb ES_q(n,t)$, $\mu_n=f_{2,n}$ and $\nu_n=f_{3,n}$.</p>

<a id="tag-VH4M" data-assertion="theorem" data-title="Independent ordered-discovery sums have Gaussian limits for every fixed hierarchical power sum"></a>
<p>Fix an integer $p\ge2$. At each level $n$ and time $0\le t\le t_n$, choose any deterministic enumeration of the block vertices. Let $Z_{n,i}$ be the $p$th power of the cluster size at vertex $i$ if its cluster contains no earlier vertex, and zero otherwise. Suppressing $t$ in this notation, put</p>
<div class="math-display">$$
m_{n,i}=\mathbb EZ_{n,i},\qquad
A_{p,n}=\sum_{i=1}^{N_n}\operatorname{Var}(Z_{n,i}).
$$</div>
<p>Then, uniformly over the time and the enumeration,</p>
<div class="math-display">$$
0\le f_{2p,n}-A_{p,n}=\sum_i m_{n,i}^2
\le\frac{f_{p,n}f_{p+1,n}}{N_n}=o(f_{2p,n}),
\tag{4}
$$</div>
<div class="math-display">$$
\frac{\sum_i\mathbb E(Z_{n,i}-m_{n,i})^4}{A_{p,n}^2}
\le\frac{f_{4p,n}}{A_{p,n}^2}\longrightarrow0.
\tag{5}
$$</div>
<p>In particular $A_{p,n}$ is positive for all sufficiently large $n$. For any sequence of times and deterministic enumerations, let $Z_{n,i}^*$ be independent variables with the respective marginal laws of the $Z_{n,i}$. Then</p>
<div class="math-display">$$
\frac{\sum_i(Z_{n,i}^*-m_{n,i})}{\sqrt{f_{2p,n}}}
\Rightarrow G,
$$</div>
<p>where $G$ is standard normal. The actual centered variables $(S_p-f_{p,n})/\sqrt{f_{2p,n}}$ are tight and their squares are uniformly integrable; every subsequential weak limit is bounded above by $G$ in convex order.</p>

<p><em>Proof.</em> Every cluster contributes at exactly one vertex, so $\sum_iZ_{n,i}=S_p$ and $\sum_iZ_{n,i}^2=S_{2p}$. These identities give the equality in (4). The rooted identity and transitivity from <a href="/tag/54V4/">54V4</a> give</p>
<div class="math-display">$$
m_{n,i}\le\mathbb E|K_{n,t}(v_i)|^p
=\frac{f_{p+1,n}}{N_n},
\qquad
\sum_i m_{n,i}=f_{p,n}.
$$</div>
<p>Bounding one factor of each $m_{n,i}^2$ by this common upper bound proves the inequality. It does not identify a discovery contribution with the rooted cluster variable: the avoidance of earlier vertices is still present.</p>
<p>Set $a_q=(2q-5)!!$ with $a_2=1$. The uniform equivalents in <a href="/tag/ANYT/">ANYT</a> imply</p>
<div class="math-display">$$
\frac{f_{p,n}f_{p+1,n}}{N_nf_{2p,n}}
\sim\frac{a_pa_{p+1}}{a_{2p}}\frac{\mu_n^2}{N_n\nu_n},
\qquad
\frac{\mu_n^2}{N_n\nu_n}=L^{-\alpha n+o(n)}\longrightarrow0.
$$</div>
<p>Thus $A_{p,n}\sim f_{2p,n}$ uniformly, independently of the enumeration. The nonnegative-variable fourth-moment bound in <a href="/tag/I2YU/">I2YU</a>, together with $\sum_iZ_{n,i}^4=S_{4p}$, gives the inequality in (5). Another application of ANYT gives</p>
<div class="math-display">$$
\frac{f_{4p,n}}{f_{2p,n}^2}
\sim\frac{a_{4p}}{a_{2p}^2}\frac{\nu_n^2}{\mu_n^3}
\longrightarrow0
$$</div>
<p>by <a href="/tag/KPCV/">KPCV</a>. This proves (5). For every $\varepsilon&gt;0$, the Lindeberg expression is bounded by</p>
<div class="math-display">$$
\frac1{A_{p,n}}\sum_i\mathbb E\left[(Z_{n,i}-m_{n,i})^2
\mathbf1_{\{|Z_{n,i}-m_{n,i}|&gt;\varepsilon\sqrt{A_{p,n}}\}}\right]
\le\frac{\sum_i\mathbb E(Z_{n,i}-m_{n,i})^4}{\varepsilon^2A_{p,n}^2}
\longrightarrow0.
$$</div>
<p>Apply <a href="/tag/25Z0/">25Z0</a> to the independent copies, whose variance deficit is zero, to obtain their Gaussian limit. For the actual discovery sums, I2YU supplies the required quadrant dependence, and the first part of 25Z0 gives tightness, uniform integrability of squares and the comparison of limiting laws. Finally replace $A_{p,n}$ by its equivalent $f_{2p,n}$. $\square$</p>

## The variance gap for squared mass {#section-hierarchical-discovery-variance-gap}

<a id="tag-Q7QG" data-assertion="corollary" data-title="Hierarchical squared mass has two thirds of the independent discovery variance"></a>
<p>In the same critical exact model with $d\ge3\alpha$, take $p=2$ and write $B_n(t)=\operatorname{Var}(S_2(n,t))$. Uniformly over time and deterministic vertex enumeration,</p>
<div class="math-display">$$
A_{2,n}\sim f_{4,n},\qquad
B_n\sim\frac23f_{4,n},\qquad
\frac{B_n}{A_{2,n}}\longrightarrow\frac23,
\qquad
A_{2,n}-B_n\sim\frac13f_{4,n}.
\tag{6}
$$</div>
<p>Equivalently, with the squared-mass discovery contributions,</p>
<div class="math-display">$$
\sum_{i=2}^{N_n}\operatorname{Cov}\left(\sum_{j&lt;i}Z_{n,j},Z_{n,i}\right)
\sim-\frac16 f_{4,n}.
$$</div>
<p>The variance-matching hypothesis (3) therefore fails for these discovery variables. Nevertheless, the variables</p>
<div class="math-display">$$
H_n=\frac{S_2(n,t)-\mu_n(t)}{\sqrt{B_n(t)}}
$$</div>
<p>are tight for all sufficiently large $n$. Along any sequence of times, every subsequential weak limit $H$ has mean zero, variance one and</p>
<div class="math-display">$$
H\le_{\mathrm{cx}}\sqrt{\frac32}\,G.
\tag{7}
$$</div>
<p>In particular, for every real $u$ and every $x&gt;0$,</p>
<div class="math-display">$$
\mathbb E e^{uH}\le e^{3u^2/4},\qquad
\mathbb P(|H|\ge x)\le2e^{-x^2/3},\qquad
\mathbb EH^4\le\frac{27}{4}.
$$</div>

<p><em>Proof.</em> The first equivalent in (6) is <a href="/tag/VH4M/">VH4M</a>. The second is the variance equivalent proved in <a href="/tag/LWRN/">LWRN</a>, corresponding to Proposition 6.5 of the cited preprint. Subtracting and dividing the two equivalents gives the other statements in (6). The exact covariance-deficit identity following 25Z0 gives the covariance sum.</p>
<p>VH4M gives tightness and uniform integrability of the squares of $X_n=(S_2-\mu_n)/\sqrt{f_{4,n}}$. Since $B_n/f_{4,n}\to2/3$, the same is true after normalization by $\sqrt{B_n}$. In any weak limit of $H_n$, the mean and second moment therefore retain their finite-$n$ values zero and one. Along the same subsequence, $X_n\Rightarrow\sqrt{2/3}\,H$, and VH4M gives $\sqrt{2/3}\,H\le_{\mathrm{cx}}G$. Positive rescaling proves (7).</p>
<p>Apply (7) to $e^{ux}$ and $x^4$ to obtain the moment bounds. For the upper tail, Markov's inequality gives $\mathbb P(H\ge x)\le\exp(-ux+3u^2/4)$ for $u&gt;0$; its minimum occurs at $u=2x/3$. Apply the same argument to $-H$ and add the two bounds. $\square$</p>

<p>This calculation settles the two checks left open after 25Z0 for squared-mass discovery: the independent Lindeberg condition holds, but the variance deficit is not negligible, at the critical dimension as well as above it. No choice of deterministic vertex order removes the asymptotic gap. This does not contradict the conjectured Gaussian fluctuations: a standard normal variable is itself dominated in convex order by $\sqrt{3/2}\,G$. It shows that equality of variances cannot be used to identify the limit through this particular independent comparison.</p>
<p>The exponential and fourth-moment bounds above concern the limiting laws. They do not assert convergence of higher moments or exponential moments of the finite-block variables. Neither the Gaussian conjecture in <a href="https://arxiv.org/html/2211.05686v1">Remark 6.14</a> nor the laws for general comparable kernels are established here. No new source error is diagnosed; all existing provisional errata remain unchanged. Independent mathematical review and Lean formalisation remain pending.</p>


## Moments of the independent comparison {#section-independent-comparison-moments}

<p>The fixed-order moment estimates give more than the fourth-moment Lindeberg bound. The following array argument lets us pass all fixed moments to subsequential limits without identifying those limits as Gaussian.</p>

<a id="tag-9FO5" data-assertion="proposition" data-title="Vanishing aggregate higher moments give Gaussian moments for independent triangular arrays"></a>
<p>For each $n$, let $W_{n,1},\ldots,W_{n,k_n}$ be independent centered real random variables with moments of every order. Suppose that</p>
<div class="math-display">$$
\sum_i\mathbb EW_{n,i}^2=1,
\qquad
T_{j,n}:=\sum_i\mathbb E|W_{n,i}|^j\longrightarrow0
\quad\text{for every fixed integer }j\ge3.
$$</div>
<p>Then $Y_n=\sum_iW_{n,i}$ converges in distribution to a standard normal variable $G$, and for every positive integer $k$ and every real $r&gt;0$,</p>
<div class="math-display">$$
\mathbb EY_n^k\longrightarrow\mathbb EG^k,
\qquad
\mathbb E|Y_n|^r\longrightarrow\mathbb E|G|^r.
$$</div>
<p>If $X_n\le_{\mathrm{cx}}Y_n$, then $|X_n|^r$ is uniformly integrable for every fixed $r&gt;0$. Along every subsequence on which $X_n\Rightarrow X$, all its fixed absolute moments, and all its integer moments, converge to those of $X$. Moreover $X\le_{\mathrm{cx}}G$ and, for $r\ge1$,</p>
<div class="math-display">$$
\limsup_n\mathbb E|X_n|^r
\le\mathbb E|G|^r
=\frac{2^{r/2}\Gamma((r+1)/2)}{\sqrt\pi}.
$$</div>

<p><em>Proof.</em> The fourth-moment assumption gives Lindeberg's condition, so the independent part of <a href="/tag/25Z0/">25Z0</a> gives $Y_n\Rightarrow G$. We calculate its moments explicitly. Write $v_{n,i}=\mathbb EW_{n,i}^2$. In the expansion of $Y_n^k$, group the positions $1,\ldots,k$ according to which summand index they carry. Independence gives</p>
<div class="math-display">$$
\mathbb EY_n^k
=\sum_{\pi}\ \sum_{\iota:\pi\hookrightarrow\{1,\ldots,k_n\}}
\prod_{B\in\pi}\mathbb EW_{n,\iota(B)}^{|B|},
$$</div>
<p>where the first sum is over set partitions of $\{1,\ldots,k\}$ and the second assigns distinct indices to its blocks. A singleton block makes the product zero. For a partition with all block sizes at least two, the absolute value of its contribution is at most $\prod_{B\in\pi}T_{|B|,n}$, where $T_{2,n}=1$. If any block has size at least three, this tends to zero. There are only finitely many partitions for fixed $k$.</p>
<p>Only pair partitions remain. For $k=2m$, each such partition contributes</p>
<div class="math-display">$$
R_{m,n}=\sum_{i_1,\ldots,i_m\ \mathrm{distinct}}
\prod_{a=1}^m v_{n,i_a}.
$$</div>
<p>For $m=1$ this equals one. For $m\ge2$, bounding the tuples with a repeated index gives</p>
<div class="math-display">$$
0\le1-R_{m,n}
\le\binom m2\sum_i v_{n,i}^2
\le\binom m2 T_{4,n}\longrightarrow0.
$$</div>
<p>There are $(2m-1)!!$ pair partitions. For odd $k$ there are none. This proves convergence of the integer moments, including the centered first moment.</p>
<p>Given any fixed $r&gt;0$, choose an even integer $2m&gt;r$. The convergent $2m$th moments give a uniform bound, and</p>
<div class="math-display">$$
\mathbb E\bigl[|Y_n|^r\mathbf1_{\{|Y_n|&gt;R\}}\bigr]
\le R^{r-2m}\mathbb E|Y_n|^{2m}.
$$</div>
<p>This proves uniform integrability and hence convergence of the absolute $r$th moments under weak convergence. Integrating the normal density gives the stated gamma formula.</p>
<p>For the dominated variables, convex order gives $\mathbb E|X_n|^{2m}\le\mathbb E|Y_n|^{2m}$. The same tail bound proves uniform integrability at every smaller fixed power, including powers below one. Weak convergence and truncation then give convergence of absolute moments and signed integer moments along any convergent subsequence. The first part of <a href="/tag/MDB8/">MDB8</a> gives $X\le_{\mathrm{cx}}G$. Finally apply convex order to $|x|^r$, which is convex for $r\ge1$, and use the absolute-moment convergence of $Y_n$. $\square$</p>

## All fixed moments of hierarchical fluctuation limits {#section-hierarchical-fluctuation-moments}

<a id="tag-V7MP" data-assertion="theorem" data-title="Hierarchical discovery comparison gives convergence of every fixed moment along fluctuation subsequences"></a>
<p>In the critical exact hierarchical model with $d\ge3\alpha$, fix an integer $p\ge2$ and retain the notation of <a href="/tag/VH4M/">VH4M</a>. Set</p>
<div class="math-display">$$
X_{p,n}(t)=\frac{S_p(n,t)-f_{p,n}(t)}{\sqrt{f_{2p,n}(t)}}.
$$</div>
<p>Along any sequence of block times, $|X_{p,n}|^r$ is uniformly integrable for every fixed $r&gt;0$. Consequently every weakly convergent subsequence converges in all fixed absolute moments and in all integer moments. For every fixed $r\ge1$,</p>
<div class="math-display">$$
\limsup_{n\to\infty}\ \sup_{0\le t\le t_n}
\mathbb E|X_{p,n}(t)|^r\le\mathbb E|G|^r.
\tag{8}
$$</div>
<p>The independent discovery comparisons, with the same normalization, converge to $G$ in distribution and in all fixed moments, uniformly in the choice of intermediate times and deterministic vertex orders.</p>
<p>In particular, for the variance-normalized squared mass $H_n$ of <a href="/tag/Q7QG/">Q7QG</a>, all fixed moments converge along every weakly convergent subsequence, and for $r\ge1$,</p>
<div class="math-display">$$
\limsup_{n\to\infty}\ \sup_{0\le t\le t_n}
\mathbb E|H_n(t)|^r
\le\left(\frac32\right)^{r/2}\mathbb E|G|^r.
\tag{9}
$$</div>
<p>Here $H_n$ is used only for sufficiently large $n$, when its variance is positive. Its limiting laws still need not be identified by these inequalities.</p>

<p><em>Proof.</em> Fix $p$ and an integer $j\ge3$. A cluster contributes at exactly one discovery vertex, so $\sum_iZ_{n,i}^j=S_{pj}$. For a nonnegative variable $Z$ with mean $m$, convexity gives</p>
<div class="math-display">$$
\mathbb E|Z-m|^j
\le2^{j-1}(\mathbb EZ^j+m^j)
\le2^j\mathbb EZ^j.
$$</div>
<p>Let $A_{p,n}=\sum_i\operatorname{Var}(Z_{n,i})$. By VH4M it is positive eventually and asymptotic to $f_{2p,n}$, uniformly over time and deterministic order. For independent copies $Z_{n,i}^*$ of the discovery marginals, put $W_{n,i}=(Z_{n,i}^*-m_{n,i})/\sqrt{A_{p,n}}$. Then</p>
<div class="math-display">$$
\sum_i\mathbb E|W_{n,i}|^j
\le\frac{2^j f_{pj,n}}{A_{p,n}^{j/2}}.
$$</div>
<p>Writing $a_q=(2q-5)!!$ as in <a href="/tag/ANYT/">ANYT</a>, its fixed-index equivalents give</p>
<div class="math-display">$$
\frac{f_{pj,n}}{f_{2p,n}^{j/2}}
\sim\frac{a_{pj}}{a_{2p}^{j/2}}
\left(\frac{\nu_n^2}{\mu_n^3}\right)^{j/2-1}
\longrightarrow0
$$</div>
<p>uniformly in time, by <a href="/tag/KPCV/">KPCV</a>. The exponent is positive because $j&gt;2$. Thus 9FO5 applies. The discovery quadrant condition from <a href="/tag/I2YU/">I2YU</a> and the integrable comparison <a href="/tag/3NBK/">3NBK</a> give</p>
<div class="math-display">$$
\frac{S_p-f_{p,n}}{\sqrt{A_{p,n}}}
\le_{\mathrm{cx}}\sum_i W_{n,i}.
$$</div>
<p>The dominated-variable conclusions of 9FO5 therefore apply to the actual sums. Replacing $A_{p,n}$ by its equivalent $f_{2p,n}$ preserves all fixed-moment conclusions and the uniform bounds. Every estimate above is uniform in time and order. If uniform convergence or (8) failed, one could choose a sequence of times and orders witnessing the failure and apply the same argument to that sequence, a contradiction.</p>
<p>Finally, Q7QG gives $\operatorname{Var}(S_2)/f_{4,n}\to2/3$ uniformly. Rescaling (8) and the uniform-integrability bounds proves (9) and the subsequential moment assertion for $H_n$. $\square$</p>

<p>This strengthens the preceding treatment of the fluctuation limits: all fixed moments now pass along weakly convergent subsequences. It does not make those moments Gaussian, remove the one-third variance gap, or establish the Gaussian conjecture in the cited version's Remark 6.14. If a Gaussian distributional limit is proved separately for $H_n$, this theorem will supply convergence of each fixed moment to the corresponding Gaussian moment.</p>
<p>All indices here are fixed before the block scale tends to infinity. The constants depend on those indices; no uniform bound as $p$ or $r$ grows is asserted. In particular, these conclusions do not justify exchanging an infinite exponential series with the limit or claim convergence of exponential moments. The model remains the exact hierarchical kernel. No new source error or journal-version comparison is claimed; attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>.</p>


## Gaussian fluctuations of squared mass {#section-squared-mass-gaussian-limit}

<p>The preceding moment bounds control the error terms in the centered coalescent equation. That equation identifies the limit for squared mass even though its variance differs from the independent discovery variance.</p>

<a id="tag-J0DE" data-assertion="theorem" data-title="Critical hierarchical squared mass has Gaussian fluctuations and all fixed Gaussian moments"></a>
<p>Consider the critical exact hierarchical model of <a href="/tag/VI3Y/">VI3Y</a>, with $0&lt;\alpha&lt;d$ and $d\ge3\alpha$. Write</p>
<div class="math-display">$$
\mu_n(t)=\mathbb ES_2(n,t),\qquad
V_n(t)=\operatorname{Var}(S_2(n,t)),\qquad
H_n(t)=\frac{S_2(n,t)-\mu_n(t)}{\sqrt{V_n(t)}}.
$$</div>
<p>The variance is positive for all sufficiently large $n$, uniformly over $0\le t\le t_n$. For every deterministic sequence of times $s_n\in[0,t_n]$, $H_n(s_n)$ converges in distribution to a standard normal variable $G$. For every fixed nonnegative integer $k$ and every fixed real $r&gt;0$,</p>
<div class="math-display">$$
\sup_{0\le t\le t_n}\left|\mathbb EH_n(t)^k-m_k\right|\longrightarrow0,
\qquad
\sup_{0\le t\le t_n}\left|\mathbb E|H_n(t)|^r-\mathbb E|G|^r\right|\longrightarrow0,
$$</div>
<div class="math-display">$$
m_k=\mathbb EG^k=
\begin{cases}0,&amp;k\text{ odd},\\(k-1)!!,&amp;k\text{ even},\end{cases}
\qquad m_0=(-1)!!=1.
$$</div>
<p>Distributional convergence is also uniform in time in the sense that, for each bounded continuous function $h$, $\sup_{0\le t\le t_n}|\mathbb Eh(H_n(t))-\mathbb Eh(G)|\to0$.</p>

<p><em>Proof.</em> Suppress $n,t$ when there is no ambiguity. Set $\nu=\mathbb ES_3$, $f_j=\mathbb ES_j$,</p>
<div class="math-display">$$
Z=S_2-\mu,\qquad F=\frac{2\nu^2}{\mu},\qquad
\eta=\frac{\nu^2}{\mu^3},\qquad
M_k=\mathbb EZ^k,\qquad g_k=\frac{M_k}{F^{k/2}}.
$$</div>
<p>All limits and bounds below are uniform over the level's time interval; constants may depend on fixed moment indices. Hydrodynamics holds in the stated dimensions by <a href="/tag/6WO3/">6WO3</a> and <a href="/tag/UL8V/">UL8V</a>. The estimates already proved in <a href="/tag/ANYT/">ANYT</a>, <a href="/tag/KPCV/">KPCV</a>, <a href="/tag/LWRN/">LWRN</a> and <a href="/tag/V7MP/">V7MP</a> give</p>
<div class="math-display">$$
\eta\longrightarrow0,\qquad
\frac{V}{F}\longrightarrow1,\qquad
\mathbb E|Z|^a=O(F^{a/2})\quad(a&gt;0\text{ fixed}),
\qquad
\left\|\frac{S_j}{f_j}-1\right\|_a\longrightarrow0
\quad(j\ge2,\ a\ge1\text{ fixed}).
\tag{10}
$$</div>
<p>In particular, $F&gt;0$ and the $g_k$ are bounded. The exact mean and third-moment equations used in ANYT imply</p>
<div class="math-display">$$
\frac{F'}F=(5+o(1))\mu,
\qquad
I_n:=\int_0^{t_n}\mu_n(t)\,dt\longrightarrow\alpha\log L.
\tag{11}
$$</div>
<p>The second assertion follows from <a href="/tag/W2VN/">W2VN</a>. For the first, write $\mu'/\mu=(1-\epsilon_n)\mu$ and $\nu'/\nu=3(1-\epsilon_{3,n})\mu$, where both errors tend uniformly to zero, and differentiate $F=2\nu^2/\mu$. No derivative of an asymptotic equivalent is being taken.</p>

<p>We next derive the centered moment equation. A merger of masses $a,b$ occurs at rate $ab$ and increases $S_2$ by $2ab$. The time-dependent finite generator of <a href="/tag/Z960/">Z960</a>, with the derivative of the centering retained, therefore gives, for $k\ge2$,</p>
<div class="math-display">$$
\begin{aligned}
M_k'={}&2k\mu M_k
+k\mathbb E\left[Z^{k-1}\bigl(Z^2-V-(S_4-f_4)\bigr)\right]\\
&amp;+\sum_{j=2}^k\binom kj2^{j-1}
\mathbb E\left[Z^{k-j}(S_{j+1}^2-S_{2j+2})\right].
\end{aligned}
\tag{12}
$$</div>
<p>Indeed the single-jump term is $k\mathbb E[Z^{k-1}(S_2^2-S_4-\mu')]$, with $\mu'=\mu^2+V-f_4$. For the $j$th jump power, summing $ab(2ab)^j$ over unordered pairs gives $2^{j-1}(S_{j+1}^2-S_{2j+2})$. These identities hold for every finite initial law, with no independence assumption on the power sums.</p>

<p>The second term in (12) is negligible on the scale $\mu F^{k/2}$. In fact, (10), Cauchy–Schwarz and $f_4\asymp F$ give</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E|Z|^{k+1}+V\mathbb E|Z|^{k-1}
&amp;=O(F^{(k+1)/2}),\\
\mathbb E\left[|Z|^{k-1}|S_4-f_4|\right]
&amp;\le(\mathbb E|Z|^{2k-2})^{1/2}\|S_4-f_4\|_2
=O(F^{(k+1)/2}).
\end{aligned}
$$</div>
<p>Dividing by $\mu F^{k/2}$ leaves $O(\sqrt F/\mu)=O(\sqrt\eta)$.</p>
<p>For $j=2$, KPCV gives $\|S_3^2-\nu^2\|_2=o(\nu^2)$: use $S_3/\nu\to1$ in $L^4$ and factor the difference of squares. Also $\|S_6\|_2=O(f_6)=o(\nu^2)$ by ANYT, since $f_6/\nu^2=O(\eta)$. A further Cauchy–Schwarz bound, with $\mathbb E|Z|^0=1$ when $k=2$, now gives</p>
<div class="math-display">$$
\mathbb E\left[Z^{k-2}(S_3^2-S_6)\right]
=\nu^2M_{k-2}+o\bigl(\nu^2F^{(k-2)/2}\bigr).
$$</div>
<p>For $3\le j\le k$, the diagonal subtraction is nonnegative and at most $S_{j+1}^2$. Using (10) once more,</p>
<div class="math-display">$$
\left|\mathbb E\left[Z^{k-j}(S_{j+1}^2-S_{2j+2})\right]\right|
\le(\mathbb E|Z|^{2k-2j})^{1/2}(\mathbb ES_{j+1}^4)^{1/2}
=O\bigl(F^{(k-j)/2}f_{j+1}^2\bigr).
$$</div>
<p>Here and below the zeroth moment is one. Since $f_{j+1}\asymp\nu^{j-1}\mu^{-(j-2)}$, division by $\mu F^{k/2}$ gives</p>
<div class="math-display">$$
O\left(\frac{f_{j+1}^2}{\mu F^{j/2}}\right)
=O\bigl(\eta^{(j-2)/2}\bigr)=o(1).
$$</div>
<p>There are only finitely many terms for fixed $k$. Equation (12) consequently reduces to</p>
<div class="math-display">$$
M_k'=2k\mu M_k+k(k-1)\nu^2M_{k-2}
+o(\mu F^{k/2}).
$$</div>
<p>Divide by $F^{k/2}$ and use (11), boundedness of $g_k$, and $\nu^2/F=\mu/2$. The normalized equation is</p>
<div class="math-display">$$
g_k'=\frac{k\mu}{2}\bigl((k-1)g_{k-2}-g_k\bigr)+\mu o(1).
\tag{13}
$$</div>

<p>We prove $g_k\to m_k$ by induction on $k$. The cases $k=0,1$ are exact, and $k=2$ is $V/F\to1$. Fix $k\ge3$ and suppose all smaller orders have been proved. Since $m_k=(k-1)m_{k-2}$, (13) gives, for $e_{k,n}=g_{k,n}-m_k$,</p>
<div class="math-display">$$
e_{k,n}(t)=
\exp\left(-\frac k2\int_0^t\mu_n(v)\,dv\right)e_{k,n}(0)+o(1)
\quad(0\le t\le t_n).
\tag{14}
$$</div>
<p>The error is uniform: the integrating factor for the forcing has modulus at most one, and its integral is bounded by $I_n$ times the uniform $o(1)$ in (13).</p>
<p>It remains to check the initial value at the next level; it cannot be imposed independently of the children. By <a href="/tag/54V4/">54V4</a>, the centered initial squared mass is a sum of $Q=L^d$ independent copies of the preceding terminal centered mass. Moreover $\mu_{n+1}(0)=Q\mu_n(t_n)$ and $\nu_{n+1}(0)=Q\nu_n(t_n)$, so $F_{n+1}(0)=QF_n(t_n)$ exactly. The multinomial formula gives</p>
<div class="math-display">$$
g_{k,n+1}(0)=Q^{-k/2}
\sum_{a_1+\cdots+a_Q=k}\frac{k!}{a_1!\cdots a_Q!}
\prod_{\ell=1}^Q g_{a_\ell,n}(t_n).
\tag{15}
$$</div>
<p>The $Q$ terms with one $a_\ell=k$ contribute $c_k g_{k,n}(t_n)$, where $c_k=Q^{1-k/2}&lt;1$. Every other nonzero term uses orders at most $k-2$, since $g_1=0$. By the induction hypothesis their sum tends to $(1-c_k)m_k$. To evaluate that constant, put the standard Gaussian moments into (15): the normalized sum of $Q$ independent standard normal variables is again standard normal. Thus</p>
<div class="math-display">$$
e_{k,n+1}(0)=c_k e_{k,n}(t_n)+o(1).
$$</div>
<p>Combining this with (14) yields</p>
<div class="math-display">$$
|e_{k,n+1}(0)|\le\rho_n|e_{k,n}(0)|+o(1),
\qquad
\rho_n=c_k e^{-kI_n/2}\longrightarrow
Q^{1-k/2}L^{-k\alpha/2}&lt;1.
$$</div>
<p>Choose a fixed $\rho&lt;1$ bounding the late $\rho_n$. Iteration sends the initial error and every fixed finite set of forcing errors to zero geometrically; the later errors contribute at most their supremum divided by $1-\rho$. Hence $e_{k,n}(0)\to0$, and (14) gives convergence uniformly in time. This completes the moment induction.</p>

<p>For completeness, these moments determine the distributional limit. Along any sequence of times, $Z/\sqrt F$ is tight by its bounded second moment. V7MP supplies uniform integrability of every fixed power, so each subsequential weak limit $Y$ has moments $m_k$. Taylor's formula for $e^{iuY}$ has expected remainder, at order $2m-1$, bounded by</p>
<div class="math-display">$$
\frac{|u|^{2m}\mathbb E Y^{2m}}{(2m)!}
=\frac{|u|^{2m}}{2^m m!}\longrightarrow0.
$$</div>
<p>Its characteristic function is therefore the Gaussian one, and $Y$ is standard normal. Every subsequential limit is the same, proving convergence along the original sequence. Since $V/F\to1$ uniformly, the same conclusion holds for $H_n$, and its integer moments have the stated uniform limits. Uniform integrability from V7MP gives convergence of each fixed absolute moment as well. Failure of either a uniform absolute-moment limit or the bounded-continuous-test assertion would select a sequence of times contradicting these conclusions. $\square$</p>

<p>This supplies the $p=2$ case of the Gaussian conclusion discussed in <a href="https://arxiv.org/html/2211.05686v1">Remark 6.14 of the cited preprint</a>, with the corrected standard-normal moments. The written proof uses the earlier exact-model estimates and the centered coalescent dynamics; it leaves the independent-discovery variance gap of <a href="/tag/Q7QG/">Q7QG</a> intact. It does not establish the conjecture for general $p$, a joint or process limit, convergence of exponential moments, or an extension to comparable kernels. It is not a new source erratum; attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>. The journal comparison, independent mathematical review and Lean formalisation remain pending.</p>


## Joint Gaussian fluctuations of integer power sums {#section-joint-power-gaussian-limit}

<p>The same centered generator also identifies the higher power sums. Their linearized drift is triangular: the fluctuation of $S_p$ is coupled only to those of $S_2,\ldots,S_p$. This permits a joint moment argument and gives an explicit covariance.</p>

<a id="tag-MFGT" data-assertion="theorem" data-title="Critical hierarchical integer power sums have joint Gaussian fluctuations with explicit covariance"></a>
<p>Consider the critical exact hierarchical model of <a href="/tag/VI3Y/">VI3Y</a>, with $0&lt;\alpha&lt;d$ and $d\ge3\alpha$. Put $f_{p,n}(t)=\mathbb ES_p(n,t)$, $\mu_n=f_{2,n}$, $\nu_n=f_{3,n}$ and</p>
<div class="math-display">$$
\theta_n=\frac{\nu_n}{\mu_n},\qquad
b_{p,n}=\sqrt{\mu_n}\,\theta_n^{p-1},\qquad
Y_{p,n}=\frac{S_p-f_{p,n}}{b_{p,n}},\qquad
a_p=(2p-5)!!\quad(p\ge2).
$$</div>
<p>For every fixed integer $P\ge2$, the vector $Y_n=(Y_{2,n},\ldots,Y_{P,n})$ converges to a centered Gaussian vector $N$ with positive definite covariance matrix</p>
<div class="math-display">$$
\Sigma_{pq}=a_{p+q}-a_{p+1}a_{q+1}
=(2p+2q-5)!!-(2p-3)!!(2q-3)!!,
\qquad 2\le p,q\le P.
\tag{16}
$$</div>
<p>Convergence holds along every deterministic choice of times $s_n\in[0,t_n]$, uniformly in time against each bounded continuous test function, and uniformly in every fixed mixed moment. Each fixed real linear combination also converges in every fixed absolute moment. In particular, uniformly over the level's time interval,</p>
<div class="math-display">$$
\operatorname{Cov}(S_p,S_q)\sim\Sigma_{pq}b_{p,n}b_{q,n},
\qquad
\frac{\operatorname{Var}(S_p)}{f_{2p,n}}
\longrightarrow1-\frac{a_{p+1}^2}{a_{2p}}.
\tag{17}
$$</div>
<p>Thus each fixed integer power sum, centered and divided by its actual standard deviation, tends to a standard normal variable in distribution and in all fixed integer and absolute moments. For $p,q=2,3,4$, the covariance in (16) is</p>
<div class="math-display">$$
\Sigma=\begin{pmatrix}2&amp;12&amp;90\\12&amp;96&amp;900\\90&amp;900&amp;10170\end{pmatrix}.
$$</div>

<p><em>Proof.</em> Throughout, indices and moment orders are fixed, and every asymptotic estimate is uniform over $0\le t\le t_n$. Suppress $n,t$ from the notation. Hydrodynamics holds by <a href="/tag/6WO3/">6WO3</a> and <a href="/tag/UL8V/">UL8V</a>. Set $Z_p=S_p-f_p$ and $\eta=\theta^2/\mu$. The results <a href="/tag/ANYT/">ANYT</a>, <a href="/tag/KPCV/">KPCV</a> and <a href="/tag/V7MP/">V7MP</a> give</p>
<div class="math-display">$$
f_p\sim a_p\mu\theta^{p-2},\qquad
\eta\longrightarrow0,\qquad
\|S_p/f_p-1\|_r\longrightarrow0,\qquad
\|Z_p\|_r=O(b_p)\quad(r\ge1).
\tag{18}
$$</div>
<p>The last estimate follows from $f_{2p}\sim a_{2p}b_p^2$; it also supplies uniform integrability of every fixed power of $Y_p$. The exact mean equations give $\mu'/\mu=(1+o(1))\mu$ and $\nu'/\nu=(3+o(1))\mu$. Consequently</p>
<div class="math-display">$$
\frac{b_p'}{b_p}=(2p-\tfrac32+o(1))\mu,
\qquad I_n:=\int_0^{t_n}\mu_n(t)\,dt\longrightarrow I_*:=\alpha\log L&gt;0,
\tag{19}
$$</div>
<p>where the integral limit is <a href="/tag/W2VN/">W2VN</a>. The derivative is taken in the exact expression $b_p=\nu^{p-1}\mu^{3/2-p}$, not in an asymptotic equivalent.</p>

<p>The finite coalescent generator of <a href="/tag/Z960/">Z960</a> and <a href="/tag/22H8/">22H8</a> gives the drift</p>
<div class="math-display">$$
G_p(S)=\frac12\sum_{k=1}^{p-1}\binom pk S_{k+1}S_{p-k+1}
-(2^{p-1}-1)S_{p+2}.
$$</div>
<p>Expanding about the means and subtracting $f_p'=\mathbb EG_p$ yields</p>
<div class="math-display">$$
\begin{aligned}
G_p-\mathbb EG_p
={}&\sum_{r=2}^p\binom p{r-1}f_{p-r+2}Z_r+R_p,\\
R_p={}&\frac12\sum_{k=1}^{p-1}\binom pk
\bigl(Z_{k+1}Z_{p-k+1}-\mathbb E[Z_{k+1}Z_{p-k+1}]\bigr)
-(2^{p-1}-1)Z_{p+2}.
\end{aligned}
$$</div>
<p>By Hölder's inequality and (18), $\|R_p/(\mu b_p)\|_r=O(\sqrt\eta+\eta)=o(1)$. Indeed, a quadratic term has scale $b_{k+1}b_{p-k+1}/(\mu b_p)=\sqrt\eta$, and the last term has scale $b_{p+2}/(\mu b_p)=\eta$. Also $f_{p-r+2}b_r/(\mu b_p)\to a_{p-r+2}$. Including the derivative of $b_p$ in (19), the normalized drift is therefore $\mu AY+\mu o_{L^r}(1)$, where</p>
<div class="math-display">$$
A_{pr}=\begin{cases}
\tfrac32-p,&amp;r=p,\\
\binom p{r-1}a_{p-r+2},&amp;2\le r&lt;p,\\
0,&amp;r&gt;p.
\end{cases}
\tag{20}
$$</div>

<p>We also need the simultaneous jump moments. For indices $p_1,\ldots,p_j$, let $J_{p_1\cdots p_j}$ be the sum, over unordered pairs of distinct clusters, of the merger rate times the product of their increments in these power sums. A merger of masses $a,b$ has rate $ab$ and increment $\Delta_p(a,b)=\sum_{k=1}^{p-1}\binom pk a^kb^{p-k}$. Thus, writing $R=\sum_i p_i$ and $K=\sum_i k_i$,</p>
<div class="math-display">$$
J_{p_1\cdots p_j}
=\frac12\sum_{k_1=1}^{p_1-1}\cdots\sum_{k_j=1}^{p_j-1}
\left(\prod_{i=1}^j\binom{p_i}{k_i}\right)
\bigl(S_{1+K}S_{1+R-K}-S_{2+R}\bigr).
\tag{21}
$$</div>
<p>The subtraction removes equal clusters. Each difference is nonnegative and bounded above by its first product. For $j=2$, (18) gives convergence in every fixed $L^r$:</p>
<div class="math-display">$$
\frac{J_{pq}}{\mu b_pb_q}\longrightarrow\Gamma_{pq}
:=\frac12\sum_{k=1}^{p-1}\sum_{\ell=1}^{q-1}
\binom pk\binom q\ell a_{k+\ell+1}a_{p+q-k-\ell+1}.
\tag{22}
$$</div>
<p>The diagonal term divided by $\mu b_pb_q$ is $O_{L^r}(\eta)$. For $j\ge3$, the products in (21) have $L^r$ size $O(\mu^2\theta^{R-2})$, whereas $\mu\prod_i b_{p_i}=\mu^{1+j/2}\theta^{R-j}$. Hence</p>
<div class="math-display">$$
\left\|\frac{J_{p_1\cdots p_j}}{\mu\prod_i b_{p_i}}\right\|_r
=O(\eta^{j/2-1})=o(1).
$$</div>
<p>The exact Taylor expansion of any fixed polynomial $h$ under a merger terminates. Equations (18)–(22), with Hölder's inequality for the remaining polynomial factors, consequently give</p>
<div class="math-display">$$
\frac{d}{dt}\mathbb Eh(Y)
=\mu\mathbb E\mathcal Lh(Y)+\mu o(1),
\qquad
\mathcal Lh(y)=(Ay)\cdot\nabla h(y)
+\frac12\sum_{p,q=2}^P\Gamma_{pq}\partial_p\partial_q h(y).
\tag{23}
$$</div>
<p>Both the changing mean and the changing scale are included here. No independence between the power sums is used.</p>

<p>We verify the covariance in (16) before using (23). Let $T$ be the square of a standard normal variable. Then $\Sigma_{pq}=\operatorname{Cov}(T^{p-1},T^{q-1})$, so $\Sigma$ is positive definite: a polynomial with no constant term cannot be almost surely constant on a variable with positive density on $(0,\infty)$ unless all its coefficients vanish. This representation is only an identity for the covariance matrix; the proposed limit $N$ is jointly Gaussian.</p>
<p>The identity $A\Sigma+\Sigma A^{\mathsf T}+\Gamma=0$ can be checked at all indices by formal power series. Put</p>
<div class="math-display">$$
\begin{aligned}
B(z)&amp;=1-\sqrt{1-2z}=\sum_{m\ge1}a_{m+1}\frac{z^m}{m!},
&amp;C(z)&amp;=\int_0^zB(u)\,du=\sum_{m\ge2}a_m\frac{z^m}{m!},\\
K(x,y)&amp;=C(x+y)-C(x)-C(y)-B(x)B(y),
&amp;H(x,y)&amp;=B(x+y)-B(x)-B(y).
\end{aligned}
$$</div>
<p>The coefficient of $x^py^q/(p!q!)$ in $K$ is $\Sigma_{pq}$, and in $H^2/2$ it is $\Gamma_{pq}$. The operator corresponding to left multiplication by $A$ is $(B(x)-2x)\partial_x+3/2$. Thus the desired identity is</p>
<div class="math-display">$$
\bigl((B(x)-2x)\partial_x+(B(y)-2y)\partial_y+3\bigr)K
+\tfrac12H^2=0.
\tag{24}
$$</div>
<p>For an explicit verification, set $u=B(x)$, $v=B(y)$ and $w=B(x+y)$. Use $B^2=2B-2z$, $B'=1/(1-B)$ and $C=B^2/2-B^3/3$. The left side of (24) becomes $w(u^2-2u+v^2-2v+2w-w^2)=0$. Comparing coefficients proves the matrix identity. Gaussian integration by parts now gives $\mathbb E\mathcal Lh(N)=0$ for every polynomial $h$.</p>

<p>We prove convergence of mixed moments by induction on their total degree. Degrees zero and one are exact. Fix $k\ge2$ and suppose all smaller degrees converge uniformly. Let $e_{k,n}(t)$ be the vector of differences between the degree-$k$ moments of $Y_n(t)$ and those of $N$. On homogeneous polynomials of degree $k$, the drift operator $(Ay)\cdot\nabla$ has a fixed matrix $D_k$. Order monomials by $\sum_p p m_p$, where $m_p$ is the exponent of $y_p$. The matrix is triangular, with diagonal entries</p>
<div class="math-display">$$
\sum_{p=2}^P m_p(\tfrac32-p)\le-\frac k2.
$$</div>
<p>The second-order part of $\mathcal L$ lowers degree by two. Subtract its Gaussian identity from (23) and use the induction hypothesis to obtain</p>
<div class="math-display">$$
e_{k,n}'=\mu_nD_ke_{k,n}+\mu_n o(1),\qquad
e_{k,n}(t)=e^{D_k\int_0^t\mu_n(v)\,dv}e_{k,n}(0)+o(1).
\tag{25}
$$</div>
<p>The second error is uniform because $I_n$ is bounded and the matrix exponential is bounded on bounded nonnegative intervals.</p>
<p>For the initial value at the next level, use the exact independent-child identity <a href="/tag/54V4/">54V4</a>. With $Q=L^d$, both $\mu$ and $\nu$ are multiplied by $Q$ at gluing, so $\theta$ is unchanged and every $b_p$ is multiplied by $\sqrt Q$. The whole vector $Y_{n+1}(0)$ therefore has the law of $Q^{-1/2}$ times the sum of $Q$ independent copies of $Y_n(t_n)$. In the expansion of a degree-$k$ mixed moment, terms placing all factors in one child contribute $c_k$ times that moment, where $c_k=Q^{1-k/2}\le1$. Every other nonzero term contains only child moments of degrees at most $k-2$, since a child receiving exactly one factor has mean zero. The same expansion leaves the Gaussian vector's moments unchanged. By induction,</p>
<div class="math-display">$$
e_{k,n+1}(0)=c_ke_{k,n}(t_n)+o(1)
=c_ke^{D_k I_n}e_{k,n}(0)+o(1).
\tag{26}
$$</div>
<p>A matrix need not contract in a given norm just because its eigenvalues have negative real parts, so we use products of the matrices in (26). The triangular form of $D_k$ gives $\|e^{D_ks}\|\le C_ke^{-ks/4}$ for $s\ge0$: the polynomial factors from its finite Jordan blocks are absorbed by the weaker exponential. For late $n$, $I_n\ge I_*/2$. The matrices commute, and hence a product over $n-m$ consecutive late levels has norm at most</p>
<div class="math-display">$$
\left\|c_k^{n-m}e^{D_k\sum_{j=m}^{n-1}I_j}\right\|
\le C_ke^{-kI_*(n-m)/8}.
$$</div>
<p>Iteration of (26) now sends the initial error and any fixed finite set of forcing errors to zero. The remaining errors are bounded by their supremum times a convergent geometric series. Thus $e_{k,n}(0)\to0$, and (25) gives uniform convergence throughout the level. This proves every fixed mixed moment, including the covariances in (17). The variance ratio there follows from $f_{2p}\sim a_{2p}b_p^2$.</p>

<p>Finally, along any sequence of times the vectors are tight by their bounded second moments. Equation (18) and Hölder's inequality give uniform integrability of every mixed monomial, so every subsequential weak limit has the Gaussian mixed moments. For a real vector $c$, its linear combination has even moments $(2m-1)!!(c^{\mathsf T}\Sigma c)^m$. The expected remainder in the characteristic-function Taylor expansion of order $2m-1$ is bounded by</p>
<div class="math-display">$$
\frac{|u|^{2m}(2m-1)!!(c^{\mathsf T}\Sigma c)^m}{(2m)!}
=\frac{(u^2c^{\mathsf T}\Sigma c/2)^m}{m!}\longrightarrow0.
$$</div>
<p>Every linear combination is therefore normal with the prescribed variance, identifying the joint limit as $N$. Higher moment bounds imply convergence of each fixed absolute moment. Choosing a sequence of times witnessing a putative failure proves the uniform versions. Positive definiteness of $\Sigma$ and (17) justify division by each actual standard deviation and give the final assertion. $\square$</p>

<p>This extends the preceding squared-mass result to every fixed finite collection of integer powers $p\ge2$, as discussed in <a href="https://arxiv.org/html/2211.05686v1">Remark 6.14 of the cited preprint</a>. It retains the $2/3$ squared-mass variance ratio and quantifies the independent-discovery variance deficit for every such power. The result concerns power sums at a common time; it does not give a joint limit at several times, a process limit, noninteger powers, growing indices, exponential-moment convergence or comparable kernels. Attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>; Lean formalisation is pending. No new source erratum or journal-version audit is claimed.</p>


## Gaussian fluctuations at several times {#section-multitime-power-gaussian-limit}

<p>The clock for the limiting fluctuations is the integrated mean squared mass. In this clock the limiting law is stationary, although the unnormalized power sums grow throughout a level. The same generator estimates identify the dependence between finitely many times.</p>

<a id="tag-OQV3" data-assertion="theorem" data-title="Hierarchical power-sum fluctuations at finitely many times converge to a time-changed stationary Gaussian Markov law"></a>
<p>Under the hypotheses of <a href="/tag/MFGT/">MFGT</a>, fix integers $P\ge2$ and $k\ge1$. Use the coalescent coupling within each level, and retain its vector $Y_n=(Y_{2,n},\ldots,Y_{P,n})$, drift matrix $A$ and covariance matrix $\Sigma$. Put</p>
<div class="math-display">$$
q=L^{-\alpha},\qquad \phi(u)=1-(1-q)u,\qquad
\tau(u)=-\log\phi(u),\qquad 0\le u\le1.
$$</div>
<p>Let $U$ be the centered stationary Gaussian Markov law with marginal covariance $\Sigma$ and, for $s\le t$,</p>
<div class="math-display">$$
\mathbb E[U(s)U(t)^{\mathsf T}]
=\Sigma e^{A^{\mathsf T}(t-s)}.
\tag{27}
$$</div>
<p>For every deterministic choice $0\le u_{1,n}\le\cdots\le u_{k,n}\le1$ converging to $(u_1,\ldots,u_k)$,</p>
<div class="math-display">$$
\bigl(Y_n(u_{1,n}t_n),\ldots,Y_n(u_{k,n}t_n)\bigr)
\ \Longrightarrow\
\bigl(U(\tau(u_1)),\ldots,U(\tau(u_k))\bigr).
\tag{28}
$$</div>
<p>For every fixed polynomial, convergence of its expectation is uniform over the ordered time tuples, with the limiting expectation evaluated at those same tuples. The same uniform assertion holds for bounded continuous tests and for each fixed absolute moment of each fixed real linear combination. Repeated times are allowed. In particular, writing $H_n(t)=(S_2(n,t)-\mu_n(t))/\sqrt{\operatorname{Var}(S_2(n,t))}$, uniformly over $0\le u\le v\le1$ one has</p>
<div class="math-display">$$
\mathbb E[H_n(ut_n)H_n(vt_n)]
\longrightarrow \sqrt{\frac{\phi(v)}{\phi(u)}}.
\tag{29}
$$</div>
<p>The variance in this normalization is positive for all sufficiently large $n$, uniformly in time, by MFGT.</p>

<p><em>Proof.</em> Let $\Gamma$ be the limiting jump covariance in (22). It is positive semidefinite: for every real vector $c$, the corresponding quadratic form in the normalized jump covariance is a sum of merger rates times squares, and its expectation tends to $c^{\mathsf T}\Gamma c$. The identity proved in (24) implies, for $h\ge0$,</p>
<div class="math-display">$$
Q(h):=\int_0^h e^{Ar}\Gamma e^{A^{\mathsf T}r}\,dr
=\Sigma-e^{Ah}\Sigma e^{A^{\mathsf T}h}\succeq0.
$$</div>
<p>Thus the Gaussian transition from $y$ after a time $h$ is $e^{Ah}y+\xi_h$, where $\xi_h$ is independent and centered with covariance $Q(h)$. The identity $Q(h+\ell)=Q(\ell)+e^{A\ell}Q(h)e^{A^{\mathsf T}\ell}$ proves consistency of these transitions, and the displayed expression in terms of $\Sigma$ proves stationarity and (27). This constructs every finite-dimensional law needed below, including coincident times.</p>

<p>Write $P_h f(y)=\mathbb E f(e^{Ah}y+\xi_h)$ for the transition operator. On polynomials of degree at most $m$, it is a finite-dimensional linear operator whose coefficients are continuously differentiable in $h$ and bounded on bounded intervals. Gaussian moments and $Q'(0)=\Gamma$ give its generator</p>
<div class="math-display">$$
\mathcal Lf(y)=(Ay)\cdot\nabla f(y)
+\frac12\sum_{p,r=2}^P\Gamma_{pr}\partial_p\partial_r f(y),
\qquad \frac{d}{dh}P_hf=\mathcal LP_hf.
$$</div>
<p>For completeness, the derivative at zero follows by expanding the polynomial at $y$: the first increment has mean $hAy+O(h^2)$, its second moment is $h\Gamma+O(h^2)$, and every higher term is $o(h)$, by the Gaussian moment formula. Applying the transition identity $P_{h+\ell}=P_hP_\ell$ gives the derivative at every $h$.</p>

<p>We require the generator approximation before taking expectation, so that it can be multiplied by observations of the past. Denote by $\mathscr G_{n,t}$ the finite coalescent generator acting on $f(Y_n(t))$, including the deterministic derivatives of its mean and scale. The bounds (18)–(22) give, for each fixed polynomial $f$ and each finite $r\ge1$,</p>
<div class="math-display">$$
\sup_{0\le t\le t_n}
\left\|\frac{\mathscr G_{n,t}f}{\mu_n(t)}
-\mathcal Lf(Y_n(t))\right\|_r\longrightarrow0.
\tag{30}
$$</div>
<p>Indeed, the normalized drift error tends to zero in every fixed $L^r$, the normalized second jump moments tend to $\Gamma$, and each normalized jump moment of order at least three is $o_{L^r}(1)$. The polynomial Taylor expansion terminates. Its remaining factors are polynomials in $Y_n$, whose moments of every fixed order are bounded by (18). Hölder's inequality therefore bounds every error term in $L^r$. The conclusion also holds uniformly for polynomials in a fixed degree space with bounded coefficients. No conditional version of a hydrodynamic estimate is being assumed.</p>

<p>Set $T_n(t)=\int_0^t\mu_n(v)\,dv$. The mean profile <a href="/tag/W2VN/">W2VN</a> gives</p>
<div class="math-display">$$
\sup_{0\le u\le1}|T_n(ut_n)-\tau(u)|\longrightarrow0,
\qquad T_n(t_n)\longrightarrow\log(1/q).
\tag{31}
$$</div>
<p>In fact $t_n\mu_n(ut_n)\to(1-q)/\phi(u)$ uniformly, and integration yields (31). In particular, all clock intervals under consideration have a common finite bound.</p>

<p>Fix deterministic $s\le t$ in one level and a polynomial $f$. For $s\le v\le t$ put $g_v=P_{T_n(t)-T_n(v)}f$. Its explicit time derivative is $-\mu_n(v)\mathcal Lg_v$. The Markov property and the finite-state generator formula, applied after time $s$, consequently imply</p>
<div class="math-display">$$
\mathbb E\bigl[F f(Y_n(t))\bigr]
=\mathbb E\bigl[F(P_{T_n(t)-T_n(s)}f)(Y_n(s))\bigr]+o(1)
\tag{32}
$$</div>
<p>whenever $F$ is a fixed product of polynomial observations at deterministic times at or before $s$. To see that the error is uniform, the integral left after the two $\mathcal Lg_v$ terms cancel is bounded by</p>
<div class="math-display">$$
T_n(t_n)\,\|F\|_2
\sup_{s\le v\le t}
\left\|\frac{\mathscr G_{n,v}g_v}{\mu_n(v)}
-\mathcal Lg_v(Y_n(v))\right\|_2=o(1).
$$</div>
<p>The norm of $F$ is bounded uniformly over its observation times by Hölder and (18); the coefficients of $g_v$ are uniformly bounded by the finite clock bound. For each fixed $n$ the underlying chain is finite and all these variables are bounded, so the conditional generator formula has no stopping or integrability qualification. This proves (32) using unconditional estimates only.</p>

<p>Apply (32) to a product $\prod_{j=1}^k f_j(Y_n(t_j))$, beginning with the last factor. Replace it by its Gaussian transition polynomial at $t_{k-1}$ and multiply by $f_{k-1}$. Repeat until only a polynomial of $Y_n(t_1)$ remains. Degrees stay bounded in terms of the original factors, and all coefficients remain in a bounded set. MFGT gives its expectation under $N(0,\Sigma)$ with a uniform $o(1)$ error. The exact Gaussian transition rule performs precisely the same reductions for $U$. Finally (31) and continuity of the polynomial transition coefficients replace the clock differences by $\tau(u_j)-\tau(u_{j-1})$. Products of monomials span all polynomials on the $k$ observations, proving the uniform mixed-moment assertion.</p>

<p>Along any convergent sequence of time tuples, bounded second moments give tightness of the observed vectors. Hölder and (18) give uniform integrability of every fixed monomial, so each subsequential limit has the moments of the Gaussian vector specified by (27). Every linear combination has Gaussian moments. The characteristic-function Taylor bound used at the end of MFGT identifies its normal law, also when the variance is zero; hence it identifies the joint law. This proves (28). Higher even-moment bounds give convergence of the stated absolute moments. If uniform convergence for a bounded continuous test or an absolute moment failed, compactness of the ordered time simplex would select a convergent sequence contradicting these conclusions and continuity of the limiting Gaussian laws.</p>

<p>The first coordinate has $A_{22}=-1/2$ and no lower coordinate, while $\Sigma_{22}=2$. Its covariance is therefore $2e^{-(t-s)/2}$. Division by the actual variance, using the uniform equivalent in MFGT, and substitution of $\tau(v)-\tau(u)=\log(\phi(u)/\phi(v))$ give (29). $\square$</p>

<p>This is a finite-dimensional limit for the coupled dynamics within a level, including the critical dimension $d=3\alpha$. It strengthens the common-time conclusion of MFGT. It does not prove tightness in a path space, convergence across several nested levels, noninteger or growing power indices, exponential-moment convergence, or an extension to comparable kernels. Attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>. Independent mathematical review, the journal-version comparison and Lean formalisation remain pending. All source errata and their repair assessments are unchanged.</p>


## A functional Gaussian limit within a level {#section-functional-power-gaussian-limit}

<p>The fourth jump moment controls the fluctuations missed by a finite set of observations. It gives a maximal increment bound on each short interval; summing that bound over a deterministic grid supplies the required path approximation.</p>

<a id="tag-Q4PO" data-assertion="theorem" data-title="Critical hierarchical integer power sums have a functional Gaussian limit within a coalescent layer"></a>
<p>Under the hypotheses of <a href="/tag/MFGT/">MFGT</a>, fix an integer $P\ge2$ and use the coalescent coupling within each level. Set $X_n(u)=Y_n(ut_n)$ for $0\le u\le1$. With $A,\Sigma,\Gamma,\tau$ as in <a href="/tag/OQV3/">OQV3</a>, let</p>
<div class="math-display">$$
U(s)=e^{As}N+\int_0^s e^{A(s-v)}\Gamma^{1/2}\,dB(v),
\qquad X(u)=U(\tau(u)),
\tag{33}
$$</div>
<p>where $N$ has law $N(0,\Sigma)$ and is independent of a standard $(P-1)$-dimensional Brownian motion $B$. Then</p>
<div class="math-display">$$
X_n\Longrightarrow X
\quad\text{in }D([0,1],\mathbb R^{P-1})\text{ with the }J_1\text{ topology}.
\tag{34}
$$</div>
<p>The limit has continuous paths. For any deterministic integers $m_n\to\infty$, the linear interpolations of $X_n$ on the grid $\{j/m_n:0\le j\le m_n\}$ converge to $X$ in $C([0,1],\mathbb R^{P-1})$ with the uniform norm. Moreover, for $0&lt;r&lt;4$,</p>
<div class="math-display">$$
\mathbb E\|X_n\|_\infty^r\longrightarrow\mathbb E\|X\|_\infty^r,
\qquad \|x\|_\infty=\sup_{0\le u\le1}\|x(u)\|.
\tag{35}
$$</div>
<p>All norms on vectors below are Euclidean. The assertion includes $d=3\alpha$.</p>

<p><em>Proof.</em> The positive semidefiniteness of $\Gamma$ and the Lyapunov identity were proved in OQV3. Formula (33) consequently has exactly its stationary Gaussian transition laws. Its paths are continuous: integration by parts rewrites the stochastic convolution as</p>
<div class="math-display">$$
\Gamma^{1/2}B(s)+\int_0^s Ae^{A(s-v)}\Gamma^{1/2}B(v)\,dv.
$$</div>
<p>The clock $\tau$ is continuous on $[0,1]$, since $\phi(1)=L^{-\alpha}&gt;0$.</p>

<p>Put $\eta_n(t)=\nu_n(t)^2/\mu_n(t)^3$ and $\varepsilon_n=\sup_{0\le t\le t_n}\eta_n(t)\to0$. Constants in the rest of the proof may depend on $P$ and the fixed model parameters, but not on $n$ or the observation interval; all bounds are for sufficiently large $n$. The finite-state generator gives the semimartingale decomposition, in the rescaled time $u$,</p>
<div class="math-display">$$
X_n(u)=X_n(0)+\int_0^u D_n(v)\,dv+M_n(u),
\qquad M_n(0)=0.
\tag{36}
$$</div>
<p>Here $D_n$ is the predictable drift, including the derivatives of the centering and normalization, and $M_n$ is the compensated merger martingale. For a coordinate $p$, write $j_{p,\ell,n}(u)$ for the predictable rate of the $\ell$th power of its jump, $\ell=2,3,4$. In the notation of (21),</p>
<div class="math-display">$$
j_{p,\ell,n}(u)
=\frac{t_n J_{\overbrace{p\cdots p}^{\ell}}(n,ut_n-)}{b_{p,n}(ut_n)^\ell}.
$$</div>
<p>The rates are evaluated just before a merger, with the initial state used at time zero; the deterministic functions in the denominator are continuous. A merger has probability zero at any fixed positive time, so deterministic-time bounds also apply to these predictable versions. The mean profile bounds $t_n\mu_n(ut_n)$ uniformly. Equations (18)–(22) therefore imply</p>
<div class="math-display">$$
\sup_u\mathbb E\|D_n(u)\|^4\le C,
\qquad \sup_u\mathbb E j_{p,2,n}(u)^2\le C,
\qquad \sup_u\mathbb E j_{p,4,n}(u)\le C\varepsilon_n,
\qquad \mathbb E\|X_n(0)\|^4\le C.
\tag{37}
$$</div>
<p>For the first bound, the drift is $t_n\mu_n(AX_n+o_{L^4}(1))$. For the second, use (22) in $L^2$. For the third, the fourfold jump estimate following (22) is $O_{L^1}(\eta_n)$ after division by $\mu_n b_{p,n}^4$. These are bounds at deterministic times under the original law; no estimate after conditioning on an atypical state is required.</p>

<p>We give the maximal inequality used here directly. Fix one coordinate, a deterministic interval $[a,b]\subseteq[0,1]$, and write $Z(v)=M_{p,n}(v)-M_{p,n}(a)$ on that interval. Let $K=\int_a^b j_{p,2,n}(v)\,dv$ and $R=\int_a^b j_{p,4,n}(v)\,dv$. Cauchy–Schwarz in the finite sum over possible mergers gives $|j_{p,3,n}|\le\sqrt{j_{p,2,n}j_{p,4,n}}$. The compensated fourth-power identity hence yields</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E Z(b)^4
&=\mathbb E\int_a^b
\bigl(6Z(v-)^2j_{p,2,n}(v)+4Z(v-)j_{p,3,n}(v)+j_{p,4,n}(v)\bigr)\,dv\\
&\le8\mathbb E\left[\sup_{a\le v\le b}|Z(v)|^2K\right]+3\mathbb ER.
\end{aligned}
$$</div>
<p>Indeed $4|Z|\sqrt{j_2j_4}\le2Z^2j_2+2j_4$. All moments are finite for a fixed $n$, because the chain and time interval are finite. Doob's $L^4$ inequality, with $d_4=(4/3)^4$, and Cauchy–Schwarz give, on writing $V=\mathbb E\sup_{[a,b]}|Z|^4$,</p>
<div class="math-display">$$
V\le8d_4\sqrt{V\mathbb EK^2}+3d_4\mathbb ER
\le\frac V2+32d_4^2\mathbb EK^2+3d_4\mathbb ER.
$$</div>
<p>Thus $V\le64d_4^2\mathbb EK^2+6d_4\mathbb ER$. If $h=b-a$, (37) bounds the two terms by $Ch^2$ and $C\varepsilon_n h$. The drift increment has fourth moment at most $h^3\int_a^b\mathbb E\|D_n(v)\|^4\,dv\le Ch^4$. Summing over the finitely many coordinates in (36) proves</p>
<div class="math-display">$$
\mathbb E\sup_{a\le v\le b}\|X_n(v)-X_n(a)\|^4
\le C(h^2+\varepsilon_n h).
\tag{38}
$$</div>
<p>Taking $[a,b]=[0,1]$ and using the last bound in (37) also gives $\sup_n\mathbb E\|X_n\|_\infty^4&lt;\infty$, after discarding finitely many initial levels. Separately, compensation and (37) show $\mathbb E\sum_{0&lt;u\le1}\|\Delta X_n(u)\|^4\le C\varepsilon_n$, so the largest merger jump tends to zero in probability.</p>

<p>Let $\Pi_m x$ be the linear interpolation of a path's values at $j/m$. On each grid interval the difference from this interpolation is at most twice the largest increment from the left endpoint. Markov's inequality, (38), and a union bound over the $m$ intervals give, for $\delta&gt;0$,</p>
<div class="math-display">$$
\mathbb P\bigl(\|X_n-\Pi_m X_n\|_\infty&gt;\delta\bigr)
\le C\delta^{-4}(m^{-1}+\varepsilon_n).
\tag{39}
$$</div>
<p>This estimate includes jumps at grid endpoints. It also gives the usual modulus bound: two points at distance at most $1/m$ lie in the same or adjacent intervals, so their difference is at most three times the largest increment from a grid endpoint.</p>

<p>For a fixed $m$, OQV3 implies $\Pi_mX_n\Longrightarrow\Pi_mX$ in the uniform norm: interpolation is a continuous map of the finite vector of grid values. The continuous paths of $X$ give $\|\Pi_mX-X\|_\infty\to0$ almost surely as $m\to\infty$. These facts and (39) imply (34). More explicitly, the $J_1$ distance is bounded above by the uniform distance, by choosing the identity change of time. For any bounded Lipschitz function on $D$ with its $J_1$ metric, insert $\Pi_mX_n$ and $\Pi_mX$ between its expectations. The middle difference tends to zero for fixed $m$; the two outer differences tend to zero by (39) and continuity of $X$, first letting $n\to\infty$, then $m\to\infty$. Bounded Lipschitz tests determine weak convergence on this space.</p>

<p>For a deterministic sequence $m_n\to\infty$, (39) gives $\|X_n-\Pi_{m_n}X_n\|_\infty\to0$ in probability. Thus the interpolations have the same $J_1$ limit. On continuous paths the $J_1$ topology agrees with uniform convergence, so this is the asserted convergence in $C$. Finally the supremum norm is $J_1$-continuous at continuous paths. Its fourth-moment bound makes every smaller positive power uniformly integrable, proving (35). $\square$</p>

<p>The finite-dimensional Gaussian law is now accompanied by path tightness for one coalescent layer. It is deduced from the existing exact-model estimates, including the critical dimension; attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>. Dependence across nested levels, noninteger or growing power indices, exponential-moment convergence, and comparable kernels remain separate. Independent mathematical review, the journal-version comparison and Lean formalisation remain pending. All earlier tagged statements and source errata are preserved.</p>


## Gaussian dependence across nested blocks {#section-nested-power-gaussian-limit}

<p>A parent starts from the terminal clusters of its children. The normalization in MFGT makes this gluing an exact normalized sum, while the parent's fresh clocks supply a new Gaussian increment in the limit. These two operations determine the joint law on every fixed finite tree of blocks.</p>

<a id="tag-F7Q2" data-assertion="theorem" data-title="Hierarchical power-sum paths on a fixed tree of nested blocks have a joint Gaussian limit"></a>
<p>Use the critical exact-model coupling of <a href="/tag/VI3Y/">VI3Y</a>, with $d\ge3\alpha$, and fix integers $P\ge2$ and $k\ge0$. Put $Q=L^d$. In a level-$(n+k)$ block, label its descendants down to level $n$ by words $v\in\mathcal T_k:=\bigcup_{j=0}^k\{1,\ldots,Q\}^j$, with the empty word denoting the root and $vi$ the $i$th child of $v$. The block at $v$ has level $\ell_n(v)=n+k-|v|$. Define</p>
<div class="math-display">$$
X_{v,n}(u)=\left(
\frac{S_p(B_{v,n},ut_{\ell_n(v)})-f_{p,\ell_n(v)}(ut_{\ell_n(v)})}
{b_{p,\ell_n(v)}(ut_{\ell_n(v)})}
\right)_{p=2}^P,
\qquad 0\le u\le1.
\tag{40}
$$</div>
<p>Here $S_p(B,t)$ is evaluated during that block's own layer, after all child layers have finished and before any ancestor layer is added. In particular these are the truncated block partitions, not the full configuration restricted to each block. The means and scales are those of MFGT.</p>

<p>Define a Gaussian family $\{X_v:v\in\mathcal T_k\}$ recursively. At the leaves take independent copies of the process $X$ in <a href="/tag/Q4PO/">Q4PO</a>. At every nonleaf take a standard $(P-1)$-dimensional Brownian motion $B_v$, with all these Brownian motions independent of one another and of the leaf processes, and set</p>
<div class="math-display">$$
X_v(u)=e^{A\tau(u)}Q^{-1/2}\sum_{i=1}^Q X_{vi}(1)
+\int_0^{\tau(u)}e^{A(\tau(u)-s)}\Gamma^{1/2}\,dB_v(s).
\tag{41}
$$</div>
<p>Then, in the finite product of $D([0,1],\mathbb R^{P-1})$ with its $J_1$ topology,</p>
<div class="math-display">$$
(X_{v,n})_{v\in\mathcal T_k}\Longrightarrow(X_v)_{v\in\mathcal T_k}.
\tag{42}
$$</div>
<p>All limiting paths are continuous, and every node has the marginal law in Q4PO. Linear interpolation at any deterministic uniform grids whose meshes tend to zero at every node gives convergence in the finite product of the uniform path spaces. Every fixed mixed moment of finitely many observations converges, uniformly over their times; so does every fixed absolute moment of a real linear combination of those observations. Moreover, for $0&lt;r&lt;4$,</p>
<div class="math-display">$$
\mathbb E\left[\max_{v\in\mathcal T_k}\|X_{v,n}\|_\infty^r\right]
\longrightarrow
\mathbb E\left[\max_{v\in\mathcal T_k}\|X_v\|_\infty^r\right].
$$</div>

<p>Processes in disjoint subtrees are independent. If $w$ is a descendant of $v$ at distance $h\ge1$, write $I_*=\tau(1)=\alpha\log L$. Their covariance is</p>
<div class="math-display">$$
\mathbb E[X_w(u)X_v(z)^{\mathsf T}]
=Q^{-h/2}\Sigma e^{A^{\mathsf T}(hI_*-\tau(u)+\tau(z))},
\qquad 0\le u,z\le1.
\tag{43}
$$</div>
<p>In particular, for squared mass centered and divided by its own actual standard deviation in each block, the correlation tends uniformly in $u,z$ to</p>
<div class="math-display">$$
L^{-(d+\alpha)h/2}\sqrt{\frac{\phi(z)}{\phi(u)}},
\qquad \phi(u)=1-(1-L^{-\alpha})u.
\tag{44}
$$</div>
<p>The depth $k$, the power cutoff $P$ and the number and orders of observations are fixed as $n\to\infty$.</p>

<p><em>Proof.</em> The complete-block layers in VI3Y use independent clocks at different blocks, even for copies of the same physical pair. At the start of a parent's layer, its power sums are the sums of those in the terminal child partitions. The exact mean identities of <a href="/tag/54V4/">54V4</a> give</p>
<div class="math-display">$$
f_{p,m+1}(0)=Qf_{p,m}(t_m),\qquad
\mu_{m+1}(0)=Q\mu_m(t_m),\qquad
\nu_{m+1}(0)=Q\nu_m(t_m).
$$</div>
<p>Since $b_p=\nu^{p-1}\mu^{3/2-p}$, the scale is multiplied by $\sqrt Q$. Thus gluing gives the pathwise identity</p>
<div class="math-display">$$
X_{v,n}(0)=Q^{-1/2}\sum_{i=1}^QX_{vi,n}(1).
\tag{45}
$$</div>
<p>Child subtrees are independent, but a parent is not independent of them. Identity (45) is where their dependence enters.</p>

<p>We first identify joint moments. Reveal blocks in an order in which every descendant precedes its ancestors. When a block $v$ is reached, all previously revealed layers lie in its strict descendants or in blocks disjoint from it. Their clocks are independent of the fresh clocks of $v$. Enlarge the initial sigma-field for $v$ to include those complete histories and all its lower-layer data. Conditional on this sigma-field, its initial labelled partition is fixed and its subsequent evolution still has the finite coalescent generator of <a href="/tag/Z960/">Z960</a>. This would not hold if ancestor clocks had already been revealed; the chosen order avoids that problem.</p>

<p>Let $m=\ell_n(v)$ and $T_m(u)=\int_0^{ut_m}\mu_m(s)\,ds$. The backward polynomial argument (30)–(32) of <a href="/tag/OQV3/">OQV3</a> therefore also gives</p>
<div class="math-display">$$
\mathbb E[F f(X_{v,n}(b))]
=\mathbb E\bigl[F(P_{T_m(b)-T_m(a)}f)(X_{v,n}(a))\bigr]+o(1),
\qquad 0\le a\le b\le1,
\tag{46}
$$</div>
<p>where $P_s$ is its Gaussian transition operator and $F$ is any fixed product of polynomial observations from earlier revealed blocks and from $v$ at times at most $a$. Indeed, $F$ is measurable at time $a$ in the enlarged filtration. Its $L^2$ norm is bounded by Hölder's inequality and the unconditional moment bounds in MFGT, even though it involves several levels. The error in (46) is bounded by this norm times the bounded clock length and the $L^2$ generator error in (30). The latter is evaluated under the unchanged marginal law of $v$. All bounds are uniform over the observation times and the finitely many offsets $m-n\in\{0,\ldots,k\}$. No conditional moment estimate is used.</p>

<p>Take a product of polynomial observations over all nodes. Starting with the last block in the reveal order, apply (46) backwards through its observation times, then down to time zero. This replaces all its observations by a polynomial in $X_{v,n}(0)$, multiplying the observations of earlier blocks. Substitute (45) and expand the polynomial. This only introduces terminal observations of its children, which are earlier blocks. Repeat in reverse reveal order until only leaf observations remain. At every step the degrees are bounded by the original total degree and the number of steps is fixed. Transition coefficients are uniformly bounded because the clock lengths are bounded. The accumulated error is therefore $o(1)$, uniformly over the times.</p>

<p>The leaf paths are independent copies of $X_n$, so OQV3 evaluates their remaining polynomial expectations. Also $T_m(u)\to\tau(u)$ uniformly for every offset $m-n$ under consideration. Replacing the clock intervals by their limits in the preceding reduction gives exactly the same polynomial reductions for (41): each parent has the Gaussian transitions $P_s$ conditional on the child histories, with the initial value (45). This proves convergence of every mixed moment to that of (41).</p>

<p>Recursion (41) defines a centered jointly Gaussian family with continuous paths. Different child subtrees are independent. Their terminal vectors each have covariance $\Sigma$, by induction from the leaves. Their normalized sum consequently has covariance $\Sigma$. The Lyapunov identity in OQV3 then gives the stationary marginal law at their parent. This proves the asserted marginal and independence properties. To pass from moments to finite-dimensional laws, use bounded second moments for tightness and higher marginal moments with Hölder for uniform integrability of every mixed monomial. Any subsequential limit has the moments just computed. Each of its real linear combinations has Gaussian moments, and the characteristic-function Taylor estimate in MFGT identifies its normal law, including zero variance. Thus the joint observation law is the one in (41). Higher moment bounds also give the stated absolute-moment limits. Compactness of the finite product of time simplexes proves their uniform versions, since the limiting Gaussian covariances are continuous in all observation times.</p>

<p>Each coordinate path family is tight by Q4PO, at level $n+j$ for a fixed $j$. A finite union bound on compact sets gives tightness of their joint laws in the product path space. Every subsequential limit has continuous coordinate paths, because each marginal does. Evaluation at a fixed time is continuous at such a limit. The joint finite-dimensional laws just identified therefore determine every subsequential path law: evaluations on a dense countable time set determine continuous paths. This proves (42).</p>

<p>The grid estimate (39), applied at each of the finitely many nodes, makes the maximum uniform interpolation error tend to zero in probability for the stated refining grids. The interpolated vectors thus have the same product $J_1$ limit. On continuous paths this topology agrees with the product uniform topology. Finally Q4PO bounds the fourth moment of the maximum supremum norm by the sum of the nodes' fourth-moment bounds. Uniform integrability of every smaller positive power proves the displayed supremum-moment limit.</p>

<p>For (43), first suppose $w$ is a child of $v$. In (41) the other children and the new Brownian term are independent of $X_w$. Its covariance with the selected child's terminal value is $\Sigma e^{A^{\mathsf T}(I_*-\tau(u))}$. Multiplying by the parent's transition matrix on the right gives (43) with $h=1$. Each further ancestor contributes $Q^{-1/2}$ and a full-layer transition $e^{A^{\mathsf T}I_*}$ before the last partial-layer transition. These are exponentials of the same matrix, so they combine to give (43) for every $h$. For the first coordinate $A_{22}=-1/2$ and $\Sigma_{22}=2$. The uniform actual-variance equivalent in MFGT cancels the factor two. Substituting $Q=L^d$, $I_*=\alpha\log L$ and $\tau=-\log\phi$ gives (44). $\square$</p>

<p>This determines dependence across any fixed number of nested levels in the exact layer coupling, including the critical dimension. It does not treat a depth or power cutoff growing with $n$, noninteger powers, comparable kernels, exponential moments, or clusters of the full law restricted to the blocks. Attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>. Independent mathematical review, the journal-version comparison and Lean formalisation remain pending. Earlier statements and source errata are unchanged.</p>


## Supremum moments of the Gaussian path limit {#section-gaussian-path-moments}

<p>The fourth-moment argument in Q4PO proves tightness. Higher jump estimates give the corresponding maximal bound at every fixed even order, removing the restriction on the moments of the path supremum.</p>

<a id="tag-NC7F" data-assertion="theorem" data-title="Hierarchical Gaussian path limits converge in every fixed supremum moment and for polynomially bounded continuous functionals"></a>
<p>Under the hypotheses and normalization of <a href="/tag/Q4PO/">Q4PO</a>, fix $P\ge2$ and put $\varepsilon_n=\sup_{0\le t\le t_n}\nu_n(t)^2/\mu_n(t)^3\to0$. For each integer $m\ge2$ there is a constant $C_m$, independent of $n,a,b,N$, such that for all sufficiently large $n$, all $0\le a\le b\le1$, and all integers $N\ge1$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E\sup_{a\le u\le b}\|X_n(u)-X_n(a)\|^{2m}
&\le C_m\bigl((b-a)^m+\varepsilon_n^{m-1}(b-a)\bigr),\\
\mathbb E\|X_n-\Pi_NX_n\|_\infty^{2m}
&\le C_m\bigl(N^{1-m}+\varepsilon_n^{m-1}\bigr),
\end{aligned}
\tag{47}
$$</div>
<p>where $\Pi_N$ is linear interpolation on the uniform grid with $N$ intervals. The constants may depend on $m,P$ and the model parameters. For every fixed real $r&gt;0$,</p>
<div class="math-display">$$
\sup_n\mathbb E\|X_n\|_\infty^r&lt;\infty,
\qquad
\mathbb E\|X_n\|_\infty^r\longrightarrow\mathbb E\|X\|_\infty^r&lt;\infty.
\tag{48}
$$</div>
<p>For any deterministic $N_n\to\infty$, the interpolation error tends to zero in every fixed positive moment:</p>
<div class="math-display">$$
\mathbb E\|X_n-\Pi_{N_n}X_n\|_\infty^r\longrightarrow0.
\tag{49}
$$</div>
<p>The same supremum-moment and interpolation conclusions hold jointly on each fixed finite tree in <a href="/tag/F7Q2/">F7Q2</a>, using the maximum over its nodes. The grid sizes may differ between nodes, provided each tends to infinity.</p>

<p>More generally, let $\mathcal X_n=(X_{v,n})_{v\in\mathcal T_k}$ and $\mathcal X=(X_v)_{v\in\mathcal T_k}$ be its path vectors, allowing $k=0$ for a single block. If a real Borel function $F$ on this finite product of $J_1$ spaces is continuous at every vector of continuous paths and satisfies</p>
<div class="math-display">$$
|F(x)|\le C\bigl(1+\|x\|_*^s\bigr),\qquad
\|x\|_*:=\max_{v\in\mathcal T_k}\|x_v\|_\infty,
\quad s&gt;0,
$$</div>
<p>then $\mathbb EF(\mathcal X_n)\to\mathbb EF(\mathcal X)$. For deterministic grid sizes $N_{v,n}\to\infty$ at every node $v$, the interpolated paths $(\Pi_{N_{v,n}}X_{v,n})_{v\in\mathcal T_k}$ also satisfy this conclusion, with the same limit $\mathcal X$, for every continuous function on the product uniform path space with the same growth bound. This includes positive powers of supremum norms and integrals of fixed polynomials of the paths.</p>

<p><em>Proof.</em> Use the decomposition $X_n=X_n(0)+\int D_n+M_n$ from (36). For a fixed coordinate $p$, let $j_{\ell,n}$ be the predictable rate of the $\ell$th power of its jump. All these jumps are nonnegative, since a merger increases $S_p$ and the deterministic normalization is continuous and positive. The estimates (18)–(22) in <a href="/tag/MFGT/">MFGT</a>, together with the bounded rescaled mean $t_n\mu_n(ut_n)$, give</p>
<div class="math-display">$$
\begin{aligned}
\sup_u\mathbb E\|D_n(u)\|^{2m}+\mathbb E\|X_n(0)\|^{2m}&\le C_m,\\
\sup_u\mathbb E j_{2,n}(u)^m&\le C_m,\\
\sup_u\mathbb E j_{2m,n}(u)&\le C_m\varepsilon_n^{m-1}.
\end{aligned}
\tag{50}
$$</div>
<p>These are unconditional deterministic-time estimates. The last uses the $2m$-fold jump bound $J_{p\cdots p}/(\mu_n b_{p,n}^{2m})=O_{L^1}(\eta_n^{m-1})$, where $\eta_n=\nu_n^2/\mu_n^3$. Predictable rates use the left-limit partition; as in Q4PO, there is no merger at a fixed positive time with positive probability.</p>

<p>We prove the maximal estimate needed for the martingale increment $Z(u)=M_{p,n}(u)-M_{p,n}(a)$ on $[a,b]$. Put</p>
<div class="math-display">$$
Z^*=\sup_{a\le u\le b}|Z(u)|,\qquad
K=\int_a^b j_{2,n}(u)\,du,\qquad
R=\int_a^b j_{2m,n}(u)\,du.
$$</div>
<p>For $2\le\ell\le2m$, interpolation in the finite sum of merger rates, then Hölder's inequality in time, gives</p>
<div class="math-display">$$
\int_a^b j_{\ell,n}(u)\,du\le K^{a_\ell}R^{b_\ell},
\qquad
a_\ell=\frac{2m-\ell}{2m-2},\quad
b_\ell=\frac{\ell-2}{2m-2}.
$$</div>
<p>At the two endpoints this is simply $K$ or $R$. For the intermediate orders, apply Hölder first to the measure assigning each possible merger its rate: its $\ell$th jump moment is bounded by the second and $2m$th moments with these exponents. They sum to one, which gives the same interpolation after integration.</p>

<p>The compensated polynomial identity and $Z(a)=0$ imply</p>
<div class="math-display">$$
\mathbb E|Z(b)|^{2m}
\le\sum_{\ell=2}^{2m}\binom{2m}{\ell}
\mathbb E\bigl[(Z^*)^{2m-\ell}K^{a_\ell}R^{b_\ell}\bigr].
$$</div>
<p>The first-order term has zero expectation because $Z$ is a martingale; the remaining terms are exactly its jump compensators, with absolute values giving the displayed upper bound. All variables are bounded for each fixed $n$, so this identity and Doob's $L^{2m}$ inequality need no localization. Write $V=\mathbb E(Z^*)^{2m}$ and $d_m=(2m/(2m-1))^{2m}$. For $\ell&lt;2m$, the three nonnegative weights</p>
<div class="math-display">$$
\frac{2m-\ell}{2m},\qquad \frac{a_\ell}{m},\qquad b_\ell
$$</div>
<p>sum to one, and the first is strictly below one. Weighted Young's inequality therefore gives, for every $\delta&gt;0$,</p>
<div class="math-display">$$
(Z^*)^{2m-\ell}K^{a_\ell}R^{b_\ell}
\le\delta(Z^*)^{2m}+C_{m,\ell,\delta}(K^m+R).
$$</div>
<p>The last term $\ell=2m$ is $R$ itself. Apply Doob's inequality to the preceding polynomial bound and choose $\delta$ so that $d_m\delta\sum_{\ell=2}^{2m-1}\binom{2m}{\ell}\le1/2$. Absorbing the resulting $V/2$ gives</p>
<div class="math-display">$$
\mathbb E(Z^*)^{2m}\le C_m(\mathbb EK^m+\mathbb ER).
\tag{51}
$$</div>
<p>If $h=b-a$, (50) and Hölder give $\mathbb EK^m\le C_mh^m$ and $\mathbb ER\le C_m\varepsilon_n^{m-1}h$. The drift supremum has $2m$th moment at most $h^{2m-1}\int_a^b\mathbb E\|D_n(u)\|^{2m}du\le C_mh^{2m}$. Since $h\le1$, this term is bounded by $C_mh^m$. Combine the finitely many coordinate bounds with the drift to prove the first inequality of (47). The zero-length interval is immediate.</p>

<p>On a grid interval the interpolation error is at most twice the maximum increment from its left endpoint. The $2m$th power of the maximum over intervals is bounded by the sum of their $2m$th powers. Summing the first bound in (47) over the $N$ intervals proves the second. Taking the whole interval and adding the initial-value bound in (50) gives a uniform $2m$th moment of $\|X_n\|_\infty$. The finitely many earlier levels also have finite moments of every order. Choosing $2m\ge r$ proves the first part of (48). The same choice in the interpolation bound, with $m\ge2$, and the inequality $\mathbb EW^r\le(\mathbb EW^{2m})^{r/(2m)}$ for $W\ge0$ prove (49).</p>

<p>For the finite tree, apply these bounds at each level $n+j$, where $0\le j\le k$. The maximum raised to a positive power is bounded by the sum over the fixed set of nodes. Thus its supremum moments are uniformly bounded at every fixed order and its maximum interpolation error tends to zero in every such moment. Independence between nodes is not required for either estimate.</p>

<p>Q4PO and F7Q2 give weak convergence to continuous paths. The maximum supremum norm is continuous there in the product $J_1$ topology. Truncating its powers first shows that the limiting supremum has all fixed moments; choosing a strictly larger even-order bound makes each desired power uniformly integrable. Removing the truncation proves (48) and its finite-tree version. For the asserted function $F$, the continuous mapping theorem gives convergence in distribution of its values. A moment bound of order greater than $s$ makes those values uniformly integrable, so their expectations converge. The same argument applies to the interpolations, whose supremum norms are at most the corresponding original norms and whose laws converge in the uniform path space. $\square$</p>

<p>This strengthens the supremum-moment conclusions of Q4PO and F7Q2 at every fixed order, including at $d=3\alpha$. It gives no bound uniform in the order, no exponential-moment conclusion and no extension to growing tree depth, growing or noninteger power indices, comparable kernels or full-law block restrictions. It is not a source erratum; attribution is in <a href="/articles/hierarchical-runaway/#section-history">History and attribution</a>. Independent mathematical review, the journal comparison and Lean formalisation remain pending; all earlier tagged statements and source assessments are preserved.</p>

## History and attribution {#section-history}

<p>The setting of the final sections and the conjecture of Gaussian fluctuations for the critical power sums are from <a href="https://arxiv.org/abs/2211.05686v1">Hutchcroft (2022)</a>, Remark 6.14. The following results go beyond that remark: <a href="/tag/Q7QG/">the two-thirds variance gap for squared mass</a>; <a href="/tag/9FO5/">Gaussian moments for independent triangular arrays with vanishing aggregate higher moments</a>; <a href="/tag/V7MP/">convergence of every fixed moment along fluctuation subsequences</a>; <a href="/tag/J0DE/">Gaussian fluctuations of squared mass</a>; <a href="/tag/MFGT/">joint Gaussian fluctuations of integer power sums with explicit covariance</a>; <a href="/tag/OQV3/">the Gaussian limit at several times</a>; <a href="/tag/Q4PO/">the functional Gaussian limit within a coalescent layer</a>; <a href="/tag/F7Q2/">the joint Gaussian limit across nested blocks</a>; and <a href="/tag/NC7F/">convergence of every fixed supremum moment of the path limit</a>. Each of these results is original to this wiki; proof not independently checked.</p>
