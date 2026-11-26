---
{
  "id": "hierarchical-lattice",
  "title": "The hierarchical lattice and radial kernels",
  "subtitle": "Finite-support geometry, shell counts and summable intensities",
  "kind": "model",
  "category": "Models",
  "summary": "The hierarchical lattice is a countable direct sum of finite groups. Its exact ball and shell counts turn radial summability into a geometric series and give elementary small-intensity susceptibility bounds. The full radial summability criterion and a return-corrected two-point bound keep the divergent and degenerate cases explicit.",
  "context": [
    "Integers $d\\geq0$ and $L\\geq1$; the nontrivial hierarchical geometry has $d\\geq1$ and $L\\geq2$.",
    "Elements have finite support. The full infinite product is a different space.",
    "Percolation uses unordered pairs of distinct vertices; diagonal coordinates do not affect the simple open graph."
  ],
  "related": [
    "hierarchical-two-point",
    "subcritical-bound",
    "product-model",
    "product-symmetries",
    "cutoff-families",
    "walk-kernels"
  ],
  "sourceIds": ["hutchcroft-book", "perclib-hierarchical-model", "perclib-hierarchical-geometry", "perclib-hierarchical-small-two-point", "perclib-hierarchical-cutoff", "perclib-hierarchical-ball-sums", "perclib-train10-models-hierarchicalsymmetry"],
  "aliases": [
    "hierarchical lattice",
    "ultrametric",
    "radial kernel",
    "shell count",
    "hierarchical row sum",
    "direct sum"
  ],
  "prototypeUses": []
}
---

## A countable direct sum {#section-lattice}

<p>We use the existing <a href="/tag/XMYD/">hierarchical lattice</a> and <a href="/tag/T6SL/">distance convention</a>, indexing coordinates from zero instead of one. Coordinate $j$ here is coordinate $j+1$ there, so the extra one in the level leaves the distance unchanged. Put $A=(\mathbb Z/L\mathbb Z)^d$ and $N=|A|=L^d$. The hierarchical lattice is the additive group</p><div class="math-display">$$\mathbb H=\bigoplus_{j\geq0}A=\{x=(x_0,x_1,\ldots):x_j\in A,\ x_j=0\text{ for all but finitely many }j\}.$$</div><p>Set $\ell(0)=0$ and, for $x\ne0$,</p><div class="math-display">$$\ell(x)=1+\max\{j:x_j\ne0\}.$$</div><p>The level-$n$ block at the origin is $B_n=\{x:\ell(x)\leq n\}$, equivalently the sequences supported in $\{0,\ldots,n-1\}$. The block at $x$ is $x+B_n$. Define $D(x,x)=0$ and $D(x,y)=L^{\ell(y-x)}$ for $x\ne y$.</p><p>Every element lies in some finite block, so $\mathbb H$ is countable. When $d=0$ or $L=1$, $A$ and $\mathbb H$ are singletons. The indexing starts with $B_0=\{0\}$; the first nontrivial displacement, when it exists, has level one.</p>

## Geometry of blocks and shells {#section-counts}

<p>The function $D$ is the translation-invariant ultrametric of the existing distance convention, and its closed ball of radius $L^n$ at $x$ is $x+B_n$.</p><a id="tag-9408" data-assertion="proposition" data-title="Nested hierarchical blocks and exact shell counts"></a><p>Any two blocks are disjoint or one contains the other. The known ball count and its shell consequence are</p><div class="math-display">$$|B_n|=N^n,\qquad |\{x:\ell(x)=n\}|=N^n-N^{n-1}\quad(n\geq1).$$</div><p><em>Proof.</em> Above the largest index at which either $u$ or $v$ is nonzero, $u+v$ vanishes. Thus $\ell(u+v)\leq\max\{\ell(u),\ell(v)\}$; negation preserves the level. These facts give symmetry and the strong triangle inequality for $D$. The zero case supplies positive definiteness, and the distance depends only on displacement.</p><p>Restriction to the first $n$ coordinates is a bijection from $B_n$ to $A^n$: its inverse extends a finite string by zero. This proves the ball count. The level-$n$ shell is $B_n\setminus B_{n-1}$, giving the difference. The groups $B_n$ are nested subgroups. If two cosets of possibly different levels intersect, the coset of the smaller subgroup is contained in the coset of the larger. The metric-ball description follows directly from the level definition; in the singleton cases it is immediate.</p>

## Summing a radial kernel {#section-radial}

<a id="tag-6KJQ" data-assertion="proposition" data-title="Radial sums and the geometric hierarchical kernel"></a><p>For $f:\mathbb N\to[0,\infty]$, with $0\cdot\infty=0$ for empty shells,</p><div class="math-display">$$\sum_{x\in\mathbb H}f(\ell(x))=f(0)+\sum_{n\geq1}(N^n-N^{n-1})f(n)\leq\sum_{n\geq0}N^nf(n).$$</div><p>In particular, for finite $C,r\geq0$ with $Nr&lt;1$, the kernel $k(x)=Cr^{\ell(x)}$, using $r^0=1$ also when $r=0$, satisfies</p><div class="math-display">$$\sum_{x\ne0}k(x)=\frac{C(N-1)r}{1-Nr}=:M,\qquad \sum_xk(x)\leq\frac C{1-Nr}.$$</div><p>If $2Nr\leq1$, the total sum is at most $2C$.</p><p><em>Proof.</em> Partition the countable lattice by level and use the shell counts. Nonnegativity permits regrouping, including for an infinite sum. For the geometric kernel,</p><div class="math-display">$$\sum_{n\geq1}(N^n-N^{n-1})Cr^n=C(N-1)r\sum_{j\geq0}(Nr)^j.$$</div><p>Summing the geometric series proves the exact off-diagonal formula. Bounding each shell by its ball gives $\sum_xk(x)\leq C\sum_{n\geq0}(Nr)^n$, and $Nr\leq1/2$ gives the last bound.</p><p>For $L\geq2$ and $r=L^{-(d+\alpha)}$ with $\alpha&gt;0$, $Nr=L^{-\alpha}&lt;1$. Thus this radial power kernel is summable. The convenient sufficient condition for the bound $2C$ is $L^\alpha\geq2$; it is stronger than summability itself. When $N=1$, there are no nonzero displacements and the exact off-diagonal sum is zero.</p>

## Cutoff blocks and omitted rows {#section-cutoff}

<a id="tag-KL29" data-assertion="proposition" data-title="Finite hierarchical cutoff clusters and exact omitted geometric row"></a>
<p>For $J(x,y)=Cr^{\ell(y-x)}$ with $Nr&lt;1$, retain only bonds whose displacement has level at most $n$, where $n\geq0$. Every cutoff cluster at $x$ lies in $x+B_n$, so its volume is at most $N^n$ in every configuration. The omitted intensity row is</p>
<div class="math-display">$$\sum_{\ell(y-x)&gt;n}J(x,y)=\frac{C(N-1)r}{1-Nr}(Nr)^n=M(Nr)^n,$$</div>
<p>using $(Nr)^0=1$ also when $r=0$. Thus in the exponential intensity family the omitted probability row is at most $\beta M(Nr)^n$.</p>
<p><em>Proof.</em> Every retained edge has displacement in the subgroup $B_n$. All vertices reached along a retained path therefore remain in the starting coset, which has $N^n$ vertices. For the row, sum the shells from level $n+1$ onwards:</p>
<div class="math-display">$$\sum_{j=n+1}^\infty C(N^j-N^{j-1})r^j=C(N-1)r\sum_{j=n}^\infty(Nr)^j=M(Nr)^n.$$</div>
<p>The probability estimate follows term by term from $1-e^{-\beta J}\leq\beta J$.</p>
<p>For $L\geq2$ and the power kernel $r=L^{-(d+\alpha)}$, $\alpha&gt;0$, this is exactly $ML^{-\alpha n}$, or $MR^{-\alpha}$ at the hierarchical radius $R=L^n$. Cutoff clusters have finite moments of every order at every finite intensity, because their volumes are deterministically bounded. This uses confinement to a finite subgroup coset, not merely the fact that a vertex has finitely many retained neighbours.</p>

## Independent bonds with radial intensity {#section-percolation}

<a id="tag-B6KD" data-assertion="corollary" data-title="Hierarchical small-intensity susceptibility and threshold bounds"></a><p>For distinct $x,y\in\mathbb H$, let $J(x,y)=Cr^{\ell(y-x)}$, and open their bond independently with probability $1-e^{-\beta J(x,y)}$, where $\beta\geq0$ is finite. Diagonal intensities may be arbitrary. Suppose $Nr&lt;1$ and let $M=C(N-1)r/(1-Nr)$. Whenever $\beta M&lt;1$,</p><div class="math-display">$$\chi_\beta(x)\leq\frac1{1-\beta M}\quad\text{for every }x,$$</div><p>and almost surely every cluster is finite. For $M&gt;0$, every root critical intensity and the global critical intensity are at least $M^{-1}$. If $M=0$, all off-diagonal intensities vanish, every cluster is a singleton, susceptibility is one, and those critical intensities are infinite.</p><p>Under the simpler condition $2Nr\leq1$, one may replace $M$ by the upper bound $2C$: $2\beta C&lt;1$ gives $\chi_\beta(x)\leq(1-2\beta C)^{-1}$, and for $C&gt;0$ the critical intensities are at least $(2C)^{-1}$.</p><p><em>Proof.</em> Negation preserves level, so $J(x,y)=J(y,x)$ defines an intensity on unordered pairs. Translation by $x$ identifies its off-diagonal row with $\sum_{z\ne0}k(z)=M$. Apply the <a href="/tag/E771/">intensity row-sum bound</a> and its <a href="/tag/JZ47/">threshold consequence</a>. The lattice is countable, so the fixed-root finiteness conclusions hold simultaneously at all vertices. The estimate with $2C$ follows from the radial total-sum bound. If $M=0$, nonnegativity forces every off-diagonal intensity to be zero.</p><p>For example, $d=1$, $L=2$, $C=1$ and $r=1/4$ satisfy $2Nr=1$. The conservative bound at $\beta=1/8$ is $\chi\leq4/3$. The exact shell calculation gives $M=1/2$ and the stronger bound $\chi\leq16/15$. These are sufficient small-intensity estimates, not assertions identifying the critical intensity or describing behaviour at it.</p>

<p>This article gives the concrete direct-sum realization and elementary radial calculations. The exact shell formulas strengthen the ball-count estimates used in the current library construction, but no compiled association or correspondence review is inferred from that mathematical relationship. The <a href="/articles/hierarchical-two-point/">critical two-point theorem</a> needs additional arguments and hypotheses.</p>

<p>The algebraic descent of the radial kernel to unordered pairs uses only invariance of support under negation. It therefore also works on the direct sum of copies of any additive group: the level is unchanged by negation, including at zero, and $Cr^{\ell(y-x)}=Cr^{\ell(x-y)}$. In particular it remains valid if the coordinate group is $\mathbb Z^d$, corresponding to the source's zero-modulus convention. That case lies outside the finite-coordinate-group setting above: for $d\geq1$, its level-one block is infinite, so none of the displayed finite ball counts or their summability consequences is asserted for it.</p>


## Coefficient groups and child blocks {#section-coefficient-groups}

<p>For this section allow $A$ to be any Abelian group, finite or infinite, and write $\mathbb H(A)=\bigoplus_{j\geq0}A$. Keep the same support level $\ell$ and origin blocks $B_n$.</p>

<a id="tag-BW7V" data-assertion="proposition" data-title="Support-level blocks over arbitrary Abelian coefficient groups and their child partition"></a>
<p>The level is zero exactly at the zero vector and satisfies $\ell(u+v)\leq\max\{\ell(u),\ell(v)\}$. Displacement levels are symmetric, translation invariant, and satisfy the corresponding strong triangle inequality. Each $B_n$ is a subgroup, restriction gives a bijection $B_n\simeq A^n$, and its translates are precisely the level-$n$ balls. Intersecting balls of the same level coincide. If $e_n(a)$ is the vector with entry $a$ at coordinate $n$ and zero elsewhere, then</p>
<div class="math-display">$$B_{n+1}=\bigsqcup_{a\in A}\bigl(e_n(a)+B_n\bigr).$$</div>
<p>In particular, every ball is finite when $A$ is finite, while $B_1$ is infinite when $A$ is infinite.</p>
<p><em>Proof.</em> The condition $\ell(z)\leq n$ is exactly that $z_i=0$ for $i\geq n$. Supports of sums lie in unions of supports, and negation preserves support; these give the level inequalities and the subgroup property. Subtracting two vectors gives the displacement assertions. A translated ball is a subgroup coset, so equal-level balls either coincide or are disjoint. Restriction below $n$, with zero extension as inverse, proves the bijection.</p>
<p>Finally, every $z\in B_{n+1}$ has a unique decomposition $z=e_n(z_n)+w$ with $w\in B_n$. Its coordinate $n$ determines the child label, proving both the union and disjointness. None of these arguments requires finiteness of $A$. Finite ball counts and countability of the whole direct sum require separate hypotheses.</p>

## The full radial summability criterion {#section-full-radial}

<p>Return to $A=(\mathbb Z/L\mathbb Z)^d$, $L\geq1$, and $N=L^d$. The origin has level zero, and the earlier exact shell count is $N^{n+1}-N^n=(N-1)N^n$ at level $n+1$.</p>

<a id="tag-YW7B" data-assertion="theorem" data-title="Extended geometric radial sums and the complete hierarchical power-kernel summability criterion"></a>
<p>For any $r\in[0,\infty]$, the origin-deleted radial sum is</p>
<div class="math-display">$$S(r):=\sum_{z\ne0}r^{\ell(z)}=(N-1)r\sum_{n\geq0}(Nr)^n.$$</div>
<p>With $0\cdot\infty=0$, this identity includes all degenerate cases. If $N=1$ or $r=0$, then $S(r)=0$. If $N&gt;1$ and $0&lt;r&lt;\infty$, then</p>
<div class="math-display">$$S(r)=\begin{cases}(N-1)r/(1-Nr),&amp;Nr&lt;1,\\ \infty,&amp;Nr\geq1.\end{cases}$$</div>
<p>For $N&gt;1$ and $r=\infty$, $S(r)=\infty$. In particular, if $L\geq2$ and $d\geq1$, then for every real $\alpha$,</p>
<div class="math-display">$$\sum_{z\ne0}L^{-(d+\alpha)\ell(z)}&lt;\infty\quad\Longleftrightarrow\quad\alpha&gt;0.$$</div>
<p><em>Proof.</em> Group by the finite shells and factor their exact cardinalities:</p>
<div class="math-display">$$S(r)=\sum_{n\geq0}(N-1)N^n r^{n+1}=(N-1)r\sum_{n\geq0}(Nr)^n.$$</div>
<p>For $N&gt;1$ and finite positive $r$, the prefactor is finite and positive. The geometric series is finite exactly when $Nr&lt;1$, giving the displayed cases. If $N=1$ there are no nonzero vectors, and if $r=0$ every positive-level term vanishes. Infinite $r$ gives an infinite term as soon as a nonzero vector exists. Finally put $r=L^{-(d+\alpha)}$. This is finite and positive, and $Nr=L^{-\alpha}&lt;1$ exactly for $\alpha&gt;0$ because $L&gt;1$.</p>
<p>The criterion needs no condition such as $L^\alpha\geq2$; that stronger condition was used only for the convenient total-mass bound $2C$. The earlier assertions 9408, 6KJQ and B6KD retain their finite-sum formulas and conservative estimates. The exact geometry source additionally proves the full equivalence above; this does not change what the earlier model source exported.</p>

## Two-point decay at small intensity {#section-small-two-point}

<a id="tag-0K45" data-assertion="theorem" data-title="The hierarchical two-point function inherits radial decay at small intensity"></a>
<p>Let $C\geq0$, $0\leq r\leq1$, and $\beta\geq0$ be finite. Give distinct $x,y\in\mathbb H$ intensity $J(x,y)=Cr^{\ell(y-x)}$ and independent opening probability $1-e^{-\beta J(x,y)}$. Diagonal parameters may be arbitrary. Write</p>
<div class="math-display">$$M=\sum_{z\ne0}Cr^{\ell(z)}\in[0,\infty].$$</div>
<p>For distinct $x,y$, with $H(t)=\sum_{n\geq0}t^n$ and extended products interpreted as above,</p>
<div class="math-display">$$\tau_\beta(x,y)\leq\beta J(x,y)H(2\beta M)H(\beta M).$$</div>
<p>In particular, if $M&lt;\infty$ and $2\beta M&lt;1$,</p>
<div class="math-display">$$\tau_\beta(x,y)\leq\frac{\beta C r^{\ell(y-x)}}{(1-2\beta M)(1-\beta M)}.$$</div>
<p><em>Proof.</em> Set $j(x,x)=0$ and $j(x,y)=J(x,y)$ otherwise. Its rows and columns both sum to $M$, by translation and symmetry. For $z\notin\{x,y\}$, the strong triangle inequality gives</p>
<div class="math-display">$$\ell(y-x)\leq\max\{\ell(z-x),\ell(y-z)\}.$$</div>
<p>Since $r\leq1$, at least one of $J(x,z),J(z,y)$ is at most $J(x,y)$. The terms at $z=x,y$ vanish, so for all $z$,</p>
<div class="math-display">$$j(x,z)j(z,y)\leq J(x,y)\bigl(j(x,z)+j(z,y)\bigr).$$</div>
<p>Summation gives $\sum_z j(x,z)j(z,y)\leq2MJ(x,y)$. The kernel $\beta j$ therefore has row bound $\beta M$ and off-diagonal convolution constant $2\beta M$, and it dominates the bond probabilities by $1-e^{-t}\leq t$. Apply the <a href="/tag/9L60/">two-point bound with its return factor</a>. Deleting loops leaves connection events unchanged, so the argument does not restrict their original marginals.</p>
<p>For $N&gt;1$, $C&gt;0$ and $0&lt;r&lt;1/N$, the earlier shell formula gives $M=C(N-1)r/(1-Nr)$. At a fixed $\beta&gt;0$ with $2\beta M&lt;1$, the direct edge also gives the additional lower bound</p>
<div class="math-display">$$\tau_\beta(x,y)\geq1-e^{-\beta J(x,y)}\geq\beta e^{-\beta C}J(x,y).$$</div>
<p>Indeed, $0\leq J(x,y)\leq C$ and $1-e^{-t}=\int_0^t e^{-u}\,du\geq te^{-\beta C}$ for $0\leq t\leq\beta C$. Thus the two-point function is comparable to the radial kernel in this small-intensity regime. The source exports the upper bound; the one-edge lower comparison is an additional deduction.</p>
<p>At $\beta=0$, or when $C=0$ or $r=0$, distinct vertices are disconnected. When the group is a singleton there are no distinct vertices. The extended upper bound also covers infinite $M$, but supplies no finite decay estimate there. At or beyond $2\beta M=1$ its geometric factor diverges. No critical-intensity conclusion or critical two-point asymptotic follows from this small-intensity argument; the original <a href="/articles/hierarchical-two-point/">critical article</a> is unchanged.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-hierarchical/">30-contract inventory</a> reconciles the existing radial-model estimates, arbitrary-coefficient geometry, exact extended sums and the two-point application. Formal tag associations and independent correspondence review remain separate.</p>

## Source conventions for cutoff confinement {#section-cutoff-source}

<p>The source separates the deterministic geometry in <a href="/tag/KL29/">KL29</a> from its probabilistic use. A configuration containing only bonds of level at most $n$ has every cluster in a level-$n$ ball, by the strong triangle inequality along a path. If instead a profile assigns probability zero to longer bonds, the conclusion holds almost surely: on the countable lattice, the union of all zero-probability long-edge events is null. This is simultaneous for every root. The ambient configuration space still contains exceptional configurations with long edges, so the profile hypothesis does not imply confinement for every point of that space.</p>
<p>For finite $C,r\geq0$, set $\rho=Nr$ and $a=C(N-1)r$. The omitted intensity mass has the extended-sum expression</p>
<div class="math-display">$$\sum_{\ell(y-x)&gt;n}J(x,y)=a\rho^n\sum_{j\geq0}\rho^j.$$</div>
<p>If $a=0$, the sum is zero. If $a&gt;0$ and $\rho\geq1$, it is infinite for every finite cutoff $n$. In the summable case $\rho&lt;1$ it equals $a\rho^n/(1-\rho)$, as in KL29. The source writes one extended quotient for all cases, using truncated subtraction and $0\cdot\infty=0$. The finite real formula in KL29 continues to require $\rho&lt;1$; it is not a geometric-series formula beyond its convergence range.</p>
<p>The source specializes the cutoff radius to zero to recover the exact off-diagonal row used in <a href="/tag/B6KD/">B6KD</a>. With $N=2$, $C=1$ and $r=1/4$, it has $M=1/2$ and omitted mass $2^{-n-1}$. At intensity one this gives $\chi\leq2$, almost-sure finiteness of all clusters, and both critical intensities at least two. Its zero-amplitude example gives singleton clusters and infinite thresholds.</p>
<p>The radial formula in this source is imposed on all pairs, so it gives $J(x,x)=C$. The off-diagonal row and graph observables do not depend on that choice. Replacing the diagonal by any other finite nonnegative values recovers the arbitrary-diagonal formulation of B6KD without changing the calculation. Finite ball counts require $L\ne0$; the separate deterministic reachability bound does not. The <a href="/coverage/sources/perclib-22d8485-applications/">thirteen-contract cutoff inventory</a> records these distinctions.</p>


## What pointwise bounds give on a ball {#section-ball-sums-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-spatial/">ball-sum source</a> isolates the summation step behind <a href="/tag/V4QQ/">V4QQ</a> and <a href="/tag/YWTU/">YWTU</a>. Let $L\geq2$, $d\geq1$, $\alpha&gt;0$, and suppose a nonnegative kernel satisfies $f(x,x)\leq1$ and</p>
<div class="math-display">$$aL^{-\ell(y-x)(d-\alpha)}\leq f(x,y)\leq AL^{-\ell(y-x)(d-\alpha)}\qquad(x\ne y),$$</div>
<p>with $a,A\geq0$. Each shell contributes at most $AL^{\alpha j}$, so summing the geometric series gives an upper ball sum $(1+AL^\alpha/(L^\alpha-1))L^{\alpha n}$. For $n\geq1$, the outer shell alone has at least $L^{dn}/2$ points and gives the lower bound $(a/2)L^{\alpha n}$. At $n=0$ the sum is just $f(x,x)$; an off-diagonal assumption supplies no positive lower bound there. The lower-shell calculation by itself permits every real $\alpha$.</p>
<p>For the two-point function the ball sum is $\mathbb E|K_x\cap(x+B_n)|$, by summing vertex indicators. If instead $f(x,y)$ is the probability of connection inside the smallest common ball of $x$ and $y$, the same shell estimates bound that local sum. Local connection implies full connection, giving a lower bound for the full expected intersection. It supplies no corresponding upper bound for the full intersection, because a connecting path can leave the smallest common ball.</p>
<p>The pointwise bounds remain hypotheses of this source. It does not establish the critical estimates in the preserved <a href="/articles/hierarchical-two-point/">critical two-point article</a>, and it needs no translation invariance merely to reindex a ball sum about its centre.</p>


## Moving pairs of equal level {#section-level-isometries}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-analysis-symmetry/">symmetry source</a> proves that any two ordered pairs with the same displacement level are related by a level-preserving bijection, for every Abelian coefficient group $A$. The construction uses the characterization</p>
<div class="math-display">$$\ell(a-b)\leq m\quad\Longleftrightarrow\quad a_i=b_i\text{ for every }i\geq m.$$</div>
<p>Translate the first endpoints to zero. If the two resulting nonzero vectors $u,v$ have level $m+1$, they vanish above coordinate $m$ and are nonzero at $m$. Their level-$m$ balls therefore exclude zero. If these balls coincide, translating that ball by $v-u$ and fixing its complement is a level isometry. If they differ, translate the ball of $u$ to that of $v$, translate the latter back, and fix the complement. Within each ball differences are unchanged; between distinct level-$m$ balls the first differing coordinate is at least $m$, and the exchange preserves that level. The map fixes zero and sends $u$ to $v$. Translating back gives the desired pair map. At level zero the two endpoints coincide and a translation suffices.</p>
<p>A radial intensity is preserved by this bijection, so its product law is preserved as well. Consequently the full two-point function depends only on the displacement level. The map also takes the smallest ball containing one pair to the corresponding ball for the other, proving the same statement for internal connections. Translations give root independence of susceptibility and, for countable $A$, of the extended cluster-volume distribution.</p>
<p>For $A=(\mathbb Z/L\mathbb Z)^d$, constancy on a nonempty level-$m+1$ shell identifies its two-point value with the shell average. The shell has $L^{d(m+1)}-L^{dm}$ points. The source assumes a point in that shell before dividing by its cardinality, so the singleton coefficient-group cases cause no division by zero.</p>
