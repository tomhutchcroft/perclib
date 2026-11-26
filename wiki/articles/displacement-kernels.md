---
{
  "id": "displacement-kernels",
  "title": "Displacement kernels and translation symmetry",
  "subtitle": "Unordered pairs, the choice of translation action, and exact row sums",
  "kind": "model",
  "category": "Models",
  "summary": "An inversion-even displacement kernel defines symmetric pair intensities. Its off-diagonal row is the kernel mass away from the identity, and the chosen displacement convention determines which translations preserve it. On the integer line, closed cuts have an exact infinite-product criterion and can trap every cluster.",
  "context": [
    "A countable group $G$ with identity $e$, written multiplicatively until the examples on additive groups.",
    "A finite nonnegative intensity kernel $k:G\\to[0,\\infty)$; its sum may be infinite.",
    "The convention $J(x,y)=k(yx^{-1})$ corresponds to $k(y-x)$ in additive notation."
  ],
  "related": [
    "product-model",
    "product-symmetries",
    "subcritical-bound",
    "criticality",
    "hierarchical-two-point",
    "infinite-cluster-zero-one",
    "integrated-susceptibility",
    "open-degree-laws"
  ],
  "sourceIds": ["hutchcroft-book", "perclib-translation-models", "perclib-long-range-cuts", "perclib-power-law", "perclib-nonsummable-kernels", "perclib-line-first-moment", "perclib-long-range-interface", "perclib-train10-models-longrange-rootindependence", "perclib-train10-models-longrange-cutoffpowerlaw"],
  "aliases": [
    "displacement kernel",
    "translation invariant",
    "even kernel",
    "right translation",
    "conjugacy invariant",
    "kernel row sum",
    "long-range cuts",
    "crossing intensity",
    "closed gap",
    "one-dimensional cut probability",
    "power kernel summability",
    "lattice shell counts",
    "nonsummable intensity"
  ],
  "prototypeUses": []
}
---

## Descending to unordered pairs {#section-symmetry}

<a id="tag-U8CI" data-assertion="proposition" data-title="Even displacement kernels and the translation action"></a><p>The prescription $J(x,y)=k(yx^{-1})$ defines a function on unordered pairs, including repeated pairs, if and only if</p><div class="math-display">$$k(z^{-1})=k(z)\qquad(z\in G).$$</div><p>When this holds, it is invariant under simultaneous right translation:</p><div class="math-display">$$J(xg,yg)=J(x,y).$$</div><p>It is invariant under all simultaneous left translations if and only if $k$ is conjugacy invariant, meaning $k(gzg^{-1})=k(z)$ for every $g,z\in G$.</p><p><em>Proof.</em> Swapping $x,y$ replaces $yx^{-1}$ by its inverse, so inversion symmetry is sufficient. Conversely, symmetry of the pair $(e,z)$ gives $k(z)=k(z^{-1})$. For right translations,</p><div class="math-display">$$(yg)(xg)^{-1}=yx^{-1},$$</div><p>whereas left translation changes the displacement to $(gy)(gx)^{-1}=g(yx^{-1})g^{-1}$. This proves sufficiency of conjugacy invariance; taking $x=e$ and $y=z$ proves necessity.</p><p>On an Abelian group, left and right translation coincide, and inversion symmetry is the usual condition $k(-z)=k(z)$. On a general group the distinction matters. For example, in the permutation group of three letters, the kernel supported on one transposition is inversion-even but not conjugacy invariant: conjugation can move that transposition to another one. The corresponding pair intensity is right-invariant but need not be left-invariant.</p><p>Using $k(x^{-1}y)$ instead would give the left-invariant convention. The two conventions agree on Abelian groups. A statement about translation symmetry should specify the action when the group is not Abelian.</p>

## The off-diagonal row {#section-row}

<a id="tag-R01V" data-assertion="proposition" data-title="Displacement-kernel row identity excluding the diagonal"></a><p>For $J(x,y)=k(yx^{-1})$, every vertex has the same off-diagonal row:</p><div class="math-display">$$\sum_{y\ne x}J(x,y)=\sum_{z\ne e}k(z)=:M\leq\sum_zk(z).$$</div><p>These are nonnegative extended sums. The identity does not need inversion symmetry; that condition is needed to interpret the ordered-pair expression as an undirected bond intensity. It is unchanged if the diagonal values $J(x,x)$ are replaced arbitrarily.</p><p><em>Proof.</em> The map $y\mapsto yx^{-1}$ is a bijection from $G$ to itself, taking $x$ to $e$. Reindex the sum over their complements. The inequality follows by adding the nonnegative identity term.</p><p>Thus a bound on the total kernel mass is sufficient, but it may discard useful information: $k(e)$ contributes to that total and not to any open edge of the simple graph. A positive kernel concentrated at the identity produces no non-loop bonds.</p>

## Probability profiles and intensity families {#section-probability}

<p>If an inversion-even function $p:G\to[0,1]$ specifies the off-diagonal bond probabilities by $q(\{x,y\})=p(yx^{-1})$, their row sum is $m=\sum_{z\ne e}p(z)$. For $m&lt;1$, the <a href="/tag/53Z9/">row-sum theorem</a> gives $\chi_q(x)\leq(1-m)^{-1}$ at every vertex and simultaneous almost-sure finiteness of all clusters. No support-generation hypothesis is needed for this estimate.</p><p>For an intensity kernel with $M&lt;\infty$, the <a href="/tag/A65C/">exponential family</a> instead has off-diagonal probabilities $1-e^{-\beta k(yx^{-1})}$. The inequality $1-e^{-t}\leq t$ bounds their row by $\beta M$, so the <a href="/tag/E771/">intensity bound</a> gives</p><div class="math-display">$$\beta M&lt;1\quad\Longrightarrow\quad\chi_\beta(x)\leq\frac1{1-\beta M}.$$</div><p>For $M&gt;0$, the <a href="/tag/JZ47/">threshold consequence</a> gives root and global critical intensities at least $M^{-1}$. If $M=0$, all off-diagonal intensities vanish, susceptibility is one and both kinds of threshold are infinite. This does not assert a transition at a finite intensity when $M&gt;0$.</p><p>The simple open graph is right-translation invariant in law, by <a href="/tag/6VY0/">product-law transport</a>, and its vertex observables therefore have the same distribution at every root. Arbitrary diagonal probabilities do not alter that graph law. Invariance of the entire configuration, including loop coordinates, would additionally require those diagonal marginals to be preserved by the action.</p>

## Concrete kernels {#section-examples}

<p>On $\mathbb Z^d$, the nearest-neighbour intensity $k(z)=C\mathbf1_{\{\|z\|_1=1\}}$ has $M=2dC$. For $d\geq1$ and $C&gt;0$, the preceding estimate reads $\chi_\beta\leq(1-2dC\beta)^{-1}$ when $2dC\beta&lt;1$, and the intensity thresholds are at least $(2dC)^{-1}$. For $d=0$ the vertex group is a singleton and the off-diagonal row is zero.</p><p>More generally, on any group choose $a\in G$ and take the intensity kernel</p><div class="math-display">$$k(z)=\mathbf1_{\{z=a\}}+\mathbf1_{\{z=a^{-1}\}}.$$</div><p>It is inversion-even and its total mass is two. If $a\ne e$, the off-diagonal mass is also two, yielding $\chi_{1/4}\leq2$ and threshold lower bounds $1/2$. If $a=a^{-1}\ne e$, the single nonzero kernel value is two: the two terms are added, not collapsed into one. This is an intensity kernel, so a value above one is allowed. If $a=e$, both contributions lie on the diagonal and the off-diagonal mass is zero.</p><p>The support may generate only a proper subgroup, leaving the possible-edge graph disconnected. None of the row estimates requires connectedness, and none turns this elementary small-intensity control into a claim of criticality or uniqueness.</p>

## Euclidean power-kernel tails {#section-power-tail}

<a id="tag-B2ZL" data-assertion="proposition" data-title="Omitted-row bounds for a Euclidean power-law intensity"></a>
<p>On $\mathbb Z^d$, $d\geq1$, use the norm $\|z\|_\infty=\max_i|z_i|$. Suppose $\alpha&gt;0$ and, for every $z\neq0$,</p>
<div class="math-display">$$c\|z\|_\infty^{-d-\alpha}\leq k(z)\leq C\|z\|_\infty^{-d-\alpha},\qquad 0&lt;c\leq C&lt;\infty.$$</div>
<p>For every real $R\geq1$,</p>
<div class="math-display">$$\frac{2dc}{\alpha\,2^\alpha}R^{-\alpha}\leq\sum_{\|z\|_\infty&gt;R}k(z)\leq\frac{2d\,3^{d-1}C\,2^\alpha}{\alpha}R^{-\alpha}.$$</div>
<p>The upper bound needs only the upper hypothesis on $k$. In particular the off-diagonal intensity row is finite. For an inversion-even kernel, closing all bonds of length greater than $R$ omits a probability row at most $\beta$ times the displayed upper bound in the exponential intensity family.</p>
<p><em>Proof.</em> The shell of radius $n\geq1$ has $(2n+1)^d-(2n-1)^d$ vertices. Integrating the derivative $d t^{d-1}$ of $t^d$ between $2n-1$ and $2n+1$ gives</p>
<div class="math-display">$$2d\,n^{d-1}\leq(2n+1)^d-(2n-1)^d\leq2d\,3^{d-1}n^{d-1}.$$</div>
<p>Multiplication by the kernel bounds reduces the omitted row to constant multiples of $\sum_{n&gt;R}n^{-1-\alpha}$. With $m=\lfloor R\rfloor\geq1$, comparison with integrals gives</p>
<div class="math-display">$$\frac{(m+1)^{-\alpha}}\alpha\leq\sum_{n=m+1}^\infty n^{-1-\alpha}\leq\frac{m^{-\alpha}}\alpha.$$</div>
<p>Since $m\geq R/2$ and $m+1\leq2R$, this proves the constants above. Summing the finitely many inner shells as well proves full row finiteness. Reindexing by displacement makes the same bound valid at every vertex, and $1-e^{-\beta k}\leq\beta k$ gives the probability-row estimate.</p>
<p>This supplies the omitted-kernel power bound used in a cutoff-to-full ghost comparison, for a kernel with the displayed pointwise upper estimate. Finite-range truncation on $\mathbb Z^d$ still leaves an infinite vertex set: the row-tail estimate alone does not show that its clusters have finite volume or finite moments.</p>


## Shells and radial sums {#section-radial-sums}

<p>Continue to use the supremum norm on $\mathbb Z^d$. It is integer-valued: $\|z\|_\infty=\max_i|z_i|$, with the maximum of the empty coordinate family equal to zero when $d=0$. Hence $\lfloor\|z\|_\infty\rfloor=\|z\|_\infty$, and this integer is zero exactly at the origin. The ball of radius $n$ is the coordinate box $[-n,n]^d\cap\mathbb Z^d$.</p>

<a id="tag-FQCZ" data-assertion="proposition" data-title="Exact supremum-norm shell counts and radial sum comparisons"></a>
<p>For integers $d,n\geq0$, the ball has $(2n+1)^d$ vertices. Write $a_d(n)=|\{z:\|z\|_\infty=n\}|$. Then $a_d(0)=1$ and, for $n\geq1$,</p>
<div class="math-display">$$a_d(n)=(2n+1)^d-(2n-1)^d.$$</div>
<p>For $d,n\geq1$,</p>
<div class="math-display">$$2d(2n-1)^{d-1}\leq a_d(n)\leq2d(2n+1)^{d-1}.$$</div>
<p>Every $g:\mathbb N\to[0,\infty]$ satisfies the extended-sum identity</p>
<div class="math-display">$$\sum_{z\in\mathbb Z^d}g(\|z\|_\infty)=\sum_{n\geq0}a_d(n)g(n).$$</div>
<p>When $d\geq1$ and $g(0)=0$, this gives</p>
<div class="math-display">$$\sum_{n\geq1}n^{d-1}g(n)\leq\sum_zg(\|z\|_\infty)\leq2d\,3^{d-1}\sum_{n\geq1}n^{d-1}g(n).$$</div>
<p><em>Proof.</em> Each of the $d$ coordinates in the ball has $2n+1$ choices. Subtracting the ball of radius $n-1$ counts the sphere, since norms are integers. For any $b\geq0$ and integer $e\geq0$, integration of $(e+1)t^e$ on $[b,b+2]$ gives</p>
<div class="math-display">$$2(e+1)b^e\leq(b+2)^{e+1}-b^{e+1}\leq2(e+1)(b+2)^e.$$</div>
<p>Taking $b=2n-1$ and $e=d-1$ gives the sharper shell bounds. Their weaker form follows from $n\leq2n-1$ and $2n+1\leq3n$. Finally, the finite shells partition the lattice. Grouping the nonnegative sum over this partition proves the identity and comparisons, including infinite sums. In dimension zero the origin is the only point, all positive-radius spheres are empty, and the radial sum is simply $g(0)$.</p>

## The summability threshold and an inclusive tail {#section-power-summability}

<a id="tag-6VNM" data-assertion="theorem" data-title="Power-kernel summability and a tail bound retaining the boundary shell"></a>
<p>For $d\geq1$ and any real $\alpha$, set $k_\alpha(0)=0$ and $k_\alpha(z)=\|z\|_\infty^{-d-\alpha}$ for $z\ne0$. This is a finite nonnegative even kernel, and</p>
<div class="math-display">$$\sum_z k_\alpha(z)&lt;\infty\quad\Longleftrightarrow\quad\alpha&gt;0.$$</div>
<p>The sum is interpreted in $[0,\infty]$, so it equals infinity when $\alpha\leq0$. For $\alpha&gt;0$ and every real $r\geq1$,</p>
<div class="math-display">$$\sum_{\|z\|_\infty\geq r}k_\alpha(z)\leq2d\,3^{d-1}\left(1+\frac1\alpha\right)r^{-\alpha}.$$</div>
<p><em>Proof.</em> Evenness follows from $\|-z\|_\infty=\|z\|_\infty$. Shell comparison reduces the sum to $\sum_{n\geq1}n^{-1-\alpha}$, since</p>
<div class="math-display">$$n^{d-1}n^{-d-\alpha}=n^{-1-\alpha}.$$</div>
<p>The positive-term power series $\sum_{n\geq1}n^t$ converges exactly for $t&lt;-1$, by integral comparison when $t&lt;0$ and failure of its terms to tend to zero when $t\geq0$. Thus the claimed threshold follows. For any family of nonnegative real numbers, summability is equivalent to finiteness of its extended nonnegative sum; no value is assigned to a divergent real series in this argument.</p>
<p>For the tail, let $m=\lceil r\rceil\geq1$. The first term and an integral bound give</p>
<div class="math-display">$$\sum_{n\geq m}n^{-1-\alpha}\leq m^{-1-\alpha}+\int_m^\infty t^{-1-\alpha}\,dt\leq\left(1+\frac1\alpha\right)r^{-\alpha}.$$</div>
<p>Multiplication by the shell constant proves the result. The corresponding finite-sum estimate can be seen directly from</p>
<div class="math-display">$$\alpha(x+1)^{-1-\alpha}\leq x^{-\alpha}-(x+1)^{-\alpha}\qquad(x&gt;0),$$</div>
<p>which follows by integrating $\alpha t^{-1-\alpha}$ on $[x,x+1]$. With $A(t)=t^{-\alpha}/\alpha+t^{-1-\alpha}$, it implies $n^{-1-\alpha}\leq A(n)-A(n+1)$ and hence $\sum_{n=m}^{N-1}n^{-1-\alpha}\leq A(m)-A(N)$ for $N\geq m$. For $N&lt;m$ the truncated sum is empty. This also proves the infinite-tail estimate by telescoping.</p>
<p>The boundary convention here is $\|z\|_\infty\geq r$, as in the source. The earlier estimate B2ZL concerns the strictly omitted row $\|z\|_\infty&gt;R$ and has different constants; both statements remain as written. For $d=0$, $k_\alpha$ is identically zero for every $\alpha$, so summability no longer characterizes a positive exponent. Setting the origin to zero explicitly avoids any convention for a real power of zero.</p>

## Infinite kernel rows {#section-nonsummable}

<a id="tag-K38T" data-assertion="corollary" data-title="Nonsummable displacement intensities have zero rooted and global thresholds"></a>
<p>Let $G$ be a countable group and let the finite nonnegative inversion-even kernel $k$ satisfy</p>
<div class="math-display">$$\sum_{z\ne e}k(z)=\infty.$$</div>
<p>For each fixed $\beta&gt;0$, independent bonds with non-diagonal probabilities $1-e^{-\beta k(yx^{-1})}$ give every vertex infinite degree, and hence an infinite cluster, almost surely. All rooted and global critical intensities are zero. At $\beta=0$ the graph has no edges and all clusters are singletons. Diagonal probabilities have no effect.</p>
<p><em>Proof.</em> The <a href="/tag/R01V/">row identity</a> gives infinite off-diagonal intensity at every vertex. For $t\geq0$, concavity on $[0,1]$ and monotonicity beyond one give</p>
<div class="math-display">$$1-e^{-\beta t}\geq(1-e^{-\beta})\min\{t,1\}.$$</div>
<p>If infinitely many values of $k$ are at least one, the sum of their truncated values diverges. Otherwise only finitely many finite terms were truncated, so that sum still diverges. The probability row is therefore infinite. The <a href="/tag/XJ74/">independent degree criterion</a> gives infinite degree at each root; countability makes the conclusion simultaneous at all vertices. Every positive intensity belongs to every rooted percolating set, whose infimum is consequently zero, as is the global infimum.</p>
<p>Thus, in positive dimension, the power kernel in 6VNM has zero critical intensities for $\alpha\leq0$. For $\alpha&gt;0$ its finite, positive row gives a strictly positive lower bound instead. The latter does not guarantee a finite threshold: the one-dimensional crossing criterion below is stronger than row summability. The constant kernel on $\mathbb Z$ is a simple nonsummable example. Neither the group argument nor the degree criterion assumes that the group is commutative.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-power-kernels/">power-kernel inventory</a> records all 33 named contracts for lattice geometry, radial sums and tails, together with the two nonsummable-kernel threshold contracts. The infinite-degree mechanism is supplied by XJ74; the two latter source exports state the threshold conclusions. These source correspondences remain pending independent review and compiled association.</p>


## Closed cuts on the integer line {#section-line-cuts}

<p>For a configuration on $\mathbb Z$, let $C_j$ be the event that no open bond crosses the gap between $j$ and $j+1$:</p>
<div class="math-display">$$C_j=\bigcap_{a\leq j&lt;b}\{\{a,b\}\text{ is closed}\}.$$</div>
<p>This is a measurable event, being a countable intersection of coordinate events. On $C_j$, two connected vertices lie on the same side of the gap. Indeed, every step of an open path stays on its starting side. Thus, if $\ell&lt;x\leq r$ and both $C_\ell,C_r$ occur, then $K(x)\subseteq(\ell,r]\cap\mathbb Z$ and the cluster is finite. These facts are deterministic and allow arbitrary long edges and loops.</p>
<p>Every pair crossing the gap at $j$ has a unique representation</p>
<div class="math-display">$$\{j-i,j+n-i\},\qquad n\geq1,\quad 0\leq i&lt;n.$$</div>
<p>Here $n=b-a$ is its length and $i=j-a$ is its left-endpoint offset. The smaller endpoint identifies the orientation of the unordered pair, so this parametrization is injective. In particular, exactly $n$ pairs of length $n$ cross a given gap. For arbitrary independent pair probabilities $q_{a,b}$, the <a href="/tag/QH7Q/">countable closed-product formula</a> gives</p>
<div class="math-display">$$\mathbb P_q(C_j)=\prod_{n\geq1}\prod_{i=0}^{n-1}(1-q_{j-i,j+n-i}).$$</div>
<p>The product is the decreasing limit over lengths $n\leq N$. Those finite families exhaust all crossing pairs. No diagonal coordinate occurs.</p>

<a id="tag-BQ44" data-assertion="theorem" data-title="The exact criterion for a positive long-range cut probability"></a>
<p>Suppose the non-diagonal probabilities have the distance form $q_{a,b}=p_{|b-a|}$, where $0\leq p_n\leq1$ for $n\geq1$. Diagonal probabilities may be arbitrary. Then, for every $j\in\mathbb Z$,</p>
<div class="math-display">$$\mathbb P_q(C_j)=\prod_{n\geq1}(1-p_n)^n,$$</div>
<p>and this probability is positive if and only if</p>
<div class="math-display">$$p_n&lt;1\quad(n\geq1),\qquad \sum_{n\geq1}np_n&lt;\infty.$$</div>
<p><em>Proof.</em> The product formula follows by grouping the crossing pairs by length. If $p_n=1$ at some positive length, a factor vanishes. For every $N$,</p>
<div class="math-display">$$\prod_{n=1}^N(1-p_n)^n\leq\exp\!\left(-\sum_{n=1}^Nnp_n\right),$$</div>
<p>so divergence of the sum also forces the limit to vanish. Conversely, suppose the sum is finite and all $p_n&lt;1$. Then $p_n\to0$. For sufficiently large $n$, $p_n\leq1/2$, and</p>
<div class="math-display">$$0\leq-\log(1-p_n)=\int_0^{p_n}\frac{dt}{1-t}\leq2p_n.$$</div>
<p>It follows that $\sum_n n[-\log(1-p_n)]&lt;\infty$: the finitely many initial terms are finite by $p_n&lt;1$. The product is the exponential of the negative of this sum, hence is strictly positive.</p>
<p>For example, $p_n=2^{-n}$ satisfies the criterion. For finite nonnegative intensities $J_n$ and $p_n=1-e^{-\beta J_n}$, a finite weighted sum $B=\sum_{n\geq1}nJ_n$ gives $\mathbb P_\beta(C_j)=e^{-\beta B}$ for every finite $\beta\geq0$. If $B=\infty$, the cut probability is zero for $\beta&gt;0$, whereas at $\beta=0$ every gap is closed. The latter case is evaluated directly, without a convention for $0\cdot\infty$.</p>

## From positive cut probability to finite clusters {#section-cuts-and-clusters}

<a id="tag-ZH13" data-assertion="corollary" data-title="Positive cut probability gives cuts on both sides of every vertex"></a>
<p>Under the distance-profile hypotheses of BQ44, if $p_n&lt;1$ for all $n\geq1$ and $\sum_{n\geq1}np_n&lt;\infty$, then almost surely the set of closed gaps is unbounded in both directions. Every open cluster is therefore finite.</p>
<p><em>Proof.</em> Let $D(\omega)=\{j:C_j\text{ occurs}\}$. The event $D\ne\varnothing$ is measurable and translation invariant. By <a href="/tag/WUAF/">ergodicity of the bond law</a>, its probability is zero or one. Since it contains $C_0$ and $\mathbb P_q(C_0)&gt;0$, its probability is one. The ergodic assertion applies after <a href="/tag/LNKT/">erasing diagonal coordinates</a>, which leaves every $C_j$ unchanged.</p>
<p>A stationary random subset of $\mathbb Z$ cannot have a largest element with positive probability. To see this, the measurable events $\{\max D=j\}$ are disjoint and all have the same probability by translation invariance. That probability must be zero, and their countable union has probability zero. The same argument excludes a smallest element. A nonempty subset of $\mathbb Z$ bounded above has a largest element, and one bounded below has a smallest element. Hence $D$ is almost surely unbounded in both directions. For every integer $x$, choose closed gaps $\ell&lt;x\leq r$. The preceding path argument traps $K(x)$ in the finite interval $(\ell,r]$. On this one event every cluster is finite.</p>
<p>The cuts need not be independent. They share long-edge coordinates; the proof uses stationarity and ergodicity instead. In the intensity model, the <a href="/tag/JK7V/">existing finite-crossing-intensity theorem</a> gives the same conclusion by a direct covariance calculation. In particular, $J_n\leq Cn^{-1-\alpha}$ with $\alpha&gt;1$ has no infinite cluster at any finite intensity.</p>
<p>The converse fails: clusters can be finite even when no gap is closed. Take $p_n=1/(4n^2)$. Then $\sum_n np_n=\infty$, so each $C_j$ has probability zero and almost surely no closed gap exists. Nevertheless the probability row is</p>
<div class="math-display">$$2\sum_{n\geq1}p_n=\frac{\pi^2}{12}&lt;1,$$</div>
<p>and the <a href="/tag/53Z9/">row-sum bound</a> gives $\chi\leq(1-\pi^2/12)^{-1}&lt;\infty$. Thus absence of cuts gives no percolation conclusion at the marginal power $n^{-2}$, or for slower decay.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-line-cuts/">12-contract source inventory</a> covers deterministic barriers, measurability, crossing-pair enumeration and the cut-product criterion. ZH13 combines those results with the separately proved ergodic theorem; it is an additional deduction, rather than a claimed export of the cut module. The earlier intensity proof JK7V and all preceding kernel statements are preserved.</p>


## Recurrence from decreasing events {#section-cut-recurrence}

<p>There is another short way to obtain the recurrence used in <a href="/tag/ZH13/">ZH13</a>. It is the argument in the newer one-dimensional source. Suppose the bond profile is translation invariant and every cut has probability at least $c&gt;0$. For $n\geq0$, put</p>
<div class="math-display">$$A_n^+=\bigcup_{k\geq n}C_k,\qquad A_n^-=\bigcup_{k\leq-n}C_k.$$</div>
<p>Both sequences decrease, and each event has probability at least $c$, since it contains $C_n$ or $C_{-n}$. Continuity from above gives</p>
<div class="math-display">$$\mathbb P\left(\bigcap_{n\geq0}A_n^+\right)\geq c,
\qquad\mathbb P\left(\bigcap_{n\geq0}A_n^-\right)\geq c.$$</div>
<p>The intersections mean that cuts are unbounded to the right and to the left. Translation shifts their cut indices by an integer and leaves each intersection unchanged. Ergodicity therefore makes both probabilities one. Their intersection is a single event on which every vertex is trapped between two cuts. This argument uses neither independence of the cut events nor an ergodic theorem for their spatial density.</p>
<p>For the intensity family in <a href="/tag/JK7V/">JK7V</a>, $B=\sum_{r\geq1}rJ_r&lt;\infty$ gives $c=e^{-\beta B}&gt;0$ at each finite $\beta\geq0$. Equivalently, the positive-cut criterion applies because $1-e^{-\beta J_r}&lt;1$ and $\sum_r r(1-e^{-\beta J_r})\leq\beta B$. Thus every rooted critical intensity and the global critical intensity are infinite. No law at infinite intensity is needed: the sets whose infima define these thresholds are empty. The weighted sum imposes no condition on $J_0$.</p>
<p>The source's translation and radial hypotheses specify diagonal values too. The graph conclusion with arbitrary diagonals follows by erasing them, as above; that extension is separate from the literal source contract. The <a href="/coverage/sources/perclib-caed44f-models/">ten-contract inventory</a> records the measurable recurrence events, translation identities, interval confinement and both threshold conclusions. The earlier product and covariance proofs remain unchanged.</p>


## The cutoff kernel in the new interface {#section-cutoff-interface}

<p>The <a href="/coverage/sources/perclib-f51f639-interfaces/">long-range interface</a> forms a radial intensity from a real profile by taking its nonnegative part off the diagonal and setting the diagonal to zero. Its cutoff profile is $K(s)-K(r)$ for $s\leq r$ and zero for $s&gt;r$. If $K$ is decreasing on positive distances, increasing $r$ increases the cutoff intensity. If $K$ is merely nonnegative there, the cutoff intensity is at most the full intensity for every $r&gt;0$; this comparison follows from taking nonnegative parts and does not require monotonicity.</p>
<p>The source proves these elementary comparisons and a one-dimensional inverse-square summability example. It also states the four power-law targets <a href="/tag/PVA8/">PVA8</a>, <a href="/tag/MQNP/">MQNP</a>, <a href="/tag/LF50/">LF50</a> and <a href="/tag/6YYS/">6YYS</a> as propositions to be proved. Their presence in the interface does not yet supply source proofs of the integral formula, the full convergence statement, the exact deficit or the derivative formulas.</p>


## Root independence throughout the cutoff family {#section-root-functional-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-analysis-symmetry/">root-independence source</a> transports the cluster together with the product law. A law-preserving vertex bijection takes the cluster of $x$ to the cluster of its image, without changing its cardinality. Thus every nonnegative measurable function of cluster size has the same expectation at roots related by such a bijection; infinite expectations are allowed. The source also states the transport identity for lower integrals of arbitrary functions, which does not assert measurability of those functions.</p>
<p>Both the radial lattice kernel and its soft-cutoff kernel depend only on displacement. Translation therefore gives equal root expectations at every scale and intensity. This conclusion needs no summability, regular variation or positivity of the original real profile: the kernel definition already takes its nonnegative part and removes the diagonal.</p>
<p>At positive field, the ghost transform equals the probability that the cluster meets an independent field of marks. Root equality therefore supplies the root-dominance premise used by the outside volume-tail arguments, uniformly over the entire cutoff family. It supplies only that premise. Almost-sure cutoff finiteness, omitted-row estimates and the analytic tail assumptions remain separate obligations.</p>


## Exact power-cutoff formulas {#section-power-cutoff-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-cutoff-locality/">power-cutoff source</a> now proves the four interface conclusions <a href="/tag/PVA8/">PVA8</a>, <a href="/tag/MQNP/">MQNP</a>, <a href="/tag/LF50/">LF50</a> and <a href="/tag/6YYS/">6YYS</a>. With $a=d+\alpha&gt;0$, positive radius $r$ and off-diagonal distance $s&gt;0$, its normalization is</p>
<div class="math-display">$$J_r(s)=\mathbf1_{\{s\leq r\}}\int_s^r t^{-a-1}\,dt=\frac{(s^{-a}-r^{-a})_+}{a}.$$</div>
<p>Integration gives the factor $1/a$. The formula increases to $s^{-a}/a$ as $r\to\infty$, and its deficit inside the radius is exactly $r^{-a}/a$. At $r\ne s$ its derivative is $r^{-a-1}\mathbf1_{\{s&lt;r\}}$; the intensity probability has derivative $\beta e^{-\beta J_r(s)}$ times that expression. At the corner $r=s$, the left derivative is zero and the right derivative is $s^{-a-1}$, so the ordinary derivative is not asserted there.</p>
<p>The general-profile source separates these conclusions. Decrease of $K$ on positive radii gives $J_r(s)=K(s)-K(r)$ inside the cutoff. The limit $K(r)\to0$ alone gives convergence of the clipped cutoff to the full clipped radial kernel. The derivative requires the local derivative of $K$ as well as avoidance of the distance corner. These facts do not prove a radius Russo formula for an infinite-cluster observable; its limiting argument is separate.</p>



## Edges between separated bulk sets {#section-bulk-edges}

<a id="tag-TKAS" data-assertion="proposition" data-title="Conditional direct-edge probabilities between separated bulk sets"></a>
<p>Suppose $J$ is a symmetric nonnegative lattice intensity kernel and, for some $\alpha&gt;0$,</p>
<div class="math-display">$$c|z|^{-d-\alpha}\leq J(z)\leq C|z|^{-d-\alpha}\qquad(|z|\geq r_0),$$</div>
<p>where $0&lt;c\leq C&lt;\infty$. Fix $\beta&gt;0$. For each $R\geq1$, let $U_R,V_R$ be finite disjoint deterministic vertex sets such that every cross distance lies in $[aR,bR]$, for fixed $0&lt;a\leq b&lt;\infty$. Reveal all bond coordinates except those with one endpoint in each set, and let $\mathcal F_R$ be the resulting sigma algebra. Let $A_R\subseteq U_R$ and $B_R\subseteq V_R$ be $\mathcal F_R$-measurable sets. Write $N_R$ for the number of open bonds between them and</p>
<div class="math-display">$$W_R=\sum_{x\in A_R,y\in B_R}J(y-x).$$</div>
<p>Almost surely, including when either set is empty,</p>
<div class="math-display">$$\mathbb P(N_R=0\mid\mathcal F_R)=e^{-\beta W_R},\qquad
\mathbb E[N_R\mid\mathcal F_R]=\sum_{x\in A_R,y\in B_R}(1-e^{-\beta J(y-x)}).$$</div>
<p>Suppose in addition that fixed $0&lt;\rho\leq M&lt;\infty$ satisfy $\rho R^d\leq|A_R|,|B_R|\leq MR^d$ almost surely for all large $R$. There are constants $0&lt;k_1\leq k_2&lt;\infty$ such that, for all sufficiently large $R$,</p>
<div class="math-display">$$\begin{gathered}
k_1R^{d-\alpha}\leq W_R\leq k_2R^{d-\alpha},\\
\frac{\beta k_1}{2}R^{d-\alpha}\leq\mathbb E[N_R\mid\mathcal F_R]\leq\beta k_2R^{d-\alpha},\\
e^{-\beta k_2R^{d-\alpha}}\leq\mathbb P(N_R=0\mid\mathcal F_R)\leq e^{-\beta k_1R^{d-\alpha}}.
\end{gathered}$$</div>
<p>Consequently the conditional probability of at least one direct edge tends uniformly to one when $\alpha&lt;d$, stays bounded away from both zero and one when $\alpha=d$, and is of order $R^{d-\alpha}$ when $\alpha&gt;d$. Averaging gives the same conclusions without conditioning.</p>
<p><em>Proof.</em> Conditional on $\mathcal F_R$, the unrevealed finite family still has its independent product law and the two selected sets are fixed. Since they are disjoint, each cross pair labels one distinct unordered bond. Multiplying closed-bond probabilities gives the exponential formula; summing opening probabilities gives the mean.</p>
<p>For $aR\geq r_0$, each summand of $W_R$ lies between $c(bR)^{-d-\alpha}$ and $C(aR)^{-d-\alpha}$. Multiply by $|A_R||B_R|$ to obtain the bounds with $k_1=c\rho^2b^{-d-\alpha}$ and $k_2=CM^2a^{-d-\alpha}$. For large $R$, all $\beta J(y-x)\leq1$; the inequalities $t/2\leq1-e^{-t}\leq t$ for $0\leq t\leq1$ give the mean bounds. The assertions about a direct connection follow from $1-e^{-\beta W_R}$ and the same scalar inequalities.</p>
<p>This makes the bulk-to-bulk count a conditional probability estimate. The sets may, for example, be clusters selected using edges internal to the two boxes. Selecting them after looking at their cross edges would invalidate the displayed conditional product law. Positive bulk density is a hypothesis; the result does not supply it for critical clusters, or identify the long-range/short-range universality threshold.</p>

## The marginal direct-edge count {#section-bulk-poisson}

<a id="tag-NIWS" data-assertion="theorem" data-title="A Poisson limit for direct edges between separated macroscopic sets at the marginal bulk exponent"></a>
<p>Let $d\geq1$ and suppose $J$ is symmetric, finite and nonnegative, with $J(z)|z|^{2d}\to c\in(0,\infty)$ as $|z|\to\infty$. Let $A,B\subset\mathbb R^d$ be bounded Jordan measurable sets of positive volume whose closures have positive distance. For fixed $\beta\geq0$, count the open bonds between $A_R=(RA)\cap\mathbb Z^d$ and $B_R=(RB)\cap\mathbb Z^d$. Then their number $N_R$ converges in total variation, as $R\to\infty$, to a Poisson variable of mean</p>
<div class="math-display">$$\lambda=\beta c\int_A\int_B|u-v|^{-2d}\,dv\,du.$$</div>
<p>In particular, $\mathbb P(N_R\geq1)\to1-e^{-\lambda}$.</p>
<p><em>Proof.</em> Positive separation keeps the integrand bounded and continuous on a neighbourhood of $\overline A\times\overline B$. The boundary sets have measure zero, so the lattice Riemann sums converge. The tail assumption is uniform over the cross displacements, giving</p>
<div class="math-display">$$W_R=\sum_{x\in A_R,y\in B_R}J(y-x)
=cR^{-2d}\sum_{x\in A_R,y\in B_R}|x/R-y/R|^{-2d}+o(1)
\longrightarrow c\int_A\int_B|u-v|^{-2d}\,dv\,du.$$</div>
<p>There are $O(R^{2d})$ cross pairs and their intensities are $O(R^{-2d})$. Thus, with $q_{xy}=1-e^{-\beta J(y-x)}$ and $\mu_R=\sum q_{xy}$,</p>
<div class="math-display">$$\sum q_{xy}^2=O(R^{-2d}),\qquad
0\leq\beta W_R-\mu_R\leq\frac{\beta^2}{2}\sum J(y-x)^2=O(R^{-2d}).$$</div>
<p>In particular $\mu_R\to\lambda$. To pass from means to distributions, couple a Bernoulli variable of parameter $q$ to a Poisson variable of mean $q$. The common mass of their laws at zero and one is</p>
<div class="math-display">$$(1-q)+qe^{-q}=1-q(1-e^{-q})\geq1-q^2.$$</div>
<p>They therefore admit a coupling that differs with probability at most $q^2$. Take such couplings independently for all cross pairs and sum. The original sum is $N_R$ and the Poisson sum has mean $\mu_R$, so their total-variation distance is at most $\sum q_{xy}^2$. Poisson laws with means $\mu_R$ and $\lambda$ can in turn be coupled by adding an independent Poisson variable of mean $|\mu_R-\lambda|$ to the smaller one; their distance is at most $|\mu_R-\lambda|$. Both bounds vanish.</p>
<p>The nontrivial marginal connection probability follows from the direct-edge law, independently of the state of edges inside the sets. This is a statement about dense macroscopic sets in $\mathbb Z^d$, not about the sizes or geometry of critical clusters. When $\beta=0$, both the count and its limiting Poisson mean are zero.</p>
