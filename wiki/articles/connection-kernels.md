---
{
  "id": "connection-kernels",
  "title": "Connection kernels and triangle bounds",
  "subtitle": "Cluster positivity and finite matrix restrictions",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The connection kernel is positive semidefinite. Finite restrictions give off-diagonal bounds, open-triangle decay and the first diagram comparison without an infinite-volume operator assumption.",
  "context": [
    "A random undirected graph on a nonempty countable set $V$.",
    "Every connection event is measurable; independence is not assumed.",
    "Connections use the full graph, with each vertex connected to itself."
  ],
  "related": [
    "connectivity",
    "susceptibility",
    "triangle-condition"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "perclib-connection-kernel",
    "perclib-train10-analysis-discreteconvolution",
    "hutchcroft-lrp-3"
  ],
  "aliases": [
    "positive semidefinite connection kernel",
    "cluster Gram representation",
    "off-diagonal triangle bound",
    "diagram comparison"
  ],
  "prototypeUses": [
    "triangle-condition"
  ]
}
---

## Positivity from the cluster partition {#section-positivity}

<p>Write $T(x,y)=\mathbb P(x\leftrightarrow y)$. Thus $T$ is symmetric, $0\leq T(x,y)\leq1$ and $T(x,x)=1$. These facts use only undirected connectivity, not a product law.</p>
<a id="tag-70KD" data-assertion="proposition" data-title="Positive semidefiniteness of the connection kernel"></a>
<p>For every finitely supported real family $(a_x)_{x\in V}$,</p>
<div class="math-display">$$\sum_{x,y\in V}a_xa_yT(x,y)=\mathbb E\!\left[\sum_C\left(\sum_{x\in C}a_x\right)^2\right]\geq0,$$</div>
<p>where $C$ ranges over the open clusters. Consequently every finite principal submatrix of $T$ is positive semidefinite.</p>
<p><em>Proof.</em> In each configuration, two vertices belong to the same cluster exactly when they are connected. Expanding the squares therefore gives</p>
<div class="math-display">$$\sum_C\left(\sum_{x\in C}a_x\right)^2=\sum_{x,y}a_xa_y\mathbf1_{\{x\leftrightarrow y\}}.$$</div>
<p>Only the finitely many clusters meeting the support of $a$ contribute. The right side is a finite sum of measurable random variables, so taking expectations proves the identity. In particular, no measurable enumeration of all clusters is needed.</p>

## Bounding open triangles {#section-triangles}

<p>Interpret all matrix sums as nonnegative sums, initially allowing infinity. Write</p>
<div class="math-display">$$T^2(x,y)=\sum_uT(x,u)T(u,y),\qquad T^3(x,y)=\sum_{u,v}T(x,u)T(u,v)T(v,y),\qquad \Delta_x=T^3(x,x).$$</div>
<p>The last expression is the rooted triangle diagram of <a href="/tag/67VP/">67VP</a>, here written for the present connection kernel.</p>
<a id="tag-UZ7J" data-assertion="proposition" data-title="Cubic connection bounds from finite diagonal triangles"></a>
<p>If $\Delta_x$ and $\Delta_y$ are finite, then</p>
<div class="math-display">$$T^3(x,y)\leq\sqrt{\Delta_x\Delta_y}&lt;\infty.$$</div>
<p>Also, for every $x$,</p>
<div class="math-display">$$\sum_uT(x,u)^2\leq\Delta_x,$$</div>
<p>as an inequality of nonnegative extended sums.</p>
<p><em>Proof.</em> For a finite set $F$ containing $x,y$, let $T_F=(T(u,v))_{u,v\in F}$. This is the restriction of the full connection kernel, not the kernel of the graph induced by $F$. By positivity, its eigenvalues are nonnegative, so $T_F^3$ is positive semidefinite. The Cauchy–Schwarz inequality for a positive semidefinite matrix gives</p>
<div class="math-display">$$\bigl(T_F^3(x,y)\bigr)^2\leq T_F^3(x,x)T_F^3(y,y).$$</div>
<p>Choose finite sets increasing to $V$. All entries of $T$ are nonnegative, so each of these cubic sums increases to its full counterpart. Passing to the limit proves the first claim, with a finite right side. For the second, retain just the terms $u=v$ in the defining double sum for $\Delta_x$ and use $T(u,u)=1$ and symmetry.</p>
<p>If a group acts transitively on $V$ and preserves $T$, then all $\Delta_x$ have the same value $\Delta$. Thus $\Delta&lt;\infty$ implies $T^3(x,y)\leq\Delta$ for every pair. This is a uniform bound, not a claim that $T^3(x,y)$ tends to zero when the vertices separate. The further argument giving open-triangle decay follows next.</p>

## Open-triangle decay {#section-localization}

<a id="tag-96A2" data-assertion="theorem" data-title="Open-triangle decay under a uniform triangle bound"></a>
<p>Suppose $D=\sup_x\Delta_x&lt;\infty$. For every fixed root $o$ and every $\varepsilon&gt;0$, there is a finite set $E\subseteq V$ such that</p>
<div class="math-display">$$T^3(o,x)&lt;\varepsilon\qquad(x\notin E).$$</div>
<p>If a group acts transitively on $V$, preserving both $T$ and a finite-valued metric $d$, then</p>
<div class="math-display">$$\lim_{r\to\infty}\ \sup_{d(u,v)\geq r}T^3(u,v)=0,$$</div>
<p>with the supremum of an empty set taken to be zero. In this case the uniform hypothesis is simply $\Delta_o&lt;\infty$ at one root.</p>
<p><em>Proof.</em> The quadratic bound above gives $\sum_vT(u,v)^2\leq D$ for every $u$. In particular $T(u,x)$ tends to zero outside finite sets. The same is true of $T^2(u,x)$: for a finite set $K$, Cauchy–Schwarz gives</p>
<div class="math-display">$$T^2(u,x)\leq\sum_{v\in K}T(u,v)T(v,x)+\sqrt D\left(\sum_{v\notin K}T(u,v)^2\right)^{1/2}.$$</div>
<p>First choose $K$ to make the second term small, then send $x$ outside a finite set to make every term in the finite sum small.</p>
<p>Fix $o$. For finite $F\subseteq V$, put</p>
<div class="math-display">$$R_F=\sum_{u,v\notin F}T(o,u)T(u,v)T(v,o).$$</div>
<p>As $F$ increases to $V$, $R_F\to0$, since this is a tail of the finite nonnegative sum $\Delta_o$. Positivity of $T$ yields the more useful one-sided tail estimate</p>
<div class="math-display">$$\sum_{u\notin F,\ v\in V}T(o,u)T(u,v)T(v,x)\leq\sqrt{R_F\Delta_x}\leq\sqrt{D R_F}.$$</div>
<p>To justify it, restrict to any finite set $H$ and apply Cauchy–Schwarz for the positive semidefinite matrix $T_H$ to the vectors $a_u=\mathbf1_{\{u\notin F\}}T(o,u)$ and $b_u=T(x,u)$, indexed by $H$. Their quadratic forms are bounded by $R_F$ and $\Delta_x$. Exhausting $V$ by $H$ proves the inequality by nonnegative summation; no bounded operator on $\ell^2(V)$ is assumed.</p>
<p>Splitting the first intermediate vertex according to membership in $F$ now gives</p>
<div class="math-display">$$T^3(o,x)\leq\sum_{u\in F}T(o,u)T^2(u,x)+\sqrt{D R_F}.$$</div>
<p>Choose $F$ to make the remainder less than $\varepsilon/2$. Each term in the finite sum tends to zero outside finite sets, so the sum is less than $\varepsilon/2$ outside a suitable finite set $E$. This proves the first claim. Under the transitive isometric action, every pair $(u,v)$ can be carried to $(o,x)$ with $d(o,x)=d(u,v)$. Choose $r$ larger than all distances from $o$ to points of $E$. The same bound then holds for every pair at distance at least $r$.</p>
<p>This supplies the decay of the three-link quantity needed for open-triangle localization. For a connected transitive graph one may take graph distance. No finite-susceptibility or unimodularity assumption is needed. If $T_\beta\leq T_{\beta_c}$ entrywise for $\beta\leq\beta_c$, the nonnegative cubic sums satisfy the same inequality, so a separation scale chosen at criticality also works uniformly below criticality. The subsequent cluster-coupling and path-surgery estimates are separate assertions.</p>

## The first diagram comparison {#section-comparison}

<a id="tag-C2YT" data-assertion="proposition" data-title="The first triangle-diagram comparison under a uniform diagonal bound"></a>
<p>Suppose $D=\sup_x\Delta_x&lt;\infty$. For a root $o$, define</p>
<div class="math-display">$$A_o=\sum_vT(o,v)T^2(o,v)T^3(o,v).$$</div>
<p>Then all the displayed kernel entries are finite and</p>
<div class="math-display">$$A_o\leq D\Delta_o\leq D^2.$$</div>
<p>In the transitive invariant case this gives $A_o\leq\Delta^2$.</p>
<p><em>Proof.</em> Retaining $v=y$ in the cubic sum shows $T^2(x,y)\leq T^3(x,y)$, since $T(y,y)=1$. The preceding bound therefore makes both entries finite and gives $T^3(o,v)\leq D$. Symmetry and rearrangement of nonnegative sums give</p>
<div class="math-display">$$A_o\leq D\sum_vT(o,v)T^2(o,v)=D\sum_{v,u}T(o,v)T(v,u)T(u,o)=D\Delta_o.$$</div>
<p>This is the first half of the diagram comparison. The proof requires neither independent edges nor unimodularity. The second comparison is proved below under group invariance and finite susceptibility; those assumptions are not needed for the first comparison.</p>
<p>One sufficient condition for the uniform hypothesis is $\sup_x\sum_yT(x,y)\leq M&lt;\infty$. Indeed, $T(v,x)\leq1$ gives</p>
<div class="math-display">$$\Delta_x\leq\sum_uT(x,u)\sum_vT(u,v)\leq M^2.$$</div>
<p>This sufficient condition is stronger than the finite-triangle hypothesis and is not substituted for it. In particular, the finite-restriction argument above remains applicable when susceptibility is infinite but every diagonal triangle is finite with a uniform bound.</p>

## A finite matrix comparison {#section-matrix-comparison}

<p>For matrices of the same size, write $S\circ R$ for their entrywise product. This notation is distinct from ordinary matrix multiplication.</p>
<a id="tag-CS16" data-assertion="proposition" data-title="Entrywise comparison of powers of a positive semidefinite matrix"></a>
<p>If $S$ is a finite real symmetric positive semidefinite matrix, then</p>
<div class="math-display">$$S^2\circ S^2\preceq S\circ S^3,$$</div>
<p>where $\preceq$ denotes positive semidefinite order, not entrywise order.</p>
<p><em>Proof.</em> Choose an orthonormal eigenbasis $u_i$ with eigenvalues $\lambda_i\geq0$. Put $w_{ij}=u_i\circ u_j$, the vector of coordinatewise products. Expanding both matrix powers in this basis and pairing the terms indexed by $(i,j)$ and $(j,i)$ gives</p>
<div class="math-display">$$S\circ S^3-S^2\circ S^2=\frac12\sum_{i,j}\lambda_i\lambda_j(\lambda_i-\lambda_j)^2\,w_{ij}w_{ij}^{\mathsf T}.$$</div>
<p>Every summand is positive semidefinite. This proves the comparison without an entrywise positivity assumption on $S$.</p>

## The second diagram comparison on a group {#section-group-comparison}

<a id="tag-87W3" data-assertion="theorem" data-title="Second triangle-diagram comparison for a group-invariant connection kernel"></a>
<p>Suppose the vertex set is a countable group $G$, with identity $o$, and the connection kernel is invariant under simultaneous left translation:</p>
<div class="math-display">$$T(gx,gy)=T(x,y)\qquad(g,x,y\in G).$$</div>
<p>Assume $\chi=\sum_yT(o,y)&lt;\infty$. With $A_o$ as above, define</p>
<div class="math-display">$$B_o=\sum_v\bigl(T^2(o,v)\bigr)^3.$$</div>
<p>Then $B_o\leq A_o$. Combined with the first diagram comparison, this gives $B_o\leq A_o\leq\Delta_o^2$ under these assumptions.</p>
<p><em>Proof.</em> Translation invariance makes every row sum of $T$ equal to $\chi$, and symmetry gives the same column sums. For a finitely supported vector $f$, weighted Cauchy–Schwarz gives</p>
<div class="math-display">$$\sum_x\left|\sum_yT(x,y)f(y)\right|^2\leq\chi\sum_{x,y}T(x,y)|f(y)|^2=\chi^2\|f\|_2^2.$$</div>
<p>Thus $T$ extends to a bounded self-adjoint operator on $\ell^2(G)$. Its positivity follows from the cluster quadratic form. Nonnegative summation gives row sums $\chi^n$ for $T^n$. Since $T(x,y)\leq1$, it also gives $T^2(x,y)\leq\chi$ and $T^3(x,y)\leq\chi^2$.</p>
<p>Set $H=T\circ T^3-T^2\circ T^2$. Both entrywise products have row and column sums bounded by $\chi^3$, so their difference is a bounded self-adjoint operator by the same row-and-column estimate. To see that $H$ is positive, exhaust $G$ by finite sets $F$. Apply the finite matrix comparison to $T_F$. The entries of $T_F^2$ and $T_F^3$ converge to those of $T^2$ and $T^3$, respectively, by nonnegative summation. For every finitely supported $a$, the resulting finite quadratic forms therefore converge to $\langle a,Ha\rangle\geq0$. Boundedness extends this inequality to all of $\ell^2(G)$.</p>
<p>For a bounded matrix $M$ invariant under simultaneous left translation, define $\operatorname{tr}_o(M)=M(o,o)$. If $M,N$ are two such matrices, their product's diagonal series is absolutely convergent by Cauchy–Schwarz. Translation by $x^{-1}$ and reindexing give</p>
<div class="math-display">$$\begin{aligned}\operatorname{tr}_o(MN)&=\sum_x M(o,x)N(x,o)\\&=\sum_x M(x^{-1},o)N(o,x^{-1})=\operatorname{tr}_o(NM).\end{aligned}$$</div>
<p>All ordinary and entrywise products used here retain the invariance. Applying this trace identity with $M=HT$ and $N=T$ gives</p>
<div class="math-display">$$\operatorname{tr}_o(HT^2)=\operatorname{tr}_o(THT)=\langle T\delta_o,H T\delta_o\rangle\geq0.$$</div>
<p>By symmetry of $T^2$, the left side is exactly $A_o-B_o$. These sums are finite: each is at most $\chi^4$, using the row and pointwise bounds above. This proves $B_o\leq A_o$. Finally $\Delta_x\leq\chi^2$ for every $x$, and translation invariance makes the diagonal constant, so the first comparison applies.</p>
<p>This proves the second step of the diagram comparison for countable groups with translation-invariant connection kernels and finite susceptibility. A more general unimodular-graph statement uses the invariant trace supplied below, under an explicit mass-transport assumption. Neither the finite matrix comparison nor positivity of $H$ asserts a pointwise inequality between their entries.</p>

## The unimodular trace {#section-unimodular}

<a id="tag-N0HM" data-assertion="definition" data-title="The mass-transport property of a transitive action"></a>
<p>Let a group $\Gamma$ act transitively on the countable vertex set $V$, and fix $o\in V$. The action has the mass-transport property if every diagonally invariant function $F:V\times V\to[0,\infty]$, meaning $F(gx,gy)=F(x,y)$, satisfies</p>
<div class="math-display">$$\sum_{v\in V}F(o,v)=\sum_{v\in V}F(v,o).$$</div>
<p>The sums may be infinite. This is the form of unimodularity used below. It is an additional assumption on the action; transitivity alone does not imply it.</p>

<a id="tag-IZAO" data-assertion="theorem" data-title="Triangle-diagram comparison under the mass-transport property"></a>
<p>Suppose the connection kernel $T$ is invariant under a transitive action with the mass-transport property, and $\chi=\sum_vT(o,v)&lt;\infty$. With</p>
<div class="math-display">$$\Delta=T^3(o,o),\qquad A=\sum_vT(o,v)T^2(v,o)T^3(o,v),\qquad B=\sum_v\bigl(T^2(o,v)\bigr)^3,$$</div>
<p>one has $B\leq A\leq\Delta^2$.</p>
<p><em>Proof.</em> Invariance and transitivity make all row sums of $T$ equal to $\chi$. The row-and-column estimate and finite principal-matrix argument used above therefore apply unchanged: $T$ is a bounded positive operator, and $H=T\circ T^3-T^2\circ T^2$ is bounded and positive. Those arguments use neither a group structure on $V$ nor a trace.</p>
<p>For invariant bounded real operators $M,N$, the series $\sum_vM(o,v)N(v,o)$ is absolutely convergent by Cauchy–Schwarz on the square-summable row and column. The function $F(x,y)=M(x,y)N(y,x)$ is diagonally invariant. Apply mass transport to its positive and negative parts; absolute convergence allows subtraction and gives</p>
<div class="math-display">$$\operatorname{tr}_o(MN)=\sum_vM(o,v)N(v,o)=\sum_vM(v,o)N(o,v)=\operatorname{tr}_o(NM).$$</div>
<p>Ordinary and entrywise products retain invariance. Taking $M=HT$ and $N=T$ now gives</p>
<div class="math-display">$$A-B=\operatorname{tr}_o(HT^2)=\operatorname{tr}_o(THT)=\langle T\delta_o,H T\delta_o\rangle\geq0.$$</div>
<p>The series defining $A$ and $B$ are finite by the same $\chi^4$ bounds as in the group case. Transitivity also makes the diagonal triangle constant, so the first comparison gives $A\leq\Delta^2$.</p>
<p>This gives the unimodular-graph comparison under an explicit mass-transport hypothesis. The regular action of a countable group is the earlier special case, where inversion gives the trace identity directly. Independence of bonds is unnecessary for this diagram comparison; the connection kernel's positivity comes from the cluster partition.</p>

## Finite quadratic forms in the source {#section-kernel-source}

<p>The source proves the product-law case of <a href="/tag/70KD/">70KD</a> for an arbitrary finite indexed family of vertices, allowing repeated vertices and signed real weights. In each configuration, group the indices by their open component. The quadratic form is the sum of the squared total weights in those groups. Only finitely many groups contribute, even if the graph has infinitely many components. Countability is used when taking expectations of connection indicators; the pointwise identity needs no countability.</p>
<p>For the triangle bound, the source avoids spectral powers altogether. On a finite set $F$, write</p>
<div class="math-display">$$\langle a,b\rangle_F=\sum_{u,v\in F}a_u b_vT(u,v).$$</div>
<p>Positivity of $\langle a+tb,a+tb\rangle_F$ for every real $t$ gives $\langle a,b\rangle_F^2\leq\langle a,a\rangle_F\langle b,b\rangle_F$, including a zero diagonal form. Take $a_u=T(x,u)$ and $b_u=T(u,y)$. The mixed form is the truncated cubic sum, and the two diagonal forms are bounded by $\Delta_x$ and $\Delta_y$. Every finite set of pairs $(u,v)$ lies in some $F\times F$, so taking the supremum over finite sums gives</p>
<div class="math-display">$$T^3(x,y)^2\leq\Delta_x\Delta_y$$</div>
<p>as an extended nonnegative inequality. This step assumes neither finite susceptibility nor a bounded infinite matrix operator. Finite diagonal triangles give the real square-root formulation of <a href="/tag/UZ7J/">UZ7J</a>. The diagonal bubble bound follows just by retaining $u=v$; its source export needs no countability.</p>
<p>The weighted bound <a href="/tag/C2YT/">C2YT</a> is likewise first proved with $D=\sup_x\Delta_x$ allowed to be infinite, then specialized to finite $D$. Its regrouping identity uses nonnegative sums and symmetry. The <a href="/coverage/sources/perclib-22d8485-geometry/">sixteen-contract inventory</a> records these distinctions. Although the partition argument works for the article's general random graph, the probabilistic source exports use the independent bond law. They do not yet supply the open-triangle decay or second diagram comparison elsewhere in this article.</p>


## A lower bound from isolated vertices {#section-singleton-lower}

<a id="tag-R1HO" data-assertion="proposition" data-title="Uniform kernel positivity from singleton probabilities"></a>
<p>For the random graph of this article, put $p_x=\mathbb P(K_x=\{x\})$. Every finitely supported real vector $f$ satisfies</p>
<div class="math-display">$$\sum_{x,y}f(x)T(x,y)f(y)\geq\sum_xp_xf(x)^2.$$</div>
<p>In particular, if $p_x\geq\delta&gt;0$ for every $x$, then $T\succeq\delta I$ as a quadratic form. For independent bonds with probabilities $1-e^{-\beta J(x,y)}$, finite $\beta\geq0$, and $\sup_x\sum_{y\ne x}J(x,y)\leq L&lt;\infty$, one may take $\delta=e^{-\beta L}$.</p>
<p><em>Proof.</em> In the cluster-square identity <a href="/tag/70KD/">70KD</a>, retain just the singleton clusters. Every discarded term is a square. Under the product law, a vertex is isolated exactly when all its incident bonds are closed. Finite intersections have probability $\exp(-\beta\sum_{y\in F}J(x,y))$; continuity from above along an exhaustion gives $p_x=\exp(-\beta\sum_{y\ne x}J(x,y))\geq e^{-\beta L}$.</p>
<p>This is a lower quadratic-form bound, even when $T$ is not a bounded operator. If $T$ is bounded on $\ell^2(V)$, density extends it to all vectors and the bounded self-adjoint spectral theorem gives a bounded inverse with $\|T^{-1}\|\leq\delta^{-1}$. The uniform constant matters: the diagonal matrix $D(n,n)=1/n$ on the positive integers has a strictly positive minimum eigenvalue on every finite principal submatrix, but no common positive lower bound. Finite principal matrices characterize positive semidefiniteness; they characterize a bound $T\succeq\delta I$ only when the same $\delta$ works for all of them.</p>

## Schur products and bounded operators {#section-schur}

<p>Here a real symmetric matrix is positive semidefinite when its quadratic form is nonnegative on finitely supported vectors. Boundedness is a separate condition. For a bounded operator $S$ on $\ell^2(V)$, its matrix entry is $S(x,y)=\langle\delta_x,S\delta_y\rangle$; $S^*$ denotes its adjoint.</p>
<a id="tag-TAB8" data-assertion="theorem" data-title="Schur positivity and the operator norm of an entrywise product"></a>
<p>If $S,T$ are positive semidefinite matrices on a countable set, then $S\circ T$ is positive semidefinite. No boundedness is needed for this claim. If instead $S,T$ are arbitrary bounded real operators, their entrywise product defines a bounded operator and</p>
<div class="math-display">$$\|S\circ T\|\leq\|S\|\,\|T\|.$$</div>
<p><em>Proof.</em> On any finite index set, write the two positive matrices as Gram matrices $S(x,y)=\langle a_x,a_y\rangle$ and $T(x,y)=\langle b_x,b_y\rangle$. Then $S(x,y)T(x,y)=\langle a_x\otimes b_x,a_y\otimes b_y\rangle$, another Gram matrix. Each finitely supported quadratic form lies in one such finite restriction, proving the countable assertion.</p>
<p>For the norm bound, let $U:\ell^2(V)\to\ell^2(V\times V)$ be the isometry $U\delta_x=\delta_x\otimes\delta_x$. The bounded tensor product satisfies $\|S\otimes T\|\leq\|S\|\|T\|$, and its compression obeys</p>
<div class="math-display">$$U^*(S\otimes T)U(x,y)=S(x,y)T(x,y).$$</div>
<p>For completeness, the tensor norm bound follows by writing $S\otimes T=(S\otimes I)(I\otimes T)$. Each factor acts on the corresponding square-summable slices and has norm at most the norm of that operator. Compression by an isometry cannot increase the norm.</p>
<p>A useful independent boundedness criterion is the row-and-column estimate. If $r=\sup_x\sum_y|M(x,y)|&lt;\infty$ and $c=\sup_y\sum_x|M(x,y)|&lt;\infty$, weighted Cauchy–Schwarz gives, for finitely supported $f$,</p>
<div class="math-display">$$\sum_x\left|\sum_yM(x,y)f(y)\right|^2\leq r\sum_{x,y}|M(x,y)|\,|f(y)|^2\leq rc\|f\|_2^2.$$</div>
<p>Thus $\|M\|\leq\sqrt{rc}$. This supplies the operator estimate used earlier without interpolation. For any bounded $M,N$, the series for $(MN)(x,y)$ is absolutely convergent, since it pairs an $\ell^2$ row of $M$ with an $\ell^2$ column of $N$.</p>

## Positive block matrices {#section-block-matrices}

<a id="tag-530W" data-assertion="proposition" data-title="Schur complements and equal-diagonal block matrices"></a>
<p>Let $S,T$ be bounded self-adjoint real operators on $\ell^2(V)$, let $X$ be bounded, and suppose $T\succeq\delta I$ for some $\delta&gt;0$. Then</p>
<div class="math-display">$$\begin{pmatrix}S&amp;X\\X^*&amp;T\end{pmatrix}\succeq0
\quad\Longleftrightarrow\quad S-XT^{-1}X^*\succeq0.$$</div>
<p>For arbitrary symmetric matrices $A,B$, without a boundedness assumption,</p>
<div class="math-display">$$\begin{pmatrix}A&amp;B\\B&amp;A\end{pmatrix}\succeq0
\quad\Longleftrightarrow\quad A+B\succeq0\text{ and }A-B\succeq0.$$</div>
<p>More generally, for any real $\delta$, that block matrix is at least $\delta I$ if and only if both $A+B$ and $A-B$ are at least $\delta I$.</p>
<p><em>Proof.</em> The first block quadratic form at $(f,g)$ equals</p>
<div class="math-display">$$\langle f,(S-XT^{-1}X^*)f\rangle+
\left\|T^{1/2}\bigl(g+T^{-1}X^*f\bigr)\right\|_2^2.$$</div>
<p>This proves sufficiency. For necessity, choose $g=-T^{-1}X^*f$. That vector need not have finite support, but boundedness extends positivity from finitely supported pairs to every pair in $\ell^2(V)\oplus\ell^2(V)$, so the choice is legitimate. For the second statement, the orthogonal change of variables $(f,g)\mapsto((f+g)/\sqrt2,(f-g)/\sqrt2)$ turns the form into the sum of the forms of $A+B$ and $A-B$. This change preserves finite support and the squared norm, giving both assertions including the common lower bound.</p>
<p>The inverse in the first statement requires the uniform lower bound on $T$. It cannot be used merely because $T$ is positive semidefinite. The next argument treats that case without an inverse.</p>

## Ando's comparison without invertibility {#section-ando}

<a id="tag-0FTH" data-assertion="theorem" data-title="Ando comparison for commuting bounded positive operators"></a>
<p>Let $S,T$ be commuting bounded positive semidefinite real operators on $\ell^2(V)$, where $V$ is countable. Then $ST$ is positive, its positive square root $R=(ST)^{1/2}$ satisfies</p>
<div class="math-display">$$R\circ R\preceq S\circ T,$$</div>
<p>and both sides are bounded operators. In particular, every bounded positive operator $T$ satisfies $T^2\circ T^2\preceq T\circ T^3$, with no entrywise nonnegativity assumption.</p>
<p><em>Proof.</em> We use the bounded self-adjoint spectral theorem for positive square roots. Polynomial approximation to the square-root function shows that an operator commuting with a positive operator also commutes with its positive square root. Thus $S^{1/2}$ and $T^{1/2}$ commute. Their product is positive: for example, $S^{1/2}T^{1/2}=T^{1/4}S^{1/2}T^{1/4}$. Its square is $ST$, so uniqueness of the positive square root gives $R=S^{1/2}T^{1/2}$.</p>
<p>The two block matrices</p>
<div class="math-display">$$P=\begin{pmatrix}S&amp;R\\R&amp;T\end{pmatrix},\qquad
Q=\begin{pmatrix}T&amp;R\\R&amp;S\end{pmatrix}$$</div>
<p>are positive: their quadratic forms are respectively $\|S^{1/2}f+T^{1/2}g\|_2^2$ and $\|T^{1/2}f+S^{1/2}g\|_2^2$. By <a href="/tag/TAB8/">Schur positivity</a>,</p>
<div class="math-display">$$P\circ Q=\begin{pmatrix}S\circ T&amp;R\circ R\\R\circ R&amp;S\circ T\end{pmatrix}\succeq0.$$</div>
<p>Evaluate this form at $(f,-f)$ to obtain $S\circ T-R\circ R\succeq0$. The Schur norm bound gives boundedness. Finally apply the comparison to $S=T$ and the second operator $T^3$; the positive square root of $T^4$ is $T^2$.</p>
<p>This supplies the full bounded-operator form of the finite comparison <a href="/tag/CS16/">CS16</a>. Singular operators, including the zero operator, are allowed. The argument uses positive square roots, not an assertion that $T^a\to I$ as $a\downarrow0$ for every positive semidefinite $T$. With the usual convention $T^0=I$, that last assertion fails on a nonzero kernel.</p>

## Invariant square roots {#section-invariant-roots}

<a id="tag-Z4JP" data-assertion="proposition" data-title="Invariance and norm of the positive square root"></a>
<p>Let a group act by permutations of a countable set $V$. If a bounded positive operator $T$ has invariant matrix entries, then $T^{1/2}$ has invariant entries also, and $\|T^{1/2}\|=\|T\|^{1/2}$.</p>
<p><em>Proof.</em> A permutation $g$ acts unitarily by $U_gf(x)=f(g^{-1}x)$. Invariance says $U_gTU_g^{-1}=T$. The conjugate $U_gT^{1/2}U_g^{-1}$ is positive and its square is $T$; uniqueness of the positive square root identifies it with $T^{1/2}$. The norm identity follows from the spectral theorem. Neither transitivity nor mass transport is needed.</p>
<p>The exponent $1/2$ in the norm identity is essential. For $T=I/4$, the square root has norm $1/2$, while $\|T\|^2=1/16$. This corrects the intermediate norm bound in the source proof without changing the invariance conclusion.</p>

## A faithful invariant trace {#section-faithful-trace}

<p>For the next two statements assume a transitive action with the <a href="/tag/N0HM/">mass-transport property</a>. Let $\mathcal A$ be the bounded real operators with invariant matrix entries, and put $\operatorname{tr}_o(M)=\langle\delta_o,M\delta_o\rangle$.</p>
<a id="tag-AKHL" data-assertion="theorem" data-title="The root diagonal is a faithful tracial state"></a>
<p>The algebra $\mathcal A$ is closed under adjoints, ordinary products and entrywise products. Its positive elements have their positive square roots in $\mathcal A$. The functional $\operatorname{tr}_o$ is linear, independent of the root, and satisfies</p>
<div class="math-display">$$\operatorname{tr}_o(I)=1,\qquad
\operatorname{tr}_o(MN)=\operatorname{tr}_o(NM),\qquad
\operatorname{tr}_o(MM^*)=\sum_v|M(o,v)|^2\geq0.$$</div>
<p>The last quantity vanishes if and only if $M=0$.</p>
<p><em>Proof.</em> Invariant operators are exactly those commuting with every $U_g$. This proves closure under adjoints and ordinary products. Entrywise multiplication preserves invariance and is bounded by <a href="/tag/TAB8/">TAB8</a>; square-root closure is <a href="/tag/Z4JP/">Z4JP</a>. Linearity, root independence and normalization follow from the definition and transitivity.</p>
<p>For cyclicity, $F(x,y)=M(x,y)N(y,x)$ is invariant. Cauchy–Schwarz gives</p>
<div class="math-display">$$\sum_v|F(o,v)|\leq\|M^*\delta_o\|_2\|N\delta_o\|_2&lt;\infty.$$</div>
<p>Mass transport applied to $|F|$ makes the incoming absolute sum finite too. Applying it separately to the positive and negative parts and subtracting gives $\operatorname{tr}_o(MN)=\operatorname{tr}_o(NM)$. The displayed square-sum identity follows by matrix multiplication. If it is zero, the root row is zero; transitivity makes every row zero. Conversely $M=0$ plainly gives zero trace.</p>
<p>For positive $T\in\mathcal A$, the identity with $M=T^{1/2}$ gives $\operatorname{tr}_o(T)\geq0$, with equality only for $T=0$. Also $|\operatorname{tr}_o(M)|\leq\|M\|$. These facts explain the words <em>faithful tracial state</em> in the statement; no summation of all diagonal entries is intended.</p>

<a id="tag-F77F" data-assertion="proposition" data-title="Positive products have nonnegative invariant trace"></a>
<p>If $S,T\in\mathcal A$ are positive, then $\operatorname{tr}_o(ST)\geq0$. Consequently $S\preceq T$ implies $\operatorname{tr}_o(SX)\leq\operatorname{tr}_o(TX)$ for every positive $X\in\mathcal A$ and self-adjoint $S,T\in\mathcal A$.</p>
<p><em>Proof.</em> Cyclicity and invariant square roots give</p>
<div class="math-display">$$\operatorname{tr}_o(ST)=\operatorname{tr}_o(S^{1/2}TS^{1/2})
=\bigl\|T^{1/2}S^{1/2}\delta_o\bigr\|_2^2\geq0.$$</div>
<p>Apply this to the positive pair $T-S,X$ for the second claim. Commutativity of $S,T$ is not assumed; their product need not itself be self-adjoint.</p>

## Passing the diagram comparison to a critical endpoint {#section-diagram-limits}

<a id="tag-QGQ1" data-assertion="theorem" data-title="Monotone limits of the invariant triangle-diagram comparison"></a>
<p>Suppose $T_n$ are connection kernels invariant under the same transitive mass-transport action, with $\sum_vT_n(o,v)&lt;\infty$ for each $n$, and $T_n(x,y)\uparrow T(x,y)$ for every pair. Define $\Delta,A,B$ from $T$ by the nonnegative sums in <a href="/tag/IZAO/">IZAO</a>. Then, as extended nonnegative inequalities,</p>
<div class="math-display">$$B\leq A\leq\Delta^2.$$</div>
<p>In particular, if $\Delta&lt;\infty$, then both diagrams are finite, even if the row sum of $T$ is infinite.</p>
<p><em>Proof.</em> IZAO gives $B_n\leq A_n\leq\Delta_n^2$ for every $n$. Expand each diagram into its multiple sum of products of entries. Every factor is nonnegative and nondecreasing in $n$. Monotone convergence therefore gives $B_n\uparrow B$, $A_n\uparrow A$ and $\Delta_n\uparrow\Delta$. Passing to the limit proves the result, without subtracting divergent diagrams or treating $T$ as a bounded operator.</p>
<p>For independent intensity percolation, this applies at the critical parameter on a countable transitive weighted graph with $0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty$ and a weight-preserving mass-transport action. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness argument</a> gives finite susceptibility at every finite subcritical intensity, including when $\beta_c=\infty$.</p>
<p>To check the limit of the kernels, couple the models with independent uniforms $U_e$ and declare $e$ open at $\beta$ when $U_e&lt;1-e^{-\beta J(e)}$. If $\beta_n\uparrow b&lt;\infty$, then every edge open at $b$ is open at some $\beta_n$. A connection has a finite path witness, so it occurs at some $\beta_n$ as well. Thus the connection events increase to those at $b$. If $b=\infty$, every positive-intensity edge is eventually open almost surely; countability makes this simultaneous, and the same finite-path argument gives the connection kernel of the positive-intensity support graph. Take $b=\beta_c$ and a subcritical sequence. At intensity zero the kernel is $I$, and all three rooted diagrams equal one.</p>
<p>The finite-row and mass-transport hypotheses enter before the limit. This result does not assert the second comparison for an arbitrary invariant kernel of infinite row sum without such an approximation. The positive-square-root and matrix arguments above, together with this endpoint passage, supply the mathematical ingredients of Appendix A of <a href="https://arxiv.org/html/2106.06400v3#A1">the triangle paper</a>. The bounded self-adjoint spectral theorem remains a standard functional-analytic input. The <a href="/errata/hutchcroft-triangle-2021/">source errata</a> distinguish the repaired intermediate statements from the unchanged diagram theorem.</p>


## Fourier comparison on the lattice and hierarchical group {#section-fourier-diagrams}

<p>There is also a scalar proof on the two abelian groups used in the triangle paper. Let either $G=\mathbb Z^d$, $d\geq1$, or $G=\bigoplus_{j\geq1}(\mathbb Z/L\mathbb Z)^d$, $L\geq2$. Their compact dual groups are respectively</p>
<div class="math-display">$$K=(\mathbb R/2\pi\mathbb Z)^d
\quad\text{and}\quad K=\prod_{j\geq1}(\mathbb Z/L\mathbb Z)^d.$$</div>
<p>Write $\mu$ for normalized Haar measure: normalized Lebesgue measure in the first case and product uniform measure in the second. The character associated to $z\in K$ is $\gamma_z(x)=e^{iz\cdot x}$ on $\mathbb Z^d$, and</p>
<div class="math-display">$$\gamma_z(x)=\exp\!\left(\frac{2\pi i}{L}\sum_{j\geq1}z_j\cdot x_j\right)$$</div>
<p>on the hierarchical group. The last sum is finite because $x$ has finite support; $z$ need not. Restricting a character to each coordinate group identifies the hierarchical dual with this product, with its product topology. In particular, the discrete direct sum is not its own compact dual.</p>

<a id="tag-F77A" data-assertion="theorem" data-title="Fourier identities and triangle comparison on Euclidean and hierarchical groups"></a>
<p>Let $T(x,y)=\tau(y-x)$ be a translation-invariant connection kernel on either group, with $\chi=\sum_x\tau(x)&lt;\infty$. Define $f(z)=\sum_x\tau(x)\gamma_z(x)$, and let $*$ on $K$ denote convolution with respect to $\mu$. Then $f$ is continuous, real, even and nonnegative, and</p>
<div class="math-display">$$\Delta=\int_K f^3\,d\mu,\qquad
A=(f*f^2*f^3)(0),\qquad B=(f^2*f^2*f^2)(0),\qquad
B\leq A\leq\Delta^2.$$</div>
<p>The powers of $f$ here are pointwise powers, while the stars are convolution. The definitions of $A,B,\Delta$ are those of IZAO.</p>
<p><em>Proof.</em> Absolute summability makes the Fourier series uniformly convergent. The symmetry $\tau(-x)=\tau(x)$ makes its sum real and even. To prove nonnegativity directly, take $F_n=[-n,n]^d\cap\mathbb Z^d$ in the lattice case and the subgroup consisting of the first $n$ coordinates in the hierarchical case. Positivity of the connection matrix gives</p>
<div class="math-display">$$0\leq\frac1{|F_n|}\sum_{x,y\in F_n}\tau(y-x)\overline{\gamma_z(x)}\gamma_z(y)
=\sum_u\tau(u)\gamma_z(u)\frac{|F_n\cap(F_n-u)|}{|F_n|}.$$</div>
<p>The real quadratic-form inequality <a href="/tag/70KD/">70KD</a> applies to complex coefficients by splitting them into real and imaginary parts; the mixed terms cancel by symmetry. For each fixed $u$, the overlap ratio tends to one, and it always lies in $[0,1]$. Summability of $\tau$ therefore makes the last sum converge uniformly to $f(z)$, proving $f\geq0$.</p>
<p>The elementary character identity</p>
<div class="math-display">$$\int_K\gamma_z(x)\,d\mu(z)=\mathbf1_{\{x=0\}}$$</div>
<p>follows by integrating one nontrivial coordinate when $x\ne0$. It gives Fourier inversion and the product/convolution identities by expansion and Fubini. All these expansions are absolutely convergent: the discrete convolutions $\tau^{*j}$ have total mass $\chi^j$, and the dual measure has total mass one. In particular, $\widehat{\tau^{*j}}=f^j$, the zero coefficient of $f^3$ is $\Delta$, and convolution of the three Fourier series gives</p>
<div class="math-display">$$\begin{aligned}
(f*f^2*f^3)(0)&amp;=\sum_x\tau(x)\tau^{*2}(x)\tau^{*3}(x)=A,\\
(f^2*f^2*f^2)(0)&amp;=\sum_x\bigl(\tau^{*2}(x)\bigr)^3=B.
\end{aligned}$$</div>
<p>Hölder's inequality and translation invariance of $\mu$ give, for every $z\in K$,</p>
<div class="math-display">$$(f*f^2)(z)\leq
\left(\int_Kf^3\,d\mu\right)^{1/3}
\left(\int_Kf^3\,d\mu\right)^{2/3}=\Delta.$$</div>
<p>Convolving with $f^3$ and evaluating at zero proves $A\leq\Delta^2$. For the other inequality, Cauchy–Schwarz gives</p>
<div class="math-display">$$\begin{aligned}
(f^2*f^2)(z)
&amp;\leq\left[\int_Kf(u)f(z-u)^3\,d\mu(u)\right]^{1/2}
\left[\int_Kf(u)^3f(z-u)\,d\mu(u)\right]^{1/2}\\
&amp;=(f*f^3)(z).
\end{aligned}$$</div>
<p>The two integrals are equal by the substitution $u\mapsto z-u$. Convolution with the nonnegative function $f^2$ preserves this inequality and gives $B\leq A$ at zero.</p>
<p>This proves the Fourier route in Section 2 using counting measure on $G$ and probability Haar measure on $K$. The constant transform of the point mass at zero is therefore integrable on $K$; using counting measure on the hierarchical direct sum would lose this property. The existing <a href="/errata/hutchcroft-triangle-2021/#hierarchical-fourier-dual">dual-group erratum</a> records that distinction. For critical kernels without finite susceptibility, use the nonnegative diagram limit QGQ1 rather than asserting convergence of these Fourier series.</p>


## The source's group-kernel scope {#section-group-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-matrices/">new matrix inventory</a> separates three implementations from the more general results above. The finite Hadamard source follows the eigenvector expansion in CS16 for every real symmetric matrix, then uses nonnegative eigenvalues to obtain positive semidefiniteness. It imposes no entrywise sign condition and includes the zero matrix.</p>
<p>The trace source works on a group with left-invariant kernels, without requiring the group to be countable. Translation and inversion give $M(v,o)=M(o,v^{-1})$ and reindex the two trace sums. Its formal sum identity does not require summability; to interpret it as an absolutely convergent trace series, the source separately uses</p>
<div class="math-display">$$2|M(o,v)N(v,o)|\leq |M(o,v)|^2+|N(v,o)|^2.$$</div>
<p>For extended nonnegative invariant kernels, translation makes every row sum equal to the root row sum $\chi$, and inversion gives the same for every column, without assuming symmetry. Starting from the identity kernel, Tonelli and induction then give row and column mass $\chi^n$ for the $n$-fold product, including $n=0$ and $\chi=\infty$. These facts underlie the bounded group argument 87W3 when the required sums are finite. They do not by themselves establish the general mass-transport trace or its positivity for products.</p>

## The source's decay hypotheses {#section-decay-source}

<p>The decay implementation is for the independent bond kernel. Its bilinear Cauchy–Schwarz bound allows nonnegative, finite-valued coefficient families and extended sums: apply the finite quadratic-form bound on a set containing both coordinates of each finite set of summands, then take suprema. A finite diagonal triangle gives square summability of that root row, hence its entries tend to zero outside finite sets. The source states this single-row conclusion without countability.</p>
<p>The quadratic and cubic decay exports assume countable vertices and a uniform finite diagonal triangle bound. They split off finite heads and bound the tails using the bilinear inequality, as in <a href="/tag/96A2/">96A2</a>. For the quadratic tail, the source chooses a point mass for one coefficient family, so its diagonal quadratic form is exactly one. The cubic tail instead uses a connection row, whose quadratic form is a diagonal triangle.</p>
<p>For the uniform separation statement, profile-preserving vertex bijections need only preserve a real-valued function $d$. Given a finite exceptional set $E$ at the root, choose $r&gt;\max_{x\in E}d(o,x)$; a pair with $d(u,v)\geq r$ can be carried to $(o,x)$ with $x\notin E$. Thus metric axioms and local finiteness are unnecessary for this source generalization. The existing metric statement remains unchanged. Neither these source inspections nor the train's reported local validation provide a newly extracted or reviewed tag association.</p>


## Nonnegative convolution on a group {#section-convolution-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-analysis-symmetry/">convolution source</a> supplies the group identities behind the translation-invariant kernel calculations. For nonnegative functions, write $(f*g)(x)=\sum_y f(y)g(y^{-1}x)$, allowing infinite values. Reindexing by group translations and interchanging nonnegative sums prove associativity, the reflected formula $\sum_zf(xz^{-1})g(z)$, and</p>
<div class="math-display">$$\sum_x(f*g)(x)=\Bigl(\sum_xf(x)\Bigr)\Bigl(\sum_xg(x)\Bigr).$$</div>
<p>Neither countability nor commutativity of the group is needed. Weighted Hölder gives, for finite $p\geq1$,</p>
<div class="math-display">$$(f*g)(x)^p\leq\Bigl(\sum_yf(y)\Bigr)^{p-1}\sum_yf(y)g(y^{-1}x)^p.$$</div>
<p>Summing in $x$ and taking the $p$th root proves Young’s inequality $\|f*g\|_p\leq\|f\|_1\|g\|_p$. The source obtains its extended-value version directly from finite Hölder bounds, avoiding division by a possibly zero or infinite total mass.</p>
<p>If $\mu(x^{-1})=\mu(x)$, its convolution powers are symmetric. The addition law for powers gives $\sum_x\mu^{*n}(x)^2=\mu^{*2n}(1)$. Cauchy–Schwarz applied to the convolution of the two $n$th powers then gives $\mu^{*2n}(x)\leq\mu^{*2n}(1)$. This even-time maximum requires symmetry, but not probability normalization; it remains an identity and inequality for nonnegative extended masses.</p>


## Moving the observation window {#section-translated-window-mean}

<a id="tag-MTUQ" data-assertion="proposition" data-title="Cluster positivity bounds every translated window by a centred window"></a>
<p>Let a random partition of $\mathbb Z^d$ have a translation-invariant law, and write $\tau(z)=\mathbb P(0\leftrightarrow z)$. For a norm ball $\Lambda_R=\{z:\|z\|\leq R\}$ and $R&gt;0$,</p>
<div class="math-display">$$\sup_x\sum_{z\in x+\Lambda_R}\tau(z)
\leq\frac{|\Lambda_{2R}|}{|\Lambda_R|}\sum_{z\in\Lambda_{4R}}\tau(z).$$</div>
<p>No independence or finite susceptibility is required.</p>
<p><em>Proof.</em> Put $H=\Lambda_{2R}$ and $f(w)=|H\cap(H+w)|$. The two indicator vectors of $H$ and $x+H$, paired through the <a href="/tag/70KD/">positive semidefinite connection kernel</a>, have equal squared norms. Cauchy–Schwarz therefore gives</p>
<div class="math-display">$$S(x):=\sum_{a,b\in H}\tau(x+b-a)
\leq S(0).$$</div>
<p>Grouping by the displacement yields $S(x)=\sum_z\tau(z)f(z-x)$. If $\|w\|\leq R$, then $\Lambda_R\subseteq H\cap(H+w)$, so $f(w)\geq|\Lambda_R|$. Also $f\leq|H|$ and its support lies in $\Lambda_{4R}$. Consequently</p>
<div class="math-display">$$|\Lambda_R|\sum_{z\in x+\Lambda_R}\tau(z)
\leq S(x)\leq S(0)
\leq|\Lambda_{2R}|\sum_{z\in\Lambda_{4R}}\tau(z),$$</div>
<p>as required. These are finite sums even when some clusters are infinite.</p>
<p>For the radial critical model of <a href="/tag/C0OR/">C0OR</a>, the centred estimate <a href="/tag/MRZO/">MRZO</a> and the bounded ball-cardinality ratio give</p>
<div class="math-display">$$\sup_x\mathbb E_{\beta_c}|K_0\cap(x+\Lambda_R)|\leq C R^\alpha\qquad(R\geq1).$$</div>
<p>Every cutoff law below critical intensity satisfies the same bound by domination. This supplies the uniform translated-window mean used in the hydrodynamic transfer. Translation invariance alone moves the root as well as the window; positivity is what permits a bound uniform in their separation.</p>
