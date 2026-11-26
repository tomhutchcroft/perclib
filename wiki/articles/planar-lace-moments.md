---
{
  "id": "planar-lace-moments",
  "title": "Higher lace moments from planar Fourier bounds",
  "subtitle": "Two marked lines at arbitrary lace order",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Bounded faces of the expanded lace diagrams have at most six edges. A planar Fourier representation and mixed H\u00f6lder bounds control two marked lines while retaining small unmarked connector factors. This gives higher moments of the entire lace series in sufficiently large dimension.",
  "context": [
    "Nearest-neighbour Bernoulli bond percolation on $\\mathbb Z^d$.",
    "The argument uses the completed critical Fourier bootstrap and no spatial decay hypothesis.",
    "This is a qualitative large-dimension argument. It does not reproduce the sharper dimension range of Hara's diagram estimates."
  ],
  "related": [
    "fourier-spatial-moment-bridge",
    "two-mark-first-coefficients",
    "higher-lace-moments",
    "lace-coefficient-diagrams",
    "completed-fourier-bootstrap"
  ],
  "sourceIds": [
    "hara-nearest-neighbour-2008",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "planar lace diagram duality",
    "all-order two-mark estimate",
    "critical lace moment doubling"
  ],
  "prototypeUses": []
}
---

## A Fourier bound for planar diagrams {#section-planar}

<p>Fourier integrals use normalized Haar measure on $\mathbb T^d$. Fix one vertex $o$ of a finite connected plane graph $G$, orient its edges, and assign a nonnegative kernel $f_e$ on $\mathbb Z^d$ to each edge. Define its rooted sum by</p>
<div class="math-display">$$\mathcal D_G=\sum_{(x_v)_{v\ne o}}\prod_{e=(u,v)}f_e(x_v-x_u),\qquad x_o=0.$$</div>

<a id="tag-VPUS" data-assertion="theorem" data-title="A facewise Hölder condition bounds a nonnegative rooted planar diagram"></a>
<p>Suppose $G$ has no bridges. For every edge $e$, let $A_e\in L^{p_e}(\mathbb T^d)$, with $1\le p_e<\infty$, have inverse Fourier coefficients $f_e$. If every bounded face $F$ satisfies</p>
<div class="math-display">$$\sum_{e\in\partial F}\frac1{p_e}\le1,$$</div>
<p>then</p>
<div class="math-display">$$\mathcal D_G\le\prod_{e\in E(G)}\|A_e\|_{p_e}<\infty.$$</div>
<p><em>Proof.</em> First suppose the kernels have finite support. Give each bounded face a Fourier variable $q_F$ and put $q_\infty=0$ for the outer face. Orient facial boundaries consistently. If $F_L(e),F_R(e)$ are the faces on the two sides of an oriented edge, Fourier expansion gives</p>
<div class="math-display">$$\mathcal D_G=\int\prod_e A_e\bigl(q_{F_L(e)}-q_{F_R(e)}\bigr)\prod_{F\ne\infty}dq_F.$$</div>
<p>Indeed, integration forces the signed sum of the edge displacements around each bounded face to be zero. Facial boundaries generate the integer cycle space: the boundary of any simple cycle is the signed sum of the faces it encloses. Thus every closed walk has zero displacement. Integrating displacements along paths from $o$ gives a unique assignment of the $x_v$, and every vertex assignment has this property. This proves the identity with no multiplicity or normalization factor.</p>
<p>Take absolute values and integrate one face variable at a time. Hölder, with a constant factor one if the reciprocal exponents sum to less than one, replaces all remaining incident edge factors by their $L^{p_e}$ norms. Each norm is independent of the other face variable by translation invariance of Haar measure. Those edge factors can now be removed. The condition still holds at every remaining face, so iteration proves the bound. An edge is incident to two distinct faces because there are no bridges; hence every factor is removed in this procedure.</p>
<p>For general kernels, smooth each $A_e$ by the product Fejér kernel. Its inverse coefficients are $\theta_n(x)f_e(x)$, where</p>
<div class="math-display">$$\theta_n(x)=\prod_{j=1}^d\left(1-\frac{|x_j|}{n+1}\right)_+.$$</div>
<p>These coefficients have finite support, are nonnegative, and increase to $f_e(x)$. Smoothing is an $L^{p_e}$ contraction, so the finite-support bound is uniform in $n$. Monotone convergence in the rooted spatial sum proves the assertion. No absolutely convergent Fourier series for the original kernels is required.</p>
<p>The Hölder step is a product-space inequality; a general formulation is discussed in Section 7 of <a href="https://math.berkeley.edu/~mchrist/Papers/bcctshort.pdf">Bennett–Carbery–Christ–Tao</a>. The direct argument above supplies the case used here.</p>

## The faces of the lace chain {#section-faces}

<p>Expand the two terms of each intermediate $B_2$ in <a href="/tag/SJIL/">SJIL</a>. At order $N\ge1$ this gives $2^{N-1}$ diagrams, each with $N$ edges carrying $\widetilde\tau=jD*\tau$ and $5N+2$ edges carrying $\tau$.</p>
<p>Here is an explicit plane embedding. Start with the triangle $(0,w_0,u_0)$. Connector $i$ has edges $(w_{i-1},z_i)$ and $(u_{i-1},t_i)$, the latter carrying $\widetilde\tau$. The intermediate block has one of two forms:</p>
<table>
<thead><tr><th>Term of $B_2$</th><th>Edges and identification</th><th>Interior face</th></tr></thead>
<tbody>
<tr><td>First</td><td>$(z_i,t_i),(z_i,u_i),(t_i,w_i),(w_i,u_i)$</td><td>A quadrilateral</td></tr>
<tr><td>Second</td><td>$w_i=t_i$; edges $(a_i,t_i),(a_i,z_i),(a_i,u_i),(z_i,u_i)$</td><td>The triangle $(z_i,a_i,u_i)$</td></tr>
</tbody>
</table>
<p>Finish with the triangle $(z_N,t_N,x)$. The blocks form a strip between the two outer routes from $0$ to $x$. In the first intermediate block both outer sides contain one edge. In the second, one side is the edge $(z_i,u_i)$ and the other has length zero because $w_i=t_i$. The three edges incident to $a_i$ lie inside the strip.</p>
<p>The face at connector $i$ consists of its two connector edges and the boundary paths of its neighbouring blocks. Each boundary path has length one or two: on the right it is $(z_i,t_i)$ or $(z_i,a_i,t_i)$; on the left it is $(w_{i-1},u_{i-1})$ or $(w_{i-1},a_{i-1},u_{i-1})$. Consequently each connector face has at most six edges. The other bounded faces are the two end triangles and the $N-1$ intermediate triangles or quadrilaterals.</p>
<p>This also checks the embedding inductively: attach one connector and one of the two displayed blocks along the current boundary path. Their interiors are disjoint, and the new exposed boundary has the same form. There are $4N+2$ vertices, $6N+2$ edges and $2N+1$ bounded faces. Every edge separates two faces, so there are no bridges. Each of the two outer routes has at most $2N+1$ edges, and the routes share no edge. Collapsed zero-length sides need no edge or mark.</p>

## Two marks at arbitrary positions {#section-moments}

<p>Suppose critical clusters are finite almost surely and</p>
<div class="math-display">$$\tau_c(x)=\int e^{-ik\cdot x}R(k)\,dk,\qquad
R=\frac{\widehat b}{1-\widehat Q},\qquad S=j_c\widehat D R,$$</div>
<p>where $b,Q$ are real even kernels, $\sum Q=1$ and $1-\widehat Q(k)\ge c|k|^2$ for some $c>0$. Thus $S$ has inverse coefficients $\widetilde\tau_c$. Let $M\ge2$ be even, and suppose both kernels have finite absolute $M$th moments. Define</p>
<div class="math-display">$$U=\max\{1,\|R\|_{12}\},\quad V=\|S\|_{12},\quad
B_M=\max\left\{1,\max_j\|\partial_j^M R\|_3,\max_j\|\partial_j^M S\|_3\right\},\quad
\rho=2U^5V.$$</div>

<a id="tag-KOTM" data-assertion="theorem" data-title="A small connector Fourier norm doubles the moment of the entire critical lace series"></a>
<p>If $d>\max\{24,3(M+2)\}$ and $\rho<1$, then $B_M<\infty$, and for every $N\ge2$,</p>
<div class="math-display">$$\sum_x|x|^{2M}\Pi_c^{(N)}(x)
\le 2d^M B_M^2U^{12}(2N+1)^{2M}\rho^{N-2}.$$</div>
<p>The full nonnegative coefficient series satisfies</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\sum_x(1+|x|^{2M})\Pi_p^{(N)}(x)<\infty,$$</div>
<p>and</p>
<div class="math-display">$$\sum_{N\ge0}\sum_x(1+|x|^{2M})\left|\Pi_p^{(N)}(x)-\Pi_c^{(N)}(x)\right|\longrightarrow0
\qquad(p\uparrow p_c).$$</div>
<p><em>Proof.</em> <a href="/tag/2ZOB/">2ZOB</a> gives $|\partial_j^M R(k)|\le C|k|^{-2-M}$. The same bound holds for $S$: its numerator kernel is $j_cD*b$, whose $M$th moment is finite. Since $3(M+2)<d$, both derivatives belong to $L^3$. Also $R,S\in L^{12}$ because $d>24$. By <a href="/tag/1165/">1165</a>, the inverse coefficients of $i^{-M}\partial_j^M R$ and $i^{-M}\partial_j^M S$ are $|x_j|^M\tau_c(x)$ and $|x_j|^M\widetilde\tau_c(x)$. These are nonnegative because $M$ is even.</p>
<p>Fix a coordinate $j$ and one expanded diagram. Apply</p>
<div class="math-display">$$\left|\sum_{r=1}^{L}y_r\right|^M\le L^{M-1}\sum_{r=1}^{L}|y_r|^M$$</div>
<p>on each of its two outer routes, with $L\le2N+1$. Multiplying the two inequalities distributes $|x_j|^{2M}$ over pairs of distinct edges, one from each route. There are at most $(2N+1)^2$ pairs, and the route factor is at most $(2N+1)^{2M-2}$.</p>
<p>For any pair, give the marked edges exponent $3$ in VPUS and the other edges exponent $12$. At a face of length at most six, the reciprocal sum is bounded by</p>
<div class="math-display">$$\max\left\{\frac6{12},\ \frac13+\frac5{12},\ \frac23+\frac4{12}\right\}=1.$$</div>
<p>Thus VPUS applies to every placement, including widely separated marks. Each marked edge contributes at most $B_M$. If $h\le2$ marked edges carry $\widetilde\tau_c$, the other factors contribute at most $U^{5N+h}V^{N-h}$. The inequality $\rho<1$ and $U\ge1$ imply $V<1$. For $N\ge2$ this is at most $U^{5N+2}V^{N-2}$.</p>
<p>Now sum the $2^{N-1}$ expanded diagrams and all pairs of marks. The identity</p>
<div class="math-display">$$2^{N-1}U^{5N+2}V^{N-2}=2U^{12}\rho^{N-2}$$</div>
<p>gives the claimed bound for one coordinate without the factor $d^M$. Finally $|x|^{2M}\le d^{M-1}\sum_j|x_j|^{2M}$ gives that factor. If $V=0$, then the connector kernel vanishes and all positive-order diagrams vanish; this degenerate case can instead be handled directly.</p>
<p>With no marks, use exponent $12$ on every edge. The same argument bounds the total mass at order $N\ge1$ by $(U^2/2)\rho^N$. Orders zero and one have finite $2M$-moments by <a href="/tag/0TO3/">0TO3</a>; its dimension condition follows from the stronger one here. The polynomial factor in $N$ is summable against $\rho^{N-2}$, proving finiteness of the full weighted series.</p>
<p>Every lower-parameter witness diagram is bounded by its critical diagram. This gives the uniform bound, including a weighted order tail tending to zero uniformly in $p$. For a fixed order and bond tuple, the uniform-edge coupling makes its cutting events stabilize as $p\uparrow p_c$: its finitely many relevant critical clusters are finite, and their incident edge variables are almost surely different from $p_c$. The weighted critical diagram is a summable envelope over tuples, targets and witness vertices. Dominated convergence gives convergence in the weighted norm at each fixed order. The uniform order tail then gives the last display. This argument does not assume monotonicity of a lace coefficient.</p>

## Higher moments without a spatial bootstrap hypothesis {#section-dimension}

<a id="tag-GIN9" data-assertion="theorem" data-title="In sufficiently large dimension the full lace series has any prescribed fixed moment and a quadratic relative Fourier remainder"></a>
<p>For every fixed integer $m\ge0$, there is $d_m<\infty$ such that nearest-neighbour bond percolation in every dimension $d\ge d_m$ satisfies</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\sum_x(1+|x|^m)\Pi_p^{(N)}(x)<\infty,$$</div>
<p>with convergence of the entire series in this weighted norm as $p\uparrow p_c$. Moreover,</p>
<div class="math-display">$$\tau_{p_c}(x)\le C_{d,m}\langle x\rangle^{-m}.$$</div>
<p>In sufficiently large dimension one also has, with $\Pi_c$ the alternating sum, $j_c=2dp_c$ and $a_c=1+j_c\sum_x|x|^2\Pi_c(x)>0$,</p>
<div class="math-display">$$R(k)=\frac{2d}{j_ca_c|k|^2}\,[1+O_d(|k|^2)]\qquad(k\to0,\ k\ne0).$$</div>
<p><em>Proof.</em> <a href="/tag/F7N7/">F7N7</a> supplies the critical representation, the gap, finite critical clusters and absolute second moments. It also gives $j_c\le A$ and $0\le R(k)\le A/(1-\widehat D(k))$ with a constant $A$ independent of all sufficiently large dimensions. By <a href="/tag/RD3X/">RD3X</a>,</p>
<div class="math-display">$$\|R\|_{12}^{12}\le A^{12}I_{d,12}\le C,\qquad
\|S\|_{12}^{12}\le j_c^{12}A^{12}\int\frac{\widehat D(k)^{12}}{(1-\widehat D(k))^{12}}\,dk\le Cd^{-6}.$$</div>
<p>Hence $U$ is bounded uniformly and $V=O(d^{-1/2})$. In particular $\rho<1$ for all sufficiently large dimensions. This smallness condition depends only on the unweighted density, so it remains unchanged when the moment order is increased.</p>
<p>Apply KOTM first with $M=2$ to obtain an absolute fourth moment of the full nonnegative lace series. The alternating sum therefore has that moment, and finite-range convolution transfers it to $Q=j_cD*(\delta_0+\Pi_c)$. Apply KOTM with $M=4$ to obtain an eighth moment. Both steps use only $d>24$ in addition to the qualitative bootstrap and smallness thresholds. Further doubling is possible whenever $d>3(M+2)$. For a prescribed $m$, choose a power of two at least $m$ and then a dimension satisfying the finitely many conditions needed to reach it. This proves the weighted summability and continuity claims. Applying 1165 with derivative order $m$ gives the spatial bound; the chosen dimension also satisfies $m<d-2$.</p>
<p>For the Fourier remainder, the fourth moment suffices. Evenness and the bound $|\cos t-1+t^2/2|\le t^4/24$ give a fourth-order Taylor remainder for both $b=\delta_0+\Pi_c$ and $Q$. Coordinate reflections and permutations, the critical mass identity, and the convolution calculation in <a href="/tag/22TW/">22TW</a> give</p>
<div class="math-display">$$\widehat b(k)=j_c^{-1}+O_d(|k|^2),\qquad
1-\widehat Q(k)=\frac{a_c}{2d}|k|^2+O_d(|k|^4).$$</div>
<p>The quadratic gap implies $a_c>0$ by taking the limit along a coordinate axis. Dividing gives the asserted relative $O_d(|k|^2)$ remainder.</p>
<p>The order of quantifiers matters: the dimension may increase with the prescribed moment. This does not give moments of every order in a single fixed dimension. Nor does the spatial estimate above give $|x|^{2-d}$ decay in that dimension. The pointwise coefficient estimate, the sharper spatial iteration and the Gaussian asymptotic still require their separate arguments.</p>

## Relation to the source argument {#section-source}

<p>Hara's Section 3.4 obtains the all-order moment gain by a finer decomposition of marked spatial diagrams. The proof here uses the explicit kernels in SJIL, their plane embedding and Fourier norm smallness instead. It completes the qualitative sufficiently-high-dimensional moment step left open in the <a href="/articles/two-mark-first-coefficients/">first-coefficient article</a>; it does not claim Hara's sharper dimension range or his separated-long-segment estimate in Section 3.5. All new assertions are written mathematics, with no new Lean proof, numerical dimension threshold or source erratum claimed.</p>

## The subsequent pointwise step {#section-pointwise-followup}

<p>The <a href="/articles/planar-pointwise-lace/">two-edge deletion argument</a> now supplies the separate pointwise estimate. <a href="/tag/8F9A/">8F9A</a> doubles a spatial exponent in the full coefficient series, and <a href="/tag/KF2I/">KF2I</a> combines this with KOTM at a dimension-dependent even order to prove the Gaussian spatial asymptotic in sufficiently large dimension. The sharper numerical dimension range remains open here.</p>

## Real orders in the moment gain {#section-real-moments}

<p>The parity restriction in KOTM came from identifying a weight with an ordinary derivative. The endpoint density in <a href="/tag/ENZ7/">ENZ7</a> removes that restriction. No change to the plane diagrams is needed.</p>
<p>Retain the critical representation, finite-cluster assumption and kernel hypotheses of the two-mark argument, but suppose the input moment has any real order $K\ge2$. Let $B_{K,j}$ and $C_{K,j}$ be the Fourier densities with inverse coefficients $|x_j|^K\tau_c(x)$ and $|x_j|^K\widetilde\tau_c(x)$, respectively, and put</p>
<div class="math-display">$$\mathcal B_K=\max\left\{1,\max_j\|B_{K,j}\|_3,\max_j\|C_{K,j}\|_3\right\}.$$</div>
<p>The definitions of $U,V,\rho$ above are unchanged.</p>

<a id="tag-PCOC" data-assertion="theorem" data-title="The planar two-mark bound doubles any real input moment and gives weighted critical continuity"></a>
<p>If $d>\max\{24,3(K+2)\}$ and $\rho<1$, then these densities exist, $\mathcal B_K<\infty$, and for $N\ge2$,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_x|x|^{2K}\Pi_p^{(N)}(x)
\le 2d^K\mathcal B_K^2U^{12}(2N+1)^{2K}\rho^{N-2}.$$</div>
<p>The two lower orders satisfy</p>
<div class="math-display">$$\begin{aligned}
\sup_{p\le p_c}\sum_x|x|^{2K}\Pi_p^{(0)}(x)&\le d^K\mathcal B_K^2,\\
\sup_{p\le p_c}\sum_x|x|^{2K}\Pi_p^{(1)}(x)&\le d^K\mathcal B_K^2U^6\,3^{2K}.
\end{aligned}$$</div>
<p>In particular,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\sum_x(1+|x|^{2K})\Pi_p^{(N)}(x)<\infty,$$</div>
<p>and</p>
<div class="math-display">$$\sum_{N\ge0}\sum_x(1+|x|^{2K})\left|\Pi_p^{(N)}(x)-\Pi_c^{(N)}(x)\right|\longrightarrow0
\qquad(p\uparrow p_c).$$</div>
<p><em>Proof.</em> Apply ENZ7 with exponent $3$ to $R=\widehat b/(1-\widehat Q)$ and to $S=j_c\widehat D\widehat b/(1-\widehat Q)$. The second numerator has kernel $j_cD*b$, so finite range of $D$ preserves its absolute $K$th moment. The condition $3(K+2)<d$ gives both densities in $L^3$. Their inverse coefficients are nonnegative, including when $K$ is odd or noninteger.</p>
<p>For $K\ge1$, convexity gives</p>
<div class="math-display">$$\left|\sum_{r=1}^L y_r\right|^K\le L^{K-1}\sum_{r=1}^L|y_r|^K.$$</div>
<p>Apply this to the $j$th coordinate of the displacements along each outer route. Their edges are disjoint and their lengths are at most $2N+1$. Thus the weight $|x_j|^{2K}$ is distributed over distinct pairs of edges with total factor at most $(2N+1)^{2K}$. Give both marked factors exponent $3$ in VPUS, and every unmarked factor exponent $12$. The largest facewise reciprocal sum is $2/3+4/12=1$.</p>
<p>If $h$ marks fall on connector edges, the unmarked norms contribute at most $U^{5N+h}V^{N-h}$. For $N\ge2$, use $h\le2$, $U\ge1$ and $V<1$. Summing the $2^{N-1}$ expanded diagrams gives</p>
<div class="math-display">$$2^{N-1}\mathcal B_K^2U^{5N+h}V^{N-h}
\le2\mathcal B_K^2U^{12}\rho^{N-2}.$$</div>
<p>Finally, $|x|^{2K}\le d^{K-1}\sum_j|x_j|^{2K}$ gives the stated radial factor. For $N=1$ there is one diagram, the routes have length at most three, and there is only one connector. Thus $h\le1$ and $U^{5+h}V^{1-h}\le U^6$, giving the second low-order bound. If $V=0$, the connector kernel is zero and all positive-order diagrams vanish; the same conclusions follow directly.</p>
<p>At order zero, BK gives $\Pi_p^{(0)}(x)\le\tau_c(x)^2$ off the origin, and the coefficient at zero vanishes. Since $B_{K,j}\in L^3\subset L^2$, Parseval gives</p>
<div class="math-display">$$\sum_x|x_j|^{2K}\tau_c(x)^2=\|B_{K,j}\|_2^2
\le\|B_{K,j}\|_3^2\le\mathcal B_K^2.$$</div>
<p>Summing the coordinate bounds proves the remaining estimate. The unweighted masses are controlled by the unmarked diagrams as in KOTM. The geometric factor in $N$ absorbs the polynomial factor for each fixed real $K$, proving summability of the entire weighted series.</p>
<p>For continuity, use the same critical witness envelope as in KOTM. At each fixed order and bond tuple, the cutting events stabilize under the uniform-edge coupling because the relevant critical clusters are finite. The weighted critical diagrams are summable by the bounds just proved, so dominated convergence applies to the tuple and vertex sums. Their summable order bounds then give convergence of the full series. This uses no monotonicity of a lace coefficient and no integrality of the weight.</p>

## The moment range in a fixed dimension {#section-real-range}

<p>Now suppose $b=\delta_0+\Pi_c$ and $Q=j_cD*b$, where $\Pi_c$ is the alternating lace sum. Assume the critical representation, gap and finite-cluster hypotheses above, finite absolute second moments of $b,Q$, $d>24$ and $\rho<1$.</p>

<a id="tag-6N01" data-assertion="corollary" data-title="The real-order iteration reaches every moment strictly below two thirds of the dimension minus four"></a>
<p>For every real</p>
<div class="math-display">$$0\le s<\frac{2(d-6)}3,$$</div>
<p>the full nonnegative lace series has a uniformly finite absolute $s$th moment for $p\le p_c$ and converges in that weighted norm as $p\uparrow p_c$. Moreover,</p>
<div class="math-display">$$\tau_c(x)\le C_{d,s}\langle x\rangle^{-s}.$$</div>
<p><em>Proof.</em> PCOC at $K=2$ gives an absolute fourth moment and weighted continuity. This already covers $s\le4$ by domination. For $s>4$, put $K=s/2$. Starting with the known second moment, apply KOTM at successive powers of two strictly less than $K$, stopping as soon as the available moment is at least $K$. Every such input order $M$ satisfies $3(M+2)<3(K+2)<d$. The alternating sum inherits each new absolute moment, as do $b$ and the finite-range convolution $Q$. PCOC at the real order $K$ therefore gives exactly the requested moment $s=2K$, together with its weighted continuity.</p>
<p>The final kernels have the required absolute $s$th moment, or an absolute fourth moment if $s\le4$. Since $s<2(d-6)/3<d-2$, ENZ7 with exponent $1$ gives the spatial bound when $s\ge2$; 65QV covers the smaller weights. The Fourier gap and $\rho$ concern the same critical kernels throughout the iteration. They are not new hypotheses at each step.</p>
<p>This is a range of moments at one fixed dimension. The upper endpoint is excluded, and the argument does not give moments of every order in that dimension.</p>

<p>The comparison with Hara Section 3.4, particularly (3.11)–(3.15), is unchanged: the two-route weights are common to both arguments, while VPUS supplies a different estimate for the marked diagrams. The exact Fourier endpoint makes this alternative work at every real input order. No sharper source diagram estimate, numerical percolation dimension threshold or new source erratum is asserted.</p>

## Integrating the block faces first {#section-ordered-faces}

<p>The exponents in PCOC allow all six edges of a connector face to remain when that face is integrated. The strip admits a better order. Call the two end triangles and the intermediate triangles or quadrilaterals <em>block faces</em>; the other bounded faces are the connector faces.</p>

<a id="tag-7TNU" data-assertion="proposition" data-title="An ordered integration of the lace strip uses at most four factors at each face"></a>
<p>In an expanded order-$N$ strip, mark one edge on each outer route. Suppose the nonnegative edge kernels have Fourier densities in $L^a$ on the two marked edges and in $L^b$ on the others, where $1\le a,b<\infty$ and</p>
<div class="math-display">$$\frac4b\le1,\qquad \frac1a+\frac3b\le1,\qquad \frac2a+\frac2b\le1.$$</div>
<p>Then the rooted diagram is at most the product of these norms. In particular, one may take $a=18/7$ and $b=9$.</p>
<p><em>Proof.</em> Use the facial Fourier identity of VPUS and integrate the block-face variables first. Their boundaries have three or four edges, and distinct block faces share no edge. Each such integration removes every incident factor at the cost of its prescribed norm. There are at most two marked factors, so the three inequalities in the statement cover every possibility.</p>
<p>After these integrations, a connector face retains its two connector edges and at most one edge from each neighbouring block. A first-type block leaves none of its edges. In a second-type block, the triangle $(z_i,a_i,u_i)$ removes $(z_i,a_i),(a_i,u_i),(z_i,u_i)$; only $(a_i,t_i)$ remains, shared by the adjacent connector faces. The end triangles likewise leave no edge. Thus every remaining connector face has at most four factors. Subsequent integrations can only remove more of them, and the same three Hölder inequalities apply. All factors are eventually removed. For the displayed exponents the three reciprocal sums are $4/9,13/18,1$.</p>
<p>For finitely supported kernels this proves the bound directly. In general use positive product Fejér smoothing as in VPUS. It contracts every prescribed norm and gives nonnegative, finitely supported coefficients increasing to the original kernels. Monotone convergence proves the asserted bound for the full rooted sum.</p>

## The moment gain with ninth Fourier norms {#section-ninth-moments}

<p>Retain the critical representation and finite-cluster hypotheses of PCOC. Write</p>
<div class="math-display">$$U_9=\max\{1,\|R\|_9\},\qquad V_9=\|S\|_9,\qquad
\rho_9=2U_9^5V_9,\qquad S=j_c\widehat D R.$$</div>
<p>For real $K\ge2$ define, using the absolute-weight densities of ENZ7,</p>
<div class="math-display">$$\mathcal B_{K,9}=\max\left\{1,\max_j\|B_{K,j}\|_{18/7},\max_j\|C_{K,j}\|_{18/7}\right\}.$$</div>

<a id="tag-5T90" data-assertion="theorem" data-title="Ordered face integration doubles real lace moments and reaches every order below seven ninths of the dimension minus four"></a>
<p>Suppose $b,Q$ have finite absolute $K$th moments, $d>18$, $\rho_9<1$, and</p>
<div class="math-display">$$\frac{18}{7}(K+2)<d.$$</div>
<p>Then $\mathcal B_{K,9}<\infty$, and for $N\ge2$,</p>
<div class="math-display">$$\sup_{p\le p_c}\sum_x|x|^{2K}\Pi_p^{(N)}(x)
\le 2d^K\mathcal B_{K,9}^2U_9^{12}(2N+1)^{2K}\rho_9^{N-2}.$$</div>
<p>The orders zero and one are bounded respectively by $d^K\mathcal B_{K,9}^2$ and $d^K\mathcal B_{K,9}^2U_9^6 3^{2K}$. The full coefficient series is uniformly summable with weight $1+|x|^{2K}$ for $p\le p_c$, and converges in that weighted norm as $p\uparrow p_c$.</p>
<p>In particular, if $b=\delta_0+\Pi_c$, $Q=j_cD*b$ and only their absolute second moments are initially assumed, then the same critical hypotheses and $\rho_9<1$ give, for every</p>
<div class="math-display">$$0\le s<\frac{7d}{9}-4,$$</div>
<p>uniform summability and critical continuity of the full coefficient series with weight $1+|x|^s$, and $\tau_c(x)\le C_{d,s}\langle x\rangle^{-s}$.</p>
<p><em>Proof.</em> The quadratic gap puts $R,S$ in $L^9$ because $d>18$. ENZ7 gives the two weighted densities in $L^{18/7}$ under the displayed moment condition; finite range of $D$ transfers the input moment to the numerator of $S$.</p>
<p>Distribute $|x_j|^{2K}$ over the two outer routes exactly as in PCOC. Their edge sets are disjoint, their lengths are at most $2N+1$, and convexity gives a total factor at most $(2N+1)^{2K}$ after summing over the marked pairs. Apply 7TNU with marked exponent $18/7$ and unmarked exponent $9$. If $h$ marked edges are connectors, the unmarked norms contribute</p>
<div class="math-display">$$U_9^{5N+h}V_9^{N-h}\le U_9^{5N+2}V_9^{N-2}\qquad(N\ge2),$$</div>
<p>since $h\le2$, $U_9\ge1$ and $V_9<1$. Sum the $2^{N-1}$ expanded diagrams and use</p>
<div class="math-display">$$2^{N-1}U_9^{5N+2}V_9^{N-2}=2U_9^{12}\rho_9^{N-2}.$$</div>
<p>The radial inequality $|x|^{2K}\le d^{K-1}\sum_j|x_j|^{2K}$ proves the stated bound. At order one, $h\le1$ gives the factor $U_9^6$. At order zero use BK and Parseval, with $L^{18/7}\subset L^2$. If $V_9=0$, all connector kernels vanish and all positive orders vanish, so the conclusions follow directly.</p>
<p>The unmarked diagrams have mass at most $(U_9^2/2)\rho_9^N$ for $N\ge1$. The polynomial order factors are summable against the geometric factor. Critical witness diagrams dominate all lower-parameter diagrams. At fixed order and bond tuple, the uniform-edge coupling makes the cutting events stabilize because the relevant critical clusters are finite. Dominated convergence applies to the tuple and vertex sums, and the uniform weighted order tail gives convergence of the full series. This is the continuity argument of PCOC, using the new summable envelope; it does not require monotonicity of a lace coefficient.</p>
<p>For the last assertion, the input $K=2$ first supplies a fourth moment, since $72/7<d$. This covers $s\le4$. For $s>4$, put $K=s/2<7d/18-2$. Starting at order two, double the available moment until it reaches $K$. Every input used before that happens is less than $K$, and hence satisfies the strict dimension inequality. The alternating sum and the finite-range convolution defining $Q$ inherit each moment. One application at the real input $K$ now gives the requested output $s$. Finally $s<7d/9-4<d-2$, so ENZ7, or 65QV for $s<2$, gives the spatial bound. The critical kernels and $\rho_9$ stay fixed throughout this iteration.</p>

<p>This refines the earlier planar argument by changing the order of integration, without changing any of its tagged statements. It uses the explicit strip of SJIL. It is not a verification of the numerical smallness hypotheses in a specified percolation dimension.</p>

## Two weights in the spatial transition {#section-weighted-rows}

<p>A spatial row estimate gives a further improvement for moments. It retains the small-triangle quantity from SJIL, instead of estimating each unmarked edge separately. Work at criticality, write $\tau=\tau_c$, $\widetilde\tau=j_cD*\tau$, and put</p>
<div class="math-display">$$\Delta=\|\tau*\tau*\tau\|_\infty,\qquad
T=\|\tau*\tau*\widetilde\tau\|_\infty,\qquad r=2T\Delta.$$</div>
<p>For $K\ge1$, set $g_{K,j}(x)=|x_j|^K\tau(x)$ and $\widetilde g_{K,j}(x)=|x_j|^K\widetilde\tau(x)$, with $g_{0,j}=\tau$ and $\widetilde g_{0,j}=\widetilde\tau$. Define</p>
<div class="math-display">$$M_K=\max\left\{1,\max_j\max_{a,b\in\{0,K\}}
\left\{\|g_{a,j}*g_{b,j}*\tau\|_\infty,
\|g_{a,j}*\widetilde g_{b,j}*\tau\|_\infty\right\}\right\}.$$</div>

<a id="tag-SL9H" data-assertion="theorem" data-title="Two weighted triangle row bounds control every placement of two outer-route marks"></a>
<p>Suppose critical clusters are finite almost surely, $M_K<\infty$ and $r<1$. Then, for $N\ge2$,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_x|x|^{2K}\Pi_p^{(N)}(x)
\le2d^K M_K^5(2N+1)^{2K}r^{N-2}.$$</div>
<p>The orders zero and one are bounded respectively by $d^KM_K$ and $d^KM_K^3 3^{2K}$. The full coefficient series is uniformly summable with weight $1+|x|^{2K}$ for $p\le p_c$ and converges in that weighted norm as $p\uparrow p_c$.</p>
<p><em>Proof.</em> Fix a coordinate and a pair of distinct marked outer-route edges. Each marked factor is replaced by its $K$-weighted kernel. Consider one connector together with the block to its right, as a transition from the fixed pair $(w_0,u_0)$ to the outgoing pair. We show that its row sum is at most $M_K^2$ if it contains a mark, and at most $T\Delta$ if it does not. At most two transitions contain marks.</p>
<p>For a first-type block, denote the connector factors by $F(z-w_0)$ and $H(t-u_0)$, and the two outer block factors by $J(u-z)$ and $L(w-t)$. Here $F,J,L$ are either $\tau$ or $g_{K,j}$, and $H$ is either $\widetilde\tau$ or $\widetilde g_{K,j}$. The two transverse factors remain unweighted. Summing the outgoing pair $(w,u)$ first gives the exact row sum</p>
<div class="math-display">$$\sum_{z,t}F(z-w_0)H(t-u_0)\tau(t-z)
(J*L*\tau)(t-z)
\le\|J*L*\tau\|_\infty\,\|F*H*\tau\|_\infty.$$</div>
<p>All these kernels are even, so no reflected kernel is needed. The right side is at most $M_K^2$, and is $\Delta T$ when no factor is marked.</p>
<p>For a second-type block, its zero-length side carries no edge. Denote its other outer factor by $G(u-z)$, where $G$ is either $\tau$ or $g_{K,j}$; its other three factors are unweighted. With the same connector factors $F,H$, the row sum is</p>
<div class="math-display">$$\sum_{z,t,a,u}F(z-w_0)H(t-u_0)
\tau(a-t)\tau(z-a)\tau(u-a)G(u-z).$$</div>
<p>Sum $t$, put $v=a-z$, and sum $u$ and the common translation $z$. This becomes</p>
<div class="math-display">$$\sum_v\tau(v)(\tau*G)(v)(F*H*\tau)(w_0-u_0+v)
\le\|F*H*\tau\|_\infty\,(\tau*\tau*G)(0).$$</div>
<p>This again is at most $M_K^2$, or $T\Delta$ with no mark. The identities are Tonelli rearrangements of nonnegative sums and hold before finiteness is established.</p>
<p>The initial triangle, with zero, one or two marked outer edges, has total mass at most $M_K$. Enlarge the terminal triangle to a first-type block and sum its outgoing pair: the diagonal terms $w=u=x$ reproduce the terminal triangle exactly because $\tau(0)=1$. This also preserves either or both terminal weights. Thus an expanded order-$N$ diagram has an initial factor of mass at most $M_K$ followed by $N$ transitions. If $b\le2$ transitions contain marks, its full sum is bounded by</p>
<div class="math-display">$$M_K^{2b+1}(T\Delta)^{N-b}
\le M_K^5(T\Delta)^{N-2}\qquad(N\ge2).$$</div>
<p>The last inequality uses $M_K\ge1$ and $T\Delta<1$. There are $2^{N-1}$ expanded diagrams. Convexity distributes the coordinate weight over the two disjoint routes with total factor at most $(2N+1)^{2K}$, exactly as in PCOC. Since $2^{N-1}(T\Delta)^{N-2}=2r^{N-2}$, summing the diagrams and then the coordinates gives the stated bound.</p>
<p>At order one there is a single transition, giving $M_K^3 3^{2K}$ before the radial factor. At order zero, BK and $\tau(0)=1$ give</p>
<div class="math-display">$$\sum_x|x_j|^{2K}\Pi_p^{(0)}(x)
\le\sum_x g_{K,j}(x)^2
\le(g_{K,j}*g_{K,j}*\tau)(0)\le M_K.$$</div>
<p>If $T=0$, then $\widetilde\tau=0$, since $\tau\ge\delta_0$, and all positive-order diagrams vanish; this case is immediate. Otherwise the polynomial order factors are summable against $r^{N-2}$. SJIL supplies the unweighted mass bounds. Critical diagrams dominate the lower-parameter diagrams, and the fixed-tuple coupling and dominated-convergence argument of PCOC applies with this new weighted envelope. It gives the claimed uniform summability and critical continuity.</p>

## Reaching moments below dimension minus six {#section-triangle-moment-range}

<a id="tag-B0RG" data-assertion="theorem" data-title="The critical Fourier gap and small triangle give every lace moment strictly below dimension minus six"></a>
<p>Suppose $d>10$, critical clusters are finite almost surely, and the critical Fourier representation holds with real even kernels</p>
<div class="math-display">$$R=\frac{\widehat b}{1-\widehat Q},\qquad
b=\delta_0+\Pi_c,\qquad Q=j_cD*b,\qquad \sum_xQ(x)=1,
\qquad 1-\widehat Q(k)\ge c|k|^2.$$</div>
<p>Assume $b,Q$ have finite absolute second moments and $r=2T\Delta<1$. For every real $0\le s<d-6$,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\sum_x(1+|x|^s)\Pi_p^{(N)}(x)<\infty,$$</div>
<p>the full series converges in this weighted norm as $p\uparrow p_c$, and $\tau_c(x)\le C_{d,s}\langle x\rangle^{-s}$. Weight one is used at $s=0$. No Gaussian spatial estimate is assumed.</p>
<p><em>Proof.</em> Suppose first that the input kernels have an absolute moment of some real order $K\ge2$ with $2K+6<d$. The endpoint convolution result ENZ7 gives</p>
<div class="math-display">$$\|g_{a,j}*g_{b,j}*\tau\|_\infty<\infty
\qquad(a,b\in\{0,K\}).$$</div>
<p>It applies to all four choices, including $a=b=K$, since the total power-counting exponent is at most $6+2K$. For a nearest-neighbour shift $z$, $|z_j|\le1$, so</p>
<div class="math-display">$$\widetilde g_{K,j}(x)
\le j_c2^{K-1}\,[D*(g_{K,j}+\tau)](x).$$</div>
<p>Also $\widetilde g_{0,j}=j_cD*\tau$. Convolution with the probability kernel $D$ contracts the supremum norm. Thus the mixed triples defining $M_K$ are finite as well. SL9H gives an absolute $2K$th moment of the full nonnegative coefficient series, with weighted critical continuity. The alternating sum, $b$ and its finite-range convolution $Q$ inherit this moment.</p>
<p>Start with $K=2$; its condition is exactly $d>10$, and it gives a fourth moment. For $s>4$, put $K=s/2<(d-6)/2$. Double the available moment until it reaches $K$, then apply the preceding gain at $K$ itself. Every earlier input is smaller than $K$, so all dimension inequalities are strict. This gives every $s<d-6$; the range $s\le4$ follows from the first gain by domination. Since $s<d-6<d-2$, ENZ7 and 65QV give the spatial bound. The quantity $r$ is unchanged throughout: it belongs to the fixed critical connection kernel.</p>
<p>The new smallness assumption is implied by the ninth-norm assumption used above. Indeed the convolution identities and Hölder give $\Delta\le\|R\|_9^3$ and $T\le\|R\|_9^2\|S\|_9$, so $r\le\rho_9$. The spatial iteration in CP1T may therefore use this larger moment range. Its separate pointwise coefficient estimate still uses ninth-norm connector smallness; the present theorem does not remove that hypothesis from the Gaussian conclusion.</p>

<p>This gives the moment range in JJJN without its assumed Gaussian two-point decay. The row argument is a sufficient alternative to the finer marked-diagram decomposition in Hara Section 3.4; the loss of six dimensions comes from controlling a triangle with both weights. It neither asserts the endpoint $s=d-6$ nor verifies a numerical percolation threshold.</p>
